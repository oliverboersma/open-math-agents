import FormalConjectures.ErdosProblems.«1088»
import Mathlib

-- Erdos Problem 1088: for fixed n >= 3, f_d(n) = 2^{o(d)}.
--
-- The mathematics below is NOT the work of the submitter. It is a port of the public proof
--   Source: https://github.com/H0W4RD-dev/erdos-1088-lean
--   Commit: d164b380cc372d2a446a2b2f81a9d47b9d709292
--   Authors: Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer (the repository says
--   the argument and the Lean code were produced by AI agents in sessions directed by
--   Will Howe).
--   Licence: Apache License, Version 2.0, http://www.apache.org/licenses/LICENSE-2.0
--   Used here under the terms of that licence.
--
-- Changes made to the source: the modules imported by E1088/Assembly.lean are concatenated
-- in dependency order into this one file, each module's sections closed; the module
-- E1088/Statement/Erdos1088.lean, a verbatim copy of the Formal Conjectures definitions, is
-- left out, so the proof runs against the definitions pinned on this site; comments and
-- blank lines are removed to fit the size limit; file-level options are attached to the
-- declarations they covered; one local tactic macro (memtac) is written out at its eight
-- uses, because this site forbids macros. Only the final theorem OMA.solution is new; it is
-- the body of the source's E1088/Final.lean.

section
open Filter Asymptotics Real
namespace E1088
theorem sqrt_log_isLittleO :
    (fun x : ℝ => Real.sqrt x * Real.log (x + 2)) =o[atTop] (fun x => x) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h2 : (fun x : ℝ => Real.log (x + 2)) =o[atTop] (fun x => (x + 2) ^ (1 / 2 : ℝ)) :=
    h1.comp_tendsto (tendsto_atTop_add_const_right _ 2 tendsto_id)
  have h3 : (fun x : ℝ => (x + 2) ^ (1 / 2 : ℝ)) =O[atTop] (fun x => Real.sqrt x) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have : Real.sqrt (x + 2) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    exact this
  have h4 := h2.trans_isBigO h3
  have h5 : (fun x : ℝ => Real.sqrt x * Real.log (x + 2)) =o[atTop]
      (fun x => Real.sqrt x * Real.sqrt x) := (isBigO_refl _ _).mul_isLittleO h4
  refine h5.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Real.mul_self_sqrt hx
theorem bound_isLittleO (c₀ c₁ : ℝ) :
    (fun d : ℕ => c₀ + c₁ * (Real.sqrt d * Real.logb 2 (d + 2))) =o[atTop]
      (fun d : ℕ => (d : ℝ)) := by
  have hA : (fun d : ℕ => c₀) =o[atTop] (fun d : ℕ => (d : ℝ)) :=
    (isLittleO_const_id_atTop c₀).natCast_atTop
  have hB : (fun d : ℕ => Real.sqrt d * Real.log ((d : ℝ) + 2)) =o[atTop]
      (fun d : ℕ => (d : ℝ)) := sqrt_log_isLittleO.natCast_atTop
  have hB' : (fun d : ℕ => c₁ * (Real.sqrt d * Real.logb 2 (d + 2))) =o[atTop]
      (fun d : ℕ => (d : ℝ)) := by
    have := hB.const_mul_left (c₁ / Real.log 2)
    refine this.congr' (Eventually.of_forall fun d => ?_) EventuallyEq.rfl
    simp only [Real.logb]
    ring
  exact hA.add hB'
end E1088
end
section
open Filter Asymptotics
open scoped EuclideanGeometry
namespace E1088
def RainbowFree (n : ℕ) {d : ℕ} (X : Finset (ℝ^d)) : Prop :=
  ¬ Erdos1088.HasSubsetWithDistinctDistances n X
noncomputable def affDim {d : ℕ} (X : Finset (ℝ^d)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (X : Set (ℝ^d)))
noncomputable def halvingExp (C : ℝ) (D : ℕ) : ℝ := C * (Real.sqrt D * Real.logb 2 (D + 2))
def HalvingStep (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d D B : ℕ) (X : Finset (ℝ^d)), RainbowFree n X → affDim X ≤ D →
    (∀ Y : Finset (ℝ^d), RainbowFree n Y → affDim Y ≤ D / 2 → Y.card ≤ B) →
    (X.card : ℝ) ≤ (2 : ℝ) ^ halvingExp C D * (B + 1)
noncomputable def solvedExp (C : ℝ) (D : ℕ) : ℝ := 4 * (C + 1) * (Real.sqrt D * Real.logb 2 (D + 2)) + 1
theorem card_le_one_of_affDim_zero {d : ℕ} (X : Finset (ℝ^d)) (h : affDim X = 0) :
    X.card ≤ 1 := by
  unfold affDim at h
  rw [Submodule.finrank_eq_zero, vectorSpan_eq_bot_iff_subsingleton] at h
  exact Finset.card_le_one.2 fun a ha b hb => h ha hb
theorem sqrt_mul_logb_ge_one (D : ℕ) (hD : 1 ≤ D) : 1 ≤ Real.sqrt D * Real.logb 2 (D + 2) := by
  have h1 : (1 : ℝ) ≤ Real.sqrt D := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hD)
  have h2 : (1 : ℝ) ≤ Real.logb 2 (D + 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    rw [Real.rpow_one]; linarith
  nlinarith
theorem sqrt_half_le (D : ℕ) : Real.sqrt ((D / 2 : ℕ) : ℝ) ≤ 3 / 4 * Real.sqrt D := by
  rw [show (3 / 4 : ℝ) = Real.sqrt (9 / 16) by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have : ((D / 2 : ℕ) : ℝ) ≤ (D : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self D 2
  have h0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  linarith
theorem logb_half_le (D : ℕ) : Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) ≤ Real.logb 2 (D + 2) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  have : ((D / 2 : ℕ) : ℝ) ≤ D := by exact_mod_cast Nat.div_le_self D 2
  linarith
theorem card_le_of_rainbowFree (n : ℕ) (C : ℝ) (hC : 0 < C)
    (hstep : ∀ (d D B : ℕ) (X : Finset (ℝ^d)), RainbowFree n X → affDim X ≤ D →
      (∀ Y : Finset (ℝ^d), RainbowFree n Y → affDim Y ≤ D / 2 → Y.card ≤ B) →
      (X.card : ℝ) ≤ (2 : ℝ) ^ halvingExp C D * (B + 1)) (d : ℕ) :
    ∀ D : ℕ, ∀ X : Finset (ℝ^d), RainbowFree n X → affDim X ≤ D →
      (X.card : ℝ) + 1 ≤ (2 : ℝ) ^ solvedExp C D := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro X hX hdim
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have := card_le_one_of_affDim_zero X (by omega)
      have : (X.card : ℝ) ≤ 1 := by exact_mod_cast this
      simp [solvedExp]; linarith
    set E2 := solvedExp C (D / 2) with hE2
    have hE2nn : 0 ≤ E2 := by
      simp only [hE2, solvedExp]
      have : 0 ≤ Real.sqrt ((D / 2 : ℕ) : ℝ) * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.logb_nonneg (by norm_num) (by
          have : (0 : ℝ) ≤ ((D / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith))
      nlinarith
    have h2E : (1 : ℝ) ≤ 2 ^ E2 := Real.one_le_rpow (by norm_num) hE2nn
    set B := ⌊(2 : ℝ) ^ E2 - 1⌋₊ with hB
    have hYB : ∀ Y : Finset (ℝ^d), RainbowFree n Y → affDim Y ≤ D / 2 → Y.card ≤ B := by
      intro Y hY hYd
      have := ih (D / 2) (Nat.div_lt_self hD (by norm_num)) Y hY hYd
      exact Nat.le_floor (by linarith)
    have hBle : (B : ℝ) ≤ 2 ^ E2 - 1 := Nat.floor_le (by linarith)
    have hX' := hstep d D B X hX hdim hYB
    have hhE : halvingExp C D + E2 + 1 ≤ solvedExp C D := by
      simp only [halvingExp, hE2, solvedExp]
      have a1 := sqrt_half_le D
      have a2 := logb_half_le D
      have a3 := sqrt_mul_logb_ge_one D hD
      have a4 : 0 ≤ Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) := Real.logb_nonneg (by norm_num) (by
          have : (0 : ℝ) ≤ ((D / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith)
      have a5 : Real.sqrt ((D / 2 : ℕ) : ℝ) * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) ≤
          3 / 4 * (Real.sqrt D * Real.logb 2 (D + 2)) := by
        calc Real.sqrt ((D / 2 : ℕ) : ℝ) * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2)
            ≤ 3 / 4 * Real.sqrt D * Real.logb 2 (((D / 2 : ℕ) : ℝ) + 2) :=
              mul_le_mul_of_nonneg_right a1 a4
          _ ≤ 3 / 4 * Real.sqrt D * Real.logb 2 (D + 2) :=
              mul_le_mul_of_nonneg_left a2 (by positivity)
          _ = _ := by ring
      nlinarith
    have hpow : (2 : ℝ) ^ halvingExp C D * 2 ^ E2 * 2 ≤ 2 ^ solvedExp C D := by
      have e : (2 : ℝ) ^ (halvingExp C D + E2 + 1) = 2 ^ halvingExp C D * 2 ^ E2 * 2 := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]
      rw [← e]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hhE
    have h1 : (1 : ℝ) ≤ 2 ^ halvingExp C D := Real.one_le_rpow (by norm_num) (by
      simp only [halvingExp]
      exact mul_nonneg hC.le (mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith))))
    have : (X.card : ℝ) ≤ 2 ^ halvingExp C D * 2 ^ E2 := by
      calc (X.card : ℝ) ≤ 2 ^ halvingExp C D * (B + 1) := hX'
        _ ≤ 2 ^ halvingExp C D * 2 ^ E2 := by gcongr; linarith
    nlinarith
theorem affDim_le {d : ℕ} (X : Finset (ℝ^d)) : affDim X ≤ d := by
  unfold affDim
  exact (Submodule.finrank_le _).trans (by simp)
theorem erdos_1088_of_halving (hH : ∀ n ≥ 3, HalvingStep n) :
    ∀ n ≥ 3,
      (fun d : ℕ ↦ Real.logb 2 (Erdos1088.f d n : ℝ)) =o[atTop] (fun d : ℕ ↦ (d : ℝ)) := by
  intro n hn
  obtain ⟨C, hC, hstep⟩ := hH n hn
  have hcard := card_le_of_rainbowFree n C hC hstep
  have hf : ∀ d : ℕ, (Erdos1088.f d n : ℝ) ≤ n * 2 ^ solvedExp C d := by
    intro d
    set m := max n ⌊(2 : ℝ) ^ solvedExp C d⌋₊ with hm
    have hmem : m ∈ Erdos1088.cardSet d n := by
      refine ⟨le_max_left _ _, fun S hS => ?_⟩
      by_contra hcon
      have h1 := hcard d d S hcon (affDim_le S)
      have h2 : S.card + 1 ≤ ⌊(2 : ℝ) ^ solvedExp C d⌋₊ := Nat.le_floor (by exact_mod_cast h1)
      have h3 : ⌊(2 : ℝ) ^ solvedExp C d⌋₊ ≤ m := le_max_right _ _
      omega
    have hle : Erdos1088.f d n ≤ m := Nat.sInf_le hmem
    have hE : (1 : ℝ) ≤ 2 ^ solvedExp C d := Real.one_le_rpow (by norm_num) (by
      simp only [solvedExp]
      have : 0 ≤ Real.sqrt d * Real.logb 2 (d + 2) := mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      nlinarith)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hm' : (m : ℝ) ≤ n * 2 ^ solvedExp C d := by
      rcases le_total n ⌊(2 : ℝ) ^ solvedExp C d⌋₊ with h | h
      · rw [hm, max_eq_right h]
        have := Nat.floor_le (show (0 : ℝ) ≤ 2 ^ solvedExp C d by positivity)
        nlinarith
      · rw [hm, max_eq_left h]; nlinarith
    calc (Erdos1088.f d n : ℝ) ≤ m := by exact_mod_cast hle
      _ ≤ _ := hm'
  have hlog : ∀ d : ℕ, ‖Real.logb 2 (Erdos1088.f d n : ℝ)‖ ≤
      Real.logb 2 n + (1 + 4 * (C + 1) * (Real.sqrt d * Real.logb 2 (d + 2))) := by
    intro d
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    rcases Nat.eq_zero_or_pos (Erdos1088.f d n) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero, norm_zero]
      have : 0 ≤ Real.sqrt d * Real.logb 2 (d + 2) := mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      have : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
      nlinarith
    · have hf1 : (1 : ℝ) ≤ Erdos1088.f d n := by exact_mod_cast hpos
      have hnn : 0 ≤ Real.logb 2 (Erdos1088.f d n : ℝ) := Real.logb_nonneg (by norm_num) hf1
      rw [Real.norm_of_nonneg hnn]
      calc Real.logb 2 (Erdos1088.f d n : ℝ) ≤ Real.logb 2 (n * 2 ^ solvedExp C d) :=
            Real.logb_le_logb_of_le (by norm_num) (by linarith) (hf d)
        _ = Real.logb 2 n + solvedExp C d := by
            rw [Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num)
              (by norm_num)]
        _ = _ := by simp only [solvedExp]; ring
  refine IsBigO.trans_isLittleO (g := fun d : ℕ =>
    Real.logb 2 n + (1 + 4 * (C + 1) * (Real.sqrt d * Real.logb 2 (d + 2)))) ?_ ?_
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun d => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have : 0 ≤ Real.logb 2 n + (1 + 4 * (C + 1) * (Real.sqrt d * Real.logb 2 (d + 2))) := by
      have : 0 ≤ Real.sqrt d * Real.logb 2 (d + 2) := mul_nonneg (Real.sqrt_nonneg _)
        (Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      have : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
      nlinarith
    rw [one_mul, Real.norm_of_nonneg this]
    exact hlog d
  · have := bound_isLittleO (Real.logb 2 n + 1) (4 * (C + 1))
    refine this.congr' (Eventually.of_forall fun d => ?_) EventuallyEq.rfl
    ring
end E1088
end
section
open Matrix
namespace E1088
section Field
variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype m] [Fintype n]
theorem exists_factor (A : Matrix m n K) :
    ∃ (r : ℕ) (U : Matrix m (Fin r) K) (V : Matrix (Fin r) n K), r = A.rank ∧ A = U * V := by
  classical
  set S := Submodule.span K (Set.range A.col) with hS
  have hcol : ∀ j, A.col j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
  let b := Module.finBasis K S
  refine ⟨Module.finrank K S, Matrix.of fun i k => (b k : m → K) i,
    Matrix.of fun k j => b.repr ⟨A.col j, hcol j⟩ k, A.rank_eq_finrank_span_cols.symm, ?_⟩
  ext i j
  have h := congrArg (fun v : S => (v : m → K) i) (b.sum_repr ⟨A.col j, hcol j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  simp only [Matrix.mul_apply, Matrix.of_apply]
  change A.col j i = _
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
omit [Fintype m] in
theorem rank_mul_le_card {k : Type*} [Fintype k] (U : Matrix m k K) (V : Matrix k n K) :
    (U * V).rank ≤ Fintype.card k :=
  (rank_mul_le_left U V).trans (rank_le_card_width U)
theorem rank_submatrix_le' {m' n' : Type*} [Fintype m'] [Fintype n'] (A : Matrix m n K)
    (f : m' → m) (g : n' → n) : (A.submatrix f g).rank ≤ A.rank := by
  obtain ⟨r, U, V, hr, rfl⟩ := exists_factor A
  have : (U * V).submatrix f g = U.submatrix f id * V.submatrix id g := by
    ext i j; simp [Matrix.mul_apply]
  rw [this, hr.symm]
  exact (rank_mul_le_card _ _).trans_eq (by simp)
theorem rank_hadamard_le (A B : Matrix m n K) : (A ⊙ B).rank ≤ A.rank * B.rank := by
  obtain ⟨r, U, V, hr, rfl⟩ := exists_factor A
  obtain ⟨s, U', V', hs, hB⟩ := exists_factor B
  rw [← hr, ← hs]
  have : (U * V) ⊙ B = (Matrix.of fun i (p : Fin r × Fin s) => U i p.1 * U' i p.2) *
      (Matrix.of fun (p : Fin r × Fin s) j => V p.1 j * V' p.2 j) := by
    ext i j
    rw [hB]
    simp only [hadamard_apply, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact (rank_mul_le_card _ _).trans_eq (by simp)
theorem rank_add_le' (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  obtain ⟨r, U, V, hr, rfl⟩ := exists_factor A
  obtain ⟨s, U', V', hs, hB⟩ := exists_factor B
  rw [← hr, ← hs]
  have : U * V + B = (Matrix.of fun i (p : Fin r ⊕ Fin s) => Sum.elim (U i) (U' i) p) *
      (Matrix.of fun (p : Fin r ⊕ Fin s) j => Sum.elim (fun k => V k j) (fun k => V' k j) p) := by
    ext i j
    rw [hB]
    simp [Matrix.mul_apply, Fintype.sum_sum_type]
  rw [this]
  exact (rank_mul_le_card _ _).trans_eq (by simp)
theorem rank_prod_le (e : ℕ) (M : Fin e → Matrix m n K) :
    (Matrix.of fun i j => ∏ k, M k i j).rank ≤ ∏ k, (M k).rank := by
  induction e with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have : (Matrix.of fun (_ : m) (_ : n) => (1 : K)) = vecMulVec (fun _ => 1) (fun _ => 1) := by
      ext; simp [vecMulVec]
    rw [this]; exact rank_vecMulVec_le _ _
  | succ e ih =>
    have : (Matrix.of fun i j => ∏ k : Fin (e + 1), M k i j) =
        M 0 ⊙ Matrix.of fun i j => ∏ k : Fin e, M k.succ i j := by
      ext i j; simp [Fin.prod_univ_succ]
    rw [this, Fin.prod_univ_succ]
    exact (rank_hadamard_le _ _).trans (Nat.mul_le_mul_left _ (ih _))
theorem card_le_rank_sq_of_kill [DecidableEq m] (F : Matrix m m K) (hdiag : ∀ i, F i i ≠ 0)
    (hkill : ∀ i j, i ≠ j → F i j = 0 ∨ F j i = 0) : Fintype.card m ≤ F.rank ^ 2 := by
  classical
  have hD : F ⊙ Fᵀ = diagonal fun i => F i i * F i i := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rcases hkill i j h with h' | h' <;> simp [h, h']
  have h1 : (F ⊙ Fᵀ).rank = Fintype.card m := by
    rw [hD, rank_diagonal]
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun i => mul_ne_zero (hdiag i) (hdiag i))
  have h2 := rank_hadamard_le F Fᵀ
  rw [h1, rank_transpose] at h2
  simpa [sq] using h2
end Field
section Geometry
variable {m n : Type*} [Fintype m] [Fintype n] {D : ℕ}
omit [Fintype m] in
theorem rank_sqdist_le (p : m → EuclideanSpace ℝ (Fin D)) (q : n → EuclideanSpace ℝ (Fin D))
    (f : m → ℝ) (g : n → ℝ) :
    (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j).rank ≤ D + 2 := by
  have : (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j) =
      (Matrix.of fun i (k : Fin D ⊕ Fin 2) =>
        Sum.elim (fun k => -2 * p i k) (fun t => if t = 0 then ‖p i‖ ^ 2 - f i else 1) k) *
      (Matrix.of fun (k : Fin D ⊕ Fin 2) j =>
        Sum.elim (fun k => q j k) (fun t => if t = 0 then 1 else ‖q j‖ ^ 2 - g j) k) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Fin.sum_univ_two]
    rw [@norm_sub_sq_real, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, if_true, if_false, one_ne_zero, mul_one, one_mul]
    have : ∑ x, -2 * (p i).ofLp x * (q j).ofLp x = -(2 * ∑ x, (q j).ofLp x * (p i).ofLp x) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this]; ring
  rw [this]
  exact (rank_mul_le_card _ _).trans_eq (by simp)
theorem card_le_of_kill [DecidableEq m] (p : m → EuclideanSpace ℝ (Fin D)) (e : ℕ)
    (f : Fin e → m → ℝ) (g : Fin e → m → ℝ)
    (hdiag : ∀ i, ∏ k, (‖p i - p i‖ ^ 2 - f k i - g k i) ≠ 0)
    (hkill : ∀ i j, i ≠ j → ∏ k, (‖p i - p j‖ ^ 2 - f k i - g k j) = 0 ∨
      ∏ k, (‖p j - p i‖ ^ 2 - f k j - g k i) = 0) :
    Fintype.card m ≤ (D + 2) ^ (2 * e) := by
  set F : Matrix m m ℝ := Matrix.of fun i j => ∏ k, (‖p i - p j‖ ^ 2 - f k i - g k j)
  have hF : F.rank ≤ (D + 2) ^ e := by
    have := rank_prod_le e (fun k => Matrix.of fun i j => ‖p i - p j‖ ^ 2 - f k i - g k j)
    refine this.trans ?_
    calc ∏ k : Fin e, (Matrix.of fun i j => ‖p i - p j‖ ^ 2 - f k i - g k j).rank
        ≤ ∏ _k : Fin e, (D + 2) := Finset.prod_le_prod' fun k _ => rank_sqdist_le _ _ _ _
      _ = (D + 2) ^ e := by simp
  have := card_le_rank_sq_of_kill F hdiag hkill
  calc Fintype.card m ≤ F.rank ^ 2 := this
    _ ≤ ((D + 2) ^ e) ^ 2 := Nat.pow_le_pow_left hF 2
    _ = (D + 2) ^ (2 * e) := by ring
end Geometry
end E1088
end
section
open Matrix Finset
namespace E1088
variable {K : Type*} [Field K] [DecidableEq K] {α β : Type*} [DecidableEq α] [DecidableEq β]
noncomputable def rankOn (B : α → β → K) (X : Finset α) (Y : Finset β) : ℕ :=
  (Matrix.of fun (i : X) (j : Y) => B i j).rank
omit [DecidableEq K] [DecidableEq α] [DecidableEq β] in
theorem rankOn_mono (B : α → β → K) {X X' : Finset α} {Y Y' : Finset β} (hX : X' ⊆ X)
    (hY : Y' ⊆ Y) : rankOn B X' Y' ≤ rankOn B X Y := by
  unfold rankOn
  have : (Matrix.of fun (i : X') (j : Y') => B i j) =
      (Matrix.of fun (i : X) (j : Y) => B i j).submatrix (fun i => ⟨i.1, hX i.2⟩)
        (fun j => ⟨j.1, hY j.2⟩) := by ext; simp
  rw [this]; exact rank_submatrix_le' _ _ _
def supp (B : α → β → K) (X : Finset α) (Y : Finset β) : Finset (α × β) :=
  (X ×ˢ Y).filter fun p => B p.1 p.2 ≠ 0
theorem card_le_rankOn_of_induced (B : α → β → K) (X : Finset α) (Y : Finset β)
    (F : Finset (α × β)) (hF : F ⊆ X ×ˢ Y) (hind : ∀ p ∈ F, ∀ q ∈ F, B p.1 q.2 ≠ 0 ↔ p = q) :
    #F ≤ rankOn B X Y := by
  classical
  have hmem : ∀ p ∈ F, p.1 ∈ X ∧ p.2 ∈ Y := fun p hp => mem_product.1 (hF hp)
  let G : Matrix F F K := (Matrix.of fun (i : X) (j : Y) => B i j).submatrix
    (fun p => ⟨p.1.1, (hmem p.1 p.2).1⟩) (fun q => ⟨q.1.2, (hmem q.1 q.2).2⟩)
  have hG : G = diagonal fun p => B p.1.1 p.1.2 := by
    ext p q
    by_cases h : p = q
    · subst h; simp [G]
    · have : ¬ (B p.1.1 q.1.2 ≠ 0) := fun h' =>
        h (Subtype.ext ((hind p.1 p.2 q.1 q.2).1 h'))
      simp only [ne_eq, not_not] at this
      simp [G, h, this]
  have h1 : G.rank = #F := by
    rw [hG, rank_diagonal]
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (p := fun p : F => B p.1.1 p.1.2 ≠ 0)
      fun p => ((hind p.1 p.2 p.1 p.2).2 rfl))]
    simp
  rw [← h1]
  exact rank_submatrix_le' _ _ _
omit [DecidableEq α] [DecidableEq β] in
theorem card_supp_eq_sum (B : α → β → K) (X : Finset α) (Y : Finset β) :
    #(supp B X Y) = ∑ i ∈ X, #(Y.filter fun j => B i j ≠ 0) := by
  unfold supp
  rw [card_filter, sum_product]
  exact sum_congr rfl fun i _ => (card_filter _ _).symm
omit [DecidableEq α] [DecidableEq β] in
theorem card_supp_eq_sum' (B : α → β → K) (X : Finset α) (Y : Finset β) :
    #(supp B X Y) = ∑ j ∈ Y, #(X.filter fun i => B i j ≠ 0) := by
  unfold supp
  rw [card_filter, sum_product_right]
  exact sum_congr rfl fun i _ => (card_filter _ _).symm
theorem heavy_rows (B : α → β → K) (X : Finset α) (Y : Finset β) (R : ℕ)
    (hnz : 16 * R * #(supp B X Y) ≤ #X * #Y) (hY : 0 < #Y) :
    4 * #(X.filter fun i => ¬ 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y) ≤ #X := by
  set H := X.filter fun i => ¬ 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y
  have h1 : #H * #Y ≤ 4 * R * #(supp B X Y) := by
    rw [card_supp_eq_sum, mul_sum, card_eq_sum_ones, sum_mul]
    calc ∑ i ∈ H, 1 * #Y ≤ ∑ i ∈ H, 4 * R * #(Y.filter fun j => B i j ≠ 0) :=
          sum_le_sum fun i hi => by
            have := (mem_filter.1 hi).2; omega
      _ ≤ ∑ i ∈ X, 4 * R * #(Y.filter fun j => B i j ≠ 0) :=
          sum_le_sum_of_subset (filter_subset _ _)
  have : 4 * #H * #Y ≤ #X * #Y := by nlinarith
  exact Nat.le_of_mul_le_mul_right this hY
theorem heavy_cols (B : α → β → K) (X : Finset α) (Y : Finset β) (R : ℕ)
    (hnz : 16 * R * #(supp B X Y) ≤ #X * #Y) (hX : 0 < #X) :
    4 * #(Y.filter fun j => ¬ 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X) ≤ #Y := by
  set H := Y.filter fun j => ¬ 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X
  have h1 : #H * #X ≤ 4 * R * #(supp B X Y) := by
    rw [card_supp_eq_sum', mul_sum, card_eq_sum_ones, sum_mul]
    calc ∑ i ∈ H, 1 * #X ≤ ∑ j ∈ H, 4 * R * #(X.filter fun i => B i j ≠ 0) :=
          sum_le_sum fun i hi => by
            have := (mem_filter.1 hi).2; omega
      _ ≤ ∑ j ∈ Y, 4 * R * #(X.filter fun i => B i j ≠ 0) :=
          sum_le_sum_of_subset (filter_subset _ _)
  have : 4 * #H * #X ≤ #Y * #X := by nlinarith
  exact Nat.le_of_mul_le_mul_right this hX
theorem cleaning (B : α → β → K) (X : Finset α) (Y : Finset β) (R : ℕ) (hR : 1 ≤ R)
    (hrank : rankOn B X Y ≤ R) (hnz : 16 * R * #(supp B X Y) ≤ #X * #Y) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 2 * #X' ∧ #Y ≤ 2 * #Y' ∧ ∀ i ∈ X', ∀ j ∈ Y', B i j = 0 := by
  classical
  rcases Nat.eq_zero_or_pos #X with hX | hX
  · refine ⟨X, subset_refl _, Y, subset_refl _, by omega, by omega, fun i hi => ?_⟩
    simp_all
  rcases Nat.eq_zero_or_pos #Y with hY | hY
  · refine ⟨X, subset_refl _, Y, subset_refl _, by omega, by omega, fun i _ j hj => ?_⟩
    simp_all
  set X0 := X.filter fun i => 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y with hX0
  set Y0 := Y.filter fun j => 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X with hY0
  have hX0c : 3 * #X ≤ 4 * #X0 := by
    have h := heavy_rows B X Y R hnz hY
    have := card_filter_add_card_filter_not (s := X) (fun i => 4 * R * #(Y.filter fun j => B i j ≠ 0) ≤ #Y)
    rw [hX0]; omega
  have hY0c : 3 * #Y ≤ 4 * #Y0 := by
    have h := heavy_cols B X Y R hnz hX
    have := card_filter_add_card_filter_not (s := Y) (fun j => 4 * R * #(X.filter fun i => B i j ≠ 0) ≤ #X)
    rw [hY0]; omega
  set Mset := (X0 ×ˢ Y0).powerset.filter
    (fun F => ∀ p ∈ F, ∀ q ∈ F, B p.1 q.2 ≠ 0 ↔ p = q) with hMset
  have hne : Mset.Nonempty := ⟨∅, by simp [hMset]⟩
  obtain ⟨F, hFM, hFmax⟩ := exists_max_image Mset (fun F => #F) hne
  obtain ⟨hFsub, hFind⟩ := mem_filter.1 hFM
  rw [mem_powerset] at hFsub
  have hFsub' : F ⊆ X ×ˢ Y := hFsub.trans (product_subset_product (filter_subset _ _)
    (filter_subset _ _))
  have hFR : #F ≤ R := (card_le_rankOn_of_induced B X Y F hFsub' hFind).trans hrank
  set NC := X0.filter fun i => ∃ q ∈ F, B i q.2 ≠ 0 with hNC
  set NR := Y0.filter fun j => ∃ p ∈ F, B p.1 j ≠ 0 with hNR
  have hNCc : 4 * #NC ≤ #X := by
    have hsub : NC ⊆ F.biUnion fun q => X.filter fun i => B i q.2 ≠ 0 := by
      intro i hi
      obtain ⟨hi0, q, hq, hb⟩ := mem_filter.1 hi
      exact mem_biUnion.2 ⟨q, hq, mem_filter.2 ⟨(mem_filter.1 hi0).1, hb⟩⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ q ∈ F, 4 * R * #(X.filter fun i => B i q.2 ≠ 0) ≤ #X := fun q hq =>
      (mem_filter.1 (mem_product.1 (hFsub hq)).2).2
    have h3 : 4 * R * #NC ≤ #F * #X := by
      calc 4 * R * #NC ≤ 4 * R * ∑ q ∈ F, #(X.filter fun i => B i q.2 ≠ 0) :=
            Nat.mul_le_mul_left _ h1
        _ = ∑ q ∈ F, 4 * R * #(X.filter fun i => B i q.2 ≠ 0) := by rw [mul_sum]
        _ ≤ ∑ q ∈ F, #X := sum_le_sum h2
        _ = #F * #X := by simp
    have h4 : 4 * R * #NC ≤ R * #X := h3.trans (Nat.mul_le_mul_right _ hFR)
    have : R * (4 * #NC) ≤ R * #X := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hNRc : 4 * #NR ≤ #Y := by
    have hsub : NR ⊆ F.biUnion fun p => Y.filter fun j => B p.1 j ≠ 0 := by
      intro j hj
      obtain ⟨hj0, p, hp, hb⟩ := mem_filter.1 hj
      exact mem_biUnion.2 ⟨p, hp, mem_filter.2 ⟨(mem_filter.1 hj0).1, hb⟩⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ p ∈ F, 4 * R * #(Y.filter fun j => B p.1 j ≠ 0) ≤ #Y := fun p hp =>
      (mem_filter.1 (mem_product.1 (hFsub hp)).1).2
    have h3 : 4 * R * #NR ≤ #F * #Y := by
      calc 4 * R * #NR ≤ 4 * R * ∑ p ∈ F, #(Y.filter fun j => B p.1 j ≠ 0) :=
            Nat.mul_le_mul_left _ h1
        _ = ∑ p ∈ F, 4 * R * #(Y.filter fun j => B p.1 j ≠ 0) := by rw [mul_sum]
        _ ≤ ∑ p ∈ F, #Y := sum_le_sum h2
        _ = #F * #Y := by simp
    have h4 : 4 * R * #NR ≤ R * #Y := h3.trans (Nat.mul_le_mul_right _ hFR)
    have : R * (4 * #NR) ≤ R * #Y := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  refine ⟨X0 \ NC, sdiff_subset.trans (filter_subset _ _), Y0 \ NR,
    sdiff_subset.trans (filter_subset _ _), ?_, ?_, ?_⟩
  · have := le_card_sdiff NC X0; omega
  · have := le_card_sdiff NR Y0; omega
  · intro i hi j hj
    by_contra hb
    obtain ⟨hi0, hiN⟩ := mem_sdiff.1 hi
    obtain ⟨hj0, hjN⟩ := mem_sdiff.1 hj
    have hiq : ∀ q ∈ F, B i q.2 = 0 := fun q hq => by
      by_contra h; exact hiN (mem_filter.2 ⟨hi0, q, hq, h⟩)
    have hjp : ∀ p ∈ F, B p.1 j = 0 := fun p hp => by
      by_contra h; exact hjN (mem_filter.2 ⟨hj0, p, hp, h⟩)
    have hnot : (i, j) ∉ F := fun h => hb (hiq _ h)
    have hmem : insert (i, j) F ∈ Mset := by
      refine mem_filter.2 ⟨mem_powerset.2 (insert_subset (mem_product.2 ⟨hi0, hj0⟩) hFsub), ?_⟩
      intro p hp q hq
      rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
      · simpa using hb
      · simp only [hiq q hq, ne_eq, not_true_eq_false, false_iff]
        rintro rfl; exact hnot hq
      · simp only [hjp p hp, ne_eq, not_true_eq_false, false_iff]
        rintro rfl; exact hnot hp
      · exact hFind p hp q hq
    have := hFmax _ hmem
    rw [card_insert_of_notMem hnot] at this
    omega
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem rank_sqdist_le_affine {m n : Type*} [Fintype m] [Fintype n] (X : Finset (ℝ^d)) (D : ℕ)
    (hD : affDim X ≤ D) (p : m → ℝ^d) (q : n → ℝ^d) (hp : ∀ i, p i ∈ X) (hq : ∀ j, q j ∈ X)
    (f : m → ℝ) (g : n → ℝ) :
    (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j).rank ≤ D + 2 := by
  classical
  rcases X.eq_empty_or_nonempty with hX | ⟨x0, hx0⟩
  ·
    rcases isEmpty_or_nonempty m with hm | ⟨⟨i⟩⟩
    · exact (Matrix.rank_le_card_height _).trans (by simp)
    · exact absurd (hp i) (by simp [hX])
  set V := vectorSpan ℝ (X : Set (ℝ^d)) with hV
  set b := stdOrthonormalBasis ℝ V with hb
  set k := Module.finrank ℝ V with hk
  have hkD : k ≤ D := hD
  have hmem : ∀ y ∈ X, y - x0 ∈ V := fun y hy =>
    vsub_mem_vectorSpan ℝ (mem_coe.2 hy) (mem_coe.2 hx0)
  set a : m → V := fun i => ⟨p i - x0, hmem _ (hp i)⟩
  set c : n → V := fun j => ⟨q j - x0, hmem _ (hq j)⟩
  have hinner : ∀ i j, inner ℝ (p i - x0) (q j - x0) =
      ∑ t : Fin k, inner ℝ (a i) (b t) * inner ℝ (b t) (c j) := by
    intro i j
    rw [b.sum_inner_mul_inner (a i) (c j)]
    rfl
  have : (Matrix.of fun i j => ‖p i - q j‖ ^ 2 - f i - g j) =
      (Matrix.of fun i (t : Fin k ⊕ Fin 2) => Sum.elim (fun t => -2 * inner ℝ (a i) (b t))
        (fun t => if t = 0 then ‖p i - x0‖ ^ 2 - f i else 1) t) *
      (Matrix.of fun (t : Fin k ⊕ Fin 2) j => Sum.elim (fun t => inner ℝ (b t) (c j))
        (fun t => if t = 0 then 1 else ‖q j - x0‖ ^ 2 - g j) t) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Fin.sum_univ_two, Fin.isValue, if_true, one_ne_zero, if_false, mul_one,
      one_mul]
    have e : p i - q j = (p i - x0) - (q j - x0) := by abel
    rw [e, norm_sub_sq_real, hinner i j]
    have h2 : ∑ t : Fin k, -2 * inner ℝ (a i) (b t) * inner ℝ (b t) (c j) =
        -2 * ∑ t : Fin k, inner ℝ (a i) (b t) * inner ℝ (b t) (c j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h2]
    ring
  rw [this]
  exact (rank_mul_le_card _ _).trans (by simp; omega)
end E1088
end
section
open Finset
namespace E1088
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def degIn (s : Finset V) (v : V) : ℕ := #(s.filter (G.Adj v))
theorem degIn_mono {s s' : Finset V} (h : s' ⊆ s) (v : V) : degIn G s' v ≤ degIn G s v :=
  card_le_card (filter_subset_filter _ h)
theorem caro_wei_harmonic : ∀ (s : Finset V), ∃ t ⊆ s, (t : Set V).Pairwise (fun a b => ¬ G.Adj a b) ∧
    ∑ v ∈ s, (1 : ℝ) / (degIn G s v + 1) ≤ #t := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, subset_refl _, by simp, by simp⟩
    obtain ⟨v, hv, hmin⟩ := exists_min_image s (degIn G s) hne
    set Nv := s.filter (G.Adj v) with hNv
    set s' := s \ insert v Nv with hs'
    have hsub : s' ⊂ s := by
      refine ⟨sdiff_subset, fun h => ?_⟩
      have := h hv
      simp [hs'] at this
    obtain ⟨t', ht's, hind, hsum⟩ := ih s' hsub
    have hvt' : v ∉ t' := fun h => by
      have := ht's h; simp [hs'] at this
    refine ⟨insert v t', insert_subset hv (ht's.trans sdiff_subset), ?_, ?_⟩
    · rw [coe_insert]
      refine hind.insert fun b hb hvb => ?_
      have hb' := ht's hb
      simp only [hs', mem_sdiff, mem_insert, hNv, mem_filter, not_or, not_and] at hb'
      constructor
      · intro hadj; exact hb'.2.2 hb'.1 hadj
      · intro hadj; exact hb'.2.2 hb'.1 (G.adj_symm hadj)
    · rw [card_insert_of_notMem hvt', Nat.cast_add, Nat.cast_one]
      have hsplit : s = insert v Nv ∪ s' := by
        rw [hs', union_sdiff_of_subset (insert_subset hv (filter_subset _ _))]
      have hdisj : Disjoint (insert v Nv) s' := disjoint_sdiff
      rw [hsplit, sum_union hdisj]
      rw [← hsplit]
      have hvN : v ∉ Nv := fun h => G.loopless.irrefl v (mem_filter.1 h).2
      have h1 : ∑ u ∈ insert v Nv, (1 : ℝ) / (degIn G s u + 1) ≤ 1 := by
        calc ∑ u ∈ insert v Nv, (1 : ℝ) / (degIn G s u + 1)
            ≤ ∑ _u ∈ insert v Nv, (1 : ℝ) / (degIn G s v + 1) := by
              refine sum_le_sum fun u hu => ?_
              have hus : u ∈ s := by
                rcases mem_insert.1 hu with rfl | hu
                · exact hv
                · exact (mem_filter.1 hu).1
              apply one_div_le_one_div_of_le (by positivity)
              have := hmin u hus
              exact_mod_cast Nat.add_le_add_right this 1
          _ = 1 := by
              rw [sum_const, card_insert_of_notMem hvN, nsmul_eq_mul]
              have : (degIn G s v : ℝ) = #Nv := rfl
              rw [this]; push_cast
              exact mul_one_div_cancel (Nat.cast_add_one_ne_zero _)
      have h2 : ∑ u ∈ s', (1 : ℝ) / (degIn G s u + 1) ≤
          ∑ u ∈ s', (1 : ℝ) / (degIn G s' u + 1) := by
        refine sum_le_sum fun u _ => ?_
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (degIn_mono G sdiff_subset u) 1
      linarith
theorem caro_wei (s : Finset V) : ∃ t ⊆ s, (t : Set V).Pairwise (fun a b => ¬ G.Adj a b) ∧
    ((#s : ℝ)) ^ 2 ≤ #t * ∑ v ∈ s, ((degIn G s v : ℝ) + 1) := by
  obtain ⟨t, hts, hind, hsum⟩ := caro_wei_harmonic G s
  refine ⟨t, hts, hind, ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpos : 0 < ∑ v ∈ s, ((degIn G s v : ℝ) + 1) :=
    sum_pos (fun v _ => by positivity) hne
  have hCS := sq_sum_div_le_sum_sq_div s (fun _ => (1 : ℝ))
    (g := fun v => (degIn G s v : ℝ) + 1) (fun v _ => by positivity)
  simp only [sum_const, nsmul_eq_mul, mul_one, one_pow] at hCS
  have : (#s : ℝ) ^ 2 / ∑ v ∈ s, ((degIn G s v : ℝ) + 1) ≤ #t := hCS.trans hsum
  rwa [div_le_iff₀ hpos] at this
end E1088
end
section
open Finset
namespace E1088
variable {ι : Type*} [DecidableEq ι]
theorem kill_bound (W : Finset ι) (F : ι → ι → ℝ) (m Δ : ℕ) (hrank : rankOn F W W ≤ m)
    (hdiag : ∀ b ∈ W, F b b ≠ 0)
    (hsurv : ∀ b ∈ W, #(W.filter fun x => x ≠ b ∧ F b x ≠ 0) ≤ Δ) :
    #W ≤ m ^ 2 * (Δ + 1) := by
  classical
  let G : SimpleGraph ι := SimpleGraph.fromRel fun a b => F a b ≠ 0 ∧ F b a ≠ 0
  have hdeg : ∀ b ∈ W, degIn G W b ≤ Δ := by
    intro b hb
    refine (card_le_card fun x hx => ?_).trans (hsurv b hb)
    obtain ⟨hxW, hadj⟩ := mem_filter.1 hx
    rw [SimpleGraph.fromRel_adj] at hadj
    refine mem_filter.2 ⟨hxW, hadj.1.symm, ?_⟩
    rcases hadj.2 with h | h
    · exact h.1
    · exact h.2
  obtain ⟨I, hIW, hind, hcw⟩ := caro_wei G W
  have h1 : (#W : ℝ) ≤ #I * (Δ + 1) := by
    rcases W.eq_empty_or_nonempty with hW | hW
    · simp only [hW, card_empty, Nat.cast_zero]; positivity
    have hsum : ∑ v ∈ W, ((degIn G W v : ℝ) + 1) ≤ #W * ((Δ : ℝ) + 1) := by
      calc ∑ v ∈ W, ((degIn G W v : ℝ) + 1) ≤ ∑ _v ∈ W, ((Δ : ℝ) + 1) :=
            sum_le_sum fun v hv => by have := hdeg v hv; push_cast; exact_mod_cast
              (show degIn G W v + 1 ≤ Δ + 1 by omega)
        _ = #W * ((Δ : ℝ) + 1) := by rw [sum_const, nsmul_eq_mul]
    have hWpos : (0 : ℝ) < #W := by exact_mod_cast card_pos.2 hW
    have : (#W : ℝ) ^ 2 ≤ #I * (#W * ((Δ : ℝ) + 1)) :=
      hcw.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    nlinarith
  have h2 : #I ≤ m ^ 2 := by
    have hH := card_le_rank_sq_of_kill (Matrix.of fun (i : I) (j : I) => F i j)
      (fun i => hdiag i (hIW i.2)) (fun i j hij => by
        by_contra h
        push Not at h
        have hne : (i : ι) ≠ j := fun e => hij (Subtype.ext e)
        exact hind i.2 j.2 hne ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨h.1, h.2⟩⟩))
    have hr : (Matrix.of fun (i : I) (j : I) => F i j).rank ≤ m :=
      (rankOn_mono F hIW hIW).trans hrank
    simp only [Fintype.card_coe] at hH
    exact hH.trans (Nat.pow_le_pow_left hr 2)
  have h3 : ((#I : ℕ) : ℝ) ≤ (m ^ 2 : ℕ) := by exact_mod_cast h2
  have : (#W : ℝ) ≤ (m ^ 2 : ℕ) * ((Δ : ℝ) + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  exact_mod_cast this
open scoped EuclideanGeometry
theorem kill_bound_geometric {D : ℕ} (W : Finset ι) (p : ι → EuclideanSpace ℝ (Fin D)) (e Δ : ℕ)
    (f g : Fin e → ι → ℝ)
    (hdiag : ∀ b ∈ W, ∏ k, (‖p b - p b‖ ^ 2 - f k b - g k b) ≠ 0)
    (hsurv : ∀ b ∈ W, #(W.filter fun x => x ≠ b ∧
      ∏ k, (‖p b - p x‖ ^ 2 - f k b - g k x) ≠ 0) ≤ Δ) :
    #W ≤ ((D + 2) ^ e) ^ 2 * (Δ + 1) := by
  refine kill_bound W (fun b x => ∏ k, (‖p b - p x‖ ^ 2 - f k b - g k x)) ((D + 2) ^ e) Δ ?_
    hdiag hsurv
  unfold rankOn
  have := rank_prod_le e (fun k => Matrix.of fun (i : W) (j : W) =>
    ‖p i - p j‖ ^ 2 - f k i - g k j)
  refine this.trans ?_
  calc ∏ k : Fin e, (Matrix.of fun (i : W) (j : W) => ‖p i - p j‖ ^ 2 - f k i - g k j).rank
      ≤ ∏ _k : Fin e, (D + 2) := Finset.prod_le_prod' fun k _ =>
        rank_sqdist_le (fun i : W => p i) (fun j : W => p j) (fun i : W => f k i)
          (fun j : W => g k j)
    _ = (D + 2) ^ e := by simp
end E1088
end
section
open Finset
namespace E1088
variable {α β : Type*}
theorem card_le_of_cover3 [DecidableEq α] {X A B C : Finset α}
    (h : ∀ x ∈ X, x ∈ A ∨ x ∈ B ∨ x ∈ C) : #X ≤ #A + #B + #C := by
  have hsub : X ⊆ A ∪ B ∪ C := by
    intro x hx
    rcases h x hx with h | h | h <;> simp [h]
  calc #X ≤ #(A ∪ B ∪ C) := card_le_card hsub
    _ ≤ #(A ∪ B) + #C := card_union_le _ _
    _ ≤ #A + #B + #C := by have := card_union_le A B; omega
theorem half_split (X : Finset α) (p : α → Prop) [DecidablePred p] :
    #X ≤ 2 * #(X.filter p) ∨ #X ≤ 2 * #(X.filter fun x => ¬ p x) := by
  have := card_filter_add_card_filter_not (s := X) p
  omega
theorem exists_median (X : Finset α) (hX : X.Nonempty) (a : α → ℝ) :
    ∃ θ, 2 * #(X.filter fun x => a x < θ) ≤ #X ∧ 2 * #(X.filter fun x => θ < a x) ≤ #X := by
  classical
  set V := X.filter fun x => 2 * #(X.filter fun y => a y < a x) ≤ #X with hV
  have hVne : V.Nonempty := by
    obtain ⟨x0, hx0, hmin⟩ := exists_min_image X a hX
    refine ⟨x0, mem_filter.2 ⟨hx0, ?_⟩⟩
    have : X.filter (fun y => a y < a x0) = ∅ :=
      filter_eq_empty_iff.2 fun y hy => not_lt.2 (hmin y hy)
    simp [this]
  obtain ⟨xs, hxs, hmax⟩ := exists_max_image V a hVne
  refine ⟨a xs, (mem_filter.1 hxs).2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hne : (X.filter fun x => a xs < a x).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; rw [h] at hcon; simp at hcon
  obtain ⟨y, hy, hymin⟩ := exists_min_image _ a hne
  obtain ⟨hyX, hya⟩ := mem_filter.1 hy
  have heq : X.filter (fun z => a z < a y) = X.filter (fun z => ¬ a xs < a z) := by
    ext z
    simp only [mem_filter, not_lt]
    constructor
    · rintro ⟨hz, hzy⟩
      refine ⟨hz, ?_⟩
      by_contra h
      push Not at h
      exact absurd (hymin z (mem_filter.2 ⟨hz, h⟩)) (not_le.2 hzy)
    · rintro ⟨hz, hzx⟩
      exact ⟨hz, lt_of_le_of_lt hzx hya⟩
  have hsum := card_filter_add_card_filter_not (s := X) (fun z => a xs < a z)
  have hyV : y ∈ V := by
    refine mem_filter.2 ⟨hyX, ?_⟩
    rw [heq]; omega
  exact absurd (hmax y hyV) (not_le.2 hya)
theorem card_trichotomy (X : Finset α) (a : α → ℝ) (θ : ℝ) :
    #(X.filter fun x => a x < θ) + #(X.filter fun x => a x = θ) +
      #(X.filter fun x => θ < a x) = #X := by
  classical
  have e1 := card_filter_add_card_filter_not (s := X) (fun x => a x < θ)
  have e2 := card_filter_add_card_filter_not (s := X.filter fun x => ¬ a x < θ)
    (fun x => a x = θ)
  simp only [filter_filter] at e2
  have h1 : X.filter (fun x => ¬ a x < θ ∧ a x = θ) = X.filter (fun x => a x = θ) :=
    filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨by simp [h], h⟩⟩
  have h2 : X.filter (fun x => ¬ a x < θ ∧ ¬ a x = θ) = X.filter (fun x => θ < a x) :=
    filter_congr fun x _ => ⟨fun h => lt_of_le_of_ne (not_lt.1 h.1) (Ne.symm h.2),
      fun h => ⟨not_lt.2 h.le, h.ne'⟩⟩
  rw [h1, h2] at e2
  omega
theorem lemmaA (X : Finset α) (Y : Finset β) (hX : X.Nonempty) (a : α → ℝ) (b : β → ℝ) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 2 * #Y' ∧
      ((∃ c, ∀ x ∈ X', a x = c) ∨
       (∃ θ, (∀ x ∈ X', θ < a x) ∧ ∀ w ∈ Y', b w ≤ θ) ∨
       (∃ θ, (∀ x ∈ X', a x < θ) ∧ ∀ w ∈ Y', θ ≤ b w)) := by
  classical
  obtain ⟨θ, h1, h2⟩ := exists_median X hX a
  have h3 := card_trichotomy X a θ
  by_cases hc : #X ≤ 4 * #(X.filter fun x => a x = θ)
  · exact ⟨_, filter_subset _ _, Y, subset_refl _, hc, by omega,
      Or.inl ⟨θ, fun x hx => (mem_filter.1 hx).2⟩⟩
  rcases half_split Y (fun w => b w ≤ θ) with hY | hY
  · refine ⟨X.filter fun x => θ < a x, filter_subset _ _, _, filter_subset _ _, by omega, hY,
      Or.inr (Or.inl ⟨θ, fun x hx => (mem_filter.1 hx).2, fun w hw => (mem_filter.1 hw).2⟩)⟩
  · refine ⟨X.filter fun x => a x < θ, filter_subset _ _, _, filter_subset _ _, by omega, hY,
      Or.inr (Or.inr ⟨θ, fun x hx => (mem_filter.1 hx).2,
        fun w hw => le_of_lt (not_le.1 (mem_filter.1 hw).2)⟩)⟩
theorem lemmaB (X : Finset α) (Y : Finset β) (hY : Y.Nonempty) (D : α → ℝ) (E : β → ℝ)
    (hD : ∀ x ∈ X, 0 < D x) (_hE : ∀ w ∈ Y, 0 ≤ E w) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 4 * #Y' ∧
      ((∀ x ∈ X', ∀ w ∈ Y', 2 * E w ≤ D x) ∨
       (∀ x ∈ X', ∀ w ∈ Y', 2 * D x ≤ E w) ∨
       (∃ s > 0, (∀ x ∈ X', s / 4 < D x ∧ D x < 4 * s) ∧
          ∀ w ∈ Y', s / 4 < E w ∧ E w < 4 * s)) := by
  classical
  obtain ⟨s, h1, h2⟩ := exists_median Y hY E
  have h3 := card_trichotomy Y E s
  have hle : #Y ≤ 2 * #(Y.filter fun w => E w ≤ s) := by
    have := card_le_of_cover3 (X := Y) (A := Y.filter fun w => E w ≤ s)
      (B := Y.filter fun w => s < E w) (C := ∅) (fun w hw => by
        rcases le_or_gt (E w) s with h | h
        · exact Or.inl (mem_filter.2 ⟨hw, h⟩)
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hw, h⟩)))
    simp at this; omega
  have hge : #Y ≤ 2 * #(Y.filter fun w => s ≤ E w) := by
    have := card_le_of_cover3 (X := Y) (A := Y.filter fun w => s ≤ E w)
      (B := Y.filter fun w => E w < s) (C := ∅) (fun w hw => by
        rcases le_or_gt s (E w) with h | h
        · exact Or.inl (mem_filter.2 ⟨hw, h⟩)
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hw, h⟩)))
    simp at this; omega
  rcases le_or_gt s 0 with hs | hs
  · refine ⟨X, subset_refl _, Y.filter fun w => E w ≤ s, filter_subset _ _, by omega, by omega,
      Or.inl ?_⟩
    intro x hx w hw
    have := (mem_filter.1 hw).2
    have := hD x hx
    linarith
  by_cases hA : #X ≤ 4 * #(X.filter fun x => 2 * s ≤ D x)
  · refine ⟨_, filter_subset _ _, Y.filter fun w => E w ≤ s, filter_subset _ _, hA, by omega,
      Or.inl ?_⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2; have := (mem_filter.1 hw).2; linarith
  by_cases hB : #X ≤ 4 * #(X.filter fun x => D x ≤ s / 2)
  · refine ⟨_, filter_subset _ _, Y.filter fun w => s ≤ E w, filter_subset _ _, hB, by omega,
      Or.inr (Or.inl ?_)⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2; have := (mem_filter.1 hw).2; linarith
  set R1 := X.filter fun x => s / 2 < D x ∧ D x < 2 * s with hR1
  have hR1c : #X ≤ 2 * #R1 := by
    have := card_le_of_cover3 (X := X) (A := R1) (B := X.filter fun x => 2 * s ≤ D x)
      (C := X.filter fun x => D x ≤ s / 2) (fun x hx => by
        by_cases h1 : 2 * s ≤ D x
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hx, h1⟩))
        by_cases h2 : D x ≤ s / 2
        · exact Or.inr (Or.inr (mem_filter.2 ⟨hx, h2⟩))
        exact Or.inl (mem_filter.2 ⟨hx, not_le.1 h2, not_le.1 h1⟩))
    omega
  by_cases hC : #Y ≤ 4 * #(Y.filter fun w => E w ≤ s / 4)
  · refine ⟨R1, filter_subset _ _, _, filter_subset _ _, by omega, hC, Or.inl ?_⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2.1; have := (mem_filter.1 hw).2; linarith
  by_cases hC' : #Y ≤ 4 * #(Y.filter fun w => 4 * s ≤ E w)
  · refine ⟨R1, filter_subset _ _, _, filter_subset _ _, by omega, hC', Or.inr (Or.inl ?_)⟩
    intro x hx w hw
    have := (mem_filter.1 hx).2.2; have := (mem_filter.1 hw).2; linarith
  set C1 := Y.filter fun w => s / 4 < E w ∧ E w < 4 * s with hC1
  have hC1c : #Y ≤ 2 * #C1 := by
    have := card_le_of_cover3 (X := Y) (A := C1) (B := Y.filter fun w => E w ≤ s / 4)
      (C := Y.filter fun w => 4 * s ≤ E w) (fun w hw => by
        by_cases h1 : E w ≤ s / 4
        · exact Or.inr (Or.inl (mem_filter.2 ⟨hw, h1⟩))
        by_cases h2 : 4 * s ≤ E w
        · exact Or.inr (Or.inr (mem_filter.2 ⟨hw, h2⟩))
        exact Or.inl (mem_filter.2 ⟨hw, not_le.1 h1, not_le.1 h2⟩))
    omega
  refine ⟨R1, filter_subset _ _, C1, filter_subset _ _, by omega, by omega,
    Or.inr (Or.inr ⟨s, hs, fun x hx => ?_, fun w hw => (mem_filter.1 hw).2⟩)⟩
  have := (mem_filter.1 hx).2
  constructor <;> linarith [this.1, this.2]
end E1088
end
section
open Finset
namespace E1088
inductive TF (α β : Type*) where
  | row (a : α → ℝ)
  | col (b : β → ℝ)
namespace TF
variable {α β : Type*}
def eval : TF α β → α → β → ℝ
  | row a => fun x _ => a x
  | col b => fun _ w => b w
def rp : TF α β → α → ℝ
  | row a => a
  | col _ => 0
def cp : TF α β → β → ℝ
  | row _ => 0
  | col b => b
theorem eval_eq (t : TF α β) (x : α) (w : β) : t.eval x w = t.rp x + t.cp w := by
  cases t <;> simp [eval, rp, cp]
end TF
variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
def Covers (M : α → β → ℝ) (τ : ι → TF α β) (S : Finset ι) (X : Finset α) (Y : Finset β) :
    Prop :=
  ∀ x ∈ X, ∀ w ∈ Y, ∃ t ∈ S, M x w = (τ t).eval x w
theorem Covers.mono {M : α → β → ℝ} {τ : ι → TF α β} {S : Finset ι} {X X' : Finset α}
    {Y Y' : Finset β} (h : Covers M τ S X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    Covers M τ S X' Y' := fun x hx w hw => h x (hX hx) w (hY hw)
def Comparable (g : α → β → ℝ) (c : ℝ) (X : Finset α) (Y : Finset β) : Prop :=
  ∃ qr : α → ℝ, ∃ qc : β → ℝ, (∀ x ∈ X, 0 < qr x) ∧ (∀ w ∈ Y, 0 < qc w) ∧
    ∀ x ∈ X, ∀ w ∈ Y, qr x * qc w ≤ |g x w| ∧ |g x w| ≤ c * (qr x * qc w)
theorem Comparable.mono {g : α → β → ℝ} {c : ℝ} {X X' : Finset α} {Y Y' : Finset β}
    (h : Comparable g c X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : Comparable g c X' Y' := by
  obtain ⟨qr, qc, h1, h2, h3⟩ := h
  exact ⟨qr, qc, fun x hx => h1 x (hX hx), fun w hw => h2 w (hY hw),
    fun x hx w hw => h3 x (hX hx) w (hY hw)⟩
def StrictSign (g : α → β → ℝ) (X : Finset α) (Y : Finset β) : Prop :=
  (∀ x ∈ X, ∀ w ∈ Y, 0 < g x w) ∨ (∀ x ∈ X, ∀ w ∈ Y, g x w < 0)
theorem StrictSign.mono {g : α → β → ℝ} {X X' : Finset α} {Y Y' : Finset β}
    (h : StrictSign g X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : StrictSign g X' Y' := by
  rcases h with h | h
  · exact Or.inl fun x hx w hw => h x (hX hx) w (hY hw)
  · exact Or.inr fun x hx w hw => h x (hX hx) w (hY hw)
theorem sum_comparable (X : Finset α) (Y : Finset β) (hY : Y.Nonempty) (D : α → ℝ)
    (E : β → ℝ) (hD : ∀ x ∈ X, 0 < D x) (hE : ∀ w ∈ Y, 0 ≤ E w) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 4 * #Y' ∧
      Comparable (fun x w => D x + E w) 32 X' Y' := by
  obtain ⟨X', hX', Y', hY', h1, h2, h⟩ := lemmaB X Y hY D E hD hE
  refine ⟨X', hX', Y', hY', h1, h2, ?_⟩
  rcases X'.eq_empty_or_nonempty with hXe | hX0
  · exact ⟨fun _ => 1, fun _ => 1, fun _ _ => one_pos, fun _ _ => one_pos, by simp [hXe]⟩
  rcases h with h | h | ⟨s, hs, hDs, hEs⟩
  · refine ⟨D, fun _ => 1, fun x hx => hD x (hX' hx), fun _ _ => one_pos, fun x hx w hw => ?_⟩
    have := hD x (hX' hx); have := hE w (hY' hw); have := h x hx w hw
    rw [abs_of_pos (by linarith)]
    constructor <;> nlinarith
  · refine ⟨fun _ => 1, E, fun _ _ => one_pos, fun w hw => ?_, fun x hx w hw => ?_⟩
    · obtain ⟨x, hx⟩ := hX0
      have := hD x (hX' hx); have := h x hx w hw; linarith
    · have := hD x (hX' hx); have := hE w (hY' hw); have := h x hx w hw
      rw [abs_of_pos (by linarith)]
      constructor <;> nlinarith
  · refine ⟨fun _ => s / 4, fun _ => 1, fun _ _ => by positivity, fun _ _ => one_pos,
      fun x hx w hw => ?_⟩
    have := hDs x hx; have := hEs w hw
    rw [abs_of_pos (by linarith)]
    constructor <;> nlinarith
theorem three_split (X : Finset α) (g : α → ℝ) :
    #X ≤ 3 * #(X.filter fun x => g x < 0) ∨ #X ≤ 3 * #(X.filter fun x => g x = 0) ∨
      #X ≤ 3 * #(X.filter fun x => 0 < g x) := by
  have := card_trichotomy X g 0
  omega
theorem comparable_row (X : Finset α) (Y : Finset β) (g : α → ℝ) (hg : ∀ x ∈ X, g x ≠ 0) :
    Comparable (fun x _ => g x) 32 X Y :=
  ⟨fun x => |g x|, fun _ => 1, fun x hx => abs_pos.2 (hg x hx), fun _ _ => one_pos,
    fun x hx w hw => by
      have := abs_nonneg (g x)
      simp only [mul_one]; constructor <;> linarith⟩
theorem comparable_col (X : Finset α) (Y : Finset β) (g : β → ℝ) (hg : ∀ w ∈ Y, g w ≠ 0) :
    Comparable (fun _ w => g w) 32 X Y :=
  ⟨fun _ => 1, fun w => |g w|, fun _ _ => one_pos, fun w hw => abs_pos.2 (hg w hw),
    fun x hx w hw => by
      have := abs_nonneg (g w)
      simp only [one_mul]; constructor <;> linarith⟩
theorem gap_lemma (X : Finset α) (Y : Finset β) (hX : X.Nonempty) (hY : Y.Nonempty)
    (A : α → ℝ) (B : β → ℝ) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 16 * #X' ∧ #Y ≤ 16 * #Y' ∧
      ((∀ x ∈ X', ∀ w ∈ Y', A x + B w = 0) ∨
        (StrictSign (fun x w => A x + B w) X' Y' ∧
          Comparable (fun x w => A x + B w) 32 X' Y')) := by
  obtain ⟨X1, hX1, Y1, hY1, c1, c2, h⟩ := lemmaA X Y hX A (fun w => -B w)
  have hY1ne : Y1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hY; omega
  rcases h with ⟨c, hc⟩ | ⟨θ, hA, hB⟩ | ⟨θ, hA, hB⟩
  ·
    rcases three_split Y1 (fun w => c + B w) with h | h | h
    · refine ⟨X1, hX1, Y1.filter fun w => c + B w < 0, (filter_subset _ _).trans hY1, by omega,
        by omega, Or.inr ⟨?_, ?_⟩⟩
      · exact Or.inr fun x hx w hw => by show A x + B w < 0; rw [hc x hx]; exact (mem_filter.1 hw).2
      · obtain ⟨qr, qc, h1, h2, h3⟩ := comparable_col X1 (Y1.filter fun w => c + B w < 0)
          (fun w => c + B w) (fun w hw => (mem_filter.1 hw).2.ne)
        exact ⟨qr, qc, h1, h2, fun x hx w hw => by
          show _ ≤ |A x + B w| ∧ |A x + B w| ≤ _; rw [hc x hx]; exact h3 x hx w hw⟩
    · refine ⟨X1, hX1, Y1.filter fun w => c + B w = 0, (filter_subset _ _).trans hY1, by omega,
        by omega, Or.inl ?_⟩
      intro x hx w hw; rw [hc x hx]; exact (mem_filter.1 hw).2
    · refine ⟨X1, hX1, Y1.filter fun w => 0 < c + B w, (filter_subset _ _).trans hY1, by omega,
        by omega, Or.inr ⟨?_, ?_⟩⟩
      · exact Or.inl fun x hx w hw => by show 0 < A x + B w; rw [hc x hx]; exact (mem_filter.1 hw).2
      · obtain ⟨qr, qc, h1, h2, h3⟩ := comparable_col X1 (Y1.filter fun w => 0 < c + B w)
          (fun w => c + B w) (fun w hw => (mem_filter.1 hw).2.ne')
        exact ⟨qr, qc, h1, h2, fun x hx w hw => by
          show _ ≤ |A x + B w| ∧ |A x + B w| ≤ _; rw [hc x hx]; exact h3 x hx w hw⟩
  ·
    obtain ⟨X2, hX2, Y2, hY2, d1, d2, hcmp⟩ := sum_comparable X1 Y1 hY1ne (fun x => A x - θ)
      (fun w => θ + B w) (fun x hx => by linarith [hA x hx]) (fun w hw => by linarith [hB w hw])
    refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, by omega, by omega, Or.inr ⟨?_, ?_⟩⟩
    · exact Or.inl fun x hx w hw => by linarith [hA x (hX2 hx), hB w (hY2 hw)]
    · obtain ⟨qr, qc, h1, h2, h3⟩ := hcmp
      exact ⟨qr, qc, h1, h2, fun x hx w hw => by
        have := h3 x hx w hw; simp only at this; ring_nf at this ⊢; exact this⟩
  ·
    obtain ⟨X2, hX2, Y2, hY2, d1, d2, hcmp⟩ := sum_comparable X1 Y1 hY1ne (fun x => θ - A x)
      (fun w => -B w - θ) (fun x hx => by linarith [hA x hx]) (fun w hw => by linarith [hB w hw])
    refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, by omega, by omega, Or.inr ⟨?_, ?_⟩⟩
    · exact Or.inr fun x hx w hw => by linarith [hA x (hX2 hx), hB w (hY2 hw)]
    · obtain ⟨qr, qc, h1, h2, h3⟩ := hcmp
      refine ⟨qr, qc, h1, h2, fun x hx w hw => ?_⟩
      have := h3 x hx w hw
      have e : |A x + B w| = |θ - A x + (-B w - θ)| := by
        rw [← abs_neg]; ring_nf
      rw [e]; exact this
def gap (τ : ι → TF α β) (t t' : ι) (x : α) (w : β) : ℝ := (τ t).eval x w - (τ t').eval x w
def PairGood (τ : ι → TF α β) (t t' : ι) (X : Finset α) (Y : Finset β) : Prop :=
  StrictSign (gap τ t t') X Y ∧ Comparable (gap τ t t') 32 X Y
theorem PairGood.mono {τ : ι → TF α β} {t t' : ι} {X X' : Finset α} {Y Y' : Finset β}
    (h : PairGood τ t t' X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : PairGood τ t t' X' Y' :=
  ⟨h.1.mono hX hY, h.2.mono hX hY⟩
theorem gap_eq (τ : ι → TF α β) (t t' : ι) (x : α) (w : β) :
    gap τ t t' x w = ((τ t).rp x - (τ t').rp x) + ((τ t).cp w - (τ t').cp w) := by
  simp only [gap, TF.eval_eq]; ring
theorem pair_step (M : α → β → ℝ) (τ : ι → TF α β) (S : Finset ι) (X : Finset α)
    (Y : Finset β) (hX : X.Nonempty) (hY : Y.Nonempty) (hcov : Covers M τ S X Y) (t t' : ι) (ht : t ∈ S) (htt : t ≠ t') :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 16 * #X' ∧ #Y ≤ 16 * #Y' ∧ ∃ S' ⊆ S, Covers M τ S' X' Y' ∧
      (t' ∉ S' ∨ PairGood τ t t' X' Y') := by
  obtain ⟨X', hX', Y', hY', h1, h2, h⟩ := gap_lemma X Y hX hY
    (fun x => (τ t).rp x - (τ t').rp x) (fun w => (τ t).cp w - (τ t').cp w)
  refine ⟨X', hX', Y', hY', h1, h2, ?_⟩
  rcases h with h | ⟨hs, hc⟩
  · refine ⟨S.erase t', erase_subset _ _, fun x hx w hw => ?_, Or.inl (notMem_erase _ _)⟩
    obtain ⟨u, hu, hM⟩ := hcov x (hX' hx) w (hY' hw)
    by_cases hut : u = t'
    · subst hut
      have hg := h x hx w hw
      have : (τ t).eval x w = (τ u).eval x w := by
        have := gap_eq τ t u x w; simp only [gap] at this; linarith
      exact ⟨t, mem_erase.2 ⟨htt, ht⟩, by rw [hM, this]⟩
    · exact ⟨u, mem_erase.2 ⟨hut, hu⟩, hM⟩
  · refine ⟨S, subset_refl _, hcov.mono hX' hY', Or.inr ⟨?_, ?_⟩⟩
    · rcases hs with hs | hs
      · exact Or.inl fun x hx w hw => by rw [gap_eq]; exact hs x hx w hw
      · exact Or.inr fun x hx w hw => by rw [gap_eq]; exact hs x hx w hw
    · obtain ⟨qr, qc, a1, a2, a3⟩ := hc
      exact ⟨qr, qc, a1, a2, fun x hx w hw => by rw [gap_eq]; exact a3 x hx w hw⟩
theorem process_pairs (M : α → β → ℝ) (τ : ι → TF α β) (P : Finset (ι × ι)) :
    ∀ (S : Finset ι) (X : Finset α) (Y : Finset β), X.Nonempty → Y.Nonempty →
      Covers M τ S X Y →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 16 ^ #P * #X' ∧ #Y ≤ 16 ^ #P * #Y' ∧ ∃ S' ⊆ S,
        Covers M τ S' X' Y' ∧
        ∀ p ∈ P, p.1 ∈ S' → p.2 ∈ S' → p.1 ≠ p.2 → PairGood τ p.1 p.2 X' Y' := by
  induction P using Finset.induction_on with
  | empty =>
    intro S X Y _ _ hcov
    exact ⟨X, subset_refl _, Y, subset_refl _, by simp, by simp, S, subset_refl _, hcov,
      by simp⟩
  | insert a P haP ih =>
    intro S X Y hX hY hcov
    obtain ⟨X1, hX1, Y1, hY1, c1, c2, S1, hS1, hcov1, hgood1⟩ := ih S X Y hX hY hcov
    have hX1ne : X1.Nonempty := by
      rw [← card_pos]; have := card_pos.2 hX
      rcases Nat.eq_zero_or_pos #X1 with h | h
      · rw [h] at c1; omega
      · exact h
    have hY1ne : Y1.Nonempty := by
      rw [← card_pos]; have := card_pos.2 hY
      rcases Nat.eq_zero_or_pos #Y1 with h | h
      · rw [h] at c2; omega
      · exact h
    rw [card_insert_of_notMem haP, pow_succ]
    by_cases hcase : a.1 ∈ S1 ∧ a.1 ≠ a.2
    · obtain ⟨X2, hX2, Y2, hY2, d1, d2, S2, hS2, hcov2, h2⟩ :=
        pair_step M τ S1 X1 Y1 hX1ne hY1ne hcov1 a.1 a.2 hcase.1 hcase.2
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, ?_, ?_, S2, hS2.trans hS1, hcov2, ?_⟩
      · calc #X ≤ 16 ^ #P * #X1 := c1
          _ ≤ 16 ^ #P * (16 * #X2) := Nat.mul_le_mul_left _ d1
          _ = 16 ^ #P * 16 * #X2 := by ring
      · calc #Y ≤ 16 ^ #P * #Y1 := c2
          _ ≤ 16 ^ #P * (16 * #Y2) := Nat.mul_le_mul_left _ d2
          _ = 16 ^ #P * 16 * #Y2 := by ring
      · intro p hp hp1 hp2 hne
        rcases mem_insert.1 hp with rfl | hp
        · rcases h2 with h2 | h2
          · exact absurd hp2 h2
          · exact h2
        · exact (hgood1 p hp (hS2 hp1) (hS2 hp2) hne).mono hX2 hY2
    · refine ⟨X1, hX1, Y1, hY1, ?_, ?_, S1, hS1, hcov1, ?_⟩
      · calc #X ≤ 16 ^ #P * #X1 := c1
          _ ≤ 16 ^ #P * 16 * #X1 := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by norm_num))
      · calc #Y ≤ 16 ^ #P * #Y1 := c2
          _ ≤ 16 ^ #P * 16 * #Y1 := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by norm_num))
      · intro p hp hp1 hp2 hne
        rcases mem_insert.1 hp with rfl | hp
        · exact absurd ⟨hp1, hne⟩ hcase
        · exact hgood1 p hp hp1 hp2 hne
end E1088
end
section
open Finset
namespace E1088
variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
theorem nonempty_of_card_le {γ : Type*} {X X' : Finset γ} {c : ℕ} (hX : X.Nonempty)
    (h : #X ≤ c * #X') : X'.Nonempty := by
  rw [← card_pos]
  have := card_pos.2 hX
  rcases Nat.eq_zero_or_pos #X' with h0 | h0
  · rw [h0] at h; omega
  · exact h0
theorem cross_le {a b c d k : ℝ} (hb : 0 < b) (hd : 0 < d) (h : k * (c / d) ≤ a / b) :
    k * c * b ≤ a * d := by
  have := mul_le_mul_of_nonneg_right h (mul_pos hb hd).le
  have e1 : k * (c / d) * (b * d) = k * c * b := by field_simp
  have e2 : a / b * (b * d) = a * d := by field_simp
  linarith
theorem cross_lt {a b c d k : ℝ} (hb : 0 < b) (hd : 0 < d) (h : c / d < k * (a / b)) :
    c * b < k * a * d := by
  have := mul_lt_mul_of_pos_right h (mul_pos hb hd)
  have e1 : k * (a / b) * (b * d) = k * a * d := by field_simp
  have e2 : c / d * (b * d) = c * b := by field_simp
  linarith
theorem compare_basic (X : Finset α) (Y : Finset β) (hY : Y.Nonempty)
    (qr qr' : α → ℝ) (qc qc' : β → ℝ) (h1 : ∀ x ∈ X, 0 < qr x) (h2 : ∀ x ∈ X, 0 < qr' x)
    (h3 : ∀ w ∈ Y, 0 < qc w) (h4 : ∀ w ∈ Y, 0 < qc' w) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 * #X' ∧ #Y ≤ 4 * #Y' ∧
      ((∀ x ∈ X', ∀ w ∈ Y', qr' x * qc' w ≤ 16 * (qr x * qc w)) ∨
       (∀ x ∈ X', ∀ w ∈ Y', qr x * qc w ≤ 16 * (qr' x * qc' w))) := by
  obtain ⟨X', hX', Y', hY', c1, c2, h⟩ := lemmaB X Y hY (fun x => qr x / qr' x)
    (fun w => qc' w / qc w) (fun x hx => div_pos (h1 x hx) (h2 x hx))
    (fun w hw => (div_pos (h4 w hw) (h3 w hw)).le)
  refine ⟨X', hX', Y', hY', c1, c2, ?_⟩
  rcases h with h | h | ⟨s, hs, hD, hE⟩
  · refine Or.inl fun x hx w hw => ?_
    have a1 := h1 x (hX' hx); have a2 := h2 x (hX' hx)
    have a3 := h3 w (hY' hw); have a4 := h4 w (hY' hw)
    have := cross_le a2 a3 (h x hx w hw)
    nlinarith [mul_pos a1 a3, mul_pos a2 a4]
  · refine Or.inr fun x hx w hw => ?_
    have a1 := h1 x (hX' hx); have a2 := h2 x (hX' hx)
    have a3 := h3 w (hY' hw); have a4 := h4 w (hY' hw)
    have := cross_le a3 a2 (h x hx w hw)
    nlinarith [mul_pos a1 a3, mul_pos a2 a4]
  · refine Or.inl fun x hx w hw => ?_
    have a1 := h1 x (hX' hx); have a2 := h2 x (hX' hx)
    have a3 := h3 w (hY' hw); have a4 := h4 w (hY' hw)
    obtain ⟨d1, d2⟩ := hD x hx
    obtain ⟨e1, e2⟩ := hE w hw
    have : qc' w / qc w < 16 * (qr x / qr' x) := by linarith
    have := cross_lt a2 a3 this
    nlinarith [mul_pos a1 a3, mul_pos a2 a4]
theorem tournament {κ : Type*} [DecidableEq κ] (qr : κ → α → ℝ) (qc : κ → β → ℝ)
    (J : Finset κ) :
    ∀ (X : Finset α) (Y : Finset β), Y.Nonempty → J.Nonempty →
      (∀ j ∈ J, ∀ x ∈ X, 0 < qr j x) → (∀ j ∈ J, ∀ w ∈ Y, 0 < qc j w) →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 ^ #J * #X' ∧ #Y ≤ 4 ^ #J * #Y' ∧ ∃ j₀ ∈ J,
        ∀ j ∈ J, ∀ x ∈ X', ∀ w ∈ Y', qr j x * qc j w ≤ 16 ^ #J * (qr j₀ x * qc j₀ w) := by
  induction J using Finset.induction_on with
  | empty => intro X Y _ h; exact absurd h (by simp)
  | insert a J haJ ih =>
    intro X Y hY _ hqr hqc
    rw [card_insert_of_notMem haJ]
    rcases J.eq_empty_or_nonempty with hJ | hJ
    · subst hJ
      refine ⟨X, subset_refl _, Y, subset_refl _, by simp; omega, by simp; omega, a,
        mem_insert_self _ _, fun j hj x hx w hw => ?_⟩
      simp only [insert_empty, mem_singleton] at hj
      subst hj
      have := mul_pos (hqr j (mem_insert_self _ _) x hx) (hqc j (mem_insert_self _ _) w hw)
      simp; linarith
    obtain ⟨X1, hX1, Y1, hY1, c1, c2, j₁, hj₁, hdom⟩ := ih X Y hY hJ
      (fun j hj => hqr j (mem_insert_of_mem hj)) (fun j hj => hqc j (mem_insert_of_mem hj))
    have hY1ne : Y1.Nonempty := nonempty_of_card_le hY c2
    obtain ⟨X2, hX2, Y2, hY2, d1, d2, hc⟩ := compare_basic X1 Y1 hY1ne (qr j₁) (qr a) (qc j₁)
      (qc a) (fun x hx => hqr j₁ (mem_insert_of_mem hj₁) x (hX1 hx))
      (fun x hx => hqr a (mem_insert_self _ _) x (hX1 hx))
      (fun w hw => hqc j₁ (mem_insert_of_mem hj₁) w (hY1 hw))
      (fun w hw => hqc a (mem_insert_self _ _) w (hY1 hw))
    have cX : #X ≤ 4 ^ (#J + 1) * #X2 := by
      calc #X ≤ 4 ^ #J * #X1 := c1
        _ ≤ 4 ^ #J * (4 * #X2) := Nat.mul_le_mul_left _ d1
        _ = 4 ^ (#J + 1) * #X2 := by ring
    have cY : #Y ≤ 4 ^ (#J + 1) * #Y2 := by
      calc #Y ≤ 4 ^ #J * #Y1 := c2
        _ ≤ 4 ^ #J * (4 * #Y2) := Nat.mul_le_mul_left _ d2
        _ = 4 ^ (#J + 1) * #Y2 := by ring
    have h16 : (16 : ℝ) ^ #J ≤ 16 ^ (#J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rcases hc with hc | hc
    ·
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, cX, cY, j₁, mem_insert_of_mem hj₁,
        fun j hj x hx w hw => ?_⟩
      have hpos := mul_pos (hqr j₁ (mem_insert_of_mem hj₁) x (hX1 (hX2 hx)))
        (hqc j₁ (mem_insert_of_mem hj₁) w (hY1 (hY2 hw)))
      rcases mem_insert.1 hj with rfl | hj
      · have := hc x hx w hw
        have : (16 : ℝ) ≤ 16 ^ (#J + 1) := by
          calc (16 : ℝ) = 16 ^ 1 := by norm_num
            _ ≤ 16 ^ (#J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      · have := hdom j hj x (hX2 hx) w (hY2 hw)
        nlinarith
    ·
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, cX, cY, a, mem_insert_self _ _,
        fun j hj x hx w hw => ?_⟩
      have hpos := mul_pos (hqr a (mem_insert_self _ _) x (hX1 (hX2 hx)))
        (hqc a (mem_insert_self _ _) w (hY1 (hY2 hw)))
      rcases mem_insert.1 hj with rfl | hj
      · have : (1 : ℝ) ≤ 16 ^ (#J + 1) := one_le_pow₀ (by norm_num)
        nlinarith
      · have h1 := hdom j hj x (hX2 hx) w (hY2 hw)
        have h2 := hc x hx w hw
        have hp16 : (0 : ℝ) ≤ 16 ^ #J := by positivity
        calc qr j x * qc j w ≤ 16 ^ #J * (qr j₁ x * qc j₁ w) := h1
          _ ≤ 16 ^ #J * (16 * (qr a x * qc a w)) := mul_le_mul_of_nonneg_left h2 hp16
          _ = 16 ^ (#J + 1) * (qr a x * qc a w) := by ring
end E1088
end
section
open Finset
namespace E1088
variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
def CutData (τ : ι → TF α β) (S' : Finset ι) (K : ℝ) (X : Finset α) (Y : Finset β) : Prop :=
  ∃ Lo Hi : Finset ι, Lo ∪ Hi = S' ∧ Disjoint Lo Hi ∧ Lo.Nonempty ∧ Hi.Nonempty ∧
  ∃ (φ : α → ℝ) (θ : β → ℝ) (qr : α → ℝ) (qc : β → ℝ),
    (∀ x ∈ X, 0 < qr x) ∧ (∀ w ∈ Y, 0 < qc w) ∧
    ∀ x ∈ X, ∀ w ∈ Y,
      (∀ t ∈ Lo, -(K * (qr x * qc w)) ≤ (τ t).eval x w - (φ x + θ w) ∧
          (τ t).eval x w - (φ x + θ w) ≤ -(qr x * qc w) / 2) ∧
      (∀ t ∈ Hi, (qr x * qc w) / 2 ≤ (τ t).eval x w - (φ x + θ w) ∧
          (τ t).eval x w - (φ x + θ w) ≤ K * (qr x * qc w))
theorem cut_of_good (τ : ι → TF α β) (S : Finset ι) (X : Finset α) (Y : Finset β)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hS : 2 ≤ #S)
    (hgood : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → PairGood τ t t' X Y) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, #X ≤ 4 ^ #S * #X' ∧ #Y ≤ 4 ^ #S * #Y' ∧
      CutData τ S (32 * #S * 16 ^ #S) X' Y' := by
  classical
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨w0, hw0⟩ := hY
  set q := #S with hq
  set val : ι → ℝ := fun t => (τ t).eval x0 w0 with hval
  have transfer : ∀ t ∈ S, ∀ t' ∈ S, val t < val t' →
      ∀ x ∈ X, ∀ w ∈ Y, (τ t).eval x w < (τ t').eval x w := by
    intro t ht t' ht' hlt x hx w hw
    have hne : t ≠ t' := by rintro rfl; exact lt_irrefl _ hlt
    rcases (hgood t ht t' ht' hne).1 with h | h
    · have := h x0 hx0 w0 hw0; simp only [gap] at this; simp only [hval] at hlt; linarith
    · have := h x hx w hw; simp only [gap] at this; linarith
  have inj : Set.InjOn val S := by
    intro t ht t' ht' heq
    by_contra hne
    rcases (hgood t ht t' ht' hne).1 with h | h
    · have := h x0 hx0 w0 hw0; simp only [gap] at this; simp only [hval] at heq; linarith
    · have := h x0 hx0 w0 hw0; simp only [gap] at this; simp only [hval] at heq; linarith
  set V := S.image val with hV
  have hVc : #V = q := card_image_of_injOn inj
  set emb := V.orderEmbOfFin hVc with hemb
  have hch : ∀ i : Fin q, ∃ t ∈ S, val t = emb i := by
    intro i
    have := orderEmbOfFin_mem V hVc i
    obtain ⟨t, ht, h⟩ := mem_image.1 this
    exact ⟨t, ht, h⟩
  choose f hfS hfv using hch
  have hq0 : 0 < q := by omega
  let e : ℕ → ι := fun i => if h : i < q then f ⟨i, h⟩ else f ⟨0, hq0⟩
  have heS : ∀ i, e i ∈ S := by
    intro i; simp only [e]; split_ifs <;> exact hfS _
  have hev : ∀ i (h : i < q), val (e i) = emb ⟨i, h⟩ := by
    intro i h; simp only [e, dif_pos h]; exact hfv _
  have hmono : ∀ i j, i < j → j < q → val (e i) < val (e j) := by
    intro i j hij hj
    rw [hev i (by omega), hev j hj]
    exact emb.strictMono (Fin.mk_lt_mk.2 hij)
  have hsurj : ∀ t ∈ S, ∃ i < q, e i = t := by
    intro t ht
    have hmem : val t ∈ Set.range emb := by
      rw [hemb, range_orderEmbOfFin]; exact mem_coe.2 (mem_image_of_mem _ ht)
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i, i.2, inj (heS _) ht ?_⟩
    rw [hev i i.2]; exact hi
  have hle : ∀ i j, i ≤ j → j < q → ∀ x ∈ X, ∀ w ∈ Y,
      (τ (e i)).eval x w ≤ (τ (e j)).eval x w := by
    intro i j hij hj x hx w hw
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (transfer _ (heS i) _ (heS j) (hmono i j hlt hj) x hx w hw).le
  have hgap : ∀ i : ℕ, ∃ qr : α → ℝ, ∃ qc : β → ℝ, i < q - 1 →
      (∀ x ∈ X, 0 < qr x) ∧ (∀ w ∈ Y, 0 < qc w) ∧ ∀ x ∈ X, ∀ w ∈ Y,
        qr x * qc w ≤ gap τ (e (i + 1)) (e i) x w ∧
          gap τ (e (i + 1)) (e i) x w ≤ 32 * (qr x * qc w) := by
    intro i
    by_cases hi : i < q - 1
    · have hne : e (i + 1) ≠ e i := by
        intro h; have := hmono i (i + 1) (by omega) (by omega); rw [h] at this
        exact lt_irrefl _ this
      obtain ⟨qr, qc, h1, h2, h3⟩ := (hgood _ (heS _) _ (heS _) hne).2
      refine ⟨qr, qc, fun _ => ⟨h1, h2, fun x hx w hw => ?_⟩⟩
      have hpos : 0 < gap τ (e (i + 1)) (e i) x w := by
        have := transfer _ (heS i) _ (heS (i + 1)) (hmono i (i + 1) (by omega) (by omega))
          x hx w hw
        simp only [gap]; linarith
      have := h3 x hx w hw
      rwa [abs_of_pos hpos] at this
    · exact ⟨fun _ => 1, fun _ => 1, fun h => absurd h hi⟩
  choose qr qc hQ using hgap
  have hJ : (range (q - 1)).Nonempty := ⟨0, mem_range.2 (by omega)⟩
  obtain ⟨X', hX', Y', hY', c1, c2, i0, hi0, hdom⟩ := tournament qr qc (range (q - 1)) X Y
    ⟨w0, hw0⟩ hJ (fun j hj x hx => (hQ j (mem_range.1 hj)).1 x hx)
    (fun j hj w hw => (hQ j (mem_range.1 hj)).2.1 w hw)
  rw [card_range] at c1 c2 hdom
  have hi0q : i0 < q - 1 := mem_range.1 hi0
  have h4 : 4 ^ (q - 1) ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨X', hX', Y', hY', c1.trans (Nat.mul_le_mul_right _ h4),
    c2.trans (Nat.mul_le_mul_right _ h4), ?_⟩
  refine ⟨(range (i0 + 1)).image e, (Ico (i0 + 1) q).image e, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← image_union, range_eq_Ico, Ico_union_Ico_eq_Ico (by omega) (by omega)]
    ext t
    simp only [mem_image, mem_Ico]
    constructor
    · rintro ⟨i, _, rfl⟩; exact heS i
    · intro ht; obtain ⟨i, hi, rfl⟩ := hsurj t ht; exact ⟨i, ⟨by omega, hi⟩, rfl⟩
  · rw [disjoint_left]
    intro t ht ht'
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ht
    obtain ⟨j, hj, hji⟩ := mem_image.1 ht'
    rw [mem_range] at hi; rw [mem_Ico] at hj
    have := hmono i j (by omega) hj.2
    rw [hji] at this; exact lt_irrefl _ this
  · exact ⟨e 0, mem_image.2 ⟨0, mem_range.2 (by omega), rfl⟩⟩
  · exact ⟨e (i0 + 1), mem_image.2 ⟨i0 + 1, mem_Ico.2 ⟨le_rfl, by omega⟩, rfl⟩⟩
  refine ⟨fun x => ((τ (e i0)).rp x + (τ (e (i0 + 1))).rp x) / 2,
    fun w => ((τ (e i0)).cp w + (τ (e (i0 + 1))).cp w) / 2, qr i0, qc i0,
    fun x hx => (hQ i0 hi0q).1 x (hX' hx), fun w hw => (hQ i0 hi0q).2.1 w (hY' hw), ?_⟩
  intro x hx w hw
  have hxX := hX' hx
  have hwY := hY' hw
  have hz : ((τ (e i0)).rp x + (τ (e (i0 + 1))).rp x) / 2 +
      ((τ (e i0)).cp w + (τ (e (i0 + 1))).cp w) / 2 =
      ((τ (e i0)).eval x w + (τ (e (i0 + 1))).eval x w) / 2 := by
    rw [TF.eval_eq, TF.eval_eq]; ring
  rw [hz]
  set σ := qr i0 x * qc i0 w with hσ
  have hσpos : 0 < σ := mul_pos ((hQ i0 hi0q).1 x hxX) ((hQ i0 hi0q).2.1 w hwY)
  have hg0 := ((hQ i0 hi0q).2.2 x hxX w hwY).1
  simp only [gap] at hg0
  have htel : (τ (e (q - 1))).eval x w - (τ (e 0)).eval x w =
      ∑ i ∈ range (q - 1), gap τ (e (i + 1)) (e i) x w := by
    simp only [gap]
    rw [sum_range_sub (fun i => (τ (e i)).eval x w)]
  have hspread : (τ (e (q - 1))).eval x w - (τ (e 0)).eval x w ≤ 32 * #S * 16 ^ #S * σ := by
    rw [htel]
    calc ∑ i ∈ range (q - 1), gap τ (e (i + 1)) (e i) x w
        ≤ ∑ _i ∈ range (q - 1), 32 * (16 ^ (q - 1) * σ) := by
          refine sum_le_sum fun i hi => ?_
          have h1 := ((hQ i (mem_range.1 hi)).2.2 x hxX w hwY).2
          have h2 := hdom i hi x hx w hw
          nlinarith
      _ = (q - 1 : ℕ) * (32 * (16 ^ (q - 1) * σ)) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ 32 * #S * 16 ^ #S * σ := by
          have a1 : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
          have a2 : (16 : ℝ) ^ (q - 1) ≤ 16 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
          have a3 : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          rw [← hq]
          have : ((q - 1 : ℕ) : ℝ) * 16 ^ (q - 1) ≤ q * 16 ^ q :=
            mul_le_mul a1 a2 (by positivity) (by positivity)
          nlinarith
  have hbot : ∀ j, j < q → (τ (e 0)).eval x w ≤ (τ (e j)).eval x w :=
    fun j hj => hle 0 j (Nat.zero_le _) hj x hxX w hwY
  have htop : ∀ j, j < q → (τ (e j)).eval x w ≤ (τ (e (q - 1))).eval x w :=
    fun j hj => hle j (q - 1) (by omega) (by omega) x hxX w hwY
  have hA := hbot i0 (by omega)
  have hB := htop (i0 + 1) (by omega)
  have hA' := htop i0 (by omega)
  have hB' := hbot (i0 + 1) (by omega)
  constructor
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
    rw [mem_range] at hj
    have h1 := hle j i0 (by omega) (by omega) x hxX w hwY
    have h2 := hbot j (by omega)
    constructor <;> linarith
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
    rw [mem_Ico] at hj
    have h1 := hle (i0 + 1) j hj.1 hj.2 x hxX w hwY
    have h2 := htop j hj.2
    constructor <;> linarith
end E1088
end
section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal
namespace E1088
theorem integral_mul_exp_half :
    ∫ r in Ioi (0 : ℝ), r * Real.exp (-(1 / 2) * r ^ 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have e : (fun r : ℝ => (r : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (r : ℂ) ^ 2)) =
      fun r : ℝ => ((r * Real.exp (-(1 / 2) * r ^ 2) : ℝ) : ℂ) := by
    funext r
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [e, integral_complex_ofReal] at h
  have h2 : (2 * (1 / 2 : ℂ))⁻¹ = ((1 : ℝ) : ℂ) := by norm_num
  rw [h2] at h
  exact_mod_cast h
theorem volume_arc (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
    volume ({θ : ℝ | 0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - φ)} ∩ Ioo (-π) π) =
      ENNReal.ofReal (π - φ) := by
  have hpi := Real.pi_pos
  set A := {θ : ℝ | 0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - φ)} ∩ Ioo (-π) π with hA
  have h1 : Icc (φ - π / 2) (π / 2) ⊆ A := by
    rintro θ ⟨ha, hb⟩
    refine ⟨⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, hb⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩, by linarith, by linarith⟩
  have h2 : A ⊆ Icc (φ - π / 2) (π / 2) ∪ {-(π / 2)} := by
    rintro θ ⟨⟨hc1, hc2⟩, hlo, hhi⟩
    have hθ1 : θ ≤ π / 2 := by
      by_contra h
      push Not at h
      exact absurd hc1 (not_le.2 (Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith)))
    have hθ2 : -(π / 2) ≤ θ := by
      by_contra h
      push Not at h
      have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := -θ) (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      exact absurd hc1 (not_le.2 this)
    by_cases h3 : φ - π / 2 ≤ θ
    · exact Or.inl ⟨h3, hθ1⟩
    · push Not at h3
      by_cases h4 : θ - φ = -(3 * π / 2)
      · right
        rw [mem_singleton_iff]
        linarith
      · exfalso
        have h5 : -(3 * π / 2) < θ - φ := lt_of_le_of_ne (by linarith) (Ne.symm h4)
        have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := θ - φ + 2 * π) (by linarith)
          (by linarith)
        rw [Real.cos_add_two_pi] at this
        exact absurd hc2 (not_le.2 this)
  apply le_antisymm
  · calc volume A ≤ volume (Icc (φ - π / 2) (π / 2) ∪ {-(π / 2)}) := measure_mono h2
      _ ≤ volume (Icc (φ - π / 2) (π / 2)) + volume ({-(π / 2)} : Set ℝ) := measure_union_le _ _
      _ = ENNReal.ofReal (π - φ) := by
          rw [Real.volume_singleton, add_zero, Real.volume_Icc]; congr 1; ring
  · calc ENNReal.ofReal (π - φ) = volume (Icc (φ - π / 2) (π / 2)) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ volume A := measure_mono h1
noncomputable abbrev gauss2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
theorem gauss_pdf_prod (r θ : ℝ) :
    gaussianPDFReal 0 1 (r * Real.cos θ) * gaussianPDFReal 0 1 (r * Real.sin θ) =
      Real.exp (-(1 / 2) * r ^ 2) / (2 * π) := by
  have hpi := Real.pi_pos
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have h2 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have h3 : Real.exp (-(r * Real.cos θ) ^ 2 / 2) * Real.exp (-(r * Real.sin θ) ^ 2 / 2) =
      Real.exp (-(1 / 2) * r ^ 2) := by
    rw [← Real.exp_add]; congr 1
    have := Real.cos_sq_add_sin_sq θ
    nlinarith [this]
  calc (√(2 * π))⁻¹ * Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
        ((√(2 * π))⁻¹ * Real.exp (-(r * Real.sin θ) ^ 2 / 2))
      = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          Real.exp (-(r * Real.sin θ) ^ 2 / 2)) := by ring
    _ = _ := by rw [h2, h3]; field_simp
theorem gauss2_sector (a : ℝ) (ha1 : -1 ≤ a) (ha2 : a ≤ 1) :
    gauss2 {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ a * p.1 + √(1 - a ^ 2) * p.2} =
      ENNReal.ofReal (1 / 2 - Real.arccos a / (2 * π)) := by
  have hpi := Real.pi_pos
  set φ := Real.arccos a with hφ
  have hc : Real.cos φ = a := Real.cos_arccos ha1 ha2
  have hs : Real.sin φ = √(1 - a ^ 2) := Real.sin_arccos a
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg a
  have hφπ : φ ≤ π := Real.arccos_le_pi a
  rw [← hs, ← hc]
  set S := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ Real.cos φ * p.1 + Real.sin φ * p.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ)) measurable_const measurable_fst).inter
      (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ))
        (g := fun p : ℝ × ℝ => Real.cos φ * p.1 + Real.sin φ * p.2) measurable_const
        (by fun_prop))
  set f : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2 with hf
  have hν : gauss2 = volume.withDensity f := by
    simp only [gauss2]
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
      ← Measure.volume_eq_prod]
  rw [hν, withDensity_apply _ hSm, ← lintegral_indicator hSm, ← lintegral_comp_polarCoord_symm]
  set A := {θ : ℝ | 0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - φ)} with hA
  set F : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r * Real.exp (-(1 / 2) * r ^ 2) / (2 * π))
    with hF
  have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • S.indicator f (polarCoord.symm p) =
      F p.1 * A.indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : 0 < r := hr
    simp only [polarCoord_symm_apply]
    have hiff : (r * Real.cos θ, r * Real.sin θ) ∈ S ↔ θ ∈ A := by
      simp only [hS, hA, mem_ofPred_eq, Real.cos_sub]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨nonneg_of_mul_nonneg_right (by linarith [h1]) hr0, ?_⟩
        have : 0 ≤ r * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) := by nlinarith
        exact nonneg_of_mul_nonneg_right (by linarith) hr0
      · rintro ⟨h1, h2⟩
        exact ⟨mul_nonneg hr0.le h1, by nlinarith⟩
    by_cases hθA : θ ∈ A
    · rw [indicator_of_mem (hiff.2 hθA), indicator_of_mem hθA]
      simp only [hf, gaussianPDF, Pi.one_apply, mul_one, smul_eq_mul, hF]
      rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        ← ENNReal.ofReal_mul hr0.le, gauss_pdf_prod]
      congr 1; ring
    · rw [indicator_of_notMem (fun h => hθA (hiff.1 h)), indicator_of_notMem hθA]
      simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hAm : MeasurableSet A :=
    (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) measurable_const
      Real.continuous_cos.measurable).inter
      (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) (g := fun θ => Real.cos (θ - φ))
        measurable_const (by fun_prop))
  rw [lintegral_prod_mul (by fun_prop) ((measurable_one.indicator hAm).aemeasurable)]
  have hrad : ∫⁻ r in Ioi (0 : ℝ), F r = ENNReal.ofReal (1 / (2 * π)) := by
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_div, integral_mul_exp_half]
    · exact ((integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn).div_const _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have : (0 : ℝ) < r := hr
      positivity
  have hang : ∫⁻ θ in Ioo (-π) π, A.indicator 1 θ = ENNReal.ofReal (π - φ) := by
    rw [lintegral_indicator_one hAm, Measure.restrict_apply hAm]
    exact volume_arc φ hφ0 hφπ
  rw [hrad, hang, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
theorem pi_map_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (i j : ι) (hij : i ≠ j) :
    (Measure.pi μ).map (fun x => (x i, x j)) = (μ i).prod (μ j) := by
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply (by fun_prop) (hs.prod ht)]
  have hset : (fun x : ι → ℝ => (x i, x j)) ⁻¹' (s ×ˢ t) =
      Set.pi univ (fun k => if k = i then s else if k = j then t else univ) := by
    ext x
    simp only [mem_preimage, mem_prod, Set.mem_pi, mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hki : k = i
      · subst hki; simpa using h1
      · by_cases hkj : k = j
        · subst hkj; simpa [hki] using h2
        · simp [hki, hkj]
    · intro h
      exact ⟨by simpa using h i, by simpa [Ne.symm hij] using h j⟩
  rw [hset, Measure.pi_pi,
    Fintype.prod_eq_mul i j hij (fun k hk => by simp [hk.1, hk.2])]
  simp [Ne.symm hij]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
theorem inner_sum_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E)
    (x : ι → ℝ) (j : ι) : inner ℝ (∑ i, x i • b i) (b j) = x j := by
  simp [sum_inner, real_inner_smul_left, orthonormal_iff_ite.1 b.orthonormal]
theorem stdGaussian_map_pair (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0) :
    (stdGaussian E).map (fun g => (inner ℝ g u, inner ℝ g w)) = gauss2 := by
  classical
  have huw' : u ≠ w := by
    rintro rfl; rw [real_inner_self_eq_norm_sq, hu] at huw; norm_num at huw
  have hon : Orthonormal ℝ (Subtype.val : ({u, w} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp [real_inner_self_eq_norm_sq, hu]
    · simp [huw, huw']
    · rw [real_inner_comm]; simp [huw, Ne.symm huw']
    · simp [real_inner_self_eq_norm_sq, hw]
  obtain ⟨U, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  have hu' : u ∈ U := hsub (by simp)
  have hw' : w ∈ U := hsub (by simp)
  have hbu : b ⟨u, hu'⟩ = u := by rw [hb]
  have hbw : b ⟨w, hw'⟩ = w := by rw [hb]
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_map (by fun_prop) (by fun_prop)]
  have : (fun g => (inner ℝ g u, inner ℝ g w)) ∘ (fun x : U → ℝ => ∑ i, x i • b i) =
      fun x => (x ⟨u, hu'⟩, x ⟨w, hw'⟩) := by
    funext x
    simp only [Function.comp]
    conv_lhs => rw [← hbu, ← hbw]
    rw [inner_sum_basis, inner_sum_basis]
  rw [this, pi_map_pair _ _ _ (fun h => huw' (congrArg Subtype.val h))]
theorem stdGaussian_map_one (u : E) (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g => inner ℝ g u) = gaussianReal 0 1 := by
  classical
  have hon : Orthonormal ℝ (Subtype.val : ({u} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    simp [real_inner_self_eq_norm_sq, hu]
  obtain ⟨U, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  have hu' : u ∈ U := hsub (by simp)
  have hbu : b ⟨u, hu'⟩ = u := by rw [hb]
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_map (by fun_prop) (by fun_prop)]
  have : (fun g => inner ℝ g u) ∘ (fun x : U → ℝ => ∑ i, x i • b i) = fun x => x ⟨u, hu'⟩ := by
    funext x
    simp only [Function.comp]
    conv_lhs => rw [← hbu]
    rw [inner_sum_basis]
  rw [this]
  exact (measurePreserving_eval (fun _ : U => gaussianReal 0 1) ⟨u, hu'⟩).map_eq
theorem sheppard_general (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian E).real {g | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} =
      1 / 2 - Real.arccos (inner ℝ u v) / (2 * π) := by
  have hpi := Real.pi_pos
  set a := inner ℝ u v with ha
  have hab : |a| ≤ 1 := by
    have := abs_real_inner_le_norm u v; rw [hu, hv, one_mul] at this; exact this
  have ha1 : -1 ≤ a := (abs_le.1 hab).1
  have ha2 : a ≤ 1 := (abs_le.1 hab).2
  set c := √(1 - a ^ 2) with hc
  set S := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ a * p.1 + c * p.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ)) measurable_const measurable_fst).inter
      (measurableSet_le (f := fun _ : ℝ × ℝ => (0 : ℝ))
        (g := fun p : ℝ × ℝ => a * p.1 + c * p.2) measurable_const (by fun_prop))
  have hnorm : ‖v - a • u‖ ^ 2 = 1 - a ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, real_inner_comm, hu, hv]
    rw [Real.norm_eq_abs, mul_one, sq_abs, ← ha]; ring
  have key : stdGaussian E {g | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} = gauss2 S := by
    by_cases hlt : a ^ 2 < 1
    · have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith)
      set w := c⁻¹ • (v - a • u) with hw
      have hvau : ‖v - a • u‖ = c := by
        rw [hc, ← hnorm, Real.sqrt_sq (norm_nonneg _)]
      have hw1 : ‖w‖ = 1 := by
        rw [hw, norm_smul, hvau, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos,
          inv_mul_cancel₀ hcpos.ne']
      have huw : inner ℝ u w = 0 := by
        rw [hw, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hu, ← ha]; ring
      have hv' : v = a • u + c • w := by
        rw [hw, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]; abel
      have hset : {g : E | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} =
          (fun g => (inner ℝ g u, inner ℝ g w)) ⁻¹' S := by
        ext g
        simp only [mem_setOf_eq, mem_preimage, hS]
        rw [hv', inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [hset, ← Measure.map_apply (by fun_prop) hSm, stdGaussian_map_pair u w hu hw1 huw]
    · have ha2' : a ^ 2 = 1 := by nlinarith [sq_abs a, abs_nonneg a]
      have hc0 : c = 0 := by rw [hc, ha2']; simp
      have hvau : v = a • u := by
        have : ‖v - a • u‖ ^ 2 = 0 := by rw [hnorm, ha2']; ring
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        exact sub_eq_zero.1 (norm_eq_zero.1 this)
      set S1 := {x : ℝ | 0 ≤ x ∧ 0 ≤ a * x} with hS1
      have hS1m : MeasurableSet S1 :=
        (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) measurable_const measurable_id).inter
          (measurableSet_le (f := fun _ : ℝ => (0 : ℝ)) (g := fun x : ℝ => a * x)
            measurable_const (by fun_prop))
      have hSS : S = S1 ×ˢ univ := by
        ext p; simp [hS, hS1, hc0]
      have hset : {g : E | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v} = (fun g => inner ℝ g u) ⁻¹' S1 := by
        ext g; simp only [mem_setOf_eq, mem_preimage, hS1]; rw [hvau, real_inner_smul_right]
      rw [hset, ← Measure.map_apply (by fun_prop) hS1m, stdGaussian_map_one u hu, hSS,
        Measure.prod_prod, measure_univ, mul_one]
  rw [measureReal_def, key, hS, hc, gauss2_sector a ha1 ha2, ENNReal.toReal_ofReal]
  have := Real.arccos_le_pi a
  rw [sub_nonneg, div_le_iff₀ (by positivity)]; linarith
end E1088
end
section
open Finset Matrix
namespace E1088
theorem kw_scalar (r : ℕ) (hr : 1 ≤ r) (q : ℝ) (hq0 : 0 ≤ q)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → (1 - t) ^ r + t * (1 - t) ^ (r - 1) * q ≤ 1) :
    q ≤ r := by
  by_contra hcon
  push Not at hcon
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hqpos : 0 < q := lt_of_lt_of_le (by linarith) hcon.le
  set t : ℝ := (q - r) / (2 * r * q) with ht
  have htpos : 0 < t := div_pos (by linarith) (by positivity)
  have ht2 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]
    nlinarith
  have hrt : (r : ℝ) * t ≤ 1 / 2 := by
    rw [ht, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hb1 : 1 + (r : ℝ) * (-t) ≤ (1 + -t) ^ r := one_add_mul_le_pow (by linarith) r
  have hb2 : 1 + ((r - 1 : ℕ) : ℝ) * (-t) ≤ (1 + -t) ^ (r - 1) := one_add_mul_le_pow (by linarith) _
  have hcast : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub hr]; simp
  rw [hcast] at hb2
  have hpos2 : 0 ≤ 1 + ((r : ℝ) - 1) * (-t) := by nlinarith
  have key := h t htpos ht2
  have e1 : (1 - t) ^ r ≥ 1 - r * t := by
    have : (1 + -t) = 1 - t := by ring
    rw [this] at hb1; linarith
  have e2 : (1 - t) ^ (r - 1) ≥ 1 - (r - 1) * t := by
    have : (1 + -t) = 1 - t := by ring
    rw [this] at hb2; linarith
  have e3 : t * (1 - t) ^ (r - 1) * q ≥ t * (1 - (r - 1) * t) * q := by
    have : 0 ≤ t * q := by positivity
    have := mul_le_mul_of_nonneg_left e2 this
    linarith [show t * (1 - t) ^ (r - 1) * q = t * q * (1 - t) ^ (r - 1) by ring,
      show t * (1 - (r - 1) * t) * q = t * q * (1 - (r - 1) * t) by ring]
  have e4 : t * (q - r) - (r - 1) * q * t ^ 2 > 0 := by
    have h1 : (r - 1) * q * t ≤ (q - r) / 2 := by
      have : (r : ℝ) * q * t = (q - r) / 2 := by
        rw [ht]; field_simp
      nlinarith
    have : t * (q - r) - (r - 1) * q * t ^ 2 = t * ((q - r) - (r - 1) * q * t) := by ring
    rw [this]
    apply mul_pos htpos
    linarith
  nlinarith
section design
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
noncomputable def designMat (a : ι → Fin r → ℝ) (lam : ι → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ i, lam i • vecMulVec (a i) (a i)
theorem designMat_mulVec (a : ι → Fin r → ℝ) (lam : ι → ℝ) (x : Fin r → ℝ) :
    designMat a lam *ᵥ x = ∑ i, (lam i * (a i ⬝ᵥ x)) • a i := by
  unfold designMat
  rw [sum_mulVec]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, vecMulVec_mulVec]
  ext k
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring
theorem designMat_quad (a : ι → Fin r → ℝ) (lam : ι → ℝ) (x y : Fin r → ℝ) :
    y ⬝ᵥ (designMat a lam *ᵥ x) = ∑ i, lam i * (a i ⬝ᵥ x) * (a i ⬝ᵥ y) := by
  rw [designMat_mulVec, dotProduct_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm y (a i)]
theorem designMat_isHermitian (a : ι → Fin r → ℝ) (lam : ι → ℝ) :
    (designMat a lam).IsHermitian := by
  unfold designMat IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  ext k l
  simp [transpose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]
theorem designMat_posSemidef (a : ι → Fin r → ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    (designMat a lam).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (designMat_isHermitian a lam) fun x => ?_
  rw [star_trivial, designMat_quad]
  exact sum_nonneg fun i _ => by
    have := hlam i
    have : 0 ≤ (a i ⬝ᵥ x) * (a i ⬝ᵥ x) := mul_self_nonneg _
    nlinarith
theorem designMat_comb (a : ι → Fin r → ℝ) (lam : ι → ℝ) (t : ℝ) (i0 : ι) :
    designMat a ((1 - t) • lam + t • Pi.single i0 1) =
      (1 - t) • designMat a lam + t • vecMulVec (a i0) (a i0) := by
  unfold designMat
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, sum_add_distrib, mul_smul,
    ← smul_sum]
  congr 1
  rw [Finset.sum_eq_single i0]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · intro h; exact absurd (mem_univ _) h
theorem kw_design [Nonempty ι] (a : ι → Fin r → ℝ) (hr : 1 ≤ r)
    (hspan : ∀ x : Fin r → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ (designMat a lam).PosDef ∧
      ∀ i, a i ⬝ᵥ ((designMat a lam)⁻¹ *ᵥ a i) ≤ r := by
  classical
  set f : (ι → ℝ) → ℝ := fun lam => (designMat a lam).det with hf
  have hfc : Continuous f := by
    refine Continuous.matrix_det ?_
    unfold designMat
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set u : ι → ℝ := fun _ => 1 / n with hu
  have hu_mem : u ∈ stdSimplex ℝ ι := by
    refine ⟨fun i => by positivity, ?_⟩
    simp only [hu, sum_const, card_univ, nsmul_eq_mul]
    rw [← hn]; field_simp
  obtain ⟨lam, hlam, hmax⟩ := (isCompact_stdSimplex ℝ ι).exists_isMaxOn ⟨u, hu_mem⟩ hfc.continuousOn
  have hlam0 : ∀ i, 0 ≤ lam i := hlam.1
  have hlam1 : ∑ i, lam i = 1 := hlam.2
  have hupd : (designMat a u).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos (designMat_isHermitian a u) fun x hx => ?_
    rw [star_trivial, designMat_quad]
    have hex : ∃ i, a i ⬝ᵥ x ≠ 0 := by
      by_contra hno; push Not at hno; exact hx (hspan x hno)
    obtain ⟨i0, hi0⟩ := hex
    have hterm : ∀ i ∈ univ, 0 ≤ u i * (a i ⬝ᵥ x) * (a i ⬝ᵥ x) := fun i _ => by
      have h1 : 0 ≤ u i := by simp only [hu]; exact div_nonneg zero_le_one hnpos.le
      rw [mul_assoc]; exact mul_nonneg h1 (mul_self_nonneg _)
    refine lt_of_lt_of_le ?_ (single_le_sum hterm (mem_univ i0))
    have : 0 < (a i0 ⬝ᵥ x) * (a i0 ⬝ᵥ x) := mul_self_pos.2 hi0
    rw [mul_assoc]; exact mul_pos (by simp only [hu]; exact div_pos one_pos hnpos) this
  have hdetu : 0 < f u := hupd.det_pos
  have hdet : 0 < f lam := lt_of_lt_of_le hdetu (hmax hu_mem)
  set M := designMat a lam with hM
  have hMpd : M.PosDef := (designMat_posSemidef a lam hlam0).posDef_iff_det_ne_zero.2 hdet.ne'
  refine ⟨lam, hlam0, hlam1, hMpd, fun i0 => ?_⟩
  set q := a i0 ⬝ᵥ (M⁻¹ *ᵥ a i0) with hq
  have hq0 : 0 ≤ q := by
    have := hMpd.inv.posSemidef
    have h2 := (posSemidef_iff_dotProduct_mulVec.1 this).2 (a i0)
    rwa [star_trivial] at h2
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet.ne'
  refine kw_scalar r hr q hq0 fun t ht0 ht2 => ?_
  have ht1 : t < 1 := by linarith
  have hmem : (1 - t) • lam + t • Pi.single i0 1 ∈ stdSimplex ℝ ι := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hlam0 i
      have : 0 ≤ (Pi.single i0 (1 : ℝ) : ι → ℝ) i := by
        by_cases h : i = i0 <;> simp [Pi.single_apply, h]
      nlinarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hlam1]
      simp
  have hle : f ((1 - t) • lam + t • Pi.single i0 1) ≤ f lam := hmax hmem
  simp only [hf] at hle
  rw [designMat_comb] at hle
  set c : ℝ := t / (1 - t) with hc
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hsplit : (1 - t) • M + t • vecMulVec (a i0) (a i0) =
      (1 - t) • (M + replicateCol Unit (c • a i0) * replicateRow Unit (a i0)) := by
    rw [← vecMulVec_eq, smul_add]
    congr 1
    ext k l
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hc]
    field_simp
  have hlemma := det_add_replicateCol_mul_replicateRow (ι := Unit) hMunit (c • a i0) (a i0)
  have hentry : (1 + replicateRow Unit (a i0) * M⁻¹ * replicateCol Unit (c • a i0)).det =
      1 + c * q := by
    rw [det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
      replicateCol_apply, Pi.smul_apply, smul_eq_mul, hq, dotProduct, mulVec, Finset.univ_unique,
      Finset.sum_singleton]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [hsplit, det_smul, hlemma, hentry, Fintype.card_fin] at hle
  have hdetM : 0 < M.det := hdet
  have h3 : (1 - t) ^ r * (1 + c * q) ≤ 1 := by
    have : (1 - t) ^ r * (M.det * (1 + c * q)) ≤ 1 * M.det := by linarith
    nlinarith
  have hr1 : (1 - t) ^ r = (1 - t) * (1 - t) ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : (1 - t) ^ r * (1 + c * q) = (1 - t) ^ r + t * (1 - t) ^ (r - 1) * q := by
    rw [hr1, hc]; field_simp
  linarith
end design
theorem dot_mulVec_mulVec {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ) (y z : Fin r → ℝ) :
    (A *ᵥ y) ⬝ᵥ (B *ᵥ z) = y ⬝ᵥ ((Aᵀ * B) *ᵥ z) := by
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec]
theorem pd_factor {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.PosDef) :
    ∃ L R : Matrix (Fin r) (Fin r) ℝ, Lᵀ * R = 1 ∧ Rᵀ * R = M ∧ Lᵀ * L = M⁻¹ := by
  classical
  have hH := hM.1
  set U : Matrix (Fin r) (Fin r) ℝ := (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  set e := hH.eigenvalues with he
  have hspec : M = U * diagonal e * Uᵀ := by
    have h := hH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp] at h
    exact h
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using this
  have hUtU : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using this
  have hepos : ∀ i, 0 < e i := hM.eigenvalues_pos
  set sq : Fin r → ℝ := fun i => Real.sqrt (e i) with hsq
  have hsqpos : ∀ i, 0 < sq i := fun i => Real.sqrt_pos.2 (hepos i)
  refine ⟨diagonal (fun i => (sq i)⁻¹) * Uᵀ, diagonal sq * Uᵀ, ?_, ?_, ?_⟩
  · rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have : (fun i => (sq i)⁻¹ * sq i) = fun _ => (1 : ℝ) := by
      funext i; exact inv_mul_cancel₀ (hsqpos i).ne'
    rw [this, diagonal_one, Matrix.one_mul, hUU]
  · have hss : (fun i => sq i * sq i) = e := funext fun i => Real.mul_self_sqrt (hepos i).le
    rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal, hss, hspec, Matrix.mul_assoc]
  · rw [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    symm
    apply inv_eq_right_inv
    rw [hspec]
    calc U * diagonal e * Uᵀ * (U * (diagonal (fun i => (sq i)⁻¹ * (sq i)⁻¹) * Uᵀ))
        = U * (diagonal e * (Uᵀ * U) * diagonal (fun i => (sq i)⁻¹ * (sq i)⁻¹)) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * Uᵀ := by
          rw [hUtU, Matrix.mul_one, diagonal_mul_diagonal]
          have : (fun i => e i * ((sq i)⁻¹ * (sq i)⁻¹)) = fun _ => (1 : ℝ) := by
            funext i
            have h1 : sq i * sq i = e i := Real.mul_self_sqrt (hepos i).le
            rw [← h1]; field_simp [(hsqpos i).ne']
          rw [this, diagonal_one, Matrix.mul_one]
      _ = 1 := hUU
theorem rank_factor {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) :
    ∃ (r : ℕ) (a : X → Fin r → ℝ) (b : Y → Fin r → ℝ), r = rankOn N X Y ∧
      (∀ (i : X) (j : Y), N i j = a i ⬝ᵥ b j) ∧
        (∀ x : Fin r → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0) := by
  classical
  set A : Matrix X Y ℝ := Matrix.of fun (i : X) (j : Y) => N i j with hA
  set V := LinearMap.range A.mulVecLin with hV
  set bV := Module.finBasis ℝ V with hbV
  let col : Y → V := fun j => ⟨A.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨Module.finrank ℝ V, fun i k => (bV k : X → ℝ) i, fun j k => bV.repr (col j) k, rfl,
    ?_, ?_⟩
  · intro i j
    have h := bV.sum_repr (col j)
    have h2 := congrArg (fun v : V => (v : X → ℝ) i) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h2
    have hcol : ((col j : V) : X → ℝ) i = N i j := by
      simp [col, Matrix.mulVecLin_apply, mulVec_single_one, hA]
    rw [← hcol, ← h2, dotProduct]
    exact sum_congr rfl fun k _ => mul_comm _ _
  · intro x hx
    have hsum : ∑ k, x k • bV k = 0 := by
      apply Subtype.ext
      funext i
      have := hx i
      simp only [dotProduct] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
      rw [← this]
      exact sum_congr rfl fun k _ => mul_comm _ _
    funext k
    exact Fintype.linearIndependent_iff.1 bV.linearIndependent x hsum k
noncomputable def embR {r : ℕ} (s : ℕ) (v : Fin r → ℝ) : EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 (fun k : Fin s => if hk : (k : ℕ) < r then v ⟨k, hk⟩ else 0)
theorem embR_inner {r s : ℕ} (hrs : r ≤ s) (v w : Fin r → ℝ) :
    inner ℝ (embR s v) (embR s w) = v ⬝ᵥ w := by
  let f : ℕ → ℝ := fun n => if h : n < r then v ⟨n, h⟩ * w ⟨n, h⟩ else 0
  have h1 : inner ℝ (embR s v) (embR s w) = ∑ k : Fin s, f k := by
    simp only [embR, PiLp.inner_apply, f]
    refine sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < r <;> simp [hk, mul_comm]
  have h2 : v ⬝ᵥ w = ∑ k : Fin r, f k := by
    simp only [dotProduct, f]
    exact sum_congr rfl fun k _ => by simp [k.2]
  rw [h1, h2, Fin.sum_univ_eq_sum_range f s, Fin.sum_univ_eq_sum_range f r]
  symm
  refine sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun n _ hn => ?_
  simp only [mem_range] at hn
  simp [f, hn]
theorem embR_norm_sq {r s : ℕ} (hrs : r ≤ s) (v : Fin r → ℝ) : ‖embR s v‖ ^ 2 = v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq, embR_inner hrs]
theorem norm_le_of_sq_le {E : Type*} [NormedAddCommGroup E] {e : E} {B : ℝ} (hB : 0 ≤ B)
    (h : ‖e‖ ^ 2 ≤ B ^ 2) : ‖e‖ ≤ B := by
  nlinarith [norm_nonneg e]
theorem john_factor_proved {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (s : ℕ) (hs1 : 1 ≤ s) (K : ℝ) (hK0 : 0 ≤ K)
    (hrank : rankOn N X Y ≤ s) (hK : ∀ x ∈ X, ∀ w ∈ Y, |N x w| ≤ K) :
    ∃ (u : α → EuclideanSpace ℝ (Fin s)) (v : β → EuclideanSpace ℝ (Fin s)),
      (∀ x ∈ X, ∀ w ∈ Y, N x w = inner ℝ (u x) (v w)) ∧
      (∀ x ∈ X, ‖u x‖ ≤ (s : ℝ) ^ (1 / 4 : ℝ)) ∧
      (∀ w ∈ Y, ‖v w‖ ≤ K * (s : ℝ) ^ (1 / 4 : ℝ)) := by
  classical
  obtain ⟨r, a, b, hr, hab, hspan⟩ := rank_factor N X Y
  have hrs : r ≤ s := hr ▸ hrank
  have hs4 : (0 : ℝ) ≤ (s : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · refine ⟨0, 0, fun x hx w hw => ?_, fun x _ => by simpa using hs4,
      fun w _ => by simpa using mul_nonneg hK0 hs4⟩
    have h := hab ⟨x, hx⟩ ⟨w, hw⟩
    subst hr0
    simp only [dotProduct, univ_eq_empty, sum_empty] at h
    simp [h]
  have : Nonempty X := by
    rcases isEmpty_or_nonempty X with h | h
    · exfalso
      have := hspan (fun _ => 1) (fun i => isEmptyElim i)
      have h1 := congrFun this ⟨0, hr1⟩
      simp at h1
    · exact h
  obtain ⟨lam, hlam0, hlam1, hMpd, hopt⟩ := kw_design a hr1 hspan
  obtain ⟨L, R, hLR, hRR, hLL⟩ := pd_factor _ hMpd
  set c : ℝ := (r : ℝ) ^ (1 / 4 : ℝ) with hc
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hcpos : 0 < c := Real.rpow_pos_of_pos hrpos _
  have hc2 : c ^ 2 = Real.sqrt r := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hrpos.le, Real.sqrt_eq_rpow]; norm_num
  have hcs : c ≤ (s : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hrpos.le (by exact_mod_cast hrs) (by norm_num)
  refine ⟨fun x => if hx : x ∈ X then c⁻¹ • embR s (L *ᵥ a ⟨x, hx⟩) else 0,
    fun w => if hw : w ∈ Y then c • embR s (R *ᵥ b ⟨w, hw⟩) else 0, ?_, ?_, ?_⟩
  · intro x hx w hw
    simp only [dif_pos hx, dif_pos hw, inner_smul_left, inner_smul_right, embR_inner hrs,
      dot_mulVec_mulVec, hLR, Matrix.one_mulVec, RCLike.conj_to_real]
    rw [hab ⟨x, hx⟩ ⟨w, hw⟩]
    field_simp
  · intro x hx
    simp only [dif_pos hx, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hcpos]
    have hq : ‖embR s (L *ᵥ a ⟨x, hx⟩)‖ ≤ Real.sqrt r := by
      refine norm_le_of_sq_le (Real.sqrt_nonneg _) ?_
      rw [embR_norm_sq hrs, dot_mulVec_mulVec, hLL, Real.sq_sqrt hrpos.le]
      exact hopt _
    calc c⁻¹ * ‖embR s (L *ᵥ a ⟨x, hx⟩)‖ ≤ c⁻¹ * Real.sqrt r :=
          mul_le_mul_of_nonneg_left hq (inv_nonneg.2 hcpos.le)
      _ = c := by rw [← hc2]; field_simp
      _ ≤ _ := hcs
  · intro w hw
    simp only [dif_pos hw, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    have hq : ‖embR s (R *ᵥ b ⟨w, hw⟩)‖ ≤ K := by
      refine norm_le_of_sq_le hK0 ?_
      rw [embR_norm_sq hrs, dot_mulVec_mulVec, hRR, designMat_quad]
      calc ∑ i, lam i * (a i ⬝ᵥ b ⟨w, hw⟩) * (a i ⬝ᵥ b ⟨w, hw⟩)
          ≤ ∑ i, lam i * K ^ 2 := by
            refine sum_le_sum fun i _ => ?_
            have hN := hK i.1 i.2 w hw
            rw [show N i w = a i ⬝ᵥ b ⟨w, hw⟩ from hab i ⟨w, hw⟩] at hN
            have : (a i ⬝ᵥ b ⟨w, hw⟩) * (a i ⬝ᵥ b ⟨w, hw⟩) ≤ K ^ 2 := by
              rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hN 2
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this (hlam0 i)
        _ = K ^ 2 := by rw [← sum_mul, hlam1, one_mul]
    calc c * ‖embR s (R *ᵥ b ⟨w, hw⟩)‖ ≤ c * K := mul_le_mul_of_nonneg_left hq hcpos.le
      _ = K * c := mul_comm _ _
      _ ≤ K * (s : ℝ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hcs hK0
end E1088
end
section
open Finset MeasureTheory ProbabilityTheory Real
namespace E1088
noncomputable def roundsT (K δ : ℝ) (s : ℕ) : ℕ :=
  ⌈Real.pi * K * Real.sqrt s * Real.log (2 / δ ^ 2)⌉₊
theorem john_factor {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (s : ℕ) (hs1 : 1 ≤ s) (K : ℝ) (hK0 : 0 ≤ K)
    (hrank : rankOn N X Y ≤ s) (hK : ∀ x ∈ X, ∀ w ∈ Y, |N x w| ≤ K) :
    ∃ (u : α → EuclideanSpace ℝ (Fin s)) (v : β → EuclideanSpace ℝ (Fin s)),
      (∀ x ∈ X, ∀ w ∈ Y, N x w = inner ℝ (u x) (v w)) ∧
      (∀ x ∈ X, ‖u x‖ ≤ (s : ℝ) ^ (1 / 4 : ℝ)) ∧
      (∀ w ∈ Y, ‖v w‖ ≤ K * (s : ℝ) ^ (1 / 4 : ℝ)) :=
  john_factor_proved N X Y s hs1 K hK0 hrank hK
def quadrant {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) : Set (EuclideanSpace ℝ (Fin s)) :=
  {g | 0 ≤ inner ℝ g u ∧ 0 ≤ inner ℝ g v}
theorem sheppard {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin s))).real (quadrant u v) =
      1 / 2 - Real.arccos (inner ℝ u v) / (2 * Real.pi) :=
  sheppard_general u v hu hv
theorem measurableSet_quadrant {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) :
    MeasurableSet (quadrant u v) := by
  have h1 : IsClosed {g : EuclideanSpace ℝ (Fin s) | 0 ≤ inner ℝ g u} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  have h2 : IsClosed {g : EuclideanSpace ℝ (Fin s) | 0 ≤ inner ℝ g v} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  exact (h1.inter h2).measurableSet
theorem sheppard_pos {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : 0 ≤ inner ℝ u v) :
    1 / 4 ≤ (stdGaussian (EuclideanSpace ℝ (Fin s))).real (quadrant u v) := by
  rw [sheppard u v hu hv]
  have h1 := Real.arccos_le_pi_div_two.2 ha
  have hπ := Real.pi_pos
  have : Real.arccos (inner ℝ u v) / (2 * Real.pi) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith
theorem sheppard_neg {s : ℕ} (u v : EuclideanSpace ℝ (Fin s)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ha : inner ℝ u v ≤ -b) :
    (stdGaussian (EuclideanSpace ℝ (Fin s))).real (quadrant u v) ≤
      1 / 4 - b / (2 * Real.pi) := by
  rw [sheppard u v hu hv]
  have hπ := Real.pi_pos
  have h1 : Real.arccos (-b) ≤ Real.arccos (inner ℝ u v) := Real.arccos_le_arccos ha
  rw [Real.arccos_neg, Real.arccos_eq_pi_div_two_sub_arcsin] at h1
  have h2 : b ≤ Real.arcsin b := by
    have := Real.sin_le (Real.arcsin_nonneg.2 hb0)
    rwa [Real.sin_arcsin (by linarith) hb1] at this
  have h3 : (Real.pi / 2 + b) / (2 * Real.pi) ≤ Real.arccos (inner ℝ u v) / (2 * Real.pi) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h4 : (Real.pi / 2 + b) / (2 * Real.pi) = 1 / 4 + b / (2 * Real.pi) := by
    field_simp; ring
  linarith
theorem one_sub_pow_le_exp (y L : ℝ) (T : ℕ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hT : L ≤ y * T) :
    (1 - y) ^ T ≤ Real.exp (-L) := by
  calc (1 - y) ^ T ≤ (Real.exp (-y)) ^ T := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (-y); linarith
    _ = Real.exp (-(y * T)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
theorem rankOn_eq_zero_imp {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (h : rankOn N X Y = 0) : ∀ x ∈ X, ∀ w ∈ Y, N x w = 0 := by
  intro x hx w hw
  obtain ⟨r, U, V, hr, hUV⟩ := exists_factor (Matrix.of fun (i : X) (j : Y) => N i j)
  have hr0 : r = 0 := by rw [hr]; exact h
  subst hr0
  have := congrFun (congrFun hUV ⟨x, hx⟩) ⟨w, hw⟩
  simpa [Matrix.mul_apply] using this
set_option maxHeartbeats 2000000 in
theorem lemmaR {α β : Type*} [DecidableEq α] [DecidableEq β] (N : α → β → ℝ)
    (X : Finset α) (Y : Finset β) (s : ℕ) (K δ : ℝ) (hs : rankOn N X Y ≤ s)
    (hN : ∀ x ∈ X, ∀ w ∈ Y, 1 / 2 ≤ |N x w| ∧ |N x w| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hpos : δ * (#X * #Y) ≤ #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y,
      δ / 2 * #X ≤ 4 ^ roundsT K δ s * #X' ∧ δ / 2 * #Y ≤ 4 ^ roundsT K δ s * #Y' ∧
      (#((X' ×ˢ Y').filter fun p => N p.1 p.2 < 0) : ℝ) ≤ δ * (#X' * #Y') := by
  classical
  set T := roundsT K δ s with hT
  have h4T : (1 : ℝ) ≤ 4 ^ T := one_le_pow₀ (by norm_num)
  by_cases hne : X.Nonempty ∧ Y.Nonempty
  swap
  · refine ⟨X, subset_refl _, Y, subset_refl _, ?_, ?_, ?_⟩
    · have : (0 : ℝ) ≤ #X := Nat.cast_nonneg _
      nlinarith
    · have : (0 : ℝ) ≤ #Y := Nat.cast_nonneg _
      nlinarith
    · have : X ×ˢ Y = ∅ := by
        rcases not_and_or.1 hne with h | h
        · rw [not_nonempty_iff_eq_empty] at h; simp [h]
        · rw [not_nonempty_iff_eq_empty] at h; simp [h]
      simp only [this, filter_empty, card_empty, Nat.cast_zero]
      positivity
  obtain ⟨⟨x0, hx0⟩, ⟨w0, hw0⟩⟩ := hne
  have hK : 1 / 2 ≤ K := (hN x0 hx0 w0 hw0).1.trans (hN x0 hx0 w0 hw0).2
  have hs1 : 1 ≤ s := by
    by_contra h
    have h0 : rankOn N X Y = 0 := by omega
    have h1 := rankOn_eq_zero_imp N X Y h0 x0 hx0 w0 hw0
    have h2 := (hN x0 hx0 w0 hw0).1
    rw [h1, abs_zero] at h2; norm_num at h2
  obtain ⟨u, v, hNuv, hu, hv⟩ := john_factor N X Y s hs1 K (by linarith) hs (fun x hx w hw => (hN x hx w hw).2)
  set c4 : ℝ := (s : ℝ) ^ (1 / 4 : ℝ) with hc4
  have hs1r : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hc4pos : 0 < c4 := Real.rpow_pos_of_pos (by linarith) _
  have hc4sq : c4 * c4 = Real.sqrt s := by
    rw [hc4, ← Real.rpow_add (by linarith), Real.sqrt_eq_rpow]; norm_num
  have hsqrt1 : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs1r
  have hun : ∀ x ∈ X, 0 < ‖u x‖ := by
    intro x hx
    rw [norm_pos_iff]; intro h0
    have := (hN x hx w0 hw0).1
    rw [hNuv x hx w0 hw0, h0, inner_zero_left, abs_zero] at this; norm_num at this
  have hvn : ∀ w ∈ Y, 0 < ‖v w‖ := by
    intro w hw
    rw [norm_pos_iff]; intro h0
    have := (hN x0 hx0 w hw).1
    rw [hNuv x0 hx0 w hw, h0, inner_zero_right, abs_zero] at this; norm_num at this
  set uh : α → EuclideanSpace ℝ (Fin s) := fun x => ‖u x‖⁻¹ • u x with huh
  set vh : β → EuclideanSpace ℝ (Fin s) := fun w => ‖v w‖⁻¹ • v w with hvh
  have huh1 : ∀ x ∈ X, ‖uh x‖ = 1 := fun x hx => by
    simp only [huh]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hun x hx).ne']
  have hvh1 : ∀ w ∈ Y, ‖vh w‖ = 1 := fun w hw => by
    simp only [hvh]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hvn w hw).ne']
  have hinner : ∀ x ∈ X, ∀ w ∈ Y, inner ℝ (uh x) (vh w) = N x w / (‖u x‖ * ‖v w‖) := by
    intro x hx w hw
    simp only [huh, hvh]
    rw [real_inner_smul_left, real_inner_smul_right, ← hNuv x hx w hw]
    field_simp
  set b : ℝ := 1 / (2 * K * Real.sqrt s) with hb
  have hKs : 1 ≤ 2 * K * Real.sqrt s := by nlinarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb1 : b ≤ 1 := by rw [hb, div_le_one (by linarith)]; exact hKs
  have hbK : b * (K * Real.sqrt s) = 1 / 2 := by
    rw [hb]; field_simp
  have hmarg_pos : ∀ x ∈ X, ∀ w ∈ Y, 0 < N x w → 0 ≤ inner ℝ (uh x) (vh w) := by
    intro x hx w hw h
    rw [hinner x hx w hw]
    exact div_nonneg h.le (mul_pos (hun x hx) (hvn w hw)).le
  have hmarg_neg : ∀ x ∈ X, ∀ w ∈ Y, N x w < 0 → inner ℝ (uh x) (vh w) ≤ -b := by
    intro x hx w hw h
    rw [hinner x hx w hw]
    have hP := mul_pos (hun x hx) (hvn w hw)
    have hPle : ‖u x‖ * ‖v w‖ ≤ K * Real.sqrt s := by
      have := mul_le_mul (hu x hx) (hv w hw) (norm_nonneg _) hc4pos.le
      rw [← hc4sq]; nlinarith
    have hNle : N x w ≤ -(1 / 2) := by
      have := (hN x hx w hw).1
      rw [abs_of_neg h] at this; linarith
    rw [div_le_iff₀ hP]
    nlinarith
  set γ := stdGaussian (EuclideanSpace ℝ (Fin s)) with hγ
  set p : α → β → ℝ := fun x w => γ.real (quadrant (uh x) (vh w)) with hp
  have hp_pos : ∀ x ∈ X, ∀ w ∈ Y, 0 < N x w → 1 / 4 ≤ p x w := fun x hx w hw h =>
    sheppard_pos _ _ (huh1 x hx) (hvh1 w hw) (hmarg_pos x hx w hw h)
  have hp_neg : ∀ x ∈ X, ∀ w ∈ Y, N x w < 0 → p x w ≤ 1 / 4 * (1 - 2 * b / Real.pi) := by
    intro x hx w hw h
    have := sheppard_neg _ _ (huh1 x hx) (hvh1 w hw) b hb0.le hb1 (hmarg_neg x hx w hw h)
    have hπ := Real.pi_pos
    have e : 1 / 4 - b / (2 * Real.pi) = 1 / 4 * (1 - 2 * b / Real.pi) := by field_simp; ring
    linarith
  have hp_nn : ∀ x w, 0 ≤ p x w := fun x w => measureReal_nonneg
  set μ : Measure (Fin T → EuclideanSpace ℝ (Fin s)) := Measure.pi fun _ => γ with hμ
  set B : α → β → Set (Fin T → EuclideanSpace ℝ (Fin s)) :=
    fun x w => Set.pi Set.univ fun _ => quadrant (uh x) (vh w) with hB
  have hBmeas : ∀ x w, MeasurableSet (B x w) := fun x w =>
    MeasurableSet.univ_pi fun _ => measurableSet_quadrant _ _
  have hμB : ∀ x w, μ.real (B x w) = p x w ^ T := by
    intro x w
    simp only [hμ, hB, measureReal_def, Measure.pi_pi, prod_const, card_univ, Fintype.card_fin,
      ENNReal.toReal_pow, hp]
  set Qp := (X ×ˢ Y).filter fun q => 0 < N q.1 q.2 with hQp
  set Qn := (X ×ˢ Y).filter fun q => N q.1 q.2 < 0 with hQn
  set F : (Fin T → EuclideanSpace ℝ (Fin s)) → ℝ := fun ω =>
    (∑ q ∈ Qp, (B q.1 q.2).indicator 1 ω) - (1 / δ) * ∑ q ∈ Qn, (B q.1 q.2).indicator 1 ω
    with hF
  have hint : ∀ q : α × β, Integrable ((B q.1 q.2).indicator (1 : (Fin T → EuclideanSpace ℝ (Fin s)) → ℝ)) μ := fun q =>
    (integrable_const (1 : ℝ)).indicator (hBmeas q.1 q.2)
  have hFint : Integrable F μ :=
    (integrable_finsetSum _ fun q _ => hint q).sub
      ((integrable_finsetSum _ fun q _ => hint q).const_mul _)
  have hIF : ∫ ω, F ω ∂μ = (∑ q ∈ Qp, p q.1 q.2 ^ T) - (1 / δ) * ∑ q ∈ Qn, p q.1 q.2 ^ T := by
    simp only [hF]
    rw [integral_sub (integrable_finsetSum _ fun q _ => hint q)
      ((integrable_finsetSum _ fun q _ => hint q).const_mul _), integral_const_mul,
      integral_finsetSum _ fun q _ => hint q, integral_finsetSum _ fun q _ => hint q]
    simp only [integral_indicator_one (hBmeas _ _), hμB]
  set y : ℝ := 2 * b / Real.pi with hy
  have hπ := Real.pi_pos
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one hπ]; have := Real.pi_gt_three; linarith
  have hL : Real.log (2 / δ ^ 2) ≤ y * T := by
    have hlog : 0 ≤ Real.log (2 / δ ^ 2) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hTge : Real.pi * K * Real.sqrt s * Real.log (2 / δ ^ 2) ≤ T := Nat.le_ceil _
    have : y * (Real.pi * K * Real.sqrt s * Real.log (2 / δ ^ 2)) = Real.log (2 / δ ^ 2) := by
      rw [hy]
      have : 2 * b * (K * Real.sqrt s) = 1 := by linarith
      field_simp
      linear_combination Real.log (2 / δ ^ 2) * this
    nlinarith
  have hexp : (1 - y) ^ T ≤ δ ^ 2 / 2 := by
    have := one_sub_pow_le_exp y _ T hy0 hy1 hL
    rwa [Real.exp_neg, Real.exp_log (by positivity), inv_div] at this
  have hq : (0 : ℝ) < (1 / 4) ^ T := by positivity
  have hsumP : #Qp * (1 / 4 : ℝ) ^ T ≤ ∑ q ∈ Qp, p q.1 q.2 ^ T := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun q hq' => ?_
    obtain ⟨hqXY, hq0⟩ := mem_filter.1 hq'
    obtain ⟨hqx, hqw⟩ := mem_product.1 hqXY
    exact pow_le_pow_left₀ (by norm_num) (hp_pos q.1 hqx q.2 hqw hq0) T
  have hsumN : ∑ q ∈ Qn, p q.1 q.2 ^ T ≤ (#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2)) := by
    calc ∑ q ∈ Qn, p q.1 q.2 ^ T ≤ ∑ _q ∈ Qn, (1 / 4 : ℝ) ^ T * (δ ^ 2 / 2) := by
          refine sum_le_sum fun q hq' => ?_
          obtain ⟨hqXY, hq0⟩ := mem_filter.1 hq'
          obtain ⟨hqx, hqw⟩ := mem_product.1 hqXY
          calc p q.1 q.2 ^ T ≤ (1 / 4 * (1 - 2 * b / Real.pi)) ^ T :=
                pow_le_pow_left₀ (hp_nn _ _) (hp_neg q.1 hqx q.2 hqw hq0) T
            _ = (1 / 4) ^ T * (1 - y) ^ T := by rw [mul_pow]
            _ ≤ (1 / 4) ^ T * (δ ^ 2 / 2) := mul_le_mul_of_nonneg_left hexp hq.le
      _ = #Qn * ((1 / 4 : ℝ) ^ T * (δ ^ 2 / 2)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : #Qn ≤ #X * #Y := (card_filter_le _ _).trans (card_product X Y).le
          exact_mod_cast this
  have hEF : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ ∫ ω, F ω ∂μ := by
    rw [hIF]
    have h1 : δ * (#X * #Y) * (1 / 4 : ℝ) ^ T ≤ ∑ q ∈ Qp, p q.1 q.2 ^ T :=
      (mul_le_mul_of_nonneg_right hpos hq.le).trans hsumP
    have h2 : (1 / δ) * ∑ q ∈ Qn, p q.1 q.2 ^ T ≤
        (1 / δ) * ((#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2))) :=
      mul_le_mul_of_nonneg_left hsumN (by positivity)
    have h3 : (1 / δ) * ((#X * #Y : ℝ) * ((1 / 4) ^ T * (δ ^ 2 / 2))) =
        (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) := by field_simp
    nlinarith
  obtain ⟨ω, hω⟩ := exists_integral_le hFint
  set X' := X.filter fun x => ∀ t, 0 ≤ inner ℝ (ω t) (uh x) with hX'
  set Y' := Y.filter fun w => ∀ t, 0 ≤ inner ℝ (ω t) (vh w) with hY'
  have hmemB : ∀ q ∈ X ×ˢ Y, ω ∈ B q.1 q.2 ↔ q ∈ X' ×ˢ Y' := by
    intro q hq'
    obtain ⟨hqx, hqw⟩ := mem_product.1 hq'
    simp only [hB, Set.mem_pi, Set.mem_univ, true_implies, quadrant, Set.mem_ofPred_eq, hX', hY',
      mem_product, mem_filter]
    constructor
    · intro h; exact ⟨⟨hqx, fun t => (h t).1⟩, ⟨hqw, fun t => (h t).2⟩⟩
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ t; exact ⟨h1 t, h2 t⟩
  have hcount : ∀ (Q : Finset (α × β)) (P : α × β → Prop) [DecidablePred P],
      Q = (X ×ˢ Y).filter P →
      ∑ q ∈ Q, (B q.1 q.2).indicator (1 : (Fin T → EuclideanSpace ℝ (Fin s)) → ℝ) ω = #((X' ×ˢ Y').filter P) := by
    intro Q P _ hQ
    rw [hQ]
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [sum_boole]
    norm_cast
    congr 1
    ext q
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hq', hP⟩, hB'⟩
      exact ⟨(hmemB q hq').1 hB', hP⟩
    · rintro ⟨hq', hP⟩
      have hq'' : q ∈ X ×ˢ Y := by
        obtain ⟨a, b'⟩ := mem_product.1 hq'
        exact mem_product.2 ⟨(mem_filter.1 a).1, (mem_filter.1 b').1⟩
      exact ⟨⟨hq'', hP⟩, (hmemB q hq'').2 hq'⟩
  have hFω : F ω = (#((X' ×ˢ Y').filter fun q => 0 < N q.1 q.2) : ℝ) -
      (1 / δ) * (#((X' ×ˢ Y').filter fun q => N q.1 q.2 < 0) : ℝ) := by
    simp only [hF]
    rw [hcount Qp (fun q => 0 < N q.1 q.2) hQp, hcount Qn (fun q => N q.1 q.2 < 0) hQn]
  set Pc : ℝ := ((#((X' ×ˢ Y').filter fun q => 0 < N q.1 q.2) : ℕ) : ℝ) with hPc
  set Nc : ℝ := ((#((X' ×ˢ Y').filter fun q => N q.1 q.2 < 0) : ℕ) : ℝ) with hNc
  have hmain : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ Pc - (1 / δ) * Nc := by
    rw [← hFω]; linarith
  have hPle : Pc ≤ #X' * #Y' := by
    have : #((X' ×ˢ Y').filter fun q => 0 < N q.1 q.2) ≤ #X' * #Y' :=
      (card_filter_le _ _).trans (card_product X' Y').le
    rw [hPc]; exact_mod_cast this
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 ⟨x0, hx0⟩
  have hYpos : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 ⟨w0, hw0⟩
  have hNc0 : 0 ≤ Nc := Nat.cast_nonneg _
  have hpos' : 0 < (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) := by positivity
  have hX'le : (#X' : ℝ) ≤ #X := by exact_mod_cast card_le_card (filter_subset _ _)
  have hY'le : (#Y' : ℝ) ≤ #Y := by exact_mod_cast card_le_card (filter_subset _ _)
  have h4q : (4 : ℝ) ^ T * (1 / 4) ^ T = 1 := by rw [← mul_pow]; norm_num
  have hXY' : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ #X' * #Y' := by
    have : 0 ≤ (1 / δ) * Nc := by positivity
    linarith
  refine ⟨X', filter_subset _ _, Y', filter_subset _ _, ?_, ?_, ?_⟩
  ·
    have h1 : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ #X' * #Y := by
      have : (#X' : ℝ) * #Y' ≤ #X' * #Y := mul_le_mul_of_nonneg_left hY'le (Nat.cast_nonneg _)
      linarith
    have h2 : (1 / 4 : ℝ) ^ T * (δ / 2) * #X ≤ #X' := by
      have := h1
      rw [show (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) = ((1 / 4 : ℝ) ^ T * (δ / 2) * #X) * #Y
        by ring] at this
      exact le_of_mul_le_mul_right this hYpos
    calc δ / 2 * #X = 4 ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #X) := by
          rw [show (4 : ℝ) ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #X) =
            ((4 : ℝ) ^ T * (1 / 4) ^ T) * (δ / 2 * #X) by ring, h4q, one_mul]
      _ ≤ 4 ^ T * #X' := mul_le_mul_of_nonneg_left h2 (by positivity)
  · have h1 : (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) ≤ #X * #Y' := by
      have : (#X' : ℝ) * #Y' ≤ #X * #Y' := mul_le_mul_of_nonneg_right hX'le (Nat.cast_nonneg _)
      linarith
    have h2 : (1 / 4 : ℝ) ^ T * (δ / 2) * #Y ≤ #Y' := by
      have := h1
      rw [show (1 / 4 : ℝ) ^ T * (δ / 2) * (#X * #Y) = ((1 / 4 : ℝ) ^ T * (δ / 2) * #Y) * #X
        by ring, mul_comm (#X : ℝ) (#Y' : ℝ)] at this
      exact le_of_mul_le_mul_right this hXpos
    calc δ / 2 * #Y = 4 ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #Y) := by
          rw [show (4 : ℝ) ^ T * ((1 / 4 : ℝ) ^ T * (δ / 2) * #Y) =
            ((4 : ℝ) ^ T * (1 / 4) ^ T) * (δ / 2 * #Y) by ring, h4q, one_mul]
      _ ≤ 4 ^ T * #Y' := mul_le_mul_of_nonneg_left h2 (by positivity)
  ·
    have h1 : (1 / δ) * Nc ≤ Pc := by linarith
    have h2 : Nc ≤ δ * Pc := by
      have := mul_le_mul_of_nonneg_left h1 hδ0.le
      rwa [← mul_assoc, mul_one_div_cancel hδ0.ne', one_mul] at this
    calc Nc ≤ δ * Pc := h2
      _ ≤ δ * (#X' * #Y') := mul_le_mul_of_nonneg_left hPle hδ0.le
end E1088
end
section
open Finset Matrix
namespace E1088
variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
theorem rank_finset_prod_le {m n : Type*} [Fintype m] [Fintype n] (A : Finset ι)
    (F : ι → Matrix m n ℝ) :
    (Matrix.of fun i j => ∏ t ∈ A, F t i j).rank ≤ ∏ t ∈ A, (F t).rank := by
  induction A using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    have : (Matrix.of fun (_ : m) (_ : n) => (1 : ℝ)) = vecMulVec (fun _ => 1) (fun _ => 1) := by
      ext; simp [vecMulVec]
    rw [this]; exact rank_vecMulVec_le _ _
  | insert a A haA ih =>
    have : (Matrix.of fun i j => ∏ t ∈ insert a A, F t i j) =
        F a ⊙ Matrix.of fun i j => ∏ t ∈ A, F t i j := by
      ext i j; simp [prod_insert haA]
    rw [this, prod_insert haA]
    exact (rank_hadamard_le _ _).trans (Nat.mul_le_mul_left _ ih)
theorem rank_tf_le {m n : Type*} [Fintype m] [Fintype n] (t : TF α β) (fx : m → α)
    (fw : n → β) : (Matrix.of fun i j => t.eval (fx i) (fw j)).rank ≤ 1 := by
  cases t with
  | row a =>
    have : (Matrix.of fun i j => (TF.row a : TF α β).eval (fx i) (fw j)) =
        vecMulVec (fun i => a (fx i)) (fun _ => 1) := by ext; simp [vecMulVec, TF.eval]
    rw [this]; exact rank_vecMulVec_le _ _
  | col b =>
    have : (Matrix.of fun i j => (TF.col b : TF α β).eval (fx i) (fw j)) =
        vecMulVec (fun _ => 1) (fun j => b (fw j)) := by ext; simp [vecMulVec, TF.eval]
    rw [this]; exact rank_vecMulVec_le _ _
theorem rank_neg_le {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    (-A).rank ≤ A.rank := by
  rw [show -A = (-1 : ℝ) • A by simp,
    rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero (by norm_num))]
theorem rankOn_sub_tf (M : α → β → ℝ) (t : TF α β) (X : Finset α) (Y : Finset β) :
    rankOn (fun x w => M x w - t.eval x w) X Y ≤ rankOn M X Y + 1 := by
  unfold rankOn
  have : (Matrix.of fun (i : X) (j : Y) => M i j - t.eval i j) =
      (Matrix.of fun (i : X) (j : Y) => M i j) +
        -(Matrix.of fun (i : X) (j : Y) => t.eval i j) := by
    ext; simp [sub_eq_add_neg]
  rw [this]
  refine (rank_add_le' _ _).trans (Nat.add_le_add_left ?_ _)
  exact (rank_neg_le _).trans (rank_tf_le t (fun i : X => (i : α)) (fun j : Y => (j : β)))
theorem rankOn_prod_sub (M : α → β → ℝ) (τ : ι → TF α β) (A : Finset ι) (X : Finset α)
    (Y : Finset β) (r : ℕ) (hr : rankOn M X Y ≤ r) :
    rankOn (fun x w => ∏ t ∈ A, (M x w - (τ t).eval x w)) X Y ≤ (r + 1) ^ #A := by
  unfold rankOn
  have := rank_finset_prod_le A
    (fun t => Matrix.of fun (i : X) (j : Y) => M i j - (τ t).eval i j)
  refine this.trans ?_
  calc ∏ t ∈ A, (Matrix.of fun (i : X) (j : Y) => M i j - (τ t).eval i j).rank
      ≤ ∏ _t ∈ A, (r + 1) := prod_le_prod' fun t _ =>
        (rankOn_sub_tf M (τ t) X Y).trans (by unfold rankOn at hr ⊢; omega)
    _ = (r + 1) ^ #A := by simp
theorem rankOn_rescale (M : α → β → ℝ) (φ : α → ℝ) (θ : β → ℝ) (qr : α → ℝ) (qc : β → ℝ)
    (X : Finset α) (Y : Finset β) :
    rankOn (fun x w => (M x w - (φ x + θ w)) / (qr x * qc w)) X Y ≤ rankOn M X Y + 2 := by
  unfold rankOn
  have h1 : (Matrix.of fun (i : X) (j : Y) => (M i j - (φ i + θ j)) / (qr i * qc j)) =
      ((Matrix.of fun (i : X) (j : Y) => M i j) + vecMulVec (fun i : X => -φ i) (fun _ => 1) +
        vecMulVec (fun _ => 1) (fun j : Y => -θ j)) ⊙
        vecMulVec (fun i : X => 1 / qr i) (fun j : Y => 1 / qc j) := by
    ext i j
    simp only [of_apply, hadamard_apply, Matrix.add_apply, vecMulVec_apply, one_div,
      div_eq_mul_inv, mul_inv]
    ring
  rw [h1]
  refine (rank_hadamard_le _ _).trans ?_
  have h2 := rank_vecMulVec_le (fun i : X => 1 / qr i) (fun j : Y => 1 / qc j)
  have h3 := rank_add_le' ((Matrix.of fun (i : X) (j : Y) => M i j) +
    vecMulVec (fun i : X => -φ i) (fun _ => 1)) (vecMulVec (fun _ => 1) (fun j : Y => -θ j))
  have h4 := rank_add_le' (Matrix.of fun (i : X) (j : Y) => M i j)
    (vecMulVec (fun i : X => -φ i) (fun _ => 1))
  have h5 := rank_vecMulVec_le (fun i : X => -φ i) (fun _ : Y => (1 : ℝ))
  have h6 := rank_vecMulVec_le (fun _ : X => (1 : ℝ)) (fun j : Y => -θ j)
  calc _ ≤ (rank (Matrix.of fun (i : X) (j : Y) => M i j) + 2) * 1 :=
        Nat.mul_le_mul (by omega) h2
    _ = _ := by ring
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
def RainbowF {P : Type*} (δ : P → P → ℝ) (A : Finset P) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, ∀ c ∈ A, ∀ c' ∈ A, a ≠ a' → c ≠ c' → δ a a' = δ c c' →
    (a = c ∧ a' = c') ∨ (a = c' ∧ a' = c)
abbrev Rainbow (A : Finset (ℝ^d)) : Prop := RainbowF dist A
noncomputable def dists (A : Finset (ℝ^d)) : Finset ℝ := A.offDiag.image fun p => dist p.1 p.2
set_option maxHeartbeats 3000000 in
theorem rainbowF_insert_insert {P : Type*} [DecidableEq P] (δ : P → P → ℝ)
    (hcomm : ∀ u v, δ u v = δ v u) (S : Finset P) (b x : P)
    (hbS : RainbowF δ (insert b S)) (hxS : RainbowF δ (insert x S))
    (hcross : ∀ s ∈ S, ∀ s' ∈ S, δ x s ≠ δ b s')
    (h1 : ∀ s ∈ S, δ x b ≠ δ b s) (h2 : ∀ s ∈ S, δ x b ≠ δ x s)
    (h3 : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → δ x b ≠ δ s s') :
    RainbowF δ (insert x (insert b S)) := by
  have C : ∀ s s', δ x s = δ b s' → s ∈ S → s' ∈ S → False :=
    fun s s' h hs hs' => hcross s hs s' hs' h
  have E1 : ∀ s, δ x b = δ b s → s ∈ S → False := fun s h hs => h1 s hs h
  have E2 : ∀ s, δ x b = δ x s → s ∈ S → False := fun s h hs => h2 s hs h
  have E3 : ∀ s s', δ x b = δ s s' → s ∈ S → s' ∈ S → s ≠ s' → False :=
    fun s s' h hs hs' hne => h3 s hs s' hs' hne h
  intro a ha a' ha' c hc c' hc' hne hne' hd
  have hd1 : δ a a' = δ c c' := hd
  have hd2 : δ c c' = δ a a' := hd.symm
  have hd3 : δ a' a = δ c c' := by rw [hcomm]; exact hd
  have hd4 : δ a a' = δ c' c := by rw [hcomm c']; exact hd
  have hd5 : δ a' a = δ c' c := by rw [hcomm a', hcomm c']; exact hd
  have hd6 : δ c c' = δ a' a := by rw [hcomm a']; exact hd.symm
  have hd7 : δ c' c = δ a a' := by rw [hcomm]; exact hd.symm
  have hd8 : δ c' c = δ a' a := by rw [hcomm c', hcomm a']; exact hd.symm
  simp only [mem_insert] at ha ha' hc hc'
  rcases ha with rfl | rfl | ha <;> rcases ha' with rfl | rfl | ha' <;>
    rcases hc with rfl | rfl | hc <;> rcases hc' with rfl | rfl | hc' <;>
  first
    | exact absurd rfl hne
    | exact absurd rfl hne'
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩
    | exact hxS _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) hne hne' hd
    | exact hbS _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) _ (by (first | exact mem_insert_self _ _ | exact mem_insert_of_mem (by assumption) | exact mem_insert_of_mem (mem_insert_self _ _) | exact mem_insert_of_mem (mem_insert_of_mem (by assumption)))) hne hne' hd
    | exact (C _ _ hd1 (by assumption) (by assumption)).elim
    | exact (E1 _ hd1 (by assumption)).elim
    | exact (E2 _ hd1 (by assumption)).elim
    | exact (E3 _ _ hd1 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd1 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd2 (by assumption) (by assumption)).elim
    | exact (E1 _ hd2 (by assumption)).elim
    | exact (E2 _ hd2 (by assumption)).elim
    | exact (E3 _ _ hd2 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd2 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd3 (by assumption) (by assumption)).elim
    | exact (E1 _ hd3 (by assumption)).elim
    | exact (E2 _ hd3 (by assumption)).elim
    | exact (E3 _ _ hd3 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd3 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd4 (by assumption) (by assumption)).elim
    | exact (E1 _ hd4 (by assumption)).elim
    | exact (E2 _ hd4 (by assumption)).elim
    | exact (E3 _ _ hd4 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd4 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd5 (by assumption) (by assumption)).elim
    | exact (E1 _ hd5 (by assumption)).elim
    | exact (E2 _ hd5 (by assumption)).elim
    | exact (E3 _ _ hd5 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd5 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd6 (by assumption) (by assumption)).elim
    | exact (E1 _ hd6 (by assumption)).elim
    | exact (E2 _ hd6 (by assumption)).elim
    | exact (E3 _ _ hd6 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd6 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd7 (by assumption) (by assumption)).elim
    | exact (E1 _ hd7 (by assumption)).elim
    | exact (E2 _ hd7 (by assumption)).elim
    | exact (E3 _ _ hd7 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd7 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
    | exact (C _ _ hd8 (by assumption) (by assumption)).elim
    | exact (E1 _ hd8 (by assumption)).elim
    | exact (E2 _ hd8 (by assumption)).elim
    | exact (E3 _ _ hd8 (by assumption) (by assumption) (by assumption)).elim
    | exact (E3 _ _ hd8 (by assumption) (by assumption) (Ne.symm (by assumption))).elim
theorem rainbow_insert_insert (S : Finset (ℝ^d)) (b x : ℝ^d)
    (hbS : Rainbow (insert b S)) (hxS : Rainbow (insert x S))
    (hcross : ∀ s ∈ S, ∀ s' ∈ S, dist x s ≠ dist b s')
    (h1 : ∀ s ∈ S, dist x b ≠ dist b s) (h2 : ∀ s ∈ S, dist x b ≠ dist x s)
    (h3 : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → dist x b ≠ dist s s') :
    Rainbow (insert x (insert b S)) :=
  rainbowF_insert_insert dist dist_comm S b x hbS hxS hcross h1 h2 h3
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
structure Config (X S W : Finset (ℝ^d)) (j : ℕ) (σ : ℝ) : Prop where
  subX : S ⊆ X
  rainbow : Rainbow S
  card : S.card = j
  subW : W ⊆ X
  disj : Disjoint W S
  ext : ∀ x ∈ W, Rainbow (insert x S)
  cap : ∀ s ∈ S, ∀ t : ℝ, 0 < t → ((W.filter fun x => dist x s = t).card : ℝ) < σ
noncomputable def Rb (S : Finset (ℝ^d)) (b : ℝ^d) : Finset ℝ := dists S ∪ S.image (dist b)
noncomputable def Big (S W : Finset (ℝ^d)) (b : ℝ^d) (τ : ℝ) : Finset ℝ :=
  ((W.erase b).image fun x => dist x b).filter fun l =>
    l ∉ Rb S b ∧ τ ≤ ((W.filter fun x => dist x b = l).card : ℝ)
def ClaimAt (X : Finset (ℝ^d)) (j : ℕ) (Γ σmin : ℝ) : Prop :=
  ∀ S W : Finset (ℝ^d), ∀ σ : ℝ, Config X S W j σ → σmin ≤ σ → (W.card : ℝ) ≤ Γ * σ
theorem mem_dists {A : Finset (ℝ^d)} {a a' : ℝ^d} (ha : a ∈ A) (ha' : a' ∈ A) (h : a ≠ a') :
    dist a a' ∈ dists A :=
  mem_image.2 ⟨(a, a'), mem_offDiag.2 ⟨ha, ha', h⟩, rfl⟩
theorem pos_of_mem_dists {A : Finset (ℝ^d)} {t : ℝ} (h : t ∈ dists A) : 0 < t := by
  obtain ⟨p, hp, rfl⟩ := mem_image.1 h
  exact dist_pos.2 (mem_offDiag.1 hp).2.2
theorem sq_ne_of_ne {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≠ b ^ 2) : a ≠ b := by
  rintro rfl; exact h rfl
theorem ne_of_sq_sub_ne {a b : ℝ} (h : a ^ 2 - b ^ 2 ≠ 0) : a ≠ b := by
  rintro rfl; simp at h
theorem lemma_1_2 (X : Finset (ℝ^d)) (D : ℕ) (hD : affDim X ≤ D) (r K : ℕ) (Γ σmin σ τ : ℝ)
    (hclaim : ClaimAt X (r + 1) Γ σmin) (S W : Finset (ℝ^d)) (hc : Config X S W r σ)
    (hΓ : 0 ≤ Γ) (hσpos : 0 < σ) (hσ : σmin ≤ σ) (hτ : σ ≤ τ) (hbig : ∀ b ∈ W, (Big S W b τ).card ≤ K) :
    (W.card : ℝ) ≤ (((D + 2) ^ (K + 2 * r + (dists S).card)) ^ 2 : ℕ) *
      (Γ * τ + r ^ 2 * σ + 1) := by
  classical
  let J := Fin K ⊕ (S ⊕ (S ⊕ dists S))
  have hJ : Fintype.card J = K + 2 * r + (dists S).card := by
    simp only [J, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hc.card]; ring
  let lam : ℝ^d → Fin K → ℝ := fun b i =>
    if h : (i : ℕ) < (Big S W b τ).card then ((Big S W b τ).equivFin.symm ⟨i, h⟩ : ℝ) else 0
  let f : J → ℝ^d → ℝ := fun k b => match k with
    | Sum.inl i => if (i : ℕ) < (Big S W b τ).card then lam b i ^ 2 else -1
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl s)) => dist b s ^ 2
    | Sum.inr (Sum.inr (Sum.inr δ)) => (δ : ℝ) ^ 2
  let g : J → ℝ^d → ℝ := fun k y => match k with
    | Sum.inr (Sum.inl s) => ‖y - s‖ ^ 2
    | _ => 0
  let F : ℝ^d → ℝ^d → ℝ := fun b y => ∏ k : J, (‖b - y‖ ^ 2 - f k b - g k y)
  have hlam_mem : ∀ b (i : Fin K) (h : (i : ℕ) < (Big S W b τ).card), lam b i ∈ Big S W b τ := by
    intro b i h; simp only [lam, dif_pos h]; exact Finset.coe_mem _
  have hlam_surj : ∀ b ∈ W, ∀ l ∈ Big S W b τ, ∃ i : Fin K, (i : ℕ) < (Big S W b τ).card ∧
      lam b i = l := by
    intro b hb l hl
    set j := (Big S W b τ).equivFin ⟨l, hl⟩
    refine ⟨⟨j, lt_of_lt_of_le j.2 (hbig b hb)⟩, j.2, ?_⟩
    simp only [lam, dif_pos j.2]
    simp [j]
  have hBig_pos : ∀ b l, l ∈ Big S W b τ → 0 < l := by
    intro b l hl
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 hl).1
    exact dist_pos.2 (ne_of_mem_erase hx)
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hWX : ∀ x ∈ W, x ∈ X := fun x hx => hc.subW hx
  set Δ := ⌊Γ * τ + r ^ 2 * σ⌋₊ with hΔ
  have hrank : rankOn F W W ≤ (D + 2) ^ (K + 2 * r + (dists S).card) := by
    unfold rankOn
    have h1 := rank_finset_prod_le (Finset.univ : Finset J) (fun k => Matrix.of fun (i : W) (j : W) =>
      ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j)
    refine h1.trans ?_
    calc ∏ k ∈ (Finset.univ : Finset J), (Matrix.of fun (i : W) (j : W) =>
          ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j).rank
        ≤ ∏ _k ∈ (Finset.univ : Finset J), (D + 2) := Finset.prod_le_prod' fun k _ =>
          rank_sqdist_le_affine X D hD (fun i : W => (i : ℝ^d)) (fun j : W => (j : ℝ^d))
            (fun i => hWX _ i.2) (fun j => hWX _ j.2) _ _
      _ = (D + 2) ^ (K + 2 * r + (dists S).card) := by
          rw [Finset.prod_const, Finset.card_univ, hJ]
  have hdiag : ∀ b ∈ W, F b b ≠ 0 := by
    intro b hb
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_sub]
    rcases k with i | s | s | δ
    · simp only [f, g]
      split_ifs with h
      · have := hBig_pos b _ (hlam_mem b i h)
        intro h0; nlinarith
      · norm_num
    · simp only [f, g, neg_zero, zero_sub, neg_ne_zero]
      have : b ≠ (s : ℝ^d) := fun e => hWS b hb (e ▸ s.2)
      have := norm_pos_iff.2 (sub_ne_zero.2 this)
      positivity
    · simp only [f, g, sub_zero, neg_ne_zero]
      have : b ≠ (s : ℝ^d) := fun e => hWS b hb (e ▸ s.2)
      have := dist_pos.2 this; positivity
    · simp only [f, g, sub_zero, neg_ne_zero]
      have := pos_of_mem_dists δ.2; positivity
  have hsurv : ∀ b ∈ W, #(W.filter fun x => x ≠ b ∧ F b x ≠ 0) ≤ Δ := by
    intro b hb
    set Sv := W.filter fun x => x ≠ b ∧ F b x ≠ 0
    set Cls := (S ×ˢ S).biUnion fun q => W.filter fun x => dist x q.1 = dist b q.2
    set W' := (W.erase b).filter fun x =>
      Rainbow (insert x (insert b S)) ∧ dist x b ∉ Big S W b τ
    have hsub : Sv ⊆ Cls ∪ W' := by
      intro x hx
      obtain ⟨hxW, hxb, hF⟩ := mem_filter.1 hx
      have hfac : ∀ k : J, ‖b - x‖ ^ 2 - f k b - g k x ≠ 0 := fun k =>
        Finset.prod_ne_zero_iff.1 hF k (Finset.mem_univ _)
      have hbx : ‖b - x‖ = dist x b := by rw [← dist_eq_norm, dist_comm]
      by_cases hcl : x ∈ Cls
      · exact mem_union_left _ hcl
      refine mem_union_right _ (mem_filter.2 ⟨mem_erase.2 ⟨hxb, hxW⟩, ?_, ?_⟩)
      · refine rainbow_insert_insert S b x (hc.ext b hb) (hc.ext x hxW) ?_ ?_ ?_ ?_
        · intro s hs s' hs' h
          exact hcl (mem_biUnion.2 ⟨(s, s'), mem_product.2 ⟨hs, hs'⟩, mem_filter.2 ⟨hxW, h⟩⟩)
        · intro s hs h
          have := hfac (Sum.inr (Sum.inr (Sum.inl ⟨s, hs⟩)))
          simp only [f, g, sub_zero] at this
          rw [hbx] at this
          exact ne_of_sq_sub_ne this h
        · intro s hs h
          have := hfac (Sum.inr (Sum.inl ⟨s, hs⟩))
          simp only [f, g, sub_zero] at this
          rw [hbx, ← dist_eq_norm] at this
          exact ne_of_sq_sub_ne this h
        · intro s hs s' hs' hne h
          have := hfac (Sum.inr (Sum.inr (Sum.inr ⟨dist s s', mem_dists hs hs' hne⟩)))
          simp only [f, g, sub_zero] at this
          rw [hbx] at this
          exact ne_of_sq_sub_ne this h
      · intro hl
        obtain ⟨i, hi, hli⟩ := hlam_surj b hb _ hl
        have := hfac (Sum.inl i)
        simp only [f, g, sub_zero, if_pos hi] at this
        rw [hbx, hli] at this
        exact this (by ring)
    have hCls : (#Cls : ℝ) ≤ r ^ 2 * σ := by
      have h1 : #Cls ≤ ∑ q ∈ S ×ˢ S, #(W.filter fun x => dist x q.1 = dist b q.2) :=
        card_biUnion_le
      have h2 : ∀ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) ≤ σ := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := mem_product.1 hq
        have hpos : 0 < dist b q.2 := dist_pos.2 fun e => hWS b hb (e ▸ hq2)
        exact (hc.cap q.1 hq1 _ hpos).le
      calc (#Cls : ℝ) ≤ ∑ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) := by
            exact_mod_cast h1
        _ ≤ ∑ _q ∈ S ×ˢ S, σ := sum_le_sum h2
        _ = r ^ 2 * σ := by rw [sum_const, card_product, hc.card, nsmul_eq_mul]; push_cast; ring
    have hconf' : Config X (insert b S) W' (r + 1) τ := by
      refine ⟨insert_subset (hWX b hb) hc.subX, hc.ext b hb, ?_, ?_, ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem (hWS b hb), hc.card]
      · exact (filter_subset _ _).trans ((erase_subset _ _).trans hc.subW)
      · rw [disjoint_left]
        intro x hx hxi
        obtain ⟨hxe, -⟩ := mem_filter.1 hx
        rcases mem_insert.1 hxi with rfl | hxS
        · exact (mem_erase.1 hxe).1 rfl
        · exact hWS x (mem_erase.1 hxe).2 hxS
      · intro x hx; exact (mem_filter.1 hx).2.1
      · intro s hs t ht
        have hsubW : W' ⊆ W := (filter_subset _ _).trans (erase_subset _ _)
        rcases mem_insert.1 hs with rfl | hsS
        ·
          by_cases hne : (W'.filter fun x => dist x s = t).Nonempty
          · obtain ⟨x0, hx0⟩ := hne
            obtain ⟨hx0W', hx0t⟩ := mem_filter.1 hx0
            obtain ⟨hx0e, hrb, hnb⟩ := mem_filter.1 hx0W'
            have hx0W := (mem_erase.1 hx0e).2
            have hx0b := (mem_erase.1 hx0e).1
            have himg : t ∈ (W.erase s).image fun x => dist x s :=
              mem_image.2 ⟨x0, hx0e, hx0t⟩
            have hnotR : t ∉ Rb S s := by
              intro hR
              rcases mem_union.1 hR with hR | hR
              · obtain ⟨q, hq, hqt⟩ := mem_image.1 hR
                obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
                have := hrb x0 (mem_insert_self _ _) s (mem_insert_of_mem (mem_insert_self _ _))
                  q.1 (mem_insert_of_mem (mem_insert_of_mem hq1)) q.2
                  (mem_insert_of_mem (mem_insert_of_mem hq2)) hx0b hq12 (by rw [hx0t, hqt])
                rcases this with ⟨h1, -⟩ | ⟨h1, -⟩
                · exact hWS x0 hx0W (h1 ▸ hq1)
                · exact hWS x0 hx0W (h1 ▸ hq2)
              · obtain ⟨q, hq, hqt⟩ := mem_image.1 hR
                have hsq : s ≠ q := fun e => hWS s hb (e ▸ hq)
                have := hrb x0 (mem_insert_self _ _) s (mem_insert_of_mem (mem_insert_self _ _))
                  s (mem_insert_of_mem (mem_insert_self _ _)) q
                  (mem_insert_of_mem (mem_insert_of_mem hq)) hx0b hsq (by rw [hx0t, hqt])
                rcases this with ⟨h1, -⟩ | ⟨h1, h2⟩
                · exact hx0b h1
                · exact hWS x0 hx0W (h1 ▸ hq)
            have hlt : ((W.filter fun x => dist x s = t).card : ℝ) < τ := by
              by_contra hge
              push Not at hge
              exact hnb (by rw [hx0t]; exact mem_filter.2 ⟨himg, hnotR, hge⟩)
            calc ((W'.filter fun x => dist x s = t).card : ℝ)
                ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
                  exact_mod_cast card_le_card (filter_subset_filter _ hsubW)
              _ < τ := hlt
          · rw [not_nonempty_iff_eq_empty] at hne
            rw [hne, card_empty, Nat.cast_zero]; linarith
        · calc ((W'.filter fun x => dist x s = t).card : ℝ)
              ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
                exact_mod_cast card_le_card (filter_subset_filter _ hsubW)
            _ < σ := hc.cap s hsS t ht
            _ ≤ τ := hτ
    have hW' : (#W' : ℝ) ≤ Γ * τ := hclaim _ _ τ hconf' (hσ.trans hτ)
    have : (#Sv : ℝ) ≤ Γ * τ + r ^ 2 * σ := by
      have h1 : #Sv ≤ #Cls + #W' := (card_le_card hsub).trans (card_union_le _ _)
      have : (#Sv : ℝ) ≤ #Cls + #W' := by exact_mod_cast h1
      linarith
    exact Nat.le_floor this
  have hkill := kill_bound W F _ Δ hrank hdiag hsurv
  have hτpos : 0 < τ := lt_of_lt_of_le hσpos hτ
  have hΔle : (Δ : ℝ) ≤ Γ * τ + r ^ 2 * σ := Nat.floor_le (by positivity)
  have : (W.card : ℝ) ≤ (((D + 2) ^ (K + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := by
    exact_mod_cast hkill
  calc (W.card : ℝ) ≤ (((D + 2) ^ (K + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := this
    _ ≤ _ := by gcongr
end E1088
end
section
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem affDim_add_le_of_ortho [DecidableEq (ℝ^d)] (R C : Finset (ℝ^d))
    (h : ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0) :
    affDim R + affDim C ≤ affDim (R ∪ C) := by
  unfold affDim
  set U := vectorSpan ℝ (R : Set (ℝ^d))
  set W := vectorSpan ℝ (C : Set (ℝ^d))
  have hUW : U ⟂ W := by
    simp only [U, W, vectorSpan_def]
    rw [Submodule.isOrtho_span]
    rintro u ⟨x, hx, x', hx', rfl⟩ v ⟨w, hw, w', hw', rfl⟩
    exact h x hx x' hx' w hw w' hw'
  have hdisj : U ⊓ W = ⊥ := hUW.disjoint.eq_bot
  have hsup : U ⊔ W ≤ vectorSpan ℝ ((R ∪ C : Finset (ℝ^d)) : Set (ℝ^d)) := by
    apply sup_le
    · exact vectorSpan_mono ℝ (by simp)
    · exact vectorSpan_mono ℝ (by simp)
  have := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hdisj, finrank_bot, add_zero] at this
  rw [← this]
  exact Submodule.finrank_mono hsup
theorem min_affDim_le_of_ortho [DecidableEq (ℝ^d)] (R C : Finset (ℝ^d)) (D : ℕ)
    (hD : affDim (R ∪ C) ≤ D)
    (h : ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0) :
    min (affDim R) (affDim C) ≤ D / 2 := by
  have := affDim_add_le_of_ortho R C h
  omega
theorem ortho_of_equidistant (R C : Finset (ℝ^d)) (ρ : ℝ^d → ℝ)
    (h : ∀ x ∈ R, ∀ w ∈ C, ‖x - w‖ = ρ w) :
    ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0 := by
  intro x hx x' hx' w hw w' hw'
  have e1 : ‖x - w‖ ^ 2 = ‖x' - w‖ ^ 2 := by rw [h x hx w hw, h x' hx' w hw]
  have e2 : ‖x - w'‖ ^ 2 = ‖x' - w'‖ ^ 2 := by rw [h x hx w' hw', h x' hx' w' hw']
  rw [norm_sub_sq_real, norm_sub_sq_real] at e1 e2
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith
theorem ortho_of_bisector (R C : Finset (ℝ^d)) (p : ℝ^d)
    (h : ∀ x ∈ R, ∀ w ∈ C, ‖x - p‖ = ‖x - w‖) :
    ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0 := by
  intro x hx x' hx' w hw w' hw'
  have e : ∀ z ∈ R, ∀ v ∈ C, 2 * inner ℝ z (v - p) = ‖v‖ ^ 2 - ‖p‖ ^ 2 := by
    intro z hz v hv
    have := congrArg (· ^ 2) (h z hz v hv)
    rw [norm_sub_sq_real, norm_sub_sq_real] at this
    rw [inner_sub_right]; linarith
  have a1 := e x hx w hw
  have a2 := e x' hx' w hw
  have a3 := e x hx w' hw'
  have a4 := e x' hx' w' hw'
  rw [inner_sub_right] at a1 a2 a3 a4
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith
end E1088
end
section
open Finset
namespace E1088
variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
theorem round_core (M N : α → β → ℝ) (τ : ι → TF α β) (A : Finset ι) (X : Finset α)
    (Y : Finset β) (r R' : ℕ) (K : ℝ) (hr : rankOn M X Y ≤ r) (hN : rankOn N X Y ≤ r + 2)
    (hR' : (r + 1) ^ #A ≤ R') (hR1 : 1 ≤ R')
    (hbd : ∀ x ∈ X, ∀ w ∈ Y, 1 / 2 ≤ |N x w| ∧ |N x w| ≤ K)
    (hposA : ∀ x ∈ X, ∀ w ∈ Y, 0 < N x w → ∃ t ∈ A, M x w = (τ t).eval x w)
    (hnegA : ∀ x ∈ X, ∀ w ∈ Y, N x w < 0 → ∀ t ∈ A, M x w ≠ (τ t).eval x w)
    (hmaj : #X * #Y ≤ 2 * #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2)) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y,
      (#X : ℝ) ≤ 64 * R' * 4 ^ roundsT K (1 / (16 * R')) (r + 2) * #X' ∧
      (#Y : ℝ) ≤ 64 * R' * 4 ^ roundsT K (1 / (16 * R')) (r + 2) * #Y' ∧
      Covers M τ A X' Y' := by
  classical
  set δ : ℝ := 1 / (16 * R') with hδ
  have hR'pos : (0 : ℝ) < R' := by exact_mod_cast hR1
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ R' := by exact_mod_cast hR1
    linarith
  have hpos : δ * (#X * #Y) ≤ #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2) := by
    have h1 : ((#X * #Y : ℕ) : ℝ) ≤ 2 * #((X ×ˢ Y).filter fun p => 0 < N p.1 p.2) := by
      exact_mod_cast hmaj
    have h2 : (0 : ℝ) ≤ #X * #Y := by positivity
    push_cast at h1
    nlinarith
  obtain ⟨X1, hX1, Y1, hY1, c1, c2, hneg⟩ := lemmaR N X Y (r + 2) K δ hN hbd hδ0 hδ1 hpos
  set T := roundsT K δ (r + 2)
  set H : α → β → ℝ := fun x w => ∏ t ∈ A, (M x w - (τ t).eval x w) with hH
  have hHrank : rankOn H X1 Y1 ≤ R' :=
    (rankOn_prod_sub M τ A X1 Y1 r ((rankOn_mono M hX1 hY1).trans hr)).trans hR'
  have hsupp : supp H X1 Y1 ⊆ (X1 ×ˢ Y1).filter fun p => N p.1 p.2 < 0 := by
    intro p hp
    obtain ⟨hpXY, hHp⟩ := mem_filter.1 hp
    obtain ⟨hpx, hpy⟩ := mem_product.1 hpXY
    refine mem_filter.2 ⟨hpXY, ?_⟩
    have hb := hbd p.1 (hX1 hpx) p.2 (hY1 hpy)
    rcases lt_trichotomy (N p.1 p.2) 0 with h | h | h
    · exact h
    · rw [h] at hb; norm_num at hb
    · obtain ⟨t, ht, hM⟩ := hposA p.1 (hX1 hpx) p.2 (hY1 hpy) h
      exact absurd (prod_eq_zero ht (by rw [hM]; ring)) hHp
  have hsuppc : 16 * R' * #(supp H X1 Y1) ≤ #X1 * #Y1 := by
    have h1 : (#(supp H X1 Y1) : ℝ) ≤ δ * (#X1 * #Y1) :=
      (by exact_mod_cast card_le_card hsupp : (#(supp H X1 Y1) : ℝ) ≤ _).trans hneg
    have h2 : ((16 * R' * #(supp H X1 Y1) : ℕ) : ℝ) ≤ ((#X1 * #Y1 : ℕ) : ℝ) := by
      push_cast
      rw [hδ] at h1
      have : (16 * R' : ℝ) * (1 / (16 * R') * (#X1 * #Y1)) = #X1 * #Y1 := by
        field_simp
      nlinarith
    exact_mod_cast h2
  obtain ⟨X2, hX2, Y2, hY2, d1, d2, hzero⟩ := cleaning H X1 Y1 R' hR1 hHrank hsuppc
  refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, ?_, ?_, ?_⟩
  · have e1 : (#X1 : ℝ) ≤ 2 * #X2 := by exact_mod_cast d1
    have e2 : (16 * R' : ℝ) * δ = 1 := by rw [hδ]; field_simp
    have h4 : (0 : ℝ) ≤ 4 ^ T := by positivity
    calc (#X : ℝ) = 16 * R' * 2 * (δ / 2 * #X) := by
          rw [show (16 * R' * 2 : ℝ) * (δ / 2 * #X) = (16 * R' * δ) * #X by ring, e2, one_mul]
      _ ≤ 16 * R' * 2 * (4 ^ T * #X1) := by gcongr
      _ ≤ 16 * R' * 2 * (4 ^ T * (2 * #X2)) := by gcongr
      _ ≤ 64 * R' * 4 ^ T * #X2 := by nlinarith
  · have e1 : (#Y1 : ℝ) ≤ 2 * #Y2 := by exact_mod_cast d2
    have e2 : (16 * R' : ℝ) * δ = 1 := by rw [hδ]; field_simp
    have h4 : (0 : ℝ) ≤ 4 ^ T := by positivity
    calc (#Y : ℝ) = 16 * R' * 2 * (δ / 2 * #Y) := by
          rw [show (16 * R' * 2 : ℝ) * (δ / 2 * #Y) = (16 * R' * δ) * #Y by ring, e2, one_mul]
      _ ≤ 16 * R' * 2 * (4 ^ T * #Y1) := by gcongr
      _ ≤ 16 * R' * 2 * (4 ^ T * (2 * #Y2)) := by gcongr
      _ ≤ 64 * R' * 4 ^ T * #Y2 := by nlinarith
  · intro x hx w hw
    have := hzero x hx w hw
    obtain ⟨t, ht, h0⟩ := prod_eq_zero_iff.1 this
    exact ⟨t, ht, by linarith⟩
end E1088
end
section
open Finset
namespace E1088
variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
theorem CutData.mono_K {τ : ι → TF α β} {S : Finset ι} {K K' : ℝ} {X : Finset α}
    {Y : Finset β} (hK : K ≤ K') (h : CutData τ S K X Y) : CutData τ S K' X Y := by
  obtain ⟨Lo, Hi, h1, h2, h3, h4, φ, θ, qr, qc, hqr, hqc, hb⟩ := h
  refine ⟨Lo, Hi, h1, h2, h3, h4, φ, θ, qr, qc, hqr, hqc, fun x hx w hw => ?_⟩
  have hσ := mul_pos (hqr x hx) (hqc w hw)
  obtain ⟨hL, hH⟩ := hb x hx w hw
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨a, b⟩ := hL t ht; exact ⟨by nlinarith, b⟩
  · obtain ⟨a, b⟩ := hH t ht; exact ⟨a, by nlinarith⟩
noncomputable def margK (k : ℕ) : ℝ := 32 * k * 16 ^ k
noncomputable def roundCost (k r : ℕ) : ℝ :=
  16 ^ (k * k) * 4 ^ k *
    (64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2))
theorem one_le_roundCost (k r : ℕ) : 1 ≤ roundCost k r := by
  unfold roundCost
  have h1 : (1 : ℝ) ≤ 16 ^ (k * k) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ ((r + 1) ^ k : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have h4 : (1 : ℝ) ≤ 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) :=
    one_le_pow₀ (by norm_num)
  have h5 : (1 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k)
      (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) := by nlinarith
  nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
theorem lr_round (M : α → β → ℝ) (τ : ι → TF α β) (S : Finset ι) (X : Finset α) (Y : Finset β)
    (k r : ℕ) (hX : X.Nonempty) (hY : Y.Nonempty) (hr : rankOn M X Y ≤ r)
    (hcov : Covers M τ S X Y) (hS : 2 ≤ #S) (hSk : #S ≤ k) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, (#X : ℝ) ≤ roundCost k r * #X' ∧ (#Y : ℝ) ≤ roundCost k r * #Y' ∧
      ∃ S' ⊆ S, #S' < #S ∧ Covers M τ S' X' Y' := by
  classical
  obtain ⟨X1, hX1, Y1, hY1, c1, c2, S1, hS1, hcov1, hgood⟩ :=
    process_pairs M τ (S ×ˢ S) S X Y hX hY hcov
  rw [card_product] at c1 c2
  have hX1ne := nonempty_of_card_le hX c1
  have hY1ne := nonempty_of_card_le hY c2
  have hkk : (16 : ℝ) ^ (#S * #S) ≤ 16 ^ (k * k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul hSk hSk)
  have c1r : (#X : ℝ) ≤ 16 ^ (k * k) * #X1 := by
    have : (#X : ℝ) ≤ 16 ^ (#S * #S) * #X1 := by exact_mod_cast c1
    nlinarith [(Nat.cast_nonneg #X1 : (0 : ℝ) ≤ #X1)]
  have c2r : (#Y : ℝ) ≤ 16 ^ (k * k) * #Y1 := by
    have : (#Y : ℝ) ≤ 16 ^ (#S * #S) * #Y1 := by exact_mod_cast c2
    nlinarith [(Nat.cast_nonneg #Y1 : (0 : ℝ) ≤ #Y1)]
  have hRC := one_le_roundCost k r
  by_cases hS1c : #S1 ≤ 1
  · refine ⟨X1, hX1, Y1, hY1, ?_, ?_, S1, hS1, by omega, hcov1⟩
    · have : (16 : ℝ) ^ (k * k) ≤ roundCost k r := by
        unfold roundCost
        have h2 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ ((r + 1) ^ k : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
        have h4 : (1 : ℝ) ≤ 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) :=
          one_le_pow₀ (by norm_num)
        have h0 : (0 : ℝ) ≤ 16 ^ (k * k) := by positivity
        have h5 : (1 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k)
          (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2 h0]
      nlinarith [(Nat.cast_nonneg #X1 : (0 : ℝ) ≤ #X1)]
    · have : (16 : ℝ) ^ (k * k) ≤ roundCost k r := by
        unfold roundCost
        have h2 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ ((r + 1) ^ k : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
        have h4 : (1 : ℝ) ≤ 4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) :=
          one_le_pow₀ (by norm_num)
        have h0 : (0 : ℝ) ≤ 16 ^ (k * k) := by positivity
        have h5 : (1 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) * 4 ^ roundsT (margK k)
          (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2 h0]
      nlinarith [(Nat.cast_nonneg #Y1 : (0 : ℝ) ≤ #Y1)]
  push Not at hS1c
  have hS1k : #S1 ≤ k := (card_le_card hS1).trans hSk
  obtain ⟨X2, hX2, Y2, hY2, d1, d2, hcut⟩ := cut_of_good τ S1 X1 Y1 hX1ne hY1ne hS1c
    (fun t ht t' ht' hne => hgood (t, t') (mem_product.2 ⟨hS1 ht, hS1 ht'⟩) ht ht' hne)
  have hKle : (32 * #S1 * 16 ^ #S1 : ℝ) ≤ margK k := by
    unfold margK
    have a1 : (#S1 : ℝ) ≤ k := by exact_mod_cast hS1k
    have a2 : (16 : ℝ) ^ #S1 ≤ 16 ^ k := pow_le_pow_right₀ (by norm_num) hS1k
    have := mul_le_mul a1 a2 (by positivity) (by positivity)
    nlinarith
  obtain ⟨Lo, Hi, hLH, hdisj, hLo, hHi, φ, θ, qr, qc, hqr, hqc, hb⟩ := hcut.mono_K hKle
  have hX2ne := nonempty_of_card_le hX1ne d1
  have hY2ne := nonempty_of_card_le hY1ne d2
  set N : α → β → ℝ := fun x w => (M x w - (φ x + θ w)) / (qr x * qc w) with hNdef
  have hNrank : rankOn N X2 Y2 ≤ r + 2 :=
    (rankOn_rescale M φ θ qr qc X2 Y2).trans
      (by have := (rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr; omega)
  have hcov2 := hcov1.mono hX2 hY2
  have hentry : ∀ x ∈ X2, ∀ w ∈ Y2, ∀ t ∈ S1, M x w = (τ t).eval x w →
      (t ∈ Lo → -margK k ≤ N x w ∧ N x w ≤ -1 / 2) ∧
      (t ∈ Hi → 1 / 2 ≤ N x w ∧ N x w ≤ margK k) := by
    intro x hx w hw t ht hM
    have hσ := mul_pos (hqr x hx) (hqc w hw)
    obtain ⟨hL, hH⟩ := hb x hx w hw
    constructor
    · intro htL
      obtain ⟨a, b⟩ := hL t htL
      rw [← hM] at a b
      simp only [hNdef]
      constructor
      · rw [le_div_iff₀ hσ]; linarith
      · rw [div_le_iff₀ hσ]; linarith
    · intro htH
      obtain ⟨a, b⟩ := hH t htH
      rw [← hM] at a b
      simp only [hNdef]
      constructor
      · rw [le_div_iff₀ hσ]; linarith
      · rw [div_le_iff₀ hσ]; linarith
  have hmem : ∀ t ∈ S1, t ∈ Lo ∨ t ∈ Hi := fun t ht => by
    rw [← hLH] at ht; exact mem_union.1 ht
  have hbd : ∀ x ∈ X2, ∀ w ∈ Y2, 1 / 2 ≤ |N x w| ∧ |N x w| ≤ margK k := by
    intro x hx w hw
    obtain ⟨t, ht, hM⟩ := hcov2 x hx w hw
    have he := hentry x hx w hw t ht hM
    rcases hmem t ht with h | h
    · obtain ⟨a, b⟩ := he.1 h
      rw [abs_of_neg (by linarith)]; constructor <;> linarith
    · obtain ⟨a, b⟩ := he.2 h
      rw [abs_of_pos (by linarith)]; constructor <;> linarith
  have hcardLH : #Lo + #Hi = #S1 := by rw [← card_union_of_disjoint hdisj, hLH]
  have hLoc := card_pos.2 hLo
  have hHic := card_pos.2 hHi
  have hR1 : 1 ≤ (r + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have hsplit : #((X2 ×ˢ Y2).filter fun p => 0 < N p.1 p.2) +
      #((X2 ×ˢ Y2).filter fun p => 0 < (-N p.1 p.2)) = #X2 * #Y2 := by
    rw [← card_product]
    have : (X2 ×ˢ Y2).filter (fun p => 0 < (-N p.1 p.2)) =
        (X2 ×ˢ Y2).filter (fun p => ¬ 0 < N p.1 p.2) := by
      refine filter_congr fun p hp => ?_
      obtain ⟨hx, hw⟩ := mem_product.1 hp
      have := hbd p.1 hx p.2 hw
      constructor
      · intro h; linarith
      · intro h
        rcases lt_or_eq_of_le (not_lt.1 h) with h' | h'
        · linarith
        · rw [h'] at this; norm_num at this
    rw [this]; exact card_filter_add_card_filter_not _
  have finish : ∀ X3 ⊆ X2, ∀ Y3 ⊆ Y2,
      (#X2 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) *
        4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #X3 →
      (#Y2 : ℝ) ≤ 64 * ((r + 1) ^ k : ℕ) *
        4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #Y3 →
      (#X : ℝ) ≤ roundCost k r * #X3 ∧ (#Y : ℝ) ≤ roundCost k r * #Y3 := by
    intro X3 _ Y3 _ e1 e2
    have f1 : (#X1 : ℝ) ≤ 4 ^ k * #X2 := by
      have : (#X1 : ℝ) ≤ 4 ^ #S1 * #X2 := by exact_mod_cast d1
      have a : (4 : ℝ) ^ #S1 ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hS1k
      nlinarith [(Nat.cast_nonneg #X2 : (0 : ℝ) ≤ #X2)]
    have f2 : (#Y1 : ℝ) ≤ 4 ^ k * #Y2 := by
      have : (#Y1 : ℝ) ≤ 4 ^ #S1 * #Y2 := by exact_mod_cast d2
      have a : (4 : ℝ) ^ #S1 ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hS1k
      nlinarith [(Nat.cast_nonneg #Y2 : (0 : ℝ) ≤ #Y2)]
    have p1 : (0 : ℝ) ≤ 16 ^ (k * k) := by positivity
    have p2 : (0 : ℝ) ≤ 4 ^ k := by positivity
    constructor
    · calc (#X : ℝ) ≤ 16 ^ (k * k) * #X1 := c1r
        _ ≤ 16 ^ (k * k) * (4 ^ k * #X2) := mul_le_mul_of_nonneg_left f1 p1
        _ ≤ 16 ^ (k * k) * (4 ^ k * (64 * ((r + 1) ^ k : ℕ) *
              4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #X3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 p2) p1
        _ = roundCost k r * #X3 := by unfold roundCost; ring
    · calc (#Y : ℝ) ≤ 16 ^ (k * k) * #Y1 := c2r
        _ ≤ 16 ^ (k * k) * (4 ^ k * #Y2) := mul_le_mul_of_nonneg_left f2 p1
        _ ≤ 16 ^ (k * k) * (4 ^ k * (64 * ((r + 1) ^ k : ℕ) *
              4 ^ roundsT (margK k) (1 / (16 * ((r + 1) ^ k : ℕ))) (r + 2) * #Y3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 p2) p1
        _ = roundCost k r * #Y3 := by unfold roundCost; ring
  by_cases hmaj : #X2 * #Y2 ≤ 2 * #((X2 ×ˢ Y2).filter fun p => 0 < N p.1 p.2)
  ·
    have hHk : (r + 1) ^ #Hi ≤ (r + 1) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨X3, hX3, Y3, hY3, e1, e2, hcov3⟩ := round_core M N τ Hi X2 Y2 r ((r + 1) ^ k)
      (margK k) ((rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr) hNrank hHk hR1 hbd
      (fun x hx w hw hN => by
        obtain ⟨t, ht, hM⟩ := hcov2 x hx w hw
        refine ⟨t, ?_, hM⟩
        rcases hmem t ht with h | h
        · have := ((hentry x hx w hw t ht hM).1 h).2; linarith
        · exact h)
      (fun x hx w hw hN t ht hM => by
        have := ((hentry x hx w hw t (hLH ▸ mem_union_right _ ht) hM).2 ht).1; linarith)
      hmaj
    obtain ⟨f1, f2⟩ := finish X3 hX3 Y3 hY3 e1 e2
    refine ⟨X3, hX3.trans (hX2.trans hX1), Y3, hY3.trans (hY2.trans hY1), f1, f2, Hi,
      (hLH ▸ subset_union_right).trans hS1, by have := card_le_card hS1; omega, hcov3⟩
  ·
    have hLk : (r + 1) ^ #Lo ≤ (r + 1) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have hNrank' : rankOn (fun x w => -N x w) X2 Y2 ≤ r + 2 := by
      have : (fun x w => -N x w) = fun x w =>
          (M x w - (φ x + θ w)) / ((-qr x) * qc w) := by
        funext x w; simp only [hNdef]; rw [neg_mul, div_neg]
      rw [this]
      exact (rankOn_rescale M φ θ (fun x => -qr x) qc X2 Y2).trans
        (by have := (rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr; omega)
    obtain ⟨X3, hX3, Y3, hY3, e1, e2, hcov3⟩ := round_core M (fun x w => -N x w) τ Lo X2 Y2 r
      ((r + 1) ^ k) (margK k) ((rankOn_mono M (hX2.trans hX1) (hY2.trans hY1)).trans hr)
      hNrank' hLk hR1 (fun x hx w hw => by rw [abs_neg]; exact hbd x hx w hw)
      (fun x hx w hw hN => by
        obtain ⟨t, ht, hM⟩ := hcov2 x hx w hw
        refine ⟨t, ?_, hM⟩
        rcases hmem t ht with h | h
        · exact h
        · have := ((hentry x hx w hw t ht hM).2 h).1; linarith)
      (fun x hx w hw hN t ht hM => by
        have := ((hentry x hx w hw t (hLH ▸ mem_union_left _ ht) hM).1 ht).2
        linarith)
      (by have h' := hsplit; push Not at hmaj; linarith)
    obtain ⟨f1, f2⟩ := finish X3 hX3 Y3 hY3 e1 e2
    refine ⟨X3, hX3.trans (hX2.trans hX1), Y3, hY3.trans (hY2.trans hY1), f1, f2, Lo,
      (hLH ▸ subset_union_left).trans hS1, by have := card_le_card hS1; omega, hcov3⟩
noncomputable def LRcost : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, r => roundCost (k + 1) r * LRcost k r
theorem one_le_LRcost (k r : ℕ) : 1 ≤ LRcost k r := by
  induction k with
  | zero => simp [LRcost]
  | succ k ih =>
    simp only [LRcost]
    have := one_le_roundCost (k + 1) r
    nlinarith
theorem theoremLR (M : α → β → ℝ) (τ : ι → TF α β) (r : ℕ) :
    ∀ (k : ℕ) (S : Finset ι) (X : Finset α) (Y : Finset β), #S ≤ k → X.Nonempty →
      Y.Nonempty → rankOn M X Y ≤ r → Covers M τ S X Y →
      ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ t ∈ S, (#X : ℝ) ≤ LRcost k r * #X' ∧
        (#Y : ℝ) ≤ LRcost k r * #Y' ∧ ∀ x ∈ X', ∀ w ∈ Y', M x w = (τ t).eval x w := by
  intro k
  induction k with
  | zero =>
    intro S X Y hS hX hY _ hcov
    obtain ⟨x, hx⟩ := hX; obtain ⟨w, hw⟩ := hY
    obtain ⟨t, ht, _⟩ := hcov x hx w hw
    have := card_pos.2 ⟨t, ht⟩; omega
  | succ k ih =>
    intro S X Y hS hX hY hr hcov
    by_cases h1 : #S ≤ 1
    · obtain ⟨x, hx⟩ := hX; obtain ⟨w, hw⟩ := hY
      obtain ⟨t, ht, _⟩ := hcov x hx w hw
      have hst : S = {t} := by
        rw [eq_singleton_iff_unique_mem]
        exact ⟨ht, fun u hu => card_le_one.1 h1 u hu t ht⟩
      have hL := one_le_LRcost (k + 1) r
      refine ⟨X, subset_refl _, Y, subset_refl _, t, ht, ?_, ?_, fun x' hx' w' hw' => ?_⟩
      · nlinarith [(Nat.cast_nonneg #X : (0 : ℝ) ≤ #X)]
      · nlinarith [(Nat.cast_nonneg #Y : (0 : ℝ) ≤ #Y)]
      · obtain ⟨u, hu, hM⟩ := hcov x' hx' w' hw'
        rw [hst, mem_singleton] at hu; rw [hM, hu]
    · push Not at h1
      obtain ⟨X1, hX1, Y1, hY1, c1, c2, S1, hS1, hlt, hcov1⟩ :=
        lr_round M τ S X Y (k + 1) r hX hY hr hcov h1 hS
      have hX1ne : X1.Nonempty := by
        rw [← card_pos]; by_contra h
        have h0 : #X1 = 0 := by omega
        have e : (#X : ℝ) ≤ 0 := by simpa [h0] using c1
        have e' : (0 : ℝ) < #X := by exact_mod_cast card_pos.2 hX
        linarith
      have hY1ne : Y1.Nonempty := by
        rw [← card_pos]; by_contra h
        have h0 : #Y1 = 0 := by omega
        have e : (#Y : ℝ) ≤ 0 := by simpa [h0] using c2
        have e' : (0 : ℝ) < #Y := by exact_mod_cast card_pos.2 hY
        linarith
      obtain ⟨X2, hX2, Y2, hY2, t, ht, d1, d2, hM⟩ := ih S1 X1 Y1 (by omega) hX1ne hY1ne
        ((rankOn_mono M hX1 hY1).trans hr) hcov1
      have hRC := one_le_roundCost (k + 1) r
      refine ⟨X2, hX2.trans hX1, Y2, hY2.trans hY1, t, hS1 ht, ?_, ?_, hM⟩
      · simp only [LRcost]
        calc (#X : ℝ) ≤ roundCost (k + 1) r * #X1 := c1
          _ ≤ roundCost (k + 1) r * (LRcost k r * #X2) := by gcongr
          _ = _ := by ring
      · simp only [LRcost]
        calc (#Y : ℝ) ≤ roundCost (k + 1) r * #Y1 := c2
          _ ≤ roundCost (k + 1) r * (LRcost k r * #Y2) := by gcongr
          _ = _ := by ring
end E1088
end
section
open Finset Real
namespace E1088
noncomputable def Lr (r : ℕ) : ℝ := Real.sqrt (r + 2) * Real.logb 2 (r + 2)
theorem one_le_logb (r : ℕ) : 1 ≤ Real.logb 2 ((r : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
  have := Nat.cast_nonneg (α := ℝ) r; linarith
theorem one_le_sqrt (r : ℕ) : 1 ≤ Real.sqrt ((r : ℝ) + 2) := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_le_sqrt; have := Nat.cast_nonneg (α := ℝ) r; linarith
theorem one_le_Lr (r : ℕ) : 1 ≤ Lr r := by
  unfold Lr; have := one_le_logb r; have := one_le_sqrt r; nlinarith
theorem logb_le_Lr (r : ℕ) : Real.logb 2 ((r : ℝ) + 2) ≤ Lr r := by
  unfold Lr; have := one_le_logb r; have := one_le_sqrt r; nlinarith
theorem two_rpow_le {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ 2 ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h
theorem roundCost_le (k r : ℕ) :
    roundCost k r ≤ (2 : ℝ) ^ ((4 * k * k + 3 * k + 8 + 2 * Real.pi * margK k * (9 + 2 * k)) *
      Lr r) := by
  have hL := one_le_Lr r
  have hlog := one_le_logb r
  have hsq := one_le_sqrt r
  set R' : ℕ := (r + 1) ^ k with hR'
  set δ : ℝ := 1 / (16 * (R' : ℝ)) with hδ
  set T := roundsT (margK k) δ (r + 2) with hT
  have hR'pos : (0 : ℝ) < R' := by exact_mod_cast pow_pos (Nat.succ_pos r) k
  have hmK : 0 ≤ margK k := by unfold margK; positivity
  have hA : (16 : ℝ) ^ (k * k) * 4 ^ k * 64 = 2 ^ ((4 * k * k + 2 * k + 6 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num,
      show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1; ring
  have hB : (R' : ℝ) ≤ 2 ^ (k * Real.logb 2 ((r : ℝ) + 2)) := by
    rw [hR']; push_cast
    rw [mul_comm (k : ℝ), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by positivity), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hlogδ : Real.log (2 / δ ^ 2) ≤ (9 + 2 * k) * Real.logb 2 ((r : ℝ) + 2) := by
    have e : 2 / δ ^ 2 = 512 * (R' : ℝ) ^ 2 := by rw [hδ]; field_simp; ring
    rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h512 : Real.log 512 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 512 by norm_num)
      have h2 : Real.log 512 = 9 * Real.log 2 := by
        rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    have hR'log : Real.log R' ≤ k * Real.logb 2 ((r : ℝ) + 2) := by
      have := Real.log_le_log hR'pos hB
      rw [Real.log_rpow (by norm_num)] at this
      have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      have h0 : 0 ≤ (k : ℝ) * Real.logb 2 ((r : ℝ) + 2) := by positivity
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
    push_cast
    nlinarith
  have hTle : (T : ℝ) ≤ Real.pi * margK k * (9 + 2 * k) * Lr r + 1 := by
    have h1 : (T : ℝ) < Real.pi * margK k * Real.sqrt ((r + 2 : ℕ) : ℝ) *
        Real.log (2 / δ ^ 2) + 1 := Nat.ceil_lt_add_one (by
          apply mul_nonneg (by positivity)
          apply Real.log_nonneg
          rw [hδ]; rw [show 2 / (1 / (16 * (R' : ℝ))) ^ 2 = 512 * (R' : ℝ) ^ 2 by field_simp; ring]
          have : (1 : ℝ) ≤ R' := by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos r)
          nlinarith)
    have h2 : Real.sqrt ((r + 2 : ℕ) : ℝ) = Real.sqrt ((r : ℝ) + 2) := by push_cast; rfl
    rw [h2] at h1
    have h3 : Real.pi * margK k * Real.sqrt ((r : ℝ) + 2) * Real.log (2 / δ ^ 2) ≤
        Real.pi * margK k * (9 + 2 * k) * Lr r := by
      unfold Lr
      have := mul_le_mul_of_nonneg_left hlogδ
        (show 0 ≤ Real.pi * margK k * Real.sqrt ((r : ℝ) + 2) by positivity)
      nlinarith
    linarith
  have hC : (4 : ℝ) ^ T ≤ 2 ^ ((2 * Real.pi * margK k * (9 + 2 * k) + 2) * Lr r) := by
    rw [show (4 : ℝ) ^ T = 2 ^ ((2 * T : ℕ) : ℝ) by
      rw [Real.rpow_natCast, pow_mul]; norm_num]
    apply two_rpow_le
    push_cast
    nlinarith
  unfold roundCost
  rw [← hR', ← hδ, ← hT]
  have e1 : (16 : ℝ) ^ (k * k) * 4 ^ k * (64 * (R' : ℝ) * 4 ^ T) =
      ((16 : ℝ) ^ (k * k) * 4 ^ k * 64) * (R' : ℝ) * 4 ^ T := by ring
  rw [e1, hA]
  have hA' : (2 : ℝ) ^ ((4 * k * k + 2 * k + 6 : ℕ) : ℝ) ≤
      2 ^ ((4 * k * k + 2 * k + 6 : ℝ) * Lr r) := by
    apply two_rpow_le; push_cast
    have : (0 : ℝ) ≤ 4 * k * k + 2 * k + 6 := by positivity
    nlinarith
  have hB' : (R' : ℝ) ≤ 2 ^ (k * Lr r) :=
    hB.trans (two_rpow_le (mul_le_mul_of_nonneg_left (logb_le_Lr r) (by positivity)))
  calc 2 ^ ((4 * k * k + 2 * k + 6 : ℕ) : ℝ) * (R' : ℝ) * 4 ^ T
      ≤ 2 ^ ((4 * k * k + 2 * k + 6 : ℝ) * Lr r) * 2 ^ (k * Lr r) *
          2 ^ ((2 * Real.pi * margK k * (9 + 2 * k) + 2) * Lr r) := by
        gcongr
    _ = 2 ^ ((4 * k * k + 2 * k + 6 : ℝ) * Lr r + k * Lr r +
          (2 * Real.pi * margK k * (9 + 2 * k) + 2) * Lr r) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
    _ = _ := by congr 1; ring
theorem LRcost_le (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, LRcost k r ≤ (2 : ℝ) ^ (C * Lr r) := by
  induction k with
  | zero => exact ⟨0, le_rfl, fun r => by simp [LRcost]⟩
  | succ k ih =>
    obtain ⟨C, hC, h⟩ := ih
    set c := (4 * (k + 1 : ℕ) * (k + 1 : ℕ) + 3 * (k + 1 : ℕ) + 8 +
      2 * Real.pi * margK (k + 1) * (9 + 2 * (k + 1 : ℕ)) : ℝ) with hc
    have hc0 : 0 ≤ c := by
      have : 0 ≤ margK (k + 1) := by unfold margK; positivity
      rw [hc]; positivity
    refine ⟨c + C, by linarith, fun r => ?_⟩
    simp only [LRcost]
    have h1 := roundCost_le (k + 1) r
    have h2 := h r
    have h0 : 0 ≤ LRcost k r := le_trans zero_le_one (one_le_LRcost k r)
    calc roundCost (k + 1) r * LRcost k r ≤ 2 ^ (c * Lr r) * 2 ^ (C * Lr r) :=
          mul_le_mul h1 h2 h0 (by positivity)
      _ = 2 ^ ((c + C) * Lr r) := by rw [← Real.rpow_add (by norm_num)]; ring_nf
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
noncomputable def symDist : Sym2 (ℝ^d) → ℝ := Sym2.lift ⟨dist, dist_comm⟩
theorem dists_eq_image (A : Finset (ℝ^d)) :
    dists A = (A.offDiag.image Sym2.mk.uncurry).image symDist := by
  rw [image_image]; rfl
theorem card_dists_le (A : Finset (ℝ^d)) : (dists A).card ≤ (A.card).choose 2 := by
  rw [dists_eq_image, ← Sym2.card_image_offDiag]; exact card_image_le
theorem pdd_iff_rainbow (A : Finset (ℝ^d)) :
    Erdos1088.PairwiseDistancesDistinct A ↔ Rainbow A := by
  unfold Erdos1088.PairwiseDistancesDistinct distinctDistances
  have hds : distanceSet A = dists A := rfl
  rw [hds, dists_eq_image, ← Sym2.card_image_offDiag, card_image_iff]
  constructor
  · intro hinj a ha a' ha' c hc c' hc' hne hne' hd
    have h1 : s(a, a') ∈ A.offDiag.image Sym2.mk.uncurry :=
      mem_image.2 ⟨(a, a'), mem_offDiag.2 ⟨ha, ha', hne⟩, rfl⟩
    have h2 : s(c, c') ∈ A.offDiag.image Sym2.mk.uncurry :=
      mem_image.2 ⟨(c, c'), mem_offDiag.2 ⟨hc, hc', hne'⟩, rfl⟩
    exact Sym2.eq_iff.1 (hinj h1 h2 hd)
  · intro hr z1 hz1 z2 hz2 heq
    obtain ⟨⟨a, a'⟩, hp, rfl⟩ := mem_image.1 hz1
    obtain ⟨⟨c, c'⟩, hq, rfl⟩ := mem_image.1 hz2
    obtain ⟨ha, ha', hne⟩ := mem_offDiag.1 hp
    obtain ⟨hc, hc', hne'⟩ := mem_offDiag.1 hq
    exact Sym2.eq_iff.2 (hr a ha a' ha' c hc c' hc' hne hne' heq)
theorem rainbowFree_iff (n : ℕ) (X : Finset (ℝ^d)) :
    RainbowFree n X ↔ ∀ A ⊆ X, A.card = n → ¬ Rainbow A := by
  unfold RainbowFree Erdos1088.HasSubsetWithDistinctDistances
  constructor
  · intro h A hA hAn hr; exact h ⟨A, hA, hAn, (pdd_iff_rainbow A).2 hr⟩
  · rintro h ⟨A, hA, hAn, hp⟩; exact h A hA hAn ((pdd_iff_rainbow A).1 hp)
theorem label_lemma (n : ℕ) (X T : Finset (ℝ^d)) (x w : ℝ^d) (hfree : RainbowFree n X)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hx : x ∈ X) (hw : w ∈ X)
    (hxT : x ∉ T) (hwT : w ∉ T) (hxr : Rainbow (insert x T)) (hwr : Rainbow (insert w T))
    (hdisj : ∀ t ∈ T, ∀ t' ∈ T, dist x t ≠ dist w t') :
    x ≠ w ∧ (dist x w ∈ dists T ∨ (∃ t ∈ T, dist x w = dist x t) ∨
      ∃ t ∈ T, dist x w = dist w t) := by
  have hxw : x ≠ w := by
    rintro rfl; obtain ⟨t, ht⟩ := hT1; exact hdisj t ht t ht rfl
  refine ⟨hxw, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h3, h2, h1⟩ := hcon
  have hR : Rainbow (insert x (insert w T)) :=
    rainbow_insert_insert T w x hwr hxr (fun s hs s' hs' => hdisj s hs s' hs')
      (fun s hs => h1 s hs) (fun s hs => h2 s hs)
      (fun s hs s' hs' hne h => h3 (h ▸ mem_dists hs hs' hne))
  have hcard : (insert x (insert w T)).card = n := by
    rw [card_insert_of_notMem, card_insert_of_notMem hwT]
    · omega
    · simp [hxw, hxT]
  exact (rainbowFree_iff n X).1 hfree _ (insert_subset hx (insert_subset hw hTX)) hcard hR
theorem affDim_mono {A B : Finset (ℝ^d)} (h : A ⊆ B) : affDim A ≤ affDim B := by
  unfold affDim
  exact Submodule.finrank_mono (vectorSpan_mono ℝ (by exact_mod_cast h))
def kG (n : ℕ) : ℕ := (n - 2).choose 2 + 2 * (n - 2)
theorem one_le_LRcost' (k r : ℕ) : (0 : ℝ) ≤ LRcost k r := le_trans zero_le_one (one_le_LRcost k r)
theorem G1_bip (n D h : ℕ) (X T P Q : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty)
    (hP : P ⊆ X) (hQ : Q ⊆ X) (hPg : ∀ x ∈ P, x ∉ T ∧ Rainbow (insert x T))
    (hQg : ∀ w ∈ Q, w ∉ T ∧ Rainbow (insert w T))
    (hdisj : ∀ x ∈ P, ∀ w ∈ Q, ∀ t ∈ T, ∀ t' ∈ T, dist x t ≠ dist w t') :
    (min P.card Q.card : ℝ) ≤ LRcost (kG n) (D + 2) * h := by
  classical
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · simp only [hPe, card_empty, CharP.cast_eq_zero]
    exact (min_le_left _ _).trans (mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _))
  rcases Q.eq_empty_or_nonempty with hQe | hQne
  · simp only [hQe, card_empty, CharP.cast_eq_zero]
    exact (min_le_right _ _).trans (mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _))
  let ι := ↥(dists T) ⊕ (↥T ⊕ ↥T)
  let τ : ι → TF (ℝ^d) (ℝ^d) := fun k => match k with
    | Sum.inl δ => TF.col fun _ => (δ : ℝ) ^ 2
    | Sum.inr (Sum.inl t) => TF.col fun w => dist w t ^ 2
    | Sum.inr (Sum.inr t) => TF.row fun x => dist x t ^ 2
  let M : ℝ^d → ℝ^d → ℝ := fun x w => dist x w ^ 2
  have hcardS : (Finset.univ : Finset ι).card ≤ kG n := by
    rw [card_univ]
    simp only [ι, Fintype.card_sum, Fintype.card_coe, kG]
    have hT' : T.card = n - 2 := by omega
    have := card_dists_le T
    rw [hT'] at this
    omega
  have hrank : rankOn M P Q ≤ D + 2 := by
    unfold rankOn
    have := rank_sqdist_le_affine X D hD (fun i : P => (i : ℝ^d)) (fun j : Q => (j : ℝ^d))
      (fun i => hP i.2) (fun j => hQ j.2) (fun _ => 0) (fun _ => 0)
    have e : (Matrix.of fun (i : P) (j : Q) => M i j) =
        Matrix.of fun (i : P) (j : Q) => ‖(i : ℝ^d) - j‖ ^ 2 - 0 - 0 := by
      ext i j; simp [M, dist_eq_norm]
    rw [e]; exact this
  have hcov : Covers M τ Finset.univ P Q := by
    intro x hx w hw
    obtain ⟨hxT, hxr⟩ := hPg x hx
    obtain ⟨hwT, hwr⟩ := hQg w hw
    obtain ⟨-, hcase⟩ := label_lemma n X T x w hfree hTX hTn hT1 (hP hx) (hQ hw) hxT hwT hxr hwr
      (hdisj x hx w hw)
    rcases hcase with h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · exact ⟨Sum.inl ⟨_, h⟩, mem_univ _, rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨t, ht⟩), mem_univ _, by simp [M, τ, TF.eval, h]⟩
    · exact ⟨Sum.inr (Sum.inl ⟨t, ht⟩), mem_univ _, by simp [M, τ, TF.eval, h]⟩
  obtain ⟨R, hRP, C, hCQ, t₀, -, c1, c2, hM⟩ :=
    theoremLR M τ (D + 2) (kG n) Finset.univ P Q hcardS hPne hQne hrank hcov
  have hortho : ∀ x ∈ R, ∀ x' ∈ R, ∀ w ∈ C, ∀ w' ∈ C, inner ℝ (x - x') (w - w') = 0 := by
    rcases t₀ with δ | t | t
    · refine ortho_of_equidistant R C (fun _ => (δ : ℝ)) fun x hx w hw => ?_
      have := hM x hx w hw
      simp only [M, τ, TF.eval] at this
      rw [← dist_eq_norm]
      have hδ : 0 ≤ (δ : ℝ) := (pos_of_mem_dists δ.2).le
      exact (pow_left_inj₀ dist_nonneg hδ two_ne_zero).1 this
    · refine ortho_of_equidistant R C (fun w => dist w t) fun x hx w hw => ?_
      have := hM x hx w hw
      simp only [M, τ, TF.eval] at this
      rw [← dist_eq_norm]
      exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 this
    · refine ortho_of_bisector R C t fun x hx w hw => ?_
      have := hM x hx w hw
      simp only [M, τ, TF.eval] at this
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact ((pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 this).symm
  have hRC : affDim (R ∪ C) ≤ D :=
    (affDim_mono (union_subset (hRP.trans hP) (hCQ.trans hQ))).trans hD
  have hmin := min_affDim_le_of_ortho R C D hRC hortho
  have hL := one_le_LRcost (kG n) (D + 2)
  rcases le_total (affDim R) (affDim C) with hle | hle
  · rw [min_eq_left hle] at hmin
    have hR := hh R (hRP.trans hP) hmin
    have : (R.card : ℝ) ≤ h := by exact_mod_cast hR
    calc (min P.card Q.card : ℝ) ≤ P.card := by exact_mod_cast min_le_left _ _
      _ ≤ LRcost (kG n) (D + 2) * R.card := c1
      _ ≤ LRcost (kG n) (D + 2) * h := mul_le_mul_of_nonneg_left this (by linarith)
  · rw [min_eq_right hle] at hmin
    have hC := hh C (hCQ.trans hQ) hmin
    have : (C.card : ℝ) ≤ h := by exact_mod_cast hC
    calc (min P.card Q.card : ℝ) ≤ Q.card := by exact_mod_cast min_le_right _ _
      _ ≤ LRcost (kG n) (D + 2) * C.card := c2
      _ ≤ LRcost (kG n) (D + 2) * h := mul_le_mul_of_nonneg_left this (by linarith)
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
noncomputable def labels (T : Finset (ℝ^d)) (x : ℝ^d) : Finset ℝ := T.image (dist x)
theorem card_colourings {α : Type*} [DecidableEq α] (V A B : Finset α) (hA : A ⊆ V)
    (hB : B ⊆ V) (hAB : Disjoint A B) :
    (V.powerset.filter fun R => A ⊆ R ∧ Disjoint B R).card = 2 ^ (V.card - A.card - B.card) := by
  have hc : (V \ (A ∪ B)).card = V.card - A.card - B.card := by
    rw [card_sdiff_of_subset (union_subset hA hB), card_union_of_disjoint hAB]; omega
  rw [← hc, ← card_powerset]
  refine card_nbij' (fun R => R \ A) (fun S => S ∪ A) ?_ ?_ ?_ ?_
  · intro R hR
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset] at hR
    obtain ⟨hRV, hAR, hBR⟩ := hR
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_sdiff, coe_union]
    intro x hx
    obtain ⟨hxR, hxA⟩ := hx
    refine ⟨hRV hxR, fun h => ?_⟩
    rcases h with h | h
    · exact hxA h
    · exact disjoint_left.1 hBR h hxR
  · intro S hS
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_sdiff, coe_union] at hS
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset]
    refine ⟨union_subset (fun x hx => (hS (mem_coe.2 hx)).1) hA, subset_union_right, ?_⟩
    rw [disjoint_left]
    intro x hxB hx
    rcases mem_union.1 hx with h | h
    · exact (hS (mem_coe.2 h)).2 (Or.inr hxB)
    · exact disjoint_left.1 hAB h hxB
  · intro R hR
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset] at hR
    exact sdiff_union_of_subset hR.2.1
  · intro S hS
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_sdiff, coe_union] at hS
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hxA⟩
      · exact h
      · exact absurd h hxA
    · intro hx
      exact ⟨Or.inl hx, fun hxA => (hS (mem_coe.2 hx)).2 (Or.inl hxA)⟩
theorem card_labels (T : Finset (ℝ^d)) (x : ℝ^d) (hxT : x ∉ T) (hr : Rainbow (insert x T)) :
    (labels T x).card = T.card := by
  unfold labels
  refine card_image_of_injOn fun t ht t' ht' h => ?_
  by_contra hne
  have hxt : x ≠ t := fun e => hxT (e ▸ ht)
  have hxt' : x ≠ t' := fun e => hxT (e ▸ ht')
  rcases hr x (mem_insert_self _ _) t (mem_insert_of_mem ht) x (mem_insert_self _ _) t'
      (mem_insert_of_mem ht') hxt hxt' h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact hne h2
  · exact hxt' h1
theorem G1_count (n D h : ℕ) (X T Y : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hYX : Y ⊆ X)
    (hYg : ∀ x ∈ Y, x ∉ T ∧ Rainbow (insert x T)) :
    (((Y ×ˢ Y).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) ≤
      4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) * Y.card := by
  classical
  set μ0 := LRcost (kG n) (D + 2) * h with hμ0
  have hμ0 : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  set V := Y.biUnion (labels T) with hV
  set LD := (Y ×ˢ Y).filter fun q => Disjoint (labels T q.1) (labels T q.2) with hLD
  have hlab : ∀ x ∈ Y, (labels T x).card = n - 2 := fun x hx => by
    rw [card_labels T x (hYg x hx).1 (hYg x hx).2]; omega
  have hlabV : ∀ x ∈ Y, labels T x ⊆ V := fun x hx => subset_biUnion_of_mem _ hx
  rcases LD.eq_empty_or_nonempty with hLDe | ⟨q0, hq0⟩
  · rw [hLDe, card_empty, Nat.cast_zero]; positivity
  have hV2 : 2 * (n - 2) ≤ V.card := by
    obtain ⟨hq0Y, hq0d⟩ := mem_filter.1 hq0
    obtain ⟨h1, h2⟩ := mem_product.1 hq0Y
    have := card_le_card (union_subset (hlabV _ h1) (hlabV _ h2))
    rw [card_union_of_disjoint hq0d, hlab _ h1, hlab _ h2] at this
    omega
  have hprod : ∀ R ∈ V.powerset, (((Y.filter fun x => labels T x ⊆ R).card *
      (Y.filter fun w => Disjoint (labels T w) R).card : ℕ) : ℝ) ≤ μ0 * Y.card := by
    intro R _
    set P := Y.filter fun x => labels T x ⊆ R
    set Q := Y.filter fun w => Disjoint (labels T w) R
    have hmin := G1_bip n D h X T P Q hfree hD hh hTX hTn hT1
      ((filter_subset _ _).trans hYX) ((filter_subset _ _).trans hYX)
      (fun x hx => hYg x (mem_filter.1 hx).1) (fun w hw => hYg w (mem_filter.1 hw).1)
      (fun x hx w hw t ht t' ht' heq => by
        have hxR := (mem_filter.1 hx).2
        have hwR := (mem_filter.1 hw).2
        have h1 : dist x t ∈ R := hxR (mem_image_of_mem _ ht)
        have h2 : dist w t' ∈ labels T w := mem_image_of_mem _ ht'
        exact disjoint_left.1 hwR h2 (heq ▸ h1))
    have hP : (P.card : ℝ) ≤ Y.card := by exact_mod_cast card_le_card (filter_subset _ _)
    have hQ : (Q.card : ℝ) ≤ Y.card := by exact_mod_cast card_le_card (filter_subset _ _)
    push_cast
    rcases le_total P.card Q.card with hle | hle
    · rw [min_eq_left (by exact_mod_cast hle)] at hmin
      calc (P.card : ℝ) * Q.card ≤ μ0 * Q.card :=
            mul_le_mul_of_nonneg_right hmin (Nat.cast_nonneg _)
        _ ≤ μ0 * Y.card := mul_le_mul_of_nonneg_left hQ hμ0
    · rw [min_eq_right (by exact_mod_cast hle)] at hmin
      calc (P.card : ℝ) * Q.card ≤ P.card * μ0 :=
            mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg _)
        _ ≤ Y.card * μ0 := mul_le_mul_of_nonneg_right hP hμ0
        _ = μ0 * Y.card := mul_comm _ _
  have hdc : ∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
      (Y.filter fun w => Disjoint (labels T w) R).card) =
      ∑ q ∈ Y ×ˢ Y, (V.powerset.filter fun R => labels T q.1 ⊆ R ∧
        Disjoint (labels T q.2) R).card := by
    have hR : ∀ R, (Y.filter fun x => labels T x ⊆ R).card *
        (Y.filter fun w => Disjoint (labels T w) R).card =
        ((Y ×ˢ Y).filter fun q => labels T q.1 ⊆ R ∧ Disjoint (labels T q.2) R).card := by
      intro R
      rw [← card_product]
      congr 1
      ext q
      simp only [mem_product, mem_filter]
      tauto
    rw [Finset.sum_congr rfl (fun R _ => hR R)]
    simp only [card_filter]
    exact Finset.sum_comm
  have hlow : LD.card * 2 ^ (V.card - 2 * (n - 2)) ≤
      ∑ q ∈ Y ×ˢ Y, (V.powerset.filter fun R => labels T q.1 ⊆ R ∧
        Disjoint (labels T q.2) R).card := by
    calc LD.card * 2 ^ (V.card - 2 * (n - 2))
        = ∑ q ∈ LD, (V.powerset.filter fun R => labels T q.1 ⊆ R ∧
            Disjoint (labels T q.2) R).card := by
          rw [card_eq_sum_ones, sum_mul]
          refine sum_congr rfl fun q hq => ?_
          obtain ⟨hqY, hqd⟩ := mem_filter.1 hq
          obtain ⟨h1, h2⟩ := mem_product.1 hqY
          rw [card_colourings V _ _ (hlabV _ h1) (hlabV _ h2) hqd, hlab _ h1, hlab _ h2]
          rw [one_mul]; congr 1; omega
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  have hup : (∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
      (Y.filter fun w => Disjoint (labels T w) R).card : ℕ) : ℝ) ≤
      2 ^ V.card * (μ0 * Y.card) := by
    push_cast
    calc ∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
          ((Y.filter fun w => Disjoint (labels T w) R).card : ℝ))
        ≤ ∑ _R ∈ V.powerset, μ0 * Y.card := by
          refine sum_le_sum fun R hR => ?_
          have := hprod R hR; push_cast at this; exact this
      _ = 2 ^ V.card * (μ0 * Y.card) := by rw [sum_const, card_powerset, nsmul_eq_mul]; push_cast; ring
  have hkey : (LD.card : ℝ) * 2 ^ (V.card - 2 * (n - 2)) ≤ 2 ^ V.card * (μ0 * Y.card) := by
    have : ((LD.card * 2 ^ (V.card - 2 * (n - 2)) : ℕ) : ℝ) ≤
        ((∑ R ∈ V.powerset, ((Y.filter fun x => labels T x ⊆ R).card *
          (Y.filter fun w => Disjoint (labels T w) R).card) : ℕ) : ℝ) := by
      exact_mod_cast (hlow.trans hdc.symm.le)
    push_cast at this
    exact this.trans (by exact_mod_cast hup)
  have hsplit : (2 : ℝ) ^ V.card = 2 ^ (V.card - 2 * (n - 2)) * 4 ^ (n - 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
  rw [hsplit] at hkey
  have hpos : (0 : ℝ) < 2 ^ (V.card - 2 * (n - 2)) := by positivity
  have : (LD.card : ℝ) * 2 ^ (V.card - 2 * (n - 2)) ≤
      (4 ^ (n - 2) * μ0 * Y.card) * 2 ^ (V.card - 2 * (n - 2)) := by nlinarith
  exact le_of_mul_le_mul_right this hpos
theorem G1_degree (n D h : ℕ) (X T Y : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hYX : Y ⊆ X)
    (hYg : ∀ x ∈ Y, x ∉ T ∧ Rainbow (insert x T))
    (hdeg : ∀ v : ℝ, 4 * (n - 2) * (Y.filter fun x => v ∈ labels T x).card ≤ Y.card) :
    3 * (Y.card : ℝ) ≤ 4 * (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h)) := by
  classical
  set μ0 := LRcost (kG n) (D + 2) * h with hμ0
  set V := Y.biUnion (labels T) with hV
  set LD := (Y ×ˢ Y).filter fun q => Disjoint (labels T q.1) (labels T q.2) with hLD
  set Yv : ℝ → Finset (ℝ^d) := fun v => Y.filter fun x => v ∈ labels T x with hYv
  set Sh := V.biUnion fun v => Yv v ×ˢ Yv v with hSh
  have hn2 : 1 ≤ n - 2 := by have := card_pos.2 hT1; omega
  have hlab : ∀ x ∈ Y, (labels T x).card = n - 2 := fun x hx => by
    rw [card_labels T x (hYg x hx).1 (hYg x hx).2]; omega
  have hcover : Y ×ˢ Y ⊆ LD ∪ Sh := by
    intro q hq
    by_cases hd : Disjoint (labels T q.1) (labels T q.2)
    · exact mem_union_left _ (mem_filter.2 ⟨hq, hd⟩)
    · obtain ⟨h1, h2⟩ := mem_product.1 hq
      rw [not_disjoint_iff] at hd
      obtain ⟨v, hv1, hv2⟩ := hd
      exact mem_union_right _ (mem_biUnion.2 ⟨v, mem_biUnion.2 ⟨q.1, h1, hv1⟩,
        mem_product.2 ⟨mem_filter.2 ⟨h1, hv1⟩, mem_filter.2 ⟨h2, hv2⟩⟩⟩)
  have hsumdeg : ∑ v ∈ V, (Yv v).card = (n - 2) * Y.card := by
    have : ∑ v ∈ V, (Yv v).card = ∑ x ∈ Y, (V.filter fun v => v ∈ labels T x).card := by
      simp only [hYv, card_filter]
      exact Finset.sum_comm
    rw [this]
    have h2 : ∀ x ∈ Y, (V.filter fun v => v ∈ labels T x).card = n - 2 := by
      intro x hx
      rw [← hlab x hx]
      congr 1
      ext v
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨subset_biUnion_of_mem _ hx h, h⟩⟩
    rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
  have hSh : 4 * (n - 2) * Sh.card ≤ (n - 2) * Y.card * Y.card := by
    have h1 : Sh.card ≤ ∑ v ∈ V, (Yv v).card * (Yv v).card := by
      refine card_biUnion_le.trans (le_of_eq ?_)
      exact sum_congr rfl fun v _ => card_product _ _
    calc 4 * (n - 2) * Sh.card ≤ ∑ v ∈ V, (4 * (n - 2) * (Yv v).card) * (Yv v).card := by
          calc 4 * (n - 2) * Sh.card ≤ 4 * (n - 2) * ∑ v ∈ V, (Yv v).card * (Yv v).card :=
                Nat.mul_le_mul_left _ h1
            _ = ∑ v ∈ V, (4 * (n - 2) * (Yv v).card) * (Yv v).card := by
                rw [mul_sum]; exact sum_congr rfl fun v _ => by ring
      _ ≤ ∑ v ∈ V, Y.card * (Yv v).card := sum_le_sum fun v _ => Nat.mul_le_mul_right _ (hdeg v)
      _ = Y.card * ((n - 2) * Y.card) := by rw [← mul_sum, hsumdeg]
      _ = (n - 2) * Y.card * Y.card := by ring
  have hLDc := G1_count n D h X T Y hfree hD hh hTX hTn hT1 hYX hYg
  have h1 : Y.card * Y.card ≤ LD.card + Sh.card := by
    rw [← card_product]; exact (card_le_card hcover).trans (card_union_le _ _)
  have h1r : (Y.card : ℝ) * Y.card ≤ LD.card + Sh.card := by exact_mod_cast h1
  have h2r : 4 * ((n - 2 : ℕ) : ℝ) * Sh.card ≤ ((n - 2 : ℕ) : ℝ) * Y.card * Y.card := by
    exact_mod_cast hSh
  have hn2r : (1 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast hn2
  have h3 : 4 * (Sh.card : ℝ) ≤ Y.card * Y.card := by
    have : ((n - 2 : ℕ) : ℝ) * (4 * Sh.card) ≤ ((n - 2 : ℕ) : ℝ) * (Y.card * Y.card) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  rcases Nat.eq_zero_or_pos Y.card with h0 | hpos
  · rw [h0, Nat.cast_zero]
    have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
    have := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (n - 2)) hμ
    linarith
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hpos
  have : 3 * (Y.card : ℝ) * Y.card ≤ 4 * (4 ^ (n - 2) * μ0) * Y.card := by nlinarith
  exact le_of_mul_le_mul_right this hYpos
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
noncomputable def hrSet (S V : Finset (ℝ^d)) (c : ℝ^d) (θ : ℝ) : Finset (ℝ^d) :=
  V.filter fun x => dist x c ∉ Rb S c ∧ (∀ s ∈ S, dist x c ≠ dist x s) ∧
    ((V.filter fun y => dist y c = dist x c).card : ℝ) < θ
def HRholds (S W : Finset (ℝ^d)) (σ Γ' : ℝ) : Prop :=
  ∀ c ∈ W, ∀ V ⊆ W.erase c, ∀ θ : ℝ, σ ≤ θ → ((hrSet S V c θ).card : ℝ) ≤ Γ' * θ
theorem lemma_HR (X : Finset (ℝ^d)) (r : ℕ) (Γ σmin σ : ℝ)
    (hclaim : ClaimAt X (r + 1) Γ σmin) (S W : Finset (ℝ^d)) (hc : Config X S W r σ)
    (hσpos : 0 < σ) (hσ : σmin ≤ σ) : HRholds S W σ (Γ + r ^ 2) := by
  classical
  intro c hcW V hV θ hθ
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hVW : V ⊆ W := hV.trans (erase_subset _ _)
  set V0 := hrSet S V c θ
  set Cls := (S ×ˢ S).biUnion fun q => W.filter fun x => dist x q.1 = dist c q.2
  set V1 := V0.filter fun x => x ∉ Cls
  have hV0 : V0 ⊆ Cls ∪ V1 := by
    intro x hx
    by_cases h : x ∈ Cls
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_filter.2 ⟨hx, h⟩)
  have hCls : (Cls.card : ℝ) ≤ r ^ 2 * θ := by
    have h1 : Cls.card ≤ ∑ q ∈ S ×ˢ S, (W.filter fun x => dist x q.1 = dist c q.2).card :=
      card_biUnion_le
    have h2 : ∀ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist c q.2).card : ℝ) ≤ θ := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := mem_product.1 hq
      have hpos : 0 < dist c q.2 := dist_pos.2 fun e => hWS c hcW (e ▸ hq2)
      exact (hc.cap q.1 hq1 _ hpos).le.trans hθ
    calc (Cls.card : ℝ) ≤ ∑ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist c q.2).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ _q ∈ S ×ˢ S, θ := sum_le_sum h2
      _ = r ^ 2 * θ := by rw [sum_const, card_product, hc.card, nsmul_eq_mul]; push_cast; ring
  have hconf : Config X (insert c S) V1 (r + 1) θ := by
    refine ⟨insert_subset (hc.subW hcW) hc.subX, hc.ext c hcW, ?_, ?_, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem (hWS c hcW), hc.card]
    · intro x hx
      exact hc.subW (hVW (mem_filter.1 (mem_filter.1 hx).1).1)
    · rw [disjoint_left]
      intro x hx hxi
      have hxV : x ∈ V := (mem_filter.1 (mem_filter.1 hx).1).1
      have hxc : x ≠ c := (mem_erase.1 (hV hxV)).1
      rcases mem_insert.1 hxi with h | h
      · exact hxc h
      · exact hWS x (hVW hxV) h
    · intro x hx
      obtain ⟨hx0, hxC⟩ := mem_filter.1 hx
      obtain ⟨hxV, hR, hbis, -⟩ := mem_filter.1 hx0
      have hxW := hVW hxV
      have hxc : x ≠ c := (mem_erase.1 (hV hxV)).1
      refine rainbow_insert_insert S c x (hc.ext c hcW) (hc.ext x hxW) ?_ ?_ ?_ ?_
      · intro s hs s' hs' h
        exact hxC (mem_biUnion.2 ⟨(s, s'), mem_product.2 ⟨hs, hs'⟩, mem_filter.2 ⟨hxW, h⟩⟩)
      · intro s hs h
        exact hR (mem_union_right _ (mem_image.2 ⟨s, hs, h.symm⟩))
      · intro s hs h; exact hbis s hs h
      · intro s hs s' hs' hne h
        exact hR (mem_union_left _ (h ▸ mem_dists hs hs' hne))
    · intro s hs t ht
      have hsub : V1 ⊆ V := fun x hx => (mem_filter.1 (mem_filter.1 hx).1).1
      rcases mem_insert.1 hs with rfl | hsS
      · by_cases hne : (V1.filter fun x => dist x s = t).Nonempty
        · obtain ⟨x0, hx0⟩ := hne
          obtain ⟨hx0V1, hx0t⟩ := mem_filter.1 hx0
          have hlt := (mem_filter.1 (mem_filter.1 hx0V1).1).2.2.2
          rw [hx0t] at hlt
          calc ((V1.filter fun x => dist x s = t).card : ℝ)
              ≤ ((V.filter fun x => dist x s = t).card : ℝ) := by
                exact_mod_cast card_le_card (filter_subset_filter _ hsub)
            _ < θ := hlt
        · rw [not_nonempty_iff_eq_empty] at hne
          rw [hne, card_empty, Nat.cast_zero]; linarith
      · calc ((V1.filter fun x => dist x s = t).card : ℝ)
            ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
              exact_mod_cast card_le_card (filter_subset_filter _ (hsub.trans hVW))
          _ < σ := hc.cap s hsS t ht
          _ ≤ θ := hθ
  have hV1 : (V1.card : ℝ) ≤ Γ * θ := hclaim _ _ θ hconf (hσ.trans hθ)
  have h1 : V0.card ≤ Cls.card + V1.card := (card_le_card hV0).trans (card_union_le _ _)
  have : (V0.card : ℝ) ≤ Cls.card + V1.card := by exact_mod_cast h1
  linarith
end E1088
end
section
open Finset
namespace E1088
theorem konig_cover {α β : Type*} [DecidableEq α] [DecidableEq β] (L : Finset α)
    (N : α → Finset β) (m : ℕ)
    (hno : ∀ M : Finset (α × β), (∀ p ∈ M, p.1 ∈ L ∧ p.2 ∈ N p.1) →
      (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 ∨ p.2 = q.2 → p = q) → M.card < m) :
    ∃ A ⊆ L, ∃ B : Finset β, (∀ a ∈ L, a ∉ A → N a ⊆ B) ∧ A.card + B.card < m := by
  classical
  have hm : 0 < m := hno ∅ (by simp) (by simp)
  by_cases hβ : Nonempty β
  swap
  · exact ⟨∅, empty_subset _, ∅, fun a _ _ b _ => (hβ ⟨b⟩).elim, by simpa using hm⟩
  obtain ⟨b0⟩ := hβ
  obtain ⟨S, hS, hmax⟩ := exists_max_image L.powerset
    (fun S => (S.card : ℤ) - (S.biUnion N).card) ⟨∅, empty_mem_powerset _⟩
  rw [mem_powerset] at hS
  set d : ℤ := (S.card : ℤ) - (S.biUnion N).card with hd
  have hd0 : 0 ≤ d := by
    have := hmax ∅ (empty_mem_powerset _); simpa using this
  set d' := d.toNat with hd'
  have hdd : (d' : ℤ) = d := Int.toNat_of_nonneg hd0
  let t : {a // a ∈ L} → Finset (β ⊕ Fin d') := fun a => (N a.1).disjSum Finset.univ
  have hHall : ∀ s : Finset {a // a ∈ L}, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
    · simp
    set s' := s.map (Function.Embedding.subtype _) with hs'
    have hs'L : s' ⊆ L := by
      intro a ha; obtain ⟨x, -, rfl⟩ := mem_map.1 ha; exact x.2
    have hsub : (s'.biUnion N).disjSum (Finset.univ : Finset (Fin d')) ⊆ s.biUnion t := by
      intro z hz
      rcases z with b | i
      · rw [inl_mem_disjSum, mem_biUnion] at hz
        obtain ⟨a, ha, hb⟩ := hz
        obtain ⟨x, hx, rfl⟩ := mem_map.1 ha
        exact mem_biUnion.2 ⟨x, hx, inl_mem_disjSum.2 hb⟩
      · exact mem_biUnion.2 ⟨a0, ha0, inr_mem_disjSum.2 (mem_univ _)⟩
    have h1 := card_le_card hsub
    rw [card_disjSum, card_univ, Fintype.card_fin] at h1
    have h2 := hmax s' (mem_powerset.2 hs'L)
    have h3 : s'.card = s.card := card_map _
    have : (s.card : ℤ) ≤ (s'.biUnion N).card + d' := by rw [hdd]; omega
    omega
  obtain ⟨f, hfinj, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  set Ll := (Finset.univ : Finset {a // a ∈ L}).filter fun a => (f a).isLeft with hLl
  set Lr := (Finset.univ : Finset {a // a ∈ L}).filter fun a => ¬ (f a).isLeft with hLr
  let g : {a // a ∈ L} → β := fun a => Sum.elim id (fun _ => b0) (f a)
  have hgL : ∀ a ∈ Ll, f a = Sum.inl (g a) := by
    intro a ha
    have := (mem_filter.1 ha).2
    simp only [g]
    rcases h : f a with b | i
    · rfl
    · rw [h] at this; simp at this
  set M := Ll.image fun a => (a.1, g a) with hM
  have hMprop : ∀ p ∈ M, p.1 ∈ L ∧ p.2 ∈ N p.1 := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    refine ⟨a.2, ?_⟩
    have := hft a
    rw [hgL a ha] at this
    exact inl_mem_disjSum.1 this
  have hMinj : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 ∨ p.2 = q.2 → p = q := by
    intro p hp q hq h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨a', ha', rfl⟩ := mem_image.1 hq
    rcases h with h | h
    · have : a = a' := Subtype.ext h
      rw [this]
    · have : f a = f a' := by rw [hgL a ha, hgL a' ha']; simp only at h; rw [h]
      rw [hfinj this]
  have hMcard : M.card = Ll.card :=
    card_image_of_injective _ (fun a a' h => Subtype.ext (Prod.ext_iff.1 h).1)
  have hLrcard : Lr.card ≤ d' := by
    have hmaps : ∀ a ∈ Lr, f a ∈ (Finset.univ : Finset (Fin d')).map Function.Embedding.inr := by
      intro a ha
      have := (mem_filter.1 ha).2
      rcases h : f a with b | i
      · rw [h] at this; simp at this
      · exact mem_map.2 ⟨i, mem_univ _, rfl⟩
    have := card_le_card_of_injOn f hmaps (fun x _ y _ h => hfinj h)
    simpa using this
  have hsplit : Ll.card + Lr.card = L.card := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_coe]
  have hMlt := hno M hMprop hMinj
  refine ⟨L \ S, sdiff_subset, S.biUnion N, ?_, ?_⟩
  · intro a ha haA
    have haS : a ∈ S := by
      by_contra h; exact haA (mem_sdiff.2 ⟨ha, h⟩)
    exact subset_biUnion_of_mem N haS
  · rw [card_sdiff_of_subset hS]
    have hSL := card_le_card hS
    have : ((L.card - S.card + (S.biUnion N).card : ℕ) : ℤ) = L.card - d := by
      push_cast [Nat.cast_sub hSL]; rw [hd]; ring
    have h4 : (L.card : ℤ) - d < m := by rw [← hdd]; omega
    omega
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
structure Ambient (n D h : ℕ) (X : Finset (ℝ^d)) : Prop where
  free : RainbowFree n X
  dim : affDim X ≤ D
  half : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h
def kstar (n : ℕ) : ℕ := 6 ^ n + 2 * n ^ 2
noncomputable def smin (n D h : ℕ) : ℝ := 4 ^ (n + 1) * LRcost (kstar n) (D + 2) * (h + 1)
theorem one_le_smin (n D h : ℕ) : 1 ≤ smin n D h := by
  unfold smin
  have h1 : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have h2 := one_le_LRcost (kstar n) (D + 2)
  have h3 : (1 : ℝ) ≤ h + 1 := by have := Nat.cast_nonneg (α := ℝ) h; linarith
  have := mul_le_mul h1 h2 zero_le_one (by linarith)
  nlinarith
def Kr (n r : ℕ) : ℕ := 12 * 6 ^ (n - 5 - r)
structure RainbowFamily (S W : Finset (ℝ^d)) (B : Finset (ℝ^d)) (I : Finset ℕ)
    (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) : Prop where
  Bne : B.Nonempty
  F1 : Disjoint S B ∧ Rainbow (S ∪ B)
  Cne : ∀ k ∈ I, (C k).Nonempty ∧ C k ⊆ W
  F2 : ∀ k ∈ I, ∀ x ∈ C k, ∀ b ∈ B, dist x b = β k b
  F3 : (∀ k ∈ I, ∀ k' ∈ I, ∀ b ∈ B, ∀ b' ∈ B, β k b = β k' b' → k = k' ∧ b = b') ∧
    ∀ k ∈ I, ∀ b ∈ B, β k b ∉ dists (S ∪ B)
  F4 : ∀ k ∈ I, ∀ x ∈ C k, x ∉ S ∪ B ∧ Rainbow (insert x (S ∪ B))
  F5 : ∀ k ∈ I, ∀ x ∈ C k, ∀ s ∈ S, ∀ k' ∈ I, ∀ b ∈ B, dist x s ≠ β k' b
def kc (n r : ℕ) : ℕ :=
  let w1 := (n - 2) + (n - 2).choose 2 + (n - 4 - r)
  (w1 + 1 + r) + (w1 + 2 * r + r.choose 2)
def ksl (r p K : ℕ) : ℕ := 3 * K - 1 + (r + p).choose 2 + 2 * p + 2 * r
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem LRcost_mono (r : ℕ) {k k' : ℕ} (h : k ≤ k') : LRcost k r ≤ LRcost k' r := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    simp only [LRcost]
    have h1 := one_le_roundCost (m + 1) r
    have h2 := one_le_LRcost m r
    nlinarith
theorem kG_le_kstar (n : ℕ) : kG n ≤ kstar n := by
  unfold kG kstar
  have h1 : (n - 2).choose 2 ≤ (n - 2) * (n - 2) := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have h2 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h3 : n < 6 ^ n := Nat.lt_pow_self (by norm_num)
  have h4 : n ^ 2 = n * n := sq n
  have h5 : n ≤ n * n := Nat.le_mul_self n
  rw [h4]
  generalize (n - 2).choose 2 = C at *
  generalize (n - 2) * (n - 2) = P at *
  generalize n * n = Z at *
  generalize 6 ^ n = Y at *
  omega
theorem ClaimAt.mono_Γ {X : Finset (ℝ^d)} {j : ℕ} {Γ Γ' σmin : ℝ} (hσ : 0 ≤ σmin)
    (hΓ : Γ ≤ Γ') (h : ClaimAt X j Γ σmin) : ClaimAt X j Γ' σmin := by
  intro S W σ hc hs
  have := h S W σ hc hs
  have : 0 ≤ σ := hσ.trans hs
  nlinarith
theorem claim_top (n : ℕ) (hn : 4 ≤ n) (d D h : ℕ) (X : Finset (ℝ^d)) (hX : Ambient n D h X) :
    ClaimAt X (n - 2) (4 * ((n - 2 : ℕ) : ℝ) ^ 2) (smin n D h) := by
  classical
  intro S W σ hc hσ
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  by_contra hcon
  push Not at hcon
  have hS : S.card + 2 = n := by rw [hc.card]; omega
  have hS1 : S.Nonempty := card_pos.1 (by rw [hc.card]; omega)
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hn2 : (2 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 2 by omega)
  have hdeg : ∀ v : ℝ, 4 * (n - 2) * (W.filter fun x => v ∈ labels S x).card ≤ W.card := by
    intro v
    have hsub : (W.filter fun x => v ∈ labels S x) ⊆ S.biUnion fun s => W.filter fun x => dist x s = v := by
      intro x hx
      obtain ⟨hxW, hv⟩ := mem_filter.1 hx
      obtain ⟨s, hs, hsv⟩ := mem_image.1 hv
      exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hxW, hsv⟩⟩
    have hc1 : ((W.filter fun x => v ∈ labels S x).card : ℝ) ≤ ((n - 2 : ℕ) : ℝ) * σ := by
      have h1 := (card_le_card hsub).trans card_biUnion_le
      have h2 : ∀ s ∈ S, ((W.filter fun x => dist x s = v).card : ℝ) ≤ σ := by
        intro s hs
        by_cases hv : 0 < v
        · exact (hc.cap s hs v hv).le
        · have : (W.filter fun x => dist x s = v) = ∅ := by
            rw [filter_eq_empty_iff]
            intro x hx hxv
            have := dist_pos.2 (fun e : x = s => hWS x hx (e ▸ hs))
            rw [hxv] at this; exact hv this
          rw [this, card_empty, Nat.cast_zero]; linarith
      calc ((W.filter fun x => v ∈ labels S x).card : ℝ)
          ≤ ∑ s ∈ S, ((W.filter fun x => dist x s = v).card : ℝ) := by exact_mod_cast h1
        _ ≤ ∑ _s ∈ S, σ := sum_le_sum h2
        _ = ((n - 2 : ℕ) : ℝ) * σ := by rw [sum_const, nsmul_eq_mul, hc.card]
    have key : (4 : ℝ) * ((n - 2 : ℕ) : ℝ) * ((W.filter fun x => v ∈ labels S x).card : ℝ) ≤
        W.card := by
      have h0 : (0 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have : 4 * ((n - 2 : ℕ) : ℝ) * ((W.filter fun x => v ∈ labels S x).card : ℝ) ≤
          4 * ((n - 2 : ℕ) : ℝ) * (((n - 2 : ℕ) : ℝ) * σ) :=
        mul_le_mul_of_nonneg_left hc1 (by positivity)
      nlinarith
    exact_mod_cast key
  have hG := G1_degree n D h X S W hX.free hX.dim hX.half hc.subX hS hS1 hc.subW
    (fun x hx => ⟨hWS x hx, hc.ext x hx⟩) hdeg
  have hL := LRcost_mono (D + 2) (kG_le_kstar n)
  have hL1 := one_le_LRcost (kG n) (D + 2)
  have h4 : (4 : ℝ) * 4 ^ (n - 2) ≤ 4 ^ (n + 1) := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hbound : 4 * (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h)) ≤ smin n D h := by
    unfold smin
    have e1 : LRcost (kG n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * (h + 1) :=
      mul_le_mul hL (by linarith) hh0 (by linarith)
    calc 4 * (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h))
        = (4 * 4 ^ (n - 2)) * (LRcost (kG n) (D + 2) * h) := by ring
      _ ≤ 4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * (h + 1)) :=
          mul_le_mul h4 e1 (by positivity) (by positivity)
      _ = _ := by ring
  have hW : 3 * (W.card : ℝ) ≤ smin n D h := hG.trans hbound
  have hn2' : (1 : ℝ) ≤ 4 * ((n - 2 : ℕ) : ℝ) ^ 2 := by nlinarith
  have : (W.card : ℝ) ≤ σ := by nlinarith [Nat.cast_nonneg (α := ℝ) W.card]
  nlinarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem gl_lr_or {ι : Type*} [DecidableEq ι] (n D h : ℕ) (X : Finset (ℝ^d))
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (R0 C0 : Finset (ℝ^d)) (hR0 : R0 ⊆ X) (hC0 : C0 ⊆ X) (J : Finset ι)
    (colF : ι → ℝ^d → ℝ) (P : Finset (ℝ^d)) (hk : J.card + P.card ≤ kstar n)
    (hfew : ∀ c ∈ C0, 16 * (D + 2) ^ (J.card + P.card) *
      (R0.filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card ≤ R0.card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < R0.card) :
    (C0.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  classical
  set k := J.card + P.card with hkdef
  set LRc := LRcost (kstar n) (D + 2) with hLRc
  have hLR1 : 1 ≤ LRc := one_le_LRcost _ _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  rcases C0.eq_empty_or_nonempty with hCe | hCne
  · rw [hCe, card_empty, Nat.cast_zero]; positivity
  have hRne : R0.Nonempty := by
    rw [← card_pos]; have : (0 : ℝ) < R0.card := by nlinarith
    exact_mod_cast this
  let B : ℝ^d → ℝ^d → ℝ := fun x c =>
    (∏ i ∈ J, (‖x - c‖ ^ 2 - colF i c)) * ∏ s ∈ P, (‖x - c‖ ^ 2 - ‖x - s‖ ^ 2)
  have hBzero : ∀ x c, B x c ≠ 0 → (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
      ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2 := by
    intro x c hB
    simp only [B, ne_eq, mul_eq_zero, not_or, prod_eq_zero_iff, not_exists, not_and] at hB
    exact ⟨fun i hi h => hB.1 i hi (by rw [h]; ring),
      fun s hs h => hB.2 s hs (by rw [h]; ring)⟩
  have hrank : rankOn B R0 C0 ≤ (D + 2) ^ k := by
    unfold rankOn
    let F : ι ⊕ ℝ^d → ℝ^d → ℝ^d → ℝ := fun t => match t with
      | Sum.inl i => fun x c => ‖x - c‖ ^ 2 - 0 - colF i c
      | Sum.inr s => fun x c => ‖x - c‖ ^ 2 - ‖x - s‖ ^ 2 - 0
    have hB : (Matrix.of fun (x : R0) (c : C0) => B x c) =
        Matrix.of fun (x : R0) (c : C0) => ∏ t ∈ J.disjSum P, F t x c := by
      ext x c
      simp only [Matrix.of_apply, B, prod_disjSum, F, sub_zero]
    rw [hB]
    refine (rank_finset_prod_le (J.disjSum P) (fun t => Matrix.of fun (x : R0) (c : C0) =>
      F t x c)).trans ?_
    calc ∏ t ∈ J.disjSum P, (Matrix.of fun (x : R0) (c : C0) => F t x c).rank
        ≤ ∏ _t ∈ J.disjSum P, (D + 2) := by
          refine prod_le_prod' fun t _ => ?_
          rcases t with i | s
          · exact rank_sqdist_le_affine X D hD (fun x : R0 => (x : ℝ^d)) (fun c : C0 => (c : ℝ^d))
              (fun x => hR0 x.2) (fun c => hC0 c.2) (fun _ => 0) (fun c => colF i c)
          · exact rank_sqdist_le_affine X D hD (fun x : R0 => (x : ℝ^d)) (fun c : C0 => (c : ℝ^d))
              (fun x => hR0 x.2) (fun c => hC0 c.2) (fun x => ‖(x : ℝ^d) - s‖ ^ 2) (fun _ => 0)
      _ = (D + 2) ^ k := by rw [prod_const, card_disjSum]
  have hsupp : 16 * (D + 2) ^ k * (supp B R0 C0).card ≤ R0.card * C0.card := by
    rw [card_supp_eq_sum', mul_sum]
    calc ∑ c ∈ C0, 16 * (D + 2) ^ k * (R0.filter fun x => B x c ≠ 0).card
        ≤ ∑ _c ∈ C0, R0.card := by
          refine sum_le_sum fun c hc => le_trans ?_ (hfew c hc)
          exact Nat.mul_le_mul_left _ (card_le_card fun x hx =>
            mem_filter.2 ⟨(mem_filter.1 hx).1, hBzero x c (mem_filter.1 hx).2⟩)
      _ = R0.card * C0.card := by rw [sum_const, smul_eq_mul, mul_comm]
  obtain ⟨R1, hR1, C1, hC1, c1, c2, hzero⟩ :=
    cleaning B R0 C0 ((D + 2) ^ k) (Nat.one_le_pow _ _ (by omega)) hrank hsupp
  have hR1ne : R1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hRne; omega
  have hC1ne : C1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hCne; omega
  let τ : ι ⊕ ℝ^d → TF (ℝ^d) (ℝ^d) := fun t => match t with
    | Sum.inl i => TF.col (colF i)
    | Sum.inr s => TF.row fun x => ‖x - s‖ ^ 2
  let M : ℝ^d → ℝ^d → ℝ := fun x c => ‖x - c‖ ^ 2
  have hcov : Covers M τ (J.disjSum P) R1 C1 := by
    intro x hx c hc
    have h0 := hzero x hx c hc
    simp only [B, mul_eq_zero, prod_eq_zero_iff] at h0
    rcases h0 with ⟨i, hi, hi0⟩ | ⟨s, hs, hs0⟩
    · exact ⟨Sum.inl i, inl_mem_disjSum.2 hi, by simp only [M, τ, TF.eval]; linarith⟩
    · exact ⟨Sum.inr s, inr_mem_disjSum.2 hs, by simp only [M, τ, TF.eval]; linarith⟩
  have hrankM : rankOn M R1 C1 ≤ D + 2 := by
    unfold rankOn
    have := rank_sqdist_le_affine X D hD (fun x : R1 => (x : ℝ^d)) (fun c : C1 => (c : ℝ^d))
      (fun x => hR0 (hR1 x.2)) (fun c => hC0 (hC1 c.2)) (fun _ => 0) (fun _ => 0)
    have e : (Matrix.of fun (x : R1) (c : C1) => M x c) =
        Matrix.of fun (x : R1) (c : C1) => ‖(x : ℝ^d) - c‖ ^ 2 - 0 - 0 := by
      ext; simp [M]
    rw [e]; exact this
  obtain ⟨R2, hR2, C2, hC2, t₀, -, e1, e2, hM⟩ :=
    theoremLR M τ (D + 2) (kstar n) (J.disjSum P) R1 C1 (by rw [card_disjSum]; exact hk)
      hR1ne hC1ne hrankM hcov
  have hortho : ∀ x ∈ R2, ∀ x' ∈ R2, ∀ c ∈ C2, ∀ c' ∈ C2, inner ℝ (x - x') (c - c') = 0 := by
    rcases t₀ with i | s
    · refine ortho_of_equidistant R2 C2 (fun c => Real.sqrt (colF i c)) fun x hx c hc => ?_
      have := hM x hx c hc
      simp only [M, τ, TF.eval] at this
      rw [← this, Real.sqrt_sq (norm_nonneg _)]
    · refine ortho_of_bisector R2 C2 s fun x hx c hc => ?_
      have := hM x hx c hc
      simp only [M, τ, TF.eval] at this
      exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this).symm
  have hRC : affDim (R2 ∪ C2) ≤ D :=
    (affDim_mono (union_subset ((hR2.trans hR1).trans hR0) ((hC2.trans hC1).trans hC0))).trans hD
  have hmin := min_affDim_le_of_ortho R2 C2 D hRC hortho
  have hc1r : (R0.card : ℝ) ≤ 2 * R1.card := by exact_mod_cast c1
  have hc2r : (C0.card : ℝ) ≤ 2 * C1.card := by exact_mod_cast c2
  rcases le_total (affDim R2) (affDim C2) with hle | hle
  · rw [min_eq_left hle] at hmin
    have hR := hh R2 ((hR2.trans hR1).trans hR0) hmin
    have : (R2.card : ℝ) ≤ h := by exact_mod_cast hR
    have : (R0.card : ℝ) ≤ 2 * LRc * h := by
      calc (R0.card : ℝ) ≤ 2 * R1.card := hc1r
        _ ≤ 2 * (LRc * R2.card) := by linarith
        _ ≤ 2 * LRc * h := by nlinarith
    linarith
  · rw [min_eq_right hle] at hmin
    have hC := hh C2 ((hC2.trans hC1).trans hC0) hmin
    have : (C2.card : ℝ) ≤ h := by exact_mod_cast hC
    calc (C0.card : ℝ) ≤ 2 * C1.card := hc2r
      _ ≤ 2 * (LRc * C2.card) := by linarith
      _ ≤ 2 * LRc * h := by nlinarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem dists_insert_subset (S : Finset (ℝ^d)) (b : ℝ^d) :
    dists (insert b S) ⊆ dists S ∪ S.image (dist b) := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := mem_image.1 ht
  obtain ⟨h1, h2, h12⟩ := mem_offDiag.1 hp
  rcases mem_insert.1 h1 with e1 | e1 <;> rcases mem_insert.1 h2 with e2 | e2
  · exact absurd (e1.trans e2.symm) h12
  · exact mem_union_right _ (mem_image.2 ⟨p.2, e2, by rw [e1]⟩)
  · exact mem_union_right _ (mem_image.2 ⟨p.1, e1, by rw [e2, dist_comm]⟩)
  · exact mem_union_left _ (mem_image.2 ⟨p, mem_offDiag.2 ⟨e1, e2, h12⟩, rfl⟩)
theorem union_singleton_eq (S : Finset (ℝ^d)) (b : ℝ^d) : S ∪ {b} = insert b S := by
  rw [union_comm, ← insert_eq]
def Kp (n r p : ℕ) : ℕ := 12 * 6 ^ (n - 4 - r - p)
noncomputable def thInv (n D r p : ℕ) (Γ' : ℝ) : ℝ :=
  16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r p (Kp n r (p + 1))
noncomputable def McoreHat (n D r : ℕ) (Γ' : ℝ) : ℝ :=
  2 ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * ((D + 2 : ℕ) : ℝ) ^ (2 * kc n r)
noncomputable def MslHat (n D r p : ℕ) (Γ' : ℝ) : ℝ :=
  2 * n * (n + Kp n r (p + 1)) * thInv n D r p Γ'
noncomputable def mAux (n D r : ℕ) (Γ' : ℝ) : ℕ → ℝ
  | 0 => McoreHat n D r Γ'
  | j + 1 => max (MslHat n D r (n - 4 - r - (j + 1)) Γ')
      (2 * thInv n D r (n - 4 - r - (j + 1)) Γ' * mAux n D r Γ' j)
noncomputable def mHat (n D r : ℕ) (Γ' : ℝ) (p : ℕ) : ℝ := mAux n D r Γ' (n - 4 - r - p)
noncomputable def ratioE1 (n D r : ℕ) (Γ' : ℝ) : ℝ := 2 * mHat n D r Γ' 1 + 2 * n * (n + Kr n r)
theorem mHat_top (n D r : ℕ) (Γ' : ℝ) : mHat n D r Γ' (n - 4 - r) = McoreHat n D r Γ' := by
  simp [mHat, mAux]
theorem mHat_step (n D r p : ℕ) (Γ' : ℝ) (hp : p < n - 4 - r) :
    mHat n D r Γ' p = max (MslHat n D r p Γ') (2 * thInv n D r p Γ' * mHat n D r Γ' (p + 1)) := by
  unfold mHat
  obtain ⟨j, hj⟩ : ∃ j, n - 4 - r - p = j + 1 := ⟨n - 4 - r - p - 1, by omega⟩
  rw [hj, mAux]
  have h1 : n - 4 - r - (j + 1) = p := by omega
  have h2 : n - 4 - r - (p + 1) = j := by omega
  rw [h1, h2]
theorem mAux_nonneg (n D r : ℕ) (Γ' : ℝ) (hΓ : 1 ≤ Γ') : ∀ j, 0 ≤ mAux n D r Γ' j := by
  intro j
  induction j with
  | zero => simp only [mAux, McoreHat]; positivity
  | succ j ih =>
    simp only [mAux]
    exact le_max_of_le_right (mul_nonneg (by unfold thInv; positivity) ih)
theorem initial_family (X S W : Finset (ℝ^d)) (r : ℕ) (σ τ : ℝ) (hc : Config X S W r σ)
    (hσ : 0 < σ) (b : ℝ^d) (hb : b ∈ W) (K : ℕ) (hK : K ≤ (Big S W b τ).card)
    (hτ : r * (r + K) * σ < τ) :
    ∃ (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ), RainbowFamily S W {b} (range K) C β ∧
      ∀ k ∈ range K, τ - r * (r + K) * σ ≤ (C k).card := by
  classical
  obtain ⟨I0, hI0, hI0c⟩ := exists_subset_card_eq hK
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hbS := hWS b hb
  let e := I0.equivFin
  let ρ : ℕ → ℝ := fun k => if h : k < K then (e.symm (Fin.cast hI0c.symm ⟨k, h⟩) : ℝ) else 0
  have hρmem : ∀ k ∈ range K, ρ k ∈ I0 := by
    intro k hk
    have hk' := mem_range.1 hk
    simp only [ρ, dif_pos hk']; exact coe_mem _
  have hρinj : ∀ k ∈ range K, ∀ k' ∈ range K, ρ k = ρ k' → k = k' := by
    intro k hk k' hk' h
    have h1 := mem_range.1 hk; have h2 := mem_range.1 hk'
    simp only [ρ, dif_pos h1, dif_pos h2] at h
    have := e.symm.injective (Subtype.ext h)
    simpa [Fin.ext_iff] using this
  have hBig : ∀ k ∈ range K, ρ k ∉ Rb S b ∧ τ ≤ ((W.filter fun x => dist x b = ρ k).card : ℝ) ∧
      0 < ρ k := by
    intro k hk
    have hm := hI0 (hρmem k hk)
    obtain ⟨himg, hR, hτk⟩ := mem_filter.1 hm
    refine ⟨hR, hτk, ?_⟩
    obtain ⟨x, hx, hxe⟩ := mem_image.1 himg
    rw [← hxe]; exact dist_pos.2 (ne_of_mem_erase hx)
  set T0 := S.image (dist b) ∪ I0 with hT0
  set Rem := S.biUnion fun s => W.filter fun x => dist x s ∈ T0 with hRem
  let C : ℕ → Finset (ℝ^d) := fun k => (W.filter fun x => dist x b = ρ k) \ Rem
  have hT0pos : ∀ t ∈ T0, 0 < t := by
    intro t ht
    rcases mem_union.1 ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := mem_image.1 ht
      exact dist_pos.2 fun h => hbS (h ▸ hs)
    · obtain ⟨himg, -, -⟩ := mem_filter.1 (hI0 ht)
      obtain ⟨x, hx, rfl⟩ := mem_image.1 himg
      exact dist_pos.2 (ne_of_mem_erase hx)
  have hRemc : (Rem.card : ℝ) ≤ r * (r + K) * σ := by
    have hsub : Rem ⊆ S.biUnion fun s => T0.biUnion fun t => W.filter fun x => dist x s = t := by
      intro x hx
      obtain ⟨s, hs, hx⟩ := mem_biUnion.1 hx
      obtain ⟨hxW, ht⟩ := mem_filter.1 hx
      exact mem_biUnion.2 ⟨s, hs, mem_biUnion.2 ⟨_, ht, mem_filter.2 ⟨hxW, rfl⟩⟩⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) ≤
        T0.card * σ := by
      intro s hs
      have := card_biUnion_le (s := T0) (t := fun t => W.filter fun x => dist x s = t)
      calc ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ)
          ≤ ∑ t ∈ T0, ((W.filter fun x => dist x s = t).card : ℝ) := by exact_mod_cast this
        _ ≤ ∑ _t ∈ T0, σ := sum_le_sum fun t ht => (hc.cap s hs t (hT0pos t ht)).le
        _ = T0.card * σ := by rw [sum_const, nsmul_eq_mul]
    have hT0c : (T0.card : ℝ) ≤ r + K := by
      have := card_union_le (S.image (dist b)) I0
      rw [← hT0] at this
      have h3 := card_image_le (s := S) (f := dist b)
      rw [hc.card] at h3
      have : T0.card ≤ r + K := by omega
      exact_mod_cast this
    calc (Rem.card : ℝ) ≤ ∑ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ _s ∈ S, (T0.card * σ) := sum_le_sum h2
      _ = r * (T0.card * σ) := by rw [sum_const, nsmul_eq_mul, hc.card]
      _ ≤ r * ((r + K) * σ) := by gcongr
      _ = r * (r + K) * σ := by ring
  have hCcard : ∀ k ∈ range K, τ - r * (r + K) * σ ≤ (C k).card := by
    intro k hk
    have h1 := card_le_card_sdiff_add_card (s := W.filter fun x => dist x b = ρ k) (t := Rem)
    have h2 : (((W.filter fun x => dist x b = ρ k).card : ℕ) : ℝ) ≤ (C k).card + Rem.card := by
      exact_mod_cast h1
    have := (hBig k hk).2.1
    linarith
  refine ⟨C, fun k _ => ρ k, ⟨singleton_nonempty b, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩, hCcard⟩
  · exact disjoint_singleton_right.2 hbS
  · rw [union_singleton_eq]; exact hc.ext b hb
  · intro k hk
    refine ⟨?_, fun x hx => (mem_filter.1 (mem_sdiff.1 hx).1).1⟩
    rw [← card_pos]
    have h := hCcard k hk
    have : (0 : ℝ) < (C k).card := by linarith
    exact_mod_cast this
  · intro k hk x hx b' hb'
    rw [mem_singleton] at hb'; subst hb'
    exact (mem_filter.1 (mem_sdiff.1 hx).1).2
  · intro k hk k' hk' b1 hb1 b2 hb2 h
    rw [mem_singleton] at hb1 hb2; subst hb1; subst hb2
    exact ⟨hρinj k hk k' hk' h, rfl⟩
  · intro k hk b' hb' hmem
    rw [mem_singleton] at hb'; subst hb'
    rw [union_singleton_eq] at hmem
    exact (hBig k hk).1 (dists_insert_subset S b' hmem)
  · intro k hk x hx
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    obtain ⟨hxW, hxb⟩ := mem_filter.1 hxf
    have hxb' : x ≠ b := by
      rintro rfl; rw [dist_self] at hxb; exact absurd hxb (hBig k hk).2.2.ne
    refine ⟨?_, ?_⟩
    · rw [union_singleton_eq]
      intro hmem
      rcases mem_insert.1 hmem with h | h
      · exact hxb' h
      · exact hWS x hxW h
    · rw [union_singleton_eq]
      have hnot : ∀ s ∈ S, dist x s ∉ T0 := fun s hs ht =>
        hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hxW, ht⟩⟩)
      refine rainbow_insert_insert S b x (hc.ext b hb) (hc.ext x hxW) ?_ ?_ ?_ ?_
      · intro s hs s' hs' h
        exact hnot s hs (mem_union_left _ (mem_image.2 ⟨s', hs', h.symm⟩))
      · intro s hs h
        rw [hxb] at h
        exact (hBig k hk).1 (mem_union_right _ (mem_image.2 ⟨s, hs, h.symm⟩))
      · intro s hs h
        rw [hxb] at h
        exact hnot s hs (mem_union_right _ (h ▸ hρmem k hk))
      · intro s hs s' hs' hne h
        rw [hxb] at h
        exact (hBig k hk).1 (mem_union_left _ (h ▸ mem_dists hs hs' hne))
  · intro k hk x hx s hs k' hk' b' hb' h
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    exact hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(mem_filter.1 hxf).1,
      mem_union_right _ (h ▸ hρmem k' hk')⟩⟩)
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem conflict_free (I1 : Finset ℕ) (K : ℕ) (hI1 : I1.card = 3 * K) (lam : ℕ → ℝ)
    (lab : ℕ → Finset ℝ) (hout : ∀ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ lam k ∈ lab k').card ≤ 1) :
    ∃ I' ⊆ I1, I'.card = K ∧ ∀ k ∈ I', ∀ k' ∈ I', k ≠ k' → lam k ∉ lab k' := by
  classical
  let R : ℕ → ℕ → Prop := fun k k' => lam k ∈ lab k'
  let G : SimpleGraph ℕ := SimpleGraph.fromRel R
  obtain ⟨T, hTI, hind, hcw⟩ := caro_wei G I1
  have hdeg : ∀ k ∈ I1, degIn G I1 k ≤ (I1.filter fun k' => k' ≠ k ∧ R k k').card +
      (I1.filter fun k' => k' ≠ k ∧ R k' k).card := by
    intro k _
    unfold degIn
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro k' hk'
    obtain ⟨hk'I, hadj⟩ := mem_filter.1 hk'
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hk'I, hadj.1.symm, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hk'I, hadj.1.symm, h⟩)
  have hsum2 : ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k' k).card ≤ I1.card := by
    have : ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k' k).card =
        ∑ k' ∈ I1, (I1.filter fun k => k' ≠ k ∧ R k' k).card := by
      simp only [card_filter]; exact Finset.sum_comm
    rw [this]
    calc ∑ k' ∈ I1, (I1.filter fun k => k' ≠ k ∧ R k' k).card
        ≤ ∑ _k' ∈ I1, 1 := sum_le_sum fun k' hk' => by
          have := hout k' hk'
          refine le_trans (card_le_card fun k hk => ?_) this
          obtain ⟨hkI, hne, hR⟩ := mem_filter.1 hk
          exact mem_filter.2 ⟨hkI, Ne.symm hne, hR⟩
      _ = I1.card := by simp
  have hsum : ∑ k ∈ I1, ((degIn G I1 k : ℝ) + 1) ≤ 3 * I1.card := by
    have h1 : ∑ k ∈ I1, degIn G I1 k ≤ 2 * I1.card := by
      calc ∑ k ∈ I1, degIn G I1 k
          ≤ ∑ k ∈ I1, ((I1.filter fun k' => k' ≠ k ∧ R k k').card +
              (I1.filter fun k' => k' ≠ k ∧ R k' k).card) := sum_le_sum hdeg
        _ = ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k k').card +
            ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k' k).card := sum_add_distrib
        _ ≤ I1.card + I1.card := by
            refine Nat.add_le_add ?_ hsum2
            calc ∑ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ R k k').card
                ≤ ∑ _k ∈ I1, 1 := sum_le_sum hout
              _ = I1.card := by simp
        _ = 2 * I1.card := by ring
    have h2 : (∑ k ∈ I1, degIn G I1 k : ℝ) ≤ 2 * I1.card := by exact_mod_cast h1
    rw [sum_add_distrib]; push_cast at h2 ⊢
    simp only [sum_const, nsmul_eq_mul, mul_one]
    linarith
  have hT : K ≤ T.card := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · omega
    have hIpos : (0 : ℝ) < I1.card := by rw [hI1]; push_cast; positivity
    have h1 : ((I1.card : ℝ)) ^ 2 ≤ T.card * (3 * I1.card) :=
      hcw.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    have h2 : (I1.card : ℝ) ≤ 3 * T.card := by nlinarith
    have h3 : (3 * K : ℝ) ≤ 3 * T.card := by rw [hI1] at h2; push_cast at h2; exact h2
    have : (K : ℝ) ≤ T.card := by linarith
    exact_mod_cast this
  obtain ⟨I', hI'T, hI'c⟩ := exists_subset_card_eq hT
  refine ⟨I', hI'T.trans hTI, hI'c, fun k hk k' hk' hne hR => ?_⟩
  exact hind (hI'T hk) (hI'T hk') hne ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl hR⟩)
theorem family_classes_disjoint {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {k k' : ℕ} (hk : k ∈ I) (hk' : k' ∈ I)
    (hne : k ≠ k') {x : ℝ^d} (hx : x ∈ C k) : x ∉ C k' := by
  intro hx'
  obtain ⟨b, hb⟩ := hF.Bne
  have h1 := hF.F2 k hk x hx b hb
  have h2 := hF.F2 k' hk' x hx' b hb
  exact hne (hF.F3.1 k hk k' hk' b hb b hb (h1.symm.trans h2)).1
theorem removal_bound {X S W : Finset (ℝ^d)} {r : ℕ} {σ : ℝ} (hc : Config X S W r σ)
    (T0 : Finset ℝ) (hT0 : ∀ t ∈ T0, 0 < t) :
    ((S.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ) ≤ r * (T0.card * σ) := by
  classical
  have hsub : (S.biUnion fun s => W.filter fun x => dist x s ∈ T0) ⊆
      S.biUnion fun s => T0.biUnion fun t => W.filter fun x => dist x s = t := by
    intro x hx
    obtain ⟨s, hs, hx⟩ := mem_biUnion.1 hx
    obtain ⟨hxW, ht⟩ := mem_filter.1 hx
    exact mem_biUnion.2 ⟨s, hs, mem_biUnion.2 ⟨_, ht, mem_filter.2 ⟨hxW, rfl⟩⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∀ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) ≤
      T0.card * σ := by
    intro s hs
    have := card_biUnion_le (s := T0) (t := fun t => W.filter fun x => dist x s = t)
    calc ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ)
        ≤ ∑ t ∈ T0, ((W.filter fun x => dist x s = t).card : ℝ) := by exact_mod_cast this
      _ ≤ ∑ _t ∈ T0, σ := sum_le_sum fun t ht => (hc.cap s hs t (hT0 t ht)).le
      _ = T0.card * σ := by rw [sum_const, nsmul_eq_mul]
  calc ((S.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ)
      ≤ ∑ s ∈ S, ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ _s ∈ S, (T0.card * σ) := sum_le_sum h2
    _ = r * (T0.card * σ) := by rw [sum_const, nsmul_eq_mul, hc.card]
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem union_insert_eq (S B : Finset (ℝ^d)) (c : ℝ^d) : S ∪ insert c B = insert c (S ∪ B) := by
  ext x; simp only [mem_union, mem_insert]; tauto
theorem new_family (X S W B : Finset (ℝ^d)) (r : ℕ) (σ : ℝ) (hc : Config X S W r σ)
    (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (hF : RainbowFamily S W B I C β)
    (π : ℕ) (hπ : π ∈ I) (c : ℝ^d) (hcπ : c ∈ C π) (I' : Finset ℕ) (hI' : I' ⊆ I.erase π)
    (lam : ℕ → ℝ) (hinj : ∀ k ∈ I', ∀ k' ∈ I', lam k = lam k' → k = k')
    (hΦ : ∀ k ∈ I', lam k ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c))
    (hβk : ∀ k ∈ I', lam k ∉ B.image (β k))
    (hindep : ∀ k ∈ I', ∀ k' ∈ I', k ≠ k' → lam k ∉ B.image (β k'))
    (hpos : ∀ k ∈ I', 0 < lam k)
    (hlarge : ∀ k ∈ I', (r : ℝ) * (r + I'.card) * σ <
      ((C k).filter fun x => dist x c = lam k).card) :
    ∃ (C' : ℕ → Finset (ℝ^d)) (β' : ℕ → ℝ^d → ℝ), RainbowFamily S W (insert c B) I' C' β' ∧
      (∀ k ∈ I', C' k ⊆ C k) ∧ ∀ k ∈ I',
        (((C k).filter fun x => dist x c = lam k).card : ℝ) - r * (r + I'.card) * σ ≤ (C' k).card := by
  classical
  have hI'I : ∀ k ∈ I', k ∈ I := fun k hk => (mem_erase.1 (hI' hk)).2
  have hI'π : ∀ k ∈ I', k ≠ π := fun k hk => (mem_erase.1 (hI' hk)).1
  obtain ⟨hcSB, hcR⟩ := hF.F4 π hπ c hcπ
  have hcS : c ∉ S := fun h => hcSB (mem_union_left _ h)
  have hcB : c ∉ B := fun h => hcSB (mem_union_right _ h)
  set T0 := S.image (dist c) ∪ I'.image lam with hT0
  set Rem := S.biUnion fun s => W.filter fun x => dist x s ∈ T0 with hRem
  let C' : ℕ → Finset (ℝ^d) := fun k => ((C k).filter fun x => dist x c = lam k) \ Rem
  let β' : ℕ → ℝ^d → ℝ := fun k b => if b = c then lam k else β k b
  have hT0pos : ∀ t ∈ T0, 0 < t := by
    intro t ht
    rcases mem_union.1 ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := mem_image.1 ht; exact dist_pos.2 fun h => hcS (h ▸ hs)
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 ht; exact hpos k hk
  have hT0c : (T0.card : ℝ) ≤ r + I'.card := by
    have h1 := card_union_le (S.image (dist c)) (I'.image lam)
    have h2 := card_image_le (s := S) (f := dist c)
    have h3 := card_image_le (s := I') (f := lam)
    rw [hc.card] at h2
    have : T0.card ≤ r + I'.card := by rw [hT0]; omega
    exact_mod_cast this
  have hRemc : (Rem.card : ℝ) ≤ r * (r + I'.card) * σ := by
    by_cases hS : S.Nonempty
    · obtain ⟨s, hs⟩ := hS
      have hσ0 : 0 ≤ σ := le_trans (Nat.cast_nonneg _) (hc.cap s hs 1 one_pos).le
      calc (Rem.card : ℝ) ≤ r * (T0.card * σ) := removal_bound hc T0 hT0pos
        _ ≤ r * ((r + I'.card) * σ) := by gcongr
        _ = r * (r + I'.card) * σ := by ring
    · have hSe : S = ∅ := not_nonempty_iff_eq_empty.1 hS
      have hr0 : r = 0 := by have := hc.card; rw [hSe, card_empty] at this; omega
      have : Rem = ∅ := by rw [hRem, hSe, biUnion_empty]
      rw [this, card_empty, hr0]; simp
  have hC'card : ∀ k ∈ I', (((C k).filter fun x => dist x c = lam k).card : ℝ) -
      r * (r + I'.card) * σ ≤ (C' k).card := by
    intro k _
    have h1 := card_le_card_sdiff_add_card (s := (C k).filter fun x => dist x c = lam k) (t := Rem)
    have h2 : ((((C k).filter fun x => dist x c = lam k).card : ℕ) : ℝ) ≤ (C' k).card + Rem.card := by
      exact_mod_cast h1
    linarith
  have hcdist : ∀ y ∈ S ∪ B, dist c y ∈ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) := by
    intro y hy
    rcases mem_union.1 hy with hy | hy
    · exact mem_union_right _ (mem_image.2 ⟨y, hy, rfl⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_image.2 ⟨y, hy, (hF.F2 π hπ c hcπ y hy).symm⟩))
  have hβπ : ∀ k ∈ I', ∀ b ∈ B, ∀ b' ∈ B, β k b ≠ β π b' := fun k hk b hb b' hb' h =>
    hI'π k hk (hF.F3.1 k (hI'I k hk) π hπ b hb b' hb' h).1
  refine ⟨C', β', ⟨insert_nonempty _ _, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩,
    fun k _ x hx => (mem_filter.1 (mem_sdiff.1 hx).1).1, hC'card⟩
  ·
    rw [disjoint_insert_right]; exact ⟨hcS, hF.F1.1⟩
  · rw [union_insert_eq]; exact hcR
  ·
    intro k hk
    refine ⟨?_, fun x hx => (hF.Cne k (hI'I k hk)).2 (mem_filter.1 (mem_sdiff.1 hx).1).1⟩
    rw [← card_pos]
    have := hC'card k hk; have := hlarge k hk
    have : (0 : ℝ) < (C' k).card := by linarith
    exact_mod_cast this
  ·
    intro k hk x hx b hb
    obtain ⟨hxf, -⟩ := mem_sdiff.1 hx
    obtain ⟨hxC, hxc⟩ := mem_filter.1 hxf
    rcases mem_insert.1 hb with hbc | hb
    · simp only [β', if_pos hbc]; rw [hbc]; exact hxc
    · have hbc : b ≠ c := fun h => hcB (h ▸ hb)
      simp only [β', if_neg hbc]; exact hF.F2 k (hI'I k hk) x hxC b hb
  ·
    intro k hk k' hk' b hb b' hb' h
    rcases mem_insert.1 hb with hbc | hb <;> rcases mem_insert.1 hb' with hb'c | hb'
    · simp only [β', if_pos hbc, if_pos hb'c] at h
      exact ⟨hinj k hk k' hk' h, hbc.trans hb'c.symm⟩
    · have hb'ne : b' ≠ c := fun e => hcB (e ▸ hb')
      simp only [β', if_pos hbc, if_neg hb'ne] at h
      by_cases hkk : k = k'
      · subst hkk; exact absurd (mem_image.2 ⟨b', hb', h.symm⟩) (hβk k hk)
      · exact absurd (mem_image.2 ⟨b', hb', h.symm⟩) (hindep k hk k' hk' hkk)
    · have hbne : b ≠ c := fun e => hcB (e ▸ hb)
      simp only [β', if_pos hb'c, if_neg hbne] at h
      by_cases hkk : k' = k
      · subst hkk; exact absurd (mem_image.2 ⟨b, hb, h⟩) (hβk k' hk')
      · exact absurd (mem_image.2 ⟨b, hb, h⟩) (hindep k' hk' k hk hkk)
    · have hbc : b ≠ c := fun e => hcB (e ▸ hb)
      have hb'c : b' ≠ c := fun e => hcB (e ▸ hb')
      simp only [β', if_neg hbc, if_neg hb'c] at h
      exact hF.F3.1 k (hI'I k hk) k' (hI'I k' hk') b hb b' hb' h
  ·
    intro k hk b hb hmem
    rw [union_insert_eq] at hmem
    have hmem' := dists_insert_subset (S ∪ B) c hmem
    rcases mem_insert.1 hb with hbc | hb
    · simp only [β', if_pos hbc] at hmem'
      rcases mem_union.1 hmem' with h | h
      · exact hΦ k hk (mem_union_left _ (mem_union_left _ h))
      · obtain ⟨y, hy, hye⟩ := mem_image.1 h
        exact hΦ k hk (hye ▸ hcdist y hy)
    · have hbc : b ≠ c := fun e => hcB (e ▸ hb)
      simp only [β', if_neg hbc] at hmem'
      rcases mem_union.1 hmem' with h | h
      · exact hF.F3.2 k (hI'I k hk) b hb h
      · obtain ⟨y, hy, hye⟩ := mem_image.1 h
        rcases mem_union.1 hy with hy | hy
        · exact hF.F5 π hπ c hcπ y hy k (hI'I k hk) b hb hye
        · rw [hF.F2 π hπ c hcπ y hy] at hye
          exact hβπ k hk b hb y hy hye.symm
  ·
    intro k hk x hx
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    obtain ⟨hxC, hxc⟩ := mem_filter.1 hxf
    obtain ⟨hxSB, hxRb⟩ := hF.F4 k (hI'I k hk) x hxC
    have hxcne : x ≠ c := fun e =>
      family_classes_disjoint hF (hI'I k hk) hπ (hI'π k hk) hxC (e ▸ hcπ)
    have hnot : ∀ s ∈ S, dist x s ∉ T0 := fun s hs ht =>
      hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF.Cne k (hI'I k hk)).2 hxC, ht⟩⟩)
    refine ⟨?_, ?_⟩
    · rw [union_insert_eq]
      intro hmem
      rcases mem_insert.1 hmem with h | h
      · exact hxcne h
      · exact hxSB h
    · rw [union_insert_eq]
      refine rainbow_insert_insert (S ∪ B) c x hcR hxRb ?_ ?_ ?_ ?_
      · intro y hy y' hy' h
        rcases mem_union.1 hy with hy | hy <;> rcases mem_union.1 hy' with hy' | hy'
        · exact hnot y hy (mem_union_left _ (mem_image.2 ⟨y', hy', h.symm⟩))
        · rw [hF.F2 π hπ c hcπ y' hy'] at h
          exact hF.F5 k (hI'I k hk) x hxC y hy π hπ y' hy' h
        · rw [hF.F2 k (hI'I k hk) x hxC y hy] at h
          exact hF.F5 π hπ c hcπ y' hy' k (hI'I k hk) y hy h.symm
        · rw [hF.F2 k (hI'I k hk) x hxC y hy, hF.F2 π hπ c hcπ y' hy'] at h
          exact hβπ k hk y hy y' hy' h
      · intro y hy h
        rw [hxc] at h
        exact hΦ k hk (h ▸ hcdist y hy)
      · intro y hy h
        rw [hxc] at h
        rcases mem_union.1 hy with hy | hy
        · exact hnot y hy (mem_union_right _ (mem_image.2 ⟨k, hk, h⟩))
        · rw [hF.F2 k (hI'I k hk) x hxC y hy] at h
          exact hβk k hk (mem_image.2 ⟨y, hy, h.symm⟩)
      · intro y hy y' hy' hne h
        rw [hxc] at h
        exact hΦ k hk (mem_union_left _ (mem_union_left _ (h ▸ mem_dists hy hy' hne)))
  ·
    intro k hk x hx s hs k' hk' b hb
    obtain ⟨hxf, hxR⟩ := mem_sdiff.1 hx
    obtain ⟨hxC, -⟩ := mem_filter.1 hxf
    rcases mem_insert.1 hb with hbc | hb
    · simp only [β', if_pos hbc]
      intro h
      exact hxR (mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF.Cne k (hI'I k hk)).2 hxC,
        mem_union_right _ (mem_image.2 ⟨k', hk', h.symm⟩)⟩⟩)
    · have hbc : b ≠ c := fun e => hcB (e ▸ hb)
      simp only [β', if_neg hbc]
      exact hF.F5 k (hI'I k hk) x hxC s hs k' (hI'I k' hk') b hb
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem dists_mono {A A' : Finset (ℝ^d)} (h : A ⊆ A') : dists A ⊆ dists A' :=
  image_subset_image (offDiag_mono h)
noncomputable def slNbr (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (π : ℕ) (θinv : ℝ) (c : ℝ^d) (k : ℕ) : Finset ℝ :=
  ((C k).image fun x => dist x c).filter fun l =>
    l ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) ∧ l ∉ B.image (β k) ∧
      ((C k).card : ℝ) ≤ θinv * ((C k).filter fun x => dist x c = l).card
def IsSlMatch (L : Finset ℕ) (N : ℕ → Finset ℝ) (Mt : Finset (ℕ × ℝ)) : Prop :=
  (∀ q ∈ Mt, q.1 ∈ L ∧ q.2 ∈ N q.1) ∧ (∀ q ∈ Mt, ∀ q' ∈ Mt, q.1 = q'.1 ∨ q.2 = q'.2 → q = q')
noncomputable def slBad (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (π : ℕ) (θinv : ℝ) (L : Finset ℕ) (K : ℕ) : Finset (ℝ^d) := by
  classical
  exact (C π).filter fun c => ∀ Mt, IsSlMatch L (slNbr S B C β π θinv c) Mt → Mt.card < 3 * K
theorem mem_slBad {S B : Finset (ℝ^d)} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    {π : ℕ} {θinv : ℝ} {L : Finset ℕ} {K : ℕ} {c : ℝ^d} :
    c ∈ slBad S B C β π θinv L K ↔
      c ∈ C π ∧ ∀ Mt, IsSlMatch L (slNbr S B C β π θinv c) Mt → Mt.card < 3 * K := by
  unfold slBad; simp only [mem_filter]
set_option maxHeartbeats 4000000 in
theorem bad_centres (n : ℕ) (d D h r K : ℕ) (X : Finset (ℝ^d)) (hX : Ambient n D h X)
    (S W : Finset (ℝ^d)) (σ Γ' : ℝ) (hc : Config X S W r σ) (hσ : smin n D h ≤ σ)
    (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ') (B : Finset (ℝ^d)) (I : Finset ℕ)
    (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (hF : RainbowFamily S W B I C β)
    (hI : 6 * K ≤ I.card) (hK : 1 ≤ K) (hk : ksl r B.card K ≤ kstar n) (M : ℝ)
    (hMk : ∀ k ∈ I, M ≤ (C k).card)
    (hMsl : 2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) ≤ M)
    (π : ℕ) (hπ : π ∈ I) :
    ((slBad S B C β π (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) (I.erase π) K).card : ℝ) ≤
      4 * LRcost (kstar n) (D + 2) * h := by
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast (show 1 ≤ D + 2 by omega)
  set θinv := 16 * Γ' * a ^ ksl r B.card K with hθdef
  have hθ16 : 16 ≤ θinv := by
    have : 1 ≤ a ^ ksl r B.card K := one_le_pow₀ ha1
    rw [hθdef]; nlinarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  set LRc := LRcost (kstar n) (D + 2) with hLRc
  have hLR1 : 1 ≤ LRc := one_le_LRcost _ _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ 2 * n * (n + K) := by positivity
  have hnK : (1 : ℝ) ≤ 2 * n * (n + K) := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    rcases Nat.eq_zero_or_pos n with hn | hn
    ·
      exfalso
      subst hn; unfold ksl kstar at hk; simp at hk; omega
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  have hMσ : θinv * (2 * n * (n + K) * σ) ≤ M := by
    have e : θinv * (2 * n * (n + K) * σ) =
        2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) := by
      rw [hθdef, ha]; ring
    rw [e]; exact hMsl
  have hsmin : 2 * LRc * h < smin n D h := by
    unfold smin
    have h4 : (4 : ℝ) ≤ 4 ^ (n + 1) := by
      calc (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : 4 * LRc * (h + 1) ≤ 4 ^ (n + 1) * LRc * (h + 1) := by gcongr
    nlinarith
  set L := I.erase π with hL
  set N := slNbr S B C β π θinv with hN
  set Zbad := slBad S B C β π θinv L K with hZbad
  have hcovK : ∀ c ∈ Zbad, ∃ A ⊆ L, ∃ Λ0 : Finset ℝ, (∀ k ∈ L, k ∉ A → N c k ⊆ Λ0) ∧
      A.card + Λ0.card < 3 * K := fun c hc =>
    konig_cover L (N c) (3 * K) (fun Mt h1 h2 => (mem_slBad.1 hc).2 Mt ⟨h1, h2⟩)
  choose! A hAL Λ0 hcover hsize using hcovK
  set Zk : ℕ → Finset (ℝ^d) := fun k => Zbad.filter fun c => k ∉ A c with hZk
  have hLc : 6 * K - 1 ≤ L.card := by rw [hL, card_erase_of_mem hπ]; omega
  have hLne : L.Nonempty := by rw [← card_pos]; omega
  obtain ⟨kst, hkst, hmax⟩ := exists_max_image L (fun k => (Zk k).card) hLne
  have havg : Zbad.card ≤ 2 * (Zk kst).card := by
    have h1 : ∑ k ∈ L, (Zk k).card = ∑ c ∈ Zbad, (L.filter fun k => k ∉ A c).card := by
      simp only [hZk, card_filter]; exact Finset.sum_comm
    have h2 : ∀ c ∈ Zbad, L.card - (3 * K - 1) ≤ (L.filter fun k => k ∉ A c).card := by
      intro c hc
      have e1 := card_filter_add_card_filter_not (s := L) (fun k => k ∉ A c)
      have e2 : (L.filter fun k => ¬ k ∉ A c).card ≤ (A c).card :=
        card_le_card fun k hk => by simpa using (mem_filter.1 hk).2
      have e3 := hsize c hc
      have e4 : (L.filter fun k => ¬ k ∉ A c).card ≤ 3 * K - 1 := by omega
      omega
    have h3 : Zbad.card * (L.card - (3 * K - 1)) ≤ L.card * (Zk kst).card := by
      calc Zbad.card * (L.card - (3 * K - 1)) = ∑ _c ∈ Zbad, (L.card - (3 * K - 1)) := by
            rw [sum_const, smul_eq_mul]
        _ ≤ ∑ c ∈ Zbad, (L.filter fun k => k ∉ A c).card := sum_le_sum h2
        _ = ∑ k ∈ L, (Zk k).card := h1.symm
        _ ≤ ∑ _k ∈ L, (Zk kst).card := sum_le_sum hmax
        _ = L.card * (Zk kst).card := by rw [sum_const, smul_eq_mul]
    have h4 : L.card ≤ 2 * (L.card - (3 * K - 1)) := by omega
    have hLpos : 0 < L.card := card_pos.2 hLne
    have : L.card * Zbad.card ≤ L.card * (2 * (Zk kst).card) := by
      calc L.card * Zbad.card ≤ 2 * (L.card - (3 * K - 1)) * Zbad.card :=
            Nat.mul_le_mul_right _ h4
        _ = 2 * (Zbad.card * (L.card - (3 * K - 1))) := by ring
        _ ≤ 2 * (L.card * (Zk kst).card) := Nat.mul_le_mul_left _ h3
        _ = L.card * (2 * (Zk kst).card) := by ring
    exact Nat.le_of_mul_le_mul_left this hLpos
  have hkstI : kst ∈ I := (mem_erase.1 hkst).2
  have hkstπ : kst ≠ π := (mem_erase.1 hkst).1
  have hCkW : C kst ⊆ W := (hF.Cne kst hkstI).2
  have hCπW : C π ⊆ W := (hF.Cne π hπ).2
  set Cst : Finset ℝ := dists (S ∪ B) ∪ B.image (β π) ∪ B.image (β kst) with hCst
  let ι := Fin (3 * K - 1) ⊕ (ℝ ⊕ ℝ^d)
  let lam0 : ℝ^d → Fin (3 * K - 1) → ℝ := fun c i =>
    if hi : (i : ℕ) < (Λ0 c).card then ((Λ0 c).equivFin.symm ⟨i, hi⟩ : ℝ) else 0
  let colF : ι → ℝ^d → ℝ := fun t => match t with
    | Sum.inl i => fun c => lam0 c i ^ 2
    | Sum.inr (Sum.inl v) => fun _ => v ^ 2
    | Sum.inr (Sum.inr s) => fun c => dist c s ^ 2
  let J : Finset ι := (Finset.univ : Finset (Fin (3 * K - 1))).disjSum (Cst.disjSum S)
  have hSB : (S ∪ B).card = r + B.card := by
    rw [card_union_of_disjoint hF.F1.1, hc.card]
  have hJP : J.card + S.card ≤ ksl r B.card K := by
    have hJc : J.card = (3 * K - 1) + (Cst.card + S.card) := by
      simp only [J]; rw [card_disjSum, card_disjSum, card_univ, Fintype.card_fin]
    rw [hJc]
    have h1 : Cst.card ≤ (r + B.card).choose 2 + B.card + B.card := by
      rw [hCst]
      have e1 := card_union_le (dists (S ∪ B) ∪ B.image (β π)) (B.image (β kst))
      have e2 := card_union_le (dists (S ∪ B)) (B.image (β π))
      have e3 := card_dists_le (S ∪ B)
      have e4 := card_image_le (s := B) (f := β π)
      have e5 := card_image_le (s := B) (f := β kst)
      rw [hSB] at e3
      omega
    rw [hc.card]; unfold ksl; omega
  have hfew : ∀ c ∈ Zk kst, 16 * (D + 2) ^ (J.card + S.card) *
      ((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card ≤ (C kst).card := by
    intro c hcZ
    obtain ⟨hcZb, hcA⟩ := mem_filter.1 hcZ
    have hcπ : c ∈ C π := (mem_slBad.1 hcZb).1
    have hcW : c ∈ W := hCπW hcπ
    set θ : ℝ := (C kst).card / θinv with hθ
    have hθpos : 0 < θinv := by linarith
    have hθσ : σ ≤ θ := by
      rw [hθ, le_div_iff₀ hθpos]
      have := hMk kst hkstI
      nlinarith
    have hVsub : C kst ⊆ W.erase c := fun x hx => mem_erase.2 ⟨fun e =>
      family_classes_disjoint hF hkstI hπ hkstπ hx (e ▸ hcπ), hCkW hx⟩
    have hHRc := hHR c hcW (C kst) hVsub θ hθσ
    have hsub : ((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2) ⊆ hrSet S (C kst) c θ := by
      intro x hx
      obtain ⟨hxC, hJ, hP⟩ := mem_filter.1 hx
      have hxc : ‖x - c‖ = dist x c := (dist_eq_norm x c).symm
      have hnot : ∀ v : ℝ, ∀ i ∈ J, colF i c = v ^ 2 → dist x c ≠ v := by
        intro v i hi he hv
        exact hJ i hi (by rw [hxc, hv, he])
      have hΛ : dist x c ∉ Λ0 c := by
        intro hm
        set j := (Λ0 c).equivFin ⟨dist x c, hm⟩
        have hj : (j : ℕ) < 3 * K - 1 := by
          have := hsize c hcZb; have := j.2; omega
        refine hnot (dist x c) (Sum.inl ⟨j, hj⟩) (inl_mem_disjSum.2 (mem_univ _)) ?_ rfl
        simp only [colF, lam0, dif_pos j.2]
        simp [j]
      have hCstm : ∀ v ∈ Cst, dist x c ≠ v := fun v hv =>
        hnot v (Sum.inr (Sum.inl v)) (inr_mem_disjSum.2 (inl_mem_disjSum.2 hv)) rfl
      have hΦ : dist x c ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) := by
        intro hm
        rcases mem_union.1 hm with hm | hm
        · exact hCstm _ (mem_union_left _ hm) rfl
        · obtain ⟨s, hs, hse⟩ := mem_image.1 hm
          exact hnot (dist c s) (Sum.inr (Sum.inr s)) (inr_mem_disjSum.2 (inr_mem_disjSum.2 hs))
            rfl hse.symm
      have hβk : dist x c ∉ B.image (β kst) := fun hm => hCstm _ (mem_union_right _ hm) rfl
      have hbis : ∀ s ∈ S, dist x c ≠ dist x s := fun s hs h => hP s hs (by
        rw [hxc, h, dist_eq_norm])
      have hthr : θinv * ((C kst).filter fun y => dist y c = dist x c).card < (C kst).card := by
        by_contra hge
        push Not at hge
        have hmemN : dist x c ∈ N c kst := mem_filter.2 ⟨mem_image.2 ⟨x, hxC, rfl⟩, hΦ, hβk, hge⟩
        exact hΛ (hcover c hcZb kst hkst hcA hmemN)
      refine mem_filter.2 ⟨hxC, ?_, hbis, ?_⟩
      · intro hm
        rcases mem_union.1 hm with hm | hm
        · exact hΦ (mem_union_left _ (mem_union_left _ (dists_mono subset_union_left hm)))
        · exact hΦ (mem_union_right _ hm)
      · rw [hθ, lt_div_iff₀ hθpos]; linarith
    have h1 := card_le_card hsub
    have h2 : ((((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℕ) : ℝ) ≤ Γ' * θ :=
      (by exact_mod_cast h1 : _ ≤ ((hrSet S (C kst) c θ).card : ℝ)).trans hHRc
    have hpow : ((D + 2 : ℕ) : ℝ) ^ (J.card + S.card) ≤ a ^ ksl r B.card K :=
      pow_le_pow_right₀ ha1 hJP
    have : ((16 * (D + 2) ^ (J.card + S.card) * ((C kst).filter fun x =>
        (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧ ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℕ) : ℝ) ≤
        (C kst).card := by
      push_cast
      have e : Γ' * θ * (16 * a ^ ksl r B.card K) = (C kst).card := by
        rw [hθ, hθdef]; field_simp
      have h0 : (0 : ℝ) ≤ (((C kst).filter fun x => (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
        ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℝ) := Nat.cast_nonneg _
      have hpow' : ((D : ℝ) + 2) ^ (J.card + S.card) ≤ a ^ ksl r B.card K := by
        rw [ha] at hpow ⊢; push_cast at hpow ⊢; exact hpow
      calc 16 * ((D : ℝ) + 2) ^ (J.card + S.card) * (((C kst).filter fun x =>
            (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧ ∀ s ∈ S, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℝ)
          ≤ 16 * a ^ ksl r B.card K * (Γ' * θ) := by gcongr
        _ = (C kst).card := by rw [← e]; ring
    exact_mod_cast this
  have hbig : 2 * LRc * h < (C kst).card := by
    have h1 := hMk kst hkstI
    have e1 : 1 ≤ θinv * (2 * n * (n + K)) := by nlinarith
    have e2 : σ ≤ θinv * (2 * n * (n + K) * σ) := by nlinarith
    linarith
  have hZk := gl_lr_or n D h X hX.dim hX.half (C kst) (Zk kst) (hCkW.trans hc.subW)
    (fun c hc' => hc.subW (hCπW (mem_slBad.1 (mem_filter.1 hc').1).1)) J colF S
    (hJP.trans hk) hfew hbig
  have : (Zbad.card : ℝ) ≤ 2 * (Zk kst).card := by exact_mod_cast havg
  linarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
set_option maxHeartbeats 4000000 in
theorem slicing_lemma_proved (n : ℕ) (hn : 6 ≤ n) (d D h r K : ℕ) (hr : r ≤ n - 6) (hK : 1 ≤ K)
    (X : Finset (ℝ^d)) (hX : Ambient n D h X) (S W : Finset (ℝ^d)) (σ Γ' : ℝ)
    (hc : Config X S W r σ) (hσ : smin n D h ≤ σ) (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ')
    (B : Finset (ℝ^d)) (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (hF : RainbowFamily S W B I C β) (hB1 : 1 ≤ B.card) (hB2 : B.card ≤ n - 5 - r)
    (hI : 6 * K ≤ I.card) (hk : ksl r B.card K ≤ kstar n) (M : ℝ)
    (hMk : ∀ k ∈ I, M ≤ (C k).card)
    (hMsl : 2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) ≤ M) :
    ∃ c ∈ I.biUnion C, ∃ I' ⊆ I, I'.card = K ∧ ∃ (C' : ℕ → Finset (ℝ^d)) (β' : ℕ → ℝ^d → ℝ),
      (∀ k ∈ I', C' k ⊆ C k) ∧ RainbowFamily S W (insert c B) I' C' β' ∧
      ∀ k ∈ I', M / (2 * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K)) ≤ (C' k).card := by
  classical
  obtain ⟨π, hπ⟩ : I.Nonempty := by rw [← card_pos]; omega
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast (show 1 ≤ D + 2 by omega)
  set θinv := 16 * Γ' * a ^ ksl r B.card K with hθdef
  have hθ16 : 16 ≤ θinv := by
    have : 1 ≤ a ^ ksl r B.card K := one_le_pow₀ ha1
    rw [hθdef]; nlinarith
  have hθpos : 0 < θinv := by linarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hnK : (1 : ℝ) ≤ 2 * n * (n + K) := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have : (6 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hMσ : θinv * (2 * n * (n + K) * σ) ≤ M := by
    have e : θinv * (2 * n * (n + K) * σ) =
        2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) := by
      rw [hθdef, ha]; ring
    rw [e]; exact hMsl
  have hσM : σ ≤ M := by
    have e1 : 1 ≤ θinv * (2 * n * (n + K)) := by nlinarith
    nlinarith
  set LRc := LRcost (kstar n) (D + 2) with hLRc
  have hLR1 : 1 ≤ LRc := one_le_LRcost _ _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hsmin : 4 * LRc * h < smin n D h := by
    unfold smin
    have h4 : (16 : ℝ) ≤ 4 ^ (n + 1) := by
      calc (16 : ℝ) = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : 16 * LRc * (h + 1) ≤ 4 ^ (n + 1) * LRc * (h + 1) := by gcongr
    nlinarith
  have hbad := bad_centres n d D h r K X hX S W σ Γ' hc hσ hΓ' hHR B I C β hF hI hK hk M hMk
    hMsl π hπ
  rw [← ha, ← hθdef] at hbad
  set L := I.erase π with hL
  set N := slNbr S B C β π θinv with hN
  have hlt : (slBad S B C β π θinv L K).card < (C π).card := by
    have h1 := hMk π hπ
    have : ((slBad S B C β π θinv L K).card : ℝ) < (C π).card := by linarith
    exact_mod_cast this
  obtain ⟨c, hcπ, hcgood⟩ : ∃ c ∈ C π, c ∉ slBad S B C β π θinv L K := by
    by_contra hcon
    push Not at hcon
    exact absurd (card_le_card fun x hx => hcon x hx) (not_le.2 hlt)
  have hmatch : ¬ ∀ Mt, IsSlMatch L (N c) Mt → Mt.card < 3 * K :=
    fun hall => hcgood (mem_slBad.2 ⟨hcπ, hall⟩)
  push Not at hmatch
  obtain ⟨Mt, hMt, hMtc⟩ := hmatch
  obtain ⟨Mt', hMt'sub, hMt'c⟩ := exists_subset_card_eq hMtc
  have hMt'1 : ∀ q ∈ Mt', q.1 ∈ L ∧ q.2 ∈ N c q.1 := fun q hq => hMt.1 q (hMt'sub hq)
  have hMt'2 : ∀ q ∈ Mt', ∀ q' ∈ Mt', q.1 = q'.1 ∨ q.2 = q'.2 → q = q' :=
    fun q hq q' hq' => hMt.2 q (hMt'sub hq) q' (hMt'sub hq')
  set I1 := Mt'.image Prod.fst with hI1
  have hI1c : I1.card = 3 * K := by
    rw [hI1, card_image_of_injOn (fun q hq q' hq' h => hMt'2 q hq q' hq' (Or.inl h)), hMt'c]
  let lam : ℕ → ℝ := fun k => if hk : ∃ q ∈ Mt', q.1 = k then (Classical.choose hk).2 else 0
  have hlam : ∀ k ∈ I1, (k, lam k) ∈ Mt' := by
    intro k hk
    have hex : ∃ q ∈ Mt', q.1 = k := by
      obtain ⟨q, hq, hqk⟩ := mem_image.1 hk; exact ⟨q, hq, hqk⟩
    obtain ⟨hq, hqk⟩ := Classical.choose_spec hex
    simp only [lam, dif_pos hex]
    have : (k, (Classical.choose hex).2) = Classical.choose hex := by
      ext
      · exact hqk.symm
      · rfl
    rw [this]; exact hq
  have hlamN : ∀ k ∈ I1, k ∈ L ∧ lam k ∈ N c k := fun k hk => hMt'1 _ (hlam k hk)
  have hlaminj : ∀ k ∈ I1, ∀ k' ∈ I1, lam k = lam k' → k = k' := fun k hk k' hk' h =>
    (Prod.ext_iff.1 (hMt'2 _ (hlam k hk) _ (hlam k' hk') (Or.inr h))).1
  have hout : ∀ k ∈ I1, (I1.filter fun k' => k' ≠ k ∧ lam k ∈ B.image (β k')).card ≤ 1 := by
    intro k hk
    refine card_le_one.2 fun k1 hk1 k2 hk2 => ?_
    obtain ⟨hk1I, -, hm1⟩ := mem_filter.1 hk1
    obtain ⟨hk2I, -, hm2⟩ := mem_filter.1 hk2
    obtain ⟨b1, hb1, he1⟩ := mem_image.1 hm1
    obtain ⟨b2, hb2, he2⟩ := mem_image.1 hm2
    have hk1I' := (mem_erase.1 (hlamN k1 hk1I).1).2
    have hk2I' := (mem_erase.1 (hlamN k2 hk2I).1).2
    exact (hF.F3.1 k1 hk1I' k2 hk2I' b1 hb1 b2 hb2 (he1.trans he2.symm)).1
  obtain ⟨I', hI'I1, hI'c, hindep⟩ := conflict_free I1 K hI1c lam (fun k => B.image (β k)) hout
  have hI'L : I' ⊆ L := fun k hk => (hlamN k (hI'I1 hk)).1
  have hedge : ∀ k ∈ I', lam k ∈ (C k).image (fun x => dist x c) ∧
      lam k ∉ dists (S ∪ B) ∪ B.image (β π) ∪ S.image (dist c) ∧ lam k ∉ B.image (β k) ∧
      ((C k).card : ℝ) ≤ θinv * ((C k).filter fun x => dist x c = lam k).card := by
    intro k hk
    have := (hlamN k (hI'I1 hk)).2
    simp only [hN, slNbr, mem_filter] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  have hpos : ∀ k ∈ I', 0 < lam k := by
    intro k hk
    obtain ⟨x, hx, hxe⟩ := mem_image.1 (hedge k hk).1
    have hkI := (mem_erase.1 (hI'L hk)).2
    have hkπ := (mem_erase.1 (hI'L hk)).1
    rw [← hxe]
    exact dist_pos.2 fun e => family_classes_disjoint hF hkI hπ hkπ hx (e ▸ hcπ)
  have hrn : (r : ℝ) * (r + K) ≤ n * (n + K) := by
    have : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith
  have hfilt : ∀ k ∈ I', 2 * n * (n + K) * σ ≤ ((C k).filter fun x => dist x c = lam k).card := by
    intro k hk
    have h1 := (hedge k hk).2.2.2
    have h2 := hMk k ((mem_erase.1 (hI'L hk)).2)
    have : θinv * (2 * n * (n + K) * σ) ≤ θinv * ((C k).filter fun x => dist x c = lam k).card := by
      linarith
    exact le_of_mul_le_mul_left this hθpos
  have hn0 : (0 : ℝ) < n * (n + K) := by
    have : (6 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  obtain ⟨C', β', hF', hsub, hcard⟩ := new_family X S W B r σ hc I C β hF π hπ c hcπ I' hI'L
    lam (fun k hk k' hk' h => hlaminj k (hI'I1 hk) k' (hI'I1 hk') h)
    (fun k hk => (hedge k hk).2.1) (fun k hk => (hedge k hk).2.2.1)
    (fun k hk k' hk' hne => hindep k hk k' hk' hne) hpos
    (fun k hk => by
      have := hfilt k hk
      rw [hI'c]
      nlinarith)
  refine ⟨c, mem_biUnion.2 ⟨π, hπ, hcπ⟩, I', fun k hk => (mem_erase.1 (hI'L hk)).2, hI'c,
    C', β', hsub, hF', fun k hk => ?_⟩
  have h1 := hcard k hk
  rw [hI'c] at h1
  have h2 := (hedge k hk).2.2.2
  have h3 := hMk k ((mem_erase.1 (hI'L hk)).2)
  have hdiv : M / (2 * θinv) ≤ ((C k).filter fun x => dist x c = lam k).card - r * (r + K) * σ := by
    rw [div_le_iff₀ (by positivity)]
    set F : ℝ := (((C k).filter fun x => dist x c = lam k).card : ℝ) with hFdef
    have s1 : M ≤ θinv * F := h3.trans h2
    have s2 : θinv * (2 * ((r : ℝ) * (r + K)) * σ) ≤ θinv * (2 * n * (n + K) * σ) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hθpos.le
    have e : (F - r * (r + K) * σ) * (2 * θinv) =
        2 * (θinv * F) - θinv * (2 * ((r : ℝ) * (r + K)) * σ) := by ring
    rw [e]; linarith
  linarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem rainbow_insert_one (T : Finset (ℝ^d)) (x : ℝ^d) (hT : Rainbow T) (hxT : x ∉ T)
    (hinj : ∀ y ∈ T, ∀ y' ∈ T, dist x y = dist x y' → y = y')
    (hout : ∀ y ∈ T, dist x y ∉ dists T) : Rainbow (insert x T) := by
  intro a ha a' ha' c hc c' hc' hne hne' hd
  rcases mem_insert.1 ha with ea | ea <;> rcases mem_insert.1 ha' with ea' | ea' <;>
    rcases mem_insert.1 hc with ec | ec <;> rcases mem_insert.1 hc' with ec' | ec'
  all_goals first
    | exact absurd (ea.trans ea'.symm) hne
    | exact absurd (ec.trans ec'.symm) hne'
    | skip
  · rw [ea, ec] at hd; exact Or.inl ⟨ea.trans ec.symm, hinj _ ea' _ ec' hd⟩
  · rw [ea, ec', dist_comm c x] at hd; exact Or.inr ⟨ea.trans ec'.symm, hinj _ ea' _ ec hd⟩
  · rw [ea] at hd; exact absurd (hd ▸ mem_dists ec ec' hne') (hout _ ea')
  · rw [ea', ec, dist_comm a x] at hd; exact Or.inr ⟨hinj _ ea _ ec' hd, ea'.trans ec.symm⟩
  · rw [ea', ec', dist_comm a x, dist_comm c x] at hd
    exact Or.inl ⟨hinj _ ea _ ec hd, ea'.trans ec'.symm⟩
  · rw [ea', dist_comm a x] at hd; exact absurd (hd ▸ mem_dists ec ec' hne') (hout _ ea)
  · rw [ec] at hd; exact absurd (hd.symm ▸ mem_dists ea ea' hne) (hout _ ec')
  · rw [ec', dist_comm c x] at hd; exact absurd (hd.symm ▸ mem_dists ea ea' hne) (hout _ ec)
  · exact hT a ea a' ea' c ec c' ec' hne hne' hd
theorem RainbowFamily.restrict {S W B : Finset (ℝ^d)} {I I' : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) (h : I' ⊆ I) :
    RainbowFamily S W B I' C β :=
  ⟨hF.Bne, hF.F1, fun k hk => hF.Cne k (h hk), fun k hk => hF.F2 k (h hk),
    ⟨fun k hk k' hk' => hF.F3.1 k (h hk) k' (h hk'), fun k hk => hF.F3.2 k (h hk)⟩,
    fun k hk => hF.F4 k (h hk), fun k hk x hx s hs k' hk' => hF.F5 k (h hk) x hx s hs k' (h hk')⟩
theorem gl_lr_or_avg {ι : Type*} [DecidableEq ι] (n D h : ℕ) (X : Finset (ℝ^d))
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (R0 C0 : Finset (ℝ^d)) (hR0 : R0 ⊆ X) (hC0 : C0 ⊆ X) (J : Finset ι)
    (colF : ι → ℝ^d → ℝ) (P : Finset (ℝ^d)) (hk : J.card + P.card ≤ kstar n)
    (htot : 16 * (D + 2) ^ (J.card + P.card) *
      ((R0 ×ˢ C0).filter fun q => (∀ i ∈ J, ‖q.1 - q.2‖ ^ 2 ≠ colF i q.2) ∧
        ∀ s ∈ P, ‖q.1 - q.2‖ ^ 2 ≠ ‖q.1 - s‖ ^ 2).card ≤ R0.card * C0.card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < R0.card) :
    (C0.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  classical
  set k := J.card + P.card with hkdef
  set LRc := LRcost (kstar n) (D + 2) with hLRc
  have hLR1 : 1 ≤ LRc := one_le_LRcost _ _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  rcases C0.eq_empty_or_nonempty with hCe | hCne
  · rw [hCe, card_empty, Nat.cast_zero]; positivity
  have hRne : R0.Nonempty := by
    rw [← card_pos]; have : (0 : ℝ) < R0.card := by nlinarith
    exact_mod_cast this
  let B : ℝ^d → ℝ^d → ℝ := fun x c =>
    (∏ i ∈ J, (‖x - c‖ ^ 2 - colF i c)) * ∏ s ∈ P, (‖x - c‖ ^ 2 - ‖x - s‖ ^ 2)
  have hBzero : ∀ x c, B x c ≠ 0 → (∀ i ∈ J, ‖x - c‖ ^ 2 ≠ colF i c) ∧
      ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2 := by
    intro x c hB
    simp only [B, ne_eq, mul_eq_zero, not_or, prod_eq_zero_iff, not_exists, not_and] at hB
    exact ⟨fun i hi h => hB.1 i hi (by rw [h]; ring),
      fun s hs h => hB.2 s hs (by rw [h]; ring)⟩
  have hrank : rankOn B R0 C0 ≤ (D + 2) ^ k := by
    unfold rankOn
    let F : ι ⊕ ℝ^d → ℝ^d → ℝ^d → ℝ := fun t => match t with
      | Sum.inl i => fun x c => ‖x - c‖ ^ 2 - 0 - colF i c
      | Sum.inr s => fun x c => ‖x - c‖ ^ 2 - ‖x - s‖ ^ 2 - 0
    have hB : (Matrix.of fun (x : R0) (c : C0) => B x c) =
        Matrix.of fun (x : R0) (c : C0) => ∏ t ∈ J.disjSum P, F t x c := by
      ext x c
      simp only [Matrix.of_apply, B, prod_disjSum, F, sub_zero]
    rw [hB]
    refine (rank_finset_prod_le (J.disjSum P) (fun t => Matrix.of fun (x : R0) (c : C0) =>
      F t x c)).trans ?_
    calc ∏ t ∈ J.disjSum P, (Matrix.of fun (x : R0) (c : C0) => F t x c).rank
        ≤ ∏ _t ∈ J.disjSum P, (D + 2) := by
          refine prod_le_prod' fun t _ => ?_
          rcases t with i | s
          · exact rank_sqdist_le_affine X D hD (fun x : R0 => (x : ℝ^d)) (fun c : C0 => (c : ℝ^d))
              (fun x => hR0 x.2) (fun c => hC0 c.2) (fun _ => 0) (fun c => colF i c)
          · exact rank_sqdist_le_affine X D hD (fun x : R0 => (x : ℝ^d)) (fun c : C0 => (c : ℝ^d))
              (fun x => hR0 x.2) (fun c => hC0 c.2) (fun x => ‖(x : ℝ^d) - s‖ ^ 2) (fun _ => 0)
      _ = (D + 2) ^ k := by rw [prod_const, card_disjSum]
  have hsupp : 16 * (D + 2) ^ k * (supp B R0 C0).card ≤ R0.card * C0.card := by
    refine le_trans (Nat.mul_le_mul_left _ (card_le_card fun q hq => ?_)) htot
    obtain ⟨hqRC, hq0⟩ := mem_filter.1 hq
    exact mem_filter.2 ⟨hqRC, hBzero q.1 q.2 hq0⟩
  obtain ⟨R1, hR1, C1, hC1, c1, c2, hzero⟩ :=
    cleaning B R0 C0 ((D + 2) ^ k) (Nat.one_le_pow _ _ (by omega)) hrank hsupp
  have hR1ne : R1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hRne; omega
  have hC1ne : C1.Nonempty := by
    rw [← card_pos]; have := card_pos.2 hCne; omega
  let τ : ι ⊕ ℝ^d → TF (ℝ^d) (ℝ^d) := fun t => match t with
    | Sum.inl i => TF.col (colF i)
    | Sum.inr s => TF.row fun x => ‖x - s‖ ^ 2
  let M : ℝ^d → ℝ^d → ℝ := fun x c => ‖x - c‖ ^ 2
  have hcov : Covers M τ (J.disjSum P) R1 C1 := by
    intro x hx c hc
    have h0 := hzero x hx c hc
    simp only [B, mul_eq_zero, prod_eq_zero_iff] at h0
    rcases h0 with ⟨i, hi, hi0⟩ | ⟨s, hs, hs0⟩
    · exact ⟨Sum.inl i, inl_mem_disjSum.2 hi, by simp only [M, τ, TF.eval]; linarith⟩
    · exact ⟨Sum.inr s, inr_mem_disjSum.2 hs, by simp only [M, τ, TF.eval]; linarith⟩
  have hrankM : rankOn M R1 C1 ≤ D + 2 := by
    unfold rankOn
    have := rank_sqdist_le_affine X D hD (fun x : R1 => (x : ℝ^d)) (fun c : C1 => (c : ℝ^d))
      (fun x => hR0 (hR1 x.2)) (fun c => hC0 (hC1 c.2)) (fun _ => 0) (fun _ => 0)
    have e : (Matrix.of fun (x : R1) (c : C1) => M x c) =
        Matrix.of fun (x : R1) (c : C1) => ‖(x : ℝ^d) - c‖ ^ 2 - 0 - 0 := by
      ext; simp [M]
    rw [e]; exact this
  obtain ⟨R2, hR2, C2, hC2, t₀, -, e1, e2, hM⟩ :=
    theoremLR M τ (D + 2) (kstar n) (J.disjSum P) R1 C1 (by rw [card_disjSum]; exact hk)
      hR1ne hC1ne hrankM hcov
  have hortho : ∀ x ∈ R2, ∀ x' ∈ R2, ∀ c ∈ C2, ∀ c' ∈ C2, inner ℝ (x - x') (c - c') = 0 := by
    rcases t₀ with i | s
    · refine ortho_of_equidistant R2 C2 (fun c => Real.sqrt (colF i c)) fun x hx c hc => ?_
      have := hM x hx c hc
      simp only [M, τ, TF.eval] at this
      rw [← this, Real.sqrt_sq (norm_nonneg _)]
    · refine ortho_of_bisector R2 C2 s fun x hx c hc => ?_
      have := hM x hx c hc
      simp only [M, τ, TF.eval] at this
      exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this).symm
  have hRC : affDim (R2 ∪ C2) ≤ D :=
    (affDim_mono (union_subset ((hR2.trans hR1).trans hR0) ((hC2.trans hC1).trans hC0))).trans hD
  have hmin := min_affDim_le_of_ortho R2 C2 D hRC hortho
  have hc1r : (R0.card : ℝ) ≤ 2 * R1.card := by exact_mod_cast c1
  have hc2r : (C0.card : ℝ) ≤ 2 * C1.card := by exact_mod_cast c2
  rcases le_total (affDim R2) (affDim C2) with hle | hle
  · rw [min_eq_left hle] at hmin
    have hR := hh R2 ((hR2.trans hR1).trans hR0) hmin
    have : (R2.card : ℝ) ≤ h := by exact_mod_cast hR
    have : (R0.card : ℝ) ≤ 2 * LRc * h := by
      calc (R0.card : ℝ) ≤ 2 * R1.card := hc1r
        _ ≤ 2 * (LRc * R2.card) := by linarith
        _ ≤ 2 * LRc * h := by nlinarith
    linarith
  · rw [min_eq_right hle] at hmin
    have hC := hh C2 ((hC2.trans hC1).trans hC0) hmin
    have : (C2.card : ℝ) ≤ h := by exact_mod_cast hC
    calc (C0.card : ℝ) ≤ 2 * C1.card := hc2r
      _ ≤ 2 * (LRc * C2.card) := by linarith
      _ ≤ 2 * LRc * h := by nlinarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
structure CoreCtx (n D h r : ℕ) (X S W : Finset (ℝ^d)) (σ Γ' : ℝ) (B : Finset (ℝ^d))
    (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) : Prop where
  hn : 5 ≤ n
  hr : r ≤ n - 5
  amb : Ambient n D h X
  conf : Config X S W r σ
  hσ : smin n D h ≤ σ
  hΓ : 1 ≤ Γ'
  hHR : HRholds S W σ Γ'
  fam : RainbowFamily S W B I C β
  BX : B ⊆ X
  hB : B.card = n - 4 - r
noncomputable def coreT (S B : Finset (ℝ^d)) (a1 a2 : ℝ^d) : Finset (ℝ^d) := insert a1 (insert a2 (S ∪ B))
def Hyp (S : Finset (ℝ^d)) (a1 a2 x : ℝ^d) : Prop :=
  ∃ s ∈ S, dist x s = dist x a1 ∨ dist x s = dist x a2
noncomputable def smRadii (S : Finset (ℝ^d)) (a1 a2 : ℝ^d) : Finset ℝ :=
  S.image (dist a1) ∪ S.image (dist a2) ∪ {dist a1 a2}
def Sm (S : Finset (ℝ^d)) (a1 a2 x : ℝ^d) : Prop :=
  ∃ s ∈ S, dist x s ∈ smRadii S a1 a2
def LamK (S B : Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (k : ℕ) (a1 a2 x : ℝ^d) : Prop :=
  dist x a1 ∈ dists (coreT S B a1 a2) ∪ B.image (β k) ∨
    dist x a2 ∈ dists (coreT S B a1 a2) ∪ B.image (β k) ∨ dist x a1 = dist x a2 ∨ Hyp S a1 a2 x
noncomputable instance (S : Finset (ℝ^d)) (a1 a2 : ℝ^d) : DecidablePred (Hyp S a1 a2) :=
  fun x => by unfold Hyp; infer_instance
noncomputable instance (S : Finset (ℝ^d)) (a1 a2 : ℝ^d) : DecidablePred (Sm S a1 a2) :=
  fun x => by unfold Sm; infer_instance
noncomputable instance (S B : Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (k : ℕ) (a1 a2 : ℝ^d) :
    DecidablePred (LamK S B β k a1 a2) :=
  fun x => by unfold LamK; infer_instance
theorem dists_coreT_subset (S B : Finset (ℝ^d)) (a1 a2 : ℝ^d) :
    dists (coreT S B a1 a2) ⊆
      dists (S ∪ B) ∪ (S ∪ B).image (dist a2) ∪ (insert a2 (S ∪ B)).image (dist a1) := by
  intro v hv
  rcases mem_union.1 (dists_insert_subset _ a1 hv) with h | h
  · rcases mem_union.1 (dists_insert_subset _ a2 h) with h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
  · exact mem_union_right _ h
theorem core_step0 {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m k : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hk : k ∈ I) (hkl : k ≠ l) (hkm : k ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m)
    (hT : Rainbow (coreT S B a1 a2)) (hβ : Disjoint (B.image (β k)) (dists (coreT S B a1 a2)))
    {x : ℝ^d} (hx : x ∈ C k) (hng : ¬ Rainbow (insert x (coreT S B a1 a2))) :
    LamK S B β k a1 a2 x ∨ Sm S a1 a2 x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hL, hSm⟩ := hcon
  simp only [LamK, not_or] at hL
  obtain ⟨hL1, hL2, hL12, hHyp⟩ := hL
  simp only [Hyp, not_exists, not_and, not_or] at hHyp
  simp only [Sm, not_exists, not_and] at hSm
  obtain ⟨hxSB, hxR⟩ := hF.F4 k hk x hx
  have hxa1 : x ≠ a1 := fun e => family_classes_disjoint hF hk hl hkl hx (e ▸ ha1)
  have hxa2 : x ≠ a2 := fun e => family_classes_disjoint hF hk hm hkm hx (e ▸ ha2)
  have hxT : x ∉ coreT S B a1 a2 := by
    simp only [coreT, mem_insert, not_or]; exact ⟨hxa1, hxa2, hxSB⟩
  have hSBinj : ∀ y ∈ S ∪ B, ∀ y' ∈ S ∪ B, dist x y = dist x y' → y = y' := by
    intro y hy y' hy' h
    have hxy : x ≠ y := fun e => hxSB (e ▸ hy)
    have hxy' : x ≠ y' := fun e => hxSB (e ▸ hy')
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) x (mem_insert_self _ _) y'
      (mem_insert_of_mem hy') hxy hxy' h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 hxy'
  have hxb : ∀ b ∈ B, dist x b ∈ B.image (β k) := fun b hb =>
    mem_image.2 ⟨b, hb, (hF.F2 k hk x hx b hb).symm⟩
  refine hng (rainbow_insert_one _ x hT hxT ?_ ?_)
  · intro y hy y' hy' h
    simp only [coreT, mem_insert] at hy hy'
    rcases hy with rfl | rfl | hy <;> rcases hy' with rfl | rfl | hy'
    · rfl
    · exact absurd h hL12
    · rcases mem_union.1 hy' with hs | hb
      · exact absurd h.symm ((hHyp _ hs).1)
      · exact absurd (h ▸ hxb y' hb) (fun hm' => hL1 (mem_union_right _ hm'))
    · exact absurd h.symm hL12
    · rfl
    · rcases mem_union.1 hy' with hs | hb
      · exact absurd h.symm ((hHyp _ hs).2)
      · exact absurd (h ▸ hxb y' hb) (fun hm' => hL2 (mem_union_right _ hm'))
    · rcases mem_union.1 hy with hs | hb
      · exact absurd h ((hHyp _ hs).1)
      · exact absurd (h.symm ▸ hxb y hb) (fun hm' => hL1 (mem_union_right _ hm'))
    · rcases mem_union.1 hy with hs | hb
      · exact absurd h ((hHyp _ hs).2)
      · exact absurd (h.symm ▸ hxb y hb) (fun hm' => hL2 (mem_union_right _ hm'))
    · exact hSBinj y hy y' hy' h
  · intro y hy hmem
    simp only [coreT, mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · exact hL1 (mem_union_left _ hmem)
    · exact hL2 (mem_union_left _ hmem)
    rcases mem_union.1 hy with hs | hb
    ·
      rcases mem_union.1 (dists_coreT_subset S B a1 a2 hmem) with h | h
      · rcases mem_union.1 h with h | h
        ·
          obtain ⟨q, hq, hqe⟩ := mem_image.1 h
          obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
          have hxy : x ≠ y := fun e => hxSB (e ▸ mem_union_left _ hs)
          rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem (mem_union_left _ hs)) q.1
            (mem_insert_of_mem hq1) q.2 (mem_insert_of_mem hq2) hxy hq12 hqe.symm with
            ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hxSB (h1 ▸ hq1)
          · exact hxSB (h1 ▸ hq2)
        · obtain ⟨z, hz, hze⟩ := mem_image.1 h
          rcases mem_union.1 hz with hzS | hzB
          · exact hSm y hs (mem_union_left _ (mem_union_right _ (mem_image.2 ⟨z, hzS, hze⟩)))
          · rw [hF.F2 m hm a2 ha2 z hzB] at hze
            exact hF.F5 k hk x hx y hs m hm z hzB hze.symm
      · obtain ⟨z, hz, hze⟩ := mem_image.1 h
        rcases mem_insert.1 hz with rfl | hz
        · exact hSm y hs (mem_union_right _ (mem_singleton.2 hze.symm))
        rcases mem_union.1 hz with hzS | hzB
        · exact hSm y hs (mem_union_left _ (mem_union_left _ (mem_image.2 ⟨z, hzS, hze⟩)))
        · rw [hF.F2 l hl a1 ha1 z hzB] at hze
          exact hF.F5 k hk x hx y hs l hl z hzB hze.symm
    · exact disjoint_left.1 hβ (hxb y hb) hmem
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
def CoverShape (S : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (w : ℕ) (δ : ℝ) (k : ℕ)
    (a1 a2 : ℝ^d) : Prop :=
  ∃ Ω : Finset ℝ, Ω.card ≤ w ∧ ∃ Ex ⊆ C k, (Ex.card : ℝ) ≤ δ * (C k).card ∧
    ∀ x ∈ C k, dist x a1 ∈ Ω ∨ dist x a2 ∈ Ω ∨ dist x a1 = dist x a2 ∨ Hyp S a1 a2 x ∨ x ∈ Ex
def AltII (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (ε : ℝ) (k k' : ℕ)
    (a1 a2 : ℝ^d) : Prop :=
  (((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
    dist x a2 ∈ B.image (β k))).card : ℝ) < 2 * ε * (C k').card
def CovK (S B : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (ε : ℝ) (k' : ℕ)
    (a1 a2 : ℝ^d) : Prop :=
  (((C k').filter fun x => ¬ LamK S B β k' a1 a2 x).card : ℝ) < 6 * ε * (C k').card
theorem G1_pairs (n D h : ℕ) (X T P Q : Finset (ℝ^d)) (hfree : RainbowFree n X)
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (hTX : T ⊆ X) (hTn : T.card + 2 = n) (hT1 : T.Nonempty) (hPX : P ⊆ X) (hQX : Q ⊆ X)
    (hPQ : Disjoint P Q) (hPg : ∀ x ∈ P, x ∉ T ∧ Rainbow (insert x T))
    (hQg : ∀ x ∈ Q, x ∉ T ∧ Rainbow (insert x T)) :
    (((Q ×ˢ P).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) ≤
      4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) * (P.card + Q.card) := by
  classical
  have hY := G1_count n D h X T (P ∪ Q) hfree hD hh hTX hTn hT1 (union_subset hPX hQX)
    (fun x hx => by rcases mem_union.1 hx with h | h; exact hPg x h; exact hQg x h)
  have hsub : ((Q ×ˢ P).filter fun q => Disjoint (labels T q.1) (labels T q.2)) ⊆
      (((P ∪ Q) ×ˢ (P ∪ Q)).filter fun q => Disjoint (labels T q.1) (labels T q.2)) := by
    intro q hq
    obtain ⟨hqQP, hd⟩ := mem_filter.1 hq
    obtain ⟨h1, h2⟩ := mem_product.1 hqQP
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_union_right _ h1, mem_union_left _ h2⟩, hd⟩
  have hc : ((P ∪ Q).card : ℝ) = P.card + Q.card := by
    rw [card_union_of_disjoint hPQ]; push_cast; ring
  rw [← hc]
  exact (by exact_mod_cast card_le_card hsub : (_ : ℝ) ≤ _).trans hY
theorem card_coreT {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m) :
    (coreT S B a1 a2).card = (S ∪ B).card + 2 := by
  have h12 : a1 ≠ a2 := fun e => family_classes_disjoint hF hl hm hlm ha1 (e ▸ ha2)
  have h1 : a1 ∉ insert a2 (S ∪ B) := by
    simp only [mem_insert, not_or]; exact ⟨h12, (hF.F4 l hl a1 ha1).1⟩
  rw [coreT, card_insert_of_notMem h1, card_insert_of_notMem (hF.F4 m hm a2 ha2).1]
set_option maxHeartbeats 1000000 in
theorem core_step1 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) (M ε δ1 : ℝ) (hM0 : 0 < M)
    (hMk : ∀ k ∈ I, M ≤ (C k).card) (hε : 0 < ε) (hP2 : 2 * n ^ 2 * σ ≤ ε * M)
    (hδ1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M) + 3 * n ^ 2 * σ / M ≤ δ1)
    {l m k k' : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hlm : l ≠ m) (hk : k ∈ I) (hk' : k' ∈ I)
    (hkl : k ≠ l) (hkm : k ≠ m) (hk'l : k' ≠ l) (hk'm : k' ≠ m) (hkk : k ≠ k')
    {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m) (hT : Rainbow (coreT S B a1 a2))
    (hβk : Disjoint (B.image (β k)) (dists (coreT S B a1 a2)))
    (hβk' : Disjoint (B.image (β k')) (dists (coreT S B a1 a2))) :
    CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2 ∨
      AltII S B C β ε k k' a1 a2 := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  set T := coreT S B a1 a2 with hTdef
  set μ0 := LRcost (kG n) (D + 2) * h with hμ0
  have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  have hSB : (S ∪ B).card = r + (n - 4 - r) := by
    rw [card_union_of_disjoint hF.F1.1, hc.card, hB]
  have hTc : T.card = n - 2 := by rw [hTdef, card_coreT hF hl hm hlm ha1 ha2, hSB]; omega
  have hTX : T ⊆ X := by
    intro y hy
    simp only [hTdef, coreT, mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · exact hc.subW ((hF.Cne l hl).2 ha1)
    · exact hc.subW ((hF.Cne m hm).2 ha2)
    · rcases mem_union.1 hy with hy | hy
      · exact hc.subX hy
      · exact hBX hy
  have hT1 : T.Nonempty := ⟨a1, mem_insert_self _ _⟩
  have hTn : T.card + 2 = n := by omega
  have hkW : C k ⊆ W := (hF.Cne k hk).2
  have hk'W : C k' ⊆ W := (hF.Cne k' hk').2
  have hnotT : ∀ j ∈ I, j ≠ l → j ≠ m → ∀ x ∈ C j, x ∉ T := by
    intro j hj hjl hjm x hx hxT
    simp only [hTdef, coreT, mem_insert] at hxT
    rcases hxT with e | e | e
    · exact family_classes_disjoint hF hj hl hjl hx (e ▸ ha1)
    · exact family_classes_disjoint hF hj hm hjm hx (e ▸ ha2)
    · exact (hF.F4 j hj x hx).1 e
  have hlabT : ∀ j ∈ I, ∀ x ∈ C j, ∀ v ∈ labels T x,
      (∃ s ∈ S, v = dist x s) ∨ v ∈ B.image (β j) ∨ v = dist x a1 ∨ v = dist x a2 := by
    intro j hj x hx v hv
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hv
    simp only [hTdef, coreT, mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · rcases mem_union.1 hy with hs | hb
      · exact Or.inl ⟨y, hs, rfl⟩
      · exact Or.inr (Or.inl (mem_image.2 ⟨y, hb, (hF.F2 j hj x hx y hb).symm⟩))
  have hRem : ∀ R0 : Finset ℝ, (∀ t ∈ R0, 0 < t) →
      (((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0).card : ℝ) ≤ r * (R0.card * σ) := by
    intro R0 hR0
    refine le_trans ?_ (removal_bound hc R0 hR0)
    exact_mod_cast card_le_card fun x hx => by
      obtain ⟨hxC, s, hs, hxs⟩ := mem_filter.1 hx
      exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hkW hxC, hxs⟩⟩
  have hsmpos : ∀ t ∈ smRadii S a1 a2, 0 < t := by
    intro t ht
    simp only [smRadii, mem_union, mem_image, mem_singleton] at ht
    rcases ht with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | rfl
    · exact dist_pos.2 fun e => (hF.F4 l hl a1 ha1).1 (mem_union_left _ (e ▸ hs))
    · exact dist_pos.2 fun e => (hF.F4 m hm a2 ha2).1 (mem_union_left _ (e ▸ hs))
    · exact dist_pos.2 fun e => family_classes_disjoint hF hl hm hlm ha1 (e ▸ ha2)
  have hsmc : (smRadii S a1 a2).card ≤ 2 * r + 1 := by
    have e1 := card_union_le (S.image (dist a1) ∪ S.image (dist a2)) {dist a1 a2}
    have e2 := card_union_le (S.image (dist a1)) (S.image (dist a2))
    have e3 := card_image_le (s := S) (f := dist a1)
    have e4 := card_image_le (s := S) (f := dist a2)
    rw [hc.card] at e3 e4
    simp only [smRadii, card_singleton] at e1 ⊢
    omega
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hrn : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hSmk : ∀ j ∈ I, (((C j).filter fun x => Sm S a1 a2 x).card : ℝ) ≤ 2 * n ^ 2 * σ := by
    intro j hj
    have h1 : (((C j).filter fun x => Sm S a1 a2 x).card : ℝ) ≤
        r * ((smRadii S a1 a2).card * σ) := by
      refine le_trans ?_ (removal_bound hc _ hsmpos)
      exact_mod_cast card_le_card fun x hx => by
        obtain ⟨hxC, s, hs, hxs⟩ := mem_filter.1 hx
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF.Cne j hj).2 hxC, hxs⟩⟩
    have h2 : ((smRadii S a1 a2).card : ℝ) ≤ 2 * r + 1 := by exact_mod_cast hsmc
    have h3 : (r : ℝ) * ((smRadii S a1 a2).card * σ) ≤ r * ((2 * r + 1) * σ) := by gcongr
    have hr5 : (r : ℝ) + 5 ≤ n := by exact_mod_cast (show r + 5 ≤ n by omega)
    have hq : (r : ℝ) * (2 * r + 1) ≤ 2 * n ^ 2 := by nlinarith
    have h4 : (r : ℝ) * ((2 * r + 1) * σ) ≤ 2 * n ^ 2 * σ := by
      have := mul_le_mul_of_nonneg_right hq hσ0
      linarith [show (r : ℝ) * ((2 * r + 1) * σ) = r * (2 * r + 1) * σ by ring]
    linarith
  set P := (C k).filter fun x => Rainbow (insert x T) with hP
  set Q := (C k').filter fun x => Rainbow (insert x T) with hQ
  set Q' := Q.filter fun w => Disjoint (labels T w) (B.image (β k)) with hQ'
  have hCk'M : M ≤ (C k').card := hMk k' hk'
  have hCkM : M ≤ (C k).card := hMk k hk
  by_cases hcase : ε * (C k').card ≤ Q'.card
  · left
    have hQ'pos : (0 : ℝ) < Q'.card := lt_of_lt_of_le (mul_pos hε (lt_of_lt_of_le hM0 hCk'M)) hcase
    have hQ'ne : Q'.Nonempty := by rw [← card_pos]; exact_mod_cast hQ'pos
    set LD := (Q' ×ˢ P).filter fun q => Disjoint (labels T q.1) (labels T q.2) with hLD
    have hLDc : (LD.card : ℝ) ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) := by
      have h1 := G1_pairs n D h X T P Q' hX.free hX.dim hX.half hTX hTn hT1
        ((filter_subset _ _).trans (hkW.trans hc.subW))
        (((filter_subset _ _).trans (filter_subset _ _)).trans (hk'W.trans hc.subW))
        (disjoint_left.2 fun x hxP hxQ => family_classes_disjoint hF hk hk' hkk
          (mem_filter.1 hxP).1 (mem_filter.1 (mem_filter.1 hxQ).1).1)
        (fun x hx => ⟨hnotT k hk hkl hkm x (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩)
        (fun x hx => ⟨hnotT k' hk' hk'l hk'm x (mem_filter.1 (mem_filter.1 hx).1).1,
          (mem_filter.1 (mem_filter.1 hx).1).2⟩)
      have e1 : (P.card : ℝ) ≤ (C k).card := by exact_mod_cast card_le_card (filter_subset _ _)
      have e2 : (Q'.card : ℝ) ≤ (C k').card :=
        by exact_mod_cast card_le_card ((filter_subset _ _).trans (filter_subset _ _))
      calc (LD.card : ℝ) ≤ 4 ^ (n - 2) * μ0 * (P.card + Q'.card) := h1
        _ ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) := by gcongr
    let part : ℝ^d → Finset (ℝ^d) := fun w => P.filter fun x => Disjoint (labels T w) (labels T x)
    obtain ⟨w0, hw0, hwmin⟩ := exists_min_image Q' (fun w => (part w).card) hQ'ne
    have hpart : (Q'.card : ℝ) * (part w0).card ≤ LD.card := by
      have : Q'.card * (part w0).card ≤ LD.card := by
        calc Q'.card * (part w0).card = ∑ _w ∈ Q', (part w0).card := by rw [sum_const, smul_eq_mul]
          _ ≤ ∑ w ∈ Q', (part w).card := sum_le_sum hwmin
          _ = LD.card := by
              rw [hLD, card_filter, sum_product]
              exact sum_congr rfl fun w _ => by simp only [part, card_filter]
      have h' : ((Q'.card * (part w0).card : ℕ) : ℝ) ≤ LD.card := by exact_mod_cast this
      rwa [Nat.cast_mul] at h'
    have hw0Q := (mem_filter.1 hw0).1
    have hw0C : w0 ∈ C k' := (mem_filter.1 hw0Q).1
    have hw0T : w0 ∉ T := hnotT k' hk' hk'l hk'm w0 hw0C
    have hw0dis : Disjoint (labels T w0) (B.image (β k)) := (mem_filter.1 hw0).2
    set R0 := S.image (dist w0) ∪ {dist w0 a1, dist w0 a2} with hR0
    have hR0pos : ∀ t ∈ R0, 0 < t := by
      intro t ht
      simp only [hR0, mem_union, mem_image, mem_insert, mem_singleton] at ht
      rcases ht with ⟨s, hs, rfl⟩ | rfl | rfl
      · exact dist_pos.2 fun e => hw0T (by simp [hTdef, coreT, e ▸ hs])
      · exact dist_pos.2 fun e => hw0T (by simp [hTdef, coreT, e])
      · exact dist_pos.2 fun e => hw0T (by simp [hTdef, coreT, e])
    have hR0c : R0.card ≤ r + 2 := by
      have e1 := card_union_le (S.image (dist w0)) {dist w0 a1, dist w0 a2}
      have e2 := card_image_le (s := S) (f := dist w0)
      have e3 : ({dist w0 a1, dist w0 a2} : Finset ℝ).card ≤ 2 := card_le_two
      rw [hc.card] at e2
      rw [hR0]; omega
    refine ⟨labels T w0 ∪ dists T ∪ B.image (β k), ?_,
      part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪ ((C k).filter fun x => Sm S a1 a2 x),
      ?_, ?_, ?_⟩
    · have e1 := card_union_le (labels T w0 ∪ dists T) (B.image (β k))
      have e2 := card_union_le (labels T w0) (dists T)
      have e3 : (labels T w0).card ≤ T.card := card_image_le
      have e4 := card_dists_le T
      have e5 := card_image_le (s := B) (f := β k)
      rw [hTc] at e3 e4
      rw [hB] at e5
      omega
    · intro x hx
      rcases mem_union.1 hx with hx | hx
      · rcases mem_union.1 hx with hx | hx
        · exact (mem_filter.1 (mem_filter.1 hx).1).1
        · exact (mem_filter.1 hx).1
      · exact (mem_filter.1 hx).1
    ·
      have h1 : ((part w0).card : ℝ) ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card := by
        rw [le_div_iff₀ hQ'pos]; linarith
      have h2 := hRem R0 hR0pos
      have h3 := hSmk k hk
      have hR0r : (R0.card : ℝ) ≤ r + 2 := by exact_mod_cast hR0c
      have h4 : (r : ℝ) * (R0.card * σ) ≤ r * ((r + 2) * σ) := by gcongr
      have hex : ((part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪
          ((C k).filter fun x => Sm S a1 a2 x)).card : ℝ) ≤
          4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card + 3 * n ^ 2 * σ := by
        have c1 := card_union_le (part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0))
          ((C k).filter fun x => Sm S a1 a2 x)
        have c2 := card_union_le (part w0) ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0)
        have c3 : ((part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪
            ((C k).filter fun x => Sm S a1 a2 x)).card : ℝ) ≤ (part w0).card +
            ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0).card +
            ((C k).filter fun x => Sm S a1 a2 x).card := by exact_mod_cast c1.trans (by omega)
        have hrn2' : (r : ℝ) * ((r + 2) * σ) ≤ n ^ 2 * σ := by
          have hr5 : (r : ℝ) + 5 ≤ n := by exact_mod_cast (show r + 5 ≤ n by omega)
          have hq : (r : ℝ) * (r + 2) ≤ n ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right hq hσ0
          linarith [show (r : ℝ) * ((r + 2) * σ) = r * (r + 2) * σ by ring]
        linarith only [c3, h1, h2, h3, h4, hrn2']
      have hCkpos : (0 : ℝ) < (C k).card := lt_of_lt_of_le hM0 hCkM
      have hfrac : 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card ≤
          2 * 4 ^ (n - 2) * μ0 / (ε * M) * (C k).card := by
        have hA : (0 : ℝ) ≤ 4 ^ (n - 2) * μ0 := mul_nonneg (by positivity) hμ
        rw [div_le_iff₀ hQ'pos, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hε hM0)]
        have hCk0 : (0 : ℝ) ≤ (C k).card := Nat.cast_nonneg _
        have hCk'0 : (0 : ℝ) ≤ (C k').card := Nat.cast_nonneg _
        have f1 : ((C k).card : ℝ) * M ≤ (C k).card * (C k').card :=
          mul_le_mul_of_nonneg_left hCk'M hCk0
        have f2 : ((C k').card : ℝ) * M ≤ (C k).card * (C k').card := by
          have := mul_le_mul_of_nonneg_right hCkM hCk'0
          linarith [mul_comm ((C k').card : ℝ) M]
        have e2 : ((C k).card + (C k').card) * (ε * M) ≤ 2 * (C k).card * (ε * (C k').card) := by
          have := mul_le_mul_of_nonneg_left (add_le_add f1 f2) hε.le
          linarith [show (((C k).card : ℝ) + (C k').card) * (ε * M) =
            ε * ((C k).card * M + (C k').card * M) by ring,
            show 2 * ((C k).card : ℝ) * (ε * (C k').card) =
            ε * ((C k).card * (C k').card + (C k).card * (C k').card) by ring]
        have e3 : 2 * (C k).card * (ε * (C k').card) ≤ 2 * (C k).card * Q'.card := by
          have : (0 : ℝ) ≤ 2 * (C k).card := by linarith [hCk0]
          exact mul_le_mul_of_nonneg_left hcase this
        calc 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) * (ε * M)
            = 4 ^ (n - 2) * μ0 * (((C k).card + (C k').card) * (ε * M)) := by ring
          _ ≤ 4 ^ (n - 2) * μ0 * (2 * (C k).card * Q'.card) := by
              exact mul_le_mul_of_nonneg_left (e2.trans e3) hA
          _ = 2 * 4 ^ (n - 2) * μ0 * (C k).card * Q'.card := by ring
      have hlast : 3 * n ^ 2 * σ ≤ 3 * n ^ 2 * σ / M * (C k).card := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hM0]
        have : (0 : ℝ) ≤ 3 * n ^ 2 * σ := mul_nonneg (by positivity) hσ0
        nlinarith
      have hδ1' : 0 ≤ (C k).card := Nat.zero_le _
      calc ((part w0 ∪ ((C k).filter fun x => ∃ s ∈ S, dist x s ∈ R0) ∪
            ((C k).filter fun x => Sm S a1 a2 x)).card : ℝ)
          ≤ 4 ^ (n - 2) * μ0 * ((C k).card + (C k').card) / Q'.card + 3 * n ^ 2 * σ := hex
        _ ≤ 2 * 4 ^ (n - 2) * μ0 / (ε * M) * (C k).card + 3 * n ^ 2 * σ / M * (C k).card := by
            linarith only [hfrac, hlast]
        _ = (2 * 4 ^ (n - 2) * μ0 / (ε * M) + 3 * n ^ 2 * σ / M) * (C k).card := by ring
        _ ≤ δ1 * (C k).card := mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg _)
    ·
      intro x hxC
      by_cases hgen : Rainbow (insert x T)
      · have hxP : x ∈ P := mem_filter.2 ⟨hxC, hgen⟩
        by_cases hpx : x ∈ part w0
        · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_left _ hpx)))))
        · have hnd : ¬ Disjoint (labels T w0) (labels T x) := fun hd => hpx (mem_filter.2 ⟨hxP, hd⟩)
          rw [not_disjoint_iff] at hnd
          obtain ⟨v, hvw, hvx⟩ := hnd
          rcases hlabT k hk x hxC v hvx with ⟨s, hs, rfl⟩ | hvb | rfl | rfl
          ·
            rcases hlabT k' hk' w0 hw0C _ hvw with ⟨s', hs', he⟩ | hvb' | he | he
            · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _
                (mem_filter.2 ⟨hxC, s, hs, by
                  rw [he]; exact mem_union_left _ (mem_image.2 ⟨s', hs', rfl⟩)⟩))))))
            · obtain ⟨b, hb, hbe⟩ := mem_image.1 hvb'
              exact absurd hbe.symm (hF.F5 k hk x hxC s hs k' hk' b hb)
            · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _
                (mem_filter.2 ⟨hxC, s, hs, by rw [he]; simp [hR0]⟩))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _
                (mem_filter.2 ⟨hxC, s, hs, by rw [he]; simp [hR0]⟩))))))
          · exact absurd hvb (disjoint_left.1 hw0dis hvw)
          · exact Or.inl (mem_union_left _ (mem_union_left _ hvw))
          · exact Or.inr (Or.inl (mem_union_left _ (mem_union_left _ hvw)))
      · rcases core_step0 hF hl hm hk hkl hkm ha1 ha2 hT hβk hxC hgen with hL | hS
        · rcases hL with h | h | h | h
          · exact Or.inl (by
              rcases mem_union.1 h with h | h
              · exact mem_union_left _ (mem_union_right _ h)
              · exact mem_union_right _ h)
          · exact Or.inr (Or.inl (by
              rcases mem_union.1 h with h | h
              · exact mem_union_left _ (mem_union_right _ h)
              · exact mem_union_right _ h))
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_union_right _ (mem_filter.2 ⟨hxC, hS⟩)))))
  · right
    push Not at hcase
    have hsub : ((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
        dist x a2 ∈ B.image (β k))) ⊆ Q' ∪ ((C k').filter fun x => Sm S a1 a2 x) := by
      intro x hx
      obtain ⟨hxC, hnot⟩ := mem_filter.1 hx
      push Not at hnot
      obtain ⟨hnL, hn1, hn2⟩ := hnot
      by_cases hgen : Rainbow (insert x T)
      · refine mem_union_left _ (mem_filter.2 ⟨mem_filter.2 ⟨hxC, hgen⟩, ?_⟩)
        rw [disjoint_left]
        intro v hvx hvb
        rcases hlabT k' hk' x hxC v hvx with ⟨s, hs, rfl⟩ | hvb' | rfl | rfl
        · obtain ⟨b, hb, hbe⟩ := mem_image.1 hvb
          exact hF.F5 k' hk' x hxC s hs k hk b hb hbe.symm
        · obtain ⟨b, hb, hbe⟩ := mem_image.1 hvb
          obtain ⟨b', hb', hbe'⟩ := mem_image.1 hvb'
          exact hkk (hF.F3.1 k hk k' hk' b hb b' hb' (hbe.trans hbe'.symm)).1
        · exact hn1 hvb
        · exact hn2 hvb
      · rcases core_step0 hF hl hm hk' hk'l hk'm ha1 ha2 hT hβk' hxC hgen with hL | hS
        · exact absurd hL hnL
        · exact mem_union_right _ (mem_filter.2 ⟨hxC, hS⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le Q' ((C k').filter fun x => Sm S a1 a2 x)
    have h3 := hSmk k' hk'
    have h4 : (2 : ℝ) * n ^ 2 * σ ≤ ε * (C k').card := hP2.trans (by gcongr)
    have : (((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
        dist x a2 ∈ B.image (β k))).card : ℝ) ≤ Q'.card +
        ((C k').filter fun x => Sm S a1 a2 x).card := by exact_mod_cast h1.trans h2
    unfold AltII
    linarith
theorem core_step2 {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) (ε : ℝ) (hε : 0 < ε) (M : ℝ)
    (hM0 : 0 < M) {k' : ℕ} (hMk' : M ≤ (C k').card) {a1 a2 : ℝ^d}
    (J : Finset ℕ) (hJI : J ⊆ I) (hJ3 : 3 ≤ J.card)
    (hII : ∀ k ∈ J, AltII S B C β ε k k' a1 a2) : CovK S B C β ε k' a1 a2 := by
  classical
  set A := (C k').filter fun x => ¬ LamK S B β k' a1 a2 x with hA
  set N : ℝ := ((C k').card : ℝ) with hN
  have hNpos : 0 < N := lt_of_lt_of_le hM0 hMk'
  unfold CovK
  by_contra hcon
  push Not at hcon
  set U1 : ℕ → Finset (ℝ^d) := fun k => A.filter fun x => dist x a1 ∈ B.image (β k) with hU1
  set U2 : ℕ → Finset (ℝ^d) := fun k => A.filter fun x => dist x a2 ∈ B.image (β k) with hU2
  have hlow : ∀ k ∈ J, (A.card : ℝ) - 2 * ε * N < (U1 k).card + (U2 k).card := by
    intro k hk
    have h1 := hII k hk
    unfold AltII at h1
    have hsub : A ⊆ ((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨ dist x a1 ∈ B.image (β k) ∨
        dist x a2 ∈ B.image (β k))) ∪ (U1 k ∪ U2 k) := by
      intro x hx
      by_cases h1' : dist x a1 ∈ B.image (β k)
      · exact mem_union_right _ (mem_union_left _ (mem_filter.2 ⟨hx, h1'⟩))
      by_cases h2' : dist x a2 ∈ B.image (β k)
      · exact mem_union_right _ (mem_union_right _ (mem_filter.2 ⟨hx, h2'⟩))
      obtain ⟨hxC, hxL⟩ := mem_filter.1 hx
      refine mem_union_left _ (mem_filter.2 ⟨hxC, ?_⟩)
      rintro (h | h | h)
      · exact hxL h
      · exact h1' h
      · exact h2' h
    have e1 := (card_le_card hsub).trans (card_union_le _ _)
    have e2 := card_union_le (U1 k) (U2 k)
    have : (A.card : ℝ) ≤ ((C k').filter fun x => ¬ (LamK S B β k' a1 a2 x ∨
        dist x a1 ∈ B.image (β k) ∨ dist x a2 ∈ B.image (β k))).card +
        ((U1 k).card + (U2 k).card) := by
      exact_mod_cast e1.trans (by omega)
    linarith
  have hdisj : ∀ (f : ℝ^d → ℝ),
      ∑ k ∈ J, (A.filter fun x => f x ∈ B.image (β k)).card ≤ A.card := by
    intro f
    rw [← card_biUnion]
    · exact card_le_card (biUnion_subset.2 fun k _ => filter_subset _ _)
    · intro k hk k'' hk'' hne
      rw [Function.onFun, disjoint_left]
      intro x hx1 hx2
      obtain ⟨b, hb, hbe⟩ := mem_image.1 (mem_filter.1 hx1).2
      obtain ⟨b', hb', hbe'⟩ := mem_image.1 (mem_filter.1 hx2).2
      exact hne (hF.F3.1 k (hJI hk) k'' (hJI hk'') b hb b' hb' (hbe.trans hbe'.symm)).1
  have hs1 := hdisj (fun x => dist x a1)
  have hs2 := hdisj (fun x => dist x a2)
  have hJpos : 0 < J.card := by omega
  have hsum : (J.card : ℝ) * ((A.card : ℝ) - 2 * ε * N) < 2 * A.card := by
    calc (J.card : ℝ) * ((A.card : ℝ) - 2 * ε * N) = ∑ _k ∈ J, ((A.card : ℝ) - 2 * ε * N) := by
          rw [sum_const, nsmul_eq_mul]
      _ < ∑ k ∈ J, (((U1 k).card : ℝ) + (U2 k).card) :=
          sum_lt_sum_of_nonempty (card_pos.1 hJpos) hlow
      _ = ((∑ k ∈ J, (U1 k).card + ∑ k ∈ J, (U2 k).card : ℕ) : ℝ) := by
          push_cast; rw [sum_add_distrib]
      _ ≤ 2 * A.card := by
          have : ∑ k ∈ J, (U1 k).card + ∑ k ∈ J, (U2 k).card ≤ 2 * A.card := by
            simp only [hU1, hU2]; omega
          exact_mod_cast this
  have hJ3r : (3 : ℝ) ≤ J.card := by exact_mod_cast hJ3
  have hεN : 0 < ε * N := mul_pos hε hNpos
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  nlinarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem gl_lr_or_sets (n D h : ℕ) (X : Finset (ℝ^d))
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (R0 C0 : Finset (ℝ^d)) (hR0 : R0 ⊆ X) (hC0 : C0 ⊆ X) (w : ℕ) (Val : ℝ^d → Finset ℝ)
    (hVal : ∀ c ∈ C0, (Val c).card ≤ w) (P : Finset (ℝ^d)) (hk : w + P.card ≤ kstar n)
    (hfew : ∀ c ∈ C0, 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + P.card) *
      ((R0.filter fun x => ‖x - c‖ ^ 2 ∉ Val c ∧ ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card : ℝ) ≤
        R0.card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < R0.card) :
    (C0.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  refine gl_lr_or n D h X hD hh R0 C0 hR0 hC0 (range w) (fun i c => (Val c).toList.getD i 0) P
    (by rwa [card_range]) ?_ hbig
  intro c hc
  rw [card_range]
  have h1' : 16 * (D + 2) ^ (w + P.card) * (R0.filter fun x => ‖x - c‖ ^ 2 ∉ Val c ∧
      ∀ s ∈ P, ‖x - c‖ ^ 2 ≠ ‖x - s‖ ^ 2).card ≤ R0.card := by exact_mod_cast hfew c hc
  refine le_trans (Nat.mul_le_mul_left _ (card_le_card ?_)) h1'
  intro x hx
  rw [mem_filter] at hx ⊢
  obtain ⟨hxR, hA, hB⟩ := hx
  refine ⟨hxR, fun hv => ?_, hB⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (mem_toList.2 hv)
  have hiw : i < w := lt_of_lt_of_le hi (by rw [length_toList]; exact hVal c hc)
  apply hA i (mem_range.2 hiw)
  rw [List.getD_eq_getElem _ _ hi, he]
theorem gl_lr_or_avg_sets (n D h : ℕ) (X : Finset (ℝ^d))
    (hD : affDim X ≤ D) (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h)
    (R0 C0 : Finset (ℝ^d)) (hR0 : R0 ⊆ X) (hC0 : C0 ⊆ X) (w : ℕ) (Val : ℝ^d → Finset ℝ)
    (hVal : ∀ c ∈ C0, (Val c).card ≤ w) (P : Finset (ℝ^d)) (hk : w + P.card ≤ kstar n)
    (htot : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + P.card) *
      (((R0 ×ˢ C0).filter fun q => ‖q.1 - q.2‖ ^ 2 ∉ Val q.2 ∧
        ∀ s ∈ P, ‖q.1 - q.2‖ ^ 2 ≠ ‖q.1 - s‖ ^ 2).card : ℝ) ≤ R0.card * C0.card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < R0.card) :
    (C0.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  refine gl_lr_or_avg n D h X hD hh R0 C0 hR0 hC0 (range w) (fun i c => (Val c).toList.getD i 0)
    P (by rwa [card_range]) ?_ hbig
  rw [card_range]
  have h1' : 16 * (D + 2) ^ (w + P.card) * ((R0 ×ˢ C0).filter fun q => ‖q.1 - q.2‖ ^ 2 ∉ Val q.2 ∧
      ∀ s ∈ P, ‖q.1 - q.2‖ ^ 2 ≠ ‖q.1 - s‖ ^ 2).card ≤ R0.card * C0.card := by exact_mod_cast htot
  refine le_trans (Nat.mul_le_mul_left _ (card_le_card ?_)) h1'
  intro q hq
  rw [mem_filter] at hq ⊢
  obtain ⟨hqR, hA, hB⟩ := hq
  refine ⟨hqR, fun hv => ?_, hB⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (mem_toList.2 hv)
  have hiw : i < w :=
    lt_of_lt_of_le hi (by rw [length_toList]; exact hVal q.2 (mem_product.1 hqR).2)
  apply hA i (mem_range.2 hiw)
  rw [List.getD_eq_getElem _ _ hi, he]
theorem e_lt_smin (n D h : ℕ) : 2 * LRcost (kstar n) (D + 2) * h < smin n D h := by
  unfold smin
  have h1 : (4 : ℝ) ≤ 4 ^ (n + 1) := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 := one_le_LRcost (kstar n) (D + 2)
  have h3 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have h4 : 4 * LRcost (kstar n) (D + 2) * (h + 1) ≤ 4 ^ (n + 1) * LRcost (kstar n) (D + 2) * (h + 1) := by
    gcongr
  nlinarith
theorem e_nonneg (n D h : ℕ) : (0 : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h :=
  mul_nonneg (mul_nonneg zero_le_two (one_le_LRcost' _ _)) (Nat.cast_nonneg _)
def Few (S : Finset (ℝ^d)) (C : ℕ → Finset (ℝ^d)) (Γ' σ θ : ℝ) (r w j : ℕ) (a2 : ℝ^d) : Prop :=
  ∃ Ξ : Finset ℝ, Ξ.card ≤ w + r + r.choose 2 ∧
    (((C j).filter fun x => dist x a2 ∉ Ξ ∧ ∀ s ∈ S, dist x a2 ≠ dist x s).card : ℝ) ≤
      Γ' * (θ + r * σ)
theorem core_step3 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {l m j : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hj : j ∈ I)
    (hjl : j ≠ l) (hjm : j ≠ m) {a2 : ℝ^d} (ha2 : a2 ∈ C m) (w : ℕ) (δ θ : ℝ) (hθ : σ ≤ θ)
    (hδ : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + 1 + r) * (δ * (C j).card) ≤ θ)
    (hk : w + 1 + r ≤ kstar n) (Z : Finset (ℝ^d)) (hZ : Z ⊆ C l)
    (hcov : ∀ a1 ∈ Z, CoverShape S C w δ j a1 a2) :
    Few S C Γ' σ θ r w j a2 ∨ (Z.card : ℝ) ≤ (w + 1) * (2 * LRcost (kstar n) (D + 2) * h) := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  have he := e_lt_smin n D h
  have he0 := e_nonneg n D h
  choose! Ω hΩ Ex hExC hEx hcv using hcov
  let R : ℝ → Finset (ℝ^d) := fun t => (C j).filter fun x => dist x a2 = t ∧ ∀ s ∈ S, dist x s ≠ t
  let Zl : ℝ → Finset (ℝ^d) := fun t => Z.filter fun a1 => t ∉ Ω a1
  have hCjX : C j ⊆ X := (hF.Cne j hj).2.trans hc.subW
  have hClX : C l ⊆ X := (hF.Cne l hl).2.trans hc.subW
  have claim : ∀ t, θ ≤ ((R t).card : ℝ) → ((Zl t).card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
    intro t hRt
    refine gl_lr_or_sets n D h X hX.dim hX.half (R t) (Zl t) ((filter_subset _ _).trans hCjX)
      ((filter_subset _ _).trans (hZ.trans hClX)) (w + 1)
      (fun a1 => (insert t (Ω a1)).image (· ^ 2)) ?_ S (by rw [hc.card]; exact hk) ?_ (by linarith)
    · intro a1 ha1
      exact card_image_le.trans ((card_insert_le _ _).trans (by
        have := hΩ a1 (mem_filter.1 ha1).1; omega))
    · intro a1 ha1
      obtain ⟨ha1Z, htΩ⟩ := mem_filter.1 ha1
      rw [hc.card]
      have hEx1 : ((Ex a1).card : ℝ) ≤ δ * (C j).card := hEx a1 ha1Z
      refine le_trans (mul_le_mul_of_nonneg_left (le_trans (Nat.cast_le.2 (card_le_card ?_)) hEx1)
        (by positivity)) (hδ.trans hRt)
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hxR, hv, hps⟩ := hx
      simp only [R, mem_filter] at hxR
      obtain ⟨hxC, hxl, hxs⟩ := hxR
      rcases hcv a1 ha1Z x hxC with h1 | h1 | h1 | h1 | h1
      · exact absurd (mem_image.2 ⟨_, mem_insert_of_mem h1, by rw [dist_eq_norm]⟩) hv
      · exact absurd (hxl ▸ h1) htΩ
      · exact absurd (mem_image.2 ⟨t, mem_insert_self _ _, by rw [← dist_eq_norm, h1, hxl]⟩) hv
      · obtain ⟨s, hs, h2 | h2⟩ := h1
        · exact absurd (by rw [← dist_eq_norm, ← dist_eq_norm, h2]) (hps s hs)
        · exact absurd (h2.trans hxl) (hxs s hs)
      · exact h1
  set Λ := ((C j).image fun x => dist x a2).filter fun t => θ ≤ ((R t).card : ℝ) with hΛdef
  by_cases hΛ : w + 1 ≤ Λ.card
  · right
    obtain ⟨Λ', hΛ'sub, hΛ'c⟩ := exists_subset_card_eq hΛ
    have hZsub : Z ⊆ Λ'.biUnion Zl := by
      intro a1 ha1
      by_contra hno
      have hsub : Λ' ⊆ Ω a1 := fun t ht => by
        by_contra htΩ
        exact hno (mem_biUnion.2 ⟨t, ht, mem_filter.2 ⟨ha1, htΩ⟩⟩)
      have := card_le_card hsub
      have := hΩ a1 ha1
      omega
    calc (Z.card : ℝ) ≤ (Λ'.biUnion Zl).card := by exact_mod_cast card_le_card hZsub
      _ ≤ ∑ t ∈ Λ', ((Zl t).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _t ∈ Λ', 2 * LRcost (kstar n) (D + 2) * h :=
          sum_le_sum fun t ht => claim t (mem_filter.1 (hΛ'sub ht)).2
      _ = (w + 1) * (2 * LRcost (kstar n) (D + 2) * h) := by
          rw [sum_const, hΛ'c, nsmul_eq_mul]; push_cast; ring
  · left
    push Not at hΛ
    refine ⟨Λ ∪ Rb S a2, ?_, ?_⟩
    · have e1 := card_union_le Λ (Rb S a2)
      have e2 : (Rb S a2).card ≤ (dists S).card + (S.image (dist a2)).card := card_union_le _ _
      have e3 := card_dists_le S
      have e4 := card_image_le (s := S) (f := dist a2)
      rw [hc.card] at e3 e4
      omega
    · have hCjW : C j ⊆ W.erase a2 := fun y hy =>
        mem_erase.2 ⟨fun e => family_classes_disjoint hF hj hm hjm hy (e ▸ ha2), (hF.Cne j hj).2 hy⟩
      have hG : ((C j).filter fun x => dist x a2 ∉ Λ ∪ Rb S a2 ∧ ∀ s ∈ S, dist x a2 ≠ dist x s) ⊆
          hrSet S (C j) a2 (θ + r * σ) := by
        intro x hx
        obtain ⟨hxC, hxn, hxs⟩ := mem_filter.1 hx
        refine mem_filter.2 ⟨hxC, fun h => hxn (mem_union_right _ h), hxs, ?_⟩
        have hRl : ((R (dist x a2)).card : ℝ) < θ := by
          by_contra hh
          push Not at hh
          exact hxn (mem_union_left _ (mem_filter.2 ⟨mem_image.2 ⟨x, hxC, rfl⟩, hh⟩))
        have hlpos : 0 < dist x a2 :=
          dist_pos.2 fun e => family_classes_disjoint hF hj hm hjm hxC (e ▸ ha2)
        have hsub2 : (C j).filter (fun y => dist y a2 = dist x a2) ⊆ R (dist x a2) ∪
            S.biUnion fun s => W.filter fun y => dist y s ∈ ({dist x a2} : Finset ℝ) := by
          intro y hy
          obtain ⟨hyC, hyl⟩ := mem_filter.1 hy
          by_cases hys : ∃ s ∈ S, dist y s = dist x a2
          · obtain ⟨s, hs, hse⟩ := hys
            exact mem_union_right _ (mem_biUnion.2 ⟨s, hs,
              mem_filter.2 ⟨(hF.Cne j hj).2 hyC, mem_singleton.2 hse⟩⟩)
          · push Not at hys
            exact mem_union_left _ (mem_filter.2 ⟨hyC, hyl, hys⟩)
        have hrb := removal_bound hc {dist x a2} (by simpa using hlpos)
        rw [card_singleton, Nat.cast_one, one_mul] at hrb
        have h3 : (((C j).filter (fun y => dist y a2 = dist x a2)).card : ℝ) ≤
            (R (dist x a2)).card +
              (S.biUnion fun s => W.filter fun y => dist y s ∈ ({dist x a2} : Finset ℝ)).card := by
          exact_mod_cast (card_le_card hsub2).trans (card_union_le _ _)
        linarith
      have hr0 : (0 : ℝ) ≤ r * σ := mul_nonneg (Nat.cast_nonneg _) (by linarith [one_le_smin n D h])
      calc (((C j).filter fun x => dist x a2 ∉ Λ ∪ Rb S a2 ∧ ∀ s ∈ S, dist x a2 ≠ dist x s).card : ℝ)
          ≤ (hrSet S (C j) a2 (θ + r * σ)).card := by exact_mod_cast card_le_card hG
        _ ≤ Γ' * (θ + r * σ) := hHR a2 ((hF.Cne m hm).2 ha2) (C j) hCjW _ (by linarith)
theorem core_step4 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {m j : ℕ} (hm : m ∈ I) (hj : j ∈ I)
    (w : ℕ) (θ : ℝ) (hk : w + r + r.choose 2 + r ≤ kstar n)
    (hA : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + r + r.choose 2 + r) * (Γ' * (θ + r * σ)) ≤ (C j).card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < (C j).card) (F : Finset (ℝ^d)) (hFm : F ⊆ C m)
    (hFew : ∀ a2 ∈ F, Few S C Γ' σ θ r w j a2) :
    (F.card : ℝ) ≤ 2 * LRcost (kstar n) (D + 2) * h := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  choose! Ξ hΞc hΞ using hFew
  refine gl_lr_or_sets n D h X hX.dim hX.half (C j) F ((hF.Cne j hj).2.trans hc.subW)
    (hFm.trans ((hF.Cne m hm).2.trans hc.subW)) (w + r + r.choose 2)
    (fun a2 => (Ξ a2).image (· ^ 2)) (fun a2 ha2 => card_image_le.trans (hΞc a2 ha2)) S
    (by rw [hc.card]; exact hk) ?_ hbig
  intro a2 ha2
  rw [hc.card]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans (Nat.cast_le.2 (card_le_card ?_))
    (hΞ a2 ha2)) (by positivity)) hA
  intro x hx
  rw [mem_filter] at hx ⊢
  obtain ⟨hxC, hv, hps⟩ := hx
  exact ⟨hxC, fun h => hv (mem_image.2 ⟨_, h, by rw [dist_eq_norm]⟩),
    fun s hs h => hps s hs (by rw [← dist_eq_norm, ← dist_eq_norm, h])⟩
theorem core_cor34 {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {l m j : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hj : j ∈ I)
    (hjl : j ≠ l) (hjm : j ≠ m) (w : ℕ) (δ θ : ℝ) (hθ : σ ≤ θ)
    (hδ : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + 1 + r) * (δ * (C j).card) ≤ θ)
    (hk3 : w + 1 + r ≤ kstar n) (hk4 : w + r + r.choose 2 + r ≤ kstar n)
    (hA : 16 * (((D + 2 : ℕ) : ℝ)) ^ (w + r + r.choose 2 + r) * (Γ' * (θ + r * σ)) ≤ (C j).card)
    (hbig : 2 * LRcost (kstar n) (D + 2) * h < (C j).card)
    (Pr : ℝ^d → ℝ^d → Prop) [DecidablePred fun q : ℝ^d × ℝ^d => Pr q.1 q.2]
    (hPr : ∀ a1 ∈ C l, ∀ a2 ∈ C m, Pr a1 a2 → CoverShape S C w δ j a1 a2) :
    ((((C l ×ˢ C m).filter fun q => Pr q.1 q.2).card : ℕ) : ℝ) ≤
      2 * LRcost (kstar n) (D + 2) * h * (C l).card +
        (w + 1) * (2 * LRcost (kstar n) (D + 2) * h) * (C m).card := by
  classical
  set e := 2 * LRcost (kstar n) (D + 2) * h with hedef
  have he0 : 0 ≤ e := e_nonneg n D h
  let Z : ℝ^d → Finset (ℝ^d) := fun a2 => (C l).filter fun a1 => Pr a1 a2
  have hcount : ((C l ×ˢ C m).filter fun q => Pr q.1 q.2).card = ∑ a2 ∈ C m, (Z a2).card := by
    rw [card_filter, sum_product_right]
    exact sum_congr rfl fun a2 _ => by
      simp only [Z, card_filter]; exact sum_congr rfl fun x _ => by by_cases hp : Pr x a2 <;> simp [hp]
  set F := (C m).filter fun a2 => Few S C Γ' σ θ r w j a2 with hFdef
  have hF := core_step4 cc hm hj w θ hk4 hA hbig F (filter_subset _ _)
    (fun a2 ha2 => (mem_filter.1 ha2).2)
  have hsplit := sum_filter_add_sum_filter_not (C m) (fun a2 => Few S C Γ' σ θ r w j a2)
    (fun a2 => ((Z a2).card : ℝ))
  have h1 : ∑ a2 ∈ F, ((Z a2).card : ℝ) ≤ e * (C l).card := by
    calc ∑ a2 ∈ F, ((Z a2).card : ℝ) ≤ ∑ _a2 ∈ F, ((C l).card : ℝ) :=
          sum_le_sum fun a2 _ => by exact_mod_cast card_le_card (filter_subset _ _)
      _ = F.card * (C l).card := by rw [sum_const, nsmul_eq_mul]
      _ ≤ e * (C l).card := by gcongr
  have h2 : ∑ a2 ∈ (C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2), ((Z a2).card : ℝ) ≤
      (w + 1) * e * (C m).card := by
    calc ∑ a2 ∈ (C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2), ((Z a2).card : ℝ)
        ≤ ∑ _a2 ∈ (C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2), (w + 1) * e := by
          refine sum_le_sum fun a2 ha2 => ?_
          obtain ⟨ha2m, hnf⟩ := mem_filter.1 ha2
          rcases core_step3 cc hl hm hj hjl hjm ha2m w δ θ hθ hδ hk3 (Z a2) (filter_subset _ _)
            (fun a1 ha1 => hPr a1 (mem_filter.1 ha1).1 a2 ha2m (mem_filter.1 ha1).2) with h | h
          · exact absurd h hnf
          · exact h
      _ = ((C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2)).card * ((w + 1) * e) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (C m).card * ((w + 1) * e) := by
          have : (((C m).filter (fun a2 => ¬ Few S C Γ' σ θ r w j a2)).card : ℝ) ≤ (C m).card := by
            exact_mod_cast card_le_card (filter_subset _ _)
          have : 0 ≤ (w + 1 : ℝ) * e := by positivity
          nlinarith
      _ = (w + 1) * e * (C m).card := by ring
  have : ((((C l ×ˢ C m).filter fun q => Pr q.1 q.2).card : ℕ) : ℝ) =
      ∑ a2 ∈ C m, ((Z a2).card : ℝ) := by rw [hcount]; push_cast; rfl
  rw [this, ← hsplit]
  linarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
noncomputable def Ty (S B : Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ) (l m : ℕ) (a1 a2 : ℝ^d) : Finset ℝ :=
  dists (S ∪ B) ∪ B.image (β l) ∪ B.image (β m) ∪ S.image (dist a1) ∪ S.image (dist a2)
theorem class_point_facts {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {k : ℕ} (hk : k ∈ I) {x : ℝ^d}
    (hx : x ∈ C k) :
    (∀ y ∈ S ∪ B, ∀ y' ∈ S ∪ B, dist x y = dist x y' → y = y') ∧
      ∀ y ∈ S ∪ B, dist x y ∉ dists (S ∪ B) := by
  obtain ⟨hxSB, hxR⟩ := hF.F4 k hk x hx
  refine ⟨fun y hy y' hy' h => ?_, fun y hy h => ?_⟩
  · have hxy : x ≠ y := fun e => hxSB (e ▸ hy)
    have hxy' : x ≠ y' := fun e => hxSB (e ▸ hy')
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) x (mem_insert_self _ _) y'
      (mem_insert_of_mem hy') hxy hxy' h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 hxy'
  · obtain ⟨q, hq, hqe⟩ := mem_image.1 h
    obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
    have hxy : x ≠ y := fun e => hxSB (e ▸ hy)
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) q.1
      (mem_insert_of_mem hq1) q.2 (mem_insert_of_mem hq2) hxy hq12 hqe.symm with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxSB (h1 ▸ hq1)
    · exact hxSB (h1 ▸ hq2)
theorem coreT_rainbow {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m)
    (hPi : ∀ s ∈ S, ∀ s' ∈ S, dist a1 s ≠ dist a2 s') (hTy : dist a1 a2 ∉ Ty S B β l m a1 a2) :
    Rainbow (coreT S B a1 a2) := by
  classical
  have h12 : a1 ≠ a2 := fun e => family_classes_disjoint hF hl hm hlm ha1 (e ▸ ha2)
  obtain ⟨hinj1, hout1⟩ := class_point_facts hF hl ha1
  have hTy1 : ∀ s ∈ S, dist a1 a2 ≠ dist a1 s := fun s hs e =>
    hTy (by unfold Ty; rw [e]; exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hs)))
  have hTy2 : ∀ b ∈ B, dist a1 a2 ≠ dist a1 b := fun b hb e => hTy (by
    unfold Ty; rw [e, hF.F2 l hl a1 ha1 b hb]
    exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_image_of_mem _ hb)))))
  have hTy3 : ∀ s ∈ S, dist a1 a2 ≠ dist a2 s := fun s hs e =>
    hTy (by unfold Ty; rw [e]; exact mem_union_right _ (mem_image_of_mem _ hs))
  have hTy4 : ∀ b ∈ B, dist a1 a2 ≠ dist a2 b := fun b hb e => hTy (by
    unfold Ty; rw [e, hF.F2 m hm a2 ha2 b hb]
    exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hb))))
  have hTy5 : dist a1 a2 ∉ dists (S ∪ B) := fun h => hTy (by
    unfold Ty
    exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ h))))
  refine rainbow_insert_one _ a1 (hF.F4 m hm a2 ha2).2 ?_ ?_ ?_
  · simp only [mem_insert, not_or]; exact ⟨h12, (hF.F4 l hl a1 ha1).1⟩
  · intro y hy y' hy' h
    rcases mem_insert.1 hy with ey | hy <;> rcases mem_insert.1 hy' with ey' | hy'
    · exact ey.trans ey'.symm
    · rw [ey] at h
      rcases mem_union.1 hy' with hs | hb
      · exact absurd h (hTy1 _ hs)
      · exact absurd h (hTy2 _ hb)
    · rw [ey'] at h
      rcases mem_union.1 hy with hs | hb
      · exact absurd h.symm (hTy1 _ hs)
      · exact absurd h.symm (hTy2 _ hb)
    · exact hinj1 y hy y' hy' h
  · intro y hy hmem
    rcases mem_union.1 (dists_insert_subset _ a2 hmem) with h | h
    · rcases mem_insert.1 hy with ey | hy
      · rw [ey] at h; exact hTy5 h
      · exact hout1 y hy h
    · obtain ⟨z, hz, hze⟩ := mem_image.1 h
      rcases mem_insert.1 hy with ey | hy
      · rw [ey] at hze
        rcases mem_union.1 hz with hzS | hzB
        · exact hTy3 z hzS hze.symm
        · exact hTy4 z hzB hze.symm
      · rcases mem_union.1 hy with hyS | hyB <;> rcases mem_union.1 hz with hzS | hzB
        · exact hPi y hyS z hzS hze.symm
        · rw [hF.F2 m hm a2 ha2 z hzB] at hze
          exact hF.F5 l hl a1 ha1 y hyS m hm z hzB hze.symm
        · rw [hF.F2 l hl a1 ha1 y hyB] at hze
          exact hF.F5 m hm a2 ha2 z hzS l hl y hyB hze
        · rw [hF.F2 l hl a1 ha1 y hyB, hF.F2 m hm a2 ha2 z hzB] at hze
          exact hlm (hF.F3.1 m hm l hl z hzB y hyB hze).1.symm
theorem beta_disjoint {S W B : Finset (ℝ^d)} {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)}
    {β : ℕ → ℝ^d → ℝ} (hF : RainbowFamily S W B I C β) {l m k : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hk : k ∈ I) (hkl : k ≠ l) (hkm : k ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m)
    (hk12 : dist a1 a2 ∉ B.image (β k)) :
    Disjoint (B.image (β k)) (dists (coreT S B a1 a2)) := by
  classical
  rw [disjoint_left]
  intro v hv hvT
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
  rcases mem_union.1 (dists_coreT_subset S B a1 a2 hvT) with h | h
  · rcases mem_union.1 h with h | h
    · exact hF.F3.2 k hk b hb h
    · obtain ⟨z, hz, hze⟩ := mem_image.1 h
      rcases mem_union.1 hz with hzS | hzB
      · exact hF.F5 m hm a2 ha2 z hzS k hk b hb hze
      · rw [hF.F2 m hm a2 ha2 z hzB] at hze
        exact hkm (hF.F3.1 m hm k hk z hzB b hb hze).1.symm
  · obtain ⟨z, hz, hze⟩ := mem_image.1 h
    rcases mem_insert.1 hz with rfl | hz
    · exact hk12 (hze ▸ hv)
    rcases mem_union.1 hz with hzS | hzB
    · exact hF.F5 l hl a1 ha1 z hzS k hk b hb hze
    · rw [hF.F2 l hl a1 ha1 z hzB] at hze
      exact hkl (hF.F3.1 l hl k hk z hzB b hb hze).1.symm
theorem cov_shape {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) {l m j : ℕ} (hl : l ∈ I) (hm : m ∈ I)
    (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l) (ha2 : a2 ∈ C m) (ε : ℝ)
    (hcov : CovK S B C β ε j a1 a2) :
    CoverShape S C ((n - 2).choose 2 + (n - 4 - r)) (6 * ε) j a1 a2 := by
  classical
  obtain ⟨hn, hr, hX, hc, hσ, hΓ, hHR, hF, hBX, hB⟩ := cc
  refine ⟨dists (coreT S B a1 a2) ∪ B.image (β j), ?_, (C j).filter fun x => ¬ LamK S B β j a1 a2 x,
    filter_subset _ _, hcov.le, ?_⟩
  · have e1 := card_union_le (dists (coreT S B a1 a2)) (B.image (β j))
    have e2 := card_dists_le (coreT S B a1 a2)
    have e3 := card_image_le (s := B) (f := β j)
    rw [card_coreT hF hl hm hlm ha1 ha2, card_union_of_disjoint hF.F1.1, hc.card, hB] at e2
    rw [hB] at e3
    have : r + (n - 4 - r) + 2 = n - 2 := by omega
    rw [this] at e2
    omega
  · intro x hx
    by_cases hL : LamK S B β j a1 a2 x
    · rcases hL with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_filter.2 ⟨hx, hL⟩))))
open Classical in
theorem pair_count {n D h r : ℕ} {X S W : Finset (ℝ^d)} {σ Γ' : ℝ} {B : Finset (ℝ^d)}
    {I : Finset ℕ} {C : ℕ → Finset (ℝ^d)} {β : ℕ → ℝ^d → ℝ}
    (cc : CoreCtx n D h r X S W σ Γ' B I C β) (hI : I.card = 12) (M ε δ1 : ℝ) (hM0 : 0 < M)
    (hMk : ∀ k ∈ I, M ≤ (C k).card) (hε : 0 < ε) (hP2 : 2 * n ^ 2 * σ ≤ ε * M)
    (hδ1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M) + 3 * n ^ 2 * σ / M ≤ δ1)
    {l m : ℕ} (hl : l ∈ I) (hm : m ∈ I) (hlm : l ≠ m) {a1 a2 : ℝ^d} (ha1 : a1 ∈ C l)
    (ha2 : a2 ∈ C m) (hPi : ∀ s ∈ S, ∀ s' ∈ S, dist a1 s ≠ dist a2 s')
    (hTy : dist a1 a2 ∉ Ty S B β l m a1 a2) :
    6 ≤ (((I.erase l).erase m).filter fun j =>
          CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 j a1 a2).card +
        (((I.erase l).erase m).filter fun j => CovK S B C β ε j a1 a2).card := by
  classical
  have hF := cc.fam
  have hT := coreT_rainbow hF hl hm hlm ha1 ha2 hPi hTy
  set I2 := (I.erase l).erase m with hI2
  have hI2c : I2.card = 10 := by
    rw [hI2, card_erase_of_mem (mem_erase.2 ⟨fun e => hlm e.symm, hm⟩), card_erase_of_mem hl, hI]
  set I0 := I2.filter fun k => dist a1 a2 ∉ B.image (β k) with hI0
  have hbad : (I2.filter fun k => dist a1 a2 ∈ B.image (β k)).card ≤ 1 := by
    rw [card_le_one]
    intro k hk k' hk'
    obtain ⟨hkI, hk1⟩ := mem_filter.1 hk
    obtain ⟨hk'I, hk'1⟩ := mem_filter.1 hk'
    obtain ⟨b, hb, hbe⟩ := mem_image.1 hk1
    obtain ⟨b', hb', hbe'⟩ := mem_image.1 hk'1
    exact (hF.F3.1 k (mem_of_mem_erase (mem_of_mem_erase hkI)) k'
      (mem_of_mem_erase (mem_of_mem_erase hk'I)) b hb b' hb' (hbe.trans hbe'.symm)).1
  have hI0c : 9 ≤ I0.card := by
    have := card_filter_add_card_filter_not (s := I2) (fun k => dist a1 a2 ∈ B.image (β k))
    rw [hI2c] at this
    rw [hI0]
    omega
  have hmemI0 : ∀ k ∈ I0, k ∈ I ∧ k ≠ l ∧ k ≠ m ∧ dist a1 a2 ∉ B.image (β k) := by
    intro k hk
    obtain ⟨hk2, hk1⟩ := mem_filter.1 hk
    obtain ⟨hkm, hk2'⟩ := mem_erase.1 hk2
    obtain ⟨hkl, hkI⟩ := mem_erase.1 hk2'
    exact ⟨hkI, hkl, hkm, hk1⟩
  have hI0sub : I0 ⊆ I2 := filter_subset _ _
  set g := (I0.filter fun k =>
    CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2).card with hg
  by_cases hgc : I0.card ≤ g + 3
  · have : g ≤ (I2.filter fun j =>
        CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 j a1 a2).card :=
      card_le_card (filter_subset_filter _ hI0sub)
    omega
  · push Not at hgc
    have hall : ∀ k' ∈ I0, CovK S B C β ε k' a1 a2 := by
      intro k' hk'
      obtain ⟨hk'I, hk'l, hk'm, hk'12⟩ := hmemI0 k' hk'
      set J := (I0.erase k').filter fun k =>
        ¬ CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2 with hJ
      have hJ3 : 3 ≤ J.card := by
        have e1 := card_filter_add_card_filter_not (s := I0.erase k') (fun k =>
          CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2)
        have e2 : ((I0.erase k').filter fun k =>
            CoverShape S C ((n - 2) + (n - 2).choose 2 + (n - 4 - r)) δ1 k a1 a2).card ≤ g :=
          card_le_card (filter_subset_filter _ (erase_subset _ _))
        rw [card_erase_of_mem hk'] at e1
        rw [hJ]
        omega
      have hJI : J ⊆ I := fun k hk => (hmemI0 k (mem_of_mem_erase (mem_filter.1 hk).1)).1
      refine core_step2 hF ε hε M hM0 (hMk k' hk'I) J hJI hJ3 fun k hk => ?_
      obtain ⟨hkI0', hnG⟩ := mem_filter.1 hk
      obtain ⟨hkk', hkI0⟩ := mem_erase.1 hkI0'
      obtain ⟨hkI, hkl, hkm, hk12⟩ := hmemI0 k hkI0
      rcases core_step1 cc M ε δ1 hM0 hMk hε hP2 hδ1 hl hm hlm hkI hk'I hkl hkm hk'l hk'm hkk'
          ha1 ha2 hT (beta_disjoint hF hl hm hkI hkl hkm ha1 ha2 hk12)
          (beta_disjoint hF hl hm hk'I hk'l hk'm ha1 ha2 hk'12) with h | h
      · exact absurd h hnG
      · exact h
    have : I0.card ≤ (I2.filter fun j => CovK S B C β ε j a1 a2).card := by
      calc I0.card = (I0.filter fun j => CovK S B C β ε j a1 a2).card := by
            rw [filter_true_of_mem hall]
        _ ≤ _ := card_le_card (filter_subset_filter _ hI0sub)
    omega
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem choose_two_le_sq' (m : ℕ) : m.choose 2 ≤ m * m := by
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
theorem quad_le_six_pow (n : ℕ) (hn : 5 ≤ n) : n ^ 2 + 7 * n + 1 ≤ 6 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ 6 k]
      nlinarith
theorem kc_le_kstar (n r : ℕ) (hn : 5 ≤ n) (hr : r ≤ n) : kc n r ≤ kstar n := by
  have h0 : kc n r ≤ 3 * n ^ 2 + 7 * n + 1 := by
    show (n - 2) + (n - 2).choose 2 + (n - 4 - r) + 1 + r +
      ((n - 2) + (n - 2).choose 2 + (n - 4 - r) + 2 * r + r.choose 2) ≤ 3 * n ^ 2 + 7 * n + 1
    have h1 := choose_two_le_sq' (n - 2)
    have h2 := choose_two_le_sq' r
    have h3 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h4 : r * r ≤ n * n := Nat.mul_le_mul hr hr
    have h6 : n ^ 2 = n * n := sq n
    rw [h6]
    generalize (n - 2).choose 2 = C1 at *
    generalize r.choose 2 = C2 at *
    generalize (n - 2) * (n - 2) = P at *
    generalize r * r = R at *
    generalize n * n = Z at *
    omega
  have := quad_le_six_pow n hn
  unfold kstar
  omega
theorem params34 (E Γ' σ δ Cj K : ℝ) (a b r n : ℕ) (hE : 1 ≤ E) (hΓ : 1 ≤ Γ') (hσ : 0 ≤ σ)
    (hK : E ^ (a + b) ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (512 * Γ' * K)) (hrn : r + 1 ≤ n)
    (hM : 32 * K * Γ' * n * σ ≤ Cj) :
    σ ≤ Cj / (32 * Γ' * E ^ b) + σ ∧
      16 * E ^ a * (δ * Cj) ≤ Cj / (32 * Γ' * E ^ b) + σ ∧
      16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b) + σ + r * σ)) ≤ Cj := by
  have hEa : 1 ≤ E ^ a := one_le_pow₀ hE
  have hEb : 1 ≤ E ^ b := one_le_pow₀ hE
  have hab : E ^ a * E ^ b ≤ K := by rw [← pow_add]; exact hK
  have hK1 : 1 ≤ K := le_trans (by nlinarith) hab
  have hEbK : E ^ b ≤ K := le_trans (by nlinarith) hab
  have hn1 : (r : ℝ) + 1 ≤ n := by exact_mod_cast hrn
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hKσ : 0 ≤ 32 * K * Γ' * n * σ := by
    have : (0 : ℝ) ≤ n := by linarith
    positivity
  have hCj : 0 ≤ Cj := hKσ.trans hM
  have hpos : 0 < 32 * Γ' * E ^ b := by positivity
  refine ⟨by have := div_nonneg hCj hpos.le; linarith, ?_, ?_⟩
  · have h1 : δ * Cj ≤ Cj / (512 * Γ' * K) := by
      calc δ * Cj ≤ 1 / (512 * Γ' * K) * Cj := mul_le_mul_of_nonneg_right hδ hCj
        _ = Cj / (512 * Γ' * K) := by ring
    have h2 : 16 * E ^ a * (Cj / (512 * Γ' * K)) ≤ Cj / (32 * Γ' * E ^ b) := by
      rw [show 16 * E ^ a * (Cj / (512 * Γ' * K)) = 16 * E ^ a * Cj / (512 * Γ' * K) by ring,
        div_le_div_iff₀ (by positivity) hpos]
      have := mul_le_mul_of_nonneg_left hab (show 0 ≤ 512 * Γ' * Cj by positivity)
      nlinarith
    have h3 : 16 * E ^ a * (δ * Cj) ≤ 16 * E ^ a * (Cj / (512 * Γ' * K)) := by gcongr
    linarith
  · have h1 : 16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b))) = Cj / 2 := by
      field_simp; ring
    have h2 : 16 * E ^ b * (Γ' * (σ + r * σ)) ≤ Cj / 2 := by
      have e1 : 16 * E ^ b * (Γ' * (σ + r * σ)) = 16 * E ^ b * Γ' * ((r + 1) * σ) := by ring
      have e2 : (r + 1 : ℝ) * σ ≤ n * σ := mul_le_mul_of_nonneg_right hn1 hσ
      have e3 : 16 * E ^ b * Γ' * ((r + 1) * σ) ≤ 16 * K * Γ' * (n * σ) := by
        have : 0 ≤ (r + 1 : ℝ) * σ := by positivity
        calc 16 * E ^ b * Γ' * ((r + 1) * σ) ≤ 16 * K * Γ' * ((r + 1) * σ) := by gcongr
          _ ≤ 16 * K * Γ' * (n * σ) := by gcongr
      nlinarith
    have : 16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b) + σ + r * σ)) =
        16 * E ^ b * (Γ' * (Cj / (32 * Γ' * E ^ b))) + 16 * E ^ b * (Γ' * (σ + r * σ)) := by ring
    linarith
theorem mu_le_sigma (n D h : ℕ) (σ : ℝ) (hσ : smin n D h ≤ σ) :
    LRcost (kG n) (D + 2) * h ≤ σ := by
  have h1 := LRcost_mono (D + 2) (kG_le_kstar n)
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have h2 : LRcost (kG n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * h :=
    mul_le_mul_of_nonneg_right h1 h0
  have h3 : LRcost (kstar n) (D + 2) * h ≤ smin n D h := by
    unfold smin
    have e1 : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have e2 := one_le_LRcost (kstar n) (D + 2)
    have a1 : LRcost (kstar n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * (h + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : LRcost (kstar n) (D + 2) * (h + 1) ≤ 4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * (h + 1)) :=
      le_mul_of_one_le_left (by positivity) e1
    linarith [show 4 ^ (n + 1) * LRcost (kstar n) (D + 2) * ((h : ℝ) + 1) =
      4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * (h + 1)) by ring]
  linarith
set_option maxHeartbeats 4000000 in
open Classical in
theorem core_lemma_proved (n : ℕ) (hn : 5 ≤ n) (d D h r : ℕ) (hr : r ≤ n - 5) (X : Finset (ℝ^d))
    (hX : Ambient n D h X) (S W : Finset (ℝ^d)) (σ Γ' : ℝ) (hc : Config X S W r σ)
    (hσ : smin n D h ≤ σ) (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ')
    (B : Finset (ℝ^d)) (I : Finset ℕ) (C : ℕ → Finset (ℝ^d)) (β : ℕ → ℝ^d → ℝ)
    (hF : RainbowFamily S W B I C β) (hBX : B ⊆ X) (hB : B.card = n - 4 - r) (hI : 12 ≤ I.card)
    (hM : ∀ k ∈ I, 2 ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * ((D + 2 : ℕ) : ℝ) ^ (2 * kc n r) * σ ≤
      (C k).card) : False := by
  obtain ⟨I', hI'sub, hI'c⟩ := exists_subset_card_eq hI
  have hF' := hF.restrict hI'sub
  have cc : CoreCtx n D h r X S W σ Γ' B I' C β := ⟨hn, hr, hX, hc, hσ, hΓ', hHR, hF', hBX, hB⟩
  obtain ⟨l, hl, m, hm, hlm⟩ := one_lt_card.1 (by omega : 1 < I'.card)
  set E : ℝ := ((D + 2 : ℕ) : ℝ) with hEdef
  have hE1 : 1 ≤ E := by rw [hEdef]; exact_mod_cast (by omega : 1 ≤ D + 2)
  set K : ℝ := E ^ kc n r with hKdef
  have hK1 : 1 ≤ K := one_le_pow₀ hE1
  set p := n - 4 - r with hp
  set w1 := (n - 2) + (n - 2).choose 2 + p with hw1
  set w2 := (n - 2).choose 2 + p with hw2
  have hkc : kc n r = (w1 + 1 + r) + (w1 + r + r.choose 2 + r) := by
    simp only [kc]; omega
  have hkst := kc_le_kstar n r hn (by omega)
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  set e := 2 * LRcost (kstar n) (D + 2) * h with hedef
  have he0 : 0 ≤ e := e_nonneg n D h
  have heσ : e < σ := lt_of_lt_of_le (e_lt_smin n D h) hσ
  set G := Γ' * K with hGdef
  have hG1 : 1 ≤ G := by rw [hGdef]; nlinarith
  have hGpos : 0 < G := by linarith
  set M0 := 2 ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * E ^ (2 * kc n r) * σ with hM0def
  have hn1 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hM0G : M0 = 2 ^ 20 * 4 ^ n * n ^ 2 * G ^ 2 * σ := by
    rw [hM0def, hGdef, hKdef, pow_mul, mul_pow]; ring
  have h4n : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hbase : 2 ^ 20 * (n ^ 2 * G * σ) ≤ M0 := by
    rw [hM0G]
    have e1 : G ≤ G ^ 2 := by nlinarith
    have e2 : G ≤ 4 ^ n * G ^ 2 := le_trans e1 (le_mul_of_one_le_left (by positivity) h4n)
    have e3 : (0 : ℝ) ≤ 2 ^ 20 * n ^ 2 * σ := by positivity
    have := mul_le_mul_of_nonneg_left e2 e3
    linarith [show 2 ^ 20 * n ^ 2 * σ * G = 2 ^ 20 * ((n : ℝ) ^ 2 * G * σ) by ring,
      show 2 ^ 20 * n ^ 2 * σ * (4 ^ n * G ^ 2) = 2 ^ 20 * 4 ^ n * (n : ℝ) ^ 2 * G ^ 2 * σ by ring]
  have hnG : (0 : ℝ) ≤ n ^ 2 * G * σ := by positivity
  have hn2 : (25 : ℝ) ≤ n ^ 2 := by nlinarith
  have hσM : σ ≤ M0 := by
    have h1 : (1 : ℝ) ≤ n ^ 2 * G := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hσ0
    linarith
  have hM0pos : 0 < M0 := by linarith
  have hMk : ∀ k ∈ I', M0 ≤ (C k).card := fun k hk => hM k (hI'sub hk)
  set ε : ℝ := 1 / (3072 * G) with hεdef
  set δ1 : ℝ := 1 / (512 * G) with hδ1def
  have hε : 0 < ε := by positivity
  have hεM : ε * M0 = M0 / (3072 * G) := by rw [hεdef]; field_simp
  have hP2 : 2 * n ^ 2 * σ ≤ ε * M0 := by
    rw [hεM, le_div_iff₀ (by positivity)]
    linarith [show 2 * (n : ℝ) ^ 2 * σ * (3072 * G) = 6144 * ((n : ℝ) ^ 2 * G * σ) by ring]
  have hμ := mu_le_sigma n D h σ hσ
  have hμ0 : 0 ≤ LRcost (kG n) (D + 2) * h :=
    mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  have hδ1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M0) + 3 * n ^ 2 * σ / M0 ≤ δ1 := by
    have h4 : (4 : ℝ) ^ n = 16 * 4 ^ (n - 2) := by
      rw [show n = (n - 2) + 2 by omega, pow_add]; norm_num; ring_nf
    have h4' : (0 : ℝ) ≤ 4 ^ (n - 2) := by positivity
    have t1 : 2 * 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) / (ε * M0) ≤ 1 / (1024 * G) := by
      rw [hεM, div_div_eq_mul_div, div_le_div_iff₀ hM0pos (by positivity), hM0G, h4]
      generalize hμg : LRcost (kG n) (D + 2) * (h : ℝ) = μg at hμ hμ0 ⊢
      generalize hFg : (4 : ℝ) ^ (n - 2) = F4 at h4' ⊢
      have e1 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
      have e2 : F4 * μg * G ^ 2 ≤ F4 * σ * G ^ 2 := by
        have : 0 ≤ F4 * G ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hμ this
        linarith [show F4 * G ^ 2 * μg = F4 * μg * G ^ 2 by ring,
          show F4 * G ^ 2 * σ = F4 * σ * G ^ 2 by ring]
      have e3 : F4 * σ * G ^ 2 ≤ F4 * σ * G ^ 2 * n ^ 2 := by
        have : 0 ≤ F4 * σ * G ^ 2 := by positivity
        exact le_mul_of_one_le_right this e1
      have l : 2 * F4 * μg * (3072 * G) * (1024 * G) = 6291456 * (F4 * μg * G ^ 2) := by ring
      have r : 1 * (2 ^ 20 * (16 * F4) * n ^ 2 * G ^ 2 * σ) = 16777216 * (F4 * σ * G ^ 2 * n ^ 2) := by
        ring
      rw [l, r]
      have : 0 ≤ F4 * σ * G ^ 2 := by positivity
      linarith
    have t2 : 3 * n ^ 2 * σ / M0 ≤ 1 / (1024 * G) := by
      rw [div_le_div_iff₀ hM0pos (by positivity)]
      linarith [show 3 * (n : ℝ) ^ 2 * σ * (1024 * G) = 3072 * ((n : ℝ) ^ 2 * G * σ) by ring]
    have : 1 / (1024 * G) + 1 / (1024 * G) = δ1 := by rw [hδ1def]; field_simp; ring
    linarith
  set I2 := (I'.erase l).erase m with hI2
  have hI2c : I2.card = 10 := by
    rw [hI2, card_erase_of_mem (mem_erase.2 ⟨fun e => hlm e.symm, hm⟩), card_erase_of_mem hl, hI'c]
  have hmemI2 : ∀ j ∈ I2, j ∈ I' ∧ j ≠ l ∧ j ≠ m := by
    intro j hj
    obtain ⟨hjm, hj'⟩ := mem_erase.1 hj
    obtain ⟨hjl, hjI⟩ := mem_erase.1 hj'
    exact ⟨hjI, hjl, hjm⟩
  have hClX : C l ⊆ X := (hF'.Cne l hl).2.trans hc.subW
  have hCmX : C m ⊆ X := (hF'.Cne m hm).2.trans hc.subW
  set A : ℝ := ((C l).card : ℝ) with hAdef
  set Bm : ℝ := ((C m).card : ℝ) with hBmdef
  have hA : M0 ≤ A := hMk l hl
  have hBm : M0 ≤ Bm := hMk m hm
  have hrn : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
  have hkc3 : ∀ w, w ≤ w1 → w + 1 + r + (w + r + r.choose 2 + r) ≤ kc n r := by
    intro w hw; rw [hkc]; omega
  have hEmono : ∀ a, a ≤ kc n r → E ^ a ≤ K := fun a ha => pow_le_pow_right₀ hE1 ha
  have hCjbig : ∀ j ∈ I', 32 * K * Γ' * n * σ ≤ (C j).card := by
    intro j hj
    refine le_trans ?_ (hMk j hj)
    have : 32 * K * Γ' * n * σ ≤ 2 ^ 20 * (n ^ 2 * G * σ) := by
      rw [hGdef]
      have e1 : (n : ℝ) ≤ n ^ 2 := by nlinarith
      have : 0 ≤ K * Γ' * σ := by positivity
      nlinarith
    linarith
  have hcor : ∀ j ∈ I2, ∀ w : ℕ, w ≤ w1 → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / (512 * Γ' * K) →
      ∀ (Pr : ℝ^d → ℝ^d → Prop),
      (∀ a1 ∈ C l, ∀ a2 ∈ C m, Pr a1 a2 → CoverShape S C w δ j a1 a2) →
      ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) => Pr q.1 q.2).card : ℕ) : ℝ) ≤ e * A + (w + 1) * e * Bm := by
    intro j hj w hw δ hδ0 hδ Pr hPr
    obtain ⟨hjI, hjl, hjm⟩ := hmemI2 j hj
    obtain ⟨p1, p2, p3⟩ := params34 E Γ' σ δ (C j).card K (w + 1 + r) (w + r + r.choose 2 + r) r n
      hE1 hΓ' hσ0 (hEmono _ (hkc3 w hw)) hδ0 hδ (by omega) (hCjbig j hjI)
    exact core_cor34 cc hl hm hjI hjl hjm w δ _ p1 p2 (by have := hkc3 w hw; omega)
      (by have := hkc3 w hw; omega) p3
      (by linarith [hMk j hjI]) Pr hPr
  have hGoodj : ∀ j ∈ I2, ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CoverShape S C w1 δ1 j q.1 q.2).card : ℕ) : ℝ) ≤ e * A + (w1 + 1) * e * Bm := by
    intro j hj
    refine hcor j hj w1 le_rfl δ1 (by positivity) (by rw [hδ1def, hGdef, mul_assoc]) _ ?_
    intro a1 _ a2 _ h; exact h
  have hCovj : ∀ j ∈ I2, ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CovK S B C β ε j q.1 q.2).card : ℕ) : ℝ) ≤ e * A + (w2 + 1) * e * Bm := by
    intro j hj
    refine hcor j hj w2 (by omega) (6 * ε) (by positivity)
      (by rw [hεdef, hGdef]; field_simp; norm_num) _ ?_
    intro a1 ha1 a2 ha2 h
    exact cov_shape cc hl hm hlm ha1 ha2 ε h
  set V := (C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
    (∀ s ∈ S, ∀ s' ∈ S, dist q.1 s ≠ dist q.2 s') ∧ dist q.1 q.2 ∉ Ty S B β l m q.1 q.2 with hVdef
  set Pi := (C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) => ∃ s ∈ S, ∃ s' ∈ S, dist q.1 s = dist q.2 s' with hPidef
  have hV6 : 6 * V.card ≤ ∑ j ∈ I2, ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CoverShape S C w1 δ1 j q.1 q.2).card) + (((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
      CovK S B C β ε j q.1 q.2).card)) := by
    have h1 : ∀ q ∈ V, 6 ≤ (I2.filter fun j => CoverShape S C w1 δ1 j q.1 q.2).card +
        (I2.filter fun j => CovK S B C β ε j q.1 q.2).card := by
      intro q hq
      obtain ⟨hqp, hPi, hTy⟩ := mem_filter.1 hq
      obtain ⟨ha1, ha2⟩ := mem_product.1 hqp
      exact pair_count cc hI'c M0 ε δ1 hM0pos hMk hε hP2 hδ1 hl hm hlm ha1 ha2 hPi hTy
    calc 6 * V.card = ∑ _q ∈ V, 6 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ q ∈ V, ((I2.filter fun j => CoverShape S C w1 δ1 j q.1 q.2).card +
          (I2.filter fun j => CovK S B C β ε j q.1 q.2).card) := sum_le_sum h1
      _ = ∑ j ∈ I2, ((V.filter fun q => CoverShape S C w1 δ1 j q.1 q.2).card +
          (V.filter fun q => CovK S B C β ε j q.1 q.2).card) := by
          simp only [card_filter, sum_add_distrib]
          rw [sum_comm, sum_comm (s := V) (t := I2)]
      _ ≤ _ := by
          refine sum_le_sum fun j _ => add_le_add ?_ ?_
          · exact card_le_card (filter_subset_filter _ (filter_subset _ _))
          · exact card_le_card (filter_subset_filter _ (filter_subset _ _))
  have hVbound : 6 * (V.card : ℝ) ≤ 10 * (2 * e * A + (w1 + w2 + 2) * e * Bm) := by
    have h1 : (6 * V.card : ℝ) ≤ ∑ j ∈ I2, (((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CoverShape S C w1 δ1 j q.1 q.2).card : ℕ) : ℝ) + ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CovK S B C β ε j q.1 q.2).card : ℕ) : ℝ)) := by exact_mod_cast hV6
    have h2 : ∑ j ∈ I2, (((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CoverShape S C w1 δ1 j q.1 q.2).card : ℕ) : ℝ) + ((((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) =>
        CovK S B C β ε j q.1 q.2).card : ℕ) : ℝ)) ≤
        ∑ _j ∈ I2, ((e * A + (w1 + 1) * e * Bm) + (e * A + (w2 + 1) * e * Bm)) :=
      sum_le_sum fun j hj => add_le_add (hGoodj j hj) (hCovj j hj)
    rw [sum_const, hI2c, nsmul_eq_mul] at h2
    push_cast at h2
    nlinarith
  have hPibound : (Pi.card : ℝ) ≤ r * (r * σ) * Bm := by
    have hcount : Pi.card = ∑ a2 ∈ C m,
        ((C l).filter fun a1 => ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s').card := by
      rw [hPidef, card_filter, sum_product_right]
      exact sum_congr rfl fun a2 _ => (card_filter _ _).symm
    have hper : ∀ a2 ∈ C m, ((((C l).filter fun a1 =>
        ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s').card : ℕ) : ℝ) ≤ r * (r * σ) := by
      intro a2 ha2
      have hpos : ∀ t ∈ S.image (dist a2), 0 < t := by
        intro t ht
        obtain ⟨s, hs, rfl⟩ := mem_image.1 ht
        exact dist_pos.2 fun e => (hF'.F4 m hm a2 ha2).1 (mem_union_left _ (e ▸ hs))
      have hsub : ((C l).filter fun a1 => ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s') ⊆
          S.biUnion fun s => W.filter fun x => dist x s ∈ S.image (dist a2) := by
        intro a1 ha1
        obtain ⟨ha1C, s, hs, s', hs', he⟩ := mem_filter.1 ha1
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hF'.Cne l hl).2 ha1C,
          mem_image.2 ⟨s', hs', he.symm⟩⟩⟩
      have h1 := removal_bound hc (S.image (dist a2)) hpos
      have h2 : ((S.image (dist a2)).card : ℝ) ≤ r := by
        rw [← hc.card]; exact_mod_cast card_image_le
      have h3 : (r : ℝ) * ((S.image (dist a2)).card * σ) ≤ r * (r * σ) := by gcongr
      exact (by exact_mod_cast card_le_card hsub : (_ : ℝ) ≤ _).trans (h1.trans h3)
    rw [hcount]; push_cast
    calc ∑ a2 ∈ C m, ((((C l).filter fun a1 => ∃ s ∈ S, ∃ s' ∈ S, dist a1 s = dist a2 s').card : ℕ) : ℝ)
        ≤ ∑ _a2 ∈ C m, (r * (r * σ)) := sum_le_sum hper
      _ = r * (r * σ) * Bm := by rw [sum_const, nsmul_eq_mul, hBmdef]; ring
  set Val : ℝ^d → Finset ℝ := fun a2 =>
    (dists (S ∪ B) ∪ B.image (β l) ∪ B.image (β m) ∪ S.image (dist a2)).image (· ^ 2) with hValdef
  have hValc : ∀ a2 ∈ C m, (Val a2).card ≤ w1 := by
    intro a2 _
    refine card_image_le.trans ?_
    have e1 := card_union_le (dists (S ∪ B) ∪ B.image (β l) ∪ B.image (β m)) (S.image (dist a2))
    have e2 := card_union_le (dists (S ∪ B) ∪ B.image (β l)) (B.image (β m))
    have e3 := card_union_le (dists (S ∪ B)) (B.image (β l))
    have e4 := card_dists_le (S ∪ B)
    rw [card_union_of_disjoint hF'.F1.1, hc.card, hB] at e4
    have e5 : (r + p).choose 2 ≤ (n - 2).choose 2 := Nat.choose_le_choose 2 (by omega)
    have e6 := card_image_le (s := B) (f := β l)
    have e7 := card_image_le (s := B) (f := β m)
    have e8 := card_image_le (s := S) (f := dist a2)
    rw [hB] at e6 e7
    rw [hc.card] at e8
    omega
  have hbad : ((C l ×ˢ C m).filter fun q : (ℝ^d) × (ℝ^d) => ‖q.1 - q.2‖ ^ (2 : ℕ) ∉ Val q.2 ∧
      ∀ s ∈ S, (‖q.1 - q.2‖ ^ (2 : ℕ) : ℝ) ≠ ‖q.1 - s‖ ^ (2 : ℕ)) ⊆ V ∪ Pi := by
    intro q hq
    obtain ⟨hqp, hv, hps⟩ := mem_filter.1 hq
    have hTy : dist q.1 q.2 ∉ Ty S B β l m q.1 q.2 := by
      intro hT
      simp only [Ty, mem_union] at hT
      rcases hT with (((h1 | h1) | h1) | h1) | h1
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inl (Or.inl (Or.inl h1)),
          by rw [dist_eq_norm]⟩)
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inl (Or.inl (Or.inr h1)),
          by rw [dist_eq_norm]⟩)
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inl (Or.inr h1),
          by rw [dist_eq_norm]⟩)
      · obtain ⟨s, hs, hse⟩ := mem_image.1 h1
        exact hps s hs (by rw [← dist_eq_norm, ← dist_eq_norm, hse])
      · exact hv (mem_image.2 ⟨_, by simp only [mem_union]; exact Or.inr h1,
          by rw [dist_eq_norm]⟩)
    by_cases hPi : ∃ s ∈ S, ∃ s' ∈ S, dist q.1 s = dist q.2 s'
    · exact mem_union_right _ (mem_filter.2 ⟨hqp, hPi⟩)
    · push Not at hPi
      exact mem_union_left _ (mem_filter.2 ⟨hqp, hPi, hTy⟩)
  have hw12 : (w1 + w2 + 2 : ℝ) ≤ 3 * n ^ 2 := by
    have h1 := choose_two_le_sq' (n - 2)
    have h3 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have : w1 + w2 + 2 ≤ 3 * (n * n) := by
      rw [hw1, hw2, hp]
      generalize (n - 2).choose 2 = C1 at *
      generalize (n - 2) * (n - 2) = P at *
      have : 5 * 5 ≤ n * n := Nat.mul_le_mul hn hn
      have : 5 * n ≤ n * n := Nat.mul_le_mul_right n hn
      generalize n * n = Z at *
      omega
    have : ((w1 + w2 + 2 : ℕ) : ℝ) ≤ ((3 * (n * n) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  have hEW : E ^ (w1 + S.card) ≤ K := by rw [hc.card]; exact hEmono _ (by rw [hkc]; omega)
  have hfin := gl_lr_or_avg_sets n D h X hX.dim hX.half (C l) (C m) hClX hCmX w1 Val hValc S
    (by rw [hc.card]; rw [hkc] at hkst; omega) ?_ (by rw [← hAdef]; linarith)
  · rw [← hBmdef] at hfin
    linarith
  · rw [← hAdef, ← hBmdef]
    set bad : ℝ := (V.card : ℝ) + Pi.card with hbaddef
    have hA0 : 0 ≤ A := by linarith
    have hB0 : 0 ≤ Bm := by linarith
    have hr2 : (r : ℝ) * (r * σ) ≤ n ^ 2 * σ := by
      have : (r : ℝ) * r ≤ n * n := mul_le_mul hrn hrn (Nat.cast_nonneg _) (by linarith)
      nlinarith
    have hbadb : 6 * bad ≤ 56 * n ^ 2 * σ * (A + Bm) := by
      have e1 : e * A ≤ σ * A := mul_le_mul_of_nonneg_right heσ.le hA0
      have e2 : (w1 + w2 + 2 : ℝ) * e * Bm ≤ 3 * n ^ 2 * σ * Bm := by
        have : (w1 + w2 + 2 : ℝ) * e ≤ 3 * n ^ 2 * σ := by
          have : (0 : ℝ) ≤ w1 + w2 + 2 := by positivity
          calc (w1 + w2 + 2 : ℝ) * e ≤ (w1 + w2 + 2) * σ := by gcongr
            _ ≤ 3 * n ^ 2 * σ := by gcongr
        exact mul_le_mul_of_nonneg_right this hB0
      have e3 : r * (r * σ) * Bm ≤ n ^ 2 * σ * Bm := mul_le_mul_of_nonneg_right hr2 hB0
      have e4 : σ * A ≤ n ^ 2 * σ * A := by
        have : 0 ≤ σ * A := by positivity
        have h1 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right h1 this
        linarith [show (n : ℝ) ^ 2 * (σ * A) = n ^ 2 * σ * A by ring]
      have f1 : 0 ≤ (n : ℝ) ^ 2 * σ * A := by positivity
      have f2 : 0 ≤ (n : ℝ) ^ 2 * σ * Bm := by positivity
      rw [hbaddef]
      linarith [hVbound, hPibound]
    have hKbig : 16 * K * (56 * n ^ 2 * σ) ≤ 3 * M0 := by
      have : 16 * K * (56 * n ^ 2 * σ) ≤ 2 ^ 20 * (n ^ 2 * G * σ) := by
        rw [hGdef]
        have h0 : 0 ≤ K * n ^ 2 * σ := by positivity
        have := mul_le_mul_of_nonneg_left hΓ' h0
        linarith [show 16 * K * (56 * (n : ℝ) ^ 2 * σ) = 896 * (K * n ^ 2 * σ) by ring,
          show 2 ^ 20 * ((n : ℝ) ^ 2 * (Γ' * K) * σ) = 2 ^ 20 * (K * n ^ 2 * σ * Γ') by ring]
      linarith
    have hEW0 : 0 ≤ E ^ (w1 + S.card) := by positivity
    have hbad0 : 0 ≤ bad := by rw [hbaddef]; positivity
    refine le_trans (mul_le_mul_of_nonneg_left (c := bad) (by
      rw [hbaddef]; exact_mod_cast (card_le_card hbad).trans (card_union_le V Pi)) (by positivity)) ?_
    calc 16 * E ^ (w1 + S.card) * bad ≤ 16 * K * bad := by gcongr
      _ ≤ 16 * K * (56 * n ^ 2 * σ * (A + Bm) / 6) := by gcongr; linarith
      _ = 16 * K * (56 * n ^ 2 * σ) * (A + Bm) / 6 := by ring
      _ ≤ 3 * M0 * (A + Bm) / 6 := by gcongr
      _ = M0 * (A + Bm) / 2 := by ring
      _ ≤ A * Bm := by nlinarith [mul_nonneg hA0 (sub_nonneg.2 hBm), mul_nonneg hB0 (sub_nonneg.2 hA)]
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem choose_two_le_sq (m : ℕ) : m.choose 2 ≤ m * m := by
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
theorem ksl_le_kstar (n r p : ℕ) (hn : 5 ≤ n) (hr : r ≤ n - 5) (hp : p ≤ n - 4 - r) :
    ksl r p (Kp n r (p + 1)) ≤ kstar n := by
  unfold ksl Kp kstar
  have h1 : 3 * (12 * 6 ^ (n - 4 - r - (p + 1))) ≤ 6 ^ n := by
    have : 3 * (12 * 6 ^ (n - 4 - r - (p + 1))) = 6 ^ (n - 4 - r - (p + 1) + 2) := by
      rw [pow_add]; ring
    rw [this]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := choose_two_le_sq (r + p)
  have h3 : r + p ≤ n := by omega
  have h4 : (r + p) * (r + p) ≤ n * n := Nat.mul_le_mul h3 h3
  have h5 : 2 * p + 2 * r ≤ n * n := by nlinarith
  have h6 : n ^ 2 = n * n := sq n
  rw [h6]
  generalize 3 * (12 * 6 ^ (n - 4 - r - (p + 1))) = X at *
  generalize (r + p).choose 2 = C at *
  generalize n * n = Z at *
  generalize 6 ^ n = Y at *
  omega
theorem natCast_le_pow (A : ℝ) (hA : 2 ≤ A) (N : ℕ) : (N : ℝ) ≤ A ^ N := by
  have h1 : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
  exact h1.le.trans (pow_le_pow_left₀ (by norm_num) hA N)
theorem kc_le (n r : ℕ) (hr : r ≤ n) : kc n r ≤ 3 * n ^ 2 + 7 * n + 1 := by
  show (n - 2) + (n - 2).choose 2 + (n - 4 - r) + 1 + r +
    ((n - 2) + (n - 2).choose 2 + (n - 4 - r) + 2 * r + r.choose 2) ≤ 3 * n ^ 2 + 7 * n + 1
  have h1 := choose_two_le_sq (n - 2)
  have h2 := choose_two_le_sq r
  have h3 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h4 : r * r ≤ n * n := Nat.mul_le_mul hr hr
  have h6 : n ^ 2 = n * n := sq n
  rw [h6]
  generalize (n - 2).choose 2 = C1 at *
  generalize r.choose 2 = C2 at *
  generalize (n - 2) * (n - 2) = P at *
  generalize r * r = R at *
  generalize n * n = Z at *
  omega
def cE1 (n : ℕ) : ℕ :=
  (22 + 2 * n + n ^ 2 + 2 * (3 * n ^ 2 + 7 * n + 1)) +
    n * (2 * n * (n + 12 * 6 ^ n) + 6 + kstar n) + 2 * n * (n + 12 * 6 ^ n) + 3
theorem ratioE1_le (n D r : ℕ) (hn : 5 ≤ n) (hr : r ≤ n - 5) (Γ' : ℝ) (hΓ : 1 ≤ Γ') :
    ratioE1 n D r Γ' ≤ ((D + 2 : ℕ) : ℝ) ^ cE1 n * Γ' ^ cE1 n := by
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha2 : 2 ≤ a := by rw [ha]; push_cast; have := Nat.cast_nonneg (α := ℝ) D; linarith
  set A := a * Γ' with hA
  have hA2 : 2 ≤ A := by rw [hA]; nlinarith
  have hA1 : 1 ≤ A := by linarith
  have haA : a ≤ A := by rw [hA]; nlinarith
  have hΓA : Γ' ≤ A := by rw [hA]; nlinarith
  have mono : ∀ {p q : ℕ}, p ≤ q → A ^ p ≤ A ^ q := fun h => pow_le_pow_right₀ hA1 h
  set e0 := 22 + 2 * n + n ^ 2 + 2 * (3 * n ^ 2 + 7 * n + 1) with he0
  set N1 := 2 * n * (n + 12 * 6 ^ n) + 6 + kstar n with hN1
  have hK : ∀ p, Kp n r p ≤ 12 * 6 ^ n := fun p =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hth : ∀ p, p ≤ n - 4 - r → thInv n D r p Γ' ≤ A ^ (5 + kstar n) := by
    intro p hp
    unfold thInv
    have h16 : (16 : ℝ) ≤ A ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ A ^ 4 := pow_le_pow_left₀ (by norm_num) hA2 4
    have hak : a ^ ksl r p (Kp n r (p + 1)) ≤ A ^ kstar n :=
      (pow_le_pow_left₀ (by linarith) haA _).trans (mono (ksl_le_kstar n r p hn hr hp))
    calc 16 * Γ' * a ^ ksl r p (Kp n r (p + 1)) ≤ A ^ 4 * A * A ^ kstar n := by
          gcongr
      _ = A ^ (5 + kstar n) := by ring
  have hMsl : ∀ p, p ≤ n - 4 - r → MslHat n D r p Γ' ≤ A ^ N1 := by
    intro p hp
    unfold MslHat
    have h1 : (2 * n * (n + Kp n r (p + 1)) : ℝ) ≤ A ^ (2 * n * (n + 12 * 6 ^ n)) := by
      have := natCast_le_pow A hA2 (2 * n * (n + Kp n r (p + 1)))
      push_cast at this
      exact this.trans (mono (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hK _) _)))
    calc (2 * n * (n + Kp n r (p + 1)) : ℝ) * thInv n D r p Γ'
        ≤ A ^ (2 * n * (n + 12 * 6 ^ n)) * A ^ (5 + kstar n) :=
          mul_le_mul h1 (hth p hp) (by unfold thInv; positivity) (by positivity)
      _ ≤ A ^ N1 := by rw [← pow_add]; exact mono (by omega)
  have hcore : McoreHat n D r Γ' ≤ A ^ e0 := by
    unfold McoreHat
    have h20 : (2 : ℝ) ^ 20 ≤ A ^ 20 := pow_le_pow_left₀ (by norm_num) hA2 20
    have h4 : (4 : ℝ) ^ n ≤ A ^ (2 * n) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by nlinarith) n
    have hn2 : ((n : ℝ)) ^ 2 ≤ A ^ (n ^ 2) := by
      have := natCast_le_pow A hA2 (n ^ 2); push_cast at this; exact this
    have hG : Γ' ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by linarith) hΓA 2
    have hkc : a ^ (2 * kc n r) ≤ A ^ (2 * (3 * n ^ 2 + 7 * n + 1)) :=
      (pow_le_pow_left₀ (by linarith) haA _).trans
        (mono (Nat.mul_le_mul_left _ (kc_le n r (by omega))))
    calc (2 : ℝ) ^ 20 * 4 ^ n * n ^ 2 * Γ' ^ 2 * a ^ (2 * kc n r)
        ≤ A ^ 20 * A ^ (2 * n) * A ^ (n ^ 2) * A ^ 2 * A ^ (2 * (3 * n ^ 2 + 7 * n + 1)) := by
          gcongr
      _ = A ^ e0 := by rw [he0]; simp only [← pow_add]; ring_nf
  have haux : ∀ j, j ≤ n - 4 - r → mAux n D r Γ' j ≤ A ^ (e0 + j * N1) := by
    intro j
    induction j with
    | zero => intro _; simpa [mAux] using hcore
    | succ j ih =>
      intro hj
      simp only [mAux]
      have hN1' : 6 + kstar n ≤ N1 := by
        rw [hN1]; generalize 2 * n * (n + 12 * 6 ^ n) = Q; omega
      have hjN : e0 + (j + 1) * N1 = e0 + j * N1 + N1 := by ring
      apply max_le
      · exact (hMsl _ (by omega)).trans (mono (by rw [hjN]; omega))
      · have h1 := ih (by omega)
        have h2 := hth (n - 4 - r - (j + 1)) (by omega)
        have h0 : 0 ≤ thInv n D r (n - 4 - r - (j + 1)) Γ' := by unfold thInv; positivity
        calc 2 * thInv n D r (n - 4 - r - (j + 1)) Γ' * mAux n D r Γ' j
            ≤ A * A ^ (5 + kstar n) * A ^ (e0 + j * N1) :=
              mul_le_mul (mul_le_mul (by linarith) h2 h0 (by linarith)) h1
                (mAux_nonneg n D r Γ' hΓ j) (by positivity)
          _ = A ^ (e0 + j * N1 + 6 + kstar n) := by ring
          _ ≤ A ^ (e0 + (j + 1) * N1) := mono (by rw [hjN]; omega)
  have hm1 : mHat n D r Γ' 1 ≤ A ^ (e0 + n * N1) :=
    (haux _ (by omega)).trans (mono (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _))
  have hrest : (2 * n * (n + Kr n r) : ℝ) ≤ A ^ (2 * n * (n + 12 * 6 ^ n)) := by
    have := natCast_le_pow A hA2 (2 * n * (n + Kr n r))
    push_cast at this
    refine this.trans (mono (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _)))
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfin : ratioE1 n D r Γ' ≤ A ^ cE1 n := by
    unfold ratioE1
    set P := e0 + n * N1 + 2 * n * (n + 12 * 6 ^ n) with hP
    have e1 : A ^ (e0 + n * N1) ≤ A ^ P := mono (by omega)
    have e2 : A ^ (2 * n * (n + 12 * 6 ^ n)) ≤ A ^ P := mono (by omega)
    have e3 : A ^ cE1 n = A ^ P * A ^ 3 := by rw [← pow_add]; rfl
    have e5 : 8 ≤ A ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA2 3; norm_num at this; linarith
    have hP0 : 0 ≤ A ^ P := by positivity
    rw [e3]
    nlinarith
  calc ratioE1 n D r Γ' ≤ A ^ cE1 n := hfin
    _ = a ^ cE1 n * Γ' ^ cE1 n := by rw [hA, mul_pow]
theorem iterate_families (n : ℕ) (hn : 5 ≤ n) (d D h r : ℕ) (hr : r ≤ n - 5) (X : Finset (ℝ^d))
    (hX : Ambient n D h X) (S W : Finset (ℝ^d)) (σ Γ' : ℝ) (hc : Config X S W r σ)
    (hσ : smin n D h ≤ σ) (hΓ' : 1 ≤ Γ') (hHR : HRholds S W σ Γ') (b : ℝ^d) (hb : b ∈ W)
    (hbig : Kr n r ≤ (Big S W b (ratioE1 n D r Γ' * σ)).card) :
    ∀ p, 1 ≤ p → p ≤ n - 4 - r → ∃ (B : Finset (ℝ^d)) (I : Finset ℕ) (C : ℕ → Finset (ℝ^d))
      (β : ℕ → ℝ^d → ℝ), RainbowFamily S W B I C β ∧ B ⊆ X ∧ B.card = p ∧ I.card = Kp n r p ∧
        ∀ k ∈ I, mHat n D r Γ' p * σ ≤ (C k).card := by
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσpos : 0 < σ := by linarith
  have hm0 : ∀ p, 0 ≤ mHat n D r Γ' p := fun p => mAux_nonneg n D r Γ' hΓ' _
  intro p hp1 hpq
  induction p, hp1 using Nat.le_induction with
  | base =>
    have hK1 : Kr n r = Kp n r 1 := by unfold Kr Kp; congr 2; omega
    set τ := ratioE1 n D r Γ' * σ with hτ
    have hrn : (r : ℝ) * (r + Kr n r) ≤ n * (n + Kr n r) := by
      have : (r : ℝ) ≤ n := by exact_mod_cast (show r ≤ n by omega)
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      nlinarith
    have hn0 : (0 : ℝ) < n * (n + Kr n r) := by
      have : (5 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    have hm1 := hm0 1
    have hτbig : (r : ℝ) * (r + Kr n r) * σ < τ := by
      rw [hτ]; unfold ratioE1; nlinarith
    obtain ⟨C, β, hF, hC⟩ := initial_family X S W r σ τ hc hσpos b hb (Kr n r) hbig hτbig
    refine ⟨{b}, range (Kr n r), C, β, hF, singleton_subset_iff.2 (hc.subW hb), card_singleton b,
      by rw [card_range, hK1], ?_⟩
    intro k hk
    have := hC k hk
    have h2 : mHat n D r Γ' 1 * σ ≤ τ - r * (r + Kr n r) * σ := by
      rw [hτ]; unfold ratioE1; nlinarith
    linarith
  | succ p hp1 ih =>
    obtain ⟨B, I, C, β, hF, hBX, hB, hI, hM⟩ := ih (by omega)
    have hpq' : p < n - 4 - r := by omega
    have hstep := mHat_step n D r p Γ' hpq'
    set K := Kp n r (p + 1) with hKdef
    have hthpos : 0 < thInv n D r p Γ' := by unfold thInv; positivity
    have hMsl : 2 * n * (n + K) * σ * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r B.card K) ≤
        mHat n D r Γ' p * σ := by
      rw [hB]
      have : MslHat n D r p Γ' ≤ mHat n D r Γ' p := by rw [hstep]; exact le_max_left _ _
      unfold MslHat thInv at this
      nlinarith
    have hI6 : 6 * K ≤ I.card := by
      rw [hI, hKdef]; unfold Kp
      have : 6 * (12 * 6 ^ (n - 4 - r - (p + 1))) = 12 * 6 ^ (n - 4 - r - p) := by
        rw [show n - 4 - r - p = (n - 4 - r - (p + 1)) + 1 by omega, pow_succ]; ring
      omega
    obtain ⟨c, hcI, I', hI'I, hI'c, C', β', hC'C, hF', hC'⟩ :=
      slicing_lemma_proved n (by omega) d D h r K (by omega) (by rw [hKdef]; unfold Kp; exact Nat.one_le_iff_ne_zero.2 (by positivity))
        X hX S W σ Γ' hc hσ hΓ' hHR B I C β hF (by omega) (by omega) hI6
        (by rw [hB]; exact ksl_le_kstar n r p hn hr (by omega)) (mHat n D r Γ' p * σ) hM hMsl
    refine ⟨insert c B, I', C', β', hF', ?_, ?_, hI'c, ?_⟩
    · obtain ⟨k, hk, hck⟩ := mem_biUnion.1 hcI
      exact insert_subset (hc.subW ((hF.Cne k hk).2 hck)) hBX
    · obtain ⟨k, hk, hck⟩ := mem_biUnion.1 hcI
      have hcB : c ∉ B := fun h => (hF.F4 k hk c hck).1 (mem_union_right _ h)
      rw [card_insert_of_notMem hcB, hB]
    · intro k hk
      have h1 := hC' k hk
      rw [hB] at h1
      have h2 : 2 * thInv n D r p Γ' * mHat n D r Γ' (p + 1) ≤ mHat n D r Γ' p := by
        rw [hstep]; exact le_max_right _ _
      have h3 : mHat n D r Γ' (p + 1) * σ ≤
          mHat n D r Γ' p * σ / (2 * (16 * Γ' * ((D + 2 : ℕ) : ℝ) ^ ksl r p K)) := by
        rw [le_div_iff₀ (by positivity)]
        unfold thInv at h2
        nlinarith
      linarith
theorem theorem_E1_proved (n : ℕ) (hn : 5 ≤ n) :
    ∃ c : ℕ, ∀ (d D h r : ℕ), r ≤ n - 5 → ∀ (Γ' : ℝ), 1 ≤ Γ' →
      ∃ ratio : ℝ, 1 ≤ ratio ∧ ratio ≤ ((D + 2 : ℕ) : ℝ) ^ c * Γ' ^ c ∧
        ∀ (X : Finset (ℝ^d)), Ambient n D h X → ∀ (S W : Finset (ℝ^d)) (σ : ℝ),
          Config X S W r σ → smin n D h ≤ σ → HRholds S W σ Γ' →
          ∀ b ∈ W, (Big S W b (ratio * σ)).card < Kr n r := by
  refine ⟨cE1 n, fun d D h r hr Γ' hΓ' =>
    ⟨ratioE1 n D r Γ', ?_, ratioE1_le n D r hn hr Γ' hΓ', ?_⟩⟩
  · unfold ratioE1
    have := mAux_nonneg n D r Γ' hΓ' (n - 4 - r - 1)
    have h1 : (1 : ℝ) ≤ 2 * n * (n + Kr n r) := by
      have : (5 : ℝ) ≤ n := by exact_mod_cast hn
      have : (0 : ℝ) ≤ Kr n r := Nat.cast_nonneg _
      nlinarith
    unfold mHat
    linarith
  · intro X hX S W σ hc hσ hHR b hb
    by_contra hcon
    push Not at hcon
    obtain ⟨B, I, C, β, hF, hBX, hB, hI, hM⟩ :=
      iterate_families n hn d D h r hr X hX S W σ Γ' hc hσ hΓ' hHR b hb hcon (n - 4 - r)
        (by omega) le_rfl
    refine core_lemma_proved n hn d D h r hr X hX S W σ Γ' hc hσ hΓ' hHR B I C β hF hBX hB ?_ ?_
    · rw [hI]; unfold Kp; simp
    · intro k hk
      have := hM k hk
      rw [mHat_top] at this
      unfold McoreHat at this
      exact this
end E1088
end
section
open Finset
namespace E1088
theorem two_dist {α β : Type*} [DecidableEq α] [DecidableEq β] (P : Finset α) (Q : Finset β)
    (f : α → ℝ) (g : β → ℝ) (ρ ρ' κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2)
    (hN : ((((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2).card : ℕ) : ℝ) ≤
      κ ^ 4 * P.card * Q.card) :
    ∃ t : ℝ, (((P.filter fun x => f x ≠ ρ' ∧ f x ≠ t).card : ℕ) : ℝ) ≤ κ * P.card ∨
      (((Q.filter fun w => g w ≠ ρ ∧ g w ≠ t).card : ℕ) : ℝ) ≤ κ * Q.card := by
  classical
  set P1 := P.filter fun x => f x ≠ ρ' with hP1
  set Q1 := Q.filter fun w => g w ≠ ρ with hQ1
  set Pc : ℝ := (P.card : ℝ) with hPc
  set Qc : ℝ := (Q.card : ℝ) with hQc
  have hP0 : 0 ≤ Pc := Nat.cast_nonneg _
  have hQ0 : 0 ≤ Qc := Nat.cast_nonneg _
  by_cases ha : (P1.card : ℝ) ≤ κ * Pc
  · have hs : (P.filter fun x => f x ≠ ρ' ∧ f x ≠ ρ') ⊆ P1 := fun x hx =>
      mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.1⟩
    exact ⟨ρ', Or.inl (le_trans (by exact_mod_cast card_le_card hs) ha)⟩
  by_cases hb : (Q1.card : ℝ) ≤ κ * Qc
  · have hs : (Q.filter fun w => g w ≠ ρ ∧ g w ≠ ρ) ⊆ Q1 := fun w hw =>
      mem_filter.2 ⟨(mem_filter.1 hw).1, (mem_filter.1 hw).2.1⟩
    exact ⟨ρ, Or.inr (le_trans (by exact_mod_cast card_le_card hs) hb)⟩
  push Not at ha hb
  set a : ℝ := (P1.card : ℝ) with hadef
  set b : ℝ := (Q1.card : ℝ) with hbdef
  let c : ℝ → ℕ := fun t => (Q1.filter fun w => g w = t).card
  have hQ1ne : Q1.Nonempty := by
    rw [← card_pos]; have : (0 : ℝ) < Q1.card := lt_of_le_of_lt (by positivity) hb
    exact_mod_cast this
  obtain ⟨t0, ht0, hmax0⟩ := exists_max_image (Q1.image g) c (hQ1ne.image g)
  have hmax : ∀ t, c t ≤ c t0 := by
    intro t
    by_cases ht : t ∈ Q1.image g
    · exact hmax0 t ht
    · have : c t = 0 := by
        simp only [c, card_eq_zero, filter_eq_empty_iff]
        intro w hw hwt; exact ht (mem_image.2 ⟨w, hw, hwt⟩)
      omega
  have hfib : ∀ s, s ≠ t0 → c s + c t0 ≤ Q1.card := by
    intro s hs
    rw [← card_union_of_disjoint]
    · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    · rw [disjoint_left]; intro w h1 h2
      exact hs ((mem_filter.1 h1).2.symm.trans (mem_filter.1 h2).2)
  set m : ℕ := ∑ x ∈ P1, c (f x) with hm
  have hmN : (P1.card * Q1.card : ℕ) ≤ m +
      ((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2).card := by
    have e1 : P1.card * Q1.card = ((P1 ×ˢ Q1).filter fun q => f q.1 = g q.2).card +
        ((P1 ×ˢ Q1).filter fun q => ¬ f q.1 = g q.2).card := by
      rw [card_filter_add_card_filter_not, card_product]
    have e2 : ((P1 ×ˢ Q1).filter fun q => f q.1 = g q.2).card = m := by
      rw [hm, card_filter, sum_product]
      refine sum_congr rfl fun x _ => ?_
      simp only [c, card_filter]
      exact sum_congr rfl fun w _ => by by_cases h : f x = g w <;> simp [h, eq_comm]
    have e3 : ((P1 ×ˢ Q1).filter fun q => ¬ f q.1 = g q.2) ⊆
        ((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2) := by
      intro q hq
      obtain ⟨hq1, hne⟩ := mem_filter.1 hq
      obtain ⟨hx, hw⟩ := mem_product.1 hq1
      obtain ⟨hxP, hx'⟩ := mem_filter.1 hx
      obtain ⟨hwQ, hw'⟩ := mem_filter.1 hw
      exact mem_filter.2 ⟨mem_product.2 ⟨hxP, hwQ⟩, hx', hw', hne⟩
    have := card_le_card e3
    omega
  have hmN' : a * b ≤ (m : ℝ) + κ ^ 4 * Pc * Qc := by
    have : ((P1.card * Q1.card : ℕ) : ℝ) ≤ (m : ℝ) +
        ((((P ×ˢ Q).filter fun q => f q.1 ≠ ρ' ∧ g q.2 ≠ ρ ∧ f q.1 ≠ g q.2).card : ℕ) : ℝ) := by
      exact_mod_cast hmN
    push_cast at this
    linarith
  set cs : ℝ := (c t0 : ℝ) with hcs
  have hm1 : (m : ℝ) ≤ a * cs := by
    have : m ≤ P1.card * c t0 := by
      rw [hm]
      calc ∑ x ∈ P1, c (f x) ≤ ∑ _x ∈ P1, c t0 := sum_le_sum fun x _ => hmax _
        _ = P1.card * c t0 := by rw [sum_const, smul_eq_mul]
    rw [hadef, hcs]; exact_mod_cast this
  set u := (P.filter fun x => f x ≠ ρ' ∧ f x ≠ t0).card with hu
  have hm2 : (m : ℝ) ≤ (a - u) * cs + u * (b - cs) := by
    have hsplit := sum_filter_add_sum_filter_not P1 (fun x => f x = t0) (fun x => c (f x))
    have hu' : (P1.filter fun x => ¬ f x = t0).card = u := by
      rw [hu, hP1, filter_filter]
    have hu'' : (P1.filter fun x => f x = t0).card + u = P1.card := by
      rw [← hu', card_filter_add_card_filter_not]
    have s1 : ∑ x ∈ P1.filter (fun x => f x = t0), c (f x) =
        (P1.filter fun x => f x = t0).card * c t0 := by
      rw [sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2], sum_const, smul_eq_mul]
    have s2 : ∑ x ∈ P1.filter (fun x => ¬ f x = t0), c (f x) ≤ u * (Q1.card - c t0) := by
      calc ∑ x ∈ P1.filter (fun x => ¬ f x = t0), c (f x)
          ≤ ∑ _x ∈ P1.filter (fun x => ¬ f x = t0), (Q1.card - c t0) := by
            refine sum_le_sum fun x hx => ?_
            have := hfib (f x) (mem_filter.1 hx).2
            omega
        _ = u * (Q1.card - c t0) := by rw [sum_const, smul_eq_mul, hu']
    have hcQ : c t0 ≤ Q1.card := card_le_card (filter_subset _ _)
    have : (m : ℝ) ≤ ((P1.filter fun x => f x = t0).card : ℝ) * cs + u * (b - cs) := by
      have h1 : m ≤ (P1.filter fun x => f x = t0).card * c t0 + u * (Q1.card - c t0) := by
        rw [hm, ← hsplit, s1]; omega
      have h2 : ((u * (Q1.card - c t0) : ℕ) : ℝ) = u * (b - cs) := by
        rw [Nat.cast_mul, Nat.cast_sub hcQ]
      have h3 : (m : ℝ) ≤ (((P1.filter fun x => f x = t0).card * c t0 : ℕ) : ℝ) +
          ((u * (Q1.card - c t0) : ℕ) : ℝ) := by exact_mod_cast h1
      rw [h2] at h3; push_cast at h3; exact h3
    have hpa : ((P1.filter fun x => f x = t0).card : ℝ) = a - u := by
      rw [hadef, ← hu'']; push_cast; ring
    rw [hpa] at this; exact this
  refine ⟨t0, Or.inl ?_⟩
  by_contra hcon
  push Not at hcon
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hcs0 : (0 : ℝ) ≤ cs := Nat.cast_nonneg _
  have hcsb : cs ≤ b := by rw [hcs, hbdef]; exact_mod_cast card_le_card (filter_subset _ _)
  have haP : a ≤ Pc := by rw [hadef, hPc]; exact_mod_cast card_le_card (filter_subset _ _)
  have k1 : u * cs ≤ κ ^ 4 * Pc * Qc := by
    have : (a - u) * cs + u * (b - cs) ≤ (a - u) * cs + a * (b - cs) := by
      have hs : (P.filter fun x => f x ≠ ρ' ∧ f x ≠ t0) ⊆ P1 := fun x hx =>
        mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.1⟩
      have hua : (u : ℝ) ≤ a := by rw [hadef, hu]; exact_mod_cast card_le_card hs
      have : 0 ≤ b - cs := by linarith
      have := mul_le_mul_of_nonneg_right hua this
      linarith
    have e : (a - u) * cs + a * (b - cs) = a * b - u * cs := by ring
    linarith
  have k2 : a * b - κ ^ 4 * Pc * Qc ≤ a * cs := by linarith
  have hκP : κ * Pc < u := hcon
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  have hb0 : 0 < b := lt_of_le_of_lt (by positivity) hb
  have k3 : u * (a * b - κ ^ 4 * Pc * Qc) ≤ a * (κ ^ 4 * Pc * Qc) := by
    calc u * (a * b - κ ^ 4 * Pc * Qc) ≤ u * (a * cs) := mul_le_mul_of_nonneg_left k2 hu0
      _ = a * (u * cs) := by ring
      _ ≤ a * (κ ^ 4 * Pc * Qc) := mul_le_mul_of_nonneg_left k1 ha0.le
  have hκ2 : κ ^ 2 ≤ 1 / 4 := by nlinarith
  have hPQ0 : 0 ≤ κ ^ 2 * Pc * Qc := by positivity
  have hpos : κ ^ 2 * Pc * Qc * (1 - κ ^ 2) ≥ κ ^ 4 * Pc * Qc := by
    have := mul_nonneg hPQ0 (show 0 ≤ 1 - 2 * κ ^ 2 by linarith)
    have e : κ ^ 2 * Pc * Qc * (1 - κ ^ 2) - κ ^ 4 * Pc * Qc = κ ^ 2 * Pc * Qc * (1 - 2 * κ ^ 2) := by
      ring
    linarith
  have hab : a * b > κ * Pc * (κ * Qc) := by
    have : κ * Pc * (κ * Qc) ≤ a * (κ * Qc) := mul_le_mul_of_nonneg_right ha.le (by positivity)
    have : a * (κ * Qc) < a * b := mul_lt_mul_of_pos_left hb ha0
    linarith
  have hD : 0 < a * b - κ ^ 4 * Pc * Qc := by
    have e : κ * Pc * (κ * Qc) = κ ^ 2 * Pc * Qc := by ring
    have : κ ^ 4 * Pc * Qc ≤ κ ^ 2 * Pc * Qc := by
      have := mul_le_mul_of_nonneg_left (show κ ^ 2 ≤ 1 by linarith) hPQ0
      linarith [show κ ^ 2 * Pc * Qc * κ ^ 2 = κ ^ 4 * Pc * Qc by ring]
    linarith
  have k4 : κ * Pc * (a * b - κ ^ 4 * Pc * Qc) < a * (κ ^ 4 * Pc * Qc) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hκP hD) k3
  rcases eq_or_lt_of_le hκ0 with hκe | hκpos
  · subst hκe; norm_num at k4
  have hPpos : 0 < Pc := by
    by_contra h; push Not at h; have : Pc = 0 := le_antisymm h hP0; rw [this] at ha; linarith
  have k5 : a * b - κ ^ 4 * Pc * Qc < a * (κ ^ 3 * Qc) := by
    have hkP : 0 < κ * Pc := mul_pos hκpos hPpos
    have : κ * Pc * (a * b - κ ^ 4 * Pc * Qc) < κ * Pc * (a * (κ ^ 3 * Qc)) := by
      calc κ * Pc * (a * b - κ ^ 4 * Pc * Qc) < a * (κ ^ 4 * Pc * Qc) := k4
        _ = κ * Pc * (a * (κ ^ 3 * Qc)) := by ring
    exact lt_of_mul_lt_mul_left this hkP.le
  have k6 : a * (b - κ ^ 3 * Qc) ≥ κ * Pc * (κ * Qc * (1 - κ ^ 2)) := by
    have e1 : b - κ ^ 3 * Qc ≥ κ * Qc * (1 - κ ^ 2) := by
      linarith [show κ * Qc * (1 - κ ^ 2) = κ * Qc - κ ^ 3 * Qc by ring]
    have e2 : 0 ≤ κ * Qc * (1 - κ ^ 2) := by
      have : 0 ≤ 1 - κ ^ 2 := by nlinarith
      positivity
    calc a * (b - κ ^ 3 * Qc) ≥ a * (κ * Qc * (1 - κ ^ 2)) := mul_le_mul_of_nonneg_left e1 ha0.le
      _ ≥ κ * Pc * (κ * Qc * (1 - κ ^ 2)) := mul_le_mul_of_nonneg_right ha.le e2
  have e1 : a * (b - κ ^ 3 * Qc) = a * b - a * (κ ^ 3 * Qc) := by ring
  have e2 : κ * Pc * (κ * Qc * (1 - κ ^ 2)) = κ ^ 2 * Pc * Qc * (1 - κ ^ 2) := by ring
  linarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem rainbow_subset {A B : Finset (ℝ^d)} (h : A ⊆ B) (hB : Rainbow B) : Rainbow A :=
  fun a ha a' ha' c hc c' hc' => hB a (h ha) a' (h ha') c (h hc) c' (h hc')
theorem removal_bound' {X S W : Finset (ℝ^d)} {r : ℕ} {σ : ℝ} (hc : Config X S W r σ)
    {S' : Finset (ℝ^d)} (hS' : S' ⊆ S) (T0 : Finset ℝ) (hT0 : ∀ t ∈ T0, 0 < t) :
    ((S'.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ) ≤ S'.card * (T0.card * σ) := by
  classical
  have hsub : (S'.biUnion fun s => W.filter fun x => dist x s ∈ T0) ⊆
      S'.biUnion fun s => T0.biUnion fun t => W.filter fun x => dist x s = t := by
    intro x hx
    obtain ⟨s, hs, hx⟩ := mem_biUnion.1 hx
    obtain ⟨hxW, ht⟩ := mem_filter.1 hx
    exact mem_biUnion.2 ⟨s, hs, mem_biUnion.2 ⟨_, ht, mem_filter.2 ⟨hxW, rfl⟩⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∀ s ∈ S', ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) ≤
      T0.card * σ := by
    intro s hs
    have := card_biUnion_le (s := T0) (t := fun t => W.filter fun x => dist x s = t)
    calc ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ)
        ≤ ∑ t ∈ T0, ((W.filter fun x => dist x s = t).card : ℝ) := by exact_mod_cast this
      _ ≤ ∑ _t ∈ T0, σ := sum_le_sum fun t ht => (hc.cap s (hS' hs) t (hT0 t ht)).le
      _ = T0.card * σ := by rw [sum_const, nsmul_eq_mul]
  calc ((S'.biUnion fun s => W.filter fun x => dist x s ∈ T0).card : ℝ)
      ≤ ∑ s ∈ S', ((T0.biUnion fun t => W.filter fun x => dist x s = t).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ _s ∈ S', (T0.card * σ) := sum_le_sum h2
    _ = S'.card * (T0.card * σ) := by rw [sum_const, nsmul_eq_mul]
theorem config_point_facts {X S W : Finset (ℝ^d)} {r : ℕ} {σ : ℝ} (hc : Config X S W r σ)
    {x : ℝ^d} (hx : x ∈ W) :
    (∀ y ∈ S, ∀ y' ∈ S, dist x y = dist x y' → y = y') ∧ ∀ y ∈ S, dist x y ∉ dists S := by
  have hxS : x ∉ S := fun h => disjoint_left.1 hc.disj hx h
  have hxR := hc.ext x hx
  refine ⟨fun y hy y' hy' h => ?_, fun y hy h => ?_⟩
  · have hxy : x ≠ y := fun e => hxS (e ▸ hy)
    have hxy' : x ≠ y' := fun e => hxS (e ▸ hy')
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) x (mem_insert_self _ _) y'
      (mem_insert_of_mem hy') hxy hxy' h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd h1 hxy'
  · obtain ⟨q, hq, hqe⟩ := mem_image.1 h
    obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
    have hxy : x ≠ y := fun e => hxS (e ▸ hy)
    rcases hxR x (mem_insert_self _ _) y (mem_insert_of_mem hy) q.1
      (mem_insert_of_mem hq1) q.2 (mem_insert_of_mem hq2) hxy hq12 hqe.symm with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxS (h1 ▸ hq1)
    · exact hxS (h1 ▸ hq2)
def kA (n : ℕ) : ℕ := (n - 2).choose 2 + 3 + (n - 4)
noncomputable def QA (n D : ℕ) : ℝ := 2 ^ 27 * n ^ 2 * (((D + 2 : ℕ) : ℝ) ^ kA n) ^ 5
noncomputable def TA (S' : Finset (ℝ^d)) (a b : ℝ^d) : Finset (ℝ^d) := insert b (insert a S')
noncomputable def SmA (S' : Finset (ℝ^d)) (a b : ℝ^d) (ρ : ℝ) : Finset ℝ :=
  insert ρ (insert (dist a b) (S'.image (dist b) ∪ S'.image (dist a)))
def CoverA (S' C : Finset (ℝ^d)) (a b : ℝ^d) (ρ1 ρ2 : ℝ) (K' : ℝ) : Prop :=
  ∃ t : ℝ, 16 * K' * (((C.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
    ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤ C.card
structure StepACtx (n D h j : ℕ) (X S W S' : Finset (ℝ^d)) (σ : ℝ) (a b : ℝ^d) (ρ1 ρ2 : ℝ) :
    Prop where
  hn : 4 ≤ n
  amb : Ambient n D h X
  conf : Config X S W j σ
  hσ : smin n D h ≤ σ
  sub : S' ⊆ S
  card : S'.card = n - 4
  hb : b ∈ W
  ha : a ∈ W
  hab : a ≠ b
  hρ : ρ1 ≠ ρ2
  ρ1pos : 0 < ρ1
  ρ2pos : 0 < ρ2
  ρ1R : ρ1 ∉ Rb S b
  ρ2R : ρ2 ∉ Rb S b
  a1 : dist a b ≠ ρ1
  a2 : dist a b ≠ ρ2
  rb : Rainbow (insert a (insert b S))
  aS : ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2
section StepA
variable {n D h j : ℕ} {X S W S' : Finset (ℝ^d)} {σ : ℝ} {a b : ℝ^d} {ρ1 ρ2 : ℝ}
theorem StepACtx.notS (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {x : ℝ^d} (hx : x ∈ W) :
    x ∉ S := fun h => disjoint_left.1 cx.conf.disj hx h
theorem StepACtx.card_T (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) :
    (TA S' a b).card = n - 2 := by
  have haS : a ∉ S' := fun h => cx.notS cx.ha (cx.sub h)
  have hbS : b ∉ insert a S' := by
    simp only [mem_insert, not_or]; exact ⟨cx.hab.symm, fun h => cx.notS cx.hb (cx.sub h)⟩
  rw [TA, card_insert_of_notMem hbS, card_insert_of_notMem haS, cx.card]
  have := cx.hn; omega
theorem StepACtx.rainbow_T (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) :
    Rainbow (TA S' a b) := by
  refine rainbow_subset ?_ cx.rb
  intro y hy
  simp only [TA, mem_insert] at hy ⊢
  rcases hy with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (cx.sub h))
theorem StepACtx.T_sub (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) : TA S' a b ⊆ X := by
  intro y hy
  simp only [TA, mem_insert] at hy
  rcases hy with h | h | h
  · exact h ▸ cx.conf.subW cx.hb
  · exact h ▸ cx.conf.subW cx.ha
  · exact cx.conf.subX (cx.sub h)
theorem dists_TA_subset (S' : Finset (ℝ^d)) (a b : ℝ^d) :
    dists (TA S' a b) ⊆ dists S' ∪ S'.image (dist a) ∪ (insert a S').image (dist b) := by
  intro v hv
  rcases mem_union.1 (dists_insert_subset _ b hv) with h | h
  · rcases mem_union.1 (dists_insert_subset _ a h) with h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
  · exact mem_union_right _ h
theorem dists_subset_of_subset {A B : Finset (ℝ^d)} (h : A ⊆ B) : dists A ⊆ dists B := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hv
  obtain ⟨h1, h2, h12⟩ := mem_offDiag.1 hq
  exact mem_image.2 ⟨q, mem_offDiag.2 ⟨h h1, h h2, h12⟩, rfl⟩
theorem StepACtx.rho_notin (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ}
    (hρR : ρ ∉ Rb S b) (hab : dist a b ≠ ρ) (has : ∀ s ∈ S', dist a s ≠ ρ) :
    ρ ∉ dists (TA S' a b) := by
  intro h
  rcases mem_union.1 (dists_TA_subset S' a b h) with h | h
  · rcases mem_union.1 h with h | h
    · exact hρR (mem_union_left _ (dists_subset_of_subset cx.sub h))
    · obtain ⟨s, hs, hse⟩ := mem_image.1 h
      exact has s hs hse
  · obtain ⟨z, hz, hze⟩ := mem_image.1 h
    rcases mem_insert.1 hz with ez | hz
    · rw [ez, dist_comm] at hze; exact hab hze
    · exact hρR (mem_union_right _ (mem_image.2 ⟨z, cx.sub hz, hze⟩))
theorem StepACtx.SmA_pos (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ t ∈ SmA S' a b ρ, 0 < t := by
  intro t ht
  simp only [SmA, mem_insert, mem_union, mem_image] at ht
  rcases ht with rfl | rfl | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · exact hρ
  · exact dist_pos.2 cx.hab
  · exact dist_pos.2 fun e => cx.notS cx.hb (e ▸ cx.sub hs)
  · exact dist_pos.2 fun e => cx.notS cx.ha (e ▸ cx.sub hs)
theorem StepACtx.SmA_card (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) (ρ : ℝ) :
    (SmA S' a b ρ).card ≤ 2 * (n - 4) + 2 := by
  have e1 := card_insert_le ρ (insert (dist a b) (S'.image (dist b) ∪ S'.image (dist a)))
  have e2 := card_insert_le (dist a b) (S'.image (dist b) ∪ S'.image (dist a))
  have e3 := card_union_le (S'.image (dist b)) (S'.image (dist a))
  have e4 := card_image_le (s := S') (f := dist b)
  have e5 := card_image_le (s := S') (f := dist a)
  rw [cx.card] at e4 e5
  simp only [SmA]
  omega
theorem StepACtx.step2 (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρT : ρ ∉ dists (TA S' a b)) (hab : dist a b ≠ ρ) {x : ℝ^d} (hx : x ∈ W)
    (hxb : dist x b = ρ) (hng : ¬ Rainbow (insert x (TA S' a b))) :
    dist x a ∈ dists (TA S' a b) ∪ {ρ} ∨ (∃ s ∈ S', dist x a = dist x s) ∨
      (∃ s ∈ S', dist x s ∈ SmA S' a b ρ) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hxS := cx.notS hx
  have hxb' : x ≠ b := fun e => by rw [e, dist_self] at hxb; linarith
  have hxa : x ≠ a := fun e => hab (by rw [← e]; exact hxb)
  have hxT : x ∉ TA S' a b := by
    simp only [TA, mem_insert, not_or]; exact ⟨hxb', hxa, fun h => hxS (cx.sub h)⟩
  obtain ⟨hinjS, houtS⟩ := config_point_facts cx.conf hx
  have hxaT : dist x a ∉ dists (TA S' a b) := fun h => h1 (mem_union_left _ h)
  have hxaρ : dist x a ≠ ρ := fun h => h1 (mem_union_right _ (mem_singleton.2 h))
  have hSm : ∀ s ∈ S', dist x s ≠ ρ ∧ dist x s ≠ dist a b ∧ (∀ s' ∈ S', dist x s ≠ dist b s') ∧
      ∀ s' ∈ S', dist x s ≠ dist a s' := by
    intro s hs
    have := h3 s hs
    simp only [SmA, mem_insert, mem_union, mem_image, not_or, not_exists, not_and] at this
    obtain ⟨e1, e2, e3, e4⟩ := this
    exact ⟨e1, e2, fun s' hs' h => e3 s' hs' h.symm, fun s' hs' h => e4 s' hs' h.symm⟩
  refine hng (rainbow_insert_one _ x cx.rainbow_T hxT ?_ ?_)
  · intro y hy y' hy' hyy
    simp only [TA, mem_insert] at hy hy'
    rcases hy with ey | ey | hy <;> rcases hy' with ey' | ey' | hy'
    · exact ey.trans ey'.symm
    · rw [ey, ey', hxb] at hyy; exact absurd hyy.symm hxaρ
    · rw [ey, hxb] at hyy; exact absurd hyy.symm (hSm y' hy').1
    · rw [ey, ey', hxb] at hyy; exact absurd hyy hxaρ
    · exact ey.trans ey'.symm
    · rw [ey] at hyy; exact absurd hyy (h2 y' hy')
    · rw [ey', hxb] at hyy; exact absurd hyy (hSm y hy).1
    · rw [ey'] at hyy; exact absurd hyy.symm (h2 y hy)
    · exact hinjS y (cx.sub hy) y' (cx.sub hy') hyy
  · intro y hy hmem
    simp only [TA, mem_insert] at hy
    rcases hy with ey | ey | hy
    · rw [ey, hxb] at hmem; exact hρT hmem
    · rw [ey] at hmem; exact hxaT hmem
    · rcases mem_union.1 (dists_TA_subset S' a b hmem) with h | h
      · rcases mem_union.1 h with h | h
        · exact houtS y (cx.sub hy) (dists_subset_of_subset cx.sub h)
        · obtain ⟨s', hs', he⟩ := mem_image.1 h
          exact (hSm y hy).2.2.2 s' hs' he.symm
      · obtain ⟨z, hz, hze⟩ := mem_image.1 h
        rcases mem_insert.1 hz with ez | hz
        · rw [ez, dist_comm] at hze; exact (hSm y hy).2.1 hze.symm
        · exact (hSm y hy).2.2.1 z hz hze.symm
end StepA
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
section StepA
variable {n D h j : ℕ} {X S W S' : Finset (ℝ^d)} {σ : ℝ} {a b : ℝ^d} {ρ1 ρ2 : ℝ}
theorem StepACtx.notT (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hab : dist a b ≠ ρ) {x : ℝ^d} (hx : x ∈ W) (hxb : dist x b = ρ) : x ∉ TA S' a b := by
  have hxb' : x ≠ b := fun e => by rw [e, dist_self] at hxb; linarith
  have hxa : x ≠ a := fun e => hab (by rw [← e]; exact hxb)
  simp only [TA, mem_insert, not_or]
  exact ⟨hxb', hxa, fun h => cx.notS hx (cx.sub h)⟩
theorem four_pow_mu_le (n D h : ℕ) (σ : ℝ) (hσ : smin n D h ≤ σ) :
    4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) ≤ σ := by
  have h1 := LRcost_mono (D + 2) (kG_le_kstar n)
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hL := one_le_LRcost (kstar n) (D + 2)
  have h2 : LRcost (kG n) (D + 2) * h ≤ LRcost (kstar n) (D + 2) * h :=
    mul_le_mul_of_nonneg_right h1 h0
  have h4 : (4 : ℝ) ^ (n - 2) ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4' : (0 : ℝ) ≤ 4 ^ (n - 2) := by positivity
  have h3 : 4 ^ (n - 2) * (LRcost (kstar n) (D + 2) * h) ≤ smin n D h := by
    unfold smin
    have : 0 ≤ LRcost (kstar n) (D + 2) * h := by positivity
    have e : 4 ^ (n - 2) * (LRcost (kstar n) (D + 2) * h) ≤
        4 ^ (n + 1) * (LRcost (kstar n) (D + 2) * h) := mul_le_mul_of_nonneg_right h4 this
    nlinarith
  have := mul_le_mul_of_nonneg_left h2 h4'
  linarith
theorem StepACtx.S2 (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) (Pg Qg : Finset (ℝ^d))
    (hPg : ∀ x ∈ Pg, x ∈ W ∧ dist x b = ρ1 ∧ Rainbow (insert x (TA S' a b)))
    (hQg : ∀ w ∈ Qg, w ∈ W ∧ dist w b = ρ2 ∧ Rainbow (insert w (TA S' a b))) :
    ((((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧ dist q.1 a ≠ dist q.2 a).card
      : ℕ) : ℝ) ≤ (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) + n ^ 2 * σ) * (Pg.card + Qg.card) := by
  classical
  set T := TA S' a b with hTdef
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans cx.hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hTn : T.card + 2 = n := by rw [cx.card_T]; have := cx.hn; omega
  have hT1 : T.Nonempty := ⟨b, mem_insert_self _ _⟩
  have hPQ : Disjoint Pg Qg := by
    rw [disjoint_left]; intro x hxP hxQ
    exact cx.hρ ((hPg x hxP).2.1.symm.trans (hQg x hxQ).2.1)
  have hLD := G1_pairs n D h X T Pg Qg cx.amb.free cx.amb.dim cx.amb.half cx.T_sub hTn hT1
    (fun x hx => cx.conf.subW (hPg x hx).1) (fun x hx => cx.conf.subW (hQg x hx).1) hPQ
    (fun x hx => ⟨cx.notT cx.ρ1pos cx.a1 (hPg x hx).1 (hPg x hx).2.1, (hPg x hx).2.2⟩)
    (fun x hx => ⟨cx.notT cx.ρ2pos cx.a2 (hQg x hx).1 (hQg x hx).2.1, (hQg x hx).2.2⟩)
  let R : ℝ^d → Finset ℝ := fun w => insert ρ2 (insert (dist w a) (S'.image (dist w)))
  set Cl1 := (Qg ×ˢ Pg).filter fun q => ∃ s ∈ S', dist q.2 s ∈ R q.1 with hCl1
  set Cl2 := (Qg ×ˢ Pg).filter fun q => ∃ s ∈ S', dist q.1 s ∈ ({ρ1, dist q.2 a} : Finset ℝ)
    with hCl2
  have hsub : ((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
      dist q.1 a ≠ dist q.2 a) ⊆
      ((Qg ×ˢ Pg).filter fun q => Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1 ∪ Cl2 := by
    intro q hq
    obtain ⟨hqp, hq1, hq2, hq3⟩ := mem_filter.1 hq
    obtain ⟨hw, hx⟩ := mem_product.1 hqp
    by_cases hd : Disjoint (labels T q.1) (labels T q.2)
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hqp, hd⟩))
    rw [not_disjoint_iff] at hd
    obtain ⟨v, hvw, hvx⟩ := hd
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hvw
    obtain ⟨y', hy', he⟩ := mem_image.1 hvx
    have hwb := (hQg _ hw).2.1
    have hxb := (hPg _ hx).2.1
    have c1 : ∀ s ∈ S', dist q.2 s ∈ R q.1 → q ∈ ((Qg ×ˢ Pg).filter fun q =>
        Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1 ∪ Cl2 := fun s hs hm =>
      mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hqp, s, hs, hm⟩))
    have c2 : ∀ s ∈ S', dist q.1 s ∈ ({ρ1, dist q.2 a} : Finset ℝ) → q ∈ ((Qg ×ˢ Pg).filter
        fun q => Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1 ∪ Cl2 := fun s hs hm =>
      mem_union_right _ (mem_filter.2 ⟨hqp, s, hs, hm⟩)
    simp only [hTdef, TA, mem_insert] at hy hy'
    rcases hy with ey | ey | hy <;> rcases hy' with ey' | ey' | hy'
    · rw [ey, ey', hwb, hxb] at he; exact absurd he cx.hρ
    · rw [ey, ey', hwb] at he; exact absurd he hq2
    · rw [ey, hwb] at he; exact c1 y' hy' (by simp [R, he])
    · rw [ey, ey', hxb] at he; exact absurd he.symm hq1
    · rw [ey, ey'] at he; exact absurd he.symm hq3
    · rw [ey] at he; exact c1 y' hy' (by simp [R, he])
    · rw [ey', hxb] at he; exact c2 y hy (by simp [he])
    · rw [ey'] at he; exact c2 y hy (by simp [he])
    · exact c1 y' hy' (mem_insert_of_mem (mem_insert_of_mem (mem_image.2 ⟨y, hy, he.symm⟩)))
  have hCl1c : (Cl1.card : ℝ) ≤ Qg.card * ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ)) := by
    have hcount : Cl1.card = ∑ w ∈ Qg, (Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w).card := by
      rw [hCl1, card_filter, sum_product]
      exact sum_congr rfl fun w _ => by simp only [card_filter]
    have hper : ∀ w ∈ Qg, (((Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w).card : ℕ) : ℝ) ≤
        (n - 4 : ℕ) * ((n - 2 : ℕ) * σ) := by
      intro w hw
      obtain ⟨hwW, hwb, -⟩ := hQg w hw
      have hwa : w ≠ a := fun e => cx.a2 (by rw [← e]; exact hwb)
      have hpos : ∀ t ∈ R w, 0 < t := by
        intro t ht
        simp only [R, mem_insert, mem_image] at ht
        rcases ht with rfl | rfl | ⟨s, hs, rfl⟩
        · exact cx.ρ2pos
        · exact dist_pos.2 hwa
        · exact dist_pos.2 fun e => cx.notS hwW (e ▸ cx.sub hs)
      have hRc : (R w).card ≤ n - 2 := by
        have e1 := card_insert_le ρ2 (insert (dist w a) (S'.image (dist w)))
        have e2 := card_insert_le (dist w a) (S'.image (dist w))
        have e3 := card_image_le (s := S') (f := dist w)
        rw [cx.card] at e3
        have := cx.hn
        simp only [R]; omega
      have hs : (Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w) ⊆
          S'.biUnion fun s => W.filter fun x => dist x s ∈ R w := by
        intro x hx
        obtain ⟨hxP, s, hs, hm⟩ := mem_filter.1 hx
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hPg x hxP).1, hm⟩⟩
      have h1 := removal_bound' cx.conf cx.sub (R w) hpos
      rw [cx.card] at h1
      have h2 : ((R w).card : ℝ) ≤ (n - 2 : ℕ) := by exact_mod_cast hRc
      have h3 : ((n - 4 : ℕ) : ℝ) * ((R w).card * σ) ≤ (n - 4 : ℕ) * ((n - 2 : ℕ) * σ) := by gcongr
      exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)
    rw [hcount]; push_cast
    calc ∑ w ∈ Qg, (((Pg.filter fun x => ∃ s ∈ S', dist x s ∈ R w).card : ℕ) : ℝ)
        ≤ ∑ _w ∈ Qg, ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ) : ℝ) := sum_le_sum hper
      _ = Qg.card * ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ)) := by rw [sum_const, nsmul_eq_mul]
  have hCl2c : (Cl2.card : ℝ) ≤ Pg.card * ((n - 4 : ℕ) * (2 * σ)) := by
    have hcount : Cl2.card = ∑ x ∈ Pg,
        (Qg.filter fun w => ∃ s ∈ S', dist w s ∈ ({ρ1, dist x a} : Finset ℝ)).card := by
      rw [hCl2, card_filter, sum_product_right]
      exact sum_congr rfl fun x _ => by simp only [card_filter]
    have hper : ∀ x ∈ Pg, (((Qg.filter fun w => ∃ s ∈ S',
        dist w s ∈ ({ρ1, dist x a} : Finset ℝ)).card : ℕ) : ℝ) ≤ (n - 4 : ℕ) * (2 * σ) := by
      intro x hx
      obtain ⟨hxW, hxb, -⟩ := hPg x hx
      have hxa : x ≠ a := fun e => cx.a1 (by rw [← e]; exact hxb)
      have hpos : ∀ t ∈ ({ρ1, dist x a} : Finset ℝ), 0 < t := by
        intro t ht
        simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact cx.ρ1pos
        · exact dist_pos.2 hxa
      have hs : (Qg.filter fun w => ∃ s ∈ S', dist w s ∈ ({ρ1, dist x a} : Finset ℝ)) ⊆
          S'.biUnion fun s => W.filter fun w => dist w s ∈ ({ρ1, dist x a} : Finset ℝ) := by
        intro w hw
        obtain ⟨hwQ, s, hs, hm⟩ := mem_filter.1 hw
        exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨(hQg w hwQ).1, hm⟩⟩
      have h1 := removal_bound' cx.conf cx.sub ({ρ1, dist x a} : Finset ℝ) hpos
      rw [cx.card] at h1
      have h2 : (({ρ1, dist x a} : Finset ℝ).card : ℝ) ≤ 2 := by exact_mod_cast card_le_two
      have h3 : ((n - 4 : ℕ) : ℝ) * ((({ρ1, dist x a} : Finset ℝ).card : ℝ) * σ) ≤
          (n - 4 : ℕ) * (2 * σ) := by gcongr
      exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)
    rw [hcount]; push_cast
    calc ∑ x ∈ Pg, (((Qg.filter fun w => ∃ s ∈ S',
          dist w s ∈ ({ρ1, dist x a} : Finset ℝ)).card : ℕ) : ℝ)
        ≤ ∑ _x ∈ Pg, ((n - 4 : ℕ) * (2 * σ) : ℝ) := sum_le_sum hper
      _ = Pg.card * ((n - 4 : ℕ) * (2 * σ)) := by rw [sum_const, nsmul_eq_mul]
  have htot : ((((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
      dist q.1 a ≠ dist q.2 a).card : ℕ) : ℝ) ≤
      (((Qg ×ˢ Pg).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) +
        Cl1.card + Cl2.card := by
    have e1 := card_le_card hsub
    have e2 := card_union_le (((Qg ×ˢ Pg).filter fun q =>
      Disjoint (labels T q.1) (labels T q.2)) ∪ Cl1) Cl2
    have e3 := card_union_le ((Qg ×ˢ Pg).filter fun q =>
      Disjoint (labels T q.1) (labels T q.2)) Cl1
    have : ((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
        dist q.1 a ≠ dist q.2 a).card ≤ ((Qg ×ˢ Pg).filter fun q =>
          Disjoint (labels T q.1) (labels T q.2)).card + Cl1.card + Cl2.card := by omega
    exact_mod_cast this
  have hn1 : ((n - 4 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) ≤ n ^ 2 := by
    have : (n - 4) * (n - 2) ≤ n ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    exact_mod_cast this
  have hn2 : ((n - 4 : ℕ) : ℝ) * 2 ≤ n ^ 2 := by
    have : (n - 4) * 2 ≤ n ^ 2 := by
      rw [sq]
      have h2 : 2 * n ≤ n * n := Nat.mul_le_mul_right n (by have := cx.hn; omega)
      omega
    exact_mod_cast this
  have hP0 : (0 : ℝ) ≤ Pg.card := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ Qg.card := Nat.cast_nonneg _
  have e1 : (Qg.card : ℝ) * ((n - 4 : ℕ) * ((n - 2 : ℕ) * σ)) ≤ Qg.card * (n ^ 2 * σ) := by
    apply mul_le_mul_of_nonneg_left _ hQ0
    have := mul_le_mul_of_nonneg_right hn1 hσ0
    linarith [show ((n - 4 : ℕ) : ℝ) * ((n - 2 : ℕ) * σ) = (n - 4 : ℕ) * (n - 2 : ℕ) * σ by ring]
  have e2 : (Pg.card : ℝ) * ((n - 4 : ℕ) * (2 * σ)) ≤ Pg.card * (n ^ 2 * σ) := by
    apply mul_le_mul_of_nonneg_left _ hP0
    have := mul_le_mul_of_nonneg_right hn2 hσ0
    linarith [show ((n - 4 : ℕ) : ℝ) * (2 * σ) = (n - 4 : ℕ) * 2 * σ by ring]
  have e3 : (((Qg ×ˢ Pg).filter fun q => Disjoint (labels T q.1) (labels T q.2)).card : ℝ) ≤
      4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) * (Pg.card + Qg.card) := hLD
  nlinarith
end StepA
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
section StepA
variable {n D h j : ℕ} {X S W S' : Finset (ℝ^d)} {σ : ℝ} {a b : ℝ^d} {ρ1 ρ2 : ℝ}
open Classical in
theorem StepACtx.bad_subset (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ ρo t : ℝ}
    (hρ0 : 0 < ρ) (hρT : ρ ∉ dists (TA S' a b)) (hab : dist a b ≠ ρ)
    (hV : ∀ v, v ∈ dists (TA S' a b) ∪ {ρ} ∪ {ρo, t} → v ∈ dists (TA S' a b) ∪ {ρ1, ρ2, t})
    (C : Finset (ℝ^d)) (hC : C = W.filter fun x => dist x b = ρ) :
    (C.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
        ∀ s ∈ S', dist x a ≠ dist x s) ⊆
      ((C.filter fun x => Rainbow (insert x (TA S' a b))).filter fun x =>
          dist x a ≠ ρo ∧ dist x a ≠ t) ∪
        (C.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ) := by
  intro x hx
  obtain ⟨hxC, hxV, hxs⟩ := mem_filter.1 hx
  have hxW : x ∈ W := by rw [hC] at hxC; exact (mem_filter.1 hxC).1
  have hxb : dist x b = ρ := by rw [hC] at hxC; exact (mem_filter.1 hxC).2
  by_cases hg : Rainbow (insert x (TA S' a b))
  · refine mem_union_left _ (mem_filter.2 ⟨mem_filter.2 ⟨hxC, hg⟩, ?_, ?_⟩)
    · intro e; exact hxV (hV _ (mem_union_right _ (by simp [e])))
    · intro e; exact hxV (hV _ (mem_union_right _ (by simp [e])))
  · rcases cx.step2 hρ0 hρT hab hxW hxb hg with h1 | h1 | h1
    · exact absurd (hV _ (mem_union_left _ h1)) hxV
    · obtain ⟨s, hs, he⟩ := h1; exact absurd he (hxs s hs)
    · exact mem_union_right _ (mem_filter.2 ⟨hxC, h1⟩)
open Classical in
theorem StepACtx.Sm_count (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (C : Finset (ℝ^d)) (hC : C ⊆ W) :
    (((C.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ).card : ℕ) : ℝ) ≤ 2 * n ^ 2 * σ := by
  have hσ0 : (0 : ℝ) ≤ σ := le_trans zero_le_one ((one_le_smin n D h).trans cx.hσ)
  have hs : (C.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ) ⊆
      S'.biUnion fun s => W.filter fun x => dist x s ∈ SmA S' a b ρ := by
    intro x hx
    obtain ⟨hxC, s, hs, hm⟩ := mem_filter.1 hx
    exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hC hxC, hm⟩⟩
  have h1 := removal_bound' cx.conf cx.sub (SmA S' a b ρ) (cx.SmA_pos hρ0)
  rw [cx.card] at h1
  have h2 : ((SmA S' a b ρ).card : ℝ) ≤ 2 * (n - 4 : ℕ) + 2 := by exact_mod_cast cx.SmA_card ρ
  have hn : ((n - 4 : ℕ) : ℝ) * (2 * (n - 4 : ℕ) + 2) ≤ 2 * n ^ 2 := by
    have h4 := cx.hn
    have hm : ((n - 4 : ℕ) : ℝ) + 4 = n := by
      have : n - 4 + 4 = n := by omega
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ ((n - 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [← hm]; nlinarith
  have h3 : ((n - 4 : ℕ) : ℝ) * ((SmA S' a b ρ).card * σ) ≤ 2 * n ^ 2 * σ := by
    calc ((n - 4 : ℕ) : ℝ) * ((SmA S' a b ρ).card * σ)
        ≤ (n - 4 : ℕ) * ((2 * (n - 4 : ℕ) + 2) * σ) := by gcongr
      _ = ((n - 4 : ℕ) * (2 * (n - 4 : ℕ) + 2)) * σ := by ring
      _ ≤ 2 * n ^ 2 * σ := mul_le_mul_of_nonneg_right hn hσ0
  exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)
set_option maxHeartbeats 1000000 in
open Classical in
theorem StepACtx.cover (cx : StepACtx n D h j X S W S' σ a b ρ1 ρ2) (C1 C2 : Finset (ℝ^d))
    (hC1 : C1 = W.filter fun x => dist x b = ρ1) (hC2 : C2 = W.filter fun x => dist x b = ρ2)
    (hQ1 : QA n D * σ ≤ C1.card) (hQ2 : QA n D * σ ≤ C2.card) :
    CoverA S' C1 a b ρ1 ρ2 (((D + 2 : ℕ) : ℝ) ^ kA n) ∨
      CoverA S' C2 a b ρ1 ρ2 (((D + 2 : ℕ) : ℝ) ^ kA n) := by
  set T := TA S' a b with hTdef
  set K' : ℝ := ((D + 2 : ℕ) : ℝ) ^ kA n with hK'
  have hK1 : 1 ≤ K' := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D + 2 by omega))
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans cx.hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast cx.hn
  have hn2 : (16 : ℝ) ≤ n ^ 2 := by nlinarith
  set θ : ℝ := 2 ^ 22 * n ^ 2 * K' ^ 4 * σ with hθ
  set κ : ℝ := 1 / (32 * K') with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ2 : κ ≤ 1 / 2 := by
    rw [hκ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hQ : QA n D = 2 ^ 27 * n ^ 2 * K' ^ 5 := rfl
  have hρ1T := cx.rho_notin cx.ρ1R cx.a1 (fun s hs => (cx.aS s hs).1)
  have hρ2T := cx.rho_notin cx.ρ2R cx.a2 (fun s hs => (cx.aS s hs).2)
  have hC1W : C1 ⊆ W := by rw [hC1]; exact filter_subset _ _
  have hC2W : C2 ⊆ W := by rw [hC2]; exact filter_subset _ _
  set Pg := C1.filter fun x => Rainbow (insert x T) with hPgdef
  set Qg := C2.filter fun x => Rainbow (insert x T) with hQgdef
  have hSm1 := cx.Sm_count cx.ρ1pos C1 hC1W
  have hSm2 := cx.Sm_count cx.ρ2pos C2 hC2W
  have hK4 : 1 ≤ K' ^ 4 := one_le_pow₀ hK1
  have hK5 : K' ≤ K' ^ 5 := by
    calc K' = K' * 1 := by ring
      _ ≤ K' * K' ^ 4 := by gcongr
      _ = K' ^ 5 := by ring
  have N1 : 16 * K' * (θ + 2 * n ^ 2 * σ) ≤ QA n D * σ := by
    rw [hQ, hθ]
    have : 32 * K' * n ^ 2 * σ ≤ 2 ^ 26 * n ^ 2 * K' ^ 5 * σ := by
      have : 0 ≤ n ^ 2 * σ := by positivity
      nlinarith
    nlinarith
  have N2 : ∀ (C : Finset (ℝ^d)) (u : ℝ), QA n D * σ ≤ C.card → u ≤ κ * C.card →
      16 * K' * (u + 2 * n ^ 2 * σ) ≤ C.card := by
    intro C u hC hu
    have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    have e1 : 16 * K' * u ≤ C.card / 2 := by
      have := mul_le_mul_of_nonneg_left hu (show 0 ≤ 16 * K' by positivity)
      have e : 16 * K' * (κ * C.card) = C.card / 2 := by rw [hκ]; field_simp; ring
      linarith
    have e2 : 16 * K' * (2 * n ^ 2 * σ) ≤ C.card / 2 := by
      have : 32 * K' * n ^ 2 * σ ≤ 2 ^ 26 * n ^ 2 * K' ^ 5 * σ := by
        have : 0 ≤ n ^ 2 * σ := by positivity
        nlinarith
      rw [hQ] at hC
      nlinarith
    linarith
  have hV1 : ∀ t v, v ∈ dists T ∪ {ρ1} ∪ {ρ2, t} → v ∈ dists T ∪ {ρ1, ρ2, t} := by
    intro t v hv; simp only [mem_union, mem_insert, mem_singleton] at hv ⊢; tauto
  have hV2 : ∀ t v, v ∈ dists T ∪ {ρ2} ∪ {ρ1, t} → v ∈ dists T ∪ {ρ1, ρ2, t} := by
    intro t v hv; simp only [mem_union, mem_insert, mem_singleton] at hv ⊢; tauto
  have cov1 : ∀ t u, (((Pg.filter fun x => dist x a ≠ ρ2 ∧ dist x a ≠ t).card : ℕ) : ℝ) ≤ u →
      16 * K' * (u + 2 * n ^ 2 * σ) ≤ C1.card → CoverA S' C1 a b ρ1 ρ2 K' := by
    intro t u hu hfin
    refine ⟨t, le_trans ?_ hfin⟩
    have hs := cx.bad_subset cx.ρ1pos hρ1T cx.a1 (hV1 t) C1 hC1
    have h1 := (card_le_card hs).trans (card_union_le _ _)
    have h2 : (((C1.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
        ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤ u + 2 * n ^ 2 * σ := by
      have : (((C1.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
          ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤
          (((Pg.filter fun x => dist x a ≠ ρ2 ∧ dist x a ≠ t).card : ℕ) : ℝ) +
          (((C1.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ1).card : ℕ) : ℝ) := by
        exact_mod_cast h1
      linarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have cov2 : ∀ t u, (((Qg.filter fun x => dist x a ≠ ρ1 ∧ dist x a ≠ t).card : ℕ) : ℝ) ≤ u →
      16 * K' * (u + 2 * n ^ 2 * σ) ≤ C2.card → CoverA S' C2 a b ρ1 ρ2 K' := by
    intro t u hu hfin
    refine ⟨t, le_trans ?_ hfin⟩
    have hs := cx.bad_subset cx.ρ2pos hρ2T cx.a2 (hV2 t) C2 hC2
    have h1 := (card_le_card hs).trans (card_union_le _ _)
    have h2 : (((C2.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
        ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤ u + 2 * n ^ 2 * σ := by
      have : (((C2.filter fun x => dist x a ∉ dists (TA S' a b) ∪ {ρ1, ρ2, t} ∧
          ∀ s ∈ S', dist x a ≠ dist x s).card : ℕ) : ℝ) ≤
          (((Qg.filter fun x => dist x a ≠ ρ1 ∧ dist x a ≠ t).card : ℕ) : ℝ) +
          (((C2.filter fun x => ∃ s ∈ S', dist x s ∈ SmA S' a b ρ2).card : ℕ) : ℝ) := by
        exact_mod_cast h1
      linarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  by_cases hP : (Pg.card : ℝ) < θ
  · left
    refine cov1 0 θ (le_trans (by exact_mod_cast card_le_card (filter_subset _ _)) hP.le)
      (N1.trans hQ1)
  by_cases hQs : (Qg.card : ℝ) < θ
  · right
    refine cov2 0 θ (le_trans (by exact_mod_cast card_le_card (filter_subset _ _)) hQs.le)
      (N1.trans hQ2)
  push Not at hP hQs
  have hS2 := cx.S2 Pg Qg
    (fun x hx => by
      obtain ⟨hxC, hg⟩ := mem_filter.1 hx
      rw [hC1] at hxC; exact ⟨(mem_filter.1 hxC).1, (mem_filter.1 hxC).2, hg⟩)
    (fun x hx => by
      obtain ⟨hxC, hg⟩ := mem_filter.1 hx
      rw [hC2] at hxC; exact ⟨(mem_filter.1 hxC).1, (mem_filter.1 hxC).2, hg⟩)
  have hμ := four_pow_mu_le n D h σ cx.hσ
  have hP0 : (0 : ℝ) ≤ Pg.card := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ Qg.card := Nat.cast_nonneg _
  have hκ4θ : κ ^ 4 * θ = 4 * n ^ 2 * σ := by rw [hκ, hθ]; field_simp; ring
  have hN : ((((Qg ×ˢ Pg).filter fun q => dist q.1 a ≠ ρ1 ∧ dist q.2 a ≠ ρ2 ∧
      dist q.1 a ≠ dist q.2 a).card : ℕ) : ℝ) ≤ κ ^ 4 * Qg.card * Pg.card := by
    refine hS2.trans ?_
    have hσn : σ ≤ n ^ 2 * σ := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n ^ 2 by linarith) hσ0
      linarith
    have e1 : 4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) + n ^ 2 * σ ≤ 2 * n ^ 2 * σ := by
      linarith
    have e2 : 4 * n ^ 2 * σ * Pg.card ≤ κ ^ 4 * Qg.card * Pg.card := by
      rw [← hκ4θ]
      have : κ ^ 4 * θ ≤ κ ^ 4 * Qg.card := mul_le_mul_of_nonneg_left hQs (by positivity)
      exact mul_le_mul_of_nonneg_right this hP0
    have e3 : 4 * n ^ 2 * σ * Qg.card ≤ κ ^ 4 * Qg.card * Pg.card := by
      rw [← hκ4θ]
      have : κ ^ 4 * θ ≤ κ ^ 4 * Pg.card := mul_le_mul_of_nonneg_left hP (by positivity)
      have := mul_le_mul_of_nonneg_right this hQ0
      linarith [show κ ^ 4 * (Pg.card : ℝ) * Qg.card = κ ^ 4 * Qg.card * Pg.card by ring]
    have e4 : (4 ^ (n - 2) * (LRcost (kG n) (D + 2) * h) + n ^ 2 * σ) * (Pg.card + Qg.card) ≤
        2 * n ^ 2 * σ * (Pg.card + Qg.card) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    linarith [show 2 * (n : ℝ) ^ 2 * σ * (Pg.card + Qg.card) =
      (4 * n ^ 2 * σ * Pg.card + 4 * n ^ 2 * σ * Qg.card) / 2 by ring]
  obtain ⟨t, ht | ht⟩ := two_dist Qg Pg (fun w => dist w a) (fun x => dist x a) ρ2 ρ1 κ hκ0 hκ2 hN
  · right
    refine cov2 t (κ * Qg.card) ht (N2 C2 _ hQ2 ?_)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (filter_subset _ _)) hκ0
  · left
    refine cov1 t (κ * Pg.card) ht (N2 C1 _ hQ1 ?_)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (filter_subset _ _)) hκ0
end StepA
open Classical in
noncomputable def AsetA (S W : Finset (ℝ^d)) (b : ℝ^d) (ρ1 ρ2 : ℝ) : Finset (ℝ^d) :=
  (W.erase b).filter fun a => dist a b ≠ ρ1 ∧ dist a b ≠ ρ2 ∧ Rainbow (insert a (insert b S))
open Classical in
theorem mem_AsetA {S W : Finset (ℝ^d)} {b : ℝ^d} {ρ1 ρ2 : ℝ} {a : ℝ^d} :
    a ∈ AsetA S W b ρ1 ρ2 ↔ a ∈ W.erase b ∧ dist a b ≠ ρ1 ∧ dist a b ≠ ρ2 ∧
      Rainbow (insert a (insert b S)) := by
  unfold AsetA; exact mem_filter
open Classical in
theorem stepA {n D h j : ℕ} (hn : 4 ≤ n) (hj1 : n - 4 ≤ j) {X S W : Finset (ℝ^d)} {σ : ℝ}
    (hX : Ambient n D h X) (hc : Config X S W j σ) (hσ : smin n D h ≤ σ) (hk : kA n ≤ kstar n)
    {b : ℝ^d} (hb : b ∈ W) {ρ1 ρ2 : ℝ} (hρ : ρ1 ≠ ρ2) (hρ1 : ρ1 ∈ Big S W b (QA n D * σ))
    (hρ2 : ρ2 ∈ Big S W b (QA n D * σ)) :
    (((AsetA S W b ρ1 ρ2).card : ℕ) : ℝ) ≤
      2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ := by
  obtain ⟨S', hS'S, hS'c⟩ := exists_subset_card_eq (show n - 4 ≤ S.card by rw [hc.card]; exact hj1)
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  set e := 2 * LRcost (kstar n) (D + 2) * h with hedef
  have he0 : 0 ≤ e := e_nonneg n D h
  have heσ : e < σ := lt_of_lt_of_le (e_lt_smin n D h) hσ
  set K' : ℝ := ((D + 2 : ℕ) : ℝ) ^ kA n with hK'
  have hK1 : 1 ≤ K' := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D + 2 by omega))
  have hQ1 : (1 : ℝ) ≤ QA n D := by
    unfold QA
    have : (1 : ℝ) ≤ n ^ 2 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have : (1 : ℝ) ≤ K' ^ 5 := one_le_pow₀ hK1
    rw [← hK']
    have : (1 : ℝ) ≤ 2 ^ 27 := by norm_num
    nlinarith [mul_le_mul this ‹(1 : ℝ) ≤ n ^ 2› zero_le_one (by positivity)]
  have bigfacts : ∀ ρ ∈ Big S W b (QA n D * σ), 0 < ρ ∧ ρ ∉ Rb S b ∧
      QA n D * σ ≤ ((W.filter fun x => dist x b = ρ).card : ℝ) := by
    intro ρ hρ
    obtain ⟨himg, hR, hcard⟩ := mem_filter.1 hρ
    obtain ⟨x, hx, rfl⟩ := mem_image.1 himg
    exact ⟨dist_pos.2 (ne_of_mem_erase hx), hR, hcard⟩
  obtain ⟨hρ1p, hρ1R, hC1big⟩ := bigfacts ρ1 hρ1
  obtain ⟨hρ2p, hρ2R, hC2big⟩ := bigfacts ρ2 hρ2
  set A := AsetA S W b ρ1 ρ2 with hAdef
  set A0 := A.filter fun a => ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2 with hA0def
  have hrem : ((A.filter fun a => ¬ ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2).card : ℝ) ≤
      2 * (n - 4 : ℕ) * σ := by
    have hs : (A.filter fun a => ¬ ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2) ⊆
        S'.biUnion fun s => W.filter fun x => dist x s ∈ ({ρ1, ρ2} : Finset ℝ) := by
      intro x hx
      obtain ⟨hxA, hn'⟩ := mem_filter.1 hx
      push Not at hn'
      obtain ⟨s, hs, hse⟩ := hn'
      have hxW : x ∈ W := (mem_erase.1 (mem_AsetA.1 hxA).1).2
      refine mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hxW, ?_⟩⟩
      by_cases h1 : dist x s = ρ1
      · simp [h1]
      · simp [hse h1]
    have h1 := removal_bound' hc hS'S ({ρ1, ρ2} : Finset ℝ) (by
      intro t ht; simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl; exact hρ1p; exact hρ2p)
    rw [hS'c] at h1
    have h2 : (({ρ1, ρ2} : Finset ℝ).card : ℝ) ≤ 2 := by exact_mod_cast card_le_two
    have h3 : ((n - 4 : ℕ) : ℝ) * ((({ρ1, ρ2} : Finset ℝ).card : ℝ) * σ) ≤ 2 * (n - 4 : ℕ) * σ := by
      have : ((n - 4 : ℕ) : ℝ) * ((({ρ1, ρ2} : Finset ℝ).card : ℝ) * σ) ≤
          (n - 4 : ℕ) * (2 * σ) := by gcongr
      linarith [show ((n - 4 : ℕ) : ℝ) * (2 * σ) = 2 * (n - 4 : ℕ) * σ by ring]
    exact (by exact_mod_cast card_le_card hs : (_ : ℝ) ≤ _).trans (h1.trans h3)
  have hctx : ∀ a ∈ A0, StepACtx n D h j X S W S' σ a b ρ1 ρ2 := by
    intro a ha
    obtain ⟨haA, haS⟩ := mem_filter.1 ha
    obtain ⟨hae, ha1, ha2, harb⟩ := mem_AsetA.1 haA
    obtain ⟨hab, haW⟩ := mem_erase.1 hae
    exact ⟨hn, hX, hc, hσ, hS'S, hS'c, hb, haW, hab, hρ, hρ1p, hρ2p, hρ1R, hρ2R, ha1, ha2, harb, haS⟩
  set C1 := W.filter fun x => dist x b = ρ1 with hC1
  set C2 := W.filter fun x => dist x b = ρ2 with hC2
  have hcov : ∀ a ∈ A0, CoverA S' C1 a b ρ1 ρ2 K' ∨ CoverA S' C2 a b ρ1 ρ2 K' := fun a ha =>
    (hctx a ha).cover C1 C2 hC1 hC2 hC1big hC2big
  have hTcard : ∀ a ∈ A0, (dists (TA S' a b)).card ≤ (n - 2).choose 2 := by
    intro a ha
    have := card_dists_le (TA S' a b)
    rwa [(hctx a ha).card_T] at this
  have step5 : ∀ (C : Finset (ℝ^d)) (ρ : ℝ), C = W.filter (fun x => dist x b = ρ) →
      QA n D * σ ≤ C.card →
      ((A0.filter fun a => CoverA S' C a b ρ1 ρ2 K').card : ℝ) ≤ e := by
    intro C ρ hC hCbig
    have hCX : C ⊆ X := by rw [hC]; exact (filter_subset _ _).trans hc.subW
    set Aν := A0.filter fun a => CoverA S' C a b ρ1 ρ2 K' with hAν
    have hAνX : Aν ⊆ X := fun a ha =>
      hc.subW (mem_erase.1 (mem_AsetA.1 (mem_filter.1 (mem_filter.1 ha).1).1).1).2
    choose! tt htt using fun a (ha : a ∈ Aν) => (mem_filter.1 ha).2
    refine gl_lr_or_sets n D h X hX.dim hX.half C Aν hCX hAνX ((n - 2).choose 2 + 3)
      (fun a => (dists (TA S' a b) ∪ {ρ1, ρ2, tt a}).image (· ^ 2)) ?_ S'
      (by rw [hS'c]; unfold kA at hk; omega) ?_ ?_
    · intro a ha
      refine card_image_le.trans ((card_union_le _ _).trans ?_)
      have e1 := hTcard a (mem_filter.1 ha).1
      have e2 : ({ρ1, ρ2, tt a} : Finset ℝ).card ≤ 3 := card_le_three
      omega
    · intro a ha
      rw [hS'c]
      have hexp : (n - 2).choose 2 + 3 + (n - 4) = kA n := rfl
      rw [hexp, ← hK']
      refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (card_le_card ?_)) (by positivity))
        (htt a ha)
      intro x hx
      rw [mem_filter] at hx ⊢
      obtain ⟨hxC, hv, hps⟩ := hx
      exact ⟨hxC, fun h => hv (mem_image.2 ⟨_, h, by rw [dist_eq_norm]⟩),
        fun s hs h => hps s hs (by rw [← dist_eq_norm, ← dist_eq_norm, h])⟩
    · have : σ ≤ QA n D * σ := by nlinarith
      linarith
  have h1 := step5 C1 ρ1 hC1 hC1big
  have h2 := step5 C2 ρ2 hC2 hC2big
  have hA0sub : A0 ⊆ (A0.filter fun a => CoverA S' C1 a b ρ1 ρ2 K') ∪
      (A0.filter fun a => CoverA S' C2 a b ρ1 ρ2 K') := by
    intro a ha
    rcases hcov a ha with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨ha, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨ha, h⟩)
  have hA0 : (A0.card : ℝ) ≤ 2 * e := by
    have := (card_le_card hA0sub).trans (card_union_le _ _)
    have : (A0.card : ℝ) ≤ ((A0.filter fun a => CoverA S' C1 a b ρ1 ρ2 K').card : ℝ) +
        ((A0.filter fun a => CoverA S' C2 a b ρ1 ρ2 K').card : ℝ) := by exact_mod_cast this
    linarith
  have hsplit := card_filter_add_card_filter_not (s := A)
    (fun a => ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2)
  have : (A.card : ℝ) = A0.card +
      ((A.filter fun a => ¬ ∀ s ∈ S', dist a s ≠ ρ1 ∧ dist a s ≠ ρ2).card : ℝ) := by
    rw [hA0def]; exact_mod_cast hsplit.symm
  rw [this]
  linarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
set_option maxHeartbeats 2000000 in
theorem rplus_step (n : ℕ) (hn : 4 ≤ n) (D h : ℕ) (X : Finset (ℝ^d)) (hX : Ambient n D h X)
    (r : ℕ) (hr : n - 4 ≤ r) (Γ τ σ : ℝ) (hclaim : ClaimAt X (r + 1) Γ (smin n D h))
    (S W : Finset (ℝ^d)) (hc : Config X S W r σ) (hΓ : 0 ≤ Γ) (hσ : smin n D h ≤ σ)
    (hτ : τ = QA n D * σ) (hk : kA n ≤ kstar n) :
    (W.card : ℝ) ≤ (((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) *
      (Γ * τ + r ^ 2 * σ + (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1) := by
  have hD := hX.dim
  have hσpos : 0 < σ := lt_of_lt_of_le zero_lt_one ((one_le_smin n D h).trans hσ)
  have hQ1 : (1 : ℝ) ≤ QA n D := by
    unfold QA
    have h1 : (1 : ℝ) ≤ n ^ 2 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have h2 : (1 : ℝ) ≤ (((D + 2 : ℕ) : ℝ) ^ kA n) ^ 5 :=
      one_le_pow₀ (one_le_pow₀ (by exact_mod_cast (show 1 ≤ D + 2 by omega)))
    have h3 : (1 : ℝ) ≤ 2 ^ 27 * n ^ 2 := by nlinarith
    nlinarith
  have hτσ : σ ≤ τ := by rw [hτ]; nlinarith
  have he0 := e_nonneg n D h
  have hτ' := hτσ
  classical
  let J := Fin 2 ⊕ (S ⊕ (S ⊕ dists S))
  have hJ : Fintype.card J = 2 + 2 * r + (dists S).card := by
    simp only [J, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hc.card]; ring
  let lam : ℝ^d → Fin 2 → ℝ := fun b i =>
    if h : (i : ℕ) < (Big S W b τ).card then ((Big S W b τ).equivFin.symm ⟨i, h⟩ : ℝ) else 0
  let f : J → ℝ^d → ℝ := fun k b => match k with
    | Sum.inl i => if (i : ℕ) < (Big S W b τ).card then lam b i ^ 2 else -1
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl s)) => dist b s ^ 2
    | Sum.inr (Sum.inr (Sum.inr δ)) => (δ : ℝ) ^ 2
  let g : J → ℝ^d → ℝ := fun k y => match k with
    | Sum.inr (Sum.inl s) => ‖y - s‖ ^ 2
    | _ => 0
  let F : ℝ^d → ℝ^d → ℝ := fun b y => ∏ k : J, (‖b - y‖ ^ 2 - f k b - g k y)
  have hlam_mem : ∀ b (i : Fin 2) (h : (i : ℕ) < (Big S W b τ).card), lam b i ∈ Big S W b τ := by
    intro b i h; simp only [lam, dif_pos h]; exact Finset.coe_mem _
  have hlam_surj : ∀ b ∈ W, (Big S W b τ).card ≤ 2 → ∀ l ∈ Big S W b τ, ∃ i : Fin 2,
      (i : ℕ) < (Big S W b τ).card ∧ lam b i = l := by
    intro b hb hB l hl
    set j := (Big S W b τ).equivFin ⟨l, hl⟩
    refine ⟨⟨j, lt_of_lt_of_le j.2 hB⟩, j.2, ?_⟩
    simp only [lam, dif_pos j.2]
    simp [j]
  have hBig_pos : ∀ b l, l ∈ Big S W b τ → 0 < l := by
    intro b l hl
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 hl).1
    exact dist_pos.2 (ne_of_mem_erase hx)
  have hWS : ∀ x ∈ W, x ∉ S := fun x hx hxS => disjoint_left.1 hc.disj hx hxS
  have hWX : ∀ x ∈ W, x ∈ X := fun x hx => hc.subW hx
  set Δ := ⌊Γ * τ + r ^ 2 * σ + (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ)⌋₊ with hΔ
  have hrank : rankOn F W W ≤ (D + 2) ^ (2 + 2 * r + (dists S).card) := by
    unfold rankOn
    have h1 := rank_finset_prod_le (Finset.univ : Finset J) (fun k => Matrix.of fun (i : W) (j : W) =>
      ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j)
    refine h1.trans ?_
    calc ∏ k ∈ (Finset.univ : Finset J), (Matrix.of fun (i : W) (j : W) =>
          ‖(i : ℝ^d) - j‖ ^ 2 - f k i - g k j).rank
        ≤ ∏ _k ∈ (Finset.univ : Finset J), (D + 2) := Finset.prod_le_prod' fun k _ =>
          rank_sqdist_le_affine X D hD (fun i : W => (i : ℝ^d)) (fun j : W => (j : ℝ^d))
            (fun i => hWX _ i.2) (fun j => hWX _ j.2) _ _
      _ = (D + 2) ^ (2 + 2 * r + (dists S).card) := by
          rw [Finset.prod_const, Finset.card_univ, hJ]
  have hdiag : ∀ b ∈ W, F b b ≠ 0 := by
    intro b hb
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_sub]
    rcases k with i | s | s | δ
    · simp only [f, g]
      split_ifs with h
      · have := hBig_pos b _ (hlam_mem b i h)
        intro h0; nlinarith
      · norm_num
    · simp only [f, g, neg_zero, zero_sub, neg_ne_zero]
      have : b ≠ (s : ℝ^d) := fun e => hWS b hb (e ▸ s.2)
      have := norm_pos_iff.2 (sub_ne_zero.2 this)
      positivity
    · simp only [f, g, sub_zero, neg_ne_zero]
      have : b ≠ (s : ℝ^d) := fun e => hWS b hb (e ▸ s.2)
      have := dist_pos.2 this; positivity
    · simp only [f, g, sub_zero, neg_ne_zero]
      have := pos_of_mem_dists δ.2; positivity
  have hsurv : ∀ b ∈ W, #(W.filter fun x => x ≠ b ∧ F b x ≠ 0) ≤ Δ := by
    intro b hb
    by_cases hB2 : (Big S W b τ).card ≤ 2
    · set Sv := W.filter fun x => x ≠ b ∧ F b x ≠ 0
      set Cls := (S ×ˢ S).biUnion fun q => W.filter fun x => dist x q.1 = dist b q.2
      set W' := (W.erase b).filter fun x =>
        Rainbow (insert x (insert b S)) ∧ dist x b ∉ Big S W b τ
      have hsub : Sv ⊆ Cls ∪ W' := by
        intro x hx
        obtain ⟨hxW, hxb, hF⟩ := mem_filter.1 hx
        have hfac : ∀ k : J, ‖b - x‖ ^ 2 - f k b - g k x ≠ 0 := fun k =>
          Finset.prod_ne_zero_iff.1 hF k (Finset.mem_univ _)
        have hbx : ‖b - x‖ = dist x b := by rw [← dist_eq_norm, dist_comm]
        by_cases hcl : x ∈ Cls
        · exact mem_union_left _ hcl
        refine mem_union_right _ (mem_filter.2 ⟨mem_erase.2 ⟨hxb, hxW⟩, ?_, ?_⟩)
        · refine rainbow_insert_insert S b x (hc.ext b hb) (hc.ext x hxW) ?_ ?_ ?_ ?_
          · intro s hs s' hs' h
            exact hcl (mem_biUnion.2 ⟨(s, s'), mem_product.2 ⟨hs, hs'⟩, mem_filter.2 ⟨hxW, h⟩⟩)
          · intro s hs h
            have := hfac (Sum.inr (Sum.inr (Sum.inl ⟨s, hs⟩)))
            simp only [f, g, sub_zero] at this
            rw [hbx] at this
            exact ne_of_sq_sub_ne this h
          · intro s hs h
            have := hfac (Sum.inr (Sum.inl ⟨s, hs⟩))
            simp only [f, g, sub_zero] at this
            rw [hbx, ← dist_eq_norm] at this
            exact ne_of_sq_sub_ne this h
          · intro s hs s' hs' hne h
            have := hfac (Sum.inr (Sum.inr (Sum.inr ⟨dist s s', mem_dists hs hs' hne⟩)))
            simp only [f, g, sub_zero] at this
            rw [hbx] at this
            exact ne_of_sq_sub_ne this h
        · intro hl
          obtain ⟨i, hi, hli⟩ := hlam_surj b hb hB2 _ hl
          have := hfac (Sum.inl i)
          simp only [f, g, sub_zero, if_pos hi] at this
          rw [hbx, hli] at this
          exact this (by ring)
      have hCls : (#Cls : ℝ) ≤ r ^ 2 * σ := by
        have h1 : #Cls ≤ ∑ q ∈ S ×ˢ S, #(W.filter fun x => dist x q.1 = dist b q.2) :=
          card_biUnion_le
        have h2 : ∀ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) ≤ σ := by
          intro q hq
          obtain ⟨hq1, hq2⟩ := mem_product.1 hq
          have hpos : 0 < dist b q.2 := dist_pos.2 fun e => hWS b hb (e ▸ hq2)
          exact (hc.cap q.1 hq1 _ hpos).le
        calc (#Cls : ℝ) ≤ ∑ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) := by
              exact_mod_cast h1
          _ ≤ ∑ _q ∈ S ×ˢ S, σ := sum_le_sum h2
          _ = r ^ 2 * σ := by rw [sum_const, card_product, hc.card, nsmul_eq_mul]; push_cast; ring
      have hconf' : Config X (insert b S) W' (r + 1) τ := by
        refine ⟨insert_subset (hWX b hb) hc.subX, hc.ext b hb, ?_, ?_, ?_, ?_, ?_⟩
        · rw [card_insert_of_notMem (hWS b hb), hc.card]
        · exact (filter_subset _ _).trans ((erase_subset _ _).trans hc.subW)
        · rw [disjoint_left]
          intro x hx hxi
          obtain ⟨hxe, -⟩ := mem_filter.1 hx
          rcases mem_insert.1 hxi with rfl | hxS
          · exact (mem_erase.1 hxe).1 rfl
          · exact hWS x (mem_erase.1 hxe).2 hxS
        · intro x hx; exact (mem_filter.1 hx).2.1
        · intro s hs t ht
          have hsubW : W' ⊆ W := (filter_subset _ _).trans (erase_subset _ _)
          rcases mem_insert.1 hs with rfl | hsS
          ·
            by_cases hne : (W'.filter fun x => dist x s = t).Nonempty
            · obtain ⟨x0, hx0⟩ := hne
              obtain ⟨hx0W', hx0t⟩ := mem_filter.1 hx0
              obtain ⟨hx0e, hrb, hnb⟩ := mem_filter.1 hx0W'
              have hx0W := (mem_erase.1 hx0e).2
              have hx0b := (mem_erase.1 hx0e).1
              have himg : t ∈ (W.erase s).image fun x => dist x s :=
                mem_image.2 ⟨x0, hx0e, hx0t⟩
              have hnotR : t ∉ Rb S s := by
                intro hR
                rcases mem_union.1 hR with hR | hR
                · obtain ⟨q, hq, hqt⟩ := mem_image.1 hR
                  obtain ⟨hq1, hq2, hq12⟩ := mem_offDiag.1 hq
                  have := hrb x0 (mem_insert_self _ _) s (mem_insert_of_mem (mem_insert_self _ _))
                    q.1 (mem_insert_of_mem (mem_insert_of_mem hq1)) q.2
                    (mem_insert_of_mem (mem_insert_of_mem hq2)) hx0b hq12 (by rw [hx0t, hqt])
                  rcases this with ⟨h1, -⟩ | ⟨h1, -⟩
                  · exact hWS x0 hx0W (h1 ▸ hq1)
                  · exact hWS x0 hx0W (h1 ▸ hq2)
                · obtain ⟨q, hq, hqt⟩ := mem_image.1 hR
                  have hsq : s ≠ q := fun e => hWS s hb (e ▸ hq)
                  have := hrb x0 (mem_insert_self _ _) s (mem_insert_of_mem (mem_insert_self _ _))
                    s (mem_insert_of_mem (mem_insert_self _ _)) q
                    (mem_insert_of_mem (mem_insert_of_mem hq)) hx0b hsq (by rw [hx0t, hqt])
                  rcases this with ⟨h1, -⟩ | ⟨h1, h2⟩
                  · exact hx0b h1
                  · exact hWS x0 hx0W (h1 ▸ hq)
              have hlt : ((W.filter fun x => dist x s = t).card : ℝ) < τ := by
                by_contra hge
                push Not at hge
                exact hnb (by rw [hx0t]; exact mem_filter.2 ⟨himg, hnotR, hge⟩)
              calc ((W'.filter fun x => dist x s = t).card : ℝ)
                  ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
                    exact_mod_cast card_le_card (filter_subset_filter _ hsubW)
                _ < τ := hlt
            · rw [not_nonempty_iff_eq_empty] at hne
              rw [hne, card_empty, Nat.cast_zero]; linarith
          · calc ((W'.filter fun x => dist x s = t).card : ℝ)
                ≤ ((W.filter fun x => dist x s = t).card : ℝ) := by
                  exact_mod_cast card_le_card (filter_subset_filter _ hsubW)
              _ < σ := hc.cap s hsS t ht
              _ ≤ τ := hτσ
      have hW' : (#W' : ℝ) ≤ Γ * τ := hclaim _ _ τ hconf' (hσ.trans hτσ)
      have : (#Sv : ℝ) ≤ Γ * τ + r ^ 2 * σ := by
        have h1 : #Sv ≤ #Cls + #W' := (card_le_card hsub).trans (card_union_le _ _)
        have : (#Sv : ℝ) ≤ #Cls + #W' := by exact_mod_cast h1
        linarith
      have hA0 : (0 : ℝ) ≤ 2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ := by
        have : (0 : ℝ) ≤ (n - 4 : ℕ) := Nat.cast_nonneg _
        nlinarith
      exact Nat.le_floor (by linarith)
    · push Not at hB2
      set Sv := W.filter fun x => x ≠ b ∧ F b x ≠ 0
      set Cls := (S ×ˢ S).biUnion fun q => W.filter fun x => dist x q.1 = dist b q.2
      have h0 : 0 < (Big S W b τ).card := by omega
      have h1 : 1 < (Big S W b τ).card := by omega
      have h0' : ((0 : Fin 2) : ℕ) < (Big S W b τ).card := by simpa using h0
      have h1' : ((1 : Fin 2) : ℕ) < (Big S W b τ).card := by simpa using h1
      have hρ1 := hlam_mem b 0 h0'
      have hρ2 := hlam_mem b 1 h1'
      have hρne : lam b 0 ≠ lam b 1 := by
        intro he
        simp only [lam, dif_pos h0', dif_pos h1'] at he
        have := (Big S W b τ).equivFin.symm.injective (Subtype.ext he)
        simp [Fin.ext_iff] at this
      have hsub : Sv ⊆ Cls ∪ AsetA S W b (lam b 0) (lam b 1) := by
        intro x hx
        obtain ⟨hxW, hxb, hF⟩ := mem_filter.1 hx
        have hfac : ∀ k : J, ‖b - x‖ ^ 2 - f k b - g k x ≠ 0 := fun k =>
          Finset.prod_ne_zero_iff.1 hF k (Finset.mem_univ _)
        have hbx : ‖b - x‖ = dist x b := by rw [← dist_eq_norm, dist_comm]
        by_cases hcl : x ∈ Cls
        · exact mem_union_left _ hcl
        refine mem_union_right _ (mem_AsetA.2 ⟨mem_erase.2 ⟨hxb, hxW⟩, ?_, ?_, ?_⟩)
        · have := hfac (Sum.inl 0)
          simp only [f, g, sub_zero] at this
          rw [if_pos h0', hbx] at this
          exact fun h => this (by rw [h]; ring)
        · have := hfac (Sum.inl 1)
          simp only [f, g, sub_zero] at this
          rw [if_pos h1', hbx] at this
          exact fun h => this (by rw [h]; ring)
        · refine rainbow_insert_insert S b x (hc.ext b hb) (hc.ext x hxW) ?_ ?_ ?_ ?_
          · intro s hs s' hs' h
            exact hcl (mem_biUnion.2 ⟨(s, s'), mem_product.2 ⟨hs, hs'⟩, mem_filter.2 ⟨hxW, h⟩⟩)
          · intro s hs h
            have := hfac (Sum.inr (Sum.inr (Sum.inl ⟨s, hs⟩)))
            simp only [f, g, sub_zero] at this
            rw [hbx] at this
            exact ne_of_sq_sub_ne this h
          · intro s hs h
            have := hfac (Sum.inr (Sum.inl ⟨s, hs⟩))
            simp only [f, g, sub_zero] at this
            rw [hbx, ← dist_eq_norm] at this
            exact ne_of_sq_sub_ne this h
          · intro s hs s' hs' hne h
            have := hfac (Sum.inr (Sum.inr (Sum.inr ⟨dist s s', mem_dists hs hs' hne⟩)))
            simp only [f, g, sub_zero] at this
            rw [hbx] at this
            exact ne_of_sq_sub_ne this h
      have hA := stepA hn hr hX hc hσ hk hb hρne (by rw [← hτ]; exact hρ1) (by rw [← hτ]; exact hρ2)
      have hCls : (#Cls : ℝ) ≤ r ^ 2 * σ := by
        have h1 : #Cls ≤ ∑ q ∈ S ×ˢ S, #(W.filter fun x => dist x q.1 = dist b q.2) :=
          card_biUnion_le
        have h2 : ∀ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) ≤ σ := by
          intro q hq
          obtain ⟨hq1, hq2⟩ := mem_product.1 hq
          have hpos : 0 < dist b q.2 := dist_pos.2 fun e => hWS b hb (e ▸ hq2)
          exact (hc.cap q.1 hq1 _ hpos).le
        calc (#Cls : ℝ) ≤ ∑ q ∈ S ×ˢ S, ((W.filter fun x => dist x q.1 = dist b q.2).card : ℝ) := by
              exact_mod_cast h1
          _ ≤ ∑ _q ∈ S ×ˢ S, σ := sum_le_sum h2
          _ = r ^ 2 * σ := by rw [sum_const, card_product, hc.card, nsmul_eq_mul]; push_cast; ring
      have hSv : (#Sv : ℝ) ≤ #Cls + (((AsetA S W b (lam b 0) (lam b 1)).card : ℕ) : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
      have hΓτ : 0 ≤ Γ * τ := mul_nonneg hΓ (by linarith)
      exact Nat.le_floor (by linarith)
  have hkill := kill_bound W F _ Δ hrank hdiag hsurv
  have hτpos : 0 < τ := lt_of_lt_of_le hσpos hτσ
  have hΔle : (Δ : ℝ) ≤ Γ * τ + r ^ 2 * σ +
      (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) := by
    refine Nat.floor_le ?_
    have : 0 ≤ Γ * τ := mul_nonneg hΓ hτpos.le
    have : (0 : ℝ) ≤ r ^ 2 * σ := by positivity
    have : (0 : ℝ) ≤ (n - 4 : ℕ) := Nat.cast_nonneg _
    nlinarith
  have : (W.card : ℝ) ≤ (((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := by
    exact_mod_cast hkill
  calc (W.card : ℝ) ≤ (((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) * ((Δ : ℝ) + 1) := this
    _ ≤ _ := by gcongr
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem kA_le_kstar (n : ℕ) (hn : 4 ≤ n) : kA n ≤ kstar n := by
  unfold kA kstar
  have h1 := choose_two_le_sq' (n - 2)
  have h3 : (n - 2) * (n - 2) ≤ n * n := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h4 : 4 * n ≤ n * n := Nat.mul_le_mul_right n hn
  rw [sq]
  generalize (n - 2).choose 2 = C1 at *
  generalize (n - 2) * (n - 2) = P at *
  generalize n * n = Z at *
  generalize 6 ^ n = Y at *
  omega
theorem two_pow_le_E (E : ℝ) (hE : 2 ≤ E) (k : ℕ) : (2 : ℝ) ^ k ≤ E ^ k :=
  pow_le_pow_left₀ (by norm_num) hE k
theorem nat_le_E_pow (E : ℝ) (hE : 2 ≤ E) (k : ℕ) : (k : ℝ) ≤ E ^ k := by
  have h1 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
  exact h1.le.trans (two_pow_le_E E hE k)
def cAdd (n : ℕ) : ℕ := 27 + 2 * n + 5 * kA n + 2 * n + 3 + 2 * (2 + 2 * n + n ^ 2)
theorem claim_step_Rplus (n : ℕ) (hn : 4 ≤ n) (D h : ℕ) (X : Finset (ℝ^d))
    (hX : Ambient n D h X) (r : ℕ) (hr : n - 4 ≤ r) (hrn : r ≤ n) (c : ℕ)
    (hcl : ClaimAt X (r + 1) (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h)) :
    ClaimAt X r (((D + 2 : ℕ) : ℝ) ^ (c + cAdd n)) (smin n D h) := by
  intro S W σ hc hσ
  set E : ℝ := ((D + 2 : ℕ) : ℝ) with hE
  have hE2 : 2 ≤ E := by rw [hE]; exact_mod_cast (show 2 ≤ D + 2 by omega)
  have hE1 : 1 ≤ E := by linarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hΓ0 : (0 : ℝ) ≤ E ^ c := by positivity
  have hW := rplus_step n hn D h X hX r hr (E ^ c) (QA n D * σ) σ hcl S W hc hΓ0 hσ rfl
    (kA_le_kstar n hn)
  have he : 2 * LRcost (kstar n) (D + 2) * h ≤ σ := (e_lt_smin n D h).le.trans hσ
  set q := 27 + 2 * n + 5 * kA n with hq
  have hQ : QA n D ≤ E ^ q := by
    unfold QA
    rw [← hE]
    have h1 : (2 : ℝ) ^ 27 ≤ E ^ 27 := two_pow_le_E E hE2 27
    have h2 : (n : ℝ) ^ 2 ≤ E ^ (2 * n) := by
      rw [pow_mul']
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (nat_le_E_pow E hE2 n) 2
    have h3 : (E ^ kA n) ^ 5 = E ^ (5 * kA n) := by rw [← pow_mul, mul_comm]
    rw [h3, hq, pow_add, pow_add]
    have : (0 : ℝ) ≤ n ^ 2 := by positivity
    have := mul_le_mul h1 h2 this (by positivity)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  set N := c + q + 2 * n with hN
  have hEN : ∀ k, k ≤ N → E ^ k ≤ E ^ N := fun k hk => pow_le_pow_right₀ hE1 hk
  have b1 : E ^ c * (QA n D * σ) ≤ E ^ N * σ := by
    have : E ^ c * QA n D ≤ E ^ (c + q) := by
      rw [pow_add]; exact mul_le_mul_of_nonneg_left hQ hΓ0
    have h' : E ^ (c + q) ≤ E ^ N := hEN _ (by omega)
    have := mul_le_mul_of_nonneg_right (this.trans h') hσ0
    linarith [show E ^ c * (QA n D * σ) = E ^ c * QA n D * σ by ring]
  have b2 : (r : ℝ) ^ 2 * σ ≤ E ^ N * σ := by
    have : (r : ℝ) ^ 2 ≤ E ^ N := by
      have e1 : (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
        have : (r : ℝ) ≤ n := by exact_mod_cast hrn
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
      have e2 : (n : ℝ) ^ 2 ≤ E ^ (2 * n) := by
        rw [pow_mul']
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (nat_le_E_pow E hE2 n) 2
      exact e1.trans (e2.trans (hEN _ (by omega)))
    exact mul_le_mul_of_nonneg_right this hσ0
  have b3 : 2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ ≤ E ^ N * σ := by
    have e1 : (4 : ℝ) + 2 * (n - 4 : ℕ) ≤ E ^ N := by
      have : ((4 + 2 * (n - 4) : ℕ) : ℝ) ≤ E ^ (4 + 2 * (n - 4)) := nat_le_E_pow E hE2 _
      push_cast at this
      exact this.trans (hEN _ (by omega))
    have := mul_le_mul_of_nonneg_right e1 hσ0
    linarith [he]
  have b4 : (1 : ℝ) ≤ E ^ N * σ := by
    have : (1 : ℝ) ≤ E ^ N := one_le_pow₀ hE1
    nlinarith
  have hbr : E ^ c * (QA n D * σ) + r ^ 2 * σ +
      (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1 ≤ E ^ (N + 3) * σ := by
    have : (4 : ℝ) * (E ^ N * σ) ≤ E ^ (N + 3) * σ := by
      have e : E ^ (N + 3) * σ = E ^ 3 * (E ^ N * σ) := by rw [pow_add]; ring
      rw [e]
      have h8 : (4 : ℝ) ≤ E ^ 3 := by
        have := two_pow_le_E E hE2 3; norm_num at this; linarith
      have h0 : 0 ≤ E ^ N * σ := by positivity
      exact mul_le_mul_of_nonneg_right h8 h0
    linarith
  have hM : ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) ≤ E ^ (2 * (2 + 2 * n + n ^ 2)) := by
    have hds : (dists S).card ≤ n ^ 2 := by
      have := card_dists_le S
      rw [hc.card] at this
      have h2 := choose_two_le_sq' r
      have h3 : r * r ≤ n * n := Nat.mul_le_mul hrn hrn
      rw [sq]; omega
    have hcast : ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) =
        E ^ ((2 + 2 * r + (dists S).card) * 2) := by rw [hE]; push_cast; ring
    rw [hcast]
    exact pow_le_pow_right₀ hE1 (by
      have : 2 + 2 * r + (dists S).card ≤ 2 + 2 * n + n ^ 2 := by omega
      calc (2 + 2 * r + (dists S).card) * 2 ≤ (2 + 2 * n + n ^ 2) * 2 := by omega
        _ = 2 * (2 + 2 * n + n ^ 2) := by ring)
  have hM0 : (0 : ℝ) ≤ ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) := by positivity
  calc (W.card : ℝ) ≤ ((((D + 2) ^ (2 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) *
        (E ^ c * (QA n D * σ) + r ^ 2 * σ +
          (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1) := hW
    _ ≤ E ^ (2 * (2 + 2 * n + n ^ 2)) * (E ^ (N + 3) * σ) := by
        have hQA0 : 0 ≤ QA n D := by unfold QA; positivity
        have he0 := e_nonneg n D h
        have hbr0 : 0 ≤ E ^ c * (QA n D * σ) + r ^ 2 * σ +
            (2 * (2 * LRcost (kstar n) (D + 2) * h) + 2 * (n - 4 : ℕ) * σ) + 1 := by
          have t1 : 0 ≤ E ^ c * (QA n D * σ) := mul_nonneg hΓ0 (mul_nonneg hQA0 hσ0)
          have t2 : (0 : ℝ) ≤ r ^ 2 * σ := mul_nonneg (sq_nonneg _) hσ0
          have t3 : (0 : ℝ) ≤ 2 * (n - 4 : ℕ) * σ := mul_nonneg (by positivity) hσ0
          linarith
        exact mul_le_mul hM hbr hbr0 (pow_nonneg (by linarith) _)
    _ = E ^ (c + cAdd n) * σ := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        simp only [cAdd, hN, hq]; ring
theorem theorem_Rplus_low_proved (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ∀ j, n - 4 ≤ j → j ≤ n - 3 → ClaimAt X j (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
  refine ⟨4 * n ^ 2 + 2 * cAdd n, fun d D h X hX hD j hj1 hj2 => ?_⟩
  have ha1 : (1 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ D + 2 by omega)
  have ha2 : (2 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ D + 2 by omega)
  have hs0 : 0 ≤ smin n D h := le_trans zero_le_one (one_le_smin n D h)
  have htop : ClaimAt X (n - 2) (((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2)) (smin n D h) := by
    refine (claim_top n hn d D h X hX).mono_Γ hs0 ?_
    have h1 : ((4 * (n - 2) ^ 2 : ℕ) : ℝ) < 2 ^ (4 * (n - 2) ^ 2) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) :=
      pow_le_pow_left₀ (by norm_num) ha2 _
    have h3 : ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2) :=
      pow_le_pow_right₀ ha1 (by
        have : (n - 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
        omega)
    push_cast at h1
    linarith
  have h3 : ClaimAt X (n - 3) (((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2 + cAdd n)) (smin n D h) :=
    claim_step_Rplus n hn D h X hX (n - 3) (by omega) (by omega) _
      (by rw [show n - 3 + 1 = n - 2 by omega]; exact htop)
  have h4 : ClaimAt X (n - 4) (((D + 2 : ℕ) : ℝ) ^ (4 * n ^ 2 + cAdd n + cAdd n)) (smin n D h) :=
    claim_step_Rplus n hn D h X hX (n - 4) le_rfl (by omega) _
      (by rw [show n - 4 + 1 = n - 3 by omega]; exact h3)
  rcases (show j = n - 3 ∨ j = n - 4 by omega) with rfl | rfl
  · exact h3.mono_Γ hs0 (pow_le_pow_right₀ ha1 (by omega))
  · exact h4.mono_Γ hs0 (pow_le_pow_right₀ ha1 (by omega))
theorem theorem_Rplus_proved (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ∀ j, n - 4 ≤ j → j ≤ n - 2 → ClaimAt X j (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
  obtain ⟨c₀, hlow⟩ := theorem_Rplus_low_proved n hn
  refine ⟨c₀ + 4 * n ^ 2, fun d D h X hX hD j hj1 hj2 => ?_⟩
  have ha1 : (1 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ D + 2 by omega)
  have ha2 : (2 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ D + 2 by omega)
  have hs0 : 0 ≤ smin n D h := le_trans zero_le_one (one_le_smin n D h)
  rcases Nat.lt_or_ge j (n - 2) with hlt | hge
  · exact (hlow d D h X hX hD j hj1 (by omega)).mono_Γ hs0
      (pow_le_pow_right₀ ha1 (by omega))
  · have hj : j = n - 2 := by omega
    subst hj
    refine (claim_top n hn d D h X hX).mono_Γ hs0 ?_
    have h1 : ((4 * (n - 2) ^ 2 : ℕ) : ℝ) < 2 ^ (4 * (n - 2) ^ 2) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) :=
      pow_le_pow_left₀ (by norm_num) ha2 _
    have h3 : ((D + 2 : ℕ) : ℝ) ^ (4 * (n - 2) ^ 2) ≤ ((D + 2 : ℕ) : ℝ) ^ (c₀ + 4 * n ^ 2) :=
      pow_le_pow_right₀ ha1 (by
        have : (n - 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
        omega)
    push_cast at h1
    linarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem rainbow_pair (x o : ℝ^d) : Rainbow (insert x ({o} : Finset (ℝ^d))) := by
  intro a ha a' ha' c hc c' hc' hne hne' _
  simp only [mem_insert, mem_singleton] at ha ha' hc hc'
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> simp_all
theorem labels_singleton (o x : ℝ^d) : labels {o} x = {dist x o} := by
  simp [labels]
theorem big_sphere (D h : ℕ) (X : Finset (ℝ^d)) (hfree : RainbowFree 3 X) (hD : affDim X ≤ D)
    (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h) (o : ℝ^d) (ho : o ∈ X) :
    ∃ r : ℝ, (((X.erase o).filter fun x => dist x o ≠ r).card : ℝ) ≤
      4 * (LRcost (kG 3) (D + 2) * h) := by
  classical
  set μ0 := LRcost (kG 3) (D + 2) * h with hμ0
  have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  set Y := X.erase o with hY
  rcases Y.eq_empty_or_nonempty with hYe | hYne
  · exact ⟨0, by rw [hYe]; simp; positivity⟩
  have hYg : ∀ x ∈ Y, x ∉ ({o} : Finset (ℝ^d)) ∧ Rainbow (insert x ({o} : Finset (ℝ^d))) :=
    fun x hx => ⟨by simpa using (mem_erase.1 hx).1, rainbow_pair x o⟩
  have hG := G1_count 3 D h X {o} Y hfree hD hh (by simpa using ho) (by simp) (by simp)
    (erase_subset _ _) hYg
  simp only [labels_singleton, disjoint_singleton] at hG
  let m : ℝ^d → ℕ := fun x => (Y.filter fun w => dist w o = dist x o).card
  obtain ⟨x0, hx0, hmax⟩ := exists_max_image Y m hYne
  refine ⟨dist x0 o, ?_⟩
  set LD := (Y ×ˢ Y).filter fun q => dist q.1 o ≠ dist q.2 o with hLD
  set SL := (Y ×ˢ Y).filter fun q => dist q.1 o = dist q.2 o with hSL
  have hsplit : LD.card + SL.card = Y.card * Y.card := by
    rw [hLD, hSL, add_comm, card_filter_add_card_filter_not, card_product]
  have hSLc : SL.card ≤ Y.card * m x0 := by
    have hsub : SL ⊆ Y.biUnion fun x => ({x} : Finset (ℝ^d)) ×ˢ
        (Y.filter fun w => dist w o = dist x o) := by
      intro q hq
      obtain ⟨hqY, hqe⟩ := mem_filter.1 hq
      obtain ⟨h1, h2⟩ := mem_product.1 hqY
      exact mem_biUnion.2 ⟨q.1, h1, mem_product.2 ⟨mem_singleton_self _, mem_filter.2 ⟨h2, hqe.symm⟩⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ x ∈ Y, (({x} : Finset (ℝ^d)) ×ˢ (Y.filter fun w => dist w o = dist x o)).card
        = ∑ x ∈ Y, m x := sum_congr rfl fun x _ => by rw [card_product, card_singleton, one_mul]
      _ ≤ ∑ _x ∈ Y, m x0 := sum_le_sum hmax
      _ = Y.card * m x0 := by rw [sum_const, smul_eq_mul]
  have hfilt : ((Y.filter fun x => dist x o ≠ dist x0 o).card) + m x0 = Y.card := by
    have := card_filter_add_card_filter_not (s := Y) (fun x => dist x o ≠ dist x0 o)
    simp only [not_not] at this
    omega
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast card_pos.2 hYne
  have h1 : (Y.card : ℝ) * Y.card ≤ 4 * μ0 * Y.card + Y.card * m x0 := by
    have e1 : ((LD.card + SL.card : ℕ) : ℝ) = Y.card * Y.card := by exact_mod_cast hsplit
    have e2 : (SL.card : ℝ) ≤ Y.card * m x0 := by exact_mod_cast hSLc
    push_cast at e1
    norm_num at hG
    linarith
  have h2 : (Y.card : ℝ) ≤ 4 * μ0 + m x0 := by
    have : (Y.card : ℝ) * Y.card ≤ (4 * μ0 + m x0) * Y.card := by linarith
    exact le_of_mul_le_mul_right this hYpos
  have h3 : ((Y.filter fun x => dist x o ≠ dist x0 o).card : ℝ) + m x0 = Y.card := by
    exact_mod_cast hfilt
  linarith
theorem card_le_n3 (D h : ℕ) (X : Finset (ℝ^d)) (hfree : RainbowFree 3 X) (hD : affDim X ≤ D)
    (hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ h) :
    (X.card : ℝ) ≤ 1 + (D + 1) * (1 + 4 * (LRcost (kG 3) (D + 2) * h)) := by
  classical
  set μ0 := LRcost (kG 3) (D + 2) * h with hμ0
  have hμ : 0 ≤ μ0 := mul_nonneg (one_le_LRcost' _ _) (Nat.cast_nonneg _)
  choose! rad hrad using fun o (ho : o ∈ X) => big_sphere D h X hfree hD hh o ho
  obtain ⟨t, htX, hspan, hind⟩ := exists_affineIndependent ℝ (ℝ^d) (X : Set (ℝ^d))
  have hfin : t.Finite := X.finite_toSet.subset htX
  haveI : Fintype t := hfin.fintype
  set O := hfin.toFinset with hO
  have hOt : (O : Set (ℝ^d)) = t := hfin.coe_toFinset
  have hOX : O ⊆ X := fun x hx => htX (hfin.mem_toFinset.1 hx)
  have hvs : vectorSpan ℝ t = vectorSpan ℝ (X : Set (ℝ^d)) := by
    rw [← direction_affineSpan, hspan, direction_affineSpan]
  have hdimO : affDim O = affDim X := by
    unfold affDim; rw [hOt, hvs]
  have hOcard : O.card ≤ affDim X + 1 := by
    have h1 := hind.card_le_finrank_succ
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hvs] at h1
    have h2 : O.card = Fintype.card t := hfin.card_toFinset
    rw [h2]; exact h1
  set Z := X.filter fun x => ∀ o ∈ O, x ≠ o ∧ dist x o = rad o with hZ
  have hcover : X ⊆ Z ∪ (O ∪ O.biUnion fun o => (X.erase o).filter fun x => dist x o ≠ rad o) := by
    intro x hx
    by_cases hz : x ∈ Z
    · exact mem_union_left _ hz
    refine mem_union_right _ ?_
    by_cases hxO : x ∈ O
    · exact mem_union_left _ hxO
    refine mem_union_right _ ?_
    have : ¬ ∀ o ∈ O, x ≠ o ∧ dist x o = rad o := fun h => hz (mem_filter.2 ⟨hx, h⟩)
    push Not at this
    obtain ⟨o, ho, hxo⟩ := this
    have hne : x ≠ o := fun e => hxO (e ▸ ho)
    exact mem_biUnion.2 ⟨o, ho, mem_filter.2 ⟨mem_erase.2 ⟨hne, hx⟩, hxo hne⟩⟩
  have hZ1 : Z.card ≤ 1 := by
    have hortho := ortho_of_equidistant Z O (fun o => rad o) fun z hz o ho => by
      rw [← dist_eq_norm]; exact ((mem_filter.1 hz).2 o ho).2
    have hadd := affDim_add_le_of_ortho Z O hortho
    have hU : affDim (Z ∪ O) ≤ affDim X := affDim_mono (union_subset (filter_subset _ _) hOX)
    have : affDim Z = 0 := by omega
    exact card_le_one_of_affDim_zero Z this
  have hbig : ∀ o ∈ O, (((X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ) ≤ 4 * μ0 :=
    fun o ho => hrad o (hOX ho)
  have h1 := (card_le_card hcover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_union_le _ _) _))
  have h2 := card_biUnion_le (s := O) (t := fun o => (X.erase o).filter fun x => dist x o ≠ rad o)
  have h3 : ((O.biUnion fun o => (X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ) ≤
      O.card * (4 * μ0) := by
    calc ((O.biUnion fun o => (X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ)
        ≤ ∑ o ∈ O, (((X.erase o).filter fun x => dist x o ≠ rad o).card : ℝ) := by
          exact_mod_cast h2
      _ ≤ ∑ _o ∈ O, 4 * μ0 := sum_le_sum hbig
      _ = O.card * (4 * μ0) := by rw [sum_const, nsmul_eq_mul]
  have hOD : (O.card : ℝ) ≤ D + 1 := by
    have : O.card ≤ D + 1 := by omega
    exact_mod_cast this
  have hX : (X.card : ℝ) ≤ Z.card + (O.card + O.card * (4 * μ0)) := by
    have : (X.card : ℝ) ≤ Z.card + (O.card + (O.biUnion fun o =>
        (X.erase o).filter fun x => dist x o ≠ rad o).card) := by exact_mod_cast h1
    linarith
  have hZr : (Z.card : ℝ) ≤ 1 := by exact_mod_cast hZ1
  have : (O.card : ℝ) * (1 + 4 * μ0) ≤ (D + 1) * (1 + 4 * μ0) :=
    mul_le_mul_of_nonneg_right hOD (by positivity)
  nlinarith
end E1088
end
section
open Finset
open scoped EuclideanGeometry
namespace E1088
variable {d : ℕ}
theorem pow_le_pow_of_le {a : ℝ} (ha : 1 ≤ a) {p q : ℕ} (h : p ≤ q) : a ^ p ≤ a ^ q :=
  pow_le_pow_right₀ ha h
theorem natsq_le_pow (a : ℝ) (ha : 2 ≤ a) (r : ℕ) : ((r ^ 2 : ℕ) : ℝ) ≤ a ^ (r ^ 2) := by
  have h1 : r ^ 2 < 2 ^ (r ^ 2) := Nat.lt_two_pow_self
  have h2 : ((r ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r ^ 2) := by exact_mod_cast h1.le
  exact h2.trans (pow_le_pow_left₀ (by norm_num) ha _)
theorem claim_step (n : ℕ) (hn : 5 ≤ n) (c₁ : ℕ)
    (hE1 : ∀ (d D h r : ℕ), r ≤ n - 5 → ∀ (Γ' : ℝ), 1 ≤ Γ' →
      ∃ ratio : ℝ, 1 ≤ ratio ∧ ratio ≤ ((D + 2 : ℕ) : ℝ) ^ c₁ * Γ' ^ c₁ ∧
        ∀ (X : Finset (ℝ^d)), Ambient n D h X → ∀ (S W : Finset (ℝ^d)) (σ : ℝ),
          Config X S W r σ → smin n D h ≤ σ → HRholds S W σ Γ' →
          ∀ b ∈ W, (Big S W b (ratio * σ)).card < Kr n r)
    (r g : ℕ) (hr : r ≤ n - 5)
    (hclaim : ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ClaimAt X (r + 1) (((D + 2 : ℕ) : ℝ) ^ g) (smin n D h)) :
    ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ClaimAt X r (((D + 2 : ℕ) : ℝ) ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2) +
        (g + c₁ + c₁ * (g + r ^ 2 + 1)) + r ^ 2 + 1)) (smin n D h) := by
  intro d D h X hX hD S W σ hc hσ
  have ha3' : (3 : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ D + 2 by omega)
  set a : ℝ := ((D + 2 : ℕ) : ℝ) with ha
  have ha3 : 3 ≤ a := ha3'
  have ha1 : 1 ≤ a := by linarith
  have hσ1 : 1 ≤ σ := (one_le_smin n D h).trans hσ
  have hσpos : 0 < σ := by linarith
  set Γ := a ^ g with hΓ
  have hΓ1 : 1 ≤ Γ := one_le_pow₀ ha1
  have hcl := hclaim d D h X hX hD
  have hHR := lemma_HR X r Γ (smin n D h) σ hcl S W hc hσpos hσ
  set Γ' := Γ + (r : ℝ) ^ 2 with hΓ'
  have hΓ'1 : 1 ≤ Γ' := by have := sq_nonneg (r : ℝ); linarith
  obtain ⟨ratio, hrat1, hrat, hbig⟩ := hE1 d D h r hr Γ' hΓ'1
  have hbig' : ∀ b ∈ W, (Big S W b (ratio * σ)).card ≤ Kr n r - 1 := by
    intro b hb; have := hbig X hX S W σ hc hσ hHR b hb; omega
  have hkill := lemma_1_2 X D hX.dim r (Kr n r - 1) Γ (smin n D h) σ (ratio * σ) hcl S W hc
    (by linarith) hσpos hσ (by nlinarith) hbig'
  have hr2 : (r : ℝ) ^ 2 ≤ a ^ (r ^ 2) := by
    have := natsq_le_pow a (by linarith) r; push_cast at this; exact this
  have hΓ'le : Γ' ≤ a ^ (g + r ^ 2 + 1) := by
    have e1 : Γ ≤ a ^ (g + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e2 : a ^ (r ^ 2) ≤ a ^ (g + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e3 : a ^ (g + r ^ 2 + 1) = a ^ (g + r ^ 2) * a := pow_succ _ _
    have e4 : 1 ≤ a ^ (g + r ^ 2) := one_le_pow₀ ha1
    rw [e3]; nlinarith
  have hratle : ratio ≤ a ^ (c₁ + c₁ * (g + r ^ 2 + 1)) := by
    rw [pow_add, mul_comm c₁, pow_mul]
    exact hrat.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) hΓ'le c₁) (by positivity))
  set E := g + c₁ + c₁ * (g + r ^ 2 + 1) with hE
  have hΓrat : Γ * ratio ≤ a ^ E := by
    rw [hE, Nat.add_assoc, pow_add]
    exact mul_le_mul_of_nonneg_left hratle (by positivity)
  have hsum : Γ * ratio + (r : ℝ) ^ 2 + 1 ≤ a ^ (E + r ^ 2 + 1) := by
    have e1 : a ^ E ≤ a ^ (E + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e2 : a ^ (r ^ 2) ≤ a ^ (E + r ^ 2) := pow_le_pow_of_le ha1 (by omega)
    have e3 : (1 : ℝ) ≤ a ^ (E + r ^ 2) := one_le_pow₀ ha1
    have e4 : a ^ (E + r ^ 2 + 1) = a ^ (E + r ^ 2) * a := pow_succ _ _
    rw [e4]; nlinarith
  have hdS : (dists S).card ≤ r.choose 2 := by
    have := card_dists_le S; rw [hc.card] at this; exact this
  have hP : ((((D + 2) ^ (Kr n r - 1 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) ≤
      a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2)) := by
    rw [ha]
    push_cast
    rw [← pow_mul, mul_comm (Kr n r - 1 + 2 * r + (dists S).card) 2]
    exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) D; linarith) (by omega)
  have hP0 : (0 : ℝ) ≤ ((((D + 2) ^ (Kr n r - 1 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  calc (W.card : ℝ)
      ≤ ((((D + 2) ^ (Kr n r - 1 + 2 * r + (dists S).card)) ^ 2 : ℕ) : ℝ) *
          (Γ * (ratio * σ) + (r : ℝ) ^ 2 * σ + 1) := hkill
    _ ≤ a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2)) * ((Γ * ratio + (r : ℝ) ^ 2 + 1) * σ) := by
        apply mul_le_mul hP _ (by positivity) (by positivity)
        nlinarith
    _ ≤ a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2)) * (a ^ (E + r ^ 2 + 1) * σ) := by
        gcongr
    _ = a ^ (2 * (Kr n r - 1 + 2 * r + r.choose 2) + E + r ^ 2 + 1) * σ := by
        rw [show 2 * (Kr n r - 1 + 2 * r + r.choose 2) + E + r ^ 2 + 1 =
          2 * (Kr n r - 1 + 2 * r + r.choose 2) + (E + r ^ 2 + 1) by ring, pow_add]; ring
theorem all_claims (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X → 1 ≤ D →
      ClaimAt X 0 (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
  obtain ⟨c₀, htop⟩ := theorem_Rplus_proved n hn
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · exact ⟨c₀, fun d D h X hX hD => htop d D h X hX hD 0 (by norm_num) (by norm_num)⟩
  have hn5' : 5 ≤ n := hn5
  obtain ⟨c₁, hE1⟩ := theorem_E1_proved n hn5'
  have key : ∀ i, i ≤ n - 4 → ∃ c : ℕ, ∀ (d D h : ℕ) (X : Finset (ℝ^d)), Ambient n D h X →
      1 ≤ D → ClaimAt X (n - 4 - i) (((D + 2 : ℕ) : ℝ) ^ c) (smin n D h) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨c₀, fun d D h X hX hD => htop d D h X hX hD (n - 4 - 0) (by omega) (by omega)⟩
    | succ i ih =>
      intro hi
      obtain ⟨g, hg⟩ := ih (by omega)
      have hr : n - 4 - (i + 1) ≤ n - 5 := by omega
      have hlev : n - 4 - (i + 1) + 1 = n - 4 - i := by omega
      refine ⟨_, claim_step n hn5' c₁ hE1 (n - 4 - (i + 1)) g hr ?_⟩
      intro d D h X hX hD
      rw [hlev]; exact hg d D h X hX hD
  obtain ⟨c, hc⟩ := key (n - 4) le_rfl
  refine ⟨c, fun d D h X hX hD => ?_⟩
  have := hc d D h X hX hD
  rwa [show n - 4 - (n - 4) = 0 by omega] at this
theorem config_zero (X : Finset (ℝ^d)) (σ : ℝ) : Config X ∅ X 0 σ := by
  refine ⟨empty_subset _, ?_, rfl, subset_refl _, disjoint_empty_right _, ?_, by simp⟩
  · intro a ha; simp at ha
  · intro x _ a ha a' ha' _ _ _ _ hne _ _
    simp only [insert_empty, mem_singleton] at ha ha'
    exact absurd (ha.trans ha'.symm) hne
theorem two_rpow_natpow (a : ℝ) (ha : 0 < a) (c : ℕ) : a ^ c = (2 : ℝ) ^ (c * Real.logb 2 a) := by
  rw [mul_comm (c : ℝ), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) ha,
    Real.rpow_natCast]
theorem halving_step_ge4 (n : ℕ) (hn : 4 ≤ n) : HalvingStep n := by
  obtain ⟨c, hc⟩ := all_claims n hn
  obtain ⟨Ck, hCk0, hCk⟩ := LRcost_le (kstar n)
  refine ⟨c + 2 * n + 2 + 6 * Ck + 1, by positivity, fun d D B X hX hD hY => ?_⟩
  set Cst : ℝ := c + 2 * n + 2 + 6 * Ck + 1 with hCst
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have := card_le_one_of_affDim_zero X (by have := hD; omega)
    have h1 : (X.card : ℝ) ≤ 1 := by exact_mod_cast this
    simp only [halvingExp, Nat.cast_zero, Real.sqrt_zero, zero_mul, mul_zero, Real.rpow_zero,
      one_mul]
    have := Nat.cast_nonneg (α := ℝ) B; linarith
  have hamb : Ambient n D B X :=
    ⟨hX, hD, fun Y hYX hYd => hY Y ((rainbowFree_iff n Y).2 fun A hA hAn =>
      (rainbowFree_iff n X).1 hX A (hA.trans hYX) hAn) hYd⟩
  have hbound := hc d D B X hamb hDpos ∅ X (smin n D B) (config_zero X _) le_rfl
  set L : ℝ := Real.sqrt D * Real.logb 2 (D + 2) with hL
  have hL1 : 1 ≤ L := sqrt_mul_logb_ge_one D hDpos
  have hsq1 : 1 ≤ Real.sqrt D := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hDpos)
  have hlog0 : 0 ≤ Real.logb 2 ((D : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  have hA : (((D + 2 : ℕ) : ℝ)) ^ c ≤ (2 : ℝ) ^ (c * L) := by
    rw [two_rpow_natpow _ (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [hL]; nlinarith
  have hB4 : (4 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ ((2 * n + 2) * L) := by
    rw [show (4 : ℝ) ^ (n + 1) = (2 : ℝ) ^ (((2 * n + 2 : ℕ) : ℝ)) by
      rw [Real.rpow_natCast, show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]; norm_num]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; nlinarith
  have hLr : Lr (D + 2) ≤ 6 * L := by
    unfold Lr
    push_cast
    have h1 : Real.sqrt ((D : ℝ) + 2 + 2) ≤ 3 * Real.sqrt D := by
      rw [show (3 : ℝ) * Real.sqrt D = Real.sqrt (9 * D) by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      apply Real.sqrt_le_sqrt
      have : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
      linarith
    have h2 : Real.logb 2 ((D : ℝ) + 2 + 2) ≤ 2 * Real.logb 2 ((D : ℝ) + 2) := by
      rw [← Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      rw [show ((D : ℝ) + 2) ^ (2 : ℝ) = ((D : ℝ) + 2) ^ (2 : ℕ) by norm_cast]
      nlinarith [Nat.cast_nonneg (α := ℝ) D]
    have h3 : 0 ≤ Real.logb 2 ((D : ℝ) + 2 + 2) :=
      Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
    calc Real.sqrt ((D : ℝ) + 2 + 2) * Real.logb 2 ((D : ℝ) + 2 + 2)
        ≤ (3 * Real.sqrt D) * (2 * Real.logb 2 ((D : ℝ) + 2)) :=
          mul_le_mul h1 h2 h3 (by positivity)
      _ = 6 * L := by rw [hL]; ring
  have hC : LRcost (kstar n) (D + 2) ≤ (2 : ℝ) ^ (6 * Ck * L) := by
    refine (hCk (D + 2)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    nlinarith
  have hB1 : (0 : ℝ) ≤ B + 1 := by positivity
  calc (X.card : ℝ) ≤ (((D + 2 : ℕ) : ℝ)) ^ c * smin n D B := hbound
    _ = (((D + 2 : ℕ) : ℝ)) ^ c * (4 ^ (n + 1) * LRcost (kstar n) (D + 2)) * (B + 1) := by
        unfold smin; ring
    _ ≤ (2 : ℝ) ^ (c * L) * ((2 : ℝ) ^ ((2 * n + 2) * L) * (2 : ℝ) ^ (6 * Ck * L)) * (B + 1) := by
        have hLR0 : 0 ≤ LRcost (kstar n) (D + 2) := le_trans zero_le_one (one_le_LRcost _ _)
        apply mul_le_mul_of_nonneg_right _ hB1
        exact mul_le_mul hA (mul_le_mul hB4 hC hLR0 (by positivity)) (by positivity)
          (by positivity)
    _ = (2 : ℝ) ^ ((c + 2 * n + 2 + 6 * Ck) * L) * (B + 1) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ halvingExp Cst D * (B + 1) := by
        gcongr
        · norm_num
        · rw [halvingExp, hCst, ← hL]; nlinarith
theorem Lr_le (D : ℕ) (hDpos : 0 < D) :
    Lr (D + 2) ≤ 6 * (Real.sqrt D * Real.logb 2 (D + 2)) := by
  unfold Lr
  push_cast
  have h1 : Real.sqrt ((D : ℝ) + 2 + 2) ≤ 3 * Real.sqrt D := by
    rw [show (3 : ℝ) * Real.sqrt D = Real.sqrt (9 * D) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    apply Real.sqrt_le_sqrt
    have : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
    linarith
  have h2 : Real.logb 2 ((D : ℝ) + 2 + 2) ≤ 2 * Real.logb 2 ((D : ℝ) + 2) := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [show ((D : ℝ) + 2) ^ (2 : ℝ) = ((D : ℝ) + 2) ^ (2 : ℕ) by norm_cast]
    nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have h3 : 0 ≤ Real.logb 2 ((D : ℝ) + 2 + 2) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  calc Real.sqrt ((D : ℝ) + 2 + 2) * Real.logb 2 ((D : ℝ) + 2 + 2)
      ≤ (3 * Real.sqrt D) * (2 * Real.logb 2 ((D : ℝ) + 2)) :=
        mul_le_mul h1 h2 h3 (by positivity)
    _ = 6 * (Real.sqrt D * Real.logb 2 (D + 2)) := by ring
theorem halving_step_three : HalvingStep 3 := by
  obtain ⟨Ck, hCk0, hCk⟩ := LRcost_le (kG 3)
  refine ⟨4 + 6 * Ck + 1, by positivity, fun d D B X hX hD hY => ?_⟩
  set Cst : ℝ := 4 + 6 * Ck + 1 with hCst
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have := card_le_one_of_affDim_zero X (by have := hD; omega)
    have h1 : (X.card : ℝ) ≤ 1 := by exact_mod_cast this
    simp only [halvingExp, Nat.cast_zero, Real.sqrt_zero, zero_mul, mul_zero, Real.rpow_zero,
      one_mul]
    have := Nat.cast_nonneg (α := ℝ) B; linarith
  have hh : ∀ Y ⊆ X, affDim Y ≤ D / 2 → Y.card ≤ B := fun Y hYX hYd =>
    hY Y ((rainbowFree_iff 3 Y).2 fun A hA hAn => (rainbowFree_iff 3 X).1 hX A (hA.trans hYX) hAn)
      hYd
  have hb := card_le_n3 D B X hX hD hh
  set L : ℝ := Real.sqrt D * Real.logb 2 (D + 2) with hL
  have hL1 : 1 ≤ L := sqrt_mul_logb_ge_one D hDpos
  have hsq1 : 1 ≤ Real.sqrt D := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hDpos)
  have hlog0 : 0 ≤ Real.logb 2 ((D : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) D; linarith)
  set LR := LRcost (kG 3) (D + 2) with hLRdef
  have hLR1 : 1 ≤ LR := one_le_LRcost _ _
  have hLR : LR ≤ (2 : ℝ) ^ (6 * Ck * L) := by
    refine (hCk (D + 2)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have := Lr_le D hDpos; rw [← hL] at this; nlinarith
  have hD2 : ((D : ℝ) + 2) ≤ (2 : ℝ) ^ L := by
    calc ((D : ℝ) + 2) = (2 : ℝ) ^ (Real.logb 2 ((D : ℝ) + 2)) := by
          rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
      _ ≤ (2 : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hL]; nlinarith)
  have h5 : (5 : ℝ) ≤ (2 : ℝ) ^ (3 * L) := by
    calc (5 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℕ) : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (3 * L) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hstep : (X.card : ℝ) ≤ ((D : ℝ) + 2) * (5 * LR * (B + 1)) := by
    have e1 : 1 + 4 * (LR * B) ≤ 5 * LR * (B + 1) := by nlinarith
    have e2 : (0 : ℝ) ≤ 1 + 4 * (LR * B) := by positivity
    have e3 : (1 : ℝ) ≤ 1 + 4 * (LR * B) := by nlinarith
    calc (X.card : ℝ) ≤ 1 + (D + 1) * (1 + 4 * (LR * B)) := hb
      _ ≤ ((D : ℝ) + 2) * (1 + 4 * (LR * B)) := by nlinarith
      _ ≤ ((D : ℝ) + 2) * (5 * LR * (B + 1)) := by gcongr
  calc (X.card : ℝ) ≤ ((D : ℝ) + 2) * (5 * LR * (B + 1)) := hstep
    _ ≤ (2 : ℝ) ^ L * ((2 : ℝ) ^ (3 * L) * (2 : ℝ) ^ (6 * Ck * L) * (B + 1)) := by
        apply mul_le_mul hD2 _ (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul h5 hLR (by linarith) (by positivity)
    _ = (2 : ℝ) ^ ((4 + 6 * Ck) * L) * (B + 1) := by
        rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num),
          ← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ halvingExp Cst D * (B + 1) := by
        gcongr
        · norm_num
        · rw [halvingExp, hCst, ← hL]; nlinarith
theorem halving_step : ∀ n ≥ 3, HalvingStep n := by
  intro n hn
  rcases Nat.eq_or_lt_of_le hn with rfl | h
  · exact halving_step_three
  · exact halving_step_ge4 n h
end E1088
end

theorem OMA.solution : type_of% @Erdos1088.erdos_1088 :=
  E1088.erdos_1088_of_halving E1088.halving_step
