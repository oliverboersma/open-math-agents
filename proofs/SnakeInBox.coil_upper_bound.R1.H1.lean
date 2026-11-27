import OMAReductions.R_SnakeInBox_coil_upper_bound_R1
import Mathlib

-- Step SnakeInBox.coil_upper_bound.R1.H1: hypothesis H1 of reduction SnakeInBox.coil_upper_bound.R1
-- Credit: @ivillar. Huang's degree theorem; the eigenvector and local-maximum argument is adapted from
-- Mathlib Archive/Sensitivity.lean (Mathlib contributors: Reid Barton, Johan Commelin, Jesse Michael Han,
-- Chris Hughes, Robert Y. Lewis, Patrick Massot), recast with matrices on Fin n -> Bool.
-- The adjacency lemma hypercube_adj_iff is copied from the reduction file by @marcusbuffett.
-- Strategy. Huang's signed matrix A (blocks [[A, 1], [1, -A]]) satisfies A^2 = n and |A p q| is the
-- adjacency of the cube. One of the eigenspaces for +-sqrt n has dimension at least 2^(n-1), so it meets
-- the vectors supported on any set C of more than 2^(n-1) vertices; at a coordinate of maximal absolute
-- value, |eigenvalue| <= degree in C. As sqrt n > 2 for n >= 5, a set of maximum degree 2 has at most 2^(n-1) vertices.

namespace OMA.SnakeHuang

open Matrix Finset SnakeInBox SimpleGraph symmDiff

abbrev Q (n : ℕ) := Fin n → Bool

/-- Hamming distance between two vertices of the cube. -/
def hd {n : ℕ} (p q : Q n) : ℕ := (univ.filter (fun i => p i ≠ q i)).card

lemma hd_succ {n : ℕ} (p q : Q (n + 1)) :
    hd p q = (if p 0 ≠ q 0 then 1 else 0) + hd (Fin.tail p) (Fin.tail q) := by
  unfold hd
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl

lemma hd_eq_zero {n : ℕ} (p q : Q n) : hd p q = 0 ↔ p = q := by
  unfold hd
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]
  simp

lemma hd_self {n : ℕ} (p : Q n) : hd p p = 0 := (hd_eq_zero p p).mpr rfl

/-- Splitting the cube along the first coordinate. -/
def splitEquiv (n : ℕ) : Q (n + 1) ≃ Q n ⊕ Q n where
  toFun p := if p 0 then Sum.inl (Fin.tail p) else Sum.inr (Fin.tail p)
  invFun x := Sum.elim (fun q => (Fin.cons true q : Q (n + 1))) (fun q => (Fin.cons false q : Q (n + 1))) x
  left_inv p := by
    by_cases h : p 0 = true
    · simp only [h, if_true, Sum.elim_inl]
      conv_rhs => rw [← Fin.cons_self_tail p, h]
    · simp only [h, Bool.false_eq_true, if_false, Sum.elim_inr]
      conv_rhs => rw [← Fin.cons_self_tail p, Bool.eq_false_iff.mpr h]
  right_inv x := by
    rcases x with x | x <;> simp

/-- Huang's signed adjacency matrix, defined by recursion on the dimension. -/
noncomputable def A : (n : ℕ) → Matrix (Q n) (Q n) ℝ
  | 0 => 0
  | n + 1 => (fromBlocks (A n) 1 1 (-A n)).submatrix (splitEquiv n) (splitEquiv n)

lemma A_sq : ∀ n : ℕ, A n * A n = (n : ℝ) • (1 : Matrix (Q n) (Q n) ℝ)
  | 0 => by simp [A]
  | n + 1 => by
    rw [A, submatrix_mul_equiv, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, A_sq n,
      add_neg_cancel]
    have h : (n : ℝ) • (1 : Matrix (Q n) (Q n) ℝ) + 1 = ((n + 1 : ℕ) : ℝ) • 1 := by
      push_cast; rw [add_smul, one_smul]
    have h' : (1 : Matrix (Q n) (Q n) ℝ) + (n : ℝ) • 1 = ((n + 1 : ℕ) : ℝ) • 1 := by
      rw [add_comm, h]
    rw [h, h', ← smul_zero (((n + 1 : ℕ) : ℝ)), ← fromBlocks_smul, fromBlocks_one]
    ext i j
    simp [one_apply]

lemma A_abs : ∀ (n : ℕ) (p q : Q n), |A n p q| = if hd p q = 1 then 1 else 0
  | 0, p, q => by simp [A, hd]
  | n + 1, p, q => by
    have hs := hd_succ p q
    have hz := hd_eq_zero (Fin.tail p) (Fin.tail q)
    have ih := A_abs n (Fin.tail p) (Fin.tail q)
    simp only [A, submatrix_apply, splitEquiv, Equiv.coe_fn_mk]
    cases hp : p 0 <;> cases hq : q 0 <;> simp only [hp, hq] at hs <;>
      simp [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        one_apply, hs, ih]
    all_goals (by_cases h : Fin.tail p = Fin.tail q <;> simp [h, hz, hd_self])

/-- The local maximum argument of Huang's proof (following Mathlib's Archive/Sensitivity.lean). -/
lemma key {ι : Type*} [Fintype ι] [DecidableEq ι] (adj : ι → ι → Prop) [DecidableRel adj]
    (B : Matrix ι ι ℝ) (hB : ∀ q p, |B q p| ≤ if adj q p then 1 else 0) (H : Finset ι) (μ : ℝ)
    (y : ι → ℝ) (hy : y ≠ 0) (hev : B *ᵥ y = μ • y) (hH : ∀ q ∉ H, y q = 0) :
    ∃ q ∈ H, |μ| ≤ ((H.filter (fun p => adj q p)).card : ℝ) := by
  obtain ⟨p0, -⟩ : ∃ p, y p ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have : Nonempty ι := ⟨p0⟩
  obtain ⟨q, hq⟩ : ∃ q, ∀ p, |y p| ≤ |y q| := Finite.exists_max (fun p => |y p|)
  have hpos : 0 < |y q| := by
    by_contra h
    push Not at h
    apply hy
    funext p
    exact abs_nonpos_iff.mp ((hq p).trans h)
  have hqH : q ∈ H := by
    by_contra h
    rw [hH q h, abs_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨q, hqH, ?_⟩
  have h1 : |μ| * |y q| = |∑ p, B q p * y p| := by
    rw [← abs_mul]
    congr 1
    have := congrFun hev q
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have h2 : |∑ p, B q p * y p| ≤ ∑ p, |B q p * y p| := Finset.abs_sum_le_sum_abs _ _
  have h3 : ∀ p, |B q p * y p| ≤ (if p ∈ H.filter (fun p => adj q p) then 1 else 0) * |y q| := by
    intro p
    rw [abs_mul]
    by_cases hp : p ∈ H
    · by_cases ha : adj q p
      · have hb := hB q p
        simp only [ha, if_true] at hb
        simp only [Finset.mem_filter, hp, ha, and_self, if_true, one_mul]
        exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans (by rw [one_mul]; exact hq p)
      · have hb := hB q p
        simp only [ha, if_false] at hb
        have : |B q p| = 0 := le_antisymm hb (abs_nonneg _)
        rw [this, zero_mul]
        exact mul_nonneg (by split_ifs <;> norm_num) (abs_nonneg _)
    · rw [hH p hp, abs_zero, mul_zero]
      exact mul_nonneg (by split_ifs <;> norm_num) (abs_nonneg _)
  have h4 : ∑ p, (if p ∈ H.filter (fun p => adj q p) then (1 : ℝ) else 0) * |y q| =
      ((H.filter (fun p => adj q p)).card : ℝ) * |y q| := by
    rw [← Finset.sum_mul, Finset.sum_boole]
    congr 3
    ext x
    simp
  have h5 : |μ| * |y q| ≤ ((H.filter (fun p => adj q p)).card : ℝ) * |y q| := by
    rw [h1, ← h4]
    exact h2.trans (Finset.sum_le_sum fun p _ => h3 p)
  exact le_of_mul_le_mul_right h5 hpos

/-- A matrix squaring to `c^2` has an eigenvector, for `c` or `-c`, supported on any set of more
than half of the coordinates. -/
lemma exists_eigvec {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ) (c : ℝ)
    (hB : B * B = (c * c) • (1 : Matrix ι ι ℝ)) (H : Finset ι) (hH : Fintype.card ι < 2 * H.card) :
    ∃ μ : ℝ, |μ| = |c| ∧ ∃ y : ι → ℝ, y ≠ 0 ∧ B *ᵥ y = μ • y ∧ ∀ q ∉ H, y q = 0 := by
  set P := B + c • (1 : Matrix ι ι ℝ) with hPdef
  set M := B - c • (1 : Matrix ι ι ℝ) with hMdef
  have hPM : P * M = 0 := by
    rw [hPdef, hMdef, add_mul, mul_sub, mul_sub, hB, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    abel
  have hMP : M * P = 0 := by
    rw [hPdef, hMdef, sub_mul, mul_add, mul_add, hB, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    abel
  let LP := Matrix.mulVecLin P
  let LM := Matrix.mulVecLin M
  have hrP : LinearMap.range LP ≤ LinearMap.ker LM := by
    rintro v ⟨w, rfl⟩
    show M *ᵥ (P *ᵥ w) = 0
    rw [mulVec_mulVec, hMP, zero_mulVec]
  have hrM : LinearMap.range LM ≤ LinearMap.ker LP := by
    rintro v ⟨w, rfl⟩
    show P *ᵥ (M *ᵥ w) = 0
    rw [mulVec_mulVec, hPM, zero_mulVec]
  have hfin : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℝ
  have rnP := LinearMap.finrank_range_add_finrank_ker LP
  have rnM := LinearMap.finrank_range_add_finrank_ker LM
  have leP := Submodule.finrank_mono hrP
  have leM := Submodule.finrank_mono hrM
  -- the subspace of vectors supported on H
  let R := LinearMap.funLeft ℝ ℝ (fun x : {q // q ∉ H} => x.1)
  have rnR := LinearMap.finrank_range_add_finrank_ker R
  have hRle : Module.finrank ℝ (LinearMap.range R) ≤ Fintype.card {q // q ∉ H} := by
    have := Submodule.finrank_le (LinearMap.range R)
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have hcard : Fintype.card {q // q ∉ H} + H.card = Fintype.card ι := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have : H.card ≤ Fintype.card ι := Finset.card_le_univ H
    omega
  -- the eigenspace argument for an eigenspace E
  have main : ∀ (E : Submodule ℝ (ι → ℝ)) (μ : ℝ), |μ| = |c| → (∀ y ∈ E, B *ᵥ y = μ • y) →
      Fintype.card ι ≤ 2 * Module.finrank ℝ E →
      ∃ μ : ℝ, |μ| = |c| ∧ ∃ y : ι → ℝ, y ≠ 0 ∧ B *ᵥ y = μ • y ∧ ∀ q ∉ H, y q = 0 := by
    intro E μ hμ hE hdim
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq E (LinearMap.ker R)
    have hsup := Submodule.finrank_le (E ⊔ LinearMap.ker R)
    have hne : E ⊓ LinearMap.ker R ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hsum
      omega
    obtain ⟨y, hyES, hy0⟩ := (Submodule.ne_bot_iff _).mp hne
    refine ⟨μ, hμ, y, hy0, hE y hyES.1, ?_⟩
    intro q hq
    have hyS : R y = 0 := hyES.2
    exact congrFun hyS ⟨q, hq⟩
  by_cases hcase : Fintype.card ι ≤ 2 * Module.finrank ℝ (LinearMap.ker LM)
  · refine main _ c rfl ?_ hcase
    intro y hy
    have h0 : M *ᵥ y = 0 := hy
    rw [hMdef, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h0
    exact h0
  · refine main (LinearMap.ker LP) (-c) (abs_neg c) ?_ (by omega)
    intro y hy
    have h0 : P *ᵥ y = 0 := hy
    rw [hPdef, add_mulVec, smul_mulVec, one_mulVec, add_eq_zero_iff_eq_neg] at h0
    rw [h0, neg_smul]

/-- Vertices of `Hypercube n` as Boolean functions. -/
def φ (n : ℕ) : Finset (Fin n) ≃ Q n where
  toFun s i := decide (i ∈ s)
  invFun f := univ.filter (fun i => f i = true)
  left_inv s := by ext i; simp
  right_inv f := by funext i; simp

lemma hd_φ {n : ℕ} (a b : Finset (Fin n)) : hd (φ n a) (φ n b) = (a ∆ b).card := by
  unfold hd
  congr 1
  ext i
  simp [φ, Finset.mem_symmDiff]
  tauto

/-- Adjacency in `Hypercube n` (as in the reduction file of @marcusbuffett). -/
lemma hypercube_adj_iff (n : ℕ) (a b : Finset (Fin n)) :
    (Hypercube n).Adj a b ↔ (a ∆ b).card = 1 := by
  simp only [Hypercube, fromRel_adj]
  rw [symmDiff_comm b a]
  constructor
  · exact fun h => h.2.elim id id
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    simp at h

open scoped Classical in
/-- Huang's degree theorem for `Hypercube n`: more than half of the vertices induce a subgraph of
maximum degree at least `√n`. -/
theorem huang (n : ℕ) (C : Finset (Finset (Fin n))) (hC : 2 ^ n < 2 * C.card) :
    ∃ v ∈ C, Real.sqrt n ≤ ((C.filter (fun w => (Hypercube n).Adj v w)).card : ℝ) := by
  let B : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ := (A n).submatrix (φ n) (φ n)
  have hB : B * B = (Real.sqrt n * Real.sqrt n) • (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ) := by
    rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
    show (A n).submatrix (φ n) (φ n) * (A n).submatrix (φ n) (φ n) = _
    rw [submatrix_mul_equiv, A_sq]
    ext i j
    simp [one_apply]
  have hcard : Fintype.card (Finset (Fin n)) < 2 * C.card := by
    rw [Fintype.card_finset, Fintype.card_fin]
    exact hC
  obtain ⟨μ, hμ, y, hy, hev, hsupp⟩ := exists_eigvec B (Real.sqrt n) hB C hcard
  have habs : ∀ q p, |B q p| ≤ if (Hypercube n).Adj q p then 1 else 0 := by
    intro q p
    show |A n (φ n q) (φ n p)| ≤ _
    rw [A_abs, hd_φ]
    by_cases h : (Hypercube n).Adj q p
    · rw [if_pos ((hypercube_adj_iff n q p).mp h), if_pos h]
    · rw [if_neg (mt (hypercube_adj_iff n q p).mpr h), if_neg h]
  obtain ⟨q, hq, hle⟩ := key (fun q p => (Hypercube n).Adj q p) B habs C μ y hy hev hsupp
  refine ⟨q, hq, ?_⟩
  rw [hμ, abs_of_nonneg (Real.sqrt_nonneg _)] at hle
  exact hle

end OMA.SnakeHuang


open SnakeInBox in
open scoped Classical in
theorem OMA.solution : OMA.R_SnakeInBox_coil_upper_bound_R1.H1 := by
  intro n hn C hC
  by_contra hlt
  push Not at hlt
  have h2 : 2 ^ n < 2 * C.card := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  obtain ⟨v, hv, hs⟩ := OMA.SnakeHuang.huang n C h2
  have h3 := hC v hv
  have h5 : (2 : ℝ) < Real.sqrt n := by
    rw [Real.lt_sqrt (by norm_num)]
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h6 : ((C.filter (fun w => (Hypercube n).Adj v w)).card : ℝ) ≤ 2 := by exact_mod_cast h3
  linarith
