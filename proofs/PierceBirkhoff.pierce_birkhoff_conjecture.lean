import FormalConjectures.Wikipedia.PierceBirkhoff
import Mathlib

/-! # The 30-dimensional Pierce–Birkhoff counterexample

Port of Maxence Faldor’s registered Lean disproof following Zehua Lai, Lek-Heng Lim,
and Junyu Ren, *Pierce-Birkhoff conjecture is false*, arXiv:2609.10420, Theorem 7.
The finite closed semialgebraic cover and the max-of-min obstruction both use the
pinned definitions directly. For the source and its Apache-2.0 license, see
https://github.com/maxencefaldor/formal-conjectures/blob/b60249617066831a050910156d9bd055e6a65b92/Solution.lean
and Palomar record PALOMAR-2026-11-27-000027.
-/
-- Port credit: @marcusbuffett
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace PierceBirkhoff
open scoped Polynomial

namespace Counterexample

open Matrix MvPolynomial

/- Part 1: Semialgebraic set closure helpers -/

lemma isSemiAlgebraic_univ {n : ℕ} : IsSemiAlgebraic (Set.univ : Set (Fin n → ℝ)) := by
  refine ⟨Unit, fun _ => ∅, fun _ => ∅, inferInstance, ?_⟩
  ext x
  simp

lemma isSemiAlgebraic_nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsSemiAlgebraic {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x p} := by
  refine ⟨Bool, fun b => if b then {p} else ∅, fun b => if b then ∅ else {p}, inferInstance, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Bool.exists_bool, Bool.false_eq_true, ↓reduceIte,
    Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.mem_singleton, forall_eq,
    true_and, and_true, gt_iff_lt]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr heq.symm
  · rintro (hlt | heq)
    · exact le_of_lt hlt
    · rw [heq]

lemma isSemiAlgebraic_nonpos {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsSemiAlgebraic {x : Fin n → ℝ | MvPolynomial.eval x p ≤ 0} := by
  have h := isSemiAlgebraic_nonneg (-p)
  convert h using 1
  ext x
  simp

lemma isSemiAlgebraic_inter {n : ℕ} {S T : Set (Fin n → ℝ)}
    (hS : IsSemiAlgebraic S) (hT : IsSemiAlgebraic T) :
    IsSemiAlgebraic (S ∩ T) := by
  classical
  rcases hS with ⟨ι₁, p₀, p₁, hι₁, rfl⟩
  rcases hT with ⟨ι₂, q₀, q₁, hι₂, rfl⟩
  refine ⟨ι₁ × ι₂, fun k => p₀ k.1 ∪ q₀ k.2, fun k => p₁ k.1 ∪ q₁ k.2, inferInstance, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, Prod.exists, Finset.mem_union]
  constructor
  · rintro ⟨⟨i, hi0, hi1⟩, ⟨j, hj0, hj1⟩⟩
    refine ⟨i, j, fun p hp => hp.elim (hi0 p) (hj0 p), fun p hp => hp.elim (hi1 p) (hj1 p)⟩
  · rintro ⟨i, j, h0, h1⟩
    exact ⟨⟨i, fun p hp => h0 p (Or.inl hp), fun p hp => h1 p (Or.inl hp)⟩,
           ⟨j, fun p hp => h0 p (Or.inr hp), fun p hp => h1 p (Or.inr hp)⟩⟩

lemma isSemiAlgebraic_finset_iInter {n : ℕ} {α : Type*} (s : Finset α)
    (P : α → Set (Fin n → ℝ)) (hP : ∀ a ∈ s, IsSemiAlgebraic (P a)) :
    IsSemiAlgebraic (⋂ a ∈ s, P a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isSemiAlgebraic_univ
  | @insert a s has ih =>
    rw [Finset.set_biInter_insert]
    exact isSemiAlgebraic_inter (hP a (Finset.mem_insert_self a s))
      (ih fun b hb => hP b (Finset.mem_insert_of_mem hb))

/- Part 2: Identification `ℝ³⁰ ≃ S²(ℝ⁵) × S²(ℝ⁵)` -/

def symIdxAux (i j : Fin 5) : Fin 15 :=
  match i.val, j.val with
  | 0, 0 => 0  | 0, 1 => 1  | 0, 2 => 2  | 0, 3 => 3  | 0, 4 => 4
  | 1, 1 => 5  | 1, 2 => 6  | 1, 3 => 7  | 1, 4 => 8
  | 2, 2 => 9  | 2, 3 => 10 | 2, 4 => 11
  | 3, 3 => 12 | 3, 4 => 13
  | 4, 4 => 14
  | _, _ => 0

def symIdx (i j : Fin 5) : Fin 15 :=
  if i ≤ j then symIdxAux i j else symIdxAux j i

def symPair (k : Fin 15) : Fin 5 × Fin 5 :=
  match k.val with
  | 0 => (0, 0)  | 1 => (0, 1)  | 2 => (0, 2)  | 3 => (0, 3)  | 4 => (0, 4)
  | 5 => (1, 1)  | 6 => (1, 2)  | 7 => (1, 3)  | 8 => (1, 4)
  | 9 => (2, 2)  | 10 => (2, 3) | 11 => (2, 4)
  | 12 => (3, 3) | 13 => (3, 4)
  | _ => (4, 4)

lemma symIdx_symm (i j : Fin 5) : symIdx i j = symIdx j i := by decide +revert

lemma symPair_symIdx (i j : Fin 5) :
    symPair (symIdx i j) = if i ≤ j then (i, j) else (j, i) := by decide +revert

def idxX (i j : Fin 5) : Fin 30 := ⟨(symIdx i j).val, by omega⟩
def idxY (i j : Fin 5) : Fin 30 := ⟨15 + (symIdx i j).val, by omega⟩

def matX (x : Fin 30 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j => x (idxX i j)
def matY (x : Fin 30 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j => x (idxY i j)

def toVec (X Y : Matrix (Fin 5) (Fin 5) ℝ) : Fin 30 → ℝ := fun k =>
  if hk : k.val < 15 then
    let p := symPair ⟨k.val, hk⟩
    X p.1 p.2
  else
    let p := symPair ⟨k.val - 15, by omega⟩
    Y p.1 p.2

lemma matX_toVec {X Y : Matrix (Fin 5) (Fin 5) ℝ} (hX : X.IsSymm) :
    matX (toVec X Y) = X := by
  ext i j
  have hlt : (idxX i j).val < 15 := (symIdx i j).isLt
  simp only [matX, Matrix.of_apply, toVec, hlt, ↓reduceDIte]
  change X (symPair (symIdx i j)).1 (symPair (symIdx i j)).2 = X i j
  rw [symPair_symIdx]
  split_ifs
  · rfl
  · exact hX.apply i j

lemma matY_toVec {X Y : Matrix (Fin 5) (Fin 5) ℝ} (hY : Y.IsSymm) :
    matY (toVec X Y) = Y := by
  ext i j
  have hge : ¬ (idxY i j).val < 15 := by simp [idxY]
  simp only [matY, Matrix.of_apply, toVec, hge, ↓reduceDIte]
  have hsub : (⟨(idxY i j).val - 15, by omega⟩ : Fin 15) = symIdx i j := by
    ext; simp [idxY]
  rw [hsub, symPair_symIdx]
  split_ifs
  · rfl
  · exact hY.apply i j

lemma toVec_add (X₁ X₂ Y₁ Y₂ : Matrix (Fin 5) (Fin 5) ℝ) :
    toVec (X₁ + X₂) (Y₁ + Y₂) = toVec X₁ Y₁ + toVec X₂ Y₂ := by
  ext k
  simp only [toVec, Pi.add_apply]
  split_ifs <;> rfl

lemma toVec_smul (c : ℝ) (X Y : Matrix (Fin 5) (Fin 5) ℝ) :
    toVec (c • X) (c • Y) = c • toVec X Y := by
  ext k
  simp only [toVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> rfl

lemma matX_smul (c : ℝ) (x : Fin 30 → ℝ) : matX (c • x) = c • matX x := by
  ext i j; rfl

lemma matY_smul (c : ℝ) (x : Fin 30 → ℝ) : matY (c • x) = c • matY x := by
  ext i j; rfl

/- Part 3: Counterexample function `fFn` and piecewise polynomiality -/

abbrev Idx := { p : Fin 5 × Fin 5 × Bool // p.1 ≠ p.2.1 }

lemma idx_nonempty : Nonempty Idx := ⟨⟨(0, 1, true), by decide⟩⟩

noncomputable def matXPoly : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 30) ℝ) :=
  Matrix.of fun i j => MvPolynomial.X (idxX i j)

noncomputable def matYPoly : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 30) ℝ) :=
  Matrix.of fun i j => MvPolynomial.X (idxY i j)

noncomputable def detXPoly : MvPolynomial (Fin 30) ℝ := matXPoly.det

noncomputable def prodPoly : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 30) ℝ) :=
  matXPoly * matYPoly

noncomputable def qPoly (idx : Idx) : MvPolynomial (Fin 30) ℝ :=
  prodPoly idx.1.1 idx.1.1 +
    (if idx.1.2.2 then (4 : MvPolynomial (Fin 30) ℝ) else -4) * prodPoly idx.1.1 idx.1.2.1

lemma eval_matXPoly (x : Fin 30 → ℝ) (i j : Fin 5) :
    MvPolynomial.eval x (matXPoly i j) = matX x i j := by
  simp [matXPoly, matX]

lemma eval_matYPoly (x : Fin 30 → ℝ) (i j : Fin 5) :
    MvPolynomial.eval x (matYPoly i j) = matY x i j := by
  simp [matYPoly, matY]

lemma eval_detXPoly (x : Fin 30 → ℝ) :
    MvPolynomial.eval x detXPoly = (matX x).det := by
  rw [detXPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, eval_matXPoly]

lemma eval_prodPoly (x : Fin 30 → ℝ) (i j : Fin 5) :
    MvPolynomial.eval x (prodPoly i j) = (matX x * matY x) i j := by
  simp only [prodPoly, Matrix.mul_apply, map_sum, map_mul, eval_matXPoly, eval_matYPoly]

lemma eval_qPoly (x : Fin 30 → ℝ) (idx : Idx) :
    MvPolynomial.eval x (qPoly idx) =
      (matX x * matY x) idx.1.1 idx.1.1 +
        (if idx.1.2.2 then (4 : ℝ) else -4) * (matX x * matY x) idx.1.1 idx.1.2.1 := by
  simp only [qPoly, map_add, map_mul, eval_prodPoly]
  split_ifs <;> simp

noncomputable def hFn (x : Fin 30 → ℝ) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty_iff.mpr idx_nonempty)
    (fun idx : Idx => MvPolynomial.eval x (qPoly idx))

noncomputable def fFn (x : Fin 30 → ℝ) : ℝ :=
  if hFn x > 0 ∧ (matX x).det > 0 then hFn x else 0

/-- Lemma 2: If `hFn x > 0`, then `P = matX x * matY x` is strictly diagonally dominant,
hence invertible, and in particular `(matX x).det ≠ 0`. -/
lemma det_ne_zero_of_hFn_pos {x : Fin 30 → ℝ} (hh : hFn x > 0) : (matX x).det ≠ 0 := by
  intro hdet
  set P : Matrix (Fin 5) (Fin 5) ℝ := matX x * matY x
  have hPdet : P.det = 0 := by
    simp [P, Matrix.det_mul, hdet]
  obtain ⟨v, hv_ne, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hPdet
  obtain ⟨i, -, hi_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 5))
    (fun k => |v k|) Finset.univ_nonempty
  have hvi_pos : 0 < |v i| := by
    by_contra hle
    have hle' : |v i| ≤ 0 := not_lt.mp hle
    have hvi0 : |v i| = 0 := le_antisymm hle' (abs_nonneg _)
    apply hv_ne
    funext k
    have hk : |v k| ≤ 0 := hvi0 ▸ hi_max k (Finset.mem_univ k)
    exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))
  have hrow : ∑ j : Fin 5, P i j * v j = 0 := by
    have := congr_fun hv_zero i
    simpa [Matrix.mulVec, dotProduct] using this
  have hrow' : P i i * v i = - ∑ j ∈ Finset.univ.erase i, P i j * v j := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin 5))
      (fun j => P i j * v j) (Finset.mem_univ i)
    linarith
  have hdom : ∀ j ∈ Finset.univ.erase i, 4 * |P i j| < P i i := by
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hp : 0 < P i i + 4 * P i j := by
      have h1 : hFn x ≤ MvPolynomial.eval x (qPoly ⟨(i, j, true), hij⟩) :=
        Finset.inf'_le _ (Finset.mem_univ _)
      rw [eval_qPoly] at h1
      simp only [↓reduceIte] at h1
      linarith
    have hm : 0 < P i i - 4 * P i j := by
      have h1 : hFn x ≤ MvPolynomial.eval x (qPoly ⟨(i, j, false), hij⟩) :=
        Finset.inf'_le _ (Finset.mem_univ _)
      rw [eval_qPoly] at h1
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      linarith
    rcases le_total 0 (P i j) with hle | hle
    · rw [abs_of_nonneg hle]; linarith
    · rw [abs_of_nonpos hle]; linarith
  have hPii_pos : 0 < P i i := by
    obtain ⟨j, hj⟩ : (Finset.univ.erase i : Finset (Fin 5)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hcard := Finset.card_erase_of_mem (Finset.mem_univ i)
      rw [hemp, Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    have := hdom j hj
    have : 0 ≤ |P i j| := abs_nonneg _
    linarith
  have hsum_lt : ∑ j ∈ Finset.univ.erase i, |P i j| < P i i := by
    have h4 : ∑ j ∈ Finset.univ.erase i, (4 * |P i j|) <
        ∑ _j ∈ Finset.univ.erase i, P i i := by
      apply Finset.sum_lt_sum_of_nonempty
      · rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hcard := Finset.card_erase_of_mem (Finset.mem_univ i)
        rw [hemp, Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hcard
        omega
      · exact hdom
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin] at h4
    simp only [Nat.reduceSub, nsmul_eq_mul, Nat.cast_ofNat] at h4
    linarith
  have hbound : P i i * |v i| ≤ (∑ j ∈ Finset.univ.erase i, |P i j|) * |v i| := by
    calc P i i * |v i|
        = |P i i * v i| := by rw [abs_mul, abs_of_pos hPii_pos]
      _ = |∑ j ∈ Finset.univ.erase i, P i j * v j| := by rw [hrow', abs_neg]
      _ ≤ ∑ j ∈ Finset.univ.erase i, |P i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.univ.erase i, |P i j| * |v j| := by
          refine Finset.sum_congr rfl fun j _ => abs_mul _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, |P i j| * |v i| := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hi_max j (Finset.mem_univ j)) (abs_nonneg _)
      _ = (∑ j ∈ Finset.univ.erase i, |P i j|) * |v i| := (Finset.sum_mul _ _ _).symm
  have : (∑ j ∈ Finset.univ.erase i, |P i j|) * |v i| < P i i * |v i| :=
    mul_lt_mul_of_pos_right hsum_lt hvi_pos
  linarith

/-- Lemma 3 (part 1): `fFn` is piecewise polynomial on a finite closed semialgebraic covering. -/
lemma isPiecewiseMvPolynomial_fFn : IsPiecewiseMvPolynomial fFn := by
  let P : Option (Idx ⊕ Idx) → Set (Fin 30 → ℝ) := fun
    | none => {x | MvPolynomial.eval x detXPoly ≤ 0}
    | some (Sum.inl idx) => {x | MvPolynomial.eval x (qPoly idx) ≤ 0}
    | some (Sum.inr idx) =>
        {x | 0 ≤ MvPolynomial.eval x detXPoly} ∩
        {x | 0 ≤ MvPolynomial.eval x (qPoly idx)} ∩
        (⋂ idx' ∈ (Finset.univ : Finset Idx),
          {x | 0 ≤ MvPolynomial.eval x (qPoly idx' - qPoly idx)})
  let g : Option (Idx ⊕ Idx) → MvPolynomial (Fin 30) ℝ := fun
    | none => 0
    | some (Sum.inl _) => 0
    | some (Sum.inr idx) => qPoly idx
  refine ⟨Option (Idx ⊕ Idx), P, g, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases i with _ | idx | idx
    · exact isClosed_le (MvPolynomial.continuous_eval _) continuous_const
    · exact isClosed_le (MvPolynomial.continuous_eval _) continuous_const
    · refine ((isClosed_le continuous_const (MvPolynomial.continuous_eval _)).inter
        (isClosed_le continuous_const (MvPolynomial.continuous_eval _))).inter ?_
      exact isClosed_biInter fun idx' _ =>
        isClosed_le continuous_const (MvPolynomial.continuous_eval _)
  · intro i
    rcases i with _ | idx | idx
    · exact isSemiAlgebraic_nonpos _
    · exact isSemiAlgebraic_nonpos _
    · exact isSemiAlgebraic_inter
        (isSemiAlgebraic_inter (isSemiAlgebraic_nonneg _) (isSemiAlgebraic_nonneg _))
        (isSemiAlgebraic_finset_iInter _ _ fun idx' _ => isSemiAlgebraic_nonneg _)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hdet : (matX x).det ≤ 0
    · exact ⟨none, by simpa [P, eval_detXPoly] using hdet⟩
    · have hdet_pos : 0 < (matX x).det := not_le.mp hdet
      obtain ⟨idx, -, hidx⟩ := Finset.exists_mem_eq_inf'
        (Finset.univ_nonempty_iff.mpr idx_nonempty)
        (fun idx : Idx => MvPolynomial.eval x (qPoly idx))
      by_cases hq : MvPolynomial.eval x (qPoly idx) ≤ 0
      · exact ⟨some (Sum.inl idx), hq⟩
      · have hq_pos : 0 < MvPolynomial.eval x (qPoly idx) := not_le.mp hq
        refine ⟨some (Sum.inr idx), ⟨⟨?_, le_of_lt hq_pos⟩, ?_⟩⟩
        · simpa [eval_detXPoly] using le_of_lt hdet_pos
        · simp only [Set.mem_iInter, Set.mem_ofPred_eq, map_sub, sub_nonneg]
          intro idx' _
          rw [← hidx]
          exact Finset.inf'_le _ (Finset.mem_univ idx')
  · intro i x hx
    rcases i with _ | idx | idx
    · have hdet : (matX x).det ≤ 0 := by simpa [P, eval_detXPoly] using hx
      simp [fFn, g, not_lt.mpr hdet]
    · have hq : MvPolynomial.eval x (qPoly idx) ≤ 0 := hx
      have hh : hFn x ≤ 0 := (Finset.inf'_le _ (Finset.mem_univ idx)).trans hq
      simp [fFn, g, not_lt.mpr hh]
    · rcases hx with ⟨⟨hdet, hq⟩, hmin⟩
      rw [Set.mem_ofPred_eq, eval_detXPoly] at hdet
      have hh_eq : hFn x = MvPolynomial.eval x (qPoly idx) := by
        apply le_antisymm
        · exact Finset.inf'_le _ (Finset.mem_univ idx)
        · unfold hFn
          rw [Finset.le_inf'_iff]
          intro idx' _
          have h' := Set.mem_iInter₂.mp hmin idx' (Finset.mem_univ idx')
          simp only [Set.mem_ofPred_eq, map_sub, sub_nonneg] at h'
          exact h'
      by_cases hpos : hFn x > 0
      · have hdet_ne : (matX x).det ≠ 0 := det_ne_zero_of_hFn_pos hpos
        have hdet_pos : (matX x).det > 0 := lt_of_le_of_ne hdet (Ne.symm hdet_ne)
        unfold fFn
        rw [if_pos ⟨hpos, hdet_pos⟩, hh_eq]
      · have hh0 : hFn x = 0 := le_antisymm (not_lt.mp hpos) (hh_eq ▸ hq)
        unfold fFn
        rw [if_neg (fun h => hpos h.1), ← hh_eq, hh0]

/-- Lemma 3 (part 2): `fFn` is positively homogeneous of degree 2. -/
lemma fFn_smul {t : ℝ} (ht : 0 < t) (x : Fin 30 → ℝ) : fFn (t • x) = t ^ 2 * fFn x := by
  have hq : ∀ idx : Idx, MvPolynomial.eval (t • x) (qPoly idx) =
      t ^ 2 * MvPolynomial.eval x (qPoly idx) := by
    intro idx
    rw [eval_qPoly, eval_qPoly, matX_smul, matY_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← sq]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hh : hFn (t • x) = t ^ 2 * hFn x := by
    apply le_antisymm
    · obtain ⟨idx, -, hidx⟩ := Finset.exists_mem_eq_inf'
        (Finset.univ_nonempty_iff.mpr idx_nonempty)
        (fun idx : Idx => MvPolynomial.eval x (qPoly idx))
      change hFn x = MvPolynomial.eval x (qPoly idx) at hidx
      calc hFn (t • x) ≤ MvPolynomial.eval (t • x) (qPoly idx) :=
            Finset.inf'_le _ (Finset.mem_univ idx)
        _ = t ^ 2 * MvPolynomial.eval x (qPoly idx) := hq idx
        _ = t ^ 2 * hFn x := by rw [← hidx]
    · conv_rhs => unfold hFn
      rw [Finset.le_inf'_iff]
      intro idx _
      rw [hq idx]
      exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ idx)) (sq_nonneg t)
  have hdet : (matX (t • x)).det = t ^ 5 * (matX x).det := by
    rw [matX_smul, Matrix.det_smul, Fintype.card_fin]
  have hdet_iff : (matX (t • x)).det > 0 ↔ (matX x).det > 0 := by
    rw [hdet]
    exact mul_pos_iff_of_pos_left (pow_pos ht 5)
  have hh_iff : hFn (t • x) > 0 ↔ hFn x > 0 := by
    rw [hh]
    exact mul_pos_iff_of_pos_left (pow_pos ht 2)
  unfold fFn
  by_cases h1 : hFn x > 0 ∧ (matX x).det > 0
  · rw [if_pos h1, if_pos ⟨hh_iff.mpr h1.1, hdet_iff.mpr h1.2⟩, hh]
  · rw [if_neg h1, if_neg (fun h => h1 ⟨hh_iff.mp h.1, hdet_iff.mp h.2⟩), mul_zero]

/-- `fFn` is nonzero at `(I₅, I₅)`. -/
lemma fFn_toVec_one_one : fFn (toVec 1 1) = 1 := by
  have hX : matX (toVec 1 1) = 1 := matX_toVec Matrix.isSymm_one
  have hY : matY (toVec 1 1) = 1 := matY_toVec Matrix.isSymm_one
  have hq : ∀ idx : Idx, MvPolynomial.eval (toVec 1 1) (qPoly idx) = 1 := by
    intro idx
    rw [eval_qPoly, hX, hY, mul_one]
    have hne : idx.1.1 ≠ idx.1.2.1 := idx.2
    simp [hne]
  have hh : hFn (toVec 1 1) = 1 := by
    apply le_antisymm
    · obtain ⟨idx⟩ := idx_nonempty
      calc hFn (toVec 1 1) ≤ MvPolynomial.eval (toVec 1 1) (qPoly idx) :=
            Finset.inf'_le _ (Finset.mem_univ idx)
        _ = 1 := hq idx
    · unfold hFn
      rw [Finset.le_inf'_iff]
      intro idx _
      rw [hq idx]
  simp [fFn, hh, hX]

/- Part 4: Homogeneous polynomials of degree 0, 1, 2 and Lemma 4 -/

lemma eval_isHomogeneous_smul {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (t : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (t • x) p = t ^ d * MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hm)
  have hsum : ∑ i : Fin n, m i = d := by
    rw [← hdeg, Finsupp.degree_apply]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    exact Finsupp.notMem_support_iff.mp hi
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hsum]
  ring

lemma eval_smul_approx {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      |MvPolynomial.eval (t • x) p -
        (MvPolynomial.eval x (p.homogeneousComponent 0) +
         MvPolynomial.eval x (p.homogeneousComponent 1) * t +
         MvPolynomial.eval x (p.homogeneousComponent 2) * t ^ 2)| ≤ M * t ^ 3 := by
  set D := max 2 p.totalDegree
  have hp_sum : p = ∑ d ∈ Finset.range (D + 1), p.homogeneousComponent d := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (le_max_right 2 p.totalDegree))) ?_
    intro d _ hd
    rw [Finset.mem_range] at hd
    exact MvPolynomial.homogeneousComponent_eq_zero d p (by omega)
  let c : ℕ → ℝ := fun d => MvPolynomial.eval x (p.homogeneousComponent d)
  have heval : ∀ t : ℝ, MvPolynomial.eval (t • x) p =
      ∑ d ∈ Finset.range (D + 1), t ^ d * c d := by
    intro t
    conv_lhs => rw [hp_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact eval_isHomogeneous_smul (MvPolynomial.homogeneousComponent_isHomogeneous d p) t x
  have hsplit : ∀ t : ℝ, MvPolynomial.eval (t • x) p - (c 0 + c 1 * t + c 2 * t ^ 2) =
      ∑ d ∈ Finset.Ico 3 (D + 1), t ^ d * c d := by
    intro t
    rw [heval t]
    have hrange : Finset.range (D + 1) = Finset.range 3 ∪ Finset.Ico 3 (D + 1) := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range 3) (Finset.Ico 3 (D + 1)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_range, Finset.mem_Ico] at hk1 hk2
      omega
    rw [hrange, Finset.sum_union hdisj, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    ring
  refine ⟨∑ d ∈ Finset.Ico 3 (D + 1), |c d|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro t ht0 ht1
  rw [hsplit t, Finset.sum_mul]
  calc |∑ d ∈ Finset.Ico 3 (D + 1), t ^ d * c d|
      ≤ ∑ d ∈ Finset.Ico 3 (D + 1), |t ^ d * c d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ico 3 (D + 1), |c d| * t ^ 3 := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [Finset.mem_Ico] at hd
        rw [abs_mul, abs_of_pos (pow_pos ht0 d), mul_comm]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (le_of_lt ht0) ht1 hd.1) (abs_nonneg _)

/-- The lexicographic positivity condition on the degree 0, 1, 2 homogeneous parts of `p` at `x`. -/
def LexPos {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  let c₀ := MvPolynomial.eval x (p.homogeneousComponent 0)
  let c₁ := MvPolynomial.eval x (p.homogeneousComponent 1)
  let c₂ := MvPolynomial.eval x (p.homogeneousComponent 2)
  c₀ > 0 ∨ (c₀ = 0 ∧ c₁ > 0) ∨ (c₀ = 0 ∧ c₁ = 0 ∧ c₂ > 0)

/-- Lemma 4: For a positively degree-2 homogeneous function `f = sup_i inf_j g_{ij}`,
`f x > 0` holds iff `∃ i, ∀ j, LexPos (g i j) x`. -/
lemma pos_iff_lexPos {n : ℕ} {ι κ : Type} [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    {f : (Fin n → ℝ) → ℝ} (hf_hom : ∀ t > 0, ∀ x, f (t • x) = t ^ 2 * f x)
    {g : ι → κ → MvPolynomial (Fin n) ℝ}
    (hg : ∀ x, f x = ⨆ i, ⨅ j, MvPolynomial.eval x (g i j))
    (x : Fin n → ℝ) :
    f x > 0 ↔ ∃ i : ι, ∀ j : κ, LexPos (g i j) x := by
  constructor
  · intro hfx
    have hex : ∀ k : ℕ, ∃ i : ι, ∀ j : κ,
        ((k + 1 : ℝ)⁻¹) ^ 2 * f x ≤ MvPolynomial.eval (((k + 1 : ℝ)⁻¹) • x) (g i j) := by
      intro k
      have htk : (0 : ℝ) < (k + 1 : ℝ)⁻¹ := by positivity
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
        (f := fun i => ⨅ j, MvPolynomial.eval (((k + 1 : ℝ)⁻¹) • x) (g i j))
      refine ⟨i, fun j => ?_⟩
      have h1 : ((k + 1 : ℝ)⁻¹) ^ 2 * f x = ⨅ j, MvPolynomial.eval (((k + 1 : ℝ)⁻¹) • x) (g i j) := by
        rw [hi, ← hg, hf_hom _ htk]
      rw [h1]
      exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) j
    choose idx hidx using hex
    obtain ⟨i, hi_inf⟩ := Finite.exists_infinite_fiber idx
    refine ⟨i, fun j => ?_⟩
    obtain ⟨M, hM, happrox⟩ := eval_smul_approx (g i j) x
    set c₀ := MvPolynomial.eval x ((g i j).homogeneousComponent 0)
    set c₁ := MvPolynomial.eval x ((g i j).homogeneousComponent 1)
    set c₂ := MvPolynomial.eval x ((g i j).homogeneousComponent 2)
    have harb : ∀ δ > 0, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t < δ ∧
        t ^ 2 * f x ≤ c₀ + c₁ * t + c₂ * t ^ 2 + M * t ^ 3 := by
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
      have hinf_set : Set.Infinite (idx ⁻¹' {i}) := Set.infinite_coe_iff.mp hi_inf
      obtain ⟨k, hk_mem, hk_gt⟩ := hinf_set.exists_gt N
      have hki : idx k = i := hk_mem
      set t : ℝ := (k + 1 : ℝ)⁻¹
      have ht0 : 0 < t := by positivity
      have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have htδ : t < δ := by
        rw [inv_lt_comm₀ (by positivity) hδ]
        have hkN : (N : ℝ) < (k : ℝ) := Nat.cast_lt.mpr hk_gt
        linarith
      have hge := hidx k j
      rw [hki] at hge
      have hbd := (abs_le.mp (happrox t ht0 ht1)).2
      exact ⟨t, ht0, ht1, htδ, by linarith⟩
    have hc₀_ge : 0 ≤ c₀ := by
      by_contra hlt
      have hlt' : c₀ < 0 := not_le.mp hlt
      have hneg : 0 < -c₀ := neg_pos.mpr hlt'
      obtain ⟨t, ht0, ht1, htδ, hineq⟩ := harb ((-c₀) / (|c₁| + |c₂| + M + 1)) (by positivity)
      have ht2 : t ^ 2 ≤ t := by nlinarith
      have ht3 : t ^ 3 ≤ t := by nlinarith [sq_nonneg t]
      have h1 : c₁ * t ≤ |c₁| * t := mul_le_mul_of_nonneg_right (le_abs_self _) (le_of_lt ht0)
      have h2 : c₂ * t ^ 2 ≤ |c₂| * t := by
        calc c₂ * t ^ 2 ≤ |c₂| * t ^ 2 :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t)
          _ ≤ |c₂| * t := mul_le_mul_of_nonneg_left ht2 (abs_nonneg _)
      have h3 : M * t ^ 3 ≤ M * t := mul_le_mul_of_nonneg_left ht3 hM
      have h4 : (|c₁| + |c₂| + M + 1) * t < -c₀ := by
        rwa [lt_div_iff₀ (by positivity), mul_comm] at htδ
      have h5 : 0 < t ^ 2 * f x := mul_pos (sq_pos_of_pos ht0) hfx
      nlinarith
    rcases lt_or_eq_of_le hc₀_ge with hc₀_pos | hc₀_zero
    · exact Or.inl hc₀_pos
    · have hc₀ : c₀ = 0 := hc₀_zero.symm
      have hc₁_ge : 0 ≤ c₁ := by
        by_contra hlt
        have hlt' : c₁ < 0 := not_le.mp hlt
        have hneg : 0 < -c₁ := neg_pos.mpr hlt'
        obtain ⟨t, ht0, ht1, htδ, hineq⟩ := harb ((-c₁) / (|c₂| + M + 1)) (by positivity)
        rw [hc₀, zero_add] at hineq
        have hpos : 0 < t * (c₁ + c₂ * t + M * t ^ 2) := by
          have : 0 < t ^ 2 * f x := mul_pos (sq_pos_of_pos ht0) hfx
          linarith
        have hdiv : 0 < c₁ + c₂ * t + M * t ^ 2 := pos_of_mul_pos_right hpos (le_of_lt ht0)
        have ht2 : t ^ 2 ≤ t := by nlinarith
        have h2 : c₂ * t ≤ |c₂| * t := mul_le_mul_of_nonneg_right (le_abs_self _) (le_of_lt ht0)
        have h3 : M * t ^ 2 ≤ M * t := mul_le_mul_of_nonneg_left ht2 hM
        have h4 : (|c₂| + M + 1) * t < -c₁ := by
          rwa [lt_div_iff₀ (by positivity), mul_comm] at htδ
        nlinarith
      rcases lt_or_eq_of_le hc₁_ge with hc₁_pos | hc₁_zero
      · exact Or.inr (Or.inl ⟨hc₀, hc₁_pos⟩)
      · have hc₁ : c₁ = 0 := hc₁_zero.symm
        have hc₂_pos : 0 < c₂ := by
          by_contra hle
          have hle' : c₂ ≤ 0 := not_lt.mp hle
          obtain ⟨t, ht0, ht1, htδ, hineq⟩ := harb (f x / (M + 1)) (by positivity)
          rw [hc₀, hc₁, zero_add, zero_mul, zero_add] at hineq
          have hdiv : f x ≤ c₂ + M * t := by
            have : t ^ 2 * f x ≤ t ^ 2 * (c₂ + M * t) := by linarith
            exact le_of_mul_le_mul_left this (sq_pos_of_pos ht0)
          have h4 : (M + 1) * t < f x := by
            rwa [lt_div_iff₀ (by positivity), mul_comm] at htδ
          nlinarith
        exact Or.inr (Or.inr ⟨hc₀, hc₁, hc₂_pos⟩)
  · rintro ⟨i, hi⟩
    have hδ_ex : ∀ j : κ, ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < t → t < δ → 0 < MvPolynomial.eval (t • x) (g i j) := by
      intro j
      obtain ⟨M, hM, happrox⟩ := eval_smul_approx (g i j) x
      set c₀ := MvPolynomial.eval x ((g i j).homogeneousComponent 0)
      set c₁ := MvPolynomial.eval x ((g i j).homogeneousComponent 1)
      set c₂ := MvPolynomial.eval x ((g i j).homogeneousComponent 2)
      rcases hi j with hc₀ | ⟨hc₀, hc₁⟩ | ⟨hc₀, hc₁, hc₂⟩
      · change c₀ > 0 at hc₀
        refine ⟨min 1 (c₀ / (2 * (|c₁| + |c₂| + M + 1))), by positivity, fun t ht0 htδ => ?_⟩
        have ht1 : t ≤ 1 := le_of_lt (lt_of_lt_of_le htδ (min_le_left _ _))
        have htd : t < c₀ / (2 * (|c₁| + |c₂| + M + 1)) :=
          lt_of_lt_of_le htδ (min_le_right _ _)
        have hbd := (abs_le.mp (happrox t ht0 ht1)).1
        have ht2 : t ^ 2 ≤ t := by nlinarith
        have ht3 : t ^ 3 ≤ t := by nlinarith [sq_nonneg t]
        have h1 : -|c₁| * t ≤ c₁ * t := by
          have := neg_abs_le c₁; nlinarith
        have h2 : -|c₂| * t ≤ c₂ * t ^ 2 := by
          have ha : -|c₂| * t ^ 2 ≤ c₂ * t ^ 2 :=
            mul_le_mul_of_nonneg_right (neg_abs_le c₂) (sq_nonneg t)
          have hb : |c₂| * t ^ 2 ≤ |c₂| * t := mul_le_mul_of_nonneg_left ht2 (abs_nonneg _)
          linarith
        have h3 : -M * t ≤ -(M * t ^ 3) := by
          have := mul_le_mul_of_nonneg_left ht3 hM
          linarith
        have h4 : 2 * (|c₁| + |c₂| + M + 1) * t < c₀ := by
          rwa [lt_div_iff₀ (by positivity), mul_comm] at htd
        nlinarith
      · change c₀ = 0 at hc₀
        change c₁ > 0 at hc₁
        refine ⟨min 1 (c₁ / (2 * (|c₂| + M + 1))), by positivity, fun t ht0 htδ => ?_⟩
        have ht1 : t ≤ 1 := le_of_lt (lt_of_lt_of_le htδ (min_le_left _ _))
        have htd : t < c₁ / (2 * (|c₂| + M + 1)) :=
          lt_of_lt_of_le htδ (min_le_right _ _)
        have hbd := (abs_le.mp (happrox t ht0 ht1)).1
        rw [hc₀, zero_add] at hbd
        have ht2 : t ^ 2 ≤ t := by nlinarith
        have h2 : -|c₂| * t ≤ c₂ * t := by
          have := neg_abs_le c₂; nlinarith
        have h3 : -M * t ≤ -(M * t ^ 2) := by
          have := mul_le_mul_of_nonneg_left ht2 hM
          linarith
        have h4 : 2 * (|c₂| + M + 1) * t < c₁ := by
          rwa [lt_div_iff₀ (by positivity), mul_comm] at htd
        have hpos : 0 < c₁ + c₂ * t - M * t ^ 2 := by nlinarith
        have : 0 < t * (c₁ + c₂ * t - M * t ^ 2) := mul_pos ht0 hpos
        linarith
      · change c₀ = 0 at hc₀
        change c₁ = 0 at hc₁
        change c₂ > 0 at hc₂
        refine ⟨min 1 (c₂ / (2 * (M + 1))), by positivity, fun t ht0 htδ => ?_⟩
        have ht1 : t ≤ 1 := le_of_lt (lt_of_lt_of_le htδ (min_le_left _ _))
        have htd : t < c₂ / (2 * (M + 1)) := lt_of_lt_of_le htδ (min_le_right _ _)
        have hbd := (abs_le.mp (happrox t ht0 ht1)).1
        rw [hc₀, hc₁, zero_add, zero_mul, zero_add] at hbd
        have h4 : 2 * (M + 1) * t < c₂ := by
          rwa [lt_div_iff₀ (by positivity), mul_comm] at htd
        have hpos : 0 < c₂ - M * t := by nlinarith
        have : 0 < t ^ 2 * (c₂ - M * t) := mul_pos (sq_pos_of_pos ht0) hpos
        linarith
    choose δ hδ_pos hδ using hδ_ex
    obtain ⟨j₀, hj₀⟩ := exists_eq_ciInf_of_finite (f := δ)
    set t := δ j₀ / 2
    have ht0 : 0 < t := half_pos (hδ_pos j₀)
    have hpos_all : ∀ j : κ, 0 < MvPolynomial.eval (t • x) (g i j) := by
      intro j
      apply hδ j t ht0
      have hle : δ j₀ ≤ δ j := by
        rw [hj₀]
        exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) j
      change δ j₀ / 2 < δ j
      linarith [hδ_pos j₀]
    obtain ⟨j₁, hj₁⟩ := exists_eq_ciInf_of_finite
      (f := fun j => MvPolynomial.eval (t • x) (g i j))
    have hinf_pos : 0 < ⨅ j, MvPolynomial.eval (t • x) (g i j) := hj₁ ▸ hpos_all j₁
    have hsup_pos : 0 < f (t • x) := by
      rw [hg]
      exact lt_of_lt_of_le hinf_pos
        (le_ciSup (f := fun i => ⨅ j, MvPolynomial.eval (t • x) (g i j))
          (Set.Finite.bddAbove (Set.finite_range _)) i)
    rw [hf_hom t ht0] at hsup_pos
    exact pos_of_mul_pos_right hsup_pos (sq_nonneg t)

/- Part 5: Algebraic identities for homogeneous degree-1 and degree-2 polynomials -/

lemma finsupp_degree_eq_one {σ : Type*} [DecidableEq σ] {d : σ →₀ ℕ} (hd : d.degree = 1) :
    ∃ k : σ, d = Finsupp.single k 1 := by
  have hne : d.support.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have : d.degree = 0 := by simp [Finsupp.degree_apply, hemp]
    omega
  obtain ⟨k, hk⟩ := hne
  have hdk_pos : 1 ≤ d k := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hk)
  have hsplit : d k + ∑ j ∈ d.support.erase k, d j = 1 := by
    rw [Finset.add_sum_erase _ _ hk]
    exact hd
  have hdk : d k = 1 := by omega
  have hrest : ∑ j ∈ d.support.erase k, d j = 0 := by omega
  refine ⟨k, ?_⟩
  ext j
  by_cases hjk : j = k
  · subst hjk; simp [hdk]
  · simp only [Finsupp.single_eq_of_ne hjk]
    by_contra hne0
    have hj : j ∈ d.support.erase k :=
      Finset.mem_erase.mpr ⟨hjk, Finsupp.mem_support_iff.mpr hne0⟩
    have := Finset.sum_eq_zero_iff.mp hrest j hj
    exact hne0 this

lemma finsupp_degree_eq_two {σ : Type*} [DecidableEq σ] {d : σ →₀ ℕ} (hd : d.degree = 2) :
    ∃ k₁ k₂ : σ, d = Finsupp.single k₁ 1 + Finsupp.single k₂ 1 := by
  have hne : d.support.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have : d.degree = 0 := by simp [Finsupp.degree_apply, hemp]
    omega
  obtain ⟨k₁, hk₁⟩ := hne
  have hdk₁ : 1 ≤ d k₁ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hk₁)
  let d' : σ →₀ ℕ := d - Finsupp.single k₁ 1
  have hadd : d = Finsupp.single k₁ 1 + d' := by
    ext j
    simp only [d', Finsupp.add_apply, Finsupp.tsub_apply]
    by_cases hjk : j = k₁
    · subst hjk; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_eq_of_ne hjk]
  have hd'_deg : d'.degree = 1 := by
    have hdeg_add : d.degree = (Finsupp.single k₁ 1).degree + d'.degree := by
      conv_lhs => rw [hadd]
      exact map_add Finsupp.degree _ _
    have hsingle : (Finsupp.single k₁ 1).degree = 1 := by simp [Finsupp.degree_apply]
    omega
  obtain ⟨k₂, hk₂⟩ := finsupp_degree_eq_one hd'_deg
  exact ⟨k₁, k₂, by rw [hadd, hk₂]⟩

lemma eval_monomial_single_one {n : ℕ} (k : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (MvPolynomial.monomial (Finsupp.single k 1) c) = c * x k := by
  simp [MvPolynomial.eval_monomial]

lemma eval_monomial_single_add {n : ℕ} (k₁ k₂ : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x
      (MvPolynomial.monomial (Finsupp.single k₁ 1 + Finsupp.single k₂ 1) c) =
      c * x k₁ * x k₂ := by
  rw [show MvPolynomial.monomial (Finsupp.single k₁ 1 + Finsupp.single k₂ 1) c =
      MvPolynomial.monomial (Finsupp.single k₁ 1) c *
      MvPolynomial.monomial (Finsupp.single k₂ 1) 1 by
    rw [MvPolynomial.monomial_mul, mul_one]]
  rw [map_mul, eval_monomial_single_one, eval_monomial_single_one, one_mul]

lemma eval_homog1_add {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 1)
    (u v : Fin n → ℝ) :
    MvPolynomial.eval (u + v) p = MvPolynomial.eval u p + MvPolynomial.eval v p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = 1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨k, rfl⟩ := finsupp_degree_eq_one hdeg
  simp only [eval_monomial_single_one, Pi.add_apply]
  ring

noncomputable def polar {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (u v : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval (u + v) p - MvPolynomial.eval u p - MvPolynomial.eval v p

lemma polar_homog2_add_sub {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 2)
    (u v : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (u + t • v) p - MvPolynomial.eval (u - t • v) p = 2 * t * polar p u v := by
  unfold polar
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨k₁, k₂, rfl⟩ := finsupp_degree_eq_two hdeg
  simp only [eval_monomial_single_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma polar_homog2_add_left {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 2)
    (u₁ u₂ v : Fin n → ℝ) :
    polar p (u₁ + u₂) v = polar p u₁ v + polar p u₂ v := by
  unfold polar
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨k₁, k₂, rfl⟩ := finsupp_degree_eq_two hdeg
  simp only [eval_monomial_single_add, Pi.add_apply]
  ring

lemma polar_homog2_smul_left {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 2)
    (c : ℝ) (u v : Fin n → ℝ) :
    polar p (c • u) v = c * polar p u v := by
  unfold polar
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨k₁, k₂, rfl⟩ := finsupp_degree_eq_two hdeg
  simp only [eval_monomial_single_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma polar_homog2_add_right {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 2)
    (u v₁ v₂ : Fin n → ℝ) :
    polar p u (v₁ + v₂) = polar p u v₁ + polar p u v₂ := by
  unfold polar
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨k₁, k₂, rfl⟩ := finsupp_degree_eq_two hdeg
  simp only [eval_monomial_single_add, Pi.add_apply]
  ring

lemma polar_homog2_second_diff {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 2)
    (z₀ z₁ z₂ : Fin n → ℝ) :
    MvPolynomial.eval (z₀ + (4 : ℝ) • z₁ + (4 : ℝ) • z₂) p -
    MvPolynomial.eval (z₀ + (4 : ℝ) • z₁ + z₂) p -
    MvPolynomial.eval (z₀ + z₁ + (4 : ℝ) • z₂) p +
    MvPolynomial.eval (z₀ + z₁ + z₂) p =
    9 * polar p z₁ z₂ := by
  unfold polar
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨k₁, k₂, rfl⟩ := finsupp_degree_eq_two hdeg
  simp only [eval_monomial_single_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- Part 6: Boundary orbit `O`, perturbations, and column-permutation invariance -/

def matD : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![1, 1, 0, 0, 0]
def matE : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![0, 0, 1, 1, 0]

noncomputable def orbitPt (U : Matrix (Fin 5) (Fin 5) ℝ) : Fin 30 → ℝ :=
  toVec (U * matD * Uᵀ) (U⁻¹ᵀ * matE * U⁻¹)

def matDX (ε η : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![1, 1, ε ^ 2, ε ^ 2, η * ε]
def matDY (ε η : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![ε ^ 2, ε ^ 2, 1, 1, η * ε]

noncomputable def pertPt (U : Matrix (Fin 5) (Fin 5) ℝ) (ε η : ℝ) : Fin 30 → ℝ :=
  toVec (U * matDX ε η * Uᵀ) (U⁻¹ᵀ * matDY ε η * U⁻¹)

lemma pertPt_zero (U : Matrix (Fin 5) (Fin 5) ℝ) (η : ℝ) :
    pertPt U 0 η = orbitPt U := by
  unfold pertPt orbitPt matDX matDY matD matE
  congr 2 <;> congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> simp

lemma continuous_pertPt (U : Matrix (Fin 5) (Fin 5) ℝ) (η : ℝ) :
    Continuous (fun ε : ℝ => pertPt U ε η) := by
  refine continuous_pi fun k => ?_
  unfold pertPt toVec
  split_ifs
  · simp only [Matrix.mul_apply, matDX, Matrix.diagonal_apply]
    refine continuous_finsetSum _ fun _ _ => Continuous.mul ?_ continuous_const
    refine continuous_finsetSum _ fun i _ => Continuous.mul continuous_const ?_
    split_ifs
    · fin_cases i <;> simp <;> fun_prop
    · exact continuous_const
  · simp only [Matrix.mul_apply, matDY, Matrix.diagonal_apply]
    refine continuous_finsetSum _ fun _ _ => Continuous.mul ?_ continuous_const
    refine continuous_finsetSum _ fun i _ => Continuous.mul continuous_const ?_
    split_ifs
    · fin_cases i <;> simp <;> fun_prop
    · exact continuous_const

lemma isSymm_conj_diagonal (A : Matrix (Fin 5) (Fin 5) ℝ) (d : Fin 5 → ℝ) :
    (A * Matrix.diagonal d * Aᵀ).IsSymm := by
  unfold Matrix.IsSymm
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma fFn_pertPt_pos {U : Matrix (Fin 5) (Fin 5) ℝ} (hU : U.det ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    fFn (pertPt U ε 1) = ε ^ 2 := by
  have hX : matX (pertPt U ε 1) = U * matDX ε 1 * Uᵀ :=
    matX_toVec (isSymm_conj_diagonal U _)
  have hY : matY (pertPt U ε 1) = U⁻¹ᵀ * matDY ε 1 * U⁻¹ :=
    matY_toVec (by
      have h := isSymm_conj_diagonal U⁻¹ᵀ ![ε ^ 2, ε ^ 2, 1, 1, 1 * ε]
      simpa [matDY, Matrix.transpose_transpose] using h)
  have hU_unit : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have hUT : Uᵀ * U⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul U hU_unit, Matrix.transpose_one]
  have hDmul : matDX ε 1 * matDY ε 1 = ε ^ 2 • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    ext i j
    simp only [matDX, matDY, Matrix.diagonal_mul_diagonal, Matrix.smul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with h
    · subst h; fin_cases i <;> simp [sq]
    · simp
  have hP : matX (pertPt U ε 1) * matY (pertPt U ε 1) =
      ε ^ 2 • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    rw [hX, hY]
    calc U * matDX ε 1 * Uᵀ * (U⁻¹ᵀ * matDY ε 1 * U⁻¹)
        = U * matDX ε 1 * (Uᵀ * U⁻¹ᵀ) * matDY ε 1 * U⁻¹ := by simp [Matrix.mul_assoc]
      _ = U * (matDX ε 1 * matDY ε 1) * U⁻¹ := by rw [hUT]; simp [Matrix.mul_assoc]
      _ = U * (ε ^ 2 • 1) * U⁻¹ := by rw [hDmul]
      _ = ε ^ 2 • (U * U⁻¹) := by simp
      _ = ε ^ 2 • 1 := by rw [Matrix.mul_nonsing_inv U hU_unit]
  have hq : ∀ idx : Idx, MvPolynomial.eval (pertPt U ε 1) (qPoly idx) = ε ^ 2 := by
    intro idx
    rw [eval_qPoly, hP]
    have hne : idx.1.1 ≠ idx.1.2.1 := idx.2
    simp [hne]
  have hh : hFn (pertPt U ε 1) = ε ^ 2 := by
    apply le_antisymm
    · obtain ⟨idx⟩ := idx_nonempty
      calc hFn (pertPt U ε 1) ≤ MvPolynomial.eval (pertPt U ε 1) (qPoly idx) :=
            Finset.inf'_le _ (Finset.mem_univ idx)
        _ = ε ^ 2 := hq idx
    · unfold hFn
      rw [Finset.le_inf'_iff]
      intro idx _
      rw [hq idx]
  have hdet : (matX (pertPt U ε 1)).det = U.det ^ 2 * ε ^ 5 := by
    rw [hX, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, matDX, Matrix.det_diagonal]
    simp [Fin.prod_univ_five]
    ring
  have hdet_pos : (matX (pertPt U ε 1)).det > 0 := by
    rw [hdet]
    exact mul_pos (sq_pos_of_ne_zero hU) (pow_pos hε 5)
  have hh_pos : hFn (pertPt U ε 1) > 0 := hh ▸ sq_pos_of_pos hε
  unfold fFn
  rw [if_pos ⟨hh_pos, hdet_pos⟩, hh]

lemma fFn_pertPt_neg {U : Matrix (Fin 5) (Fin 5) ℝ} (hU : U.det ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    fFn (pertPt U ε (-1)) = 0 := by
  have hX : matX (pertPt U ε (-1)) = U * matDX ε (-1) * Uᵀ :=
    matX_toVec (isSymm_conj_diagonal U _)
  have hdet : (matX (pertPt U ε (-1))).det = -(U.det ^ 2 * ε ^ 5) := by
    rw [hX, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, matDX, Matrix.det_diagonal]
    simp [Fin.prod_univ_five]
    ring
  have hdet_neg : ¬ (matX (pertPt U ε (-1))).det > 0 := by
    rw [hdet]
    have : 0 < U.det ^ 2 * ε ^ 5 := mul_pos (sq_pos_of_ne_zero hU) (pow_pos hε 5)
    linarith
  simp [fFn, hdet_neg]

/-- Rank-1 symmetric matrix blocks `eX U k = (M_k, 0)` and `eY U k = (0, N_k)`. -/
noncomputable def matM (U : Matrix (Fin 5) (Fin 5) ℝ) (k : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  U * Matrix.diagonal (Pi.single k (1 : ℝ)) * Uᵀ

noncomputable def matN (U : Matrix (Fin 5) (Fin 5) ℝ) (k : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  U⁻¹ᵀ * Matrix.diagonal (Pi.single k (1 : ℝ)) * U⁻¹

noncomputable def eX (U : Matrix (Fin 5) (Fin 5) ℝ) (k : Fin 5) : Fin 30 → ℝ :=
  toVec (matM U k) 0

noncomputable def eY (U : Matrix (Fin 5) (Fin 5) ℝ) (k : Fin 5) : Fin 30 → ℝ :=
  toVec 0 (matN U k)

lemma exists_perm_four (a b c d : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c ∧ σ 3 = d := by
  have hcard : ({a, b, c, d} : Finset (Fin 5)).card < (Finset.univ : Finset (Fin 5)).card := by
    calc ({a, b, c, d} : Finset (Fin 5)).card ≤ 4 := by
          refine (Finset.card_insert_le _ _).trans ?_
          refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
          refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
          simp
      _ < 5 := by omega
      _ = (Finset.univ : Finset (Fin 5)).card := by simp
  obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  rcases he with ⟨hea, heb, hec, hed⟩
  let f : Fin 5 → Fin 5 := ![a, b, c, d, e]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first | exact absurd hij hab | exact absurd hij hac | exact absurd hij had
            | exact absurd hij hbc | exact absurd hij hbd | exact absurd hij hcd
            | exact absurd hij.symm hab | exact absurd hij.symm hac | exact absurd hij.symm had
            | exact absurd hij.symm hbc | exact absurd hij.symm hbd | exact absurd hij.symm hcd
            | exact absurd hij.symm hea | exact absurd hij.symm heb | exact absurd hij.symm hec
            | exact absurd hij.symm hed | exact absurd hij hea | exact absurd hij heb
            | exact absurd hij hec | exact absurd hij hed
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), rfl, rfl, rfl, rfl⟩

/-- Any four distinct column indices `(a, b, c, d)` and nonzero scalars `(s₁, s₂, r₃, r₄)` produce
a point `s₁^2 eX a + s₂^2 eX b + r₃^2 eY c + r₄^2 eY d` lying on the boundary orbit `O`. -/
lemma mem_orbit_perm_scale {U : Matrix (Fin 5) (Fin 5) ℝ} (hU : U.det ≠ 0)
    (a b c d : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (s₁ s₂ r₃ r₄ : ℝ) (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0) (hr₃ : r₃ ≠ 0) (hr₄ : r₄ ≠ 0) :
    ∃ W : Matrix (Fin 5) (Fin 5) ℝ, W.det ≠ 0 ∧
      orbitPt W = s₁ ^ 2 • eX U a + s₂ ^ 2 • eX U b + r₃ ^ 2 • eY U c + r₄ ^ 2 • eY U d := by
  obtain ⟨σ, hσ0, hσ1, hσ2, hσ3⟩ := exists_perm_four a b c d hab hac had hbc hbd hcd
  let P : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j => if i = σ j then 1 else 0
  have hP_mul_PT : P * Pᵀ = 1 := by
    ext i j
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (σ.symm i)]
    · simp only [Equiv.apply_symm_apply, ↓reduceIte, one_mul]
      by_cases h : i = j <;> simp [h, eq_comm]
    · intro k _ hk
      have hne : i ≠ σ k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  let sd : Fin 5 → ℝ := ![s₁, s₂, r₃⁻¹, r₄⁻¹, 1]
  let sd_inv : Fin 5 → ℝ := ![s₁⁻¹, s₂⁻¹, r₃, r₄, 1]
  let S : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal sd
  let S_inv : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal sd_inv
  have hS_mul : S * S_inv = 1 := by
    ext i j
    simp only [S, S_inv, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h; fin_cases i <;> simp [sd, sd_inv, hs₁, hs₂, hr₃, hr₄]
    · rfl
  let W : Matrix (Fin 5) (Fin 5) ℝ := U * P * S
  let W_inv : Matrix (Fin 5) (Fin 5) ℝ := S_inv * Pᵀ * U⁻¹
  have hU_unit : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have hWW : W * W_inv = 1 := by
    calc W * W_inv
        = U * P * (S * S_inv) * Pᵀ * U⁻¹ := by simp [W, W_inv, Matrix.mul_assoc]
      _ = U * (P * Pᵀ) * U⁻¹ := by rw [hS_mul]; simp [Matrix.mul_assoc]
      _ = U * U⁻¹ := by rw [hP_mul_PT]; simp
      _ = 1 := Matrix.mul_nonsing_inv U hU_unit
  have hW_det : W.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hWW
  have hW_inv : W⁻¹ = W_inv := Matrix.inv_eq_right_inv hWW
  have hPconj : ∀ (v : Fin 5 → ℝ),
      P * Matrix.diagonal v * Pᵀ = Matrix.diagonal (fun i => v (σ.symm i)) := by
    intro v
    ext i j
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (σ.symm j)]
    · simp only [Equiv.apply_symm_apply, ↓reduceIte, mul_one]
      rw [Finset.sum_eq_single (σ.symm j)]
      · simp only [↓reduceIte, Equiv.apply_symm_apply]
        by_cases hij : i = j <;> simp [hij]
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro k _ hk
      have : j ≠ σ k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hX : W * matD * Wᵀ = s₁ ^ 2 • matM U a + s₂ ^ 2 • matM U b := by
    have hdiag : S * matD * Sᵀ = Matrix.diagonal (fun k => sd k * (![1, 1, 0, 0, 0] k) * sd k) := by
      simp [S, matD, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    have hPdiag : P * (S * matD * Sᵀ) * Pᵀ =
        s₁ ^ 2 • Matrix.diagonal (Pi.single a 1) + s₂ ^ 2 • Matrix.diagonal (Pi.single b 1) := by
      rw [hdiag, hPconj]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        rcases eq_or_ne i a with rfl | hia
        · have ha0 : σ.symm i = 0 := σ.symm_apply_eq.mpr hσ0.symm
          simp [ha0, sd, hab, sq]
        · rcases eq_or_ne i b with rfl | hib
          · have hb1 : σ.symm i = 1 := σ.symm_apply_eq.mpr hσ1.symm
            simp [hb1, sd, Ne.symm hab, sq]
          · have hne0 : σ.symm i ≠ 0 := fun h => hia (by rw [← hσ0, ← h, Equiv.apply_symm_apply])
            have hne1 : σ.symm i ≠ 1 := fun h => hib (by rw [← hσ1, ← h, Equiv.apply_symm_apply])
            have hzero : (![1, 1, 0, 0, 0] : Fin 5 → ℝ) (σ.symm i) = 0 := by
              generalize hk : σ.symm i = k at hne0 hne1
              fin_cases k <;> simp_all
            simp [hzero, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]
      · simp [hij]
    calc W * matD * Wᵀ
        = U * (P * (S * matD * Sᵀ) * Pᵀ) * Uᵀ := by
            simp [W, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = U * (s₁ ^ 2 • Matrix.diagonal (Pi.single a 1) +
               s₂ ^ 2 • Matrix.diagonal (Pi.single b 1)) * Uᵀ := by rw [hPdiag]
      _ = s₁ ^ 2 • matM U a + s₂ ^ 2 • matM U b := by
            simp only [matM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hY : W⁻¹ᵀ * matE * W⁻¹ = r₃ ^ 2 • matN U c + r₄ ^ 2 • matN U d := by
    have hdiag : S_invᵀ * matE * S_inv =
        Matrix.diagonal (fun k => sd_inv k * (![0, 0, 1, 1, 0] k) * sd_inv k) := by
      simp [S_inv, matE, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    have hPdiag : P * (S_invᵀ * matE * S_inv) * Pᵀ =
        r₃ ^ 2 • Matrix.diagonal (Pi.single c 1) + r₄ ^ 2 • Matrix.diagonal (Pi.single d 1) := by
      rw [hdiag, hPconj]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        rcases eq_or_ne i c with rfl | hic
        · have hc2 : σ.symm i = 2 := σ.symm_apply_eq.mpr hσ2.symm
          simp [hc2, sd_inv, hcd, sq]
        · rcases eq_or_ne i d with rfl | hid
          · have hd3 : σ.symm i = 3 := σ.symm_apply_eq.mpr hσ3.symm
            simp [hd3, sd_inv, Ne.symm hcd, sq]
          · have hne2 : σ.symm i ≠ 2 := fun h => hic (by rw [← hσ2, ← h, Equiv.apply_symm_apply])
            have hne3 : σ.symm i ≠ 3 := fun h => hid (by rw [← hσ3, ← h, Equiv.apply_symm_apply])
            have hzero : (![0, 0, 1, 1, 0] : Fin 5 → ℝ) (σ.symm i) = 0 := by
              generalize hk : σ.symm i = k at hne2 hne3
              fin_cases k <;> simp_all
            simp [hzero, Pi.single_eq_of_ne hic, Pi.single_eq_of_ne hid]
      · simp [hij]
    calc W⁻¹ᵀ * matE * W⁻¹
        = U⁻¹ᵀ * (P * (S_invᵀ * matE * S_inv) * Pᵀ) * U⁻¹ := by
            rw [hW_inv]
            simp [W_inv, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = U⁻¹ᵀ * (r₃ ^ 2 • Matrix.diagonal (Pi.single c 1) +
                  r₄ ^ 2 • Matrix.diagonal (Pi.single d 1)) * U⁻¹ := by rw [hPdiag]
      _ = r₃ ^ 2 • matN U c + r₄ ^ 2 • matN U d := by
            simp only [matN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨W, hW_det, ?_⟩
  unfold orbitPt eX eY
  rw [hX, hY]
  rw [← toVec_smul, ← toVec_smul, ← toVec_smul, ← toVec_smul]
  simp only [smul_zero, ← toVec_add, add_zero, zero_add]

lemma pertPt_decomp (U : Matrix (Fin 5) (Fin 5) ℝ) (ε η : ℝ) :
    pertPt U ε η =
      (eX U 0 + eX U 1 + ε ^ 2 • eX U 2 + ε ^ 2 • eX U 3 +
       ε ^ 2 • eY U 0 + ε ^ 2 • eY U 1 + eY U 2 + eY U 3) +
      (η * ε) • (eX U 4 + eY U 4) := by
  have hDX : matDX ε η =
      Matrix.diagonal (Pi.single 0 1) + Matrix.diagonal (Pi.single 1 1) +
      ε ^ 2 • Matrix.diagonal (Pi.single 2 1) + ε ^ 2 • Matrix.diagonal (Pi.single 3 1) +
      (η * ε) • Matrix.diagonal (Pi.single 4 1) := by
    ext i j
    simp only [matDX, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; fin_cases i <;> simp
    · simp [h]
  have hDY : matDY ε η =
      ε ^ 2 • Matrix.diagonal (Pi.single 0 1) + ε ^ 2 • Matrix.diagonal (Pi.single 1 1) +
      Matrix.diagonal (Pi.single 2 1) + Matrix.diagonal (Pi.single 3 1) +
      (η * ε) • Matrix.diagonal (Pi.single 4 1) := by
    ext i j
    simp only [matDY, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; fin_cases i <;> simp
    · simp [h]
  have hX : U * matDX ε η * Uᵀ =
      matM U 0 + matM U 1 + ε ^ 2 • matM U 2 + ε ^ 2 • matM U 3 + (η * ε) • matM U 4 := by
    rw [hDX]
    simp only [matM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hY : U⁻¹ᵀ * matDY ε η * U⁻¹ =
      ε ^ 2 • matN U 0 + ε ^ 2 • matN U 1 + matN U 2 + matN U 3 + (η * ε) • matN U 4 := by
    rw [hDY]
    simp only [matN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  unfold pertPt eX eY
  rw [hX, hY]
  simp only [← toVec_smul, ← toVec_add, smul_zero, add_zero, zero_add]

lemma homog1_pert_eq {U : Matrix (Fin 5) (Fin 5) ℝ} (hU : U.det ≠ 0)
    {p : MvPolynomial (Fin 30) ℝ} (hp : p.IsHomogeneous 1)
    (hvan : ∀ W : Matrix (Fin 5) (Fin 5) ℝ, W.det ≠ 0 → MvPolynomial.eval (orbitPt W) p = 0)
    (ε : ℝ) :
    MvPolynomial.eval (pertPt U ε 1) p = MvPolynomial.eval (pertPt U ε (-1)) p := by
  have heX4 : MvPolynomial.eval (eX U 4) p = 0 := by
    obtain ⟨W₁, hW₁, hpt₁⟩ := mem_orbit_perm_scale hU 4 0 1 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨W₂, hW₂, hpt₂⟩ := mem_orbit_perm_scale hU 4 0 1 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      2 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h1 := hvan W₁ hW₁
    have h2 := hvan W₂ hW₂
    rw [hpt₁] at h1; rw [hpt₂] at h2
    simp only [eval_homog1_add hp, eval_isHomogeneous_smul hp, pow_one] at h1 h2
    linarith
  have heY4 : MvPolynomial.eval (eY U 4) p = 0 := by
    obtain ⟨W₁, hW₁, hpt₁⟩ := mem_orbit_perm_scale hU 0 1 4 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨W₂, hW₂, hpt₂⟩ := mem_orbit_perm_scale hU 0 1 4 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      1 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h1 := hvan W₁ hW₁
    have h2 := hvan W₂ hW₂
    rw [hpt₁] at h1; rw [hpt₂] at h2
    simp only [eval_homog1_add hp, eval_isHomogeneous_smul hp, pow_one] at h1 h2
    linarith
  rw [pertPt_decomp U ε 1, pertPt_decomp U ε (-1)]
  simp only [eval_homog1_add hp, eval_isHomogeneous_smul hp, pow_one, heX4, heY4, add_zero,
    mul_zero]

lemma exists_two_other (k : Fin 5) (hk : k ≠ 4) :
    ∃ c d : Fin 5, c ≠ k ∧ c ≠ 4 ∧ d ≠ k ∧ d ≠ 4 ∧ c ≠ d := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide, by decide⟩
  · exact absurd rfl hk

lemma homog2_pert_eq {U : Matrix (Fin 5) (Fin 5) ℝ} (hU : U.det ≠ 0)
    {p : MvPolynomial (Fin 30) ℝ} (hp : p.IsHomogeneous 2)
    (hvan : ∀ W : Matrix (Fin 5) (Fin 5) ℝ, W.det ≠ 0 → MvPolynomial.eval (orbitPt W) p = 0)
    (ε : ℝ) :
    MvPolynomial.eval (pertPt U ε 1) p = MvPolynomial.eval (pertPt U ε (-1)) p := by
  have hpolar_zero : ∀ (z₀ z₁ z₂ : Fin 30 → ℝ),
      (∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = 2) → (s₂ = 1 ∨ s₂ = 2) →
        MvPolynomial.eval (z₀ + s₁ ^ 2 • z₁ + s₂ ^ 2 • z₂) p = 0) →
      polar p z₁ z₂ = 0 := by
    intro z₀ z₁ z₂ hz
    have h11 := hz 1 1 (Or.inl rfl) (Or.inl rfl)
    have h12 := hz 1 2 (Or.inl rfl) (Or.inr rfl)
    have h21 := hz 2 1 (Or.inr rfl) (Or.inl rfl)
    have h22 := hz 2 2 (Or.inr rfl) (Or.inr rfl)
    norm_num at h11 h12 h21 h22
    have hdiff := polar_homog2_second_diff hp z₀ z₁ z₂
    linarith
  have hXX : ∀ k : Fin 5, k ≠ 4 → polar p (eX U k) (eX U 4) = 0 := by
    intro k hk
    obtain ⟨c, d, hck, hc4, hdk, hd4, hcd⟩ := exists_two_other k hk
    apply hpolar_zero (eY U c + eY U d)
    intro s₁ s₂ hs₁ hs₂
    have hs₁0 : s₁ ≠ 0 := by rcases hs₁ with rfl | rfl <;> norm_num
    have hs₂0 : s₂ ≠ 0 := by rcases hs₂ with rfl | rfl <;> norm_num
    obtain ⟨W, hW, hpt⟩ := mem_orbit_perm_scale hU k 4 c d
      hk hck.symm hdk.symm hc4.symm hd4.symm hcd s₁ s₂ 1 1 hs₁0 hs₂0 one_ne_zero one_ne_zero
    have h := hvan W hW
    rw [hpt] at h
    have heq : eY U c + eY U d + s₁ ^ 2 • eX U k + s₂ ^ 2 • eX U 4 =
        s₁ ^ 2 • eX U k + s₂ ^ 2 • eX U 4 + (1 : ℝ) ^ 2 • eY U c + (1 : ℝ) ^ 2 • eY U d := by
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [heq, h]
  have hXY : ∀ k : Fin 5, k ≠ 4 → polar p (eX U k) (eY U 4) = 0 := by
    intro k hk
    obtain ⟨b, d, hbk, hb4, hdk, hd4, hbd⟩ := exists_two_other k hk
    apply hpolar_zero (eX U b + eY U d)
    intro s₁ s₂ hs₁ hs₂
    have hs₁0 : s₁ ≠ 0 := by rcases hs₁ with rfl | rfl <;> norm_num
    have hs₂0 : s₂ ≠ 0 := by rcases hs₂ with rfl | rfl <;> norm_num
    obtain ⟨W, hW, hpt⟩ := mem_orbit_perm_scale hU k b 4 d
      hbk.symm hk hdk.symm hb4 hbd hd4.symm s₁ 1 s₂ 1 hs₁0 one_ne_zero hs₂0 one_ne_zero
    have h := hvan W hW
    rw [hpt] at h
    have heq : eX U b + eY U d + s₁ ^ 2 • eX U k + s₂ ^ 2 • eY U 4 =
        s₁ ^ 2 • eX U k + (1 : ℝ) ^ 2 • eX U b + s₂ ^ 2 • eY U 4 + (1 : ℝ) ^ 2 • eY U d := by
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [heq, h]
  have hYX : ∀ k : Fin 5, k ≠ 4 → polar p (eY U k) (eX U 4) = 0 := by
    intro k hk
    obtain ⟨b, d, hbk, hb4, hdk, hd4, hbd⟩ := exists_two_other k hk
    apply hpolar_zero (eX U b + eY U d)
    intro s₁ s₂ hs₁ hs₂
    have hs₁0 : s₁ ≠ 0 := by rcases hs₁ with rfl | rfl <;> norm_num
    have hs₂0 : s₂ ≠ 0 := by rcases hs₂ with rfl | rfl <;> norm_num
    obtain ⟨W, hW, hpt⟩ := mem_orbit_perm_scale hU 4 b k d
      hb4.symm hk.symm hd4.symm hbk hbd hdk.symm s₂ 1 s₁ 1 hs₂0 one_ne_zero hs₁0 one_ne_zero
    have h := hvan W hW
    rw [hpt] at h
    have heq : eX U b + eY U d + s₁ ^ 2 • eY U k + s₂ ^ 2 • eX U 4 =
        s₂ ^ 2 • eX U 4 + (1 : ℝ) ^ 2 • eX U b + s₁ ^ 2 • eY U k + (1 : ℝ) ^ 2 • eY U d := by
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [heq, h]
  have hYY : ∀ k : Fin 5, k ≠ 4 → polar p (eY U k) (eY U 4) = 0 := by
    intro k hk
    obtain ⟨a, b, hak, ha4, hbk, hb4, hab⟩ := exists_two_other k hk
    apply hpolar_zero (eX U a + eX U b)
    intro s₁ s₂ hs₁ hs₂
    have hs₁0 : s₁ ≠ 0 := by rcases hs₁ with rfl | rfl <;> norm_num
    have hs₂0 : s₂ ≠ 0 := by rcases hs₂ with rfl | rfl <;> norm_num
    obtain ⟨W, hW, hpt⟩ := mem_orbit_perm_scale hU a b k 4
      hab hak ha4 hbk hb4 hk 1 1 s₁ s₂ one_ne_zero one_ne_zero hs₁0 hs₂0
    have h := hvan W hW
    rw [hpt] at h
    have heq : eX U a + eX U b + s₁ ^ 2 • eY U k + s₂ ^ 2 • eY U 4 =
        (1 : ℝ) ^ 2 • eX U a + (1 : ℝ) ^ 2 • eX U b + s₁ ^ 2 • eY U k + s₂ ^ 2 • eY U 4 := by
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [heq, h]
  set v : Fin 30 → ℝ :=
    eX U 0 + eX U 1 + ε ^ 2 • eX U 2 + ε ^ 2 • eX U 3 +
    ε ^ 2 • eY U 0 + ε ^ 2 • eY U 1 + eY U 2 + eY U 3
  set w : Fin 30 → ℝ := eX U 4 + eY U 4
  have hp1 : pertPt U ε 1 = v + ε • w := by
    rw [pertPt_decomp, one_mul]
  have hpm1 : pertPt U ε (-1) = v - ε • w := by
    rw [pertPt_decomp, neg_one_mul, neg_smul, ← sub_eq_add_neg]
  rw [hp1, hpm1, ← sub_eq_zero, polar_homog2_add_sub hp]
  have hvw : polar p v w = 0 := by
    simp only [v, w, polar_homog2_add_left hp, polar_homog2_smul_left hp,
      polar_homog2_add_right hp]
    rw [hXX 0 (by decide), hXX 1 (by decide), hXX 2 (by decide), hXX 3 (by decide),
        hXY 0 (by decide), hXY 1 (by decide), hXY 2 (by decide), hXY 3 (by decide),
        hYX 0 (by decide), hYX 1 (by decide), hYX 2 (by decide), hYX 3 (by decide),
        hYY 0 (by decide), hYY 1 (by decide), hYY 2 (by decide), hYY 3 (by decide)]
    ring
  rw [hvw, mul_zero]

/- Part 7: Generic point on the orbit `O` -/

def matToFun (U : Matrix (Fin 5) (Fin 5) ℝ) : Fin 5 × Fin 5 → ℝ := fun p => U p.1 p.2

noncomputable def matUPoly : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 5 × Fin 5) ℝ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

noncomputable def detUPoly : MvPolynomial (Fin 5 × Fin 5) ℝ := matUPoly.det

noncomputable def matDPoly : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 5 × Fin 5) ℝ) :=
  Matrix.diagonal ![1, 1, 0, 0, 0]

noncomputable def matEPoly : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 5 × Fin 5) ℝ) :=
  Matrix.diagonal ![0, 0, 1, 1, 0]

noncomputable def orbitSubst : MvPolynomial (Fin 30) ℝ →ₐ[ℝ] MvPolynomial (Fin 5 × Fin 5) ℝ :=
  MvPolynomial.aeval fun k : Fin 30 =>
    if hk : k.val < 15 then
      let p := symPair ⟨k.val, hk⟩
      detUPoly ^ 2 * (matUPoly * matDPoly * matUPolyᵀ) p.1 p.2
    else
      let p := symPair ⟨k.val - 15, by omega⟩
      (matUPoly.adjugateᵀ * matEPoly * matUPoly.adjugate) p.1 p.2

lemma eval_detUPoly (U : Matrix (Fin 5) (Fin 5) ℝ) :
    MvPolynomial.eval (matToFun U) detUPoly = U.det := by
  rw [detUPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [matUPoly, matToFun, Matrix.map_apply]

lemma eval_orbitSubst {d : ℕ} {p : MvPolynomial (Fin 30) ℝ} (hp : p.IsHomogeneous d)
    {U : Matrix (Fin 5) (Fin 5) ℝ} (hU : U.det ≠ 0) :
    MvPolynomial.eval (matToFun U) (orbitSubst p) =
      (U.det ^ 2) ^ d * MvPolynomial.eval (orbitPt U) p := by
  have hmapU : matUPoly.map (MvPolynomial.eval (matToFun U)) = U := by
    ext i j; simp [matUPoly, matToFun, Matrix.map_apply]
  have hmapD : matDPoly.map (MvPolynomial.eval (matToFun U)) = matD := by
    ext i j; simp only [matDPoly, matD, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; fin_cases i <;> simp
    · simp
  have hmapE : matEPoly.map (MvPolynomial.eval (matToFun U)) = matE := by
    ext i j; simp only [matEPoly, matE, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; fin_cases i <;> simp
    · simp
  have hmapAdj : matUPoly.adjugate.map (MvPolynomial.eval (matToFun U)) = U.adjugate := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, hmapU]
  have hadj_eq : U.adjugate = U.det • U⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hU, one_smul]
  have harg : (fun k : Fin 30 => MvPolynomial.eval (matToFun U)
      (if hk : k.val < 15 then
        let q := symPair ⟨k.val, hk⟩
        detUPoly ^ 2 * (matUPoly * matDPoly * matUPolyᵀ) q.1 q.2
      else
        let q := symPair ⟨k.val - 15, by omega⟩
        (matUPoly.adjugateᵀ * matEPoly * matUPoly.adjugate) q.1 q.2)) =
      U.det ^ 2 • orbitPt U := by
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, orbitPt, toVec]
    split_ifs with hk
    · set q := symPair ⟨k.val, hk⟩
      rw [map_mul, map_pow, eval_detUPoly]
      congr 1
      have hmul : (matUPoly * matDPoly * matUPolyᵀ).map
          (MvPolynomial.eval (matToFun U)) = U * matD * Uᵀ := by
        simp [Matrix.map_mul, Matrix.transpose_map, hmapU, hmapD]
      simpa [Matrix.map_apply] using congr_fun (congr_fun hmul q.1) q.2
    · set q := symPair ⟨k.val - 15, by omega⟩
      have hmul : (matUPoly.adjugateᵀ * matEPoly * matUPoly.adjugate).map
          (MvPolynomial.eval (matToFun U)) = U.adjugateᵀ * matE * U.adjugate := by
        simp [Matrix.map_mul, Matrix.transpose_map, hmapAdj, hmapE]
      have hval := congr_fun (congr_fun hmul q.1) q.2
      simp only [Matrix.map_apply] at hval
      rw [hval, hadj_eq]
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
        smul_eq_mul]
      ring
  have heval_comp : ∀ q : MvPolynomial (Fin 30) ℝ,
      MvPolynomial.eval (matToFun U) (orbitSubst q) =
      MvPolynomial.eval (U.det ^ 2 • orbitPt U) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [orbitSubst]
    | add q₁ q₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
    | mul_X q₁ k ih =>
      simp only [map_mul, ih, MvPolynomial.eval_X]
      congr 1
      simpa [orbitSubst] using congr_fun harg k
  rw [heval_comp p, eval_isHomogeneous_smul hp]

lemma exists_generic_U (S : Finset (MvPolynomial (Fin 30) ℝ))
    (hShom : ∀ p ∈ S, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2)
    (hSnz : ∀ p ∈ S, ∃ U : Matrix (Fin 5) (Fin 5) ℝ,
      U.det ≠ 0 ∧ MvPolynomial.eval (orbitPt U) p ≠ 0) :
    ∃ U : Matrix (Fin 5) (Fin 5) ℝ, U.det ≠ 0 ∧
      ∀ p ∈ S, MvPolynomial.eval (orbitPt U) p ≠ 0 := by
  have hdet_ne : detUPoly ≠ 0 := by
    intro h0
    have h1 := eval_detUPoly (1 : Matrix (Fin 5) (Fin 5) ℝ)
    rw [h0, map_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hprod_ne : ∀ p ∈ S, orbitSubst p ≠ 0 := by
    intro p hp h0
    obtain ⟨U₀, hU₀, hpU₀⟩ := hSnz p hp
    rcases hShom p hp with h1 | h2
    · have he := eval_orbitSubst h1 hU₀
      rw [h0, map_zero] at he
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hU₀)) hpU₀ he.symm
    · have he := eval_orbitSubst h2 hU₀
      rw [h0, map_zero] at he
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hU₀)) hpU₀ he.symm
  let Q : MvPolynomial (Fin 5 × Fin 5) ℝ := detUPoly * ∏ p ∈ S, orbitSubst p
  have hQ_ne : Q ≠ 0 :=
    mul_ne_zero hdet_ne (Finset.prod_ne_zero_iff.mpr hprod_ne)
  have hex : ∃ u : Fin 5 × Fin 5 → ℝ, MvPolynomial.eval u Q ≠ 0 := by
    by_contra hall
    have hall' : ∀ u : Fin 5 × Fin 5 → ℝ, MvPolynomial.eval u Q = 0 := fun u =>
      not_ne_iff.mp fun hne => hall ⟨u, hne⟩
    apply hQ_ne
    exact MvPolynomial.funext fun u => by rw [hall' u, map_zero]
  obtain ⟨u, hu⟩ := hex
  let U : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j => u (i, j)
  have hu_eq : matToFun U = u := by ext ⟨i, j⟩; rfl
  rw [← hu_eq] at hu
  simp only [Q, map_mul, map_prod, eval_detUPoly] at hu
  have hU_det : U.det ≠ 0 := left_ne_zero_of_mul hu
  have hprod_eval : (∏ p ∈ S, MvPolynomial.eval (matToFun U) (orbitSubst p)) ≠ 0 :=
    right_ne_zero_of_mul hu
  refine ⟨U, hU_det, fun p hp => ?_⟩
  have hp_ne : MvPolynomial.eval (matToFun U) (orbitSubst p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hprod_eval p hp
  rcases hShom p hp with h1 | h2
  · rw [eval_orbitSubst h1 hU_det] at hp_ne
    exact right_ne_zero_of_mul hp_ne
  · rw [eval_orbitSubst h2 hU_det] at hp_ne
    exact right_ne_zero_of_mul hp_ne

end Counterexample

end PierceBirkhoff

open PierceBirkhoff

theorem OMA.disproof : ¬ (type_of% @PierceBirkhoff.pierce_birkhoff_conjecture) := by
  classical
  intro hPB
  obtain ⟨ι, κ, g, hι, hκ, hg⟩ := hPB Counterexample.fFn Counterexample.isPiecewiseMvPolynomial_fFn
  have hι_ne : Nonempty ι := by
    by_contra hemp
    have : IsEmpty ι := not_nonempty_iff.mp hemp
    have h0 := hg (Counterexample.toVec 1 1)
    have hsup : (⨆ i : ι, ⨅ j : κ, MvPolynomial.eval (Counterexample.toVec 1 1) (g i j)) = 0 := by
      rw [iSup, Set.range_eq_empty, Real.sSup_empty]
    rw [Counterexample.fFn_toVec_one_one, hsup] at h0
    norm_num at h0
  have hκ_ne : Nonempty κ := by
    by_contra hemp
    have : IsEmpty κ := not_nonempty_iff.mp hemp
    have h0 := hg (Counterexample.toVec 1 1)
    have hinf : ∀ i : ι, (⨅ j : κ, MvPolynomial.eval (Counterexample.toVec 1 1) (g i j)) = 0 := by
      intro i
      rw [iInf, Set.range_eq_empty, Real.sInf_empty]
    simp only [hinf, ciSup_const] at h0
    rw [Counterexample.fFn_toVec_one_one] at h0
    norm_num at h0
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  let S₁_set : Finset (MvPolynomial (Fin 30) ℝ) :=
    (Finset.univ : Finset (ι × κ)).image (fun p => (g p.1 p.2).homogeneousComponent 1)
  let S₂_set : Finset (MvPolynomial (Fin 30) ℝ) :=
    (Finset.univ : Finset (ι × κ)).image (fun p => (g p.1 p.2).homogeneousComponent 2)
  let S : Finset (MvPolynomial (Fin 30) ℝ) := S₁_set ∪ S₂_set
  let Snz : Finset (MvPolynomial (Fin 30) ℝ) :=
    S.filter fun p => ∃ U : Matrix (Fin 5) (Fin 5) ℝ,
      U.det ≠ 0 ∧ MvPolynomial.eval (Counterexample.orbitPt U) p ≠ 0
  have hSnz_hom : ∀ p ∈ Snz, p.IsHomogeneous 1 ∨ p.IsHomogeneous 2 := by
    intro p hp
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    rcases Finset.mem_union.mp hpS with h1 | h2
    · obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp h1
      exact Or.inl (MvPolynomial.homogeneousComponent_isHomogeneous 1 _)
    · obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp h2
      exact Or.inr (MvPolynomial.homogeneousComponent_isHomogeneous 2 _)
  obtain ⟨U, hU_det, hU_nz⟩ := Counterexample.exists_generic_U Snz hSnz_hom
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hsmall : ∀ p ∈ Snz, ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      (MvPolynomial.eval (Counterexample.pertPt U ε 1) p > 0 ↔
        MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p > 0) ∧
      (MvPolynomial.eval (Counterexample.pertPt U ε 1) p = 0 ↔
        MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p = 0) := by
    intro p hp
    have hval := hU_nz p hp
    have hcont_pos : Continuous (fun ε : ℝ => MvPolynomial.eval (Counterexample.pertPt U ε 1) p) :=
      (MvPolynomial.continuous_eval p).comp (Counterexample.continuous_pertPt U 1)
    have hcont_neg : Continuous (fun ε : ℝ => MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p) :=
      (MvPolynomial.continuous_eval p).comp (Counterexample.continuous_pertPt U (-1))
    set v₀ := MvPolynomial.eval (Counterexample.orbitPt U) p
    have h0_pos : MvPolynomial.eval (Counterexample.pertPt U 0 1) p = v₀ := by
      rw [Counterexample.pertPt_zero]
    have h0_neg : MvPolynomial.eval (Counterexample.pertPt U 0 (-1)) p = v₀ := by
      rw [Counterexample.pertPt_zero]
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcont_pos.continuousAt
      (|v₀| / 2) (half_pos (abs_pos.mpr hval))
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcont_neg.continuousAt
      (|v₀| / 2) (half_pos (abs_pos.mpr hval))
    refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun ε hε0 hεδ => ?_⟩
    have h1 : |MvPolynomial.eval (Counterexample.pertPt U ε 1) p - v₀| < |v₀| / 2 := by
      have := hδ₁ (show dist ε 0 < δ₁ by
        rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
        exact lt_of_lt_of_le hεδ (min_le_left _ _))
      rwa [Real.dist_eq, h0_pos] at this
    have h2 : |MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p - v₀| < |v₀| / 2 := by
      have := hδ₂ (show dist ε 0 < δ₂ by
        rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
        exact lt_of_lt_of_le hεδ (min_le_right _ _))
      rwa [Real.dist_eq, h0_neg] at this
    rcases lt_or_gt_of_ne hval with hv_neg | hv_pos
    · rw [abs_of_neg hv_neg] at h1 h2
      have h1' : MvPolynomial.eval (Counterexample.pertPt U ε 1) p < 0 := by
        linarith [(abs_lt.mp h1).2]
      have h2' : MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p < 0 := by
        linarith [(abs_lt.mp h2).2]
      exact ⟨by simp [not_lt.mpr (le_of_lt h1'), not_lt.mpr (le_of_lt h2')],
             by simp [ne_of_lt h1', ne_of_lt h2']⟩
    · rw [abs_of_pos hv_pos] at h1 h2
      have h1' : MvPolynomial.eval (Counterexample.pertPt U ε 1) p > 0 := by
        linarith [(abs_lt.mp h1).1]
      have h2' : MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p > 0 := by
        linarith [(abs_lt.mp h2).1]
      exact ⟨by simp [h1', h2'], by simp [ne_of_gt h1', ne_of_gt h2']⟩
  have hε_ex : ∃ ε > 0, ∀ p ∈ Snz,
      (MvPolynomial.eval (Counterexample.pertPt U ε 1) p > 0 ↔
        MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p > 0) ∧
      (MvPolynomial.eval (Counterexample.pertPt U ε 1) p = 0 ↔
        MvPolynomial.eval (Counterexample.pertPt U ε (-1)) p = 0) := by
    by_cases hemp : Snz.Nonempty
    · choose δ hδ_pos hδ using fun p : Snz => hsmall p.1 p.2
      obtain ⟨p₀, -, hp₀⟩ := Finset.exists_min_image (Finset.univ : Finset Snz) δ
        (Finset.univ_nonempty_iff.mpr hemp.to_subtype)
      refine ⟨δ p₀ / 2, half_pos (hδ_pos p₀), fun p hp => ?_⟩
      have hle : δ p₀ ≤ δ ⟨p, hp⟩ := hp₀ ⟨p, hp⟩ (Finset.mem_univ _)
      exact hδ ⟨p, hp⟩ (δ p₀ / 2) (half_pos (hδ_pos p₀)) (by linarith [hδ_pos p₀])
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      exact ⟨1, zero_lt_one, fun p hp => by simp [hemp] at hp⟩
  obtain ⟨ε, hε_pos, hε_snz⟩ := hε_ex
  have hsame : ∀ (i : ι) (j : κ),
      Counterexample.LexPos (g i j) (Counterexample.pertPt U ε 1) ↔
      Counterexample.LexPos (g i j) (Counterexample.pertPt U ε (-1)) := by
    intro i j
    have hc₀ : MvPolynomial.eval (Counterexample.pertPt U ε 1) ((g i j).homogeneousComponent 0) =
        MvPolynomial.eval (Counterexample.pertPt U ε (-1)) ((g i j).homogeneousComponent 0) := by
      simp
    have h1_mem : (g i j).homogeneousComponent 1 ∈ S :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have h2_mem : (g i j).homogeneousComponent 2 ∈ S :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have hc₁ :
        (MvPolynomial.eval (Counterexample.pertPt U ε 1) ((g i j).homogeneousComponent 1) > 0 ↔
          MvPolynomial.eval (Counterexample.pertPt U ε (-1)) ((g i j).homogeneousComponent 1) > 0) ∧
        (MvPolynomial.eval (Counterexample.pertPt U ε 1) ((g i j).homogeneousComponent 1) = 0 ↔
          MvPolynomial.eval (Counterexample.pertPt U ε (-1)) ((g i j).homogeneousComponent 1) = 0) := by
      by_cases hmem : (g i j).homogeneousComponent 1 ∈ Snz
      · exact hε_snz _ hmem
      · have hvan : ∀ W : Matrix (Fin 5) (Fin 5) ℝ, W.det ≠ 0 →
            MvPolynomial.eval (Counterexample.orbitPt W) ((g i j).homogeneousComponent 1) = 0 := by
          intro W hW
          by_contra hne
          exact hmem (Finset.mem_filter.mpr ⟨h1_mem, ⟨W, hW, hne⟩⟩)
        have heq := Counterexample.homog1_pert_eq hU_det
          (MvPolynomial.homogeneousComponent_isHomogeneous 1 _) hvan ε
        rw [heq]
        exact ⟨Iff.rfl, Iff.rfl⟩
    have hc₂ :
        MvPolynomial.eval (Counterexample.pertPt U ε 1) ((g i j).homogeneousComponent 2) > 0 ↔
        MvPolynomial.eval (Counterexample.pertPt U ε (-1)) ((g i j).homogeneousComponent 2) > 0 := by
      by_cases hmem : (g i j).homogeneousComponent 2 ∈ Snz
      · exact (hε_snz _ hmem).1
      · have hvan : ∀ W : Matrix (Fin 5) (Fin 5) ℝ, W.det ≠ 0 →
            MvPolynomial.eval (Counterexample.orbitPt W) ((g i j).homogeneousComponent 2) = 0 := by
          intro W hW
          by_contra hne
          exact hmem (Finset.mem_filter.mpr ⟨h2_mem, ⟨W, hW, hne⟩⟩)
        have heq := Counterexample.homog2_pert_eq hU_det
          (MvPolynomial.homogeneousComponent_isHomogeneous 2 _) hvan ε
        rw [heq]
    unfold Counterexample.LexPos
    simp only [hc₀, hc₁.1, hc₁.2, hc₂]
  have hiff : Counterexample.fFn (Counterexample.pertPt U ε 1) > 0 ↔
      Counterexample.fFn (Counterexample.pertPt U ε (-1)) > 0 := by
    rw [Counterexample.pos_iff_lexPos (fun _ ht => Counterexample.fFn_smul ht) hg,
        Counterexample.pos_iff_lexPos (fun _ ht => Counterexample.fFn_smul ht) hg]
    exact exists_congr fun i => forall_congr' fun j => hsame i j
  rw [Counterexample.fFn_pertPt_pos hU_det hε_pos,
      Counterexample.fFn_pertPt_neg hU_det hε_pos] at hiff
  have hpos : ε ^ 2 > 0 := sq_pos_of_pos hε_pos
  exact lt_irrefl (0 : ℝ) (hiff.mp hpos)
