import OMAStatements.S_arxiv_2508_01163
import Mathlib

/-!
Disproof of the graph inertia conjecture from arXiv:2508.01163 (Akbari, Elphick, Kumar, Pragada):
  2 * nPos G <= nNeg G * (nNeg G + 1).

Counterexample: the 15-vertex graph W_5 of Hongzhang Chen and Jianxi Li
(Counterexamples to a conjecture on graph inertia, arXiv:2605.07196, Aug 2026),
formed from K_5 on vertices 0..4 and the Petersen graph KG(5, 2) on vertices 5..14
with cross-edges a_i ~ b_S iff i in S.

We exhibit 11 explicit integer vectors in Z^15 whose A(W_5)-Gram matrix is diagonal with
strictly positive entries (20, 10, 6, 18, 36, 60, 4, 12, 12, 36, 18). Projecting onto the
positive eigenspace of A(W_5) is therefore injective, giving 11 <= nPos W_5. Since positive
and negative eigenvalues are disjoint among the 15 eigenvalues, nNeg W_5 <= 4, contradicting
2 * nPos W_5 <= nNeg W_5 * (nNeg W_5 + 1) because 22 > 20.
-/

namespace OMA.Arxiv250801163Disproof

open Matrix SimpleGraph OMA.S_arxiv_2508_01163

private def pairOf : Fin 15 → ℕ × ℕ
  | ⟨5, _⟩ => (0, 1)
  | ⟨6, _⟩ => (0, 2)
  | ⟨7, _⟩ => (0, 3)
  | ⟨8, _⟩ => (0, 4)
  | ⟨9, _⟩ => (1, 2)
  | ⟨10, _⟩ => (1, 3)
  | ⟨11, _⟩ => (1, 4)
  | ⟨12, _⟩ => (2, 3)
  | ⟨13, _⟩ => (2, 4)
  | ⟨14, _⟩ => (3, 4)
  | _ => (0, 0)

private def w5AdjBool (u v : Fin 15) : Bool :=
  if u.val < 5 then
    if v.val < 5 then
      u.val != v.val
    else
      let p := pairOf v
      u.val == p.1 || u.val == p.2
  else
    if v.val < 5 then
      let p := pairOf u
      v.val == p.1 || v.val == p.2
    else
      let pu := pairOf u
      let pv := pairOf v
      pu.1 != pv.1 && pu.1 != pv.2 && pu.2 != pv.1 && pu.2 != pv.2

private lemma w5AdjBool_symm : ∀ u v : Fin 15, w5AdjBool u v = true → w5AdjBool v u = true := by
  decide

private lemma w5AdjBool_irrefl : ∀ u : Fin 15, w5AdjBool u u ≠ true := by
  decide

def w5Graph : SimpleGraph (Fin 15) where
  Adj u v := w5AdjBool u v = true
  symm := ⟨fun u v h => w5AdjBool_symm u v h⟩
  loopless := ⟨fun u h => w5AdjBool_irrefl u h⟩

instance : DecidableRel w5Graph.Adj := fun u v =>
  inferInstanceAs (Decidable (w5AdjBool u v = true))

private def bRows : Fin 11 → Fin 15 → ℤ
  | ⟨0, _⟩ => ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | ⟨1, _⟩ => ![-1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  | ⟨2, _⟩ => ![3, -3, 0, 0, 0, 0, 1, 1, 1, -1, -1, -1, 0, 0, 0]
  | ⟨3, _⟩ => ![3, 3, -6, 0, 0, 2, -1, 1, 1, -1, 1, 1, -2, -2, 0]
  | ⟨4, _⟩ => ![3, 3, 3, -9, 0, 2, 2, -2, 1, 2, -2, 1, -2, 1, -3]
  | ⟨5, _⟩ => ![3, 3, 3, 3, -12, 2, 2, 2, -3, 2, 2, -3, 2, -3, -3]
  | ⟨6, _⟩ => ![0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 1, 0, 0]
  | ⟨7, _⟩ => ![0, 0, 0, 0, 0, 1, -2, 1, 0, 1, -2, 0, 1, 0, 0]
  | ⟨8, _⟩ => ![0, 0, 0, 0, 0, 1, 0, 1, -2, -1, 0, 0, -1, 2, 0]
  | ⟨9, _⟩ => ![0, 0, 0, 0, 0, 1, -2, -1, 2, 1, 2, -4, -1, 2, 0]
  | ⟨10, _⟩ => ![0, 0, 0, 0, 0, 1, 1, -1, -1, 1, -1, -1, -1, -1, 3]

private def diagVal : Fin 11 → ℤ :=
  ![20, 10, 6, 18, 36, 60, 4, 12, 12, 36, 18]

private lemma diagVal_pos (k : Fin 11) : (0 : ℝ) < (diagVal k : ℝ) := by
  have h : (0 : ℤ) < diagVal k := by fin_cases k <;> decide
  exact_mod_cast h

private def gramInt (i j : Fin 11) : ℤ :=
  (List.finRange 15).foldl (fun acc u =>
    acc + bRows i u * (List.finRange 15).foldl (fun acc2 v =>
      if w5AdjBool u v then acc2 + bRows j v else acc2) 0) 0

private lemma gramInt_eq (i j : Fin 11) :
    gramInt i j = if i = j then diagVal i else 0 := by
  revert i j
  decide

private lemma list_foldl_add {α : Type*} (l : List α) (f : α → ℤ) (init : ℤ) :
    l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

private lemma list_foldl_ite {α : Type*} (l : List α) (p : α → Bool) (f : α → ℤ) (init : ℤ) :
    l.foldl (fun acc x => if p x then acc + f x else acc) init =
      init + (l.map (fun x => if p x then f x else 0)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    cases p a <;> simp [ih, add_assoc]

private lemma gramInt_eq_sum (i j : Fin 11) :
    (gramInt i j : ℝ) =
      ∑ u : Fin 15, ∑ v : Fin 15,
        (bRows i u : ℝ) * (w5Graph.adjMatrix ℝ u v) * (bRows j v : ℝ) := by
  have h1 : gramInt i j =
      ∑ u : Fin 15, bRows i u * ∑ v : Fin 15, if w5AdjBool u v then bRows j v else 0 := by
    unfold gramInt
    rw [list_foldl_add, zero_add]
    have hinner : ∀ u : Fin 15,
        (List.finRange 15).foldl (fun acc2 v => if w5AdjBool u v then acc2 + bRows j v else acc2) 0 =
          ∑ v : Fin 15, if w5AdjBool u v then bRows j v else 0 := by
      intro u
      rw [list_foldl_ite, zero_add, ← Fin.sum_univ_def]
    simp_rw [hinner]
    rw [← Fin.sum_univ_def]
  rw [h1]
  push_cast
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [SimpleGraph.adjMatrix_apply]
  change (bRows i u : ℝ) * (if w5AdjBool u v = true then (bRows j v : ℝ) else 0) =
    (bRows i u : ℝ) * (if w5AdjBool u v = true then (1 : ℝ) else 0) * (bRows j v : ℝ)
  cases w5AdjBool u v <;> simp

private noncomputable def liftLin : (Fin 11 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 15) where
  toFun c := WithLp.toLp 2 (fun u => ∑ k : Fin 11, c k * (bRows k u : ℝ))
  map_add' c₁ c₂ := by
    ext u
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    ext u
    simp [Finset.mul_sum, mul_assoc]

private lemma quad_liftLin (c : Fin 11 → ℝ) :
    inner ℝ (liftLin c) (Matrix.toEuclideanLin (w5Graph.adjMatrix ℝ) (liftLin c)) =
      ∑ k : Fin 11, (diagVal k : ℝ) * (c k) ^ 2 := by
  have hL : inner ℝ (liftLin c) (Matrix.toEuclideanLin (w5Graph.adjMatrix ℝ) (liftLin c)) =
      ∑ u : Fin 15, ∑ v : Fin 15,
        (∑ i : Fin 11, c i * (bRows i u : ℝ)) * (w5Graph.adjMatrix ℝ u v) *
          (∑ j : Fin 11, c j * (bRows j v : ℝ)) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, liftLin,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hL]
  have hexp :
      (∑ u : Fin 15, ∑ v : Fin 15,
        (∑ i : Fin 11, c i * (bRows i u : ℝ)) * (w5Graph.adjMatrix ℝ u v) *
          (∑ j : Fin 11, c j * (bRows j v : ℝ))) =
      ∑ i : Fin 11, ∑ j : Fin 11,
        c i * c j * (∑ u : Fin 15, ∑ v : Fin 15,
          (bRows i u : ℝ) * (w5Graph.adjMatrix ℝ u v) * (bRows j v : ℝ)) := by
    let F : Fin 15 → Fin 15 → Fin 11 → Fin 11 → ℝ := fun u v i j =>
      c i * c j * ((bRows i u : ℝ) * (w5Graph.adjMatrix ℝ u v) * (bRows j v : ℝ))
    have hstep1 :
        (∑ u : Fin 15, ∑ v : Fin 15,
          (∑ i : Fin 11, c i * (bRows i u : ℝ)) * (w5Graph.adjMatrix ℝ u v) *
            (∑ j : Fin 11, c j * (bRows j v : ℝ))) =
        ∑ u : Fin 15, ∑ v : Fin 15, ∑ i : Fin 11, ∑ j : Fin 11, F u v i j := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [F]; ring
    have hstep2 :
        (∑ u : Fin 15, ∑ v : Fin 15, ∑ i : Fin 11, ∑ j : Fin 11, F u v i j) =
        ∑ i : Fin 11, ∑ j : Fin 11, ∑ u : Fin 15, ∑ v : Fin 15, F u v i j := by
      calc
        ∑ u : Fin 15, ∑ v : Fin 15, ∑ i : Fin 11, ∑ j : Fin 11, F u v i j
            = ∑ u : Fin 15, ∑ i : Fin 11, ∑ v : Fin 15, ∑ j : Fin 11, F u v i j := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
        _ = ∑ i : Fin 11, ∑ u : Fin 15, ∑ v : Fin 15, ∑ j : Fin 11, F u v i j := Finset.sum_comm
        _ = ∑ i : Fin 11, ∑ u : Fin 15, ∑ j : Fin 11, ∑ v : Fin 15, F u v i j := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => Finset.sum_comm
        _ = ∑ i : Fin 11, ∑ j : Fin 11, ∑ u : Fin 15, ∑ v : Fin 15, F u v i j := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hstep1, hstep2]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp [F]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
  rw [hexp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hgram : ∀ j : Fin 11,
      (∑ u : Fin 15, ∑ v : Fin 15,
        (bRows i u : ℝ) * (w5Graph.adjMatrix ℝ u v) * (bRows j v : ℝ)) =
      if i = j then (diagVal i : ℝ) else 0 := by
    intro j
    rw [← gramInt_eq_sum, gramInt_eq]
    split_ifs <;> simp
  simp_rw [hgram]
  simp [sq, mul_comm]

private lemma quad_spectral (v : EuclideanSpace ℝ (Fin 15)) :
    inner ℝ v (Matrix.toEuclideanLin (w5Graph.adjMatrix ℝ) v) =
      ∑ i : Fin 15,
        (w5Graph.isHermitian_adjMatrix ℝ).eigenvalues i *
          (inner ℝ ((w5Graph.isHermitian_adjMatrix ℝ).eigenvectorBasis i) v) ^ 2 := by
  let hA := w5Graph.isHermitian_adjMatrix ℝ
  let b := hA.eigenvectorBasis
  let ev := hA.eigenvalues
  have hv : v = ∑ i : Fin 15, (inner ℝ (b i) v) • b i := (b.sum_repr' v).symm
  have hAv : Matrix.toEuclideanLin (w5Graph.adjMatrix ℝ) v =
      ∑ i : Fin 15, (ev i * inner ℝ (b i) v) • b i := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    have heig : Matrix.toEuclideanLin (w5Graph.adjMatrix ℝ) (b i) = ev i • b i := by
      ext u
      have := congrFun (hA.mulVec_eigenvectorBasis i) u
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, b, ev] using this
    rw [heig, smul_smul, mul_comm]
  have hEq : inner ℝ v (Matrix.toEuclideanLin (w5Graph.adjMatrix ℝ) v) =
      inner ℝ (∑ i : Fin 15, (inner ℝ (b i) v) • b i)
        (∑ j : Fin 15, (ev j * inner ℝ (b j) v) • b j) := by
    rw [← hv, ← hAv]
  rw [hEq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · have hbi : inner ℝ (b i) (b i) = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
      norm_num
    rw [inner_smul_left, inner_smul_right, hbi]
    simp only [conj_trivial, mul_one]
    ring
  · intro j _ hji
    rw [inner_smul_left, inner_smul_right, b.orthonormal.2 (Ne.symm hji)]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

lemma eleven_le_nPos_w5 : 11 ≤ nPos w5Graph := by
  let hA := w5Graph.isHermitian_adjMatrix ℝ
  let b := hA.eigenvectorBasis
  let ev := hA.eigenvalues
  let P := {i : Fin 15 // 0 < ev i}
  let Φ : (Fin 11 → ℝ) →ₗ[ℝ] (P → ℝ) :=
    { toFun := fun c i => inner ℝ (b i.1) (liftLin c)
      map_add' := fun c₁ c₂ => by
        ext i; simp [map_add, inner_add_right]
      map_smul' := fun r c => by
        ext i; simp [map_smul, inner_smul_right] }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hle : inner ℝ (liftLin c) (Matrix.toEuclideanLin (w5Graph.adjMatrix ℝ) (liftLin c)) ≤ 0 := by
      rw [quad_spectral]
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : 0 < ev i
      · have h0 : inner ℝ ((w5Graph.isHermitian_adjMatrix ℝ).eigenvectorBasis i) (liftLin c) = 0 :=
          congrFun hc ⟨i, hi⟩
        rw [h0]
        simp
      · have hle0 : (w5Graph.isHermitian_adjMatrix ℝ).eigenvalues i ≤ 0 := le_of_not_gt hi
        exact mul_nonpos_of_nonpos_of_nonneg hle0 (sq_nonneg _)
    rw [quad_liftLin] at hle
    have hge : 0 ≤ ∑ k : Fin 11, (diagVal k : ℝ) * (c k) ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (diagVal_pos k).le (sq_nonneg _)
    have hzero : ∑ k : Fin 11, (diagVal k : ℝ) * (c k) ^ 2 = 0 := le_antisymm hle hge
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (diagVal_pos k).le (sq_nonneg (c k))).mp hzero
    ext k
    have hk := hall k (Finset.mem_univ k)
    rcases mul_eq_zero.mp hk with hd | hsq
    · exact absurd hd (diagVal_pos k).ne'
    · exact sq_eq_zero_iff.mp hsq
  have hfin := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_pi, Fintype.card_fin] at hfin
  have hcard : Fintype.card P = nPos w5Graph := by
    unfold nPos P
    exact Fintype.card_subtype _
  omega

end OMA.Arxiv250801163Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2508_01163.main) := by
  intro h
  have h15 := h 15 OMA.Arxiv250801163Disproof.w5Graph
  have hpos : 11 ≤ OMA.S_arxiv_2508_01163.nPos OMA.Arxiv250801163Disproof.w5Graph :=
    OMA.Arxiv250801163Disproof.eleven_le_nPos_w5
  have hdisj : Disjoint
      (Finset.univ.filter fun i : Fin 15 =>
        0 < (OMA.Arxiv250801163Disproof.w5Graph.isHermitian_adjMatrix ℝ).eigenvalues i)
      (Finset.univ.filter fun i : Fin 15 =>
        (OMA.Arxiv250801163Disproof.w5Graph.isHermitian_adjMatrix ℝ).eigenvalues i < 0) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    linarith
  have hsum :
      OMA.S_arxiv_2508_01163.nPos OMA.Arxiv250801163Disproof.w5Graph +
      OMA.S_arxiv_2508_01163.nNeg OMA.Arxiv250801163Disproof.w5Graph ≤ 15 := by
    unfold OMA.S_arxiv_2508_01163.nPos OMA.S_arxiv_2508_01163.nNeg
    rw [← Finset.card_union_of_disjoint hdisj]
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hneg : OMA.S_arxiv_2508_01163.nNeg OMA.Arxiv250801163Disproof.w5Graph ≤ 4 := by omega
  nlinarith
