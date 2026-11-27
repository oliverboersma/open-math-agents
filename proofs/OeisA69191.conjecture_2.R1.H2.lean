import OMAReductions.R_OeisA69191_conjecture_2_R1

/-! Rank-one interlacing via the two Courant–Fischer bounds.
Port of Jon Crall's discrete min-max proof from Erotemic/mathlib4,
commit 695af67e71ef73beecc3c15fd3f3546da1adbe9b.
Copyright (c) 2026 Jon Crall. All rights reserved. Used under Apache-2.0.
The upper-direction proof allows larger subspaces. The coordinate-kernel
intersection and the bridge to the characteristic polynomial are new here. -/
-- Credit: @marcusbuffett

section
open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}








private noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))


private theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace,
    finrank_span_eq_card (b := fun i : {i : Fin n // p i} => b i)
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
    Fintype.card_subtype]


private theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E)
    (p : Fin n → Prop) {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  rw [b.repr_apply_apply]
  
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi j.2
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]


private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

namespace LinearMap.IsSymmetric







theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  have key : ⟪T x, x⟫_𝕜
      = ((∑ i : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
      mul_left_comm, RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]


private theorem re_inner_map_self_le_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp


private theorem le_re_inner_map_self_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp







private theorem card_filter_le (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i)).card = n - (k : ℕ) := by
  have : (Finset.univ.filter (fun i : Fin n => k ≤ i)).card
      = (Finset.Ici k).card := by
    congr 1
    ext i
    simp [Finset.mem_Ici]
  rw [this, Fin.card_Ici]


private theorem card_filter_ge (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  have : (Finset.univ.filter (fun i : Fin n => i ≤ k)).card
      = (Finset.Iic k).card := by
    congr 1
    ext i
    simp [Finset.mem_Iic]
  rw [this, Fin.card_Iic]


theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : (k : ℕ) + 1 ≤ finrank 𝕜 V) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := specSubspace b (fun i : Fin n => k ≤ i) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_specSubspace, card_filter_le]
  
  have hsum : n < finrank 𝕜 V + finrank 𝕜 W := by
    rw [hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ := by
    intro hbot
    have hle := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hbot, finrank_bot, add_zero] at hle
    have hsup : finrank 𝕜 (↑(V ⊔ W) : Submodule 𝕜 E) ≤ n := by
      rw [← hn]; exact Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩
  
  
  have hxW : x ∈ W := W.smul_mem _ hzW
  calc RCLike.re ⟪T x, x⟫_𝕜
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        re_inner_map_self_le_of_mem_specSubspace hT hn
          (fun _ hik => hT.eigenvalues_antitone hn hik) hxW
    _ = hT.eigenvalues hn k := by rw [hnx]; ring


theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  refine ⟨specSubspace b (fun i : Fin n => i ≤ k), ?_, ?_⟩
  · rw [finrank_specSubspace, card_filter_ge]
  · intro x hxV hnx
    
    
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
          le_re_inner_map_self_of_mem_specSubspace hT hn
            (fun _ hik => hT.eigenvalues_antitone hn hik) hxV


end LinearMap.IsSymmetric
end
open Polynomial Matrix Module
open scoped InnerProductSpace

private theorem sorted_eigenvalues_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {f : Fin n → ℝ} (hf : Antitone f)
    (hp : A.charpoly = ∏ i, (X - C (f i))) :
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin = f := by
  have hroot : A.charpoly.roots = Finset.univ.val.map f := by
    rw [hp, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsorted := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).sort_roots_charpoly_eq_eigenvalues
    finrank_euclideanSpace_fin
  have hcp : (Matrix.toEuclideanLin A).charpoly = A.charpoly := by
    rw [Matrix.toEuclideanLin_eq_toLin, Matrix.charpoly_toLin]
  rw [hcp] at hsorted
  apply List.ofFn_inj.mp
  rw [← hsorted]
  change (A.charpoly.roots.map id).sort (· ≥ ·) = List.ofFn f
  rw [Multiset.map_id, hroot, Fin.univ_val_map, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hf.sortedGE_ofFn

theorem OMA.solution : OMA.R_OeisA69191_conjecture_2_R1.H2 := by
  intro n A hA k c hc f g hf hg hAf hBg
  let B := A - Matrix.single k k c
  have hB : B.IsHermitian := hA.sub (by simp [Matrix.IsHermitian, Matrix.conjTranspose_single])
  let T := Matrix.toEuclideanLin A
  let S := Matrix.toEuclideanLin B
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hS : S.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hTf : hT.eigenvalues hdim = f := sorted_eigenvalues_eq hA hf hAf
  have hSg : hS.eigenvalues hdim = g := sorted_eigenvalues_eq hB hg hBg
  have hcoord (x : (EuclideanSpace ℝ (Fin n))) : inner ℝ (S x) x = inner ℝ (T x) x - c * (x k)^2 := by
    change inner ℝ (Matrix.toEuclideanLin (A - Matrix.single k k c) x) x = _
    rw [map_sub, LinearMap.sub_apply, inner_sub_left]
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      Matrix.single_mulVec_eq]
    simp [dotProduct_smul, dotProduct_single, pow_two, mul_comm, mul_left_comm, mul_assoc]
  constructor
  · intro i
    obtain ⟨V, hd, hV⟩ := hS.forall_unit_vector_eigenvalue_le_re_inner hdim i
    obtain ⟨x, hx, hn, hspec⟩ := hT.exists_unit_vector_re_inner_le_eigenvalue hdim i V hd.ge
    have hμ := hV x hx hn
    rw [hSg] at hμ
    rw [hTf] at hspec
    change g i ≤ inner ℝ (S x) x at hμ
    change inner ℝ (T x) x ≤ f i at hspec
    rw [hcoord] at hμ
    linarith [mul_nonneg hc (sq_nonneg (x k))]
  · intro i j hij
    obtain ⟨V, hd, hV⟩ := hT.forall_unit_vector_eigenvalue_le_re_inner hdim j
    let L : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ := PiLp.projₗ 2 (fun _ : Fin n => ℝ) k
    let K := LinearMap.ker L
    have hk : n ≤ finrank ℝ K + 1 := by
      have h := L.finrank_range_add_finrank_ker
      have hr : finrank ℝ L.range ≤ 1 := by simpa using L.range.finrank_le
      change finrank ℝ L.range + finrank ℝ K = finrank ℝ (EuclideanSpace ℝ (Fin n)) at h
      omega
    have hVk : i.val + 1 ≤ finrank ℝ (V ⊓ K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
      have h : finrank ℝ (V ⊔ K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) +
          finrank ℝ (V ⊓ K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) =
          finrank ℝ V + finrank ℝ K := Submodule.finrank_sup_add_finrank_inf_eq V K
      rw [hd] at h
      have hs : finrank ℝ (V ⊔ K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ≤ n := (V ⊔ K).finrank_le.trans hdim.le
      have hij' : i.val < j.val := hij
      omega
    obtain ⟨x, hx, hn, hμ⟩ := hS.exists_unit_vector_re_inner_le_eigenvalue hdim i (V ⊓ K) hVk
    have hspec := hV x hx.1 hn
    have hxk : x k = 0 := hx.2
    rw [hSg] at hμ
    rw [hTf] at hspec
    change inner ℝ (S x) x ≤ g i at hμ
    change f j ≤ inner ℝ (T x) x at hspec
    rw [hcoord, hxk] at hμ
    linarith

