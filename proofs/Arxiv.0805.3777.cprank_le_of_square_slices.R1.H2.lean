import OMAReductions.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1
import Mathlib

-- Step Arxiv.0805.3777.cprank_le_of_square_slices.R1.H2: hypothesis H2 of reduction Arxiv.0805.3777.cprank_le_of_square_slices.R1
-- Credit: @ivillar
--
-- REUSE. The section Pencil (PRank, span_ker, prank_of_noLeft, prank_le) is taken unchanged from
-- the merged proof proofs/Arxiv.0805.3777.isMaxRank_two.lean of this repository (PR #3391, same
-- owner). The section Regular is the proof of the sibling step H1 of this reduction (same
-- owner), with the extra conclusion that no diagonal coefficient pair vanishes. The sections
-- Abstract and Final are new.

/-!
# Pencils of square matrices: diagonal up to rank `n / 2`

H2 asks, for a singular pencil `(A, B)` of complex `n × n` matrices, for invertible `P`, `Q` with
`A = P * diagonal a * Q + ∑ j, α j • u j (v j)ᵀ` and `B = P * diagonal b * Q + ∑ j, β j • u j (v j)ᵀ`
with `n / 2` rank-one matrices. The proof below gives this for every pencil (`all_pencils`); the
classical route is Kronecker's canonical form, which is avoided.

`DP r A B` says that linear maps `A B : V → W` send a basis `bV i` to `a i • bW i`, `b i • bW i`
for a basis `bW`, up to a pencil of rank at most `r`. Matrices and linear maps are related by
`basis_data_of_matrix` and `matrix_of_DP`.

* **Regular pencils** (`regular_pencil`, `regular_abs`). The pencil is a sum of at most
  `n + n / 2` rank-one pencils (`prank_le`). An invertible sum of more than `n` rank-one
  matrices stays invertible after removing a suitable term (`exists_erase`, by the matrix
  determinant lemma and a trace count), so `n` of the terms have an invertible sum and give
  `P`, `Q`. No diagonal coefficient pair `(a k, b k)` vanishes.
* **A common kernel vector and a common left kernel functional** (`DP_of_zero_block`): the
  pencil is a pencil of size `n - 1` plus a zero block; induction.
* **No common kernel vector** (`DP_of_no_kernel`). Let `V1` be the span of the eigenvectors
  (`A x + t • B x = 0`) with `t` outside a finite set `F`; it does not depend on `F` once `F` is
  large (`exists_stable`). Then `A V1` lies in `W1 = B V1`, and for a suitable `ts` the map
  `G = A + ts • B` has `ker G ≤ V1` and `G V1 = W1`. With `W3` a complement of the range of `G`
  and `W1' = W1 ⊔ W3`, the pencil induced on `V ⧸ V1 → W ⧸ W1'` is regular (`G` induces a
  bijection), so the regular case applies to it. Now choose a basis `xs` of `V1` of eigenvectors
  whose parameters avoid `0` and the finitely many parameters of the diagonal pairs of the
  quotient. The vectors `B (xs k)` span `W1`; a subfamily is a basis of `W1` and the other `xs`,
  as many as `dim W3`, are matched with a basis of `W3`: this costs one rank-one pencil for each
  of them, and they are at most half of the `xs` because there is no common kernel vector
  (`card_le_two_mul`). After these corrections the pencil is block triangular with diagonal
  blocks whose coefficient pairs are independent across the two blocks, and `glue` removes the
  off-diagonal block by a Cramer solve for each pair of indices.
* **No common left kernel functional**: transpose and apply the previous case.
-/

open Module

namespace SqH2

section Pencil

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The pair `(A, B)` is a sum of at most `r` rank-one pencils. -/
def PRank (r : ℕ) (A B : V →ₗ[ℂ] W) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → ℂ) (ψ : ι → V →ₗ[ℂ] ℂ) (u : ι → W),
    Fintype.card ι ≤ r ∧ A = ∑ i, a i • (ψ i).smulRight (u i) ∧
      B = ∑ i, b i • (ψ i).smulRight (u i)

theorem PRank.mono {r r' : ℕ} {A B : V →ₗ[ℂ] W} (h : PRank r A B) (hr : r ≤ r') :
    PRank r' A B := by
  obtain ⟨ι, _, a, b, ψ, u, hc, hA, hB⟩ := h
  exact ⟨ι, _, a, b, ψ, u, hc.trans hr, hA, hB⟩

theorem PRank.comp_right {V' : Type} [AddCommGroup V'] [Module ℂ V'] {r : ℕ}
    {A B : V →ₗ[ℂ] W} (h : PRank r A B) (M : V' →ₗ[ℂ] V) :
    PRank r (A ∘ₗ M) (B ∘ₗ M) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  refine ⟨ι, _, a, b, fun i => ψ i ∘ₗ M, u, hc, ?_, ?_⟩ <;>
  · ext x
    simp [LinearMap.sum_apply]

theorem PRank.comp_left {W' : Type} [AddCommGroup W'] [Module ℂ W'] {r : ℕ}
    {A B : V →ₗ[ℂ] W} (h : PRank r A B) (L : W →ₗ[ℂ] W') :
    PRank r (L ∘ₗ A) (L ∘ₗ B) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  refine ⟨ι, _, a, b, ψ, fun i => L (u i), hc, ?_, ?_⟩ <;>
  · ext x
    simp [LinearMap.sum_apply]

theorem PRank.add_smulRight {r : ℕ} {A B : V →ₗ[ℂ] W} (h : PRank r A B) (a b : ℂ)
    (ψ : V →ₗ[ℂ] ℂ) (u : W) :
    PRank (r + 1) (A + a • ψ.smulRight u) (B + b • ψ.smulRight u) := by
  obtain ⟨ι, _, a', b', ψ', u', hc, rfl, rfl⟩ := h
  refine ⟨Option ι, inferInstance, fun o => o.elim a a', fun o => o.elim b b',
    fun o => o.elim ψ ψ', fun o => o.elim u u', by simpa using hc, ?_, ?_⟩ <;>
  · rw [Fintype.sum_option]
    simp [add_comm]

theorem prank_of_basis {ι : Type} [Fintype ι] (bs : Basis ι ℂ V) (t : ι → ℂ)
    (A B : V →ₗ[ℂ] W) (h : ∀ i, A (bs i) = t i • B (bs i)) :
    PRank (Fintype.card ι) A B := by
  classical
  refine ⟨ι, inferInstance, t, fun _ => 1, bs.coord, fun i => B (bs i), le_rfl, ?_, ?_⟩ <;>
  · refine bs.ext fun j => ?_
    simp [LinearMap.sum_apply, h, Finsupp.single_apply]

/-- No left eigenvector: every nontrivial combination is surjective. -/
def NoLeft (A B : V →ₗ[ℂ] W) : Prop :=
  ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → Function.Surjective (s • A + t • B)

theorem NoLeft.finrank_lt [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {A B : V →ₗ[ℂ] W}
    (h : NoLeft A B) (hW : 0 < finrank ℂ W) : finrank ℂ W < finrank ℂ V := by
  by_contra hlt
  have hB : Function.Surjective B := by
    have := h 0 1 (Or.inr one_ne_zero)
    simpa using this
  have hle : finrank ℂ W ≤ finrank ℂ V := LinearMap.finrank_le_finrank_of_surjective hB
  have heq : finrank ℂ V = finrank ℂ W := by omega
  have hBi : Function.Injective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hB
  let e : V ≃ₗ[ℂ] W := LinearEquiv.ofBijective B ⟨hBi, hB⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (e.symm.toLinearMap ∘ₗ A)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have h1 : e.symm (A v) = c • v := by
    have := hv.apply_eq_smul
    simpa using this
  have h2 : A v = c • B v := by
    have h := congrArg e h1
    rw [LinearEquiv.apply_symm_apply, map_smul] at h
    exact h
  have hs := h 1 (-c) (Or.inl one_ne_zero)
  have hi : Function.Injective ((1 : ℂ) • A + (-c) • B) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hs
  have h3 : ((1 : ℂ) • A + (-c) • B) v = ((1 : ℂ) • A + (-c) • B) 0 := by
    simp [h2]
  exact hv.2 (hi h3)

theorem span_ker (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B : V →ₗ[ℂ] W), finrank ℂ V = n → NoLeft A B → ∀ Λ : Finset ℂ,
    (⨆ (t : ℂ) (_ : t ∉ Λ), LinearMap.ker (A + t • B)) = ⊤ := by
  induction n with
  | zero =>
    intro V W _ _ _ _ _ _ A B hn hNL Λ
    have hW : finrank ℂ W = 0 := by
      by_contra hW
      have := hNL.finrank_lt (Nat.pos_of_ne_zero hW)
      omega
    have : Subsingleton W := Module.finrank_zero_iff.mp hW
    obtain ⟨t0, ht0⟩ := Infinite.exists_notMem_finset Λ
    refine top_le_iff.mp (le_iSup₂_of_le t0 ht0 ?_)
    intro x _
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro V W _ _ _ _ _ _ A B hn hNL Λ
    obtain ⟨t0, ht0⟩ := Infinite.exists_notMem_finset Λ
    by_cases hW : finrank ℂ W = 0
    · have : Subsingleton W := Module.finrank_zero_iff.mp hW
      refine top_le_iff.mp (le_iSup₂_of_le t0 ht0 ?_)
      intro x _
      exact Subsingleton.elim _ _
    have hlt := hNL.finrank_lt (Nat.pos_of_ne_zero hW)
    have hker : LinearMap.ker (A + t0 • B) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
    obtain ⟨v, hvk, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hAv : A v = -(t0 • B v) := by
      have h : A v + t0 • B v = 0 := by simpa using hvk
      exact eq_neg_of_add_eq_zero_left h
    set p : Submodule ℂ V := Submodule.span ℂ {v} with hp
    set q : Submodule ℂ W := Submodule.span ℂ {B v} with hq
    have hBq : B v ∈ q := Submodule.mem_span_singleton_self _
    have hpA : p ≤ q.comap A := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      show A v ∈ q
      rw [hAv]
      exact q.neg_mem (q.smul_mem _ hBq)
    have hpB : p ≤ q.comap B := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      exact hBq
    have hNL' : NoLeft (p.mapQ q A hpA) (p.mapQ q B hpB) := by
      intro s t hst w'
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective q w'
      obtain ⟨x, hx⟩ := hNL s t hst w
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [← hx]
      simp [Submodule.mapQ_apply]
    have hfr : finrank ℂ (V ⧸ p) = n := by
      have h1 := Submodule.finrank_quotient_add_finrank p
      have h2 : finrank ℂ p = 1 := finrank_span_singleton hv
      omega
    have IH := ih (V ⧸ p) (W ⧸ q) (p.mapQ q A hpA) (p.mapQ q B hpB) hfr hNL' (insert t0 Λ)
    set S : Submodule ℂ V := ⨆ (t : ℂ) (_ : t ∉ Λ), LinearMap.ker (A + t • B) with hS
    have hvS : v ∈ S := (le_iSup₂_of_le (f := fun (t : ℂ) (_ : t ∉ Λ) => LinearMap.ker (A + t • B))
      t0 ht0 le_rfl) hvk
    have hpS : p ≤ S := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      exact hvS
    have hmap : S.map p.mkQ = ⊤ := by
      rw [← top_le_iff, ← IH]
      refine iSup₂_le fun t ht => ?_
      have htΛ : t ∉ Λ := fun h => ht (Finset.mem_insert_of_mem h)
      have htt : t ≠ t0 := fun h => ht (h ▸ Finset.mem_insert_self _ _)
      intro xb hxb
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective p xb
      have h1 : (A + t • B) x ∈ q := by
        have h := LinearMap.mem_ker.mp hxb
        rw [← Submodule.Quotient.mk_eq_zero q]
        simpa [Submodule.mapQ_apply] using h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
      have htt' : t - t0 ≠ 0 := sub_ne_zero.mpr htt
      refine ⟨x - (c / (t - t0)) • v, ?_, ?_⟩
      · refine (le_iSup₂_of_le (f := fun (t : ℂ) (_ : t ∉ Λ) => LinearMap.ker (A + t • B))
          t htΛ le_rfl) ?_
        rw [LinearMap.mem_ker, map_sub, ← hc, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hAv, ← sub_eq_zero]
        have : c • B v - (c / (t - t0)) • (-(t0 • B v) + t • B v) - 0
            = (c - (c / (t - t0)) * (t - t0)) • B v := by
          module
        rw [this, div_mul_cancel₀ _ htt', sub_self, zero_smul]
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, sub_eq_self,
          Submodule.Quotient.mk_eq_zero]
        exact p.smul_mem _ (Submodule.mem_span_singleton_self _)
    have h2 := (Submodule.map_mkQ_eq_top p S).mp hmap
    rwa [sup_eq_right.mpr hpS] at h2

theorem prank_of_noLeft [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {A B : V →ₗ[ℂ] W}
    (h : NoLeft A B) : PRank (finrank ℂ V) A B := by
  classical
  have hspan := span_ker (finrank ℂ V) V W A B rfl h ∅
  set E : Set V := {v | ∃ t : ℂ, A v = t • B v} with hE
  have hE' : Submodule.span ℂ E = ⊤ := by
    rw [← top_le_iff, ← hspan]
    refine iSup₂_le fun t _ => ?_
    intro x hx
    refine Submodule.subset_span ⟨-t, ?_⟩
    have h1 : A x + t • B x = 0 := by simpa using hx
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  obtain ⟨b, hbE, hbspan, hli⟩ := exists_linearIndependent ℂ E
  have hb : ⊤ ≤ Submodule.span ℂ (Set.range (Subtype.val : b → V)) := by
    rw [Subtype.range_coe, hbspan, hE']
  let bs : Basis b ℂ V := Basis.mk hli hb
  have : Fintype b := FiniteDimensional.fintypeBasisIndex bs
  have hcard : finrank ℂ V = Fintype.card b := Module.finrank_eq_card_basis bs
  have ht : ∀ i : b, ∃ t : ℂ, A (bs i) = t • B (bs i) := by
    intro i
    have h1 : bs i = (i : V) := by simp [bs]
    rw [h1]
    exact hbE i.2
  choose t ht using ht
  rw [hcard]
  exact prank_of_basis bs t A B ht

theorem prank_le (k : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B : V →ₗ[ℂ] W), finrank ℂ V + finrank ℂ W = k →
    PRank (finrank ℂ W + finrank ℂ V / 2) A B := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro V W _ _ _ _ _ _ A B hk
    by_cases h0 : ∃ v : V, v ≠ 0 ∧ A v = 0 ∧ B v = 0
    · obtain ⟨v, hv, hAv, hBv⟩ := h0
      set p : Submodule ℂ V := Submodule.span ℂ {v} with hp
      have hpA : p ≤ LinearMap.ker A := by
        rw [hp, Submodule.span_le, Set.singleton_subset_iff]
        exact hAv
      have hpB : p ≤ LinearMap.ker B := by
        rw [hp, Submodule.span_le, Set.singleton_subset_iff]
        exact hBv
      have hfr : finrank ℂ (V ⧸ p) + 1 = finrank ℂ V := by
        have h1 := Submodule.finrank_quotient_add_finrank p
        have h2 : finrank ℂ p = 1 := finrank_span_singleton hv
        omega
      have IH := ih (finrank ℂ (V ⧸ p) + finrank ℂ W) (by omega) (V ⧸ p) W
        (p.liftQ A hpA) (p.liftQ B hpB) rfl
      have h2 := IH.comp_right p.mkQ
      rw [Submodule.liftQ_mkQ, Submodule.liftQ_mkQ] at h2
      exact h2.mono (by omega)
    by_cases h1 : NoLeft A B
    · have h2 := prank_of_noLeft h1
      have hinj : Function.Injective (A.prod B) := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro x hx
        by_contra hx0
        have hx' : (A x, B x) = 0 := by simpa using hx
        exact h0 ⟨x, hx0, congrArg Prod.fst hx', congrArg Prod.snd hx'⟩
      have h3 := LinearMap.finrank_le_finrank_of_injective hinj
      rw [Module.finrank_prod] at h3
      exact h2.mono (by omega)
    · simp only [NoLeft, not_forall] at h1
      obtain ⟨s, t, hst, hns⟩ := h1
      have hr : LinearMap.range (s • A + t • B) < ⊤ :=
        lt_top_iff_ne_top.mpr (fun h => hns (LinearMap.range_eq_top.mp h))
      obtain ⟨φ, hφ, hφr⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hr inferInstance
      have hφ0 : ∀ x, s * φ (A x) + t * φ (B x) = 0 := by
        intro x
        have hmem : φ ((s • A + t • B) x) ∈ (LinearMap.range (s • A + t • B)).map φ :=
          ⟨_, ⟨x, rfl⟩, rfl⟩
        rw [hφr] at hmem
        simpa using hmem
      obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
        by_contra h
        exact hφ (LinearMap.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
      set w : W := (φ w0)⁻¹ • w0 with hw
      have hφw : φ w = 1 := by simp [hw, hw0]
      let K : Submodule ℂ W := LinearMap.ker φ
      let P : W →ₗ[ℂ] K := LinearMap.codRestrict K (LinearMap.id - φ.smulRight w) (by
        intro x
        simp [K, hφw])
      have hP : ∀ x, ((P x : K) : W) = x - φ x • w := fun x => rfl
      have hfr : finrank ℂ K + 1 = finrank ℂ W := by
        have h1 : finrank ℂ (LinearMap.range φ) + finrank ℂ K = finrank ℂ W :=
          LinearMap.finrank_range_add_finrank_ker φ
        have hsurj : Function.Surjective φ := by
          intro c
          exact ⟨c • w, by simp [hφw]⟩
        have h2 : finrank ℂ (LinearMap.range φ) = 1 := by
          rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self]
        omega
      have IH := ih (finrank ℂ V + finrank ℂ K) (by omega) V K (P ∘ₗ A) (P ∘ₗ B) rfl
      have h2 := IH.comp_left K.subtype
      by_cases hs : s = 0
      · have ht : t ≠ 0 := by tauto
        have hφB : ∀ x, φ (B x) = 0 := by
          intro x
          have := hφ0 x
          simpa [hs, ht] using this
        have h3 := h2.add_smulRight 1 0 (φ ∘ₗ A) w
        have eA : K.subtype ∘ₗ P ∘ₗ A + (1 : ℂ) • (φ ∘ₗ A).smulRight w = A := by
          ext x
          simp [hP]
        have eB : K.subtype ∘ₗ P ∘ₗ B + (0 : ℂ) • (φ ∘ₗ A).smulRight w = B := by
          ext x
          simp [hP, hφB]
        rw [eA, eB] at h3
        exact h3.mono (by omega)
      · have hφA : ∀ x, φ (A x) = (-(t / s)) * φ (B x) := by
          intro x
          have := hφ0 x
          field_simp
          linear_combination this
        have h3 := h2.add_smulRight (-(t / s)) 1 (φ ∘ₗ B) w
        have eA : K.subtype ∘ₗ P ∘ₗ A + (-(t / s)) • (φ ∘ₗ B).smulRight w = A := by
          ext x
          simp [hP, hφA, mul_smul]
        have eB : K.subtype ∘ₗ P ∘ₗ B + (1 : ℂ) • (φ ∘ₗ B).smulRight w = B := by
          ext x
          simp [hP]
        rw [eA, eB] at h3
        exact h3.mono (by omega)

end Pencil
section Regular

open Matrix

/-- An invertible sum of rank-one matrices has at least `n` terms. -/
theorem card_ge_of_isUnit {n : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (x y : ι → Fin n → ℂ) (h : IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l))) : n ≤ s.card := by
  have hprod : ∑ l ∈ s, c l • vecMulVec (x l) (y l) =
      (Matrix.of fun (i : Fin n) (l : s) => c l * x l i) *
        (Matrix.of fun (l : s) (j : Fin n) => y l j) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.mul_apply,
      Matrix.of_apply, smul_eq_mul]
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hr : (∑ l ∈ s, c l • vecMulVec (x l) (y l)).rank = n := by
    rw [Matrix.rank_of_isUnit _ h, Fintype.card_fin]
  rw [hprod] at hr
  have hle := (Matrix.rank_mul_le_left (Matrix.of fun (i : Fin n) (l : s) => c l * x l i)
    (Matrix.of fun (l : s) (j : Fin n) => y l j)).trans (Matrix.rank_le_card_width _)
  rw [hr, Fintype.card_coe] at hle
  exact hle

/-- From an invertible sum of more than `n` rank-one matrices one term can be removed. -/
theorem exists_erase {n : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (x y : ι → Fin n → ℂ) (h : IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l)))
    (hcard : n < s.card) :
    ∃ l₀ ∈ s, IsUnit (∑ l ∈ s.erase l₀, c l • vecMulVec (x l) (y l)) := by
  set G := ∑ l ∈ s, c l • vecMulVec (x l) (y l) with hG
  have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det G).mp h
  have htr : (G⁻¹ * G).trace = (n : ℂ) := by
    rw [nonsing_inv_mul _ hGdet, Matrix.trace_one, Fintype.card_fin]
  have htr2 : (G⁻¹ * G).trace = ∑ l ∈ s, c l * ((G⁻¹ *ᵥ x l) ⬝ᵥ y l) := by
    have e : G⁻¹ * G = ∑ l ∈ s, c l • vecMulVec (G⁻¹ *ᵥ x l) (y l) := by
      conv_lhs => rw [hG]
      rw [Matrix.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_smul, mul_vecMulVec]
    rw [e, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]
  by_contra hall
  have h1 : ∀ l ∈ s, c l * ((G⁻¹ *ᵥ x l) ⬝ᵥ y l) = 1 := by
    intro l hl
    by_contra hne
    apply hall
    refine ⟨l, hl, ?_⟩
    rw [Finset.sum_erase_eq_sub hl, ← hG]
    have hfac : G - c l • vecMulVec (x l) (y l) =
        G * (1 + vecMulVec (-(c l) • (G⁻¹ *ᵥ x l)) (y l)) := by
      rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, mul_nonsing_inv _ hGdet, Matrix.one_mulVec, ← smul_vecMulVec,
        neg_smul, sub_eq_add_neg, neg_vecMulVec]
    rw [hfac, isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.vecMulVec_eq Unit,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    refine hGdet.mul (isUnit_iff_ne_zero.mpr ?_)
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
    intro h0
    apply hne
    linear_combination -h0
  have hsum : (n : ℂ) = (s.card : ℂ) := by
    rw [← htr, htr2, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : n = s.card := by exact_mod_cast hsum
  omega

/-- An invertible sum of rank-one matrices contains an invertible subsum with exactly `n`
terms. -/
theorem exists_subsum {n : ℕ} {ι : Type} [DecidableEq ι] (c : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∀ (k : ℕ) (s : Finset ι), s.card = n + k →
      IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l)) →
      ∃ s' ⊆ s, s'.card = n ∧ IsUnit (∑ l ∈ s', c l • vecMulVec (x l) (y l)) := by
  intro k
  induction k with
  | zero => exact fun s hs h => ⟨s, Finset.Subset.refl s, by simpa using hs, h⟩
  | succ k ih =>
    intro s hs h
    obtain ⟨l₀, hl₀, h'⟩ := exists_erase s c x y h (by omega)
    obtain ⟨s', hs', hc, hu⟩ := ih (s.erase l₀) (by rw [Finset.card_erase_of_mem hl₀]; omega) h'
    exact ⟨s', hs'.trans (Finset.erase_subset _ _), hc, hu⟩

/-- A sum of rank-one matrices over a finset of `n` indices, as `P * diagonal * Q`. -/
theorem sum_eq_mul_diag_mul {n : ℕ} {ι : Type} (s : Finset ι) (e : Fin n ≃ s)
    (d : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∑ l ∈ s, d l • vecMulVec (x l) (y l) =
      (Matrix.of fun (i : Fin n) (k : Fin n) => x (e k) i) *
        Matrix.diagonal (fun k => d (e k)) * (Matrix.of fun (k : Fin n) (j : Fin n) => y (e k) j) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp e]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A sum of rank-one matrices over a finset with at most `m` elements, padded by zeros to a
sum over `Fin m`, simultaneously for two families of coefficients. -/
theorem exists_pad {n m : ℕ} {ι : Type} (s : Finset ι) (hs : s.card ≤ m)
    (a b : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∃ (u v : Fin m → Fin n → ℂ) (α β : Fin m → ℂ),
      ∑ l ∈ s, a l • vecMulVec (x l) (y l) = ∑ j, α j • vecMulVec (u j) (v j) ∧
      ∑ l ∈ s, b l • vecMulVec (x l) (y l) = ∑ j, β j • vecMulVec (u j) (v j) := by
  have hcard : Fintype.card s ≤ Fintype.card (Fin m) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    exact hs
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨Function.extend emb (fun l : s => x l) 0, Function.extend emb (fun l : s => y l) 0,
    Function.extend emb (fun l : s => a l) 0, Function.extend emb (fun l : s => b l) 0, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort s]
    refine Fintype.sum_of_injective emb emb.injective _ _ (fun j hj => ?_) (fun l => ?_)
    · rw [Function.extend_apply' _ _ _ (fun h => hj h), Pi.zero_apply, zero_smul]
    · rw [emb.injective.extend_apply, emb.injective.extend_apply, emb.injective.extend_apply]
  · rw [← Finset.sum_coe_sort s]
    refine Fintype.sum_of_injective emb emb.injective _ _ (fun j hj => ?_) (fun l => ?_)
    · rw [Function.extend_apply' _ _ _ (fun h => hj h), Pi.zero_apply, zero_smul]
    · rw [emb.injective.extend_apply, emb.injective.extend_apply, emb.injective.extend_apply]

/-- A pencil of rank at most `r`, in matrix form. -/
theorem mat_of_prank {n r : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : PRank r (Matrix.toLin' A) (Matrix.toLin' B)) :
    ∃ (ι : Type) (_ : Fintype ι) (a b : ι → ℂ) (x y : ι → Fin n → ℂ),
      Fintype.card ι ≤ r ∧ A = ∑ l, a l • vecMulVec (x l) (y l) ∧
        B = ∑ l, b l • vecMulVec (x l) (y l) := by
  obtain ⟨ι, hι, a, b, ψ, w, hc, hA, hB⟩ := h
  refine ⟨ι, hι, a, b, w, fun l j => ψ l (Pi.single j 1), hc, ?_, ?_⟩
  · ext i j
    have h1 := congrFun (LinearMap.congr_fun hA (Pi.single j 1)) i
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    rw [h1]
    exact Finset.sum_congr rfl fun l _ => by ring
  · ext i j
    have h1 := congrFun (LinearMap.congr_fun hB (Pi.single j 1)) i
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    rw [h1]
    exact Finset.sum_congr rfl fun l _ => by ring

/-- The regular case: a pencil of `n × n` matrices containing an invertible matrix is, in
suitable bases, simultaneously diagonal up to `n / 2` rank-one pencils; moreover no diagonal
coefficient pair vanishes. -/
theorem regular_pencil (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∃ s t : ℂ, IsUnit (s • A + t • B)) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin (n / 2) → Fin n → ℂ)
      (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j) ∧
      ∃ s t : ℂ, ∀ k, s * a k + t * b k ≠ 0 := by
  classical
  obtain ⟨s, t, hst⟩ := h
  have h0 := prank_le (n + n) (Fin n → ℂ) (Fin n → ℂ) (Matrix.toLin' A) (Matrix.toLin' B)
    (by simp)
  rw [Module.finrank_fin_fun] at h0
  obtain ⟨ι, _, a, b, x, y, hc, hA, hB⟩ := mat_of_prank A B h0
  have hsum : s • A + t • B = ∑ l ∈ Finset.univ, (s * a l + t * b l) • vecMulVec (x l) (y l) := by
    rw [hA, hB, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul, smul_smul, add_smul]
  rw [hsum] at hst
  have hge : n ≤ (Finset.univ : Finset ι).card := card_ge_of_isUnit _ _ x y hst
  obtain ⟨s', hs', hcard, hu⟩ := exists_subsum (fun l => s * a l + t * b l) x y
    ((Finset.univ : Finset ι).card - n) Finset.univ (by omega) hst
  have e : Fin n ≃ s' := (Finset.equivFinOfCardEq hcard).symm
  rw [sum_eq_mul_diag_mul s' e] at hu
  have hdet := (isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hP : IsUnit (Matrix.of fun (i : Fin n) (k : Fin n) => x (e k) i) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hdet))
  have hQ : IsUnit (Matrix.of fun (k : Fin n) (j : Fin n) => y (e k) j) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
  have hD : IsUnit (Matrix.diagonal fun k => s * a (e k) + t * b (e k)).det :=
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hdet)
  rw [Matrix.det_diagonal] at hD
  have hrest : (Finset.univ \ s').card ≤ n / 2 := by
    rw [Finset.card_sdiff_of_subset hs', hcard]
    rw [Finset.card_univ]
    omega
  obtain ⟨u, v, α, β, hα, hβ⟩ := exists_pad (Finset.univ \ s') hrest a b x y
  refine ⟨_, _, fun k => a (e k), fun k => b (e k), u, v, α, β, hP, hQ, ?_, ?_, s, t,
    fun k => Finset.prod_ne_zero_iff.mp hD.ne_zero k (Finset.mem_univ k)⟩
  · rw [← sum_eq_mul_diag_mul s' e a x y, ← hα, add_comm, Finset.sum_sdiff hs']
    exact hA
  · rw [← sum_eq_mul_diag_mul s' e b x y, ← hβ, add_comm, Finset.sum_sdiff hs']
    exact hB

end Regular

section Abstract

open Matrix

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem PRank.add {r r' : ℕ} {A B A' B' : V →ₗ[ℂ] W} (h : PRank r A B) (h' : PRank r' A' B') :
    PRank (r + r') (A + A') (B + B') := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  obtain ⟨ι', _, a', b', ψ', u', hc', rfl, rfl⟩ := h'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim b b', Sum.elim ψ ψ', Sum.elim u u',
    ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    omega
  · rw [Fintype.sum_sum_type]
    rfl
  · rw [Fintype.sum_sum_type]
    rfl

/-- A pencil of rank at most `r` between quotients lifts to one between the spaces, vanishing
on the submodule that is divided out. -/
theorem PRank.lift {p : Submodule ℂ V} {q : Submodule ℂ W} {r : ℕ}
    {RA RB : (V ⧸ p) →ₗ[ℂ] (W ⧸ q)} (h : PRank r RA RB) :
    ∃ SA SB : V →ₗ[ℂ] W, PRank r SA SB ∧ (∀ v, q.mkQ (SA v) = RA (p.mkQ v)) ∧
      (∀ v, q.mkQ (SB v) = RB (p.mkQ v)) ∧ (∀ v ∈ p, SA v = 0) ∧ (∀ v ∈ p, SB v = 0) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  choose u' hu' using fun i => q.mkQ_surjective (u i)
  refine ⟨∑ i, a i • (ψ i ∘ₗ p.mkQ).smulRight (u' i), ∑ i, b i • (ψ i ∘ₗ p.mkQ).smulRight (u' i),
    ⟨ι, inferInstance, a, b, fun i => ψ i ∘ₗ p.mkQ, u', hc, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, map_sum, map_smul, hu']
  · intro v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, map_sum, map_smul, hu']
  · intro v hv
    have h0 : p.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero p).mpr hv
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, h0, map_zero, zero_smul, smul_zero, Finset.sum_const_zero]
  · intro v hv
    have h0 : p.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero p).mpr hv
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, h0, map_zero, zero_smul, smul_zero, Finset.sum_const_zero]

/-- `DP r A B`: in suitable bases of `V` and `W` (indexed by the same type) the pencil `(A, B)`
is diagonal, up to a pencil of rank at most `r`. -/
def DP (r : ℕ) (A B : V →ₗ[ℂ] W) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (bV : Basis ι ℂ V) (bW : Basis ι ℂ W) (a b : ι → ℂ)
    (RA RB : V →ₗ[ℂ] W), PRank r RA RB ∧
      (∀ i, A (bV i) = a i • bW i + RA (bV i)) ∧ (∀ i, B (bV i) = b i • bW i + RB (bV i))

theorem DP.mono {r r' : ℕ} {A B : V →ₗ[ℂ] W} (h : DP r A B) (hr : r ≤ r') : DP r' A B := by
  obtain ⟨ι, hι, bV, bW, a, b, RA, RB, hR, hA, hB⟩ := h
  exact ⟨ι, hι, bV, bW, a, b, RA, RB, hR.mono hr, hA, hB⟩

/-- From a matrix decomposition `P * diagonal * Q + rank-one terms` in some bases to bases in
which the pencil is diagonal up to the rank-one terms. -/
theorem basis_data_of_matrix {d r : ℕ} (bV0 : Basis (Fin d) ℂ V) (bW0 : Basis (Fin d) ℂ W)
    (A B : V →ₗ[ℂ] W) (P Q : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℂ)
    (u v : Fin r → Fin d → ℂ) (α β : Fin r → ℂ) (hP : IsUnit P) (hQ : IsUnit Q)
    (hA : LinearMap.toMatrix bV0 bW0 A =
      P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j))
    (hB : LinearMap.toMatrix bV0 bW0 B =
      P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)) :
    ∃ (bV : Basis (Fin d) ℂ V) (bW : Basis (Fin d) ℂ W) (RA RB : V →ₗ[ℂ] W), PRank r RA RB ∧
      (∀ i, A (bV i) = a i • bW i + RA (bV i)) ∧ (∀ i, B (bV i) = b i • bW i + RB (bV i)) := by
  classical
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hQi : IsUnit (Q⁻¹).det := Matrix.isUnit_nonsing_inv_det Q hQd
  let ψ : Fin r → V →ₗ[ℂ] ℂ := fun j => bV0.constr ℂ (fun k => v j k)
  let U : Fin r → W := fun j => ∑ i, u j i • bW0 i
  have key : ∀ c : Fin r → ℂ, Matrix.toLin bV0 bW0 (∑ j, c j • Matrix.vecMulVec (u j) (v j)) =
      ∑ j, c j • (ψ j).smulRight (U j) := by
    intro c
    refine bV0.ext fun k => ?_
    rw [Matrix.toLin_self]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, ψ, U,
      Basis.constr_basis, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have diag : ∀ (c : Fin d → ℂ) (i : Fin d),
      Matrix.toLin bV0 bW0 (P * Matrix.diagonal c * Q) (Matrix.toLin bV0 bV0 Q⁻¹ (bV0 i)) =
        c i • Matrix.toLin bW0 bW0 P (bW0 i) := by
    intro c i
    rw [← Matrix.toLin_mul_apply, Matrix.mul_nonsing_inv_cancel_right _ _ hQd, Matrix.toLin_self,
      Matrix.toLin_self, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, smul_smul, mul_comm]
  refine ⟨bV0.map (Matrix.toLinearEquiv bV0 Q⁻¹ hQi), bW0.map (Matrix.toLinearEquiv bW0 P hPd),
    Matrix.toLin bV0 bW0 (∑ j, α j • Matrix.vecMulVec (u j) (v j)),
    Matrix.toLin bV0 bW0 (∑ j, β j • Matrix.vecMulVec (u j) (v j)),
    ⟨Fin r, inferInstance, α, β, ψ, U, by simp, key α, key β⟩, ?_, ?_⟩
  · intro i
    have h1 : A = Matrix.toLin bV0 bW0 (P * Matrix.diagonal a * Q) +
        Matrix.toLin bV0 bW0 (∑ j, α j • Matrix.vecMulVec (u j) (v j)) := by
      rw [← map_add, ← hA, Matrix.toLin_toMatrix]
    conv_lhs => rw [h1]
    rw [LinearMap.add_apply, Basis.map_apply, Basis.map_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLinearEquiv_apply, diag a i]
  · intro i
    have h1 : B = Matrix.toLin bV0 bW0 (P * Matrix.diagonal b * Q) +
        Matrix.toLin bV0 bW0 (∑ j, β j • Matrix.vecMulVec (u j) (v j)) := by
      rw [← map_add, ← hB, Matrix.toLin_toMatrix]
    conv_lhs => rw [h1]
    rw [LinearMap.add_apply, Basis.map_apply, Basis.map_apply, Matrix.toLinearEquiv_apply,
      Matrix.toLinearEquiv_apply, diag b i]

/-- A statement about all pencils of `d × d` matrices transfers to pencils between spaces of
dimension `d`. -/
theorem DP_of_matrices {d : ℕ} [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hV : finrank ℂ V = d) (hW : finrank ℂ W = d) (A B : V →ₗ[ℂ] W)
    (h : ∀ A' B' : Matrix (Fin d) (Fin d) ℂ,
      ∃ (P Q : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℂ) (u v : Fin (d / 2) → Fin d → ℂ)
        (α β : Fin (d / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
        A' = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
        B' = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)) :
    DP (d / 2) A B := by
  classical
  let bV0 : Basis (Fin d) ℂ V := Module.finBasisOfFinrankEq ℂ V hV
  let bW0 : Basis (Fin d) ℂ W := Module.finBasisOfFinrankEq ℂ W hW
  obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hA, hB⟩ :=
    h (LinearMap.toMatrix bV0 bW0 A) (LinearMap.toMatrix bV0 bW0 B)
  obtain ⟨bV, bW, RA, RB, hR, h1, h2⟩ :=
    basis_data_of_matrix bV0 bW0 A B P Q a b u v α β hP hQ hA hB
  exact ⟨Fin d, inferInstance, bV, bW, a, b, RA, RB, hR, h1, h2⟩

/-- The regular case for a pencil between spaces of the same dimension `d`. -/
theorem regular_abs {d : ℕ} [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hV : finrank ℂ V = d) (hW : finrank ℂ W = d) (A B : V →ₗ[ℂ] W) (t : ℂ)
    (hinj : Function.Injective (A + t • B)) :
    ∃ (bV : Basis (Fin d) ℂ V) (bW : Basis (Fin d) ℂ W) (a b : Fin d → ℂ) (RA RB : V →ₗ[ℂ] W),
      PRank (d / 2) RA RB ∧ (∀ i, A (bV i) = a i • bW i + RA (bV i)) ∧
      (∀ i, B (bV i) = b i • bW i + RB (bV i)) ∧ ∃ s₀ t₀ : ℂ, ∀ k, s₀ * a k + t₀ * b k ≠ 0 := by
  classical
  let bV0 : Basis (Fin d) ℂ V := Module.finBasisOfFinrankEq ℂ V hV
  let bW0 : Basis (Fin d) ℂ W := Module.finBasisOfFinrankEq ℂ W hW
  have hbij : Function.Bijective (A + t • B) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hV.trans hW.symm)).mp hinj⟩
  have hunit := (LinearEquiv.ofBijective (A + t • B) hbij).isUnit_det bV0 bW0
  have hreg : ∃ s t : ℂ, IsUnit (s • LinearMap.toMatrix bV0 bW0 A + t • LinearMap.toMatrix bV0 bW0 B) := by
    refine ⟨1, t, (Matrix.isUnit_iff_isUnit_det _).mpr ?_⟩
    have e : (1 : ℂ) • LinearMap.toMatrix bV0 bW0 A + t • LinearMap.toMatrix bV0 bW0 B =
        LinearMap.toMatrix bV0 bW0 ((LinearEquiv.ofBijective (A + t • B) hbij : V ≃ₗ[ℂ] W) : V →ₗ[ℂ] W) := by
      rw [one_smul, ← map_smul, ← map_add]
      rfl
    rw [e]
    exact hunit
  obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hA, hB, hne⟩ := regular_pencil d _ _ hreg
  obtain ⟨bV, bW, RA, RB, hR, h1, h2⟩ :=
    basis_data_of_matrix bV0 bW0 A B P Q a b u v α β hP hQ hA hB
  exact ⟨bV, bW, a, b, RA, RB, hR, h1, h2, hne⟩

/-- From bases in which the pencil is diagonal up to rank `r` back to matrices. -/
theorem matrix_of_DP {n r : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : DP r (Matrix.toLin' A) (Matrix.toLin' B)) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin r → Fin n → ℂ)
      (α β : Fin r → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j) := by
  classical
  obtain ⟨ι, _, bV, bW, a, b, RA, RB, hR, hA, hB⟩ := h
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bV, Module.finrank_fin_fun]
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => bW (e k) i
  let S : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => bV (e k) i
  have hPc : P.col = bW ∘ e := by
    ext k i
    rfl
  have hSc : S.col = bV ∘ e := by
    ext k i
    rfl
  have hPu : IsUnit P := (Matrix.linearIndependent_cols_iff_isUnit (K := ℂ)).mp
    (by rw [hPc]; exact bW.linearIndependent.comp e e.injective)
  have hSu : IsUnit S := (Matrix.linearIndependent_cols_iff_isUnit (K := ℂ)).mp
    (by rw [hSc]; exact bV.linearIndependent.comp e e.injective)
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  have hRm : PRank r (Matrix.toLin' (LinearMap.toMatrix' RA))
      (Matrix.toLin' (LinearMap.toMatrix' RB)) := by
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    exact hR
  obtain ⟨κ, _, α', β', x, y, hκ, hRA, hRB⟩ := mat_of_prank _ _ hRm
  have hκ' : (Finset.univ : Finset κ).card ≤ r := by
    rw [Finset.card_univ]
    exact hκ
  obtain ⟨u, v, α, β, hα, hβ⟩ := exists_pad (m := r) (Finset.univ : Finset κ) hκ' α' β' x y
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (R : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (c : ι → ℂ),
      (∀ i, Matrix.toLin' M (bV i) = c i • bW i + R (bV i)) →
      M = P * Matrix.diagonal (fun k => c (e k)) * S⁻¹ + LinearMap.toMatrix' R := by
    intro M R c hM
    have h1 : (M - LinearMap.toMatrix' R) * S = P * Matrix.diagonal (fun k => c (e k)) := by
      ext i k
      have h2 := congrFun (hM (e k)) i
      have h3 : R (bV (e k)) = LinearMap.toMatrix' R *ᵥ bV (e k) := by
        rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
      rw [Matrix.toLin'_apply, h3] at h2
      have h4 : ((M - LinearMap.toMatrix' R) * S) i k =
          ((M - LinearMap.toMatrix' R) *ᵥ bV (e k)) i := rfl
      rw [h4, Matrix.sub_mulVec, Pi.sub_apply, h2, Matrix.mul_diagonal]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right, P,
        Matrix.of_apply, mul_comm]
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hSd, sub_add_cancel]
  refine ⟨P, S⁻¹, fun k => a (e k), fun k => b (e k), u, v, α, β, hPu,
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det S hSd), ?_, ?_⟩
  · rw [← hα, ← hRA]
    exact key A RA a hA
  · rw [← hβ, ← hRB]
    exact key B RB b hB

theorem finrank_quot_span_singleton [FiniteDimensional ℂ V] {v0 : V} (hv0 : v0 ≠ 0) :
    finrank ℂ (V ⧸ Submodule.span ℂ {v0}) + 1 = finrank ℂ V := by
  have h1 := (Submodule.span ℂ {v0}).finrank_quotient_add_finrank
  have h2 : finrank ℂ (Submodule.span ℂ {v0}) = 1 := finrank_span_singleton hv0
  omega

theorem finrank_ker_functional [FiniteDimensional ℂ W] {φ : W →ₗ[ℂ] ℂ} (hφ : φ ≠ 0) :
    finrank ℂ (LinearMap.ker φ) + 1 = finrank ℂ W := by
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have hsurj : Function.Surjective φ := fun c => ⟨(c / φ w0) • w0, by simp [hw0]⟩
  have h2 : finrank ℂ (LinearMap.range φ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self]
  omega

/-- A common kernel vector together with a common left kernel functional: the pencil is a
smaller pencil plus a zero block. -/
theorem DP_of_zero_block [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (A B : V →ₗ[ℂ] W)
    (v0 : V) (hv0 : v0 ≠ 0) (hA0 : A v0 = 0) (hB0 : B v0 = 0) (φ : W →ₗ[ℂ] ℂ) (hφ : φ ≠ 0)
    (hφA : ∀ x, φ (A x) = 0) (hφB : ∀ x, φ (B x) = 0) (r : ℕ)
    (ih : ∀ A' B' : (V ⧸ Submodule.span ℂ {v0}) →ₗ[ℂ] LinearMap.ker φ, DP r A' B') :
    DP r A B := by
  classical
  have hpA : Submodule.span ℂ {v0} ≤ LinearMap.ker
      (A.codRestrict (LinearMap.ker φ) (fun x => LinearMap.mem_ker.mpr (hφA x))) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr (Subtype.ext hA0)
  have hpB : Submodule.span ℂ {v0} ≤ LinearMap.ker
      (B.codRestrict (LinearMap.ker φ) (fun x => LinearMap.mem_ker.mpr (hφB x))) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr (Subtype.ext hB0)
  obtain ⟨ι, _, bV', bW', a, b, RA', RB', hR, hA', hB'⟩ :=
    ih ((Submodule.span ℂ {v0}).liftQ _ hpA) ((Submodule.span ℂ {v0}).liftQ _ hpB)
  choose v' hv' using fun i => (Submodule.span ℂ {v0}).mkQ_surjective (bV' i)
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
  have hliV0 : LinearIndependent ℂ (Sum.elim (fun _ : Unit => v0) v') := by
    have h1 : LinearIndependent ℂ (fun _ : Unit =>
        (⟨v0, Submodule.mem_span_singleton_self v0⟩ : Submodule.span ℂ {v0})) := by
      rw [linearIndependent_unique_iff]
      intro h
      exact hv0 (congrArg Subtype.val h)
    have h2 : LinearIndependent ℂ
        (Submodule.Quotient.mk (p := Submodule.span ℂ {v0}) ∘ v') := by
      have h3 : Submodule.Quotient.mk (p := Submodule.span ℂ {v0}) ∘ v' = bV' :=
        funext fun i => hv' i
      rw [h3]
      exact bV'.linearIndependent
    exact LinearIndependent.sumElim_of_quotient h1 v' h2
  have hliV : LinearIndependent ℂ (Sum.elim v' (fun _ : Unit => v0)) := by
    have h := hliV0.comp (Equiv.sumComm ι Unit) (Equiv.sumComm ι Unit).injective
    have e : (Sum.elim (fun _ : Unit => v0) v' ∘ ⇑(Equiv.sumComm ι Unit)) =
        Sum.elim v' (fun _ : Unit => v0) := by
      funext x
      cases x <;> rfl
    rw [e] at h
    exact h
  have hliW : LinearIndependent ℂ (Sum.elim (fun i => (bW' i : W)) (fun _ : Unit => w0)) := by
    have h2 : LinearIndependent ℂ
        (Submodule.Quotient.mk (p := LinearMap.ker φ) ∘ (fun _ : Unit => w0)) := by
      rw [linearIndependent_unique_iff]
      intro h
      exact hw0 (LinearMap.mem_ker.mp ((Submodule.Quotient.mk_eq_zero _).mp h))
    exact LinearIndependent.sumElim_of_quotient bW'.linearIndependent _ h2
  have hcV : Fintype.card (ι ⊕ Unit) = finrank ℂ V := by
    have h1 := finrank_quot_span_singleton hv0
    have h3 := Module.finrank_eq_card_basis bV'
    rw [Fintype.card_sum, Fintype.card_unit]
    omega
  have hcW : Fintype.card (ι ⊕ Unit) = finrank ℂ W := by
    have h1 := finrank_ker_functional hφ
    have h3 := Module.finrank_eq_card_basis bW'
    rw [Fintype.card_sum, Fintype.card_unit]
    omega
  have h0 : (Submodule.span ℂ {v0}).mkQ v0 = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self v0)
  refine ⟨ι ⊕ Unit, inferInstance, basisOfLinearIndependentOfCardEqFinrank hliV hcV,
    basisOfLinearIndependentOfCardEqFinrank hliW hcW, Sum.elim a (fun _ => 0),
    Sum.elim b (fun _ => 0), (LinearMap.ker φ).subtype ∘ₗ RA' ∘ₗ (Submodule.span ℂ {v0}).mkQ,
    (LinearMap.ker φ).subtype ∘ₗ RB' ∘ₗ (Submodule.span ℂ {v0}).mkQ,
    (hR.comp_right _).comp_left _, ?_, ?_⟩
  · rintro (i | u)
    · have h2 := congrArg Subtype.val (hA' i)
      rw [← hv' i] at h2
      simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inl,
        LinearMap.comp_apply, Submodule.subtype_apply]
      exact h2
    · simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inr,
        LinearMap.comp_apply, h0, map_zero, zero_smul, add_zero, hA0]
  · rintro (i | u)
    · have h2 := congrArg Subtype.val (hB' i)
      rw [← hv' i] at h2
      simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inl,
        LinearMap.comp_apply, Submodule.subtype_apply]
      exact h2
    · simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Sum.elim_inr,
        LinearMap.comp_apply, h0, map_zero, zero_smul, add_zero, hB0]

/-- Gluing two diagonal blocks of a block triangular pencil whose coefficient pairs are pairwise
independent across the blocks: a Cramer solve for each pair of indices. -/
theorem glue {I J : Type} [Fintype I] [Fintype J] (A B : V →ₗ[ℂ] W) (x : I → V) (wh : I → W)
    (a b : I → ℂ) (v' : J → V) (w' : J → W) (a' b' : J → ℂ)
    (hA : ∀ i, A (x i) = a i • wh i) (hB : ∀ i, B (x i) = b i • wh i)
    (hA' : ∀ j, A (v' j) - a' j • w' j ∈ Submodule.span ℂ (Set.range wh))
    (hB' : ∀ j, B (v' j) - b' j • w' j ∈ Submodule.span ℂ (Set.range wh))
    (hne : ∀ i j, a i * b' j - a' j * b i ≠ 0) :
    ∃ Y X : J → I → ℂ, ∀ j,
      A (v' j - ∑ i, Y j i • x i) = a' j • (w' j + ∑ i, X j i • wh i) ∧
      B (v' j - ∑ i, Y j i • x i) = b' j • (w' j + ∑ i, X j i • wh i) := by
  choose cA hcA using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hA' j)
  choose cB hcB using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hB' j)
  refine ⟨fun j i => (cA j i * b' j - a' j * cB j i) / (a i * b' j - a' j * b i),
    fun j i => (a i * cB j i - b i * cA j i) / (a i * b' j - a' j * b i), fun j => ⟨?_, ?_⟩⟩
  · have e1 : A (v' j) = a' j • w' j + ∑ i, cA j i • wh i := by
      rw [hcA j]
      abel
    rw [map_sub, map_sum, e1, smul_add, Finset.smul_sum, add_sub_assoc]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hA, smul_smul, smul_smul, ← sub_smul]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc', sub_eq_iff_eq_add, ← add_div, eq_div_iff (hne i j)]
    ring
  · have e1 : B (v' j) = b' j • w' j + ∑ i, cB j i • wh i := by
      rw [hcB j]
      abel
    rw [map_sub, map_sum, e1, smul_add, Finset.smul_sum, add_sub_assoc]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hB, smul_smul, smul_smul, ← sub_smul]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc', sub_eq_iff_eq_add, ← add_div, eq_div_iff (hne i j)]
    ring

/-- Span of the eigenvectors of the pencil whose parameter avoids the finite set `F`. -/
def ES (A B : V →ₗ[ℂ] W) (F : Finset ℂ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ t : ℂ, t ∉ F ∧ A x + t • B x = 0}

theorem ES_anti (A B : V →ₗ[ℂ] W) {F F' : Finset ℂ} (h : F ⊆ F') : ES A B F' ≤ ES A B F :=
  Submodule.span_mono fun _ ⟨t, ht, hx⟩ => ⟨t, fun h' => ht (h h'), hx⟩

/-- For `F` large enough the span of the eigenvectors with parameter outside `F` is constant. -/
theorem exists_stable [FiniteDimensional ℂ V] (A B : V →ₗ[ℂ] W) :
    ∃ F0 : Finset ℂ, ∀ F : Finset ℂ, F0 ⊆ F → ES A B F = ES A B F0 := by
  classical
  have hne : ∃ d, ∃ F : Finset ℂ, finrank ℂ (ES A B F) = d := ⟨_, ∅, rfl⟩
  obtain ⟨F0, hF0⟩ := Nat.find_spec hne
  refine ⟨F0, fun F hF => ?_⟩
  refine Submodule.eq_of_le_of_finrank_le (ES_anti A B hF) ?_
  rw [hF0]
  exact Nat.find_min' hne ⟨F, rfl⟩

theorem exists_eigen_family [FiniteDimensional ℂ V] (A B : V →ₗ[ℂ] W) (F : Finset ℂ) :
    ∃ (I : Type) (_ : Fintype I) (x : I → V) (t : I → ℂ), LinearIndependent ℂ x ∧
      Submodule.span ℂ (Set.range x) = ES A B F ∧
      ∀ i, t i ∉ F ∧ A (x i) + t i • B (x i) = 0 := by
  classical
  obtain ⟨b, hbS, hbspan, hli⟩ :=
    exists_linearIndependent ℂ {x : V | ∃ t : ℂ, t ∉ F ∧ A x + t • B x = 0}
  have hfin : Finite b := hli.finite
  have hft : Fintype b := Fintype.ofFinite b
  choose t ht using fun i : b => hbS i.2
  exact ⟨b, hft, Subtype.val, t, hli, by rw [Subtype.range_coe]; exact hbspan, ht⟩

theorem span_range_smul {I : Type} (c : I → ℂ) (hc : ∀ i, c i ≠ 0) (w : I → W) :
    Submodule.span ℂ (Set.range fun i => c i • w i) = Submodule.span ℂ (Set.range w) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h : w i = (c i)⁻¹ • (c i • w i) := by
      rw [smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Without a common kernel vector, the images under `B` of independent eigenvectors with
nonzero parameters span at least half of their number of dimensions. -/
theorem card_le_two_mul [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (A B : V →ₗ[ℂ] W)
    (hk : ∀ v, A v = 0 → B v = 0 → v = 0) {I : Type} [Fintype I] (x : I → V) (t : I → ℂ)
    (hli : LinearIndependent ℂ x) (ht : ∀ i, t i ≠ 0)
    (hx : ∀ i, A (x i) + t i • B (x i) = 0) :
    Fintype.card I ≤ 2 * finrank ℂ (Submodule.span ℂ (Set.range fun i => B (x i))) := by
  classical
  have hrB : LinearMap.range (Fintype.linearCombination ℂ (fun i => B (x i))) =
      Submodule.span ℂ (Set.range fun i => B (x i)) := Fintype.range_linearCombination ..
  have hrA : LinearMap.range (Fintype.linearCombination ℂ (fun i => A (x i))) =
      Submodule.span ℂ (Set.range fun i => B (x i)) := by
    rw [Fintype.range_linearCombination]
    have h : (fun i => A (x i)) = fun i => (-(t i)) • B (x i) := funext fun i => by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (hx i)
    rw [h]
    exact span_range_smul _ (fun i => neg_ne_zero.mpr (ht i)) _
  have hdisj : LinearMap.ker (Fintype.linearCombination ℂ (fun i => A (x i))) ⊓
      LinearMap.ker (Fintype.linearCombination ℂ (fun i => B (x i))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro c hc
    obtain ⟨hcA, hcB⟩ := Submodule.mem_inf.mp hc
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hcA hcB
    have h1 : A (∑ i, c i • x i) = 0 := by
      rw [map_sum, ← hcA]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h2 : B (∑ i, c i • x i) = 0 := by
      rw [map_sum, ← hcB]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    exact funext fun i => Fintype.linearIndependent_iff.mp hli c (hk _ h1 h2) i
  have hA := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℂ (fun i => A (x i)))
  have hB := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℂ (fun i => B (x i)))
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (Fintype.linearCombination ℂ (fun i => A (x i))))
    (LinearMap.ker (Fintype.linearCombination ℂ (fun i => B (x i))))
  rw [hdisj, finrank_bot, add_zero] at hs
  have hle := Submodule.finrank_le
    (LinearMap.ker (Fintype.linearCombination ℂ (fun i => A (x i))) ⊔
      LinearMap.ker (Fintype.linearCombination ℂ (fun i => B (x i))))
  rw [Module.finrank_fintype_fun_eq_card] at hA hB hle
  rw [hrA] at hA
  rw [hrB] at hB
  omega

/-- The main case: a pencil between spaces of the same dimension without a common kernel vector
is diagonal up to rank at most half the dimension. -/
theorem DP_of_no_kernel [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (A B : V →ₗ[ℂ] W)
    (hdim : finrank ℂ V = finrank ℂ W) (hk : ∀ v, A v = 0 → B v = 0 → v = 0) :
    DP (finrank ℂ V / 2) A B := by
  classical
  obtain ⟨F0, hF0⟩ := exists_stable A B
  obtain ⟨V1, hV1⟩ : ∃ V1 : Submodule ℂ V, V1 = ES A B F0 := ⟨_, rfl⟩
  obtain ⟨W1, hW1⟩ : ∃ W1 : Submodule ℂ W, W1 = V1.map B := ⟨_, rfl⟩
  -- a first family of eigenvectors, used to choose the parameter `ts`
  obtain ⟨I0, _, x0, t0, -, hsp0, hx0⟩ := exists_eigen_family A B F0
  rw [← hV1] at hsp0
  obtain ⟨ts, hts⟩ := Infinite.exists_notMem_finset (F0 ∪ Finset.univ.image t0)
  have hts0 : ts ∉ F0 := fun h => hts (Finset.mem_union_left _ h)
  have hts1 : ∀ i, ts ≠ t0 i := fun i h =>
    hts (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩))
  obtain ⟨G, hG⟩ : ∃ G : V →ₗ[ℂ] W, G = A + ts • B := ⟨_, rfl⟩
  have hGx : ∀ x, G x = A x + ts • B x := fun x => by
    rw [hG]
    rfl
  have hkerG : LinearMap.ker G ≤ V1 := by
    intro x hx
    rw [hV1]
    exact Submodule.subset_span ⟨ts, hts0, by rw [← hGx]; exact LinearMap.mem_ker.mp hx⟩
  have hGV1 : V1.map G = W1 := by
    rw [hW1, ← hsp0, Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
    have h : (G ∘ x0) = fun i => (ts - t0 i) • (B ∘ x0) i := funext fun i => by
      have h1 := (hx0 i).2
      rw [Function.comp_apply, Function.comp_apply, hGx, sub_smul,
        eq_neg_of_add_eq_zero_left h1]
      abel
    rw [h]
    exact span_range_smul _ (fun i => sub_ne_zero.mpr (hts1 i)) _
  have hAV1 : ∀ x ∈ V1, A x ∈ W1 := by
    have h : V1 ≤ W1.comap A := by
      rw [hV1]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨t, ht, hx⟩
      have hxV : x ∈ V1 := by
        rw [hV1]
        exact Submodule.subset_span ⟨t, ht, hx⟩
      show A x ∈ W1
      rw [eq_neg_of_add_eq_zero_left hx, ← neg_smul, hW1]
      exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hxV)
    exact fun x hx => h hx
  -- the complement `W3` of the range of `G` and the enlarged target `W1'`
  obtain ⟨W3, hW3⟩ := Submodule.exists_isCompl (LinearMap.range G)
  obtain ⟨W1', hW1'⟩ : ∃ W1' : Submodule ℂ W, W1' = W1 ⊔ W3 := ⟨_, rfl⟩
  have hW1le : W1 ≤ W1' := by
    rw [hW1']
    exact le_sup_left
  have hW3le : W3 ≤ W1' := by
    rw [hW1']
    exact le_sup_right
  have hAq : V1 ≤ W1'.comap A := fun x hx => hW1le (hAV1 x hx)
  have hBq : V1 ≤ W1'.comap B := fun x hx =>
    hW1le (by rw [hW1]; exact Submodule.mem_map_of_mem hx)
  have hGinv : ∀ x, G x ∈ W1' → x ∈ V1 := by
    intro x hx
    rw [hW1', Submodule.mem_sup] at hx
    obtain ⟨w1, hw1, w3, hw3, hsum⟩ := hx
    rw [← hGV1] at hw1
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw1
    have h4 : G (x - y) = w3 := by
      rw [map_sub, ← hsum]
      abel
    have h3 : w3 ∈ LinearMap.range G ⊓ W3 := Submodule.mem_inf.mpr ⟨⟨x - y, h4⟩, hw3⟩
    rw [hW3.inf_eq_bot, Submodule.mem_bot] at h3
    rw [h3] at h4
    have h5 := hkerG (LinearMap.mem_ker.mpr h4)
    have h6 : x = (x - y) + y := by abel
    rw [h6]
    exact V1.add_mem h5 hy
  -- the quotient pencil is regular
  obtain ⟨Aq, hAqdef⟩ : ∃ Aq : (V ⧸ V1) →ₗ[ℂ] (W ⧸ W1'), Aq = V1.mapQ W1' A hAq := ⟨_, rfl⟩
  obtain ⟨Bq, hBqdef⟩ : ∃ Bq : (V ⧸ V1) →ₗ[ℂ] (W ⧸ W1'), Bq = V1.mapQ W1' B hBq := ⟨_, rfl⟩
  have hAqx : ∀ x, Aq (V1.mkQ x) = W1'.mkQ (A x) := fun x => by
    rw [hAqdef]
    rfl
  have hBqx : ∀ x, Bq (V1.mkQ x) = W1'.mkQ (B x) := fun x => by
    rw [hBqdef]
    rfl
  have hGq : ∀ x, (Aq + ts • Bq) (V1.mkQ x) = W1'.mkQ (G x) := fun x => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, hAqx, hBqx, hGx, map_add, map_smul]
  have hinj : Function.Injective (Aq + ts • Bq) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro xq hxq
    obtain ⟨x, rfl⟩ := V1.mkQ_surjective xq
    rw [LinearMap.mem_ker, hGq] at hxq
    exact (Submodule.Quotient.mk_eq_zero V1).mpr
      (hGinv x ((Submodule.Quotient.mk_eq_zero W1').mp hxq))
  have hsurj : Function.Surjective (Aq + ts • Bq) := by
    intro wq
    obtain ⟨w, rfl⟩ := W1'.mkQ_surjective wq
    have hw : w ∈ LinearMap.range G ⊔ W3 := by
      rw [hW3.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨g, hg, w3, hw3, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hg
    have h0 : W1'.mkQ w3 = 0 := (Submodule.Quotient.mk_eq_zero W1').mpr (hW3le hw3)
    refine ⟨V1.mkQ x, ?_⟩
    rw [hGq, map_add, h0, add_zero]
  have hdq : finrank ℂ (V ⧸ V1) = finrank ℂ (W ⧸ W1') :=
    (LinearEquiv.ofBijective (Aq + ts • Bq) ⟨hinj, hsurj⟩).finrank_eq
  have hqV := V1.finrank_quotient_add_finrank
  have hqW := W1'.finrank_quotient_add_finrank
  have hW1'dim : finrank ℂ W1' = finrank ℂ V1 := by omega
  have hW1W3 : finrank ℂ W1' = finrank ℂ W1 + finrank ℂ W3 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W1 W3
    have h2 : W1 ⊓ W3 = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      obtain ⟨hw1, hw3⟩ := Submodule.mem_inf.mp hw
      have h3 : w ∈ LinearMap.range G ⊓ W3 := by
        refine Submodule.mem_inf.mpr ⟨?_, hw3⟩
        rw [← hGV1] at hw1
        exact LinearMap.map_le_range hw1
      rw [hW3.inf_eq_bot] at h3
      exact (Submodule.mem_bot ℂ).mp h3
    rw [h2, finrank_bot, add_zero, ← hW1'] at h1
    exact h1
  obtain ⟨bVq, bWq, a', b', RAq, RBq, hRq, hAq', hBq', s₀, t₀, hne⟩ :=
    regular_abs (d := finrank ℂ (V ⧸ V1)) rfl hdq.symm Aq Bq ts hinj
  obtain ⟨R2A, R2B, hR2, hR2A, hR2B, hR2A0, hR2B0⟩ := hRq.lift
  choose v' hv' using fun j => V1.mkQ_surjective (bVq j)
  choose w' hw' using fun j => W1'.mkQ_surjective (bWq j)
  -- the finite set of parameters to avoid
  obtain ⟨F, hF⟩ : ∃ F : Finset ℂ,
      F = F0 ∪ ({0} ∪ Finset.univ.image fun j => -(a' j) / b' j) := ⟨_, rfl⟩
  have hF0F : F0 ⊆ F := by
    rw [hF]
    exact Finset.subset_union_left
  have hFz : ∀ t, t ∉ F → t ≠ 0 := by
    intro t ht h
    apply ht
    rw [hF, h]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_singleton_self 0))
  have hFne : ∀ t, t ∉ F → ∀ j, a' j + t * b' j ≠ 0 := by
    intro t ht j h0
    by_cases hb : b' j = 0
    · have h1 := hne j
      rw [hb, mul_zero, add_zero] at h1 h0
      rw [h0, mul_zero] at h1
      exact h1 rfl
    · apply ht
      rw [hF]
      refine Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩))
      rw [div_eq_iff hb]
      linear_combination -h0
  -- the eigenvectors spanning `V1`, with parameters outside `F`
  obtain ⟨I, _, x, t, hli, hsp, hx⟩ := exists_eigen_family A B F
  rw [hF0 F hF0F, ← hV1] at hsp
  obtain ⟨K, sel, hsel, hselsp, hselli⟩ := exists_linearIndependent' ℂ (fun i => B (x i))
  have hfK : Fintype K := Fintype.ofInjective sel hsel
  obtain ⟨C, hfC, σ, hσl⟩ : ∃ (C : Type) (_ : Fintype C) (σ : K ⊕ C ≃ I),
      ∀ k, σ (Sum.inl k) = sel k :=
    ⟨↥(Set.range sel)ᶜ, Fintype.ofFinite _,
      (Equiv.sumCongr (Equiv.ofInjective sel hsel) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range sel)), fun k => by simp⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : K ⊕ C → V, xs = x ∘ σ := ⟨_, rfl⟩
  obtain ⟨tt, htt⟩ : ∃ tt : K ⊕ C → ℂ, tt = t ∘ σ := ⟨_, rfl⟩
  have hxsli : LinearIndependent ℂ xs := by
    rw [hxs]
    exact hli.comp σ σ.injective
  have hxsV1 : ∀ k, xs k ∈ V1 := fun k => by
    rw [hxs, ← hsp]
    exact Submodule.subset_span ⟨σ k, rfl⟩
  have hxse : ∀ k, A (xs k) = (-(tt k)) • B (xs k) := fun k => by
    rw [hxs, htt, neg_smul]
    exact eq_neg_of_add_eq_zero_left (hx (σ k)).2
  have httF : ∀ k, tt k ∉ F := fun k => by
    rw [htt]
    exact (hx (σ k)).1
  have hcardI : Fintype.card I = finrank ℂ V1 := by
    rw [← hsp, finrank_span_eq_card hli]
  have hcardKC : Fintype.card K + Fintype.card C = finrank ℂ V1 := by
    rw [← hcardI, ← Fintype.card_sum]
    exact Fintype.card_congr σ
  have hW1sp : Submodule.span ℂ (Set.range fun i => B (x i)) = W1 := by
    have h : (fun i => B (x i)) = ⇑B ∘ x := rfl
    rw [h, hW1, ← hsp, Submodule.map_span, Set.range_comp]
  have hW1K : finrank ℂ W1 = Fintype.card K := by
    rw [← hW1sp, ← hselsp, finrank_span_eq_card hselli]
  have h2 := card_le_two_mul A B hk x t hli (fun i => hFz _ (hx i).1) (fun i => (hx i).2)
  rw [hW1sp, hW1K, hcardI, ← hcardKC] at h2
  have hW3C : finrank ℂ W3 = Fintype.card C := by omega
  obtain ⟨e, hesp⟩ : ∃ e : C → W, Submodule.span ℂ (Set.range e) = W3 := by
    refine ⟨fun c => (((Module.finBasisOfFinrankEq ℂ W3 hW3C).reindex
      (Fintype.equivFin C).symm) c : W), ?_⟩
    have h : (fun c => (((Module.finBasisOfFinrankEq ℂ W3 hW3C).reindex
        (Fintype.equivFin C).symm) c : W)) = ⇑W3.subtype ∘
          ⇑((Module.finBasisOfFinrankEq ℂ W3 hW3C).reindex (Fintype.equivFin C).symm) := rfl
    rw [h, Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_subtype_top]
  -- the basis `wh` of `W1'`: images of eigenvectors where possible, else the vectors `e`
  obtain ⟨wh, hwh⟩ : ∃ wh : K ⊕ C → W, wh = Sum.elim (fun k => B (xs (Sum.inl k))) e :=
    ⟨_, rfl⟩
  have hwhl : ∀ k, wh (Sum.inl k) = B (xs (Sum.inl k)) := fun k => by
    rw [hwh]
    rfl
  have hwhr : ∀ c, wh (Sum.inr c) = e c := fun c => by
    rw [hwh]
    rfl
  have hwhsp : Submodule.span ℂ (Set.range wh) = W1' := by
    have h : (fun k => B (xs (Sum.inl k))) = (fun i => B (x i)) ∘ sel := funext fun k => by
      rw [hxs]
      exact congrArg (fun i => B (x i)) (hσl k)
    rw [hwh, Set.Sum.elim_range, Submodule.span_union, hesp, hW1', h, hselsp, hW1sp]
  have hwhmem : ∀ k, wh k ∈ W1' := fun k => by
    rw [← hwhsp]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hwhli : LinearIndependent ℂ wh := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (K ⊕ C) = finrank ℂ (Submodule.span ℂ (Set.range wh))
    rw [hwhsp, hW1'dim, ← hcardKC, Fintype.card_sum]
  -- a first basis of `V`, for the coordinate functionals of the eigenvectors
  have hmkv' : (Submodule.Quotient.mk (p := V1) ∘ v') = bVq := funext fun j => hv' j
  have hxsS : LinearIndependent ℂ (fun k => (⟨xs k, hxsV1 k⟩ : V1)) :=
    LinearIndependent.of_comp V1.subtype hxsli
  have hwhS : LinearIndependent ℂ (fun k => (⟨wh k, hwhmem k⟩ : W1')) :=
    LinearIndependent.of_comp W1'.subtype hwhli
  have hcard : Fintype.card ((K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1))) = finrank ℂ V := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
    omega
  have hli0 : LinearIndependent ℂ (Sum.elim xs v') :=
    LinearIndependent.sumElim_of_quotient hxsS v' (by rw [hmkv']; exact bVq.linearIndependent)
  obtain ⟨bV0, hbV0⟩ : ∃ bV0 : Basis ((K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1))) ℂ V,
      ⇑bV0 = Sum.elim xs v' :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli0 hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  have hbx : ∀ k, xs k = bV0 (Sum.inl k) := fun k => by
    rw [hbV0]
    rfl
  have hbv : ∀ j, v' j = bV0 (Sum.inr j) := fun j => by
    rw [hbV0]
    rfl
  have hξ1 : ∀ c, bV0.coord (Sum.inl (Sum.inr c)) (xs (Sum.inr c)) = 1 := by
    intro c
    rw [hbx, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  have hξ2 : ∀ c c', c' ≠ c → bV0.coord (Sum.inl (Sum.inr c)) (xs (Sum.inr c')) = 0 := by
    intro c c' hc
    rw [hbx, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    exact hc (Sum.inr.inj (Sum.inl.inj h))
  have hξ3 : ∀ c k, bV0.coord (Sum.inl (Sum.inr c)) (xs (Sum.inl k)) = 0 := by
    intro c k
    rw [hbx, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    exact Sum.inl_ne_inr (Sum.inl.inj h)
  have hξ4 : ∀ c j, bV0.coord (Sum.inl (Sum.inr c)) (v' j) = 0 := by
    intro c j
    rw [hbv, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
    exact Sum.inr_ne_inl
  -- the correction of rank at most `card C` on the block of the eigenvectors
  obtain ⟨R1A, hR1A⟩ : ∃ R1A : V →ₗ[ℂ] W, R1A = ∑ c : C, (-(tt (Sum.inr c))) •
      (bV0.coord (Sum.inl (Sum.inr c))).smulRight (B (xs (Sum.inr c)) - e c) := ⟨_, rfl⟩
  obtain ⟨R1B, hR1B⟩ : ∃ R1B : V →ₗ[ℂ] W, R1B = ∑ c : C, (1 : ℂ) •
      (bV0.coord (Sum.inl (Sum.inr c))).smulRight (B (xs (Sum.inr c)) - e c) := ⟨_, rfl⟩
  have hR1 : PRank (Fintype.card C) R1A R1B := by
    rw [hR1A, hR1B]
    exact ⟨C, inferInstance, fun c => -(tt (Sum.inr c)), fun _ => 1,
      fun c => bV0.coord (Sum.inl (Sum.inr c)), fun c => B (xs (Sum.inr c)) - e c, le_rfl,
      rfl, rfl⟩
  have hR1Al : ∀ k, R1A (xs (Sum.inl k)) = 0 := by
    intro k
    rw [hR1A, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ3, zero_smul, smul_zero]
  have hR1Bl : ∀ k, R1B (xs (Sum.inl k)) = 0 := by
    intro k
    rw [hR1B, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ3, zero_smul, smul_zero]
  have hR1Ar : ∀ c, R1A (xs (Sum.inr c)) =
      (-(tt (Sum.inr c))) • (B (xs (Sum.inr c)) - e c) := by
    intro c
    rw [hR1A, LinearMap.sum_apply, Finset.sum_eq_single c]
    · rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ1, one_smul]
    · intro c' _ hc'
      rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ2 c' c hc'.symm, zero_smul,
        smul_zero]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have hR1Br : ∀ c, R1B (xs (Sum.inr c)) = (1 : ℂ) • (B (xs (Sum.inr c)) - e c) := by
    intro c
    rw [hR1B, LinearMap.sum_apply, Finset.sum_eq_single c]
    · rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ1, one_smul]
    · intro c' _ hc'
      rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ2 c' c hc'.symm, zero_smul,
        smul_zero]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have hR1Av : ∀ j, R1A (v' j) = 0 := by
    intro j
    rw [hR1A, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ4, zero_smul, smul_zero]
  have hR1Bv : ∀ j, R1B (v' j) = 0 := by
    intro j
    rw [hR1B, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply, hξ4, zero_smul, smul_zero]
  -- the corrected pencil is block triangular with diagonal blocks
  obtain ⟨Ac, hAc⟩ : ∃ Ac : V →ₗ[ℂ] W, Ac = A - (R1A + R2A) := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : V →ₗ[ℂ] W, Bc = B - (R1B + R2B) := ⟨_, rfl⟩
  have hAcx : ∀ v, Ac v = A v - (R1A v + R2A v) := fun v => by
    rw [hAc]
    rfl
  have hBcx : ∀ v, Bc v = B v - (R1B v + R2B v) := fun v => by
    rw [hBc]
    rfl
  have hAcxs : ∀ k, Ac (xs k) = (-(tt k)) • wh k := by
    rintro (k | c)
    · rw [hAcx, hR1Al, hR2A0 _ (hxsV1 _), add_zero, sub_zero, hxse, hwhl]
    · rw [hAcx, hR1Ar, hR2A0 _ (hxsV1 _), add_zero, hxse, hwhr, smul_sub]
      abel
  have hBcxs : ∀ k, Bc (xs k) = (1 : ℂ) • wh k := by
    rintro (k | c)
    · rw [hBcx, hR1Bl, hR2B0 _ (hxsV1 _), add_zero, sub_zero, hwhl, one_smul]
    · rw [hBcx, hR1Br, hR2B0 _ (hxsV1 _), add_zero, hwhr, one_smul, one_smul]
      abel
  have hAcv : ∀ j, Ac (v' j) - a' j • w' j ∈ Submodule.span ℂ (Set.range wh) := by
    intro j
    have h1 := hAq' j
    rw [← hv' j, ← hw' j, hAqx, ← hR2A] at h1
    rw [hwhsp, ← Submodule.Quotient.mk_eq_zero, hAcx, hR1Av, zero_add]
    show W1'.mkQ (A (v' j) - R2A (v' j) - a' j • w' j) = 0
    rw [map_sub, map_sub, map_smul, h1]
    abel
  have hBcv : ∀ j, Bc (v' j) - b' j • w' j ∈ Submodule.span ℂ (Set.range wh) := by
    intro j
    have h1 := hBq' j
    rw [← hv' j, ← hw' j, hBqx, ← hR2B] at h1
    rw [hwhsp, ← Submodule.Quotient.mk_eq_zero, hBcx, hR1Bv, zero_add]
    show W1'.mkQ (B (v' j) - R2B (v' j) - b' j • w' j) = 0
    rw [map_sub, map_sub, map_smul, h1]
    abel
  have hne' : ∀ (k : K ⊕ C) (j : Fin (finrank ℂ (V ⧸ V1))),
      (-(tt k)) * b' j - a' j * 1 ≠ 0 := by
    intro k j h
    exact hFne (tt k) (httF k) j (by linear_combination -h)
  obtain ⟨Y, X, hYX⟩ := glue Ac Bc xs wh (fun k => -(tt k)) (fun _ => 1) v' w' a' b'
    hAcxs hBcxs hAcv hBcv hne'
  -- the final bases
  have hvh : ∀ j, Submodule.Quotient.mk (p := V1) (v' j - ∑ k, Y j k • xs k) = bVq j := by
    intro j
    rw [← hv' j]
    refine (Submodule.Quotient.eq V1).mpr ?_
    rw [sub_sub_cancel_left]
    exact V1.neg_mem (V1.sum_mem fun k _ => V1.smul_mem _ (hxsV1 k))
  have hwh' : ∀ j, Submodule.Quotient.mk (p := W1') (w' j + ∑ k, X j k • wh k) = bWq j := by
    intro j
    rw [← hw' j]
    refine (Submodule.Quotient.eq W1').mpr ?_
    rw [add_sub_cancel_left]
    exact W1'.sum_mem fun k _ => W1'.smul_mem _ (hwhmem k)
  have hliV : LinearIndependent ℂ (Sum.elim xs fun j => v' j - ∑ k, Y j k • xs k) :=
    LinearIndependent.sumElim_of_quotient hxsS _ (by
      have h : (Submodule.Quotient.mk (p := V1) ∘ fun j => v' j - ∑ k, Y j k • xs k) = bVq :=
        funext hvh
      rw [h]
      exact bVq.linearIndependent)
  have hliW : LinearIndependent ℂ (Sum.elim wh fun j => w' j + ∑ k, X j k • wh k) :=
    LinearIndependent.sumElim_of_quotient hwhS _ (by
      have h : (Submodule.Quotient.mk (p := W1') ∘ fun j => w' j + ∑ k, X j k • wh k) = bWq :=
        funext hwh'
      rw [h]
      exact bWq.linearIndependent)
  have hcardW : Fintype.card ((K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1))) = finrank ℂ W := by
    rw [hcard, hdim]
  have hDP : DP (Fintype.card C + finrank ℂ (V ⧸ V1) / 2) A B := by
    refine ⟨(K ⊕ C) ⊕ Fin (finrank ℂ (V ⧸ V1)), inferInstance,
      basisOfLinearIndependentOfCardEqFinrank' _ hliV hcard,
      basisOfLinearIndependentOfCardEqFinrank' _ hliW hcardW,
      Sum.elim (fun k => -(tt k)) a', Sum.elim (fun _ => 1) b', R1A + R2A, R1B + R2B,
      hR1.add hR2, ?_, ?_⟩
    · rintro (k | j)
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl,
          LinearMap.add_apply]
        rw [← hAcxs k, hAcx]
        abel
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr,
          LinearMap.add_apply]
        rw [← (hYX j).1, hAcx]
        abel
    · rintro (k | j)
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl,
          LinearMap.add_apply]
        rw [← hBcxs k, hBcx]
        abel
      · simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr,
          LinearMap.add_apply]
        rw [← (hYX j).2, hBcx]
        abel
  exact hDP.mono (by omega)

end Abstract

section Final

open Matrix

/-- The conclusion of H2 with `r` rank-one matrices. -/
def Goal (n r : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin r → Fin n → ℂ)
    (α β : Fin r → ℂ), IsUnit P ∧ IsUnit Q ∧
    A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
    B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j)

/-- Every pencil of `n × n` matrices is, in suitable bases, simultaneously diagonal up to
`n / 2` rank-one pencils. -/
theorem all_pencils : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), Goal n (n / 2) A B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have case2 : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
        (∀ v : Fin n → ℂ, A *ᵥ v = 0 → B *ᵥ v = 0 → v = 0) → Goal n (n / 2) A B := by
      intro A B hk
      have h := DP_of_no_kernel (Matrix.toLin' A) (Matrix.toLin' B) rfl
        (fun v h1 h2 => hk v (by rwa [Matrix.toLin'_apply] at h1)
          (by rwa [Matrix.toLin'_apply] at h2))
      rw [Module.finrank_fin_fun] at h
      exact matrix_of_DP A B h
    intro A B
    by_cases hk : ∀ v : Fin n → ℂ, A *ᵥ v = 0 → B *ᵥ v = 0 → v = 0
    · exact case2 A B hk
    by_cases hl : ∀ φ : Fin n → ℂ, φ ᵥ* A = 0 → φ ᵥ* B = 0 → φ = 0
    · obtain ⟨P, Q, a, b, u, v, α, β, hP, hQ, hA, hB⟩ := case2 Aᵀ Bᵀ (fun φ h1 h2 =>
        hl φ (by rwa [Matrix.mulVec_transpose] at h1) (by rwa [Matrix.mulVec_transpose] at h2))
      have htr : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) (γ : Fin (n / 2) → ℂ),
          Mᵀ = P * Matrix.diagonal c * Q + ∑ j, γ j • Matrix.vecMulVec (u j) (v j) →
          M = Qᵀ * Matrix.diagonal c * Pᵀ + ∑ j, γ j • Matrix.vecMulVec (v j) (u j) := by
        intro M c γ h
        have h1 := congrArg Matrix.transpose h
        rw [Matrix.transpose_transpose] at h1
        rw [h1, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
          Matrix.diagonal_transpose, Matrix.transpose_sum, Matrix.mul_assoc]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by
          rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec]
      exact ⟨Qᵀ, Pᵀ, a, b, v, u, α, β,
        (Matrix.isUnit_iff_isUnit_det _).mpr (by
          rw [Matrix.det_transpose]
          exact (Matrix.isUnit_iff_isUnit_det _).mp hQ),
        (Matrix.isUnit_iff_isUnit_det _).mpr (by
          rw [Matrix.det_transpose]
          exact (Matrix.isUnit_iff_isUnit_det _).mp hP), htr A a α hA, htr B b β hB⟩
    · push Not at hk hl
      obtain ⟨v0, hv0A, hv0B, hv0⟩ := hk
      obtain ⟨φ0, hφA, hφB, hφ0⟩ := hl
      have hn : n ≠ 0 := by
        rintro rfl
        exact hv0 (Subsingleton.elim _ _)
      let φ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
        { toFun := fun x => φ0 ⬝ᵥ x
          map_add' := fun x y => dotProduct_add φ0 x y
          map_smul' := fun c x => by simp [dotProduct_smul] }
      have hφ : φ ≠ 0 := by
        intro h
        apply hφ0
        funext j
        have h1 := LinearMap.congr_fun h (Pi.single j 1)
        simpa [φ] using h1
      have hDP : DP ((n - 1) / 2) (Matrix.toLin' A) (Matrix.toLin' B) := by
        refine DP_of_zero_block _ _ v0 hv0 (by rw [Matrix.toLin'_apply]; exact hv0A)
          (by rw [Matrix.toLin'_apply]; exact hv0B) φ hφ ?_ ?_ _ ?_
        · intro x
          show φ0 ⬝ᵥ (Matrix.toLin' A x) = 0
          rw [Matrix.toLin'_apply, Matrix.dotProduct_mulVec, hφA, zero_dotProduct]
        · intro x
          show φ0 ⬝ᵥ (Matrix.toLin' B x) = 0
          rw [Matrix.toLin'_apply, Matrix.dotProduct_mulVec, hφB, zero_dotProduct]
        · intro A' B'
          have hV : finrank ℂ ((Fin n → ℂ) ⧸ Submodule.span ℂ {v0}) = n - 1 := by
            have h := finrank_quot_span_singleton hv0
            rw [Module.finrank_fin_fun] at h
            omega
          have hW : finrank ℂ (LinearMap.ker φ) = n - 1 := by
            have h := finrank_ker_functional hφ
            rw [Module.finrank_fin_fun] at h
            omega
          exact DP_of_matrices hV hW A' B' (ih (n - 1) (by omega))
      exact matrix_of_DP A B (hDP.mono (by omega))

end Final

end SqH2

theorem OMA.solution : OMA.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1.H2 :=
  fun n A B _ => SqH2.all_pencils n A B
