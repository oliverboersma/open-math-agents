import OMAReductions.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1
import Mathlib

/-!
# Upper bound for maximal rank of `m × n × (mn - u)` tensors

Step `Arxiv.0805.3777.isMaxRank_of_le_min.R1.H1`: for `3 ≤ m ≤ n` and `u ≤ min 4 m`, every
subspace `S` of `m × n` complex matrices of codimension at least `u` is contained in the span of
`m * n - ⌈u / 2⌉` rank-one matrices.
-/

namespace MaxRankLeMinH1

open Matrix

private abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

private def rk1Set {m n : ℕ} (W : Submodule ℂ (Mat m n)) : Set (Mat m n) :=
  {M | M ∈ W ∧ ∃ a : Fin m → ℂ, ∃ b : Fin n → ℂ, M = vecMulVec a b}

private lemma coveredBy_of_spanned {m n r : ℕ} {S W : Submodule ℂ (Mat m n)}
    (hSW : S ≤ W) (hW : W ≤ Submodule.span ℂ (rk1Set W)) (hr : Module.finrank ℂ W ≤ r) :
    ∃ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ),
      S ≤ Submodule.span ℂ (Set.range fun i => vecMulVec (x i) (y i)) := by
  classical
  obtain ⟨T, hTW, hspan, hli⟩ := exists_linearIndependent ℂ (rk1Set W)
  have hTfin : T.Finite := hli.setFinite
  letI : Fintype T := hTfin.fintype
  have hspan_le : Submodule.span ℂ (rk1Set W) ≤ W :=
    Submodule.span_le.mpr fun M hM => hM.1
  have hcard : Fintype.card T ≤ r := by
    have h1 : Module.finrank ℂ (Submodule.span ℂ T) = Fintype.card T := by
      rw [← finrank_span_eq_card hli, Subtype.range_coe]
    rw [← h1, hspan]
    exact (Submodule.finrank_mono hspan_le).trans hr
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  have hab : ∀ k : Fin (Fintype.card T), ∃ a b, (e k).1 = vecMulVec a b := fun k =>
    (hTW (e k).2).2
  choose a0 b0 hab0 using hab
  let x : Fin r → Fin m → ℂ := fun i => if hi : i.1 < Fintype.card T then a0 ⟨i.1, hi⟩ else 0
  let y : Fin r → Fin n → ℂ := fun i => if hi : i.1 < Fintype.card T then b0 ⟨i.1, hi⟩ else 0
  refine ⟨x, y, hSW.trans (hW.trans ?_)⟩
  rw [← hspan]
  refine Submodule.span_mono ?_
  intro M hM
  let k : Fin (Fintype.card T) := e.symm ⟨M, hM⟩
  refine ⟨⟨k.1, lt_of_lt_of_le k.2 hcard⟩, ?_⟩
  simp only [x, y, k.2, ↓reduceDIte]
  rw [← hab0 k]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨M, hM⟩)

private lemma top_spanned_rk1 (m n : ℕ) :
    (⊤ : Submodule ℂ (Mat m n)) ≤ Submodule.span ℂ (rk1Set (⊤ : Submodule ℂ (Mat m n))) := by
  intro M _
  have hM : M = ∑ i : Fin m, ∑ j : Fin n,
      M i j • vecMulVec (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'
        simp [Pi.single_eq_of_ne (M := fun _ : Fin n => ℂ) (Ne.symm hj')]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    · intro i' _ hi'
      refine Finset.sum_eq_zero fun j' _ => ?_
      simp [Pi.single_eq_of_ne (M := fun _ : Fin m => ℂ) (Ne.symm hi')]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hM]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨trivial, _, _, rfl⟩)

private lemma vecMulVec_add_left {m n : ℕ} (x₁ x₂ : Fin m → ℂ) (y : Fin n → ℂ) :
    vecMulVec (x₁ + x₂) y = vecMulVec x₁ y + vecMulVec x₂ y := by
  ext i j; simp [vecMulVec_apply, add_mul]

private lemma vecMulVec_add_right {m n : ℕ} (x : Fin m → ℂ) (y₁ y₂ : Fin n → ℂ) :
    vecMulVec x (y₁ + y₂) = vecMulVec x y₁ + vecMulVec x y₂ := by
  ext i j; simp [vecMulVec_apply, mul_add]

private lemma vecMulVec_sub_right {m n : ℕ} (x : Fin m → ℂ) (y₁ y₂ : Fin n → ℂ) :
    vecMulVec x (y₁ - y₂) = vecMulVec x y₁ - vecMulVec x y₂ := by
  ext i j; simp [vecMulVec_apply, mul_sub]

private lemma vecMulVec_sub_left {m n : ℕ} (x₁ x₂ : Fin m → ℂ) (y : Fin n → ℂ) :
    vecMulVec (x₁ - x₂) y = vecMulVec x₁ y - vecMulVec x₂ y := by
  ext i j; simp [vecMulVec_apply, sub_mul]

private lemma vecMulVec_smul_left {m n : ℕ} (c : ℂ) (x : Fin m → ℂ) (y : Fin n → ℂ) :
    vecMulVec (c • x) y = c • vecMulVec x y := by
  ext i j; simp [vecMulVec_apply, mul_assoc]

private lemma vecMulVec_smul_right {m n : ℕ} (c : ℂ) (x : Fin m → ℂ) (y : Fin n → ℂ) :
    vecMulVec x (c • y) = c • vecMulVec x y := by
  ext i j; simp [vecMulVec_apply]; ring

private def rowMap {m n : ℕ} {D : Type*} [AddCommGroup D] [Module ℂ D]
    (C : Mat m n →ₗ[ℂ] D) (x : Fin m → ℂ) : (Fin n → ℂ) →ₗ[ℂ] D where
  toFun y := C (vecMulVec x y)
  map_add' y₁ y₂ := by rw [vecMulVec_add_right, map_add]
  map_smul' c y := by rw [vecMulVec_smul_right, map_smul]; rfl

private def colMap {m n : ℕ} {D : Type*} [AddCommGroup D] [Module ℂ D]
    (C : Mat m n →ₗ[ℂ] D) (y : Fin n → ℂ) : (Fin m → ℂ) →ₗ[ℂ] D where
  toFun x := C (vecMulVec x y)
  map_add' x₁ x₂ := by rw [vecMulVec_add_left, map_add]
  map_smul' c x := by rw [vecMulVec_smul_left, map_smul]; rfl

private def stripRight {m n : ℕ} (F₀ : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Mat m n) :=
  Submodule.span ℂ {M | ∃ x : Fin m → ℂ, ∃ y ∈ F₀, M = vecMulVec x y}

private lemma exists_mat_decomp_basis {m n : ℕ} (b : Module.Basis (Fin m) ℂ (Fin m → ℂ)) (M : Mat m n) :
    ∃ y : Fin m → Fin n → ℂ, M = ∑ k : Fin m, vecMulVec (b k) (y k) := by
  let y : Fin m → Fin n → ℂ := fun k j => ∑ i : Fin m, b.repr (Pi.single i (1 : ℂ)) k * M i j
  refine ⟨y, ?_⟩
  ext i j
  simp only [Matrix.sum_apply, vecMulVec_apply, y]
  have hi : ∑ k : Fin m, b.repr (Pi.single i (1 : ℂ)) k * b k i = 1 := by
    have h := congrFun (b.sum_repr (Pi.single i (1 : ℂ))) i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hne : ∀ i' : Fin m, i' ≠ i →
      ∑ k : Fin m, b.repr (Pi.single i' (1 : ℂ)) k * b k i = 0 := by
    intro i' hi'
    have h := congrFun (b.sum_repr (Pi.single i' (1 : ℂ))) i
    have h0 : (Pi.single i' (1 : ℂ) : Fin m → ℂ) i = 0 :=
      Pi.single_eq_of_ne (M := fun _ : Fin m => ℂ) (Ne.symm hi') 1
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h0] using h
  calc M i j = ∑ i' : Fin m, (if i' = i then 1 else 0) * M i' j := by simp
    _ = ∑ i' : Fin m, (∑ k : Fin m, b.repr (Pi.single i' (1 : ℂ)) k * b k i) * M i' j := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases h : i' = i
        · subst h; simp [hi]
        · simp [h, hne i' h]
    _ = ∑ k : Fin m, b k i * ∑ i' : Fin m, b.repr (Pi.single i' (1 : ℂ)) k * M i' j := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i' _ => ?_
        ring

private lemma ker_spanned_of_lift_right {m n : ℕ} {D : Type*} [AddCommGroup D] [Module ℂ D]
    (C : Mat m n →ₗ[ℂ] D) (F₀ : Submodule ℂ (Fin n → ℂ))
    (hspan : Submodule.span ℂ
      {x : Fin m → ℂ | ∀ y : Fin n → ℂ, ∃ z ∈ F₀, C (vecMulVec x z) = C (vecMulVec x y)} = ⊤)
    (hstrip : LinearMap.ker C ⊓ stripRight F₀ ≤ Submodule.span ℂ (rk1Set (LinearMap.ker C))) :
    LinearMap.ker C ≤ Submodule.span ℂ (rk1Set (LinearMap.ker C)) := by
  classical
  let Xgood : Set (Fin m → ℂ) :=
    {x | ∀ y : Fin n → ℂ, ∃ z ∈ F₀, C (vecMulVec x z) = C (vecMulVec x y)}
  obtain ⟨T, hTX, hTspan, hTli⟩ := exists_linearIndependent ℂ Xgood
  have hTfin : T.Finite := hTli.setFinite
  letI : Fintype T := hTfin.fintype
  have hTtop : Submodule.span ℂ T = ⊤ := hTspan.trans hspan
  have hcard : Fintype.card T = m := by
    have h1 : Module.finrank ℂ (Submodule.span ℂ T) = Fintype.card T := by
      rw [← finrank_span_eq_card hTli, Subtype.range_coe]
    rw [hTtop, finrank_top] at h1
    simpa using h1.symm
  let e : Fin m ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  let b : Module.Basis (Fin m) ℂ (Fin m → ℂ) :=
    Module.Basis.mk (hTli.comp e e.injective) (by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe, hTtop])
  have hb_good : ∀ k : Fin m, b k ∈ Xgood := fun k => by
    have : b k = (e k).1 := by simp [b]
    rw [this]
    exact hTX (e k).2
  intro M hM
  obtain ⟨y, rfl⟩ := exists_mat_decomp_basis b M
  choose z hzF hzC using fun k => hb_good k (y k)
  let M1 : Mat m n := ∑ k : Fin m, vecMulVec (b k) (y k - z k)
  let M2 : Mat m n := ∑ k : Fin m, vecMulVec (b k) (z k)
  have hdecomp : ∑ k : Fin m, vecMulVec (b k) (y k) = M1 + M2 := by
    simp only [M1, M2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← vecMulVec_add_right, sub_add_cancel]
  have hM1 : M1 ∈ Submodule.span ℂ (rk1Set (LinearMap.ker C)) := by
    refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ?_
    refine ⟨?_, b k, y k - z k, rfl⟩
    rw [LinearMap.mem_ker, vecMulVec_sub_right, map_sub, hzC k, sub_self]
  have hM2_ker : M2 ∈ LinearMap.ker C := by
    rw [LinearMap.mem_ker]
    have hCM : C (∑ k : Fin m, vecMulVec (b k) (y k)) = 0 := LinearMap.mem_ker.mp hM
    simpa only [M2, map_sum, hzC] using hCM
  have hM2_strip : M2 ∈ stripRight F₀ :=
    Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨b k, z k, hzF k, rfl⟩
  rw [hdecomp]
  exact Submodule.add_mem _ hM1 (hstrip ⟨hM2_ker, hM2_strip⟩)

private lemma ker_spanned_of_row_rank_le_one {m n : ℕ} {D : Type*} [AddCommGroup D] [Module ℂ D]
    (C : Mat m n →ₗ[ℂ] D) (hrow : ∀ x : Fin m → ℂ, Module.finrank ℂ (LinearMap.range (rowMap C x)) ≤ 1) :
    LinearMap.ker C ≤ Submodule.span ℂ (rk1Set (LinearMap.ker C)) := by
  by_cases hC0 : C = 0
  · subst hC0
    intro M _
    have htop := top_spanned_rk1 m n (by trivial : M ∈ (⊤ : Submodule ℂ (Mat m n)))
    refine Submodule.span_mono ?_ htop
    rintro N ⟨-, a, b, rfl⟩
    exact ⟨by simp, a, b, rfl⟩
  · have hex : ∃ x₀ y₀, C (vecMulVec x₀ y₀) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hC0
      ext M
      have hM : M ∈ Submodule.span ℂ (rk1Set (⊤ : Submodule ℂ (Mat m n))) :=
        top_spanned_rk1 m n trivial
      refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb => by simp [ha, hb])
        (fun c _ _ ha => by simp [ha]) hM
      rintro N ⟨-, a, b, rfl⟩
      exact h a b
    obtain ⟨x₀, y₀, hxy₀⟩ := hex
    let F₀ : Submodule ℂ (Fin n → ℂ) := Submodule.span ℂ {y₀}
    refine ker_spanned_of_lift_right C F₀ ?_ ?_
    · rw [eq_top_iff]
      intro v _
      have hmem_of_ne : ∀ x : Fin m → ℂ, C (vecMulVec x y₀) ≠ 0 →
          x ∈ {x | ∀ y : Fin n → ℂ, ∃ z ∈ F₀, C (vecMulVec x z) = C (vecMulVec x y)} := by
        intro x hx y
        have h1 : Module.finrank ℂ (LinearMap.range (rowMap C x)) ≤ 1 := hrow x
        have hle : Submodule.span ℂ ({C (vecMulVec x y₀)} : Set D) ≤ LinearMap.range (rowMap C x) :=
          Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨y₀, rfl⟩)
        have hpos : Module.finrank ℂ (Submodule.span ℂ ({C (vecMulVec x y₀)} : Set D)) = 1 :=
          finrank_span_singleton hx
        have heq : Submodule.span ℂ ({C (vecMulVec x y₀)} : Set D) = LinearMap.range (rowMap C x) :=
          Submodule.eq_of_le_of_finrank_le hle (by omega)
        have hy_mem : C (vecMulVec x y) ∈ Submodule.span ℂ ({C (vecMulVec x y₀)} : Set D) := by
          rw [heq]; exact ⟨y, rfl⟩
        rw [Submodule.mem_span_singleton] at hy_mem
        obtain ⟨c, hc⟩ := hy_mem
        refine ⟨c • y₀, Submodule.smul_mem F₀ c (Submodule.subset_span rfl), ?_⟩
        rw [vecMulVec_smul_right, map_smul, hc]
      by_cases hv : C (vecMulVec v y₀) ≠ 0
      · exact Submodule.subset_span (hmem_of_ne v hv)
      · push_neg at hv
        have hvx : C (vecMulVec (v + x₀) y₀) ≠ 0 := by
          rw [vecMulVec_add_left, map_add, hv, zero_add]
          exact hxy₀
        have h1 := Submodule.subset_span (R := ℂ) (hmem_of_ne (v + x₀) hvx)
        have h2 := Submodule.subset_span (R := ℂ) (hmem_of_ne x₀ hxy₀)
        simpa using Submodule.sub_mem _ h1 h2
    · rintro M ⟨hMker, hMstrip⟩
      have hsingle : ∀ N ∈ stripRight F₀, ∃ u : Fin m → ℂ, N = vecMulVec u y₀ := by
        intro N hN
        refine Submodule.span_induction ?_ ⟨0, by ext i j; simp [vecMulVec_apply]⟩ ?_ ?_ hN
        · rintro _ ⟨x, y, hy, rfl⟩
          rw [Submodule.mem_span_singleton] at hy
          obtain ⟨c, rfl⟩ := hy
          exact ⟨c • x, by rw [vecMulVec_smul_left, vecMulVec_smul_right]⟩
        · rintro _ _ _ _ ⟨u₁, rfl⟩ ⟨u₂, rfl⟩
          exact ⟨u₁ + u₂, (vecMulVec_add_left u₁ u₂ y₀).symm⟩
        · rintro c _ _ ⟨u, rfl⟩
          exact ⟨c • u, (vecMulVec_smul_left c u y₀).symm⟩
      obtain ⟨u, rfl⟩ := hsingle M hMstrip
      exact Submodule.subset_span ⟨hMker, u, y₀, rfl⟩

private lemma ker_spanned_of_col_rank_le_one {m n : ℕ} {D : Type*} [AddCommGroup D] [Module ℂ D]
    (C : Mat m n →ₗ[ℂ] D) (hcol : ∀ y : Fin n → ℂ, Module.finrank ℂ (LinearMap.range (colMap C y)) ≤ 1) :
    LinearMap.ker C ≤ Submodule.span ℂ (rk1Set (LinearMap.ker C)) := by
  let tr : Mat n m →ₗ[ℂ] Mat m n :=
    { toFun := Matrix.transpose
      map_add' := fun _ _ => Matrix.transpose_add _ _
      map_smul' := fun _ _ => Matrix.transpose_smul _ _ }
  let C' : Mat n m →ₗ[ℂ] D := C.comp tr
  have hrow' : ∀ y : Fin n → ℂ, Module.finrank ℂ (LinearMap.range (rowMap C' y)) ≤ 1 := by
    intro y
    have hEq : rowMap C' y = colMap C y := by
      ext x
      simp only [rowMap, colMap, C', tr, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
      congr 1
      ext i j
      simp [vecMulVec_apply, mul_comm]
    rw [hEq]
    exact hcol y
  have hspan' := ker_spanned_of_row_rank_le_one C' hrow'
  intro M hM
  have hMt : Mᵀ ∈ LinearMap.ker C' := by
    rw [LinearMap.mem_ker]
    simpa [C', tr] using LinearMap.mem_ker.mp hM
  have hMt_span := hspan' hMt
  have hback : M = tr Mᵀ := by ext i j; rfl
  rw [hback]
  refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
    (fun c _ _ ha => by rw [map_smul]; exact Submodule.smul_mem _ c ha) hMt_span
  rintro N ⟨hNker, a, b, rfl⟩
  refine Submodule.subset_span ⟨?_, b, a, ?_⟩
  · rw [LinearMap.mem_ker]
    exact LinearMap.mem_ker.mp hNker
  · ext i j
    simp [tr, vecMulVec_apply, mul_comm]

private lemma exists_surj_vanishing {m n k : ℕ} (S : Submodule ℂ (Mat m n))
    (hk : Module.finrank ℂ S + k ≤ m * n) :
    ∃ B : Mat m n →ₗ[ℂ] (Fin k → ℂ), Function.Surjective B ∧ S ≤ LinearMap.ker B := by
  let Q := Mat m n ⧸ S
  have hQ : Module.finrank ℂ Q + Module.finrank ℂ S = m * n := by
    have h := Submodule.finrank_quotient_add_finrank S
    have hdom : Module.finrank ℂ (Mat m n) = m * n := by simp [Module.finrank_matrix]
    rw [hdom] at h
    exact h
  have hkQ : k ≤ Module.finrank ℂ Q := by omega
  let bQ := Module.finBasis ℂ Q
  let proj : Q →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun q i => bQ.repr q ⟨i.1, lt_of_lt_of_le i.2 hkQ⟩
      map_add' := fun q₁ q₂ => by ext i; simp
      map_smul' := fun c q => by ext i; simp }
  refine ⟨proj.comp S.mkQ, ?_, ?_⟩
  · intro v
    let q : Q := ∑ i : Fin k, v i • bQ ⟨i.1, lt_of_lt_of_le i.2 hkQ⟩
    obtain ⟨M, hMq⟩ := Submodule.mkQ_surjective S q
    refine ⟨M, ?_⟩
    ext i
    simp only [LinearMap.comp_apply, hMq, proj, LinearMap.coe_mk, AddHom.coe_mk, q, map_sum,
      map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Module.Basis.repr_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hne : (⟨j.1, lt_of_lt_of_le j.2 hkQ⟩ : Fin (Module.finrank ℂ Q)) ≠
          ⟨i.1, lt_of_lt_of_le i.2 hkQ⟩ :=
        fun h => hji (Fin.ext (congrArg (fun x : Fin (Module.finrank ℂ Q) => x.val) h))
      simp [Finsupp.single_eq_of_ne hne.symm]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · intro M hM
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).mpr hM, map_zero]

private lemma exists_not_mem_two_proper {V : Type*} [AddCommGroup V] [Module ℂ V]
    {U₁ U₂ : Submodule ℂ V} (h₁ : U₁ ≠ ⊤) (h₂ : U₂ ≠ ⊤) :
    ∃ v : V, v ∉ U₁ ∧ v ∉ U₂ := by
  have hex₁ : ∃ u₁, u₁ ∉ U₁ := by
    by_contra h; push_neg at h; exact h₁ (eq_top_iff.mpr fun x _ => h x)
  have hex₂ : ∃ u₂, u₂ ∉ U₂ := by
    by_contra h; push_neg at h; exact h₂ (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨u₁, hu₁⟩ := hex₁
  obtain ⟨u₂, hu₂⟩ := hex₂
  by_cases h12 : u₁ ∉ U₂
  · exact ⟨u₁, hu₁, h12⟩
  · push_neg at h12
    by_cases h21 : u₂ ∉ U₁
    · exact ⟨u₂, h21, hu₂⟩
    · push_neg at h21
      refine ⟨u₁ + u₂, ?_, ?_⟩
      · intro h; exact hu₁ (by simpa using U₁.sub_mem h h21)
      · intro h; exact hu₂ (by simpa using U₂.sub_mem h h12)

private lemma exists_t_linear_quad_ne_zero (c₀ c₁ d₀ d₁ d₂ : ℂ) (hc₀ : c₀ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ∃ t : ℂ, c₀ + c₁ * t ≠ 0 ∧ d₀ + d₁ * t + d₂ * t ^ 2 ≠ 0 := by
  by_contra h
  push_neg at h
  have hq : ∀ t : ℂ, c₀ + c₁ * t ≠ 0 → d₀ + d₁ * t + d₂ * t ^ 2 = 0 := h
  have hlin : ∀ t₁ t₂ : ℂ, t₁ ≠ t₂ → c₀ + c₁ * t₁ = 0 → c₀ + c₁ * t₂ = 0 → False := by
    intro t₁ t₂ hne h1 h2
    have hc1 : c₁ * (t₁ - t₂) = 0 := by linear_combination h1 - h2
    have : c₁ = 0 := (mul_eq_zero.mp hc1).resolve_right (sub_ne_zero.mpr hne)
    rw [this] at h1
    simp at h1
    exact hc₀ h1
  have hquad3 : ∀ a b c : ℂ, a ≠ b → a ≠ c → b ≠ c →
      d₀ + d₁ * a + d₂ * a ^ 2 = 0 →
      d₀ + d₁ * b + d₂ * b ^ 2 = 0 →
      d₀ + d₁ * c + d₂ * c ^ 2 = 0 → False := by
    intro a b c hab hac hbc ha hb hc
    have h1 : (a - b) * (d₁ + d₂ * (a + b)) = 0 := by linear_combination ha - hb
    have h2 : (a - c) * (d₁ + d₂ * (a + c)) = 0 := by linear_combination ha - hc
    have h1' : d₁ + d₂ * (a + b) = 0 := (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hab)
    have h2' : d₁ + d₂ * (a + c) = 0 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hac)
    have h3 : d₂ * (b - c) = 0 := by linear_combination h1' - h2'
    exact hd₂ ((mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hbc))
  by_cases h0 : c₀ + c₁ * 0 = 0
  · exact hc₀ (by simpa using h0)
  · by_cases h1 : c₀ + c₁ * 1 = 0
    · have h2 : c₀ + c₁ * 2 ≠ 0 := fun h2 => hlin 1 2 (by norm_num) h1 h2
      have h3 : c₀ + c₁ * 3 ≠ 0 := fun h3 => hlin 1 3 (by norm_num) h1 h3
      exact hquad3 0 2 3 (by norm_num) (by norm_num) (by norm_num) (hq 0 h0) (hq 2 h2) (hq 3 h3)
    · by_cases h2 : c₀ + c₁ * 2 = 0
      · have h3 : c₀ + c₁ * 3 ≠ 0 := fun h3 => hlin 2 3 (by norm_num) h2 h3
        exact hquad3 0 1 3 (by norm_num) (by norm_num) (by norm_num) (hq 0 h0) (hq 1 h1) (hq 3 h3)
      · exact hquad3 0 1 2 (by norm_num) (by norm_num) (by norm_num) (hq 0 h0) (hq 1 h1) (hq 2 h2)

private lemma exists_corner {m n : ℕ} (B : Mat m n →ₗ[ℂ] (Fin 3 → ℂ)) (hB : Function.Surjective B)
    (hrow : ¬ ∀ x : Fin m → ℂ, Module.finrank ℂ (LinearMap.range (rowMap B x)) ≤ 1)
    (hcol : ¬ ∀ y : Fin n → ℂ, Module.finrank ℂ (LinearMap.range (colMap B y)) ≤ 1) :
    ∃ (e₁ e₂ : Fin m → ℂ) (f₁ f₂ : Fin n → ℂ),
      LinearIndependent ℂ ![B (vecMulVec e₁ f₁), B (vecMulVec e₁ f₂), B (vecMulVec e₂ f₁)] := by
  push_neg at hrow hcol
  obtain ⟨e₁, he₁⟩ := hrow
  obtain ⟨y₀, hy₀⟩ := hcol
  let P : Submodule ℂ (Fin 3 → ℂ) := LinearMap.range (rowMap B e₁)
  have he₁P : 1 < Module.finrank ℂ P := he₁
  have hP_le : Module.finrank ℂ P ≤ 3 := by
    simpa using Submodule.finrank_le P
  have hP_cases : Module.finrank ℂ P = 2 ∨ Module.finrank ℂ P = 3 := by omega
  rcases hP_cases with hP2 | hP3
  · have hP_ne_top : P ≠ ⊤ := by
      intro h
      rw [h, finrank_top] at hP2
      simp at hP2
    let U₁ : Submodule ℂ (Fin n → ℂ) := LinearMap.ker (rowMap B e₁)
    let U₂ : Submodule ℂ (Fin n → ℂ) :=
      { carrier := {y | ∀ x : Fin m → ℂ, B (vecMulVec x y) ∈ P}
        add_mem' := fun ha hb x => by rw [vecMulVec_add_right, map_add]; exact P.add_mem (ha x) (hb x)
        zero_mem' := fun x => by
          have hz : vecMulVec x (0 : Fin n → ℂ) = 0 := by ext i j; simp [vecMulVec_apply]
          rw [hz, map_zero]
          exact P.zero_mem
        smul_mem' := fun c _ ha x => by rw [vecMulVec_smul_right, map_smul]; exact P.smul_mem c (ha x) }
    have hU₁ : U₁ ≠ ⊤ := by
      intro h
      have : LinearMap.range (rowMap B e₁) = ⊥ := by
        rw [LinearMap.range_eq_bot]
        refine LinearMap.ext fun y => ?_
        have hy : y ∈ U₁ := by rw [h]; trivial
        exact LinearMap.mem_ker.mp hy
      change P = ⊥ at this
      rw [this, finrank_bot] at hP2
      omega
    have hU₂ : U₂ ≠ ⊤ := by
      intro h
      apply hP_ne_top
      rw [eq_top_iff]
      intro v _
      obtain ⟨M, rfl⟩ := hB v
      have hM := top_spanned_rk1 m n (by trivial : M ∈ (⊤ : Submodule ℂ (Mat m n)))
      refine Submodule.span_induction ?_ (by simp)
        (fun _ _ _ _ ha hb => by rw [map_add]; exact P.add_mem ha hb)
        (fun c _ _ ha => by rw [map_smul]; exact P.smul_mem c ha) hM
      rintro N ⟨-, a, b, rfl⟩
      have hb : b ∈ U₂ := by rw [h]; trivial
      exact hb a
    obtain ⟨f₁, hf₁, hf₂⟩ := exists_not_mem_two_proper hU₁ hU₂
    have hq_ne : B (vecMulVec e₁ f₁) ≠ 0 := hf₁
    have hex_e₂ : ∃ e₂ : Fin m → ℂ, B (vecMulVec e₂ f₁) ∉ P := by
      by_contra h; push_neg at h; exact hf₂ h
    obtain ⟨e₂, he₂⟩ := hex_e₂
    have hex_f₂ : ∃ f₂ : Fin n → ℂ, B (vecMulVec e₁ f₂) ∉ Submodule.span ℂ ({B (vecMulVec e₁ f₁)} : Set (Fin 3 → ℂ)) := by
      by_contra h
      push_neg at h
      have hle : P ≤ Submodule.span ℂ ({B (vecMulVec e₁ f₁)} : Set (Fin 3 → ℂ)) := by
        rintro _ ⟨y, rfl⟩; exact h y
      have h1 := Submodule.finrank_mono hle
      rw [finrank_span_singleton hq_ne] at h1
      omega
    obtain ⟨f₂, hf₂'⟩ := hex_f₂
    refine ⟨e₁, e₂, f₁, f₂, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • B (vecMulVec e₁ f₁) + c 1 • B (vecMulVec e₁ f₂) + c 2 • B (vecMulVec e₂ f₁) = 0 := by
      simpa [Fin.sum_univ_three] using hc
    have hc2 : c 2 = 0 := by
      by_contra h2
      have hmem : B (vecMulVec e₂ f₁) ∈ P := by
        have h1 : B (vecMulVec e₂ f₁) =
            (-(c 0 / c 2)) • B (vecMulVec e₁ f₁) + (-(c 1 / c 2)) • B (vecMulVec e₁ f₂) := by
          ext k
          have hk := congrFun hsum k
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
          field_simp [h2]
          linear_combination hk
        rw [h1]
        exact P.add_mem (P.smul_mem _ ⟨f₁, rfl⟩) (P.smul_mem _ ⟨f₂, rfl⟩)
      exact he₂ hmem
    have hc1 : c 1 = 0 := by
      by_contra h1
      rw [hc2, zero_smul, add_zero] at hsum
      apply hf₂'
      rw [Submodule.mem_span_singleton]
      refine ⟨-(c 0 / c 1), ?_⟩
      ext k
      have hk := congrFun hsum k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
      field_simp [h1]
      linear_combination -hk
    have hc0 : c 0 = 0 := by
      rw [hc1, hc2, zero_smul, zero_smul, add_zero, add_zero] at hsum
      exact (smul_eq_zero.mp hsum).resolve_right hq_ne
    intro i
    fin_cases i <;> assumption
  · -- finrank P = 3, so P = ⊤
    have hPtop : P = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hP3)
    -- pick x₁, x₂ with B(x₁, y₀), B(x₂, y₀) linearly independent
    have hex_x₁ : ∃ x₁, B (vecMulVec x₁ y₀) ≠ 0 := by
      by_contra h; push_neg at h
      have : LinearMap.range (colMap B y₀) = ⊥ := by
        rw [LinearMap.range_eq_bot]; exact LinearMap.ext fun x => h x
      rw [this, finrank_bot] at hy₀; omega
    obtain ⟨x₁, hx₁⟩ := hex_x₁
    have hex_x₂ : ∃ x₂, B (vecMulVec x₂ y₀) ∉ Submodule.span ℂ ({B (vecMulVec x₁ y₀)} : Set (Fin 3 → ℂ)) := by
      by_contra h; push_neg at h
      have hle : LinearMap.range (colMap B y₀) ≤ Submodule.span ℂ ({B (vecMulVec x₁ y₀)} : Set (Fin 3 → ℂ)) := by
        rintro _ ⟨x, rfl⟩; exact h x
      have h1 := Submodule.finrank_mono hle
      rw [finrank_span_singleton hx₁] at h1
      omega
    obtain ⟨x₂, hx₂⟩ := hex_x₂
    -- some 2x2 minor (k₁, k₂) of [B(x₁, y₀), B(x₂, y₀)] is nonzero
    have hminor : ∃ k₁ k₂ : Fin 3,
        B (vecMulVec x₁ y₀) k₁ * B (vecMulVec x₂ y₀) k₂ -
          B (vecMulVec x₁ y₀) k₂ * B (vecMulVec x₂ y₀) k₁ ≠ 0 := by
      by_contra h
      push_neg at h
      have hex_k : ∃ k₁ : Fin 3, B (vecMulVec x₁ y₀) k₁ ≠ 0 := by
        by_contra hk; push_neg at hk; exact hx₁ (funext hk)
      obtain ⟨k₁, hk₁⟩ := hex_k
      apply hx₂
      rw [Submodule.mem_span_singleton]
      refine ⟨B (vecMulVec x₂ y₀) k₁ / B (vecMulVec x₁ y₀) k₁, ?_⟩
      ext k₂
      have h0 := h k₁ k₂
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [hk₁]
      linear_combination -h0
    obtain ⟨k₁, k₂, hdet0⟩ := hminor
    -- pick y₁ with B(e₁, y₁) ≠ 0, so some coordinate k₀ is nonzero
    have hex_y₁ : ∃ y₁, B (vecMulVec e₁ y₁) ≠ 0 := by
      have : (Pi.single (0 : Fin 3) (1 : ℂ) : Fin 3 → ℂ) ∈ P := by rw [hPtop]; trivial
      obtain ⟨y₁, hy₁⟩ := this
      refine ⟨y₁, ?_⟩
      change rowMap B e₁ y₁ ≠ 0
      rw [hy₁]
      intro h0
      exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun h0 (0 : Fin 3))
    obtain ⟨y₁, hy₁⟩ := hex_y₁
    have hex_k₀ : ∃ k₀ : Fin 3, B (vecMulVec e₁ y₁) k₀ ≠ 0 := by
      by_contra hk; push_neg at hk; exact hy₁ (funext hk)
    obtain ⟨k₀, hk₀⟩ := hex_k₀
    let a1 := B (vecMulVec x₁ y₁)
    let a2 := B (vecMulVec x₂ y₁)
    let b1 := B (vecMulVec x₁ y₀)
    let b2 := B (vecMulVec x₂ y₀)
    let d₀ : ℂ := a1 k₁ * a2 k₂ - a1 k₂ * a2 k₁
    let d₁ : ℂ := a1 k₁ * b2 k₂ + b1 k₁ * a2 k₂ - (a1 k₂ * b2 k₁ + b1 k₂ * a2 k₁)
    let d₂ : ℂ := b1 k₁ * b2 k₂ - b1 k₂ * b2 k₁
    obtain ⟨t, ht1, ht2⟩ := exists_t_linear_quad_ne_zero
      (B (vecMulVec e₁ y₁) k₀) (B (vecMulVec e₁ y₀) k₀) d₀ d₁ d₂ hk₀ hdet0
    let f₁ : Fin n → ℂ := y₁ + t • y₀
    have hq_ne : B (vecMulVec e₁ f₁) ≠ 0 := by
      intro h0
      have := congrFun h0 k₀
      simp only [f₁, vecMulVec_add_right, vecMulVec_smul_right, map_add, map_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact ht1 (by linear_combination this)
    have hdet_t : B (vecMulVec x₁ f₁) k₁ * B (vecMulVec x₂ f₁) k₂ -
        B (vecMulVec x₁ f₁) k₂ * B (vecMulVec x₂ f₁) k₁ ≠ 0 := by
      have heq : B (vecMulVec x₁ f₁) k₁ * B (vecMulVec x₂ f₁) k₂ -
          B (vecMulVec x₁ f₁) k₂ * B (vecMulVec x₂ f₁) k₁ = d₀ + d₁ * t + d₂ * t ^ 2 := by
        simp only [f₁, vecMulVec_add_right, vecMulVec_smul_right, map_add, map_smul,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, d₀, d₁, d₂, a1, a2, b1, b2]
        ring
      rw [heq]
      exact ht2
    have hex_e₂ : ∃ e₂ : Fin m → ℂ, B (vecMulVec e₂ f₁) ∉ Submodule.span ℂ ({B (vecMulVec e₁ f₁)} : Set (Fin 3 → ℂ)) := by
      by_contra h; push_neg at h
      obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (h x₁)
      obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp (h x₂)
      apply hdet_t
      rw [← hc₁, ← hc₂]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨e₂, he₂⟩ := hex_e₂
    let Q2 : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {B (vecMulVec e₁ f₁), B (vecMulVec e₂ f₁)}
    have hQ2_dim : Module.finrank ℂ Q2 ≤ 2 := by
      have h1 := finrank_span_le_card (R := ℂ) ({B (vecMulVec e₁ f₁), B (vecMulVec e₂ f₁)} : Set (Fin 3 → ℂ))
      have h2 : ({B (vecMulVec e₁ f₁), B (vecMulVec e₂ f₁)} : Set (Fin 3 → ℂ)).toFinset.card ≤ 2 := by
        calc ({B (vecMulVec e₁ f₁), B (vecMulVec e₂ f₁)} : Set (Fin 3 → ℂ)).toFinset.card
            = ({B (vecMulVec e₁ f₁), B (vecMulVec e₂ f₁)} : Finset (Fin 3 → ℂ)).card := by
              congr 1; ext v; simp
          _ ≤ 2 := Finset.card_le_two
      exact h1.trans h2
    have hex_f₂ : ∃ f₂ : Fin n → ℂ, B (vecMulVec e₁ f₂) ∉ Q2 := by
      by_contra h; push_neg at h
      have hle : P ≤ Q2 := by rintro _ ⟨y, rfl⟩; exact h y
      have h1 := Submodule.finrank_mono hle
      omega
    obtain ⟨f₂, hf₂⟩ := hex_f₂
    refine ⟨e₁, e₂, f₁, f₂, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • B (vecMulVec e₁ f₁) + c 1 • B (vecMulVec e₁ f₂) + c 2 • B (vecMulVec e₂ f₁) = 0 := by
      simpa [Fin.sum_univ_three] using hc
    have hc1 : c 1 = 0 := by
      by_contra h1
      apply hf₂
      have heq : B (vecMulVec e₁ f₂) =
          (-(c 0 / c 1)) • B (vecMulVec e₁ f₁) + (-(c 2 / c 1)) • B (vecMulVec e₂ f₁) := by
        ext k
        have hk := congrFun hsum k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
        field_simp [h1]
        linear_combination hk
      rw [heq]
      exact Q2.add_mem (Q2.smul_mem _ (Submodule.subset_span (by simp)))
        (Q2.smul_mem _ (Submodule.subset_span (by simp)))
    have hc2 : c 2 = 0 := by
      by_contra h2
      rw [hc1, zero_smul, add_zero] at hsum
      apply he₂
      rw [Submodule.mem_span_singleton]
      refine ⟨-(c 0 / c 2), ?_⟩
      ext k
      have hk := congrFun hsum k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
      field_simp [h2]
      linear_combination -hk
    have hc0 : c 0 = 0 := by
      rw [hc1, hc2, zero_smul, zero_smul, add_zero, add_zero] at hsum
      exact (smul_eq_zero.mp hsum).resolve_right hq_ne
    intro i
    fin_cases i <;> assumption

private lemma ker_spanned_of_antidiag_block {m n : ℕ} (C : Mat m n →ₗ[ℂ] (Fin 2 → ℂ))
    (e₁ e₂ : Fin m → ℂ) (f₁ f₂ : Fin n → ℂ)
    (h11 : C (vecMulVec e₁ f₁) = 0)
    (h12 : C (vecMulVec e₁ f₂) = ![1, 0])
    (h21 : C (vecMulVec e₂ f₁) = ![0, 1])
    (h22 : C (vecMulVec e₂ f₂) = 0) :
    LinearMap.ker C ≤ Submodule.span ℂ (rk1Set (LinearMap.ker C)) := by
  let F₀ : Submodule ℂ (Fin n → ℂ) := Submodule.span ℂ {f₁, f₂}
  refine ker_spanned_of_lift_right C F₀ ?_ ?_
  · -- First lift: Xgood spans Fin m → ℂ via quadratic finite difference at w = e₁ + e₂
    let detX : (Fin m → ℂ) → ℂ := fun x =>
      C (vecMulVec x f₁) 0 * C (vecMulVec x f₂) 1 - C (vecMulVec x f₁) 1 * C (vecMulVec x f₂) 0
    have hmem_of_det : ∀ x : Fin m → ℂ, detX x ≠ 0 →
        x ∈ {x | ∀ y : Fin n → ℂ, ∃ z ∈ F₀, C (vecMulVec x z) = C (vecMulVec x y)} := by
      intro x hx y
      let d := C (vecMulVec x y)
      let c₁ : ℂ := (d 0 * C (vecMulVec x f₂) 1 - d 1 * C (vecMulVec x f₂) 0) / detX x
      let c₂ : ℂ := (C (vecMulVec x f₁) 0 * d 1 - C (vecMulVec x f₁) 1 * d 0) / detX x
      refine ⟨c₁ • f₁ + c₂ • f₂,
        F₀.add_mem (F₀.smul_mem c₁ (Submodule.subset_span (by simp)))
          (F₀.smul_mem c₂ (Submodule.subset_span (by simp))), ?_⟩
      ext k
      simp only [vecMulVec_add_right, vecMulVec_smul_right, map_add, map_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, c₁, c₂, d]
      fin_cases k
      · simp only [Fin.zero_eta]; field_simp [hx]; dsimp [detX]; ring
      · simp only [Fin.mk_one]; field_simp [hx]; dsimp [detX]; ring
    let w : Fin m → ℂ := e₁ + e₂
    have hw1 : C (vecMulVec w f₁) = ![0, 1] := by
      simp [w, vecMulVec_add_left, map_add, h11, h21]
    have hw2 : C (vecMulVec w f₂) = ![1, 0] := by
      simp [w, vecMulVec_add_left, map_add, h12, h22]
    have hdet_w : detX w = -1 := by
      simp [detX, hw1, hw2]
    have hw_good : w ∈ Submodule.span ℂ
        {x | ∀ y : Fin n → ℂ, ∃ z ∈ F₀, C (vecMulVec x z) = C (vecMulVec x y)} :=
      Submodule.subset_span (hmem_of_det w (by rw [hdet_w]; norm_num))
    rw [eq_top_iff]
    intro v _
    have hfd : detX v - 2 * detX (v + (1 : ℂ) • w) + detX (v + (2 : ℂ) • w) = -2 := by
      simp only [detX, vecMulVec_add_left, vecMulVec_smul_left, map_add, map_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw1, hw2, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      ring
    by_cases h0 : detX v ≠ 0
    · exact Submodule.subset_span (hmem_of_det v h0)
    · by_cases h1 : detX (v + (1 : ℂ) • w) ≠ 0
      · have hm1 := Submodule.subset_span (R := ℂ) (hmem_of_det (v + (1 : ℂ) • w) h1)
        simpa using Submodule.sub_mem _ hm1 hw_good
      · have h2 : detX (v + (2 : ℂ) • w) ≠ 0 := by
          push_neg at h0 h1
          intro h2
          rw [h0, h1, h2] at hfd
          norm_num at hfd
        have hm2 := Submodule.subset_span (R := ℂ) (hmem_of_det (v + (2 : ℂ) • w) h2)
        have hm2' := Submodule.sub_mem _ hm2 (Submodule.smul_mem _ (2 : ℂ) hw_good)
        simpa using hm2'
  · -- Second lift: within stripRight F₀, decompose via g₁ = f₁ + f₂ and g₂ = f₁ - f₂
    rintro M ⟨hMker, hMstrip⟩
    have hpair : ∀ N ∈ stripRight F₀, ∃ u₁ u₂ : Fin m → ℂ,
        N = vecMulVec u₁ f₁ + vecMulVec u₂ f₂ := by
      intro N hN
      refine Submodule.span_induction ?_ ⟨0, 0, by ext i j; simp [vecMulVec_apply]⟩ ?_ ?_ hN
      · rintro _ ⟨x, y, hy, rfl⟩
        rw [Submodule.mem_span_pair] at hy
        obtain ⟨c₁, c₂, rfl⟩ := hy
        exact ⟨c₁ • x, c₂ • x, by
          rw [vecMulVec_add_right, vecMulVec_smul_right, vecMulVec_smul_right,
            vecMulVec_smul_left, vecMulVec_smul_left]⟩
      · rintro _ _ _ _ ⟨u₁, u₂, rfl⟩ ⟨v₁, v₂, rfl⟩
        exact ⟨u₁ + v₁, u₂ + v₂, by
          rw [vecMulVec_add_left, vecMulVec_add_left]; abel⟩
      · rintro c _ _ ⟨u₁, u₂, rfl⟩
        exact ⟨c • u₁, c • u₂, by
          rw [vecMulVec_smul_left, vecMulVec_smul_left, smul_add]⟩
    obtain ⟨u₁, u₂, rfl⟩ := hpair M hMstrip
    let g₁ : Fin n → ℂ := f₁ + f₂
    let g₂ : Fin n → ℂ := f₁ - f₂
    let v₁ : Fin m → ℂ := (2 : ℂ)⁻¹ • (u₁ + u₂)
    let v₂ : Fin m → ℂ := (2 : ℂ)⁻¹ • (u₁ - u₂)
    have hM_g : vecMulVec u₁ f₁ + vecMulVec u₂ f₂ = vecMulVec v₁ g₁ + vecMulVec v₂ g₂ := by
      ext i j
      simp only [Matrix.add_apply, vecMulVec_apply, v₁, v₂, g₁, g₂, Pi.smul_apply,
        Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      ring
    let d₁ := C (vecMulVec v₁ g₁)
    let d₂ := C (vecMulVec v₂ g₂)
    let w₁ : Fin m → ℂ := d₁ 0 • e₁ + d₁ 1 • e₂
    let w₂ : Fin m → ℂ := (-d₂ 0) • e₁ + d₂ 1 • e₂
    have hw₁C : C (vecMulVec w₁ g₁) = d₁ := by
      ext k
      simp only [w₁, g₁, vecMulVec_add_left, vecMulVec_add_right, vecMulVec_smul_left,
        map_add, map_smul, h11, h12, h21, h22, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      fin_cases k <;> simp
    have hw₂C : C (vecMulVec w₂ g₂) = d₂ := by
      ext k
      simp only [w₂, g₂, vecMulVec_add_left, vecMulVec_sub_right, vecMulVec_smul_left,
        map_add, map_sub, map_smul, h11, h12, h21, h22, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      fin_cases k <;> simp
    have hd_sum : d₁ + d₂ = 0 := by
      have h0 : C (vecMulVec v₁ g₁ + vecMulVec v₂ g₂) = 0 := by
        rw [← hM_g]
        exact LinearMap.mem_ker.mp hMker
      simpa [d₁, d₂, map_add] using h0
    have hrem : vecMulVec w₁ g₁ + vecMulVec w₂ g₂ =
        (d₁ 0 - d₂ 0) • vecMulVec e₁ f₁ + (d₁ 1 - d₂ 1) • vecMulVec e₂ f₂ := by
      have hd0 : d₁ 0 + d₂ 0 = 0 := by simpa using congrFun hd_sum 0
      have hd1 : d₁ 1 + d₂ 1 = 0 := by simpa using congrFun hd_sum 1
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, w₁, w₂, g₁, g₂,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      linear_combination (e₁ i * f₂ j) * hd0 + (e₂ i * f₁ j) * hd1
    have htotal : vecMulVec u₁ f₁ + vecMulVec u₂ f₂ =
        vecMulVec (v₁ - w₁) g₁ + vecMulVec (v₂ - w₂) g₂ +
          ((d₁ 0 - d₂ 0) • vecMulVec e₁ f₁ + (d₁ 1 - d₂ 1) • vecMulVec e₂ f₂) := by
      rw [hM_g, ← hrem, vecMulVec_sub_left, vecMulVec_sub_left]
      abel
    rw [htotal]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.subset_span ⟨by rw [LinearMap.mem_ker, vecMulVec_sub_left, map_sub, hw₁C, sub_self], _, _, rfl⟩
    · exact Submodule.subset_span ⟨by rw [LinearMap.mem_ker, vecMulVec_sub_left, map_sub, hw₂C, sub_self], _, _, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h11, e₁, f₁, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h22, e₂, f₂, rfl⟩)

private lemma upper_bound_codim1 {m n : ℕ} (S : Submodule ℂ (Mat m n))
    (hS : Module.finrank ℂ S + 1 ≤ m * n) :
    ∃ (x : Fin (m * n - 1) → Fin m → ℂ) (y : Fin (m * n - 1) → Fin n → ℂ),
      S ≤ Submodule.span ℂ (Set.range fun r => vecMulVec (x r) (y r)) := by
  obtain ⟨C, hCsurj, hSC⟩ := exists_surj_vanishing S hS
  have hker_dim : Module.finrank ℂ (LinearMap.ker C) = m * n - 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker C
    rw [LinearMap.range_eq_top.mpr hCsurj, finrank_top] at hrn
    have hdom : Module.finrank ℂ (Mat m n) = m * n := by simp [Module.finrank_matrix]
    have hcod : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by simp
    omega
  have hrow : ∀ x : Fin m → ℂ, Module.finrank ℂ (LinearMap.range (rowMap C x)) ≤ 1 := fun x => by
    simpa using Submodule.finrank_le (LinearMap.range (rowMap C x))
  exact coveredBy_of_spanned hSC (ker_spanned_of_row_rank_le_one C hrow) (le_of_eq hker_dim)

private lemma upper_bound_codim3 {m n : ℕ} (S : Submodule ℂ (Mat m n))
    (hS : Module.finrank ℂ S + 3 ≤ m * n) :
    ∃ (x : Fin (m * n - 2) → Fin m → ℂ) (y : Fin (m * n - 2) → Fin n → ℂ),
      S ≤ Submodule.span ℂ (Set.range fun r => vecMulVec (x r) (y r)) := by
  obtain ⟨B, hBsurj, hSB⟩ := exists_surj_vanishing S hS
  let proj2 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun v i => v ⟨i.1, by omega⟩
      map_add' := fun _ _ => by ext i; rfl
      map_smul' := fun _ _ => by ext i; rfl }
  have hproj2_surj : Function.Surjective proj2 := fun v =>
    ⟨![v 0, v 1, 0], by ext i; fin_cases i <;> rfl⟩
  by_cases hrow : ∀ x : Fin m → ℂ, Module.finrank ℂ (LinearMap.range (rowMap B x)) ≤ 1
  · let C := proj2.comp B
    have hCsurj : Function.Surjective C := hproj2_surj.comp hBsurj
    have hSC : S ≤ LinearMap.ker C := fun M hM => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp (hSB hM), map_zero]
    have hker_dim : Module.finrank ℂ (LinearMap.ker C) = m * n - 2 := by
      have hrn := LinearMap.finrank_range_add_finrank_ker C
      rw [LinearMap.range_eq_top.mpr hCsurj, finrank_top] at hrn
      have hdom : Module.finrank ℂ (Mat m n) = m * n := by simp [Module.finrank_matrix]
      have hcod : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by simp
      omega
    have hrowC : ∀ x : Fin m → ℂ, Module.finrank ℂ (LinearMap.range (rowMap C x)) ≤ 1 := fun x => by
      have hcomp : rowMap C x = proj2.comp (rowMap B x) := by ext y; rfl
      rw [hcomp, LinearMap.range_comp]
      exact (Submodule.finrank_map_le proj2 _).trans (hrow x)
    exact coveredBy_of_spanned hSC (ker_spanned_of_row_rank_le_one C hrowC) (le_of_eq hker_dim)
  · by_cases hcol : ∀ y : Fin n → ℂ, Module.finrank ℂ (LinearMap.range (colMap B y)) ≤ 1
    · let C := proj2.comp B
      have hCsurj : Function.Surjective C := hproj2_surj.comp hBsurj
      have hSC : S ≤ LinearMap.ker C := fun M hM => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp (hSB hM), map_zero]
      have hker_dim : Module.finrank ℂ (LinearMap.ker C) = m * n - 2 := by
        have hrn := LinearMap.finrank_range_add_finrank_ker C
        rw [LinearMap.range_eq_top.mpr hCsurj, finrank_top] at hrn
        have hdom : Module.finrank ℂ (Mat m n) = m * n := by simp [Module.finrank_matrix]
        have hcod : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by simp
        omega
      have hcolC : ∀ y : Fin n → ℂ, Module.finrank ℂ (LinearMap.range (colMap C y)) ≤ 1 := fun y => by
        have hcomp : colMap C y = proj2.comp (colMap B y) := by ext x; rfl
        rw [hcomp, LinearMap.range_comp]
        exact (Submodule.finrank_map_le proj2 _).trans (hcol y)
      exact coveredBy_of_spanned hSC (ker_spanned_of_col_rank_le_one C hcolC) (le_of_eq hker_dim)
    · obtain ⟨e₁, e₂, f₁, f₂, hli⟩ := exists_corner B hBsurj hrow hcol
      let v : Fin 3 → Fin 3 → ℂ := ![B (vecMulVec e₁ f₁), B (vecMulVec e₁ f₂), B (vecMulVec e₂ f₁)]
      let b : Module.Basis (Fin 3) ℂ (Fin 3 → ℂ) := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
      let π : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
        { toFun := fun w => ![b.repr w 1, b.repr w 2]
          map_add' := fun w₁ w₂ => by ext i; fin_cases i <;> simp
          map_smul' := fun c w => by ext i; fin_cases i <;> simp }
      have hπ_surj : Function.Surjective π := fun w => by
        refine ⟨w 0 • b 1 + w 1 • b 2, ?_⟩
        ext i; fin_cases i <;> simp [π]
      let C := π.comp B
      have hCsurj : Function.Surjective C := hπ_surj.comp hBsurj
      have hSC : S ≤ LinearMap.ker C := fun M hM => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp (hSB hM), map_zero]
      have hker_dim : Module.finrank ℂ (LinearMap.ker C) = m * n - 2 := by
        have hrn := LinearMap.finrank_range_add_finrank_ker C
        rw [LinearMap.range_eq_top.mpr hCsurj, finrank_top] at hrn
        have hdom : Module.finrank ℂ (Mat m n) = m * n := by simp [Module.finrank_matrix]
        have hcod : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by simp
        omega
      have hC11 : C (vecMulVec e₁ f₁) = 0 := by
        have hb0 : b 0 = B (vecMulVec e₁ f₁) := by simp [b]
        ext i; fin_cases i <;> simp [C, π, ← hb0]
      have hC12 : C (vecMulVec e₁ f₂) = ![1, 0] := by
        have hb1 : b 1 = B (vecMulVec e₁ f₂) := by simp [b]
        ext i; fin_cases i <;> simp [C, π, ← hb1]
      have hC21 : C (vecMulVec e₂ f₁) = ![0, 1] := by
        have hb2 : b 2 = B (vecMulVec e₂ f₁) := by simp [b]
        ext i; fin_cases i <;> simp [C, π, ← hb2]
      let α : ℂ := C (vecMulVec e₂ f₂) 0
      let β : ℂ := C (vecMulVec e₂ f₂) 1
      let e₂' : Fin m → ℂ := e₂ - α • e₁
      let f₂' : Fin n → ℂ := f₂ - β • f₁
      have h12' : C (vecMulVec e₁ f₂') = ![1, 0] := by
        simp [f₂', vecMulVec_sub_right, vecMulVec_smul_right, map_sub, map_smul, hC12, hC11]
      have h21' : C (vecMulVec e₂' f₁) = ![0, 1] := by
        simp [e₂', vecMulVec_sub_left, vecMulVec_smul_left, map_sub, map_smul, hC21, hC11]
      have h22' : C (vecMulVec e₂' f₂') = 0 := by
        ext k
        simp only [e₂', f₂', vecMulVec_sub_left, vecMulVec_sub_right, vecMulVec_smul_left,
          vecMulVec_smul_right, map_sub, map_smul, hC11, hC12, hC21, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, Pi.zero_apply]
        fin_cases k <;> simp [α, β]
      exact coveredBy_of_spanned hSC
        (ker_spanned_of_antidiag_block C e₁ e₂' f₁ f₂' hC11 h12' h21' h22') (le_of_eq hker_dim)

theorem upper_bound : OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.H1 := by
  intro m n u hm hmn hu S hS
  have hu4 : u ≤ 4 := le_trans hu (min_le_left _ _)
  interval_cases u
  · -- u = 0
    have hceil : (0 : ℕ) ⌈/⌉ 2 = 0 := by decide
    rw [hceil, Nat.sub_zero]
    have htop_dim : Module.finrank ℂ (⊤ : Submodule ℂ (Mat m n)) ≤ m * n := by
      simp [Module.finrank_matrix]
    exact coveredBy_of_spanned le_top (top_spanned_rk1 m n) htop_dim
  · -- u = 1
    have hceil : (1 : ℕ) ⌈/⌉ 2 = 1 := by decide
    rw [hceil]
    exact upper_bound_codim1 S hS
  · -- u = 2
    have hceil : (2 : ℕ) ⌈/⌉ 2 = 1 := by decide
    rw [hceil]
    have hS' : Module.finrank ℂ S + 1 ≤ m * n := le_trans (Nat.add_le_add_left (by decide) _) hS
    exact upper_bound_codim1 S hS'
  · -- u = 3
    have hceil : (3 : ℕ) ⌈/⌉ 2 = 2 := by decide
    rw [hceil]
    exact upper_bound_codim3 S hS
  · -- u = 4
    have hceil : (4 : ℕ) ⌈/⌉ 2 = 2 := by decide
    rw [hceil]
    have hS' : Module.finrank ℂ S + 3 ≤ m * n := le_trans (Nat.add_le_add_left (by decide) _) hS
    exact upper_bound_codim3 S hS'

end MaxRankLeMinH1

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.H1 :=
  MaxRankLeMinH1.upper_bound
