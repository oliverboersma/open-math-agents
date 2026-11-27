import FormalConjectures.Arxiv.«0805.3777».TensorRank
import Mathlib

/-! # Maximal rank of m x n x (mn - u) tensors for u <= min 4 m -/

namespace OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1

open Arxiv.«0805.3777»

/-- Upper bound: a subspace of `m × n` matrices of codimension at least `u` is contained in the
span of `mn - ⌈u/2⌉` rank-one matrices. -/
def H1 : Prop :=
  ∀ (m n u : ℕ), 3 ≤ m → m ≤ n → u ≤ min 4 m →
    ∀ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S + u ≤ m * n →
      ∃ (x : Fin (m * n - u ⌈/⌉ 2) → Fin m → ℂ) (y : Fin (m * n - u ⌈/⌉ 2) → Fin n → ℂ),
        S ≤ Submodule.span ℂ (Set.range fun r => Matrix.vecMulVec (x r) (y r))

/-- Lower bound: some family of `mn - u` matrices of size `m × n` is not contained in the span of
fewer than `mn - ⌈u/2⌉` rank-one matrices. -/
def H2 : Prop :=
  ∀ (m n u : ℕ), 3 ≤ m → m ≤ n → u ≤ min 4 m →
    ∃ M : Fin (m * n - u) → Matrix (Fin m) (Fin n) ℂ,
      ∀ (R : ℕ) (x : Fin R → Fin m → ℂ) (y : Fin R → Fin n → ℂ),
        (∀ c, M c ∈ Submodule.span ℂ (Set.range fun r => Matrix.vecMulVec (x r) (y r))) →
          m * n - u ⌈/⌉ 2 ≤ R

section Bridge

variable {m n k : ℕ}

theorem ix_surjective (t : HolorIndex [m, n, k]) :
    ∃ (i : Fin m) (j : Fin n) (c : Fin k), t = ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩ := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

theorem holor_ext {T T' : Holor ℂ [m, n, k]}
    (h : ∀ (i : Fin m) (j : Fin n) (c : Fin k), T ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩ = T' ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩) : T = T' := by
  funext t
  obtain ⟨i, j, c, rfl⟩ := ix_surjective t
  exact h i j c

theorem holor_sum_apply {ds : List ℕ} {ι : Type} (s : Finset ι) (f : ι → Holor ℂ ds)
    (t : HolorIndex ds) : (∑ l ∈ s, f l) t = ∑ l ∈ s, f l t := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

/-- Every rank-one holor `u ⊗ v ⊗ w` exists as a holor of CP rank at most one. -/
theorem exists_r1 (u : Fin m → ℂ) (v : Fin n → ℂ) (w : Fin k → ℂ) :
    ∃ x : Holor ℂ [m, n, k], Holor.CPRankMax1 x ∧
      ∀ (i : Fin m) (j : Fin n) (c : Fin k), x ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩ = u i * v j * w c := by
  let x : Holor ℂ [m, n, k] := Holor.mul (fun t : HolorIndex [m] => u ⟨t.1.headI, headI_lt t⟩)
    (Holor.mul (fun t : HolorIndex [n] => v ⟨t.1.headI, headI_lt t⟩)
      (Holor.mul (fun t : HolorIndex [k] => w ⟨t.1.headI, headI_lt t⟩)
        (fun _ : HolorIndex [] => (1 : ℂ))))
  have hx : Holor.CPRankMax1 x := .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))
  refine ⟨x, hx, fun i j c => ?_⟩
  show u i * (v j * (w c * 1)) = _
  ring

theorem cprankMax1_cons {α : Type} [Mul α] {d : ℕ} {ds : List ℕ} {x : Holor α (d :: ds)}
    (h : Holor.CPRankMax1 x) :
    ∃ (u : Holor α [d]) (y : Holor α ds), Holor.CPRankMax1 y ∧ x = Holor.mul u y := by
  cases h with
  | cons u y hy => exact ⟨u, y, hy, rfl⟩

theorem cprankMax1_entries {x : Holor ℂ [m, n, k]} (h : Holor.CPRankMax1 x) :
    ∃ (u : Fin m → ℂ) (v : Fin n → ℂ) (w : Fin k → ℂ),
      ∀ (i : Fin m) (j : Fin n) (c : Fin k), x ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩ = u i * v j * w c := by
  obtain ⟨u₁, y₁, h₁, rfl⟩ := cprankMax1_cons h
  obtain ⟨u₂, y₂, h₂, rfl⟩ := cprankMax1_cons h₁
  obtain ⟨u₃, y₃, -, rfl⟩ := cprankMax1_cons h₂
  refine ⟨fun i => u₁ ⟨[i.1], .cons i.2 .nil⟩, fun j => u₂ ⟨[j.1], .cons j.2 .nil⟩,
    fun c => u₃ ⟨[c.1], .cons c.2 .nil⟩ * y₃ ⟨[], .nil⟩, fun i j c => ?_⟩
  show u₁ ⟨[i.1], .cons i.2 .nil⟩ * (u₂ ⟨[j.1], .cons j.2 .nil⟩ *
    (u₃ ⟨[c.1], .cons c.2 .nil⟩ * y₃ ⟨[], .nil⟩)) = _
  ring

/-- A holor of CP rank at most `r` is a sum of `r` holors of rank at most one. -/
theorem exists_sum_of_cprankMax {α : Type} [Mul α] [AddCommMonoid α] {ds : List ℕ} {r : ℕ}
    {x : Holor α ds} (h : Holor.CPRankMax r x) :
    ∃ f : Fin r → Holor α ds, (∀ l, Holor.CPRankMax1 (f l)) ∧ x = ∑ l, f l := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun l => l.elim0, by simp⟩
  | succ n x y hx _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    refine ⟨Fin.cons x f, fun l => Fin.cases hx hf l, ?_⟩
    rw [Fin.sum_univ_succ]
    rfl

theorem cprankMax_cprank {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x :=
  @Nat.find_spec (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {r : ℕ}
    (h : Holor.CPRankMax r x) : x.cprank ≤ r :=
  @Nat.find_min' (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ r h

theorem cprank_le_of_sum {ι : Type} [Fintype ι] (T : Holor ℂ [m, n, k]) (u : ι → Fin m → ℂ)
    (v : ι → Fin n → ℂ) (w : ι → Fin k → ℂ)
    (h : ∀ (i : Fin m) (j : Fin n) (c : Fin k), T ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩ = ∑ l, u l i * v l j * w l c) :
    T.cprank ≤ Fintype.card ι := by
  choose X hX1 hX using fun l => exists_r1 (u l) (v l) (w l)
  have hT : T = ∑ l, X l := by
    refine holor_ext fun i j c => ?_
    erw [holor_sum_apply, h]
    exact Finset.sum_congr rfl fun l _ => (hX l i j c).symm
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ X fun l _ => Holor.cprankMax_1 (hX1 l)
  rw [Finset.card_univ, mul_one, ← hT] at hr
  exact cprank_le_of_cprankMax hr

theorem exists_sum_of_cprank (T : Holor ℂ [m, n, k]) :
    ∃ (u : Fin T.cprank → Fin m → ℂ) (v : Fin T.cprank → Fin n → ℂ)
      (w : Fin T.cprank → Fin k → ℂ),
        ∀ (i : Fin m) (j : Fin n) (c : Fin k), T ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩ = ∑ l, u l i * v l j * w l c := by
  obtain ⟨f, hf, hT⟩ := exists_sum_of_cprankMax (cprankMax_cprank T)
  choose u v w huvw using fun l => cprankMax1_entries (hf l)
  refine ⟨u, v, w, fun i j c => ?_⟩
  conv_lhs => rw [hT]
  erw [holor_sum_apply]
  exact Finset.sum_congr rfl fun l _ => huvw l i j c

/-- If every slice lies in the span of `R` rank-one matrices, the rank is at most `R`. -/
theorem cprank_le_of_span (T : Holor ℂ [m, n, k]) {R : ℕ} (x : Fin R → Fin m → ℂ)
    (y : Fin R → Fin n → ℂ)
    (h : ∀ c : Fin k, (Matrix.of fun (i : Fin m) (j : Fin n) => T ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩) ∈
      Submodule.span ℂ (Set.range fun r => Matrix.vecMulVec (x r) (y r))) :
    T.cprank ≤ R := by
  choose f hf using fun c => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (h c)
  have := cprank_le_of_sum T x y (fun l c => f c l) fun i j c => by
    have hij := congrFun (congrFun (hf c) i) j
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul] at hij
    rw [← hij]
    exact Finset.sum_congr rfl fun l _ => by ring
  simpa using this

/-- The slices of a holor lie in the span of `cprank` rank-one matrices. -/
theorem exists_span_of_cprank (T : Holor ℂ [m, n, k]) :
    ∃ (x : Fin T.cprank → Fin m → ℂ) (y : Fin T.cprank → Fin n → ℂ), ∀ c : Fin k,
      (Matrix.of fun (i : Fin m) (j : Fin n) => T ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩) ∈
        Submodule.span ℂ (Set.range fun r => Matrix.vecMulVec (x r) (y r)) := by
  obtain ⟨u, v, w, h⟩ := exists_sum_of_cprank T
  refine ⟨u, v, fun c => (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨fun l => w l c, ?_⟩⟩
  ext i j
  simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, h]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Any family of matrices is the family of slices of some holor. -/
theorem exists_ofSlices (M : Fin k → Matrix (Fin m) (Fin n) ℂ) :
    ∃ T : Holor ℂ [m, n, k], ∀ c : Fin k, (Matrix.of fun (i : Fin m) (j : Fin n) => T ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩) = M c :=
  ⟨fun t => M ⟨t.1.tail.tail.headI, by
      obtain ⟨l, h⟩ := t
      cases h with
      | cons _ h => cases h with
        | cons _ h => cases h with
          | cons hc _ => exact hc⟩
    ⟨t.1.headI, headI_lt t⟩ ⟨t.1.tail.headI, by
      obtain ⟨l, h⟩ := t
      cases h with
      | cons _ h => cases h with
        | cons hb _ => exact hb⟩, fun c => rfl⟩

end Bridge

theorem main : H1 → H2 → type_of% @Arxiv.«0805.3777».isMaxRank_of_le_min := by
  intro h1 h2 m n u hm hmn hu
  have hu' : u ≤ m * n := by
    have : m ≤ m * n := Nat.le_mul_of_pos_right m (by omega)
    have : u ≤ m := le_trans hu (min_le_right _ _)
    omega
  -- Every tensor of this format has rank at most `mn - ⌈u/2⌉`.
  have upper : ∀ T : Holor ℂ [m, n, m * n - u], T.cprank ≤ m * n - u ⌈/⌉ 2 := by
    intro T
    let sl : Fin (m * n - u) → Matrix (Fin m) (Fin n) ℂ := fun c =>
      Matrix.of fun (i : Fin m) (j : Fin n) => T ⟨[i.1, j.1, c.1], .cons i.2 (.cons j.2 (.cons c.2 .nil))⟩
    set S := Submodule.span ℂ (Set.range sl)
    have hS : Module.finrank ℂ S + u ≤ m * n := by
      have h0 : Module.finrank ℂ S ≤ m * n - u := by
        have := finrank_range_le_card (R := ℂ) (b := sl)
        simpa [Set.finrank, S] using this
      omega
    obtain ⟨x, y, hxy⟩ := h1 m n u hm hmn hu S hS
    exact cprank_le_of_span T x y fun c => hxy (Submodule.subset_span ⟨c, rfl⟩)
  obtain ⟨M, hM⟩ := h2 m n u hm hmn hu
  obtain ⟨T₀, hT₀⟩ := exists_ofSlices M
  refine ⟨⟨T₀, le_antisymm (upper _) ?_⟩, ?_⟩
  · obtain ⟨x, y, hxy⟩ := exists_span_of_cprank T₀
    exact hM _ x y fun c => hT₀ c ▸ hxy c
  · rintro _ ⟨T, rfl⟩
    exact upper T

end OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1

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

private theorem h1_proof : OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.H1 :=
  MaxRankLeMinH1.upper_bound

namespace LeMinLower

open Matrix

theorem finrank_matrix_eq (m n : ℕ) :
    Module.finrank ℂ (Matrix (Fin m) (Fin n) ℂ) = m * n := by
  simp [Module.finrank_matrix]

theorem finrank_span_range_le {m n p : ℕ} (M : Fin p → Matrix (Fin m) (Fin n) ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range M)) ≤ p := by
  have h := finrank_range_le_card (R := ℂ) M
  rwa [Fintype.card_fin] at h

theorem fin4_ext {v w : Fin 4 → ℂ} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2)
    (h3 : v 3 = w 3) : v = w := by
  funext k
  fin_cases k
  exacts [h0, h1, h2, h3]

/-- The algebraic heart: a rank-one matrix whose image under `θ` lies on the line `ℂ λ` is killed
by a functional that depends only on `λ`. -/
theorem key (lam : Fin 4 → ℂ) : ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧
    ∀ (x0 x1 y0 y1 y2 y3 t : ℂ), x1 * y0 - x0 * y1 = t * lam 0 → x1 * y1 = t * lam 1 →
      x1 * y2 - x0 * y3 = t * lam 2 → x1 * y3 = t * lam 3 → x0 * (α * y1 + β * y3) = 0 := by
  by_cases hA : lam 1 ≠ 0 ∨ lam 3 ≠ 0
  · refine ⟨lam 3, -lam 1, ?_, ?_⟩
    · rcases hA with h | h
      · exact Or.inr (neg_ne_zero.mpr h)
      · exact Or.inl h
    · intro x0 x1 y0 y1 y2 y3 t h0 h1 h2 h3
      have hx : x1 * (lam 3 * y1 + -lam 1 * y3) = 0 := by
        linear_combination lam 3 * h1 - lam 1 * h3
      rcases mul_eq_zero.mp hx with hx1 | hx2
      · have ht : t = 0 := by
          rcases hA with h | h
          · have h4 : t * lam 1 = 0 := by rw [← h1, hx1, zero_mul]
            exact (mul_eq_zero.mp h4).resolve_right h
          · have h4 : t * lam 3 = 0 := by rw [← h3, hx1, zero_mul]
            exact (mul_eq_zero.mp h4).resolve_right h
        rw [hx1, ht] at h0 h2
        linear_combination (-lam 3) * h0 + lam 1 * h2
      · rw [hx2, mul_zero]
  · have hl1 : lam 1 = 0 := not_not.mp fun h => hA (Or.inl h)
    have hl3 : lam 3 = 0 := not_not.mp fun h => hA (Or.inr h)
    by_cases hB : lam 0 ≠ 0 ∨ lam 2 ≠ 0
    · refine ⟨lam 2, -lam 0, ?_, ?_⟩
      · rcases hB with h | h
        · exact Or.inr (neg_ne_zero.mpr h)
        · exact Or.inl h
      · intro x0 x1 y0 y1 y2 y3 t h0 h1 h2 h3
        by_cases hx1 : x1 = 0
        · rw [hx1] at h0 h2
          linear_combination (-lam 2) * h0 + lam 0 * h2
        · have hy1 : y1 = 0 := by
            have h4 : x1 * y1 = 0 := by rw [h1, hl1, mul_zero]
            exact (mul_eq_zero.mp h4).resolve_left hx1
          have hy3 : y3 = 0 := by
            have h4 : x1 * y3 = 0 := by rw [h3, hl3, mul_zero]
            exact (mul_eq_zero.mp h4).resolve_left hx1
          rw [hy1, hy3]
          ring
    · have hl0 : lam 0 = 0 := not_not.mp fun h => hB (Or.inl h)
      refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      intro x0 x1 y0 y1 y2 y3 t h0 h1 _ _
      by_cases hx1 : x1 = 0
      · rw [hx1] at h0
        linear_combination (-1 : ℂ) * h0 - t * hl0
      · have hy1 : y1 = 0 := by
          have h4 : x1 * y1 = 0 := by rw [h1, hl1, mul_zero]
          exact (mul_eq_zero.mp h4).resolve_left hx1
        rw [hy1]
        ring

/-- The common kernel of the four functionals is covered by no `m n - 3` rank-one matrices. -/
theorem block {m n : ℕ} (hm : 2 ≤ m) (hn : 4 ≤ n)
    (f : Fin 4 → Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (f0 : ∀ A, f 0 A = A ⟨1, by omega⟩ ⟨0, by omega⟩ - A ⟨0, by omega⟩ ⟨1, by omega⟩)
    (f1 : ∀ A, f 1 A = A ⟨1, by omega⟩ ⟨1, by omega⟩)
    (f2 : ∀ A, f 2 A = A ⟨1, by omega⟩ ⟨2, by omega⟩ - A ⟨0, by omega⟩ ⟨3, by omega⟩)
    (f3 : ∀ A, f 3 A = A ⟨1, by omega⟩ ⟨3, by omega⟩) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.pi f)) + 4 = m * n ∧
    ∀ (x : Fin (m * n - 3) → Fin m → ℂ) (y : Fin (m * n - 3) → Fin n → ℂ),
      ¬ LinearMap.ker (LinearMap.pi f) ≤
        Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have hfin : Module.finrank ℂ (LinearMap.ker (LinearMap.pi f)) + 4 = m * n := by
    have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi f)
    have hs : LinearMap.range (LinearMap.pi f) = ⊤ := by
      refine LinearMap.range_eq_top.mpr fun v => ?_
      obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin n) ℂ, B = Matrix.of fun i j =>
          if i.1 = 1 ∧ j.1 = 0 then v 0 else if i.1 = 1 ∧ j.1 = 1 then v 1
          else if i.1 = 1 ∧ j.1 = 2 then v 2 else if i.1 = 1 ∧ j.1 = 3 then v 3 else 0 :=
        ⟨_, rfl⟩
      refine ⟨B, fin4_ext ((f0 B).trans ?_) ((f1 B).trans ?_) ((f2 B).trans ?_)
        ((f3 B).trans ?_)⟩ <;> (rw [hB]; simp)
    rw [hs, finrank_top, finrank_matrix_eq] at h
    have h1 : Module.finrank ℂ (Fin 4 → ℂ) = 4 := Module.finrank_fin_fun ℂ
    omega
  refine ⟨hfin, fun x y hle => ?_⟩
  have hcard := finrank_span_range_le fun l => vecMulVec (x l) (y l)
  -- the image of the span under `θ` has dimension at most one
  have hdim : Module.finrank ℂ ((Submodule.span ℂ
      (Set.range fun l => vecMulVec (x l) (y l))).map (LinearMap.pi f)) ≤ 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((LinearMap.pi f).domRestrict
      (Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
      (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h
    omega
  obtain ⟨⟨lam, _⟩, hlam⟩ := finrank_le_one_iff.mp hdim
  obtain ⟨α, β, hαβ, hkey⟩ := key lam
  -- the functional `A ↦ α A_01 + β A_03` vanishes on the span
  have hC : Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) ≤
      LinearMap.ker (α • Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n)
        + β • Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨3, by omega⟩ : Fin n)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    have hmem : LinearMap.pi f (vecMulVec (x l) (y l)) ∈ (Submodule.span ℂ
        (Set.range fun l => vecMulVec (x l) (y l))).map (LinearMap.pi f) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
    obtain ⟨c, hc⟩ := hlam ⟨_, hmem⟩
    have hc' : c • lam = LinearMap.pi f (vecMulVec (x l) (y l)) := congrArg Subtype.val hc
    have e0 : c * lam 0 = f 0 (vecMulVec (x l) (y l)) := congrFun hc' 0
    have e1 : c * lam 1 = f 1 (vecMulVec (x l) (y l)) := congrFun hc' 1
    have e2 : c * lam 2 = f 2 (vecMulVec (x l) (y l)) := congrFun hc' 2
    have e3 : c * lam 3 = f 3 (vecMulVec (x l) (y l)) := congrFun hc' 3
    rw [f0, vecMulVec_apply, vecMulVec_apply] at e0
    rw [f1, vecMulVec_apply] at e1
    rw [f2, vecMulVec_apply, vecMulVec_apply] at e2
    rw [f3, vecMulVec_apply] at e3
    have hk := hkey _ _ _ _ _ _ c e0.symm e1.symm e2.symm e3.symm
    show vecMulVec (x l) (y l) ∈ LinearMap.ker _
    refine LinearMap.mem_ker.mpr ?_
    show α * vecMulVec (x l) (y l) ⟨0, by omega⟩ ⟨1, by omega⟩
      + β * vecMulVec (x l) (y l) ⟨0, by omega⟩ ⟨3, by omega⟩ = 0
    rw [vecMulVec_apply, vecMulVec_apply]
    linear_combination hk
  -- an element of the kernel on which the functional does not vanish
  obtain ⟨a', b', hab'⟩ : ∃ a' b' : ℂ, α * a' + β * b' ≠ 0 := by
    rcases hαβ with h | h
    · exact ⟨1, 0, by rwa [mul_one, mul_zero, add_zero]⟩
    · exact ⟨0, 1, by rwa [mul_zero, mul_one, zero_add]⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin m) (Fin n) ℂ, A = Matrix.of fun i j =>
      if (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 0) then a'
      else if (i.1 = 0 ∧ j.1 = 3) ∨ (i.1 = 1 ∧ j.1 = 2) then b' else 0 := ⟨_, rfl⟩
  have hker : A ∈ LinearMap.ker (LinearMap.pi f) := by
    refine LinearMap.mem_ker.mpr (fin4_ext ((f0 A).trans ?_) ((f1 A).trans ?_)
      ((f2 A).trans ?_) ((f3 A).trans ?_)) <;> (rw [hA]; simp)
  have h0 : α * A ⟨0, by omega⟩ ⟨1, by omega⟩ + β * A ⟨0, by omega⟩ ⟨3, by omega⟩ = 0 :=
    LinearMap.mem_ker.mp (hC (hle hker))
  refine hab' ?_
  rw [hA] at h0
  simpa using h0

/-- The statement of the hypothesis. -/
theorem lower {m n : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) :
    ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ),
      Module.finrank ℂ S + 4 ≤ m * n ∧
      ∀ (x : Fin (m * n - 3) → Fin m → ℂ) (y : Fin (m * n - 3) → Fin n → ℂ),
        ¬ S ≤ Submodule.span ℂ (Set.range fun l => Matrix.vecMulVec (x l) (y l)) := by
  have h := block (m := m) (n := n) (by omega) (by omega)
    ![Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n) -
        Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨2, by omega⟩ : Fin n) -
        Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨3, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨3, by omega⟩ : Fin n)]
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  exact ⟨_, le_of_eq h.1, h.2⟩

/-- Enlarging a family of rank-one matrices by zero matrices. -/
theorem pad_cover {m n c r : ℕ} (hcr : c ≤ r) (x : Fin c → Fin m → ℂ) (y : Fin c → Fin n → ℂ) :
    ∃ (x' : Fin r → Fin m → ℂ) (y' : Fin r → Fin n → ℂ),
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) ≤
        Submodule.span ℂ (Set.range fun l => vecMulVec (x' l) (y' l)) := by
  refine ⟨fun l => if h : l.1 < c then x ⟨l.1, h⟩ else 0,
    fun l => if h : l.1 < c then y ⟨l.1, h⟩ else 0, Submodule.span_mono ?_⟩
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨i.1, lt_of_lt_of_le i.2 hcr⟩, ?_⟩
  simp only [dif_pos i.2]

/-- A subspace of dimension at most `p` is the span of `p` matrices. -/
theorem exists_fin_span {m n p : ℕ} (S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (hS : Module.finrank ℂ S ≤ p) :
    ∃ f : Fin p → Matrix (Fin m) (Fin n) ℂ, Submodule.span ℂ (Set.range f) = S := by
  obtain ⟨g, hg, hspan, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ))
  have hd : Module.finrank ℂ (Submodule.span ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ))) ≤ p := by
    rw [Submodule.span_eq]
    exact hS
  refine ⟨fun l => if h : l.1 < Module.finrank ℂ
      (Submodule.span ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ))) then g ⟨l.1, h⟩ else 0, ?_⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    by_cases h : l.1 < Module.finrank ℂ (Submodule.span ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ)))
    · simp only [dif_pos h]
      exact hg _
    · simp only [dif_neg h]
      exact S.zero_mem
  · refine le_trans (le_of_eq ((Submodule.span_eq S).symm.trans hspan.symm))
      (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i.1, lt_of_lt_of_le i.2 hd⟩, ?_⟩
    simp only [dif_pos i.2]

theorem no_cover_top {m n r : ℕ} (hr : r < m * n) (x : Fin r → Fin m → ℂ)
    (y : Fin r → Fin n → ℂ) :
    ¬ (⊤ : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ)) ≤
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  intro hle
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_range_le fun l => vecMulVec (x l) (y l)
  rw [finrank_top, finrank_matrix_eq] at h1
  omega

/-- The common kernel of `u` independent functionals, each rank-one matrix of which has a
vanishing `(i₀, j₀)` entry while some element has not, is covered by no `m n - u` rank-one
matrices. -/
theorem no_cover_ker {m n u : ℕ} (i₀ : Fin m) (j₀ : Fin n)
    (f : Fin u → Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hsurj : ∀ v : Fin u → ℂ, ∃ A : Matrix (Fin m) (Fin n) ℂ, ∀ k, f k A = v k)
    (hr1 : ∀ (x : Fin m → ℂ) (y : Fin n → ℂ),
      (∀ k, f k (vecMulVec x y) = 0) → x i₀ * y j₀ = 0)
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : ∀ k, f k A = 0) (hA0 : A i₀ j₀ ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.pi f)) + u = m * n ∧
    ∀ (x : Fin (m * n - u) → Fin m → ℂ) (y : Fin (m * n - u) → Fin n → ℂ),
      ¬ LinearMap.ker (LinearMap.pi f) ≤
        Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have hfin : Module.finrank ℂ (LinearMap.ker (LinearMap.pi f)) + u = m * n := by
    have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi f)
    have hs : LinearMap.range (LinearMap.pi f) = ⊤ := by
      refine LinearMap.range_eq_top.mpr fun v => ?_
      obtain ⟨B, hB⟩ := hsurj v
      exact ⟨B, funext hB⟩
    rw [hs, finrank_top, finrank_matrix_eq] at h
    have h1 : Module.finrank ℂ (Fin u → ℂ) = u := Module.finrank_fin_fun ℂ
    omega
  refine ⟨hfin, fun x y hle => ?_⟩
  have hcard := finrank_span_range_le fun l => vecMulVec (x l) (y l)
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hall : Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) ≤
      LinearMap.ker (Matrix.entryLinearMap ℂ ℂ i₀ j₀) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    have hk : vecMulVec (x l) (y l) ∈ LinearMap.ker (LinearMap.pi f) := by
      rw [heq]
      exact Submodule.subset_span ⟨l, rfl⟩
    have h0 := LinearMap.mem_ker.mp hk
    have h := hr1 (x l) (y l) fun k => congrFun h0 k
    show vecMulVec (x l) (y l) ∈ LinearMap.ker (Matrix.entryLinearMap ℂ ℂ i₀ j₀)
    refine LinearMap.mem_ker.mpr ?_
    rw [Matrix.entryLinearMap_apply, vecMulVec_apply]
    exact h
  exact hA0 (LinearMap.mem_ker.mp (hall (hle (LinearMap.mem_ker.mpr (funext hA)))))

theorem no_cover_two {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S + 2 = m * n ∧
      ∀ (x : Fin (m * n - 2) → Fin m → ℂ) (y : Fin (m * n - 2) → Fin n → ℂ),
        ¬ S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have h := no_cover_ker (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n)
    ![Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n) +
        Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n)]
    ?_ ?_
    (Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then 1 else if i.1 = 1 ∧ j.1 = 1 then -1 else 0)
    ?_ ?_
  · exact ⟨_, h⟩
  · intro v
    refine ⟨Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then v 0
      else if i.1 = 0 ∧ j.1 = 1 then v 1 else 0, fun k => ?_⟩
    fin_cases k <;> simp
  · intro x y h
    have h0 : x ⟨0, by omega⟩ * y ⟨0, by omega⟩ + x ⟨1, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 0
    have h1 : x ⟨0, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 1
    refine mul_self_eq_zero.mp ?_
    linear_combination (x ⟨0, by omega⟩ * y ⟨0, by omega⟩) * h0
      - (x ⟨1, by omega⟩ * y ⟨0, by omega⟩) * h1
  · intro k
    fin_cases k <;> simp
  · simp

theorem no_cover_three {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S + 3 = m * n ∧
      ∀ (x : Fin (m * n - 3) → Fin m → ℂ) (y : Fin (m * n - 3) → Fin n → ℂ),
        ¬ S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have h := no_cover_ker (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n)
    ![Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n) +
        Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨2, by omega⟩ : Fin m) (⟨2, by omega⟩ : Fin n)]
    ?_ ?_
    (Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then 1 else if i.1 = 1 ∧ j.1 = 1 then -1 else 0)
    ?_ ?_
  · exact ⟨_, h⟩
  · intro v
    refine ⟨Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then v 0
      else if i.1 = 0 ∧ j.1 = 1 then v 1 else if i.1 = 2 ∧ j.1 = 2 then v 2 else 0, fun k => ?_⟩
    fin_cases k <;> simp
  · intro x y h
    have h0 : x ⟨0, by omega⟩ * y ⟨0, by omega⟩ + x ⟨1, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 0
    have h1 : x ⟨0, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 1
    refine mul_self_eq_zero.mp ?_
    linear_combination (x ⟨0, by omega⟩ * y ⟨0, by omega⟩) * h0
      - (x ⟨1, by omega⟩ * y ⟨0, by omega⟩) * h1
  · intro k
    fin_cases k <;> simp
  · simp

/-- The lower bounds on the level of slice spaces. -/
theorem lower_nocover {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ 4)
    (hum : u ≤ m) (r : ℕ) (hr : r + (u + 1) / 2 + 1 = m * n) :
    ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S + u ≤ m * n ∧
      ∀ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ),
        ¬ S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have hmn9 : 9 ≤ m * n := by nlinarith
  rcases Nat.lt_or_ge u 1 with h0 | h0
  · refine ⟨⊤, ?_, fun x y => no_cover_top (by omega) x y⟩
    rw [finrank_top, finrank_matrix_eq]
    omega
  rcases Nat.lt_or_ge u 3 with h3 | h3
  · obtain ⟨S, hS, hno⟩ := no_cover_two (m := m) (n := n) (by omega) (by omega)
    obtain rfl : r = m * n - 2 := by omega
    exact ⟨S, by omega, hno⟩
  rcases Nat.lt_or_ge u 4 with h4 | h4
  · obtain ⟨S, hS, hno⟩ := no_cover_three (m := m) (n := n) hm (by omega)
    obtain rfl : r = m * n - 3 := by omega
    exact ⟨S, by omega, hno⟩
  · obtain ⟨S, hS, hno⟩ := lower (m := m) (n := n) (by omega) hmn
    obtain rfl : r = m * n - 3 := by omega
    exact ⟨S, by omega, hno⟩

/-- The statement of the hypothesis. -/
theorem lower_all {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ min 4 m) :
    ∃ M : Fin (m * n - u) → Matrix (Fin m) (Fin n) ℂ,
      ∀ (R : ℕ) (x : Fin R → Fin m → ℂ) (y : Fin R → Fin n → ℂ),
        (∀ c, M c ∈ Submodule.span ℂ (Set.range fun r => Matrix.vecMulVec (x r) (y r))) →
          m * n - u ⌈/⌉ 2 ≤ R := by
  have hu4 : u ≤ 4 := le_trans hu (min_le_left _ _)
  have hum : u ≤ m := le_trans hu (min_le_right _ _)
  have hmn9 : 9 ≤ m * n := by nlinarith
  have hc : u ⌈/⌉ 2 = (u + 2 - 1) / 2 := Nat.ceilDiv_eq_add_pred_div u 2
  obtain ⟨S, hS, hno⟩ := lower_nocover hm hmn hu4 hum (m * n - u ⌈/⌉ 2 - 1) (by omega)
  obtain ⟨f, hf⟩ := exists_fin_span S (p := m * n - u) (by omega)
  refine ⟨f, fun R x y hxy => ?_⟩
  by_contra hlt
  obtain ⟨x', y', hpad⟩ := pad_cover (r := m * n - u ⌈/⌉ 2 - 1) (by omega) x y
  refine hno x' y' (le_trans ?_ hpad)
  rw [← hf]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨c, rfl⟩
  exact hxy c

end LeMinLower

private theorem h2_proof : OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.H2 := by
  intro m n u hm hmn hu
  exact LeMinLower.lower_all hm hmn hu

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isMaxRank_of_le_min :=
  OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.main h1_proof h2_proof
