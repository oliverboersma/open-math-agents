import FormalConjectures.Arxiv.«0805.3777».TensorRank
import Mathlib

/-!
A tensor of format `m × n × k` is the same as `k` matrices of size `m × n` (its slices along the
last mode), and its rank is the least number of rank-one matrices `x yᵀ` whose span contains every
slice. This file proves that translation and reduces the statement to two facts about subspaces
of `m × n` matrices:

* `H1` (upper bound): every subspace of codimension at least `u` lies in the span of
  `mn - ⌈u/2⌉` rank-one matrices;
* `H2` (lower bound): some family of `mn - u` matrices needs at least `mn - ⌈u/2⌉` rank-one
  matrices to span a space containing it.

Credit: @GamingPuzzled
-/

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
