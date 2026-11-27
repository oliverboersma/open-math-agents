import OMAReductions.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1

-- Step Arxiv.0805.3777.isMaxRank_of_le_min.R1.H2: hypothesis H2 of reduction Arxiv.0805.3777.isMaxRank_of_le_min.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Everything in this file is new; nothing is taken from other proofs. (The statement and the
-- reduction it belongs to are by GamingPuzzled, PR #4243.)

/-!
# The lower bound: `m × n × (m n - u)` tensors of rank `m n - ⌈u / 2⌉` for `u ≤ min 4 m`

Hypothesis H2 of the reduction: for `3 ≤ m ≤ n` and `u ≤ min 4 m` there are `m n - u` matrices of
size `m × n` that lie in no span of fewer than `m n - ⌈u / 2⌉` rank-one matrices.

The family is a spanning family of a subspace `S` of codimension `u`, and the claim is that `S`
lies in no span of `m n - ⌈u / 2⌉ - 1` rank-one matrices (`lower_nocover`).

* `u = 0`: `S` is the whole space, of dimension `m n`.
* `u = 1, 2, 3` (`no_cover_ker`, `no_cover_two`, `no_cover_three`): `S` is the space of matrices `A`
  with `A_00 + A_11 = 0` and `A_01 = 0` (and `A_22 = 0` for `u = 3`). A rank-one matrix `x yᵀ` in
  `S` has `x_0 y_1 = 0` and `x_0 y_0 = - x_1 y_1`, hence `(x_0 y_0)^2 = 0`. So a span of `m n - u`
  rank-one matrices (`u = 2, 3` the codimension) containing `S` would be equal to `S` and consist
  of matrices with vanishing `(0, 0)` entry, while `E_00 - E_11` lies in `S`. For `u = 1` the space
  of `u = 2` is used.
* `u = 4` (`key`, `block`, `lower`): `S` is the space of matrices `A` whose top left `2 × 4` block
  is the graph of the nilpotent map `N = E_01 + E_23` of rank two,
    `A_10 = A_01`, `A_11 = 0`, `A_12 = A_03`, `A_13 = 0`,
  the kernel of the surjective map `θ A = (A_10 - A_01, A_11, A_12 - A_03, A_13)`. (The block is the
  slice space of the pencil `x I + y N` with two Jordan blocks of size two, the `2 × 4 × 4` tensor
  of maximal rank six.) If `S` lay in the span `R` of `m n - 3` rank-one matrices `x_l y_lᵀ`, then
  `θ(R)` would have dimension at most `dim R - dim S ≤ 1`, so it would lie in a line `ℂ λ`: for
  every `l` there is `t` with
    `x_1 y_0 - x_0 y_1 = t λ_0`, `x_1 y_1 = t λ_1`, `x_1 y_2 - x_0 y_3 = t λ_2`, `x_1 y_3 = t λ_3`.
  The lemma `key` shows that these equations force `x_0 (α y_1 + β y_3) = 0` for a pair
  `(α, β) ≠ 0` that depends only on `λ`: take `(λ_3, -λ_1)` if it is nonzero, otherwise
  `(λ_2, -λ_0)` if it is nonzero, otherwise `(1, 0)`. So the functional `A ↦ α A_01 + β A_03`
  vanishes on every `x_l y_lᵀ`, hence on `R`, hence on `S`. But `S` contains `E_01 + E_10` and
  `E_03 + E_12`, on which the functional takes the values `α` and `β`: a contradiction.
-/

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

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.H2 := by
  intro m n u hm hmn hu
  exact LeMinLower.lower_all hm hmn hu
