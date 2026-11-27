import FormalConjectures.Wikipedia.LonelyRunnerConjecture

/-!
Reduction `LonelyRunnerConjecture.lonely_runner_conjecture.R1` of the Lonely Runner Conjecture
into four pillars, together with unconditional in-file proofs of stationary-frame and
sign-collision strong induction, all small cases `n ≤ 3`, the general lacunary nested-interval
theorem for all `k ≥ 3`, primitive common-divisor scaling, and the `(k + 1)`-divisibility sieve.
-/

-- Reduction LonelyRunnerConjecture.lonely_runner_conjecture.R1 of Lonely runner conjecture
-- Credit: @Pampasgras
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1

-- Pillar 1 (Bienia-Goddyn-Gvozdjak-Sebo-Tarsi 1998, Bohman-Holzman-Kleitman 2001):
-- Real-to-integer velocity reduction for non-lacunary strictly increasing positive speeds.
def H1 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (v : Fin k → ℝ),
    (∀ i : Fin k, 0 < v i) →
    StrictMono v →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧
      ((k : ℝ) - 1) * v j < 2 * (k : ℝ) * v i) →
    (∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (w : Fin m → ℕ),
      (∀ i : Fin m, 0 < w i) → StrictMono w →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

-- Pillar 2 (Betke-Wills 1972, Cusick-Pomerance 1984, Bohman-Holzman-Kleitman 2001,
-- Barajas-Serra 2008, Rosenfeld 2025):
-- Solved small-runner integer regimes for 4 to 8 total runners (3 <= k <= 7 moving runners).
def H2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → k ≤ 7 → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∃ i : Fin k, (k + 1) ∣ w i) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

-- Pillar 3 (Tao 2017, Malikiosis-Santos-Schymura 2025):
-- Zonotopal finite-checking reduction for k >= 8: unbounded primitive integer velocity tuples
-- reduce to smaller runner counts (1 <= m < k) together with velocities bounded by k^(2k).
def H3 : Prop :=
  ∀ (k : ℕ), 8 ≤ k → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∃ i : Fin k, (k + 1) ∣ w i) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    (∃ i : Fin k, k ^ (2 * k) < w i) →
    (∀ (m : ℕ), 1 ≤ m → m < k → ∀ (u : Fin m → ℕ),
      (∀ i : Fin m, 0 < u i) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) →
    (∀ (u : Fin k → ℕ),
      (∀ i : Fin k, 0 < u i) → StrictMono u → Finset.univ.gcd u = 1 →
      (∀ i : Fin k, u i ≤ k ^ (2 * k)) →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

-- Pillar 4 (Open Bounded-Velocity Frontier for 9 or more total runners):
-- Finite per-k regime of primitive, non-lacunary integer velocity tuples bounded by k^(2k)
-- that contain at least one multiple of k + 1, for k >= 8 moving runners.
def H4 : Prop :=
  ∀ (k : ℕ), 8 ≤ k → ∀ (w : Fin k → ℕ),
    (∀ i : Fin k, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∃ i : Fin k, (k + 1) ∣ w i) →
    (∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧ (k - 1) * w j < 2 * k * w i) →
    (∀ i : Fin k, w i ≤ k ^ (2 * k)) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)

section ReductionProofs

private lemma unitAddCircle_dist_eq (a b : ℝ) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) = dist ((a - b : ℝ) : UnitAddCircle) 0 := by
  rw [dist_eq_norm, dist_zero_right, ← QuotientAddGroup.mk_sub]

private lemma unitAddCircle_dist_mul_sub (t a b : ℝ) :
    dist (t * a : UnitAddCircle) (t * b : UnitAddCircle) =
      dist ((t * (b - a) : ℝ) : UnitAddCircle) 0 := by
  rw [dist_comm, unitAddCircle_dist_eq]
  congr 2
  ring

private lemma unitAddCircle_dist_neg (x : ℝ) :
    dist ((-x : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rw [dist_zero_right, dist_zero_right, QuotientAddGroup.mk_neg, norm_neg]

private lemma unitAddCircle_dist_abs (t x : ℝ) :
    dist ((t * |x| : ℝ) : UnitAddCircle) 0 = dist ((t * x : ℝ) : UnitAddCircle) 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, mul_neg, unitAddCircle_dist_neg]

private lemma unitAddCircle_dist_ge_of_Icc (x δ : ℝ) (k : ℤ)
    (h1 : (k : ℝ) + δ ≤ x) (h2 : x ≤ (k : ℝ) + 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  rw [ge_iff_le, dist_zero_right, UnitAddCircle.norm_eq]
  set m : ℤ := round x
  rcases le_or_gt m k with hmk | hkm
  · have hmk' : (m : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hmk
    have hle : δ ≤ x - (m : ℝ) := by linarith
    exact hle.trans (le_abs_self _)
  · have hkm1 : k + 1 ≤ m := Int.add_one_le_iff.mpr hkm
    have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm1
    have hle : δ ≤ -(x - (m : ℝ)) := by linarith
    exact hle.trans (neg_le_abs _)

private lemma unitAddCircle_dist_ge_of_Icc_zero (x δ : ℝ)
    (h1 : δ ≤ x) (h2 : x ≤ 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  refine unitAddCircle_dist_ge_of_Icc x δ 0 ?_ ?_
  · simp [h1]
  · simp [h2]

private lemma exists_subinterval_dist_ge (A B δ L : ℝ)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hLδ : L + 2 * δ ≤ 1) (hBA : 2 * L + 2 * δ ≤ B - A) :
    ∃ C D : ℝ, ∃ m : ℤ,
      A ≤ C ∧ D ≤ B ∧ D - C = L ∧ (m : ℝ) + δ ≤ C ∧ D ≤ (m : ℝ) + 1 - δ := by
  set k : ℤ := ⌊A⌋
  have hk1 : (k : ℝ) ≤ A := Int.floor_le A
  have hk2 : A < (k : ℝ) + 1 := Int.lt_floor_add_one A
  rcases le_or_gt A ((k : ℝ) + δ) with hA1 | hA1
  · refine ⟨(k : ℝ) + δ, (k : ℝ) + δ + L, k, hA1, ?_, by ring, le_rfl, ?_⟩
    · linarith
    · linarith
  · rcases le_or_gt (A + L) ((k : ℝ) + 1 - δ) with hA2 | hA2
    · refine ⟨A, A + L, k, le_rfl, ?_, by ring, hA1.le, hA2⟩
      linarith
    · refine ⟨(k : ℝ) + 1 + δ, (k : ℝ) + 1 + δ + L, k + 1, ?_, ?_, by ring, ?_, ?_⟩
      · linarith
      · linarith
      · push_cast; linarith
      · push_cast; linarith

private lemma lrc_pos_one (v : Fin 1 → ℝ) (hv : ∀ i : Fin 1, 0 < v i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 1, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((1 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  refine ⟨1 / (2 * v 0), by positivity, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  have hmul : 1 / (2 * v 0) * v 0 = (1 : ℝ) / 2 := by
    field_simp [ne_of_gt hv0]
  rw [hmul]
  have hcast : (1 : ℝ) / ((1 + 1 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [hcast]
  exact unitAddCircle_dist_ge_of_Icc_zero (1 / 2) (1 / 2) (by norm_num) (by norm_num)

private lemma lrc_pos_two (v : Fin 2 → ℝ) (hv : ∀ i : Fin 2, 0 < v i) (hmono : StrictMono v) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 2, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((2 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  have hv1 : 0 < v 1 := hv 1
  have hv01 : v 0 < v 1 := hmono (by decide)
  have hcast : (1 : ℝ) / ((2 + 1 : ℕ) : ℝ) = 1 / 3 := by norm_num
  rw [hcast]
  rcases lt_or_ge (v 1) (2 * v 0) with hlt | hge
  · refine ⟨1 / (3 * v 0), by positivity, fun i => ?_⟩
    fin_cases i
    · change dist ((1 / (3 * v 0) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have hmul : 1 / (3 * v 0) * v 0 = (1 : ℝ) / 3 := by
        field_simp [ne_of_gt hv0]
      rw [hmul]
      exact unitAddCircle_dist_ge_of_Icc_zero (1 / 3) (1 / 3) (by norm_num) (by norm_num)
    · change dist ((1 / (3 * v 0) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have h_eq : 1 / (3 * v 0) * v 1 = v 1 / (3 * v 0) := one_div_mul_eq_div (3 * v 0) (v 1)
      rw [h_eq]
      have hlo : (1 : ℝ) / 3 ≤ v 1 / (3 * v 0) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hhi : v 1 / (3 * v 0) ≤ 1 - 1 / 3 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 3) hlo hhi
  · have hlen : 2 * (0 : ℝ) + 2 * (1 / 3 : ℝ) ≤
        (2 * v 1) / (3 * v 0) - v 1 / (3 * v 0) := by
      have hsub : (2 * v 1) / (3 * v 0) - v 1 / (3 * v 0) = v 1 / (3 * v 0) := by ring
      rw [hsub, le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨C, D, m, hAC, hDB, hDC, hm1, hm2⟩ :=
      exists_subinterval_dist_ge (v 1 / (3 * v 0)) ((2 * v 1) / (3 * v 0)) (1 / 3) 0
        (by norm_num) le_rfl (by norm_num) hlen
    have hCD : C = D := by linarith
    have hC_nonneg : 0 ≤ C := le_trans (by positivity) hAC
    refine ⟨C / v 1, by positivity, fun i => ?_⟩
    fin_cases i
    · change dist ((C / v 1 * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have h1 : v 1 ≤ C * (3 * v 0) := (div_le_iff₀ (by positivity)).mp hAC
      have h2 : C * (3 * v 0) ≤ 2 * v 1 :=
        (le_div_iff₀ (by positivity)).mp (hCD.symm ▸ hDB)
      have h_eq : C / v 1 * v 0 = (C * v 0) / v 1 := div_mul_eq_mul_div C (v 1) (v 0)
      rw [h_eq]
      have hlo : (1 : ℝ) / 3 ≤ (C * v 0) / v 1 := by
        rw [le_div_iff₀ hv1]
        linarith
      have hhi : (C * v 0) / v 1 ≤ 1 - 1 / 3 := by
        rw [div_le_iff₀ hv1]
        linarith
      exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 3) hlo hhi
    · change dist ((C / v 1 * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have hmul : C / v 1 * v 1 = C := div_mul_cancel₀ C (ne_of_gt hv1)
      rw [hmul]
      exact unitAddCircle_dist_ge_of_Icc C (1 / 3) m hm1 (hCD ▸ hm2)

private lemma lrc_reduction_to_pos_strictMono
    (h_pos : ∀ (k : ℕ), 3 ≤ k → ∀ (v : Fin k → ℝ),
      (∀ i : Fin k, 0 < v i) → StrictMono v →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ)) :
    ∀ (n : ℕ) (speed : Fin n ↪ ℝ) (r : Fin n),
      ∃ t : ℝ, t ≥ 0 ∧ ∀ r2 : Fin n, r2 ≠ r →
        dist (t * speed r : UnitAddCircle) (t * speed r2) ≥ 1 / (n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro speed r
    rcases eq_or_ne n 0 with rfl | hn0
    · exact Fin.elim0 r
    rcases eq_or_ne n 1 with rfl | hn1
    · refine ⟨0, le_rfl, fun r2 hr2 => absurd (Subsingleton.elim r2 r) hr2⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    have hk1_ge : 1 ≤ k := by omega
    let U : Finset (Fin (k + 1)) := Finset.univ.erase r
    have hU_card : U.card = k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_fin]
      omega
    let S : Finset ℝ := U.image (fun i => |speed i - speed r|)
    have hS_pos : ∀ x ∈ S, 0 < x := by
      intro x hx
      obtain ⟨i, hiU, rfl⟩ := Finset.mem_image.mp hx
      have hir : i ≠ r := Finset.ne_of_mem_erase hiU
      exact abs_pos.mpr (sub_ne_zero.mpr (speed.injective.ne hir))
    have hS_le : S.card ≤ U.card := Finset.card_image_le
    rcases lt_or_eq_of_le hS_le with hlt_card | heq_card
    · have h0_not_mem : (0 : ℝ) ∉ S := fun h0 => (lt_irrefl (0 : ℝ)) (hS_pos 0 h0)
      let S0 : Finset ℝ := insert 0 S
      let m : ℕ := S0.card
      have hm_eq : m = S.card + 1 := Finset.card_insert_of_notMem h0_not_mem
      have hm_lt : m < k + 1 := by omega
      let emb : Fin m ↪ ℝ := (S0.orderEmbOfFin rfl).toEmbedding
      have h_range : Set.range emb = (S0 : Set ℝ) := Finset.range_orderEmbOfFin S0 rfl
      have h0_mem : (0 : ℝ) ∈ (S0 : Set ℝ) := Finset.mem_coe.mpr (Finset.mem_insert_self 0 S)
      obtain ⟨r0, hr0⟩ : ∃ r0 : Fin m, emb r0 = 0 := by
        rwa [← h_range] at h0_mem
      obtain ⟨t, ht0, ht_lonely⟩ := ih m hm_lt emb r0
      refine ⟨t, ht0, fun r2 hr2 => ?_⟩
      have hr2_U : r2 ∈ U := Finset.mem_erase.mpr ⟨hr2, Finset.mem_univ r2⟩
      have hx_S : |speed r2 - speed r| ∈ S :=
        Finset.mem_image.mpr ⟨r2, hr2_U, rfl⟩
      have hx_pos : 0 < |speed r2 - speed r| := hS_pos _ hx_S
      have hx_S0 : |speed r2 - speed r| ∈ (S0 : Set ℝ) :=
        Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx_S)
      obtain ⟨j, hj⟩ : ∃ j : Fin m, emb j = |speed r2 - speed r| := by
        rwa [← h_range] at hx_S0
      have hj_ne : j ≠ r0 := by
        intro h_eq
        rw [h_eq, hr0] at hj
        linarith
      have h_step := ht_lonely j hj_ne
      rw [hr0, mul_zero, hj] at h_step
      have h_zero_coe : ((0 : ℝ) : UnitAddCircle) = 0 := QuotientAddGroup.mk_zero _
      rw [h_zero_coe, dist_comm] at h_step
      rw [unitAddCircle_dist_mul_sub, ← unitAddCircle_dist_abs]
      have h_mn : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hm_lt.le)
      exact le_trans h_mn h_step
    · have hk_eq : S.card = k := heq_card.trans hU_card
      let emb := S.orderEmbOfFin hk_eq
      let v : Fin k → ℝ := fun i => emb i
      have hv_pos : ∀ i : Fin k, 0 < v i :=
        fun i => hS_pos (v i) (Finset.orderEmbOfFin_mem S hk_eq i)
      have hv_mono : StrictMono v := emb.strictMono
      have h_v_lonely : ∃ t : ℝ, t ≥ 0 ∧
          ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
        rcases eq_or_ne k 1 with rfl | hk_ne1
        · exact lrc_pos_one v hv_pos
        · rcases eq_or_ne k 2 with rfl | hk_ne2
          · exact lrc_pos_two v hv_pos hv_mono
          · have hk3 : 3 ≤ k := by omega
            exact h_pos k hk3 v hv_pos hv_mono
      obtain ⟨t, ht0, ht_v⟩ := h_v_lonely
      refine ⟨t, ht0, fun r2 hr2 => ?_⟩
      have hr2_U : r2 ∈ U := Finset.mem_erase.mpr ⟨hr2, Finset.mem_univ r2⟩
      have hx_S : |speed r2 - speed r| ∈ (S : Set ℝ) :=
        Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨r2, hr2_U, rfl⟩)
      have h_range : Set.range v = (S : Set ℝ) := Finset.range_orderEmbOfFin S hk_eq
      obtain ⟨i, hi⟩ : ∃ i : Fin k, v i = |speed r2 - speed r| := by
        rwa [← h_range] at hx_S
      rw [unitAddCircle_dist_mul_sub, ← unitAddCircle_dist_abs, ← hi]
      exact ht_v i

private lemma lrc_lacunary (k : ℕ) (hk : 3 ≤ k) (v : Fin k → ℝ)
    (hv_pos : ∀ i : Fin k, 0 < v i) (hv_mono : StrictMono v)
    (hlac : ∀ i j : Fin k, i.val + 1 = j.val → j.val + 1 < k →
      ((k : ℝ) - 1) * v j ≥ 2 * (k : ℝ) * v i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  let δ : ℝ := 1 / ((k + 1 : ℕ) : ℝ)
  let L : ℝ := ((k : ℝ) - 1) / ((k + 1 : ℕ) : ℝ)
  have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hδ_nonneg : 0 ≤ δ := by positivity
  have hL_nonneg : 0 ≤ L := by
    refine div_nonneg ?_ hk_pos.le
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hLδ_sum : L + 2 * δ ≤ 1 := by
    have heq : L + 2 * δ = 1 := by
      dsimp [L, δ]
      push_cast
      field_simp [ne_of_gt hk_pos]
      ring
    exact heq.le
  have h_nested : ∀ (j : ℕ) (hj : j + 1 < k),
      ∃ a b : ℝ, 0 ≤ a ∧
        b - a = L / v ⟨j, by omega⟩ ∧
        ∀ (m : Fin k), m.val ≤ j → ∀ t : ℝ, a ≤ t → t ≤ b →
          dist ((t * v m : ℝ) : UnitAddCircle) 0 ≥ δ := by
    intro j
    induction j with
    | zero =>
      intro hj
      let i0 : Fin k := ⟨0, by omega⟩
      have hv0 : 0 < v i0 := hv_pos i0
      refine ⟨δ / v i0, (1 - δ) / v i0, by positivity, ?_, ?_⟩
      · have h1 : (1 - δ) / v i0 - δ / v i0 = (1 - 2 * δ) / v i0 := by ring
        rw [h1]
        congr 1
        dsimp [L, δ]
        push_cast
        field_simp [ne_of_gt hk_pos]
        ring
      · intro m hm t hta htb
        have hm_eq : m = i0 := Fin.ext (by dsimp [i0]; omega)
        rw [hm_eq]
        have hlo : δ ≤ t * v i0 := by
          have := (div_le_iff₀ hv0).mp hta
          linarith
        have hhi : t * v i0 ≤ 1 - δ := by
          have := (le_div_iff₀ hv0).mp htb
          linarith
        exact unitAddCircle_dist_ge_of_Icc_zero (t * v i0) δ hlo hhi
    | succ j ih =>
      intro hj_succ
      obtain ⟨a, b, ha0, hba, h_safe⟩ := ih (by omega)
      let ij : Fin k := ⟨j, by omega⟩
      let ij1 : Fin k := ⟨j + 1, by omega⟩
      have hvj : 0 < v ij := hv_pos ij
      have hvj1 : 0 < v ij1 := hv_pos ij1
      have hlac_step : ((k : ℝ) - 1) * v ij1 ≥ 2 * (k : ℝ) * v ij :=
        hlac ij ij1 rfl hj_succ
      have hBA : 2 * L + 2 * δ ≤ v ij1 * b - v ij1 * a := by
        have h1 : v ij1 * b - v ij1 * a = v ij1 * (L / v ij) := by
          rw [← mul_sub, hba]
        have h2 : 2 * L + 2 * δ = (2 * (k : ℝ)) / ((k + 1 : ℕ) : ℝ) := by
          dsimp [L, δ]
          push_cast
          field_simp [ne_of_gt hk_pos]
          ring
        have h3 : v ij1 * (L / v ij) = (((k : ℝ) - 1) * v ij1) / (((k + 1 : ℕ) : ℝ) * v ij) := by
          dsimp [L]
          ring
        rw [h1, h2, h3, div_le_div_iff₀ hk_pos (by positivity)]
        nlinarith
      obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
        exists_subinterval_dist_ge (v ij1 * a) (v ij1 * b) δ L
          hδ_nonneg hL_nonneg hLδ_sum hBA
      have ha_le : a ≤ C / v ij1 := (le_div_iff₀ hvj1).mpr (by linarith)
      have hb_le : D / v ij1 ≤ b := (div_le_iff₀ hvj1).mpr (by linarith)
      refine ⟨C / v ij1, D / v ij1, le_trans ha0 ha_le, ?_, ?_⟩
      · rw [← sub_div, hDC]
      · intro m hm t hta htb
        rcases Nat.of_le_succ hm with hm_le | hm_eq
        · exact h_safe m hm_le t (le_trans ha_le hta) (le_trans htb hb_le)
        · have hm_fin : m = ij1 := Fin.ext hm_eq
          rw [hm_fin]
          have hCt : C ≤ t * v ij1 := (div_le_iff₀ hvj1).mp hta
          have htD : t * v ij1 ≤ D := (le_div_iff₀ hvj1).mp htb
          exact unitAddCircle_dist_ge_of_Icc (t * v ij1) δ z
            (le_trans hz1 hCt) (le_trans htD hz2)
  obtain ⟨a, b, ha0, hba, h_safe⟩ := h_nested (k - 2) (by omega)
  let iprev : Fin k := ⟨k - 2, by omega⟩
  let ilast : Fin k := ⟨k - 1, by omega⟩
  have hv_prev : 0 < v iprev := hv_pos iprev
  have hv_last : 0 < v ilast := hv_pos ilast
  have hv_lt : v iprev < v ilast := hv_mono (by rw [Fin.lt_def]; dsimp [iprev, ilast]; omega)
  have h2δ_le_1 : 0 + 2 * δ ≤ 1 := by linarith
  have hBA_last : 2 * (0 : ℝ) + 2 * δ ≤ v ilast * b - v ilast * a := by
    have h1 : v ilast * b - v ilast * a = (v ilast / v iprev) * L := by
      rw [← mul_sub, hba]
      ring
    have h_ratio : 1 ≤ v ilast / v iprev := (one_le_div hv_prev).mpr hv_lt.le
    have hL_le : 1 * L ≤ (v ilast / v iprev) * L :=
      mul_le_mul_of_nonneg_right h_ratio hL_nonneg
    have h2δ_le_L : 2 * δ ≤ L := by
      dsimp [δ, L]
      rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ hk_pos.le
      have hk3' : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    linarith
  obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
    exists_subinterval_dist_ge (v ilast * a) (v ilast * b) δ 0
      hδ_nonneg le_rfl h2δ_le_1 hBA_last
  have hCD : C = D := by linarith
  have ha_t : a ≤ C / v ilast := (le_div_iff₀ hv_last).mpr (by linarith)
  have ht_b : C / v ilast ≤ b := (div_le_iff₀ hv_last).mpr (by linarith)
  refine ⟨C / v ilast, le_trans ha0 ha_t, fun m => ?_⟩
  rcases le_or_gt m.val (k - 2) with hm_le | hm_gt
  · exact h_safe m hm_le (C / v ilast) ha_t ht_b
  · have hm_eq : m = ilast := Fin.ext (by dsimp [ilast]; omega)
    rw [hm_eq, div_mul_cancel₀ C (ne_of_gt hv_last)]
    exact unitAddCircle_dist_ge_of_Icc C δ z hz1 (hCD ▸ hz2)

private lemma lrc_nat_gcd_reduction (m : ℕ) (hm : 1 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (h_prim : ∀ (w' : Fin m → ℕ), (∀ i : Fin m, 0 < w' i) → StrictMono w' →
      Finset.univ.gcd w' = 1 →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w' i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  let g : ℕ := Finset.univ.gcd w
  have i0_mem : (⟨0, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  have hg_ne : g ≠ 0 := by
    intro hg0
    have hw0 : w ⟨0, by omega⟩ = 0 := (Finset.gcd_eq_zero_iff.mp hg0) _ i0_mem
    exact Nat.ne_of_gt (hw_pos ⟨0, by omega⟩) hw0
  have hg_pos : 0 < g := Nat.pos_of_ne_zero hg_ne
  let w' : Fin m → ℕ := fun i => w i / g
  have hw_mul : ∀ i : Fin m, g * w' i = w i :=
    fun i => Nat.mul_div_cancel' (Finset.gcd_dvd (Finset.mem_univ i))
  have hw'_pos : ∀ i : Fin m, 0 < w' i := by
    intro i
    rcases Nat.eq_zero_or_pos (w' i) with hw'0 | hpos
    · exfalso
      have hwi : w i = 0 := by rw [← hw_mul i, hw'0, mul_zero]
      exact Nat.ne_of_gt (hw_pos i) hwi
    · exact hpos
  have hw'_mono : StrictMono w' := by
    intro i j hij
    have hij_w : g * w' i < g * w' j := by
      rw [hw_mul i, hw_mul j]
      exact hw_mono hij
    exact lt_of_mul_lt_mul_left' hij_w
  have hw'_gcd : Finset.univ.gcd w' = 1 := by
    apply Nat.dvd_one.mp
    have hdvd_g : g * Finset.univ.gcd w' ∣ g * 1 := by
      rw [mul_one]
      refine Finset.dvd_gcd fun i hi => ?_
      rw [← hw_mul i]
      exact mul_dvd_mul_left g (Finset.gcd_dvd hi)
    exact (mul_dvd_mul_iff_left hg_ne).mp hdvd_g
  obtain ⟨t', ht'0, ht'⟩ := h_prim w' hw'_pos hw'_mono hw'_gcd
  refine ⟨t' / (g : ℝ), by positivity, fun i => ?_⟩
  have h_scale : t' / (g : ℝ) * (w i : ℝ) = t' * (w' i : ℝ) := by
    have hwi_cast : (w i : ℝ) = (g : ℝ) * (w' i : ℝ) := by exact_mod_cast (hw_mul i).symm
    rw [hwi_cast]
    field_simp [Nat.cast_ne_zero.mpr hg_ne]
  rw [h_scale]
  exact ht' i

private lemma lrc_nat_not_dvd (m : ℕ) (w : Fin m → ℕ)
    (h_ndvd : ∀ i : Fin m, ¬ (m + 1) ∣ w i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  refine ⟨1 / ((m + 1 : ℕ) : ℝ), by positivity, fun i => ?_⟩
  let q : ℕ := w i / (m + 1)
  let r : ℕ := w i % (m + 1)
  have hdiv : (m + 1) * q + r = w i := Nat.div_add_mod (w i) (m + 1)
  have hr_ne : r ≠ 0 := by
    intro hr0
    exact h_ndvd i (Nat.dvd_of_mod_eq_zero hr0)
  have hr_ge : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr_ne
  have hr_lt : r < m + 1 := Nat.mod_lt (w i) (Nat.succ_pos m)
  have hr_le : r ≤ m := Nat.le_of_lt_succ hr_lt
  have h_eq : 1 / ((m + 1 : ℕ) : ℝ) * (w i : ℝ) =
      ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have hwi_cast : (w i : ℝ) = ((m + 1 : ℕ) : ℝ) * (q : ℝ) + (r : ℝ) := by
      exact_mod_cast hdiv.symm
    rw [hwi_cast, Int.cast_natCast]
    field_simp [ne_of_gt hm_pos]
  rw [h_eq]
  have hlo : ((q : ℤ) : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) ≤
      ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
    have hdiv_le : 1 / ((m + 1 : ℕ) : ℝ) ≤ (r : ℝ) / ((m + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hr1 hm_pos.le
    linarith
  have hhi : ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
      ((q : ℤ) : ℝ) + 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
    have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hr_le
    have hdiv_le : (r : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hm_pos]
      have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have h_rhs : (1 - 1 / ((m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) = (m : ℝ) := by
        field_simp [ne_of_gt hm_pos]
        linarith
      linarith
    linarith
  exact unitAddCircle_dist_ge_of_Icc _ (1 / ((m + 1 : ℕ) : ℝ)) (q : ℤ) hlo hhi

private lemma lrc_lacunary_nat (m : ℕ) (hm3 : 3 ≤ m) (u : Fin m → ℕ)
    (hu_pos : ∀ i : Fin m, 0 < u i) (hu_mono : StrictMono u)
    (h_not_nonlac : ¬ ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
      (m - 1) * u j < 2 * m * u i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  refine lrc_lacunary m hm3 (fun i => (u i : ℝ))
    (fun i => Nat.cast_pos.mpr (hu_pos i))
    (fun i j hij => Nat.cast_lt.mpr (hu_mono hij)) ?_
  intro i j hij hj_lt
  have h_ge : 2 * m * u i ≤ (m - 1) * u j := by
    by_contra hlt
    exact h_not_nonlac ⟨i, j, hij, hj_lt, Nat.lt_of_not_le hlt⟩
  have h_cast : ((2 * m * u i : ℕ) : ℝ) ≤ (((m - 1) * u j : ℕ) : ℝ) := by
    exact_mod_cast h_ge
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  push_cast at h_cast
  rw [hm_sub] at h_cast
  exact h_cast

private lemma lrc_nat_prim_core (h2 : H2) (h4 : H4) (m : ℕ) (hm3 : 3 ≤ m)
    (u : Fin m → ℕ) (hu_pos : ∀ i : Fin m, 0 < u i) (hu_mono : StrictMono u)
    (hu_gcd : Finset.univ.gcd u = 1)
    (h_small_or_bdd : m ≤ 7 ∨ (8 ≤ m ∧ ∀ i : Fin m, u i ≤ m ^ (2 * m))) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  by_cases hdvd : ∃ i : Fin m, (m + 1) ∣ u i
  · by_cases hlac : ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
        (m - 1) * u j < 2 * m * u i
    · rcases h_small_or_bdd with hm7 | ⟨hm8, hbdd⟩
      · exact h2 m hm3 hm7 u hu_pos hu_mono hu_gcd hdvd hlac
      · exact h4 m hm8 u hu_pos hu_mono hu_gcd hdvd hlac hbdd
    · exact lrc_lacunary_nat m hm3 u hu_pos hu_mono hlac
  · exact lrc_nat_not_dvd m u (fun i hi => hdvd ⟨i, hi⟩)

private lemma lrc_all_nat (h2 : H2) (h3 : H3) (h4 : H4) :
    ∀ (m : ℕ), 1 ≤ m → ∀ (w : Fin m → ℕ),
      (∀ i : Fin m, 0 < w i) → StrictMono w →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm1 w hw_pos hw_mono
    rcases eq_or_ne m 1 with rfl | hm_ne1
    · exact lrc_pos_one (fun i => (w i : ℝ)) (fun i => Nat.cast_pos.mpr (hw_pos i))
    rcases eq_or_ne m 2 with rfl | hm_ne2
    · exact lrc_pos_two (fun i => (w i : ℝ))
        (fun i => Nat.cast_pos.mpr (hw_pos i))
        (fun i j hij => Nat.cast_lt.mpr (hw_mono hij))
    have hm3 : 3 ≤ m := by omega
    refine lrc_nat_gcd_reduction m hm1 w hw_pos hw_mono ?_
    intro w' hw'_pos hw'_mono hw'_gcd
    rcases le_or_gt m 7 with hm7 | hm7
    · exact lrc_nat_prim_core h2 h4 m hm3 w' hw'_pos hw'_mono hw'_gcd (Or.inl hm7)
    · have hm8 : 8 ≤ m := by omega
      have h_bdd_case : ∀ (u : Fin m → ℕ),
          (∀ i : Fin m, 0 < u i) → StrictMono u → Finset.univ.gcd u = 1 →
          (∀ i : Fin m, u i ≤ m ^ (2 * m)) →
          ∃ t : ℝ, t ≥ 0 ∧
            ∀ i : Fin m,
              dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
        intro u hu_pos hu_mono hu_gcd hu_bdd
        exact lrc_nat_prim_core h2 h4 m hm3 u hu_pos hu_mono hu_gcd (Or.inr ⟨hm8, hu_bdd⟩)
      by_cases h_all_le : ∀ i : Fin m, w' i ≤ m ^ (2 * m)
      · exact h_bdd_case w' hw'_pos hw'_mono hw'_gcd h_all_le
      · have h_ex_gt : ∃ i : Fin m, m ^ (2 * m) < w' i := by
          by_contra hno
          apply h_all_le
          intro i
          by_contra hgt
          exact hno ⟨i, Nat.lt_of_not_le hgt⟩
        by_cases hdvd : ∃ i : Fin m, (m + 1) ∣ w' i
        · by_cases hlac : ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
              (m - 1) * w' j < 2 * m * w' i
          · exact h3 m hm8 w' hw'_pos hw'_mono hw'_gcd hdvd hlac h_ex_gt
              (fun m' hm'1 hm'lt u hu_pos hu_mono => ih m' hm'lt hm'1 u hu_pos hu_mono)
              h_bdd_case
          · exact lrc_lacunary_nat m hm3 w' hw'_pos hw'_mono hlac
        · exact lrc_nat_not_dvd m w' (fun i hi => hdvd ⟨i, hi⟩)

end ReductionProofs

theorem main : H1 → H2 → H3 → H4 → type_of% @LonelyRunnerConjecture.lonely_runner_conjecture := by
  intro h1 h2 h3 h4 n speed lonely lonely_def r
  have h_pos : ∀ (k : ℕ), 3 ≤ k → ∀ (v : Fin k → ℝ),
      (∀ i : Fin k, 0 < v i) → StrictMono v →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
    intro k hk3 v hv_pos hv_mono
    by_cases hlac : ∃ i j : Fin k, i.val + 1 = j.val ∧ j.val + 1 < k ∧
        ((k : ℝ) - 1) * v j < 2 * (k : ℝ) * v i
    · exact h1 k hk3 v hv_pos hv_mono hlac
        (fun m hm1 _ w hw_pos hw_mono => lrc_all_nat h2 h3 h4 m hm1 w hw_pos hw_mono)
    · refine lrc_lacunary k hk3 v hv_pos hv_mono ?_
      intro i j hij hj_lt
      by_contra hlt
      exact hlac ⟨i, j, hij, hj_lt, lt_of_not_ge hlt⟩
  obtain ⟨t, ht, hdist⟩ := lrc_reduction_to_pos_strictMono h_pos n speed r
  exact ⟨t, ht, (lonely_def r t).mpr hdist⟩

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1
