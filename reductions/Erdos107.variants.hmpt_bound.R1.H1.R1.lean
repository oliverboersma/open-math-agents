import OMAReductions.R_Erdos107_variants_hmpt_bound_R1

-- Reduction Erdos107.variants.hmpt_bound.R1.H1.R1 of step Erdos107.variants.hmpt_bound.R1.H1
-- Credit: @mucoucah

/-!
Pór–Valtr positive-fraction Erdős–Szekeres, split into
* `H1`: a point sequence all of whose index-ordered triples are counterclockwise is injective and in
  convex position (elementary planar geometry);
* `H2`: the combinatorial core for `k ≥ 4`: positive-fraction parts such that every transversal
  is, in index order, uniformly counterclockwise or uniformly clockwise (a cup/cap pattern).
`main` handles `k ≤ 3` (residue-class partition and noncollinear triples) and reverses the
clockwise transversals.
-/

open Finset

namespace OMA.R_Erdos107_variants_hmpt_bound_R1_H1_R1


lemma small_convex (k : ℕ) (hk : k ≤ 3) (X : Finset (EuclideanSpace ℝ (Fin 2)))
    (hX : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2))))
    (g : Fin k → (EuclideanSpace ℝ (Fin 2))) (hg : ∀ i, g i ∈ X) (hinj : Function.Injective g) :
    ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a}) := by
  rintro a ⟨i, rfl⟩ hmem
  interval_cases k
  · exact i.elim0
  · have hsub : Set.range g \ {g i} ⊆ ∅ := by
      rintro x ⟨⟨m, rfl⟩, hne⟩
      exact hne (congrArg g (Subsingleton.elim m i))
    have := convexHull_mono hsub hmem
    simp at this
  · have hsub : Set.range g \ {g i} ⊆ {g (1 - i)} := by
      rintro x ⟨⟨m, rfl⟩, hne⟩
      fin_cases i <;> fin_cases m <;> simp_all
    have := convexHull_mono hsub hmem
    rw [convexHull_singleton] at this
    have h2 := hinj this
    fin_cases i <;> simp at h2
  · obtain ⟨j, l, hj, hl, hjl, hsub⟩ : ∃ j l : Fin 3, j ≠ i ∧ l ≠ i ∧ j ≠ l ∧
        Set.range g \ {g i} ⊆ {g j, g l} := by
      fin_cases i
      · refine ⟨1, 2, by decide, by decide, by decide, ?_⟩
        rintro x ⟨⟨m, rfl⟩, hne⟩
        fin_cases m <;> simp_all
      · refine ⟨0, 2, by decide, by decide, by decide, ?_⟩
        rintro x ⟨⟨m, rfl⟩, hne⟩
        fin_cases m <;> simp_all
      · refine ⟨0, 1, by decide, by decide, by decide, ?_⟩
        rintro x ⟨⟨m, rfl⟩, hne⟩
        fin_cases m <;> simp_all
    have := convexHull_mono hsub hmem
    rw [convexHull_pair, mem_segment_iff_wbtw] at this
    have hc := this.collinear
    have hne1 : g j ≠ g i := fun h => hj (hinj h)
    have hne2 : g i ≠ g l := fun h => hl (hinj h).symm
    have hne3 : g j ≠ g l := fun h => hjl (hinj h)
    exact hX _ (hg j) _ (hg i) _ (hg l) hne1 hne2 hne3 hc

/-- residue-class partition into k large pieces. -/
lemma partition (k : ℕ) (hk : 1 ≤ k) (X : Finset (EuclideanSpace ℝ (Fin 2))) (hkX : k ≤ X.card) :
    ∃ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)), (∀ i, T i ⊆ X) ∧ (∀ i, X.card ≤ 2 * k * (T i).card) ∧
      ∀ g : Fin k → (EuclideanSpace ℝ (Fin 2)), (∀ i, g i ∈ T i) → Function.Injective g := by
  classical
  set n := X.card with hn
  let f : ℕ → (EuclideanSpace ℝ (Fin 2)) := fun m => if h : m < n then (X.equivFin.symm ⟨m, h⟩ : (EuclideanSpace ℝ (Fin 2))) else 0
  have hfX : ∀ m < n, f m ∈ X := by
    intro m hm
    simp only [f, dif_pos hm]
    exact (X.equivFin.symm ⟨m, hm⟩).2
  have hfinj : ∀ m < n, ∀ m' < n, f m = f m' → m = m' := by
    intro m hm m' hm' h
    simp only [f, dif_pos hm, dif_pos hm'] at h
    have := X.equivFin.symm.injective (Subtype.ext h)
    simpa using this
  have hidx : ∀ (i : Fin k), ∀ m < n / k, m * k + i < n := by
    intro i m hm
    have h1 : m * k + k ≤ n / k * k := by
      have : (m + 1) * k ≤ n / k * k := Nat.mul_le_mul_right _ hm
      linarith [this]
    have h2 : n / k * k ≤ n := Nat.div_mul_le_self n k
    omega
  refine ⟨fun i => (range (n / k)).image (fun m => f (m * k + i)), ?_, ?_, ?_⟩
  · intro i x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact hfX _ (hidx i m hm)
  · intro i
    rw [card_image_of_injOn]
    · rw [card_range]
      have h1 : 1 ≤ n / k := (Nat.one_le_div_iff (by omega)).2 hkX
      have h2 := Nat.div_add_mod n k
      have h3 := Nat.mod_lt n (show k > 0 by omega)
      nlinarith
    · intro m hm m' hm' h
      simp only [coe_range, Set.mem_Iio] at hm hm'
      have := hfinj _ (hidx i m hm) _ (hidx i m' hm') h
      have hk0 : 0 < k := by omega
      have : m * k = m' * k := by omega
      exact Nat.eq_of_mul_eq_mul_right hk0 this
  · intro g hg i j hij
    have hi := hg i
    have hj := hg j
    simp only [mem_image, mem_range] at hi hj
    obtain ⟨m, hm, hmi⟩ := hi
    obtain ⟨m', hm', hmj⟩ := hj
    have := hfinj _ (hidx i m hm) _ (hidx j m' hm') (hmi.trans (hij.trans hmj.symm))
    have h1 : (m * k + i) % k = (m' * k + j) % k := by rw [this]
    rw [Nat.mul_comm m, Nat.mul_comm m', Nat.mul_add_mod, Nat.mul_add_mod,
      Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at h1
    exact Fin.ext h1


/-- Index-ordered counterclockwise sequences are injective and in convex position. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ g : Fin k → EuclideanSpace ℝ (Fin 2),
    (∀ i j l : Fin k, i < j → j < l →
      0 < (g j 0 - g i 0) * (g l 1 - g i 1) - (g j 1 - g i 1) * (g l 0 - g i 0)) →
    Function.Injective g ∧ ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a})

/-- Positive-fraction partition with uniformly oriented transversals, `k ≥ 4`. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ k : ℕ, 4 ≤ k → ∀ X : Finset (EuclideanSpace ℝ (Fin 2)),
    (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z →
      ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) →
    2 ^ (A * k) ≤ X.card →
    ∃ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)),
      (∀ i, T i ⊆ X) ∧ (∀ i, X.card ≤ 2 ^ (A * k) * (T i).card) ∧
      ∀ g : Fin k → EuclideanSpace ℝ (Fin 2), (∀ i, g i ∈ T i) →
        (∀ i j l : Fin k, i < j → j < l →
          0 < (g j 0 - g i 0) * (g l 1 - g i 1) - (g j 1 - g i 1) * (g l 0 - g i 0)) ∨
        (∀ i j l : Fin k, i < j → j < l →
          (g j 0 - g i 0) * (g l 1 - g i 1) - (g j 1 - g i 1) * (g l 0 - g i 0) < 0)

theorem main : H1 → H2 → OMA.R_Erdos107_variants_hmpt_bound_R1.H1 := by
  intro hC hPV
  obtain ⟨A, hA⟩ := hPV
  refine ⟨max A 1, ?_⟩
  intro k hk X hX hcard
  have hpow : 2 ^ (A * k) ≤ 2 ^ (max A 1 * k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (le_max_left _ _))
  by_cases hk4 : 4 ≤ k
  · obtain ⟨T, h1, h2, h3⟩ := hA k hk4 X hX (hpow.trans hcard)
    refine ⟨T, h1, fun i => (h2 i).trans (Nat.mul_le_mul_right _ hpow), fun g hg => ?_⟩
    rcases h3 g hg with hpos | hneg
    · exact hC k (by omega) g hpos
    · have hrev := hC k (by omega) (g ∘ Fin.rev) (fun i j l hij hjl => by
        have h := hneg (Fin.rev l) (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.mpr hjl)
          (Fin.rev_lt_rev.mpr hij)
        simp only [Function.comp]
        nlinarith [h])
      obtain ⟨hinj, hcv⟩ := hrev
      have hr : Set.range (g ∘ Fin.rev) = Set.range g :=
        Function.Surjective.range_comp Fin.rev_surjective g
      refine ⟨fun a b hab => ?_, by rwa [hr] at hcv⟩
      have : Fin.rev a = Fin.rev b := hinj (by simp [Function.comp, Fin.rev_rev, hab])
      exact Fin.rev_injective this
  · have hk3 : k ≤ 3 := by omega
    have h2k : 2 * k ≤ 2 ^ (max A 1 * k) := by
      have : 2 ^ k ≤ 2 ^ (max A 1 * k) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
      have : 2 * k ≤ 2 ^ k := by interval_cases k <;> norm_num
      omega
    have hkX : k ≤ X.card := by omega
    obtain ⟨T, h1, h2, h3⟩ := partition k hk X hkX
    refine ⟨T, h1, fun i => (h2 i).trans (Nat.mul_le_mul_right _ h2k), fun g hg => ?_⟩
    have hinj := h3 g hg
    exact ⟨hinj, small_convex k hk3 X hX g (fun i => h1 i (hg i)) hinj⟩

end OMA.R_Erdos107_variants_hmpt_bound_R1_H1_R1
