import OMAReductions.R_Erdos554_erdos_554_variants_jenssen_skokan_R1

/-! This step is the statement of Erdos554.erdos_554.variants.lower_bound, and the proof below
is the one merged for it in open-math-agents (proofs/Erdos554.erdos_554.variants.lower_bound.lean,
pull request 633, by @Genbox), reused unchanged apart from the name of the final statement. -/

/-! The lower-bound coloring uses binary labels on blocks of size twice the cycle parameter. -/

open SimpleGraph Finset

namespace OMA

theorem finiteMulticolorClique (t k : ℕ) : ∃ N : ℕ,
    ∀ {m : ℕ} (c : Finset (Fin m) → Fin (k + 1)) (V : Finset (Fin m)), N ≤ V.card →
      ∃ i : Fin (k + 1), ∃ S ⊆ V, S.card = t ∧ ∀ e ⊆ S, e.card = 2 → c e = i := by
  classical
  induction k with
  | zero =>
    refine ⟨t, fun c V hV ↦ ?_⟩
    obtain ⟨S, hSV, hS⟩ := Finset.exists_subset_card_eq hV
    refine ⟨0, S, hSV, hS, fun e he hcard ↦ Fin.ext ?_⟩
    have := (c e).isLt
    change (c e).val = 0
    omega
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨(N + t).choose N, fun c V hV ↦ ?_⟩
    let isLast (e : Finset _) := decide ((c e).val = k + 1)
    rcases Combinatorics.Diagonal.hasRamseyProperty_choose N t isLast V hV with
      ⟨U, hUV, hU, hu⟩ | ⟨S, hSV, hS, hs⟩
    · let lowColor (e : Finset _) : Fin (k + 1) :=
        if h : (c e).val < k + 1 then ⟨(c e).val, h⟩ else 0
      obtain ⟨i, S, hSU, hS, hs⟩ := hN lowColor U hU.ge
      refine ⟨i.castSucc, S, hSU.trans hUV, hS, fun e he hcard ↦ ?_⟩
      have hlast : (c e).val ≠ k + 1 := of_decide_eq_false (hu e (he.trans hSU) hcard)
      have hlt := (c e).isLt
      have hlow : (c e).val < k + 1 := by omega
      apply Fin.ext
      simpa only [lowColor, dif_pos hlow, Fin.val_castSucc] using congrArg Fin.val (hs e he hcard)
    · refine ⟨Fin.last (k + 1), S, hSV, hS, fun e he hcard ↦ Fin.ext ?_⟩
      exact of_decide_eq_true (hs e he hcard)

noncomputable def cliqueEdgeColor {m k : ℕ} (C : TopEdgeLabeling (Fin m) (Fin (k + 1)))
    (s : Finset (Fin m)) : Fin (k + 1) :=
  if hs : s.Nonempty then
    if h : s.min' hs ≠ s.max' hs then C.get (s.min' hs) (s.max' hs) h else 0
  else 0

theorem cliqueEdgeColor_pair {m k : ℕ} (C : TopEdgeLabeling (Fin m) (Fin (k + 1)))
    {x y : Fin m} (h : x ≠ y) : cliqueEdgeColor C {x, y} = C.get x y h := by
  classical
  unfold cliqueEdgeColor
  rw [dif_pos (Finset.insert_nonempty _ _)]
  by_cases hxy : x ≤ y
  · simp [min_eq_left hxy, max_eq_right hxy, h]
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa [Finset.min'_pair, Finset.max'_pair, min_eq_right hyx, max_eq_left hyx, h.symm] using
      (EdgeLabeling.get_comm (C := C) x y h.symm)

theorem cycleRamseyFinite (t k : ℕ) :
    {N : ℕ | ∀ C : TopEdgeLabeling (Fin N) (Fin (k + 1)),
      ∃ i, (cycleGraph t).IsContained (C.labelGraph i)}.Nonempty := by
  obtain ⟨N, hN⟩ := finiteMulticolorClique t k
  refine ⟨N, fun C ↦ ?_⟩
  obtain ⟨i, S, _, hS, hs⟩ := hN (cliqueEdgeColor C) Finset.univ (by simp)
  let f : Fin t ≃ S := Fintype.equivOfCardEq (by simpa using hS.symm)
  refine ⟨i, (isContained_iff_exists_le_comap).mpr ⟨f.toEmbedding.trans
    (Function.Embedding.subtype _), fun v w hvw ↦ ?_⟩⟩
  rw [comap_adj, TopEdgeLabeling.labelGraph_adj]
  change ∃ h : (f v).val ≠ (f w).val, C.get (f v).val (f w).val h = i
  have hne : (f v).val ≠ (f w).val :=
    fun h ↦ hvw.ne (f.injective (Subtype.ext h))
  refine ⟨hne, ?_⟩
  rw [← cliqueEdgeColor_pair C hne]
  exact hs _ (Finset.insert_subset (f v).property (Finset.singleton_subset_iff.mpr (f w).property))
    (Finset.card_pair hne)

noncomputable def bitDifferences {k : ℕ} (a b : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun i ↦ a i ≠ b i)

noncomputable def bitColor {k : ℕ} (a b : Fin k → Bool) : Fin (k + 1) :=
  if h : (bitDifferences a b).Nonempty then ((bitDifferences a b).min' h).succ else 0

theorem bitColor_symm {k : ℕ} (a b : Fin k → Bool) : bitColor b a = bitColor a b := by
  have h : bitDifferences b a = bitDifferences a b := by
    ext i
    simp [bitDifferences, ne_comm]
  simp [bitColor, h]

theorem bitColor_zero {k : ℕ} {a b : Fin k → Bool} (h : bitColor a b = 0) : a = b := by
  classical
  by_contra hn
  have hd : (bitDifferences a b).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
    exact ⟨i, by simp [bitDifferences, hi]⟩
  simp [bitColor, hd] at h

theorem bitColor_succ {k : ℕ} {a b : Fin k → Bool} {i : Fin k}
    (h : bitColor a b = i.succ) : a i ≠ b i := by
  classical
  by_cases hd : (bitDifferences a b).Nonempty
  · have hi : (bitDifferences a b).min' hd = i := by simpa [bitColor, hd] using h
    have hmem := Finset.min'_mem (bitDifferences a b) hd
    rw [hi] at hmem
    simpa [bitDifferences] using hmem
  · simp only [bitColor, dif_neg hd] at h
    exact (Fin.succ_ne_zero _ h.symm).elim

theorem oddCycleBadColoring {n k N : ℕ} (hn : 1 ≤ n) (hN : N ≤ n * 2 ^ (k + 1)) :
    ∃ C : TopEdgeLabeling (Fin N) (Fin (k + 1)),
      ∀ i, ¬ (cycleGraph (2 * n + 1)).IsContained (C.labelGraph i) := by
  classical
  have hcard : Fintype.card (Fin (2 * n) × (Fin k → Bool)) = n * 2 ^ (k + 1) := by
    simp [pow_succ]
    ring
  let e : Fin N ↪ (Fin (2 * n) × (Fin k → Bool)) :=
    (Fin.castLEEmb (hN.trans hcard.symm.le)).trans (Fintype.equivFin _).symm.toEmbedding
  let C : TopEdgeLabeling (Fin N) (Fin (k + 1)) :=
    EdgeLabeling.mk (fun x y _ ↦ bitColor (e x).2 (e y).2) (fun x y _ ↦ bitColor_symm _ _)
  refine ⟨C, fun i hi ↦ ?_⟩
  obtain ⟨f⟩ := hi
  have hcolor {v w : Fin (2 * n + 1)} (hvw : (cycleGraph (2 * n + 1)).Adj v w) :
      bitColor (e (f v)).2 (e (f w)).2 = i := by
    obtain ⟨h, hh⟩ := (TopEdgeLabeling.labelGraph_adj _ _).mp (f.toHom.map_adj hvw)
    simpa [C, EdgeLabeling.get_mk] using hh
  refine Fin.cases (motive := fun j ↦
    (∀ {v w : Fin (2 * n + 1)}, (cycleGraph (2 * n + 1)).Adj v w →
      bitColor (e (f v)).2 (e (f w)).2 = j) → False) ?_ (fun j ↦ ?_) i hcolor
  · intro h
    have hsame (v w : Fin (2 * n + 1)) : (e (f v)).2 = (e (f w)).2 := by
      obtain ⟨p⟩ := cycleGraph_preconnected v w
      induction p with
      | nil => rfl
      | cons hvw _ ih => exact (bitColor_zero (h hvw)).trans ih
    have hinj : Function.Injective (fun v ↦ (e (f v)).1) := by
      intro v w heq
      exact f.injective (e.injective (Prod.ext heq (hsame v w)))
    have hle := Fintype.card_le_of_injective _ hinj
    simp at hle
  · intro h
    have hproper : (cycleGraph (2 * n + 1)).Colorable 2 := by
      let col (v : Fin (2 * n + 1)) : Fin 2 := if (e (f v)).2 j then 1 else 0
      refine ⟨SimpleGraph.Coloring.mk col fun {v w} hvw hEq ↦ ?_⟩
      have hj := bitColor_succ (h hvw)
      by_cases hv : (e (f v)).2 j <;> by_cases hw : (e (f w)).2 j <;> simp_all [col]
    have hle := hproper.chromaticNumber_le
    rw [chromaticNumber_cycleGraph_of_odd _ (by omega) (by exact ⟨n, by omega⟩)] at hle
    norm_num at hle

end OMA

theorem OMA.solution : OMA.R_Erdos554_erdos_554_variants_jenssen_skokan_R1.H2 := by
  intro n hn k hk
  obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = k' + 1 := ⟨k - 1, by omega⟩
  unfold multicolourGraphRamsey
  refine le_csInf (OMA.cycleRamseyFinite (2 * n + 1) k) ?_
  intro N hN
  by_contra! hlt
  obtain ⟨C, hbad⟩ := OMA.oddCycleBadColoring hn (by omega : N ≤ n * 2 ^ (k + 1))
  obtain ⟨i, hi⟩ := hN C
  exact hbad i hi