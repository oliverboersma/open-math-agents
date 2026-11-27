import FormalConjectures.ErdosProblems.«629»

-- Problem: Erdős Problem 629 — radhakrishnan srinivasan
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/629.lean:99 (declaration Erdos629.erdos_629.variants.radhakrishnan_srinivasan)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Radhakrishnan-Srinivasan bound for property B, by the Cherkashin-Kozik random order
argument (Pluhar's ordered chain criterion), transferred to list colourings of bipartite
graphs by the Erdős-Rubin-Taylor comparison. -/

open SimpleGraph

lemma OMA.property_b_extract_three {V : Type*} [DecidableEq V] (H : Finset (Finset V))
    (k : ℕ) (hk : 2 ≤ k) (hU : H.IsUniform k) (hNot : ¬ H.HypergraphColorable 2) :
    ∃ J ⊆ H, J.IsUniform k ∧ J.HasHypergraphChromaticNumber 3 := by
  classical
  let bad := H.powerset.filter fun J => ¬ J.HypergraphColorable 2
  have hbad : bad.Nonempty :=
    ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun _ h => h), hNot⟩⟩
  obtain ⟨J, hJ, hmin⟩ := bad.exists_min_image Finset.card hbad
  obtain ⟨hJ_mem, hJ_not⟩ := Finset.mem_filter.mp hJ
  have hJ_sub := Finset.mem_powerset.mp hJ_mem
  have hJ_U : J.IsUniform k := fun e he => hU e (hJ_sub he)
  have hJ_ne : J.Nonempty := by
    by_contra h
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp h
    exact hJ_not ⟨fun _ => 0, by simp [hEmpty, Finset.IsProperHypergraphColoring]⟩
  obtain ⟨e, he⟩ := hJ_ne
  have hErase : (J.erase e).HypergraphColorable 2 := by
    by_contra h
    have hbadErase : J.erase e ∈ bad := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset e J).trans hJ_sub), h⟩
    have hle := hmin _ hbadErase
    have hpos := Finset.card_pos.mpr (show J.Nonempty from ⟨e, he⟩)
    rw [Finset.card_erase_of_mem he] at hle
    omega
  obtain ⟨col, hcol⟩ := hErase
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < e.card by rw [hJ_U e he]; omega)
  let extend (x : V) : Fin 3 := if x = a then 2 else Fin.castLE (by decide : 2 ≤ 3) (col x)
  have hA : extend a = 2 := if_pos rfl
  have hOther (x : V) (hx : x ≠ a) :
      extend x = Fin.castLE (by decide : 2 ≤ 3) (col x) := if_neg hx
  have hDifferent : ∀ t : Fin 2, Fin.castLE (by decide : 2 ≤ 3) t ≠ 2 := by decide
  refine ⟨J, hJ_sub, hJ_U, ⟨extend, ?_⟩, ?_⟩
  · intro f hf
    by_cases hfe : f = e
    · subst f
      refine ⟨a, ha, b, hb, ?_⟩
      rw [hA, hOther b hab.symm]
      exact (hDifferent _).symm
    · obtain ⟨x, hx, y, hy, hxy⟩ := hcol f (Finset.mem_erase.mpr ⟨hfe, hf⟩)
      refine ⟨x, hx, y, hy, ?_⟩
      have hne : x ≠ y := fun h => hxy (congrArg col h)
      by_cases hxa : x = a
      · subst x
        rw [hA, hOther y hne.symm]
        exact (hDifferent _).symm
      · rw [hOther x hxa]
        by_cases hya : y = a
        · subst y
          rw [hA]
          exact hDifferent _
        · rw [hOther y hya]
          exact (Fin.castLE_injective (by decide : 2 ≤ 3)).ne hxy
  · intro j hj hJcol
    obtain ⟨c, hc⟩ := hJcol
    have hj' : j ≤ 2 := by omega
    apply hJ_not
    refine ⟨fun x => Fin.castLE hj' (c x), ?_⟩
    intro f hf
    obtain ⟨x, hx, y, hy, hxy⟩ := hc f hf
    exact ⟨x, hx, y, hy, (Fin.castLE_injective hj').ne hxy⟩

lemma OMA.property_b_finite_witness (k : ℕ) (hk : 2 ≤ k) :
    ∃ (m : ℕ) (H : Finset (Finset (Fin m))), H.IsUniform k ∧ H.HasHypergraphChromaticNumber 3 := by
  classical
  let m := 2 * k - 1
  let H := (Finset.univ : Finset (Fin m)).powersetCard k
  have hU : H.IsUniform k := fun e he => (Finset.mem_powersetCard.mp he).2
  have hNot : ¬ H.HypergraphColorable 2 := by
    rintro ⟨c, hc⟩
    let A : Finset (Fin m) := Finset.univ.filter fun x => c x = 0
    let B : Finset (Fin m) := Finset.univ \ A
    have hB : B.card = m - A.card := by
      dsimp [B]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hmono (b : Fin 2) (S : Finset (Fin m)) (hs : k ≤ S.card)
        (hcol : ∀ x ∈ S, c x = b) : False := by
      obtain ⟨e, heS, heCard⟩ := Finset.exists_subset_card_eq hs
      have he : e ∈ H := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heCard⟩
      obtain ⟨x, hx, y, hy, hne⟩ := hc e he
      exact hne ((hcol x (heS hx)).trans (hcol y (heS hy)).symm)
    by_cases hA : k ≤ A.card
    · exact hmono 0 A hA (fun x hx => (Finset.mem_filter.mp hx).2)
    · have hBcard : k ≤ B.card := by dsimp [m] at hB; omega
      apply hmono 1 B hBcard
      intro x hx
      have hxA := (Finset.mem_sdiff.mp hx).2
      have hx0 : c x ≠ 0 := fun h => hxA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hcases : ∀ t : Fin 2, t ≠ 0 → t = 1 := by decide
      exact hcases _ hx0
  obtain ⟨J, _, hJ_U, hJ_col⟩ := OMA.property_b_extract_three H k hk hU hNot
  exact ⟨m, J, hJ_U, hJ_col⟩

lemma OMA.property_b_min_le {k m : ℕ} (H : Finset (Finset (Fin m))) (hU : H.IsUniform k)
    (hC : H.HasHypergraphChromaticNumber 3) :
    Hypergraph.minChromaticEdges k 3 ≤ (H.card : ENat) := by
  unfold Hypergraph.minChromaticEdges
  exact iInf_le_of_le m (iInf_le_of_le H (iInf_le_of_le hU (iInf_le_of_le hC le_rfl)))

lemma OMA.property_b_min_attains (k : ℕ) (hk : 2 ≤ k) :
    ∃ (m : ℕ) (H : Finset (Finset (Fin m))), H.IsUniform k ∧ H.HasHypergraphChromaticNumber 3 ∧
      Hypergraph.minChromaticEdges k 3 = (H.card : ENat) := by
  let sizes : Set ℕ := {d | ∃ (m : ℕ) (J : Finset (Finset (Fin m))),
    J.IsUniform k ∧ J.HasHypergraphChromaticNumber 3 ∧ J.card = d}
  obtain ⟨m₀, H₀, hU₀, hC₀⟩ := OMA.property_b_finite_witness k hk
  have hs : sizes.Nonempty := ⟨H₀.card, m₀, H₀, hU₀, hC₀, rfl⟩
  obtain ⟨m, H, hU, hC, hCard⟩ := Nat.sInf_mem hs
  refine ⟨m, H, hU, hC, le_antisymm (OMA.property_b_min_le H hU hC) ?_⟩
  rw [hCard]
  unfold Hypergraph.minChromaticEdges
  refine le_iInf fun n => le_iInf fun J => le_iInf fun hJ_U => le_iInf fun hJ_C => ?_
  exact_mod_cast (Nat.sInf_le (show J.card ∈ sizes from ⟨n, J, hJ_U, hJ_C, rfl⟩))

lemma OMA.property_b_choosable_mono {V : Type*} {G : SimpleGraph V} {k l : ℕ}
    (hkl : k ≤ l) (hk : G.IsKChoosable k) : G.IsKChoosable l := by
  intro L hL
  have hex (v : V) : ∃ M ⊆ L v, (M : Finset ℕ).card = k :=
    Finset.exists_subset_card_eq (by rw [hL]; exact hkl)
  choose M hM_sub hM_card using hex
  obtain ⟨C, hC⟩ := hk M hM_card
  exact ⟨C, fun v => hM_sub v (hC v)⟩

lemma OMA.property_b_finite_choosable {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.IsKChoosable (Fintype.card V) := by
  intro L hL
  have hHall (S : Finset V) : S.card ≤ (S.biUnion L).card := by
    by_cases hS : S.Nonempty
    · obtain ⟨v, hv⟩ := hS
      calc
        S.card ≤ Fintype.card V := Finset.card_le_univ S
        _ = (L v).card := (hL v).symm
        _ ≤ (S.biUnion L).card := Finset.card_le_card fun c hc =>
          Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
    · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hEmpty]
  obtain ⟨c, hc_inj, hc_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hHall
  exact ⟨Coloring.mk c (fun h => hc_inj.ne h.ne), hc_mem⟩

lemma OMA.property_b_to_bipartite {k m : ℕ} (H : Finset (Finset (Fin m)))
    (hU : H.IsUniform k) (hNot : ¬ H.HypergraphColorable 2) :
    ∃ G : SimpleGraph (Fin (2 * H.card)), G.Colorable 2 ∧ k < G.listChromaticNumber := by
  classical
  let e : Fin (2 * H.card) ≃ Fin 2 × ↥H :=
    Fintype.equivOfCardEq (by simp [Fintype.card_prod])
  let G : SimpleGraph (Fin (2 * H.card)) :=
    { Adj := fun a b => (e a).1 ≠ (e b).1
      symm := ⟨fun _ _ h => Ne.symm h⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  let L (v : Fin (2 * H.card)) : Finset ℕ := (e v).2.val.map Fin.valEmbedding
  have hL (v : Fin (2 * H.card)) : (L v).card = k := by
    rw [show L v = (e v).2.val.map Fin.valEmbedding from rfl, Finset.card_map]
    exact hU _ (e v).2.property
  have hBad : ¬ G.IsKChoosable k := by
    intro h
    obtain ⟨C, hC⟩ := h L hL
    let color (x : Fin m) : Fin 2 :=
      if ∃ ed : ↥H, C (e.symm (0, ed)) = x.val then 0 else 1
    apply hNot
    refine ⟨color, ?_⟩
    intro edge he
    let E : ↥H := ⟨edge, he⟩
    have hleft : C (e.symm (0, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (0, E))
    have hright : C (e.symm (1, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (1, E))
    obtain ⟨x, hx, hx_eq⟩ := Finset.mem_map.mp hleft
    obtain ⟨y, hy, hy_eq⟩ := Finset.mem_map.mp hright
    have h0 : color x = 0 := if_pos ⟨E, hx_eq.symm⟩
    have h1 : color y = 1 := by
      apply if_neg
      rintro ⟨F, hF⟩
      have hAdj : G.Adj (e.symm (0, F)) (e.symm (1, E)) := by
        change (e (e.symm (0, F))).1 ≠ (e (e.symm (1, E))).1
        simp
      exact C.valid hAdj (hF.trans hy_eq)
    exact ⟨x, hx, y, hy, by rw [h0, h1]; decide⟩
  have hs : {j : ℕ | G.IsKChoosable j}.Nonempty :=
    ⟨Fintype.card (Fin (2 * H.card)), OMA.property_b_finite_choosable G⟩
  have hmin : G.IsKChoosable G.listChromaticNumber := Nat.sInf_mem hs
  refine ⟨G, ⟨Coloring.mk (fun v => (e v).1) (fun h => h)⟩, ?_⟩
  by_contra! hle
  exact hBad (OMA.property_b_choosable_mono hle hmin)

lemma OMA.property_b_from_bipartite {k n : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin n))
    (hG : G.Colorable 2) (hBad : ¬ G.IsKChoosable k) :
    ∃ (m : ℕ) (H : Finset (Finset (Fin m))), H.IsUniform k ∧ H.HasHypergraphChromaticNumber 3 ∧ H.card ≤ n := by
  classical
  have hObstruction : ∃ L : Fin n → Finset ℕ, (∀ v, (L v).card = k) ∧
      ¬ ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v := by
    by_contra h
    apply hBad
    intro L hL
    by_contra hC
    exact h ⟨L, hL, hC⟩
  obtain ⟨L, hL, hNo⟩ := hObstruction
  obtain ⟨C⟩ := hG
  let P := (Finset.univ : Finset (Fin n)).biUnion L
  let e : ↥P ≃ Fin P.card := Fintype.equivFinOfCardEq (by simp)
  have hsub (v : Fin n) : L v ⊆ P := fun x hx =>
    Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hx⟩
  let mapColor (v : Fin n) : ↥(L v) ↪ Fin P.card :=
    ⟨fun x => e ⟨x.val, hsub v x.property⟩,
      fun _ _ h => Subtype.ext (congrArg (fun p : ↥P => p.val) (e.injective h))⟩
  let lists (v : Fin n) := (L v).attach.map (mapColor v)
  let H := (Finset.univ : Finset (Fin n)).image lists
  have hU : H.IsUniform k := by
    intro edge he
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
    dsimp [lists]
    rw [Finset.card_map, Finset.card_attach, hL]
  have hNot : ¬ H.HypergraphColorable 2 := by
    rintro ⟨c, hc⟩
    have hget (v : Fin n) {t : Fin P.card} (ht : t ∈ lists v) :
        ∃ q : ↥P, q.val ∈ L v ∧ e q = t := by
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp ht
      exact ⟨⟨a.val, hsub v a.property⟩, a.property, ha⟩
    have hselect (v : Fin n) : ∃ q : ↥P, q.val ∈ L v ∧ c (e q) = C v := by
      have hvH : lists v ∈ H := Finset.mem_image_of_mem lists (Finset.mem_univ _)
      obtain ⟨x, hx, y, hy, hxy⟩ := hc (lists v) hvH
      have hcases : ∀ a b d : Fin 2, a ≠ b → a = d ∨ b = d := by decide
      rcases hcases (c x) (c y) (C v) hxy with hal | har
      · obtain ⟨q, hq, hqe⟩ := hget v hx
        exact ⟨q, hq, hqe.symm ▸ hal⟩
      · obtain ⟨q, hq, hqe⟩ := hget v hy
        exact ⟨q, hq, hqe.symm ▸ har⟩
    choose q hqL hqColor using hselect
    have hValid : ∀ {a b}, G.Adj a b → (q a).val ≠ (q b).val := by
      intro a b hab heq
      have hqEq : q a = q b := Subtype.ext heq
      apply C.valid hab
      rw [← hqColor a, ← hqColor b, hqEq]
    exact hNo ⟨Coloring.mk (fun v => (q v).val) hValid, hqL⟩
  obtain ⟨J, hSub, hJ_U, hJ_col⟩ := OMA.property_b_extract_three H k hk hU hNot
  have hH_card : H.card ≤ n := by
    exact Finset.card_image_le.trans_eq (by simp)
  exact ⟨P.card, J, hJ_U, hJ_col, (Finset.card_le_card hSub).trans hH_card⟩

lemma OMA.property_b_main : ∀ k : ℕ, 2 ≤ k →
    (Hypergraph.minChromaticEdges k 3).toNat ≤ Erdos629.n k ∧
      Erdos629.n k ≤ 2 * (Hypergraph.minChromaticEdges k 3).toNat := by
  intro k hk
  obtain ⟨m, H, hU, hC, hmin⟩ := OMA.property_b_min_attains k hk
  have hNot : ¬ H.HypergraphColorable 2 := hC.2 2 (by decide)
  obtain ⟨G, hG, hGList⟩ := OMA.property_b_to_bipartite H hU hNot
  have hUpper : Erdos629.n k ≤ 2 * H.card := Erdos629.n_le G hG hGList
  have hex : {v : ℕ | ∃ J : SimpleGraph (Fin v),
      J.Colorable 2 ∧ k < J.listChromaticNumber}.Nonempty :=
    ⟨2 * H.card, G, hG, hGList⟩
  have hGmin : ∃ J : SimpleGraph (Fin (Erdos629.n k)),
      J.Colorable 2 ∧ k < J.listChromaticNumber := Nat.sInf_mem hex
  obtain ⟨J, hJ, hJList⟩ := hGmin
  have hJBad : ¬ J.IsKChoosable k := fun h =>
    (not_le_of_gt hJList) (Nat.sInf_le h)
  obtain ⟨_, K, hK_U, hK_C, hK_card⟩ := OMA.property_b_from_bipartite hk J hJ hJBad
  have hK_min := OMA.property_b_min_le K hK_U hK_C
  rw [hmin] at hK_min
  have hK_le : H.card ≤ K.card := by exact_mod_cast hK_min
  rw [hmin, ENat.toNat_natCast]
  exact ⟨hK_le.trans hK_card, hUpper⟩

namespace OMA

section RS

open Classical

/-- Weight functions whose coordinates in `S` lie in prescribed sets. -/
noncomputable def rsBox {n N : ℕ} (S : Finset (Fin n)) (T : Fin n → Finset (Fin N)) :
    Finset (Fin n → Fin N) :=
  Finset.univ.filter (fun w => ∀ u ∈ S, w u ∈ T u)

lemma rs_mem_box {n N : ℕ} (S : Finset (Fin n)) (T : Fin n → Finset (Fin N))
    (w : Fin n → Fin N) : w ∈ rsBox S T ↔ ∀ u ∈ S, w u ∈ T u := by
  simp [rsBox]

lemma rs_box {n N : ℕ} (hN : 0 < N) (S : Finset (Fin n)) (T : Fin n → Finset (Fin N)) :
    ((rsBox S T).card : ℝ) = (∏ u ∈ S, ((T u).card : ℝ) / N) * (N : ℝ) ^ n := by
  have h1 : rsBox S T = Fintype.piFinset (fun u => if u ∈ S then T u else Finset.univ) := by
    ext w
    rw [rs_mem_box, Fintype.mem_piFinset]
    constructor
    · intro h u
      by_cases hu : u ∈ S
      · simp [hu, h u hu]
      · simp [hu]
    · intro h u hu
      have := h u
      simpa [hu] using this
  rw [h1, Fintype.card_piFinset]
  push_cast
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have h2 : ∀ u : Fin n, (((if u ∈ S then T u else Finset.univ : Finset (Fin N)).card : ℝ))
      = (if u ∈ S then ((T u).card : ℝ) / N else 1) * N := by
    intro u
    by_cases hu : u ∈ S
    · simp only [hu, if_true]
      field_simp
    · simp [hu]
  rw [Finset.prod_congr rfl (fun u _ => h2 u), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_ite_mem, Finset.univ_inter]

lemma rs_cardA {n N k : ℕ} (hN : 0 < N) (e : Finset (Fin n)) (he : e.card = k)
    (A : Finset (Fin N)) :
    ((rsBox e (fun _ => A)).card : ℝ) = ((A.card : ℝ) / N) ^ k * (N : ℝ) ^ n := by
  rw [rs_box hN e (fun _ => A), Finset.prod_const, he]

lemma rs_cardD {n N : ℕ} (hN : 0 < N) (u v : Fin n) (huv : u ≠ v) :
    (((Finset.univ : Finset (Fin n → Fin N)).filter (fun w => w u = w v)).card : ℝ)
      ≤ (1 / N) * (N : ℝ) ^ n := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hsub : (Finset.univ : Finset (Fin n → Fin N)).filter (fun w => w u = w v)
      ⊆ (Finset.univ : Finset (Fin N)).biUnion (fun x =>
          rsBox ({u, v} : Finset (Fin n)) (fun _ => ({x} : Finset (Fin N)))) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, rs_mem_box]
    refine ⟨w v, ?_⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [hw]
    · simp
  have h1 : (((Finset.univ : Finset (Fin n → Fin N)).filter (fun w => w u = w v)).card : ℝ)
      ≤ ∑ x : Fin N, ((rsBox ({u, v} : Finset (Fin n))
          (fun _ => ({x} : Finset (Fin N)))).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  refine h1.trans (le_of_eq ?_)
  have h2 : ∀ x : Fin N, ((rsBox ({u, v} : Finset (Fin n))
      (fun _ => ({x} : Finset (Fin N)))).card : ℝ) = (1 / N) ^ 2 * (N : ℝ) ^ n := by
    intro x
    rw [rs_box hN, Finset.prod_pair huv]
    simp only [Finset.card_singleton, Nat.cast_one]
    ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma rs_cardC {n N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k) (e f : Finset (Fin n))
    (he : e.card = k) (hf : f.card = k) (a b : Fin N) :
    (((Finset.univ : Finset (Fin n → Fin N)).filter (fun w => ∃ v, e ∩ f = {v} ∧ a ≤ w v ∧
        w v < b ∧ (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u))).card : ℝ)
      ≤ (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) *
          (1 / N * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1)) * (N : ℝ) ^ n := by
  have hN' : (0 : ℝ) < N := by positivity
  set q : ℝ := 1 / N * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1) with hq
  have hq0 : 0 ≤ q := by positivity
  by_cases hex : ∃ v0, e ∩ f = {v0}
  · obtain ⟨v0, hv0⟩ := hex
    have hv0e : v0 ∈ e := (Finset.mem_inter.mp (by rw [hv0]; simp)).1
    have hv0f : v0 ∈ f := (Finset.mem_inter.mp (by rw [hv0]; simp)).2
    set T : Fin N → Fin n → Finset (Fin N) := fun x u =>
      if u = v0 then {x} else if u ∈ e then Finset.Iic x else Finset.Ici x with hT
    have hsub : (Finset.univ : Finset (Fin n → Fin N)).filter (fun w => ∃ v, e ∩ f = {v} ∧
        a ≤ w v ∧ w v < b ∧ (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u))
        ⊆ (Finset.Ico a b).biUnion (fun x => rsBox (e ∪ f) (T x)) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨v, hv, hav, hvb, hle, hge⟩ := hw
      have hvv : v = v0 := by
        have : ({v} : Finset (Fin n)) = {v0} := by rw [← hv, hv0]
        exact Finset.singleton_injective this
      subst hvv
      simp only [Finset.mem_biUnion, Finset.mem_Ico, rs_mem_box]
      refine ⟨w v, ⟨hav, hvb⟩, ?_⟩
      intro u hu
      by_cases huv : u = v
      · simp [hT, huv]
      · by_cases hue : u ∈ e
        · simp [hT, huv, hue, hle u hue]
        · have huf : u ∈ f := by
            rcases Finset.mem_union.mp hu with h | h
            · exact absurd h hue
            · exact h
          simp [hT, huv, hue, hge u huf]
    have hbox : ∀ x : Fin N, ((rsBox (e ∪ f) (T x)).card : ℝ) ≤ q * (N : ℝ) ^ n := by
      intro x
      rw [rs_box hN]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hunion : e ∪ f = e ∪ (f \ e) := by simp
      have hdisj : Disjoint e (f \ e) := Finset.disjoint_sdiff
      rw [hunion, Finset.prod_union hdisj, ← Finset.mul_prod_erase e _ hv0e]
      have hx1 : ((x : ℕ) : ℝ) + 1 ≤ N := by
        have := x.2
        exact_mod_cast this
      have p1 : (((T x v0).card : ℝ) / N) = 1 / N := by simp [hT]
      have p2 : ∏ u ∈ e.erase v0, (((T x u).card : ℝ) / N)
          = ((((x : ℕ) : ℝ) + 1) / N) ^ (k - 1) := by
        have : ∀ u ∈ e.erase v0, (((T x u).card : ℝ) / N) = (((x : ℕ) : ℝ) + 1) / N := by
          intro u hu
          have hu1 := (Finset.mem_erase.mp hu).1
          have hu2 := (Finset.mem_erase.mp hu).2
          simp [hT, hu1, hu2, Fin.card_Iic]
        rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_erase_of_mem hv0e, he]
      have p3 : ∏ u ∈ f \ e, (((T x u).card : ℝ) / N)
          = (((N : ℝ) - (x : ℕ)) / N) ^ (k - 1) := by
        have : ∀ u ∈ f \ e, (((T x u).card : ℝ) / N) = ((N : ℝ) - (x : ℕ)) / N := by
          intro u hu
          have hu1 := (Finset.mem_sdiff.mp hu).2
          have hu2 : u ≠ v0 := fun h => hu1 (h ▸ hv0e)
          have hxN : (x : ℕ) ≤ N := x.2.le
          simp [hT, hu1, hu2, Fin.card_Ici, Nat.cast_sub hxN]
        have hcard : (f \ e).card = k - 1 := by
          have h1 := Finset.card_sdiff_add_card_inter f e
          rw [Finset.inter_comm, hv0, Finset.card_singleton, hf] at h1
          omega
        rw [Finset.prod_congr rfl this, Finset.prod_const, hcard]
      rw [p1, p2, p3, hq, mul_assoc, ← mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine pow_le_pow_left₀ (by
        have : (0 : ℝ) ≤ (N : ℝ) - (x : ℕ) := by linarith
        positivity) ?_ _
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : (((x : ℕ) : ℝ) + 1) * ((N : ℝ) - (x : ℕ)) * 4 ≤ ((N : ℝ) + 1) ^ 2 := by
        nlinarith [sq_nonneg ((((x : ℕ) : ℝ) + 1) - ((N : ℝ) - (x : ℕ)))]
      have h5 : (0 : ℝ) ≤ (N : ℝ) * N := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h4 h5]
    have h1 : (((Finset.univ : Finset (Fin n → Fin N)).filter (fun w => ∃ v, e ∩ f = {v} ∧
        a ≤ w v ∧ w v < b ∧ (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u))).card : ℝ)
        ≤ ∑ x ∈ Finset.Ico a b, ((rsBox (e ∪ f) (T x)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    refine h1.trans ?_
    refine (Finset.sum_le_sum (fun x _ => hbox x)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Fin.card_Ico, nsmul_eq_mul]
    ring
  · have hempty : (Finset.univ : Finset (Fin n → Fin N)).filter (fun w => ∃ v, e ∩ f = {v} ∧
        a ≤ w v ∧ w v < b ∧ (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro w - ⟨v, hv, -⟩
      exact hex ⟨v, hv⟩
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

lemma rs_criterion {n N : ℕ} (H : Finset (Finset (Fin n))) (w : Fin n → Fin N)
    (hne : ∀ e ∈ H, e.Nonempty)
    (hno : ∀ e ∈ H, ∀ f ∈ H, ∀ v, v ∈ e → v ∈ f → (∀ u ∈ e, w u ≤ w v) →
      (∀ u ∈ f, w v ≤ w u) → False) :
    H.HypergraphColorable 2 := by
  refine ⟨fun v => if ∃ e ∈ H, v ∈ e ∧ ∀ u ∈ e, w u ≤ w v then 1 else 0, ?_⟩
  intro f hf
  obtain ⟨vmax, hvmax, hmax⟩ := Finset.exists_max_image f w (hne f hf)
  obtain ⟨vmin, hvmin, hmin⟩ := Finset.exists_min_image f w (hne f hf)
  refine ⟨vmin, hvmin, vmax, hvmax, ?_⟩
  have h1 : (∃ e ∈ H, vmax ∈ e ∧ ∀ u ∈ e, w u ≤ w vmax) := ⟨f, hf, hvmax, hmax⟩
  have h0 : ¬ (∃ e ∈ H, vmin ∈ e ∧ ∀ u ∈ e, w u ≤ w vmin) := by
    rintro ⟨e, he, hve, hle⟩
    exact hno e he f hf vmin hve hvmin hle hmin
  show (if ∃ e ∈ H, vmin ∈ e ∧ ∀ u ∈ e, w u ≤ w vmin then (1 : Fin 2) else 0)
    ≠ (if ∃ e ∈ H, vmax ∈ e ∧ ∀ u ∈ e, w u ≤ w vmax then (1 : Fin 2) else 0)
  rw [if_neg h0, if_pos h1]
  decide

lemma rs_good_weight {n N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k) (H : Finset (Finset (Fin n)))
    (hU : H.IsUniform k) (a b : Fin N)
    (hsum : (H.card : ℝ) * (((a : ℕ) : ℝ) / N) ^ k
        + (H.card : ℝ) * (((N - (b : ℕ) : ℕ) : ℝ) / N) ^ k
        + (H.card : ℝ) ^ 2 * ((((b : ℕ) - (a : ℕ) : ℕ) : ℝ) *
            (1 / N * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1)))
        + (n : ℝ) ^ 2 * (1 / N) < 1) :
    ∃ w : Fin n → Fin N,
      (∀ e ∈ H, ¬ ∀ u ∈ e, w u < a) ∧ (∀ e ∈ H, ¬ ∀ u ∈ e, b ≤ w u) ∧
      (∀ e ∈ H, ∀ f ∈ H, ∀ v, e ∩ f = {v} → a ≤ w v → w v < b → (∀ u ∈ e, w u ≤ w v) →
        (∀ u ∈ f, w v ≤ w u) → False) ∧
      Function.Injective w := by
  set X1 := H.biUnion (fun e => rsBox e (fun _ => Finset.Iio a)) with hX1
  set X2 := H.biUnion (fun e => rsBox e (fun _ => Finset.Ici b)) with hX2
  set C : Finset (Fin n) → Finset (Fin n) → Finset (Fin n → Fin N) := fun e f =>
    Finset.univ.filter (fun w => ∃ v, e ∩ f = {v} ∧ a ≤ w v ∧ w v < b ∧
      (∀ u ∈ e, w u ≤ w v) ∧ (∀ u ∈ f, w v ≤ w u)) with hC
  set X3 := (H ×ˢ H).biUnion (fun p => C p.1 p.2) with hX3
  set D : Fin n × Fin n → Finset (Fin n → Fin N) := fun p =>
    Finset.univ.filter (fun w => w p.1 = w p.2) with hD
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) with hP
  set X4 := P.biUnion D with hX4
  set Nn : ℝ := (N : ℝ) ^ n with hNn
  have hNn0 : 0 < Nn := by positivity
  have c1 : (X1.card : ℝ) ≤ (H.card : ℝ) * (((a : ℕ) : ℝ) / N) ^ k * Nn := by
    have h : (X1.card : ℝ) ≤ ∑ e ∈ H, ((rsBox e (fun _ => Finset.Iio a)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine h.trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl (fun e he => rs_cardA hN e (hU e he) (Finset.Iio a)),
      Finset.sum_const, nsmul_eq_mul, Fin.card_Iio]
    ring
  have c2 : (X2.card : ℝ) ≤ (H.card : ℝ) * (((N - (b : ℕ) : ℕ) : ℝ) / N) ^ k * Nn := by
    have h : (X2.card : ℝ) ≤ ∑ e ∈ H, ((rsBox e (fun _ => Finset.Ici b)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine h.trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl (fun e he => rs_cardA hN e (hU e he) (Finset.Ici b)),
      Finset.sum_const, nsmul_eq_mul, Fin.card_Ici]
    ring
  have c3 : (X3.card : ℝ) ≤ (H.card : ℝ) ^ 2 * ((((b : ℕ) - (a : ℕ) : ℕ) : ℝ) *
      (1 / N * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1))) * Nn := by
    have h : (X3.card : ℝ) ≤ ∑ p ∈ H ×ˢ H, ((C p.1 p.2).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine h.trans ?_
    have hb : ∀ p ∈ H ×ˢ H, ((C p.1 p.2).card : ℝ) ≤
        (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) *
          (1 / N * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1)) * Nn := fun p hp =>
      rs_cardC hN hk p.1 p.2 (hU _ (Finset.mem_product.mp hp).1)
        (hU _ (Finset.mem_product.mp hp).2) a b
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  have c4 : (X4.card : ℝ) ≤ (n : ℝ) ^ 2 * (1 / N) * Nn := by
    have h : (X4.card : ℝ) ≤ ∑ p ∈ P, ((D p).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine h.trans ?_
    have hb : ∀ p ∈ P, ((D p).card : ℝ) ≤ (1 / N) * Nn := fun p hp =>
      rs_cardD hN p.1 p.2 (Finset.mem_filter.mp hp).2
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hPc : (P.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h1 : P.card ≤ n * n := by
        calc P.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_filter_le _ _
          _ = n * n := by simp
      have h2 : (P.card : ℝ) ≤ (n : ℝ) * n := by exact_mod_cast h1
      nlinarith
    have h0 : 0 ≤ (1 / N : ℝ) * Nn := by positivity
    nlinarith
  have htot : ((X1 ∪ X2 ∪ X3 ∪ X4).card : ℝ) < Nn := by
    have hu : ((X1 ∪ X2 ∪ X3 ∪ X4).card : ℝ) ≤ X1.card + X2.card + X3.card + X4.card := by
      have h1 := Finset.card_union_le (X1 ∪ X2 ∪ X3) X4
      have h2 := Finset.card_union_le (X1 ∪ X2) X3
      have h3 := Finset.card_union_le X1 X2
      exact_mod_cast (by omega :
        (X1 ∪ X2 ∪ X3 ∪ X4).card ≤ X1.card + X2.card + X3.card + X4.card)
    have h5 := mul_lt_mul_of_pos_right hsum hNn0
    nlinarith
  have hex : ∃ w, w ∉ X1 ∪ X2 ∪ X3 ∪ X4 := by
    by_contra hcon
    push_neg at hcon
    have huniv : X1 ∪ X2 ∪ X3 ∪ X4 = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon
    have hc : ((Finset.univ : Finset (Fin n → Fin N)).card : ℝ) = Nn := by
      simp [hNn]
    rw [huniv, hc] at htot
    exact lt_irrefl _ htot
  obtain ⟨w, hw⟩ := hex
  simp only [Finset.mem_union, not_or] at hw
  obtain ⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩ := hw
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro e he hall
    exact hw1 (Finset.mem_biUnion.mpr ⟨e, he, (rs_mem_box _ _ _).mpr
      (fun u hu => Finset.mem_Iio.mpr (hall u hu))⟩)
  · intro e he hall
    exact hw2 (Finset.mem_biUnion.mpr ⟨e, he, (rs_mem_box _ _ _).mpr
      (fun u hu => Finset.mem_Ici.mpr (hall u hu))⟩)
  · intro e he f hf v hv hav hvb hle hge
    refine hw3 (Finset.mem_biUnion.mpr ⟨(e, f), Finset.mem_product.mpr ⟨he, hf⟩, ?_⟩)
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, hav, hvb, hle, hge⟩
  · intro u v huv
    by_contra hne
    refine hw4 (Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hne⟩, ?_⟩)
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
    exact huv

lemma rs_param {n k L : ℕ} (hk : 2 ≤ k) (hL : L < 2 * k) (m : ℝ) (hm0 : 0 ≤ m)
    (hineq : 2 * (m / 2 ^ k) * Real.exp (-(L : ℝ) / 2)
        + 4 * (m / 2 ^ k) ^ 2 * L / k + 1 / (4 * k) < 1)
    (T : ℕ) (hT : T = n ^ 2 + 1) (N : ℕ) (hNdef : N = 4 * k * T)
    (av bv : ℕ) (hav : av = (2 * k - L) * T) (hbv : bv = (2 * k + L) * T) :
    m * ((av : ℝ) / N) ^ k + m * (((N - bv : ℕ) : ℝ) / N) ^ k
      + m ^ 2 * ((((bv - av : ℕ)) : ℝ) *
          (1 / N * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1)))
      + (n : ℝ) ^ 2 * (1 / N) < 1 := by
  have hT0 : 0 < T := by omega
  have hk0 : 0 < k := by omega
  have hLk : L ≤ 2 * k := hL.le
  have hbN : bv ≤ N := by
    rw [hbv, hNdef]
    exact Nat.mul_le_mul_right T (by omega)
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT0
  have hKr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hNr : (N : ℝ) = 4 * k * T := by rw [hNdef]; push_cast; ring
  have hLr : (L : ℝ) ≤ 2 * k := by exact_mod_cast hLk
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have har : (av : ℝ) = (2 * k - L) * T := by
    rw [hav, Nat.cast_mul, Nat.cast_sub hLk]; push_cast; ring
  have hbr : (((N - bv : ℕ)) : ℝ) = (2 * k - L) * T := by
    rw [Nat.cast_sub hbN, hbv, hNr]; push_cast; ring
  have hba : ((((bv - av : ℕ))) : ℝ) = 2 * L * T := by
    have hle : av ≤ bv := by
      rw [hav, hbv]; exact Nat.mul_le_mul_right T (by omega)
    rw [Nat.cast_sub hle, hav, hbv, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hLk]
    push_cast; ring
  set P : ℝ := (2 : ℝ) ^ (k - 1) with hPdef
  have hP0 : 0 < P := by positivity
  have h2k : (2 : ℝ) ^ k = 2 * P := by
    rw [hPdef, ← pow_succ']
    congr 1
    omega
  set E : ℝ := Real.exp (-(L : ℝ) / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hx : (2 * (k : ℝ) - L) * T / (4 * k * T) = (1 / 2) * (1 - (L : ℝ) / (2 * k)) := by
    field_simp
    ring
  have hx0 : 0 ≤ 1 - (L : ℝ) / (2 * k) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hLr
  have hpow : (1 - (L : ℝ) / (2 * k)) ^ k ≤ E := by
    calc (1 - (L : ℝ) / (2 * k)) ^ k ≤ (Real.exp (-((L : ℝ) / (2 * k)))) ^ k :=
          pow_le_pow_left₀ hx0 (Real.one_sub_le_exp_neg _) k
      _ = Real.exp (k * (-((L : ℝ) / (2 * k)))) := (Real.exp_nat_mul _ k).symm
      _ = E := by
          rw [hE]
          congr 1
          field_simp
  have hhalf : ((1 : ℝ) / 2) ^ k = 1 / (2 * P) := by
    rw [one_div_pow, h2k]
  have hA : ((2 * (k : ℝ) - L) * T / (4 * k * T)) ^ k ≤ 1 / (2 * P) * E := by
    rw [hx, mul_pow, hhalf]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hquarter : ((1 : ℝ) / 4) ^ (k - 1) = 1 / P ^ 2 := by
    rw [hPdef, one_div_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hNpos : (0 : ℝ) < N := by rw [hNr]; positivity
  have hexp2 : Real.exp (1 / 2) ≤ 2 := by
    have h1 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    calc Real.exp (1 / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h1
      _ = 2 := Real.exp_log (by norm_num)
  have hCb : (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1) ≤ 2 * (1 / P ^ 2) := by
    have h1 : ((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2) = (1 / 4) * (1 + 1 / (N : ℝ)) ^ 2 := by
      field_simp
    rw [h1, mul_pow, hquarter]
    have h2 : ((1 + 1 / (N : ℝ)) ^ 2) ^ (k - 1) ≤ 2 := by
      have h3 : 1 + 1 / (N : ℝ) ≤ Real.exp (1 / (N : ℝ)) := by
        have := Real.add_one_le_exp (1 / (N : ℝ))
        linarith
      have h4 : (0 : ℝ) ≤ 1 + 1 / (N : ℝ) := by positivity
      calc ((1 + 1 / (N : ℝ)) ^ 2) ^ (k - 1) = (1 + 1 / (N : ℝ)) ^ (2 * (k - 1)) := by
            rw [← pow_mul]
        _ ≤ (Real.exp (1 / (N : ℝ))) ^ (2 * (k - 1)) := pow_le_pow_left₀ h4 h3 _
        _ = Real.exp (((2 * (k - 1) : ℕ) : ℝ) * (1 / (N : ℝ))) :=
            (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (1 / 2) := by
            apply Real.exp_le_exp.mpr
            have h5 : (((2 * (k - 1) : ℕ)) : ℝ) ≤ 2 * k := by
              have : 2 * (k - 1) ≤ 2 * k := by omega
              exact_mod_cast this
            have h6 : (4 : ℝ) * k ≤ N := by
              rw [hNr]
              have h8 : (0 : ℝ) ≤ 4 * k := by positivity
              have h9 := mul_le_mul_of_nonneg_left hTr h8
              linarith
            rw [mul_one_div, div_le_iff₀ hNpos]
            linarith
        _ ≤ 2 := hexp2
    have h7 : (0 : ℝ) ≤ 1 / P ^ 2 := by positivity
    calc 1 / P ^ 2 * ((1 + 1 / (N : ℝ)) ^ 2) ^ (k - 1) ≤ 1 / P ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left h2 h7
      _ = 2 * (1 / P ^ 2) := by ring
  have hDb : (n : ℝ) ^ 2 * (1 / N) ≤ 1 / (4 * k) := by
    have h1 : (n : ℝ) ^ 2 ≤ T := by
      rw [hT]; push_cast; linarith
    rw [hNr, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (0 : ℝ) ≤ 4 * k := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have t1 : m * ((av : ℝ) / N) ^ k ≤ m * (1 / (2 * P) * E) := by
    rw [har, hNr]
    exact mul_le_mul_of_nonneg_left hA hm0
  have t2 : m * (((N - bv : ℕ) : ℝ) / N) ^ k ≤ m * (1 / (2 * P) * E) := by
    rw [hbr, hNr]
    exact mul_le_mul_of_nonneg_left hA hm0
  have t3 : m ^ 2 * ((((bv - av : ℕ)) : ℝ) *
      (1 / N * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ (k - 1)))
      ≤ m ^ 2 * (2 * L * T * (1 / N * (2 * (1 / P ^ 2)))) := by
    rw [hba]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hCb (by positivity)
  have hfinal : 2 * (m / (2 * P)) * E + 4 * (m / (2 * P)) ^ 2 * L / k + 1 / (4 * k) < 1 := by
    rw [h2k] at hineq
    exact hineq
  have heq : m * (1 / (2 * P) * E) + m * (1 / (2 * P) * E)
      + m ^ 2 * (2 * L * T * (1 / N * (2 * (1 / P ^ 2)))) + 1 / (4 * k)
      = 2 * (m / (2 * P)) * E + 4 * (m / (2 * P)) ^ 2 * L / k + 1 / (4 * k) := by
    rw [hNr]
    field_simp
    ring
  linarith

lemma rs_core {n k : ℕ} (hk : 2 ≤ k) (H : Finset (Finset (Fin n))) (hU : H.IsUniform k)
    (L : ℕ) (hL : L < 2 * k)
    (hineq : 2 * ((H.card : ℝ) / 2 ^ k) * Real.exp (-(L : ℝ) / 2)
        + 4 * ((H.card : ℝ) / 2 ^ k) ^ 2 * L / k + 1 / (4 * k) < 1) :
    H.HypergraphColorable 2 := by
  set T : ℕ := n ^ 2 + 1 with hT
  set N : ℕ := 4 * k * T with hNdef
  have hT0 : 0 < T := by positivity
  have hk0 : 0 < k := by omega
  have hN : 0 < N := by positivity
  have hLk : L ≤ 2 * k := hL.le
  have ha : (2 * k - L) * T < N := by
    have h1 : (2 * k - L) * T ≤ 2 * k * T := Nat.mul_le_mul_right T (Nat.sub_le _ _)
    have h2 : 0 < k * T := Nat.mul_pos hk0 hT0
    rw [hNdef]
    nlinarith
  have hb : (2 * k + L) * T < N := by
    have h1 : (2 * k + L) * T < (4 * k) * T :=
      Nat.mul_lt_mul_of_pos_right (by omega) hT0
    rw [hNdef]
    exact h1
  have hsum := rs_param (n := n) hk hL (H.card : ℝ) (by positivity) hineq T hT N hNdef
    ((2 * k - L) * T) ((2 * k + L) * T) rfl rfl
  obtain ⟨w, hwA, hwB, hwC, hwI⟩ := rs_good_weight hN (by omega) H hU
    ⟨(2 * k - L) * T, ha⟩ ⟨(2 * k + L) * T, hb⟩ hsum
  apply rs_criterion H w
  · intro e he
    rw [← Finset.card_pos, hU e he]
    omega
  · intro e he f hf v hve hvf hle hge
    by_cases h1 : w v < ⟨(2 * k - L) * T, ha⟩
    · exact hwA e he (fun u hu => lt_of_le_of_lt (hle u hu) h1)
    · by_cases h2 : (⟨(2 * k + L) * T, hb⟩ : Fin N) ≤ w v
      · exact hwB f hf (fun u hu => le_trans h2 (hge u hu))
      · have hint : e ∩ f = {v} := by
          ext u
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨hue, huf⟩
            exact hwI (le_antisymm (hle u hue) (hge u huf))
          · rintro rfl
            exact ⟨hve, hvf⟩
        exact hwC e he f hf v hint (not_lt.mp h1) (not_le.mp h2) hle hge

lemma rs_numeric {k : ℕ} (hk : 3 ≤ k) (m : ℝ) (hm0 : 0 ≤ m)
    (hm : m < 1 / 8 * 2 ^ k * Real.sqrt (k / Real.log k)) :
    2 * (m / 2 ^ k) * Real.exp (-((Nat.log 2 k : ℕ) : ℝ) / 2)
      + 4 * (m / 2 ^ k) ^ 2 * ((Nat.log 2 k : ℕ) : ℝ) / k + 1 / (4 * k) < 1 := by
  set L : ℕ := Nat.log 2 k with hLdef
  have hK3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < (k : ℝ) := by linarith
  set x : ℝ := Real.log k with hxdef
  have hx1 : 1 ≤ x := by
    rw [hxdef, Real.le_log_iff_exp_le hK0]
    have := Real.exp_one_lt_d9
    linarith
  have hx0 : 0 < x := by linarith
  have h2pos : (0 : ℝ) < 2 ^ k := by positivity
  set M : ℝ := m / 2 ^ k with hMdef
  have hM0 : 0 ≤ M := by positivity
  set s : ℝ := Real.sqrt (k / x) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = k / x := Real.sq_sqrt (by positivity)
  have hMs : M < s / 8 := by
    rw [hMdef, div_lt_iff₀ h2pos]
    linarith
  have hM2 : M ^ 2 * (64 * x) ≤ k := by
    have h1 : M ^ 2 ≤ (s / 8) ^ 2 := pow_le_pow_left₀ hM0 hMs.le 2
    have h2 : (s / 8) ^ 2 = k / x / 64 := by rw [div_pow, hss]; norm_num
    rw [h2] at h1
    have h3 : k / x / 64 * (64 * x) = k := by field_simp
    nlinarith
  have hkne : k ≠ 0 := by omega
  have hL1 : (2 : ℝ) ^ L ≤ k := by
    have := Nat.pow_log_le_self 2 hkne
    exact_mod_cast this
  have hL2 : (k : ℝ) < 2 * 2 ^ L := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k
    rw [pow_succ] at this
    have h : (k : ℝ) < (2 : ℝ) ^ L * 2 := by exact_mod_cast this
    linarith
  have hLlog : (L : ℝ) * 0.69 ≤ x := by
    have h1 : Real.log ((2 : ℝ) ^ L) ≤ Real.log k := Real.log_le_log (by positivity) hL1
    rw [Real.log_pow] at h1
    have h2 := Real.log_two_gt_d9
    have h3 : (0 : ℝ) ≤ L := by positivity
    rw [hxdef]
    nlinarith
  have hexpL : (2 : ℝ) ^ L ≤ Real.exp L := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    calc (2 : ℝ) ^ L ≤ (Real.exp 1) ^ L := pow_le_pow_left₀ (by norm_num) h1 L
      _ = Real.exp L := by rw [← Real.exp_nat_mul, mul_one]
  set E : ℝ := Real.exp (-(L : ℝ) / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEE : E ^ 2 * Real.exp L = 1 := by
    rw [hE, sq, ← Real.exp_add, ← Real.exp_add]
    have : -(L : ℝ) / 2 + -(L : ℝ) / 2 + L = 0 := by ring
    rw [this, Real.exp_zero]
  have hexpLpos : 0 < Real.exp (L : ℝ) := Real.exp_pos _
  have hME : M * E < 1 / 5 := by
    have h1 : (M * E) ^ 2 * (64 * x) * Real.exp L ≤ 2 * Real.exp L := by
      have h2 : (M * E) ^ 2 * (64 * x) * Real.exp L
          = M ^ 2 * (64 * x) * (E ^ 2 * Real.exp L) := by
        ring
      rw [h2, hEE]
      nlinarith
    have h3 : (M * E) ^ 2 * (64 * x) ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have h4 : (M * E) ^ 2 < (1 / 5) ^ 2 := by
      have h5 : (M * E) ^ 2 * 64 ≤ (M * E) ^ 2 * (64 * x) := by
        have : 0 ≤ (M * E) ^ 2 := by positivity
        nlinarith
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h4
  have hterm2 : 4 * M ^ 2 * (L : ℝ) / k ≤ 1 / 10 := by
    rw [div_le_iff₀ hK0]
    have h1 : M ^ 2 * ((L : ℝ) * 0.69) ≤ M ^ 2 * x :=
      mul_le_mul_of_nonneg_left hLlog (by positivity)
    have h2 : 0 ≤ M ^ 2 * x := by positivity
    nlinarith
  have hterm3 : 1 / (4 * (k : ℝ)) ≤ 1 / 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  nlinarith

end RS

end OMA

theorem OMA.solution : type_of% @Erdos629.erdos_629.variants.radhakrishnan_srinivasan := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 3] with k hk
  have hk2 : 2 ≤ k := by omega
  obtain ⟨m, H, hU, hC, hmin⟩ := OMA.property_b_min_attains k hk2
  have hNot : ¬ H.HypergraphColorable 2 := hC.2 2 (by decide)
  have hle : (Hypergraph.minChromaticEdges k 3).toNat ≤ Erdos629.n k :=
    (OMA.property_b_main k hk2).1
  rw [hmin, ENat.toNat_natCast] at hle
  by_contra hcon
  have hcon' : (Erdos629.n k : ℝ) < 1 / 8 * 2 ^ k * Real.sqrt (k / Real.log k) :=
    not_le.mp hcon
  have hH : (H.card : ℝ) < 1 / 8 * 2 ^ k * Real.sqrt (k / Real.log k) :=
    lt_of_le_of_lt (by exact_mod_cast hle) hcon'
  have hLlt : Nat.log 2 k < 2 * k := by
    have := Nat.log_le_self 2 k
    omega
  exact hNot (OMA.rs_core hk2 H hU (Nat.log 2 k) hLlt
    (OMA.rs_numeric hk (H.card : ℝ) (by positivity) hH))
