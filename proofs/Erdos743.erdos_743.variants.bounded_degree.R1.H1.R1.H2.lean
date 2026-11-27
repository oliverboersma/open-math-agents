import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1

/-! Greedy extraction of disjoint bare paths. Root the tree anywhere and send
every vertex to a neighbour one step closer to the root. Let X be the
exceptional vertices together with the paths already chosen and the root.
If no twelve consecutive parents avoid X, each vertex outside X is fixed by
its depth below eleven and by its last ancestor outside X, whose parent lies
in X. A vertex of degree two has at most one child, so this is injective,
and those last ancestors are neighbours of X. Hence the complement of X has
at most eleven times the degree sum of X, which the hypotheses exclude. -/

namespace OMA.Erdos743BarePaths
open Finset SimpleGraph
open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma exists_parent (hc : G.Connected) (ρ v : V) (hv : v ≠ ρ) :
    ∃ q, G.Adj v q ∧ G.dist q ρ + 1 = G.dist v ρ := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v ρ
  cases p with
  | nil => exact absurd rfl hv
  | cons h q =>
    refine ⟨_, h, ?_⟩
    obtain ⟨q', hq'⟩ := hc.exists_walk_length_eq_dist _ ρ
    have h1 := SimpleGraph.dist_le q
    have h2 := SimpleGraph.dist_le (Walk.cons h q')
    simp only [Walk.length_cons] at hp h2
    omega

lemma exists_bare_path (hc : G.Connected) (ρ : V) (X : Finset V) (hρ : ρ ∈ X)
    (hX : ∀ v, v ∉ X → G.degree v = 2)
    (hsmall : 11 * ∑ x ∈ X, G.degree x < (univ \ X).card) :
    ∃ f : Fin 12 → V, Function.Injective f ∧
      (∀ j : Fin 11, G.Adj (f j.castSucc) (f j.succ)) ∧ ∀ j, f j ∉ X := by
  have hpar : ∃ par : V → V, ∀ v, v ≠ ρ → G.Adj v (par v) ∧
      G.dist (par v) ρ + 1 = G.dist v ρ := by
    choose par hp using exists_parent G hc ρ
    exact ⟨fun v => if h : v = ρ then ρ else par v h, fun v hv => by
      simp only [hv, dite_false]; exact hp v hv⟩
  obtain ⟨par, hp⟩ := hpar
  have neρ : ∀ v, v ∉ X → v ≠ ρ := fun v hv h => hv (h ▸ hρ)
  -- depth along the chain
  have depth : ∀ (w : V) (i : ℕ), (∀ t < i, par^[t] w ∉ X) →
      G.dist (par^[i] w) ρ + i = G.dist w ρ := by
    intro w i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro h
      have := ih (fun t ht => h t (by omega))
      have hx := h i (by omega)
      rw [Function.iterate_succ_apply']
      have := (hp _ (neρ _ hx)).2
      omega
  by_contra hno
  have C : ∀ w, w ∉ X → ∃ j, j ≤ 10 ∧ par^[j+1] w ∈ X := by
    intro w hw
    by_contra hall
    push_neg at hall
    have hn : ∀ t ≤ 11, par^[t] w ∉ X := by
      intro t ht
      rcases t with _ | t
      · simpa using hw
      · exact hall t (by omega)
    apply hno
    refine ⟨fun t => par^[t.val] w, ?_, ?_, ?_⟩
    · intro a b hab
      have ha := depth w a.val (fun t ht => hn t (by omega))
      have hb := depth w b.val (fun t ht => hn t (by omega))
      simp only at hab
      rw [hab] at ha
      exact Fin.ext (by omega)
    · intro j
      simp only [Fin.coe_castSucc, Fin.val_succ]
      rw [Function.iterate_succ_apply']
      exact (hp _ (neρ _ (hn j.val (by omega)))).1
    · intro t
      exact hn t.val (by omega)
  -- children of a degree-two vertex are unique
  have child : ∀ y, y ∉ X → ∀ w w', w ≠ ρ → w' ≠ ρ → par w = y → par w' = y → w = w' := by
    intro y hy w w' hw hw' h1 h2
    by_contra hne
    have hyρ := neρ y hy
    have a1 := hp w hw
    have a2 := hp w' hw'
    have a3 := hp y hyρ
    rw [h1] at a1
    rw [h2] at a2
    have n1 : par y ≠ w := by intro h; rw [h] at a3; omega
    have n2 : par y ≠ w' := by intro h; rw [h] at a3; omega
    have hsub : ({w, w', par y} : Finset V) ⊆ G.neighborFinset y := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [mem_neighborFinset]
      rcases hz with rfl | rfl | rfl
      · exact a1.1.symm
      · exact a2.1.symm
      · exact a3.1
    have hc3 : ({w, w', par y} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using n2.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne, n1.symm⟩
    have := Finset.card_le_card hsub
    rw [hc3, card_neighborFinset_eq_degree, hX y hy] at this
    omega
  have chain : ∀ j (w w' : V), (∀ i ≤ j, par^[i] w ∉ X) → (∀ i ≤ j, par^[i] w' ∉ X) →
      par^[j] w = par^[j] w' → w = w' := by
    intro j
    induction j with
    | zero => intro w w' _ _ h; simpa using h
    | succ j ih =>
      intro w w' h1 h2 h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      have e : par w = par w' := ih (par w) (par w')
        (fun i hi => by rw [← Function.iterate_succ_apply]; exact h1 (i+1) (by omega))
        (fun i hi => by rw [← Function.iterate_succ_apply]; exact h2 (i+1) (by omega)) h
      have hy : par w ∉ X := by simpa using h1 1 (by omega)
      exact child (par w) hy w w' (neρ _ (by simpa using h1 0 (by omega)))
        (neρ _ (by simpa using h2 0 (by omega))) rfl e.symm
  -- the counting map
  let S := (univ \ X).filter (fun c => par c ∈ X)
  let φ : V → ℕ × V := fun w =>
    if h : w ∈ X then (0, w) else (Nat.find (C w h), par^[Nat.find (C w h)] w)
  have good : ∀ w (h : w ∉ X), ∀ i ≤ Nat.find (C w h), par^[i] w ∉ X := by
    intro w h i hi
    rcases i with _ | i
    · simpa using h
    · have hlt : i < Nat.find (C w h) := by omega
      have := Nat.find_min (C w h) hlt
      have hle : i ≤ 10 := le_trans hlt.le (Nat.find_spec (C w h)).1
      intro hx
      exact this ⟨hle, hx⟩
  have maps : ∀ w ∈ univ \ X, φ w ∈ (range 11) ×ˢ S := by
    intro w hw
    have h : w ∉ X := (Finset.mem_sdiff.mp hw).2
    simp only [φ, h, dite_false, Finset.mem_product, Finset.mem_range]
    refine ⟨by have := (Nat.find_spec (C w h)).1; omega, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    refine ⟨good w h _ le_rfl, ?_⟩
    have := (Nat.find_spec (C w h)).2
    rwa [Function.iterate_succ_apply'] at this
  have inj : Set.InjOn φ ↑(univ \ X) := by
    intro w hw w' hw' he
    have h : w ∉ X := (Finset.mem_sdiff.mp hw).2
    have h' : w' ∉ X := (Finset.mem_sdiff.mp hw').2
    simp only [φ, h, h', dite_false, Prod.mk.injEq] at he
    obtain ⟨e1, e2⟩ := he
    apply chain (Nat.find (C w h)) w w' (good w h) (fun i hi => good w' h' i (e1 ▸ hi))
    rw [e2, e1]
  have hcard := Finset.card_le_card_of_injOn φ maps inj
  rw [Finset.card_product, Finset.card_range] at hcard
  have hS : S.card ≤ ∑ x ∈ X, G.degree x := by
    have hsub : S ⊆ X.biUnion (fun x => G.neighborFinset x) := by
      intro c hc
      simp only [S, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc
      rw [Finset.mem_biUnion]
      exact ⟨par c, hc.2, by rw [mem_neighborFinset]; exact (hp c (neρ c hc.1)).1.symm⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    exact le_of_eq (Finset.sum_congr rfl (fun x _ => card_neighborFinset_eq_degree G x))
  omega

end OMA.Erdos743BarePaths

open Finset SimpleGraph
open scoped Classical

theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1.H2 := by
  intro k r G hr hk hT B hBc hBs
  have hc : G.Connected := hT.1
  have hkpos : 0 < k := by omega
  let ρ : Fin k := ⟨0, hkpos⟩
  have step : ∀ j ≤ r, ∃ g : ℕ → Fin 12 → Fin k,
      (∀ i < j, Function.Injective (g i) ∧ (∀ t : Fin 11, G.Adj (g i t.castSucc) (g i t.succ)) ∧
        ∀ t, G.degree (g i t) = 2) ∧
      (∀ i < j, ∀ i' < j, i ≠ i' → ∀ t t', g i t ≠ g i' t') := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun _ _ => ρ, by simp, by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨g, hg1, hg2⟩ := ih (by omega)
      let U := (range j).biUnion (fun i => univ.image (g i))
      have hU : U.card ≤ 12 * j := by
        refine Finset.card_biUnion_le.trans ?_
        calc ∑ i ∈ range j, (univ.image (g i)).card ≤ ∑ i ∈ range j, 12 := by
              apply Finset.sum_le_sum; intro i _
              exact (Finset.card_image_le).trans (by simp)
          _ = 12 * j := by simp [mul_comm]
      let T := (insert ρ U).filter (fun v => G.degree v = 2)
      let X := B ∪ T
      have hT2 : T.card ≤ 12 * j + 1 :=
        (Finset.card_filter_le _ _).trans ((Finset.card_insert_le _ _).trans (by omega))
      have hXsum : ∑ x ∈ X, G.degree x ≤ 4 * r + 2 * (12 * j + 1) := by
        have h1 := Finset.sum_union_inter (s₁ := B) (s₂ := T) (f := fun x => G.degree x)
        have h2 : ∑ x ∈ T, G.degree x = 2 * T.card := by
          rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2),
            Finset.sum_const, smul_eq_mul, mul_comm]
        change ∑ x ∈ B ∪ T, G.degree x ≤ _
        omega
      have hXc : X.card ≤ 2 * r + (12 * j + 1) :=
        (Finset.card_union_le _ _).trans (by omega)
      have hcompl : (univ \ X).card = k - X.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hρX : ρ ∈ X := by
        by_cases hd : G.degree ρ = 2
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hd⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
      have hdegX : ∀ v, v ∉ X → G.degree v = 2 := by
        intro v hv
        by_contra hd
        exact hv (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))
      have hUX : ∀ v ∈ U, G.degree v = 2 → v ∈ X := fun v hv hd =>
        Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hv, hd⟩)
      obtain ⟨p, hpi, hpa, hpX⟩ := OMA.Erdos743BarePaths.exists_bare_path G hc ρ X hρX hdegX
        (by rw [hcompl]; omega)
      refine ⟨fun i => if i = j then p else g i, ?_, ?_⟩
      · intro i hi
        beta_reduce
        by_cases hij : i = j
        · rw [if_pos hij]
          exact ⟨hpi, hpa, fun t => hdegX _ (hpX t)⟩
        · rw [if_neg hij]
          exact hg1 i (by omega)
      · have key : ∀ i < j, ∀ t t', p t ≠ g i t' := by
          intro i hi t t' he
          apply hpX t
          rw [he]
          apply hUX
          · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
          · exact (hg1 i hi).2.2 t'
        intro i hi i' hi' hne t t'
        beta_reduce
        by_cases h1 : i = j
        · have h2 : i' ≠ j := by omega
          rw [if_pos h1, if_neg h2]
          exact key i' (by omega) t t'
        · by_cases h2 : i' = j
          · rw [if_neg h1, if_pos h2]
            exact fun he => key i (by omega) t' t he.symm
          · rw [if_neg h1, if_neg h2]
            exact hg2 i (by omega) i' (by omega) hne t t'
  obtain ⟨g, hg1, hg2⟩ := step r le_rfl
  refine ⟨fun x => g x.1.val x.2, ?_, ?_, ?_⟩
  · rintro ⟨i, t⟩ ⟨i', t'⟩ he
    simp only at he
    by_cases hii : i.val = i'.val
    · have hi : i = i' := Fin.ext hii
      subst hi
      rw [(hg1 i.val i.isLt).1 he]
    · exact absurd he (hg2 i.val i.isLt i'.val i'.isLt hii t t')
  · intro i j
    exact (hg1 i.val i.isLt).2.1 j
  · intro i j
    exact (hg1 i.val i.isLt).2.2 j
