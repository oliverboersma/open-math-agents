import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
The seven-cycle-free case admits a dominating induced five-cycle or a clique
of order two or three that reaches every vertex within distance two.
The private-neighbor argument uses the minimum connected dominating set
method of Camby and Schaudt, doi:10.1007/s00453-015-9989-6.
-/

namespace OMA.W133Dominating
open SimpleGraph

variable {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

private lemma path_of_embedding {n : ℕ} (f : Fin n ↪ α)
    (h : ∀ i j : Fin n, G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    n ≤ G.path := by
  have hp : G.isInducedPath (List.ofFn f) := by
    refine ⟨List.nodup_ofFn.mpr f.injective, ?_⟩
    intro i j
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact h ⟨i.val, by simpa using i.isLt⟩ ⟨j.val, by simpa using j.isLt⟩
  simpa using length_le_path_of_isInducedPath G (List.ofFn f) hp

omit [Fintype α] [DecidableEq α] in
private lemma reverse_path {n : ℕ} (f : Fin n ↪ α)
    (h : ∀ i j : Fin n, G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    ∀ i j : Fin n, G.Adj (f i.rev) (f j.rev) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  intro i j
  rw [h, Fin.val_rev, Fin.val_rev]
  omega

omit [Fintype α] [DecidableEq α] in
private lemma prepend_path {n : ℕ} (f : Fin (n + 1) ↪ α) {x : α}
    (h : ∀ i j : Fin (n + 1), G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (hx : ∀ i, x ≠ f i) (he : ∀ i, G.Adj x (f i) ↔ i = 0) :
    ∃ g : Fin (n + 2) ↪ α,
      (∀ i : Fin (n + 1), g i.succ = f i) ∧ g 0 = x ∧
      ∀ i j : Fin (n + 2), G.Adj (g i) (g j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hinj : Function.Injective (Fin.cons x f : Fin (n + 2) → α) := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp
    · intro e
      exact (hx j' e).elim
    · intro e
      exact (hx i' e.symm).elim
    · simp only [Fin.cons_succ, Fin.succ_inj]
      exact fun e : f i' = f j' => f.injective e
  let g : Fin (n + 2) ↪ α := ⟨Fin.cons x f, hinj⟩
  have hg0 : g 0 = x := rfl
  have hgs (i : Fin (n + 1)) : g i.succ = f i := rfl
  refine ⟨g, hgs, hg0, ?_⟩
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [hg0]
  · rw [hg0, hgs, he, Fin.ext_iff]
    simp
  · rw [hg0, hgs, G.adj_comm, he, Fin.ext_iff]
    simp
  · rw [hgs, hgs, h]
    simp only [Fin.val_succ]
    omega

omit [Fintype α] in
/-- A component created by deleting a vertex contains a neighbor of that vertex. -/
private lemma disconnect_neighbor {s : Finset α} (hs : (G.induce (↑s : Set α)).Connected)
    {v u : α} (hv : v ∈ s) (hu : u ∈ s.erase v)
    (hd : ¬ (G.induce (↑(s.erase v) : Set α)).Connected) :
    ∃ w : (↑(s.erase v) : Set α), G.Adj v w.val ∧
      ¬ (G.induce (↑(s.erase v) : Set α)).Reachable ⟨u, hu⟩ w := by
  classical
  let t : Set α := ↑(s.erase v)
  let h : SimpleGraph t := G.induce t
  by_contra! hn
  apply hd
  have hallFromRoot : ∀ z : t, h.Reachable ⟨u, hu⟩ z := by
    intro z
    let root : (↑s : Set α) := ⟨u, Finset.mem_of_mem_erase hu⟩
    let last : (↑s : Set α) := ⟨z.val, Finset.mem_of_mem_erase z.property⟩
    have hall (w : (↑s : Set α)) (hw : (G.induce (↑s : Set α)).Reachable root w) :
        ∀ hw' : w.val ∈ t, h.Reachable ⟨u, hu⟩ ⟨w.val, hw'⟩ := by
      rw [reachable_iff_reflTransGen] at hw
      induction hw with
      | refl => exact fun _ => SimpleGraph.Reachable.rfl
      | @tail a b _ hab ih =>
        intro hb
        by_cases ha : a.val = v
        · exact hn ⟨b.val, hb⟩ (ha ▸ hab)
        · have hat : a.val ∈ t := Finset.mem_erase.mpr ⟨ha, a.property⟩
          have hab' : h.Adj ⟨a.val, hat⟩ ⟨b.val, hb⟩ := hab
          exact (ih hat).trans hab'.reachable
    exact hall last (hs root last) z.property
  let : Nonempty t := ⟨⟨u, hu⟩⟩
  exact ⟨fun a b => (hallFromRoot a).symm.trans (hallFromRoot b)⟩

omit [Fintype α] in
private lemma extend_inside {s : Finset α} (hs : (G.induce (↑s : Set α)).Connected)
    {n : ℕ} (f : Fin (n + 2) ↪ α) (hf : ∀ i, f i ∈ s)
    (ha : ∀ i j : Fin (n + 2), G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (hd : ¬ (G.induce (↑(s.erase (f 0)) : Set α)).Connected) :
    ∃ x ∈ s, (∀ i, x ≠ f i) ∧ ∀ i, G.Adj x (f i) ↔ i = 0 := by
  let t : Set α := ↑(s.erase (f 0))
  have hmem (i : Fin (n + 1)) : f i.succ ∈ t :=
    Finset.mem_erase.mpr ⟨fun e => Fin.succ_ne_zero i (f.injective e), hf _⟩
  let g : Fin (n + 1) → t := fun i => ⟨f i.succ, hmem i⟩
  have hr (i : Fin (n + 1)) : (G.induce t).Reachable (g 0) (g i) := by
    induction i using Fin.induction with
    | zero => exact .rfl
    | succ i ih =>
      have he : (G.induce t).Adj (g i.castSucc) (g i.succ) :=
        (ha _ _).mpr (Or.inl rfl)
      exact ih.trans he.reachable
  obtain ⟨w, hw, hn⟩ := disconnect_neighbor G hs (hf 0) (hmem 0) hd
  refine ⟨w.val, Finset.mem_of_mem_erase w.property, ?_, ?_⟩
  · intro i
    refine Fin.cases (Finset.ne_of_mem_erase w.property) (fun j => ?_) i
    intro h
    exact hn (by simpa only [show w = g j from Subtype.ext h] using hr j)
  · intro i
    refine Fin.cases (by simp [hw.symm]) (fun j => ?_) i
    constructor
    · intro h
      have hwe : (G.induce t).Adj (g j) w := h.symm
      exact (hn ((hr j).trans hwe.reachable)).elim
    · exact fun h => (Fin.succ_ne_zero j h).elim

omit [Fintype α] in
/-- A removable vertex of a minimum connected dominating set has a private neighbor. -/
private lemma private_neighbor {s : Finset α}
    (hdom : ∀ v ∉ s, ∃ u ∈ s, G.Adj v u)
    (hmin : ∀ t : Finset α, (G.induce (↑t : Set α)).Connected →
      (∀ v ∉ t, ∃ u ∈ t, G.Adj v u) → s.card ≤ t.card)
    {v : α} (hv : v ∈ s) {u : α} (hu : u ∈ s.erase v) (ha : G.Adj v u)
    (hc : (G.induce (↑(s.erase v) : Set α)).Connected) :
    ∃ x ∉ s, G.Adj x v ∧ ∀ w ∈ s.erase v, ¬ G.Adj x w := by
  have hnd : ¬ (∀ x ∉ s.erase v, ∃ w ∈ s.erase v, G.Adj x w) := by
    intro hd
    have hle := hmin (s.erase v) hc hd
    have hlt := Finset.card_erase_lt_of_mem hv
    omega
  push Not at hnd
  obtain ⟨x, hx, hnot⟩ := hnd
  have hxS : x ∉ s := by
    intro hxs
    have he : x = v := by
      by_contra hn
      exact hx (Finset.mem_erase.mpr ⟨hn, hxs⟩)
    exact hnot u hu (he ▸ ha)
  obtain ⟨w, hw, hxw⟩ := hdom x hxS
  have he : w = v := by
    by_contra hn
    exact hnot w (Finset.mem_erase.mpr ⟨hn, hw⟩) hxw
  exact ⟨x, hxS, he ▸ hxw, hnot⟩

private lemma min_dominating (hG : G.Connected) :
    ∃ s : Finset α, (G.induce (↑s : Set α)).Connected ∧
      (∀ v ∉ s, ∃ u ∈ s, G.Adj v u) ∧
      ∀ t : Finset α, (G.induce (↑t : Set α)).Connected →
        (∀ v ∉ t, ∃ u ∈ t, G.Adj v u) → s.card ≤ t.card := by
  classical
  let good (n : ℕ) : Prop := ∃ s : Finset α, s.card = n ∧
    (G.induce (↑s : Set α)).Connected ∧ (∀ v ∉ s, ∃ u ∈ s, G.Adj v u)
  have hex : ∃ n, good n := by
    refine ⟨_, Finset.univ, rfl, ?_, by simp⟩
    rw [Finset.coe_univ]
    exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hG
  obtain ⟨s, hs, hconn, hdom⟩ := Nat.find_spec hex
  refine ⟨s, hconn, hdom, ?_⟩
  intro t ht hdt
  rw [hs]
  exact Nat.find_min' hex ⟨t, rfl, ht, hdt⟩


omit [Fintype α] in
private lemma private_of_path
    {s : Finset α} (hs : (G.induce (↑s : Set α)).Connected)
    (hdom : ∀ v ∉ s, ∃ u ∈ s, G.Adj v u)
    (hmin : ∀ t : Finset α, (G.induce (↑t : Set α)).Connected →
      (∀ v ∉ t, ∃ u ∈ t, G.Adj v u) → s.card ≤ t.card)
    {n : ℕ}
    (hn : ∀ g : Fin (n + 3) ↪ α, (∀ i, g i ∈ s) →
      ¬ (∀ i j : Fin (n + 3), G.Adj (g i) (g j) ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (f : Fin (n + 2) ↪ α) (hf : ∀ i, f i ∈ s)
    (ha : ∀ i j : Fin (n + 2), G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    ∃ x ∉ s, ∀ i, G.Adj x (f i) ↔ i = 0 := by
  have hc : (G.induce (↑(s.erase (f 0)) : Set α)).Connected := by
    by_contra hd
    obtain ⟨x, hxs, hxn, hxa⟩ := extend_inside G hs f hf ha hd
    obtain ⟨g, hgs, hg0, hga⟩ := prepend_path G f ha hxn hxa
    exact hn g (fun i => Fin.cases (hg0 ▸ hxs) (fun j => hgs j ▸ hf j) i) hga
  have hu : f (Fin.succ (0 : Fin (n + 1))) ∈ s.erase (f 0) :=
    Finset.mem_erase.mpr ⟨fun h => Fin.succ_ne_zero _ (f.injective h), hf _⟩
  have ha01 : G.Adj (f 0) (f (Fin.succ (0 : Fin (n + 1)))) :=
    (ha _ _).mpr (Or.inl rfl)
  obtain ⟨x, hxs, hx0, hnx⟩ := private_neighbor G hdom hmin (hf 0) hu ha01 hc
  refine ⟨x, hxs, fun i => Fin.cases (by simp [hx0]) (fun j => ?_) i⟩
  have hm : f j.succ ∈ s.erase (f 0) :=
    Finset.mem_erase.mpr ⟨fun h => Fin.succ_ne_zero _ (f.injective h), hf _⟩
  simp [hnx _ hm]

omit [Fintype α] [DecidableEq α] in
private lemma cycle_adj {m : ℕ} {i j : Fin (m + 4)} : (cycleGraph (m + 4)).Adj i j ↔
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val = 0 ∧ j.val = m + 3) ∨ (j.val = 0 ∧ i.val = m + 3) := by
  have step (a b : Fin (m + 4)) : a - b = 1 ↔
      b.val + 1 = a.val ∨ (a.val = 0 ∧ b.val = m + 3) := by
    rw [sub_eq_iff_eq_add', Fin.ext_iff]
    change a.val = (b.val + 1) % (m + 4) ↔ _
    have ha := a.isLt
    have hb := b.isLt
    by_cases hs : b.val + 1 < m + 4
    · rw [Nat.mod_eq_of_lt hs]
      omega
    · rw [show b.val + 1 = m + 4 by omega, Nat.mod_self]
      omega
  rw [cycleGraph_adj, step, step]
  tauto

omit [Fintype α] [DecidableEq α] in
private lemma close_cycle {m : ℕ} (f : Fin (m + 2) ↪ α) {x y : α}
    (ha : ∀ i j : Fin (m + 2), G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (hxn : ∀ i, x ≠ f i) (hyn : ∀ i, y ≠ f i) (hxy : G.Adj x y)
    (hx : ∀ i, G.Adj x (f i) ↔ i = 0)
    (hy : ∀ i, G.Adj y (f i) ↔ i.val = m + 1) :
    (cycleGraph (m + 4)).IsIndContained G := by
  obtain ⟨g, hgs, hg0, hga⟩ := prepend_path G f ha hxn hx
  have hne : ∀ i : Fin (m + 3), y ≠ g i := fun i =>
    Fin.cases (hg0 ▸ hxy.ne.symm) (fun j => hgs j ▸ hyn j) i
  have hg_adj (i : Fin (m + 3)) : G.Adj y (g i) ↔ i.val = 0 ∨ i.val = m + 2 := by
    refine Fin.cases (by simp [hg0, hxy.symm]) (fun j => ?_) i
    rw [hgs, hy]
    simp only [Fin.val_succ]
    omega
  have hinj : Function.Injective (Fin.cons y g : Fin (m + 4) → α) := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp
    · intro e
      exact (hne j' e).elim
    · intro e
      exact (hne i' e.symm).elim
    · simp only [Fin.cons_succ, Fin.succ_inj]
      exact fun e : g i' = g j' => g.injective e
  refine ⟨⟨⟨Fin.cons y g, hinj⟩, ?_⟩⟩
  intro i j
  change G.Adj ((Fin.cons y g : Fin (m + 4) → α) i) ((Fin.cons y g : Fin (m + 4) → α) j) ↔
    (cycleGraph (m + 4)).Adj i j
  rw [cycle_adj]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp
  · change G.Adj y (g j') ↔
      0 + 1 = j'.val + 1 ∨ j'.val + 1 + 1 = 0 ∨
        (0 = 0 ∧ j'.val + 1 = m + 3) ∨ (j'.val + 1 = 0 ∧ 0 = m + 3)
    rw [hg_adj]
    omega
  · change G.Adj (g i') y ↔
      i'.val + 1 + 1 = 0 ∨ 0 + 1 = i'.val + 1 ∨
        (i'.val + 1 = 0 ∧ 0 = m + 3) ∨ (0 = 0 ∧ i'.val + 1 = m + 3)
    rw [G.adj_comm, hg_adj]
    omega
  · simp only [Fin.cons_succ, hga, Fin.val_succ]
    omega

/-- A minimum connected dominating set in a graph with no induced path on `m + 4`
vertices either has no induced path on `m + 2` vertices or forces an induced cycle
on `m + 4` vertices in the graph. -/
lemma dominating_or_cycle {m : ℕ} (hG : G.Connected)
    (hp : ¬ (pathGraph (m + 4)).IsIndContained G) :
    (cycleGraph (m + 4)).IsIndContained G ∨
      ∃ s : Finset α, G.IsConnectedDominating (↑s : Set α) ∧
        ¬ (pathGraph (m + 2)).IsIndContained (G.induce (↑s : Set α)) := by
  obtain ⟨s, hs, hds, hmin⟩ := min_dominating G hG
  have noLongPath (f : Fin (m + 4) ↪ α) :
      ¬ (∀ i j : Fin (m + 4), G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro ha
    exact hp ⟨⟨f, fun {i j} => (ha i j).trans pathGraph_adj.symm⟩⟩
  have noIntermediatePath (f : Fin (m + 3) ↪ α) (hf : ∀ i, f i ∈ s) :
      ¬ (∀ i j : Fin (m + 3), G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro ha
    obtain ⟨x, hxs, hxa⟩ := private_of_path G hs hds hmin
      (fun g _ => noLongPath g) f hf ha
    have hxn (i : Fin (m + 3)) : x ≠ f i := by
      intro e
      apply hxs
      rw [e]
      exact hf i
    obtain ⟨g, _, _, hga⟩ := prepend_path G f ha hxn hxa
    exact noLongPath g hga
  by_cases hs5 : (pathGraph (m + 2)).IsIndContained (G.induce (↑s : Set α))
  · left
    obtain ⟨f'⟩ := hs5
    let f : Fin (m + 2) ↪ α := ⟨fun i => (f' i).val, fun _ _ h => f'.injective (Subtype.ext h)⟩
    have hf (i : Fin (m + 2)) : f i ∈ s := (f' i).property
    have ha (i j : Fin (m + 2)) : G.Adj (f i) (f j) ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val := f'.map_adj_iff.trans pathGraph_adj
    obtain ⟨x, hxs, hxa⟩ := private_of_path G hs hds hmin noIntermediatePath f hf ha
    let r : Fin (m + 2) ↪ α := ⟨fun i => f i.rev, f.injective.comp Fin.rev_injective⟩
    obtain ⟨y, hys, hyar⟩ := private_of_path G hs hds hmin noIntermediatePath
      r (fun i => hf i.rev) (reverse_path G f ha)
    have hya (i : Fin (m + 2)) : G.Adj y (f i) ↔ i.val = m + 1 := by
      have h := hyar i.rev
      change G.Adj y (f i.rev.rev) ↔ i.rev = 0 at h
      rw [Fin.rev_rev, Fin.ext_iff, Fin.val_rev] at h
      rw [h]
      change m + 2 - (i.val + 1) = 0 ↔ i.val = m + 1
      have hi := i.isLt
      omega
    have hxn (i : Fin (m + 2)) : x ≠ f i := fun h => hxs (h.symm ▸ hf i)
    have hyn (i : Fin (m + 2)) : y ≠ f i := fun h => hys (h.symm ▸ hf i)
    have hxy : G.Adj x y := by
      by_contra hna
      have hne : x ≠ y := by
        intro e
        have he := (hya 0).mp (e ▸ (hxa 0).mpr rfl)
        change 0 = m + 1 at he
        omega
      obtain ⟨g, hgs, hg0, hga⟩ := prepend_path G f ha hxn hxa
      let gr : Fin (m + 3) ↪ α := ⟨fun i => g i.rev, g.injective.comp Fin.rev_injective⟩
      have hyn' (i : Fin (m + 3)) : y ≠ g i := by
        refine Fin.cases (hg0 ▸ hne.symm) (fun j => hgs j ▸ hyn j) i
      have hya' (i : Fin (m + 3)) : G.Adj y (g i) ↔ i.val = m + 2 := by
        refine Fin.cases (by simp [hg0, G.adj_comm y x, hna]) (fun j => ?_) i
        rw [hgs, hya]
        change j.val = m + 1 ↔ j.val + 1 = m + 2
        omega
      have hyar' (i : Fin (m + 3)) : G.Adj y (gr i) ↔ i = 0 := by
        change G.Adj y (g i.rev) ↔ i = 0
        rw [hya', Fin.ext_iff, Fin.val_rev]
        change m + 3 - (i.val + 1) = m + 2 ↔ i.val = 0
        have hi := i.isLt
        omega
      obtain ⟨p, _, _, hpa⟩ :=
        prepend_path G gr (reverse_path G g hga) (fun i => hyn' i.rev) hyar'
      exact noLongPath p hpa
    exact close_cycle G f ha hxn hyn hxy hxa hya
  · exact Or.inr ⟨s, ⟨fun v => by
      by_cases hv : v ∈ s
      · exact Or.inl hv
      · exact Or.inr (hds v hv), hs⟩, hs5⟩


omit [Fintype α] [DecidableEq α] in
private lemma preconnected_p3_free (hG : G.Preconnected)
    (hP : ¬ (pathGraph 3).IsIndContained G) : ∀ {x y}, x ≠ y → G.Adj x y := by
  have close {a b c : α} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) :
      G.Adj a c := by
    by_contra hn
    let f : Fin 3 → α := ![a, b, c]
    have hf : Function.Injective f := by
      intro i j h
      have hab' := hab.ne
      have hbc' := hbc.ne
      fin_cases i <;> fin_cases j <;> simp [f, hab', hbc', hac, eq_comm] at h ⊢
    apply hP
    refine ⟨⟨⟨f, hf⟩, ?_⟩⟩
    intro i j
    change G.Adj (f i) (f j) ↔ (pathGraph 3).Adj i j
    have hn' : ¬ G.Adj c a := fun h => hn h.symm
    fin_cases i <;> fin_cases j <;>
      simp [f, pathGraph_adj, hab, hbc, hn, hab.symm, hbc.symm, hn']
  intro x y hxy
  have reach := (reachable_iff_reflTransGen _ _).mp (hG x y)
  have step : x = y ∨ G.Adj x y := by
    clear hxy
    induction reach with
    | refl => exact Or.inl rfl
    | @tail a b _ hab ih =>
      rcases ih with rfl | hxa
      · exact Or.inr hab
      · by_cases hxb : x = b
        · exact Or.inl hxb
        · exact Or.inr (close hxa hab hxb)
  exact step.resolve_left hxy

omit [Fintype α] [DecidableEq α] in
/-- In a connected graph without a four-cycle or an induced five-vertex path,
any induced five-cycle includes every vertex. -/
private lemma cycle5_no_outer
    (hG : G.Connected) (hP : ¬ (pathGraph 5).IsIndContained G)
    (hC : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (f : cycleGraph 5 ↪g G) : Function.Surjective f := by
  have noExtension (g : cycleGraph 5 ↪g G) {x : α} (hxn : ∀ i, x ≠ g i)
      (hx : G.Adj x (g 0)) (hn : ¬ G.Adj x (g 1)) : False := by
    have edge {i j : Fin 5} (h : (cycleGraph 5).Adj i j) : G.Adj (g i) (g j) :=
      g.map_adj_iff.mpr h
    have n2 : ¬ G.Adj x (g 2) := by
      intro hx2
      exact hC ⟨x, g 0, g 1, g 2, hxn _, hxn _, hxn _,
        g.injective.ne (by decide), g.injective.ne (by decide), g.injective.ne (by decide),
        hx, edge (by decide), edge (by decide), hx2.symm⟩
    have n3 : ¬ G.Adj x (g 3) := by
      intro hx3
      exact hC ⟨x, g 0, g 4, g 3, hxn _, hxn _, hxn _,
        g.injective.ne (by decide), g.injective.ne (by decide), g.injective.ne (by decide),
        hx, edge (by decide), edge (by decide), hx3.symm⟩
    let p : Fin 4 ↪ α := ⟨fun i => g ⟨i.val, by omega⟩,
      fun _ _ h => Fin.ext (congrArg (fun z : Fin 5 => z.val) (g.injective h))⟩
    have hpa (i j : Fin 4) : G.Adj (p i) (p j) ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val := by
      change G.Adj (g ⟨i.val, _⟩) (g ⟨j.val, _⟩) ↔ _
      rw [g.map_adj_iff, cycle_adj]
      simp only
      have hi := i.isLt
      have hj := j.isLt
      omega
    have hpx (i : Fin 4) : G.Adj x (p i) ↔ i = 0 := by
      fin_cases i
      · change G.Adj x (g 0) ↔ (0 : Fin 4) = 0
        simp [hx]
      · change G.Adj x (g 1) ↔ (1 : Fin 4) = 0
        simp [hn]
      · change G.Adj x (g 2) ↔ (2 : Fin 4) = 0
        simp [n2]
      · change G.Adj x (g 3) ↔ (3 : Fin 4) = 0
        simp [n3]
    obtain ⟨q, _, _, hqa⟩ := prepend_path G p hpa (fun i => hxn _) hpx
    exact hP ⟨⟨q, fun {i j} => (hqa i j).trans pathGraph_adj.symm⟩⟩
  have noOutsideEdge (i : Fin 5) {x : α} (hxn : ∀ j, x ≠ f j)
      (hx : G.Adj x (f i)) : False := by
    let g : cycleGraph 5 ↪g G := ⟨⟨fun j => f (j + i), by
        intro a b h
        exact add_right_cancel (f.injective h)⟩, by
      intro a b
      change G.Adj (f (a + i)) (f (b + i)) ↔ _
      rw [f.map_adj_iff, cycleGraph_adj, cycleGraph_adj, add_sub_add_right_eq_sub,
        add_sub_add_right_eq_sub]⟩
    have hgn (j : Fin 5) : x ≠ g j := hxn _
    have hg0 : G.Adj x (g 0) := by
      change G.Adj x (f (0 + i))
      simpa using hx
    by_cases h1 : G.Adj x (g 1)
    · have h4 : ¬ G.Adj x (g 4) := by
        intro h4
        exact hC ⟨x, g 1, g 0, g 4, hgn _, hgn _, hgn _,
          g.injective.ne (by decide), g.injective.ne (by decide), g.injective.ne (by decide),
          h1, g.map_adj_iff.mpr (by decide), g.map_adj_iff.mpr (by decide), h4.symm⟩
      let r : cycleGraph 5 ↪g G := ⟨⟨fun j => g (-j), by
          intro a b h
          exact neg_injective (g.injective h)⟩, by
        intro a b
        change G.Adj (g (-a)) (g (-b)) ↔ _
        rw [g.map_adj_iff, cycleGraph_adj, cycleGraph_adj, neg_sub_neg, neg_sub_neg]
        exact or_comm⟩
      exact noExtension r (fun j => hgn _) (show G.Adj x (g 0) from hg0)
        (show ¬ G.Adj x (g 4) from h4)
    · exact noExtension g hgn hg0 h1
  intro v
  have hv := (reachable_iff_reflTransGen _ _).mp (hG (f 0) v)
  induction hv with
  | refl => exact ⟨0, rfl⟩
  | @tail a b _ hab ih =>
    obtain ⟨i, rfl⟩ := ih
    by_contra nb
    exact noOutsideEdge i (fun j e => nb ⟨j, e.symm⟩) hab.symm

private lemma clique_or_dominating_five
    (hG : G.Connected) (hP : ¬ (pathGraph 7).IsIndContained G)
    (h7 : ¬ (cycleGraph 7).IsIndContained G)
    (hC : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    (∃ f : cycleGraph 5 ↪g G, G.IsDominating (Set.range f)) ∨
      (∃ k : Finset α, G.IsClique (↑k : Set α) ∧ ∀ v, ∃ u ∈ k, G.dist u v ≤ 2) := by
  classical
  obtain ⟨s, hs, h5⟩ := (dominating_or_cycle G hG hP).resolve_left h7
  let J := G.induce (↑s : Set α)
  obtain hC5 | ⟨t, ht, h3⟩ := dominating_or_cycle J hs.2 h5
  · left
    obtain ⟨f⟩ := hC5
    have hsC : ¬ (∃ a b c d : (↑s : Set α), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧
        b ≠ d ∧ c ≠ d ∧ J.Adj a b ∧ J.Adj b c ∧ J.Adj c d ∧ J.Adj d a) := by
      rintro ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,eab,ebc,ecd,eda⟩
      exact hC ⟨a.val,b.val,c.val,d.val,fun e => hab (Subtype.ext e),fun e => hac (Subtype.ext e),
        fun e => had (Subtype.ext e),fun e => hbc (Subtype.ext e),fun e => hbd (Subtype.ext e),
        fun e => hcd (Subtype.ext e),eab,ebc,ecd,eda⟩
    have hsurj := cycle5_no_outer J hs.2 h5 hsC f
    let g : cycleGraph 5 ↪g G := ⟨⟨fun i => (f i).val, fun _ _ h => f.injective (Subtype.ext h)⟩,
      f.map_adj_iff⟩
    refine ⟨g, fun v => ?_⟩
    rcases hs.1 v with hvs | ⟨u,hu,ha⟩
    · obtain ⟨i, hi⟩ := hsurj ⟨v,hvs⟩
      exact Or.inl ⟨i, congrArg Subtype.val hi⟩
    · obtain ⟨i, hi⟩ := hsurj ⟨u,hu⟩
      exact Or.inr ⟨u, ⟨i, congrArg Subtype.val hi⟩, ha⟩
  · right
    let k : Finset α := t.image Subtype.val
    have hk : G.IsClique (↑k : Set α) := by
      intro a ha b hb hab
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
      have hneq : (⟨a',ha'⟩ : (↑t : Set _)) ≠ ⟨b',hb'⟩ :=
        fun e => hab (congrArg (fun z => z.val.val) e)
      exact preconnected_p3_free (J.induce (↑t : Set _)) ht.2.preconnected h3 hneq
    refine ⟨k, hk, fun v => ?_⟩
    have withinOne {a b : α} (h : a = b ∨ G.Adj a b) : G.dist a b ≤ 1 := by
      rcases h with rfl | ha
      · simp
      · exact (dist_eq_one_iff_adj.mpr ha).le
    obtain ⟨w, hws, hvw⟩ : ∃ w ∈ (↑s : Set α), v = w ∨ G.Adj v w := by
      rcases hs.1 v with hv | ⟨w, hw, ha⟩
      · exact ⟨v, hv, Or.inl rfl⟩
      · exact ⟨w, hw, Or.inr ha⟩
    obtain ⟨u, hu, hwu⟩ : ∃ u ∈ t, (⟨w,hws⟩ : (↑s : Set α)) = u ∨ J.Adj ⟨w,hws⟩ u := by
      rcases ht.1 ⟨w,hws⟩ with hu | ⟨u, hu, ha⟩
      · exact ⟨_, hu, Or.inl rfl⟩
      · exact ⟨u, hu, Or.inr ha⟩
    have h1 := withinOne (a := v) (b := w) hvw
    have h2 : G.dist w u.val ≤ 1 := withinOne (hwu.imp (congrArg Subtype.val) id)
    refine ⟨u.val, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [dist_comm]
    have := hG.dist_triangle (u := v) (v := w) (w := u.val)
    omega


omit [Fintype α] [DecidableEq α] in
private lemma two_le_card_of_distance_cover {k : Finset α} (hG : G.Connected)
    (hr : G.radius.toNat = 3) (hk : ∀ v, ∃ u ∈ k, G.dist u v ≤ 2) :
    2 ≤ k.card := by
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨u, hu, _⟩ := hk v
  by_contra! hle
  have hcard : k.card = 1 := by
    have := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hcard
  have he : G.eccent c ≤ 2 := (G.eccent_le_iff c 2).mpr (fun w => by
    obtain ⟨z, hz, hzw⟩ := hk w
    rw [Finset.mem_singleton.mp hz] at hzw
    rw [← (hG c w).coe_dist_eq_edist]
    exact_mod_cast hzw)
  have hr' := ENat.toNat_le_toNat (G.radius_le_eccent.trans he)
    (by decide : (2 : ℕ∞) ≠ ⊤)
  rw [hr] at hr'
  norm_num at hr'

omit [Fintype α] [DecidableEq α] in
private lemma card_clique_le_three {k : Finset α}
    (hC : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hk : G.IsClique (↑k : Set α)) : k.card ≤ 3 := by
  classical
  by_contra! h
  have h4 : 4 ≤ Fintype.card k := by simpa using (Nat.succ_le_of_lt h)
  let e : Fin 4 ↪ α := ⟨fun i => ((Fintype.equivFin k).symm (i.castLE h4)).val, by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (Fintype.card k) => z.val)
      ((Fintype.equivFin k).symm.injective (Subtype.ext hij)))⟩
  have hm (i : Fin 4) : e i ∈ k := ((Fintype.equivFin k).symm (i.castLE h4)).property
  have hn {i j : Fin 4} (hne : i ≠ j) : e i ≠ e j := e.injective.ne hne
  exact hC ⟨e 0, e 1, e 2, e 3,
    hn (by decide), hn (by decide), hn (by decide), hn (by decide), hn (by decide), hn (by decide),
    hk (hm 0) (hm 1) (hn (by decide)), hk (hm 1) (hm 2) (hn (by decide)),
    hk (hm 2) (hm 3) (hn (by decide)), hk (hm 3) (hm 0) (hn (by decide))⟩

lemma dominating_cycle_or_small_clique (hG : G.Connected)
    (hC : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : G.radius.toNat = 3) (hp : G.path = 6)
    (h7 : ¬ (cycleGraph 7).IsIndContained G) :
    (∃ f : cycleGraph 5 ↪g G, G.IsDominating (Set.range f)) ∨
      (∃ k : Finset α, 2 ≤ k.card ∧ k.card ≤ 3 ∧ G.IsClique (↑k : Set α) ∧
        ∀ v, ∃ u ∈ k, G.dist u v ≤ 2) := by
  have hP : ¬ (pathGraph 7).IsIndContained G := by
    rintro ⟨f⟩
    have h := path_of_embedding G f.toEmbedding (fun i j => f.map_adj_iff.trans pathGraph_adj)
    omega
  rcases clique_or_dominating_five G hG hP h7 hC with h5 | ⟨k, hk, hd⟩
  · exact Or.inl h5
  · exact Or.inr ⟨k, two_le_card_of_distance_cover G hG hr hd, card_clique_le_three G hC hk, hk, hd⟩

end OMA.W133Dominating

namespace OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1_H1_R1

open SimpleGraph

/-- The case with an induced seven-cycle. -/
def H1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    G.radius.toNat = 3 → G.path = 6 →
    (∃ v, 3 < G.indepNeighborsCard v) →
    3 * Fintype.card α < 2 * Nat.card G.edgeSet →
    (cycleGraph 7).IsIndContained G → G.l ≤ 3

/-- The seven-cycle-free case, with a dominating five-cycle or a clique
of order two or three whose distance-two neighborhoods cover the graph. -/
def H2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    G.radius.toNat = 3 → G.path = 6 →
    (∃ v, 3 < G.indepNeighborsCard v) →
    3 * Fintype.card α < 2 * Nat.card G.edgeSet →
    ¬ (cycleGraph 7).IsIndContained G →
    ((∃ f : cycleGraph 5 ↪g G, G.IsDominating (Set.range f)) ∨
      (∃ k : Finset α, 2 ≤ k.card ∧ k.card ≤ 3 ∧ G.IsClique (↑k : Set α) ∧
        ∀ v, ∃ u ∈ k, G.dist u v ≤ 2)) →
    G.l ≤ 3

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1.H1 := by
  intro h1 h2 α _ _ _ G hG hc hr hp hv hd
  by_cases h7 : (cycleGraph 7).IsIndContained G
  · exact h1 G hG hc hr hp hv hd h7
  · exact h2 G hG hc hr hp hv hd h7
      (OMA.W133Dominating.dominating_cycle_or_small_clique G hG hc hr hp h7)

end OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1_H1_R1

