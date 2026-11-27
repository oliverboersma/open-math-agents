import FormalConjectures.ErdosProblems.«1068»

/-!
Disproof of Erdős Problem 1068. Ported from the certified conjectures.io result
d5e35e41-6e20-43fa-8e9a-acead5e2bd48 (solver credited in the PR body; Lean-verified
12 Nov 2026, certified 19 Nov 2026). Changes: the final theorem is restated against the catalogue
declaration, and two `dite_eq_left` rewrites became `dif_pos`.
-/

/-!
# Erdős problem 1068 — counterexample

The construction below has chromatic cardinal aleph one and has no infinitely
connected induced subgraph. The final theorem proves the counterexample target
for the pinned Conjectures.io task.

This file is the submission body. The verifier supplies the trusted imports and
the enclosing `Bounty` namespace through its task header and footer.
-/

noncomputable section

open Set Cardinal Ordinal Function

namespace Erdos1068Counterexample

abbrev Level : Type := (Ordinal.omega 1).ToType
abbrev Letter := Set ℕ
abbrev Label := List Letter
abbrev History := ℕ → Letter
abbrev Node := Σ a : Level, Set.Iio a → Label
abbrev Vertex := Node × History

def levelZero : Level :=
  Ordinal.ToType.mk ⟨0, (Cardinal.isSuccLimit_omega 1).pos⟩

def levelNext (a : Level) : Level :=
  Ordinal.ToType.mk ⟨(a : Ordinal) + 1,
    (Cardinal.isSuccLimit_omega 1).add_one_lt a.toOrd.property⟩

lemma levelNext_gt (a : Level) : a < levelNext a := by
  apply (Ordinal.ToType.mk.symm.lt_iff_lt).mp
  simp only [levelNext, OrderIso.symm_apply_apply]
  exact lt_add_one (a : Ordinal)

lemma level_bound (f : ℕ → Level) : ∃ a : Level, ∀ n, f n < a := by
  let o : Ordinal := ⨆ n, (f n : Ordinal)
  have ho : o < Ordinal.omega 1 :=
    Ordinal.iSup_lt_omega_one (fun n => (f n).toOrd.property)
  refine ⟨Ordinal.ToType.mk ⟨o + 1, (Cardinal.isSuccLimit_omega 1).add_one_lt ho⟩, ?_⟩
  intro n
  apply (Ordinal.ToType.mk.symm.lt_iff_lt).mp
  rw [OrderIso.symm_apply_apply]
  change (f n : Ordinal) < o + 1
  exact (le_ciSup Ordinal.bddAbove_of_small n).trans_lt (lt_add_one o)

lemma level_initial_countable (a : Level) : Countable (Set.Iio a) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  simpa [Level] using Cardinal.mk_Iio_lt a (by simp [Level])

lemma mk_level : Cardinal.mk Level = Cardinal.aleph 1 := by simp [Level]
lemma mk_letter : Cardinal.mk Letter = Cardinal.continuum := Cardinal.mk_set_nat
lemma mk_label : Cardinal.mk Label = Cardinal.continuum := by
  rw [Cardinal.mk_list_eq_mk, mk_letter]
lemma mk_history : Cardinal.mk History = Cardinal.continuum := by
  simp [History, Letter]

def Prefix (t u : Node) : Prop :=
  t.1 ≤ u.1 ∧ ∀ (a : Level) (ht : a < t.1) (hu : a < u.1),
    t.2 ⟨a, ht⟩ = u.2 ⟨a, hu⟩

lemma prefix_refl (t : Node) : Prefix t t := by
  exact ⟨le_rfl, fun _ _ _ => rfl⟩

lemma prefix_trans {t u v : Node} (htu : Prefix t u) (huv : Prefix u v) :
    Prefix t v := by
  refine ⟨htu.1.trans huv.1, ?_⟩
  intro a ht hv
  exact (htu.2 a ht (ht.trans_le htu.1)).trans
    (huv.2 a (ht.trans_le htu.1) hv)

lemma prefix_antisymm {t u : Node} (htu : Prefix t u) (hut : Prefix u t) : t = u := by
  obtain ⟨a, f⟩ := t
  obtain ⟨b, g⟩ := u
  have hab : a = b := le_antisymm htu.1 hut.1
  subst b
  congr 1
  funext i
  exact htu.2 i.1 i.2 i.2

lemma prefix_eq_of_height_eq {t u : Node} (htu : Prefix t u) (h : t.1 = u.1) :
    t = u := by
  apply prefix_antisymm htu
  refine ⟨h.ge, ?_⟩
  intro a hu ht
  exact (htu.2 a ht hu).symm

lemma prefixes_comparable {t u v : Node} (htv : Prefix t v) (huv : Prefix u v) :
    Prefix t u ∨ Prefix u t := by
  rcases le_total t.1 u.1 with h | h
  · left
    refine ⟨h, ?_⟩
    intro a ht hu
    exact (htv.2 a ht (ht.trans_le htv.1)).trans
      (huv.2 a hu (hu.trans_le huv.1)).symm
  · right
    refine ⟨h, ?_⟩
    intro a hu ht
    exact (huv.2 a hu (hu.trans_le huv.1)).trans
      (htv.2 a ht (ht.trans_le htv.1)).symm

def Child (t : Node) (s : Label) (u : Node) : Prop :=
  Prefix t u ∧ ∃ h : t.1 < u.1, u.2 ⟨t.1, h⟩ = s

lemma child_height {t u : Node} {s : Label} (h : Child t s u) : t.1 < u.1 :=
  h.2.choose

lemma child_unique {t u : Node} {s r : Label} (hs : Child t s u) (hr : Child t r u) :
    s = r := hs.2.choose_spec.symm.trans hr.2.choose_spec

lemma child_upwards {t u v : Node} {s : Label} (h : Child t s u) (huv : Prefix u v) :
    Child t s v := by
  refine ⟨prefix_trans h.1 huv, (child_height h).trans_le huv.1, ?_⟩
  exact (huv.2 t.1 (child_height h) ((child_height h).trans_le huv.1)).symm.trans
    h.2.choose_spec

lemma child_downwards {t u v : Node} {s : Label} (h : Child t s v)
    (htu : Prefix t u) (huv : Prefix u v) (hlt : t.1 < u.1) : Child t s u := by
  refine ⟨htu, hlt, ?_⟩
  exact (huv.2 t.1 hlt (child_height h)).trans h.2.choose_spec

def extendNode (t : Node) (s : Label) : Node :=
  ⟨levelNext t.1, fun i => if h : i.1 < t.1 then t.2 ⟨i.1, h⟩ else s⟩

lemma extendNode_child (t : Node) (s : Label) : Child t s (extendNode t s) := by
  refine ⟨⟨(levelNext_gt t.1).le, ?_⟩, levelNext_gt t.1, ?_⟩
  · intro a ht hu
    simp [extendNode, ht]
  · simp [extendNode]

def historyPrefix (b : History) (n : ℕ) : Label :=
  List.ofFn (fun i : Fin n => b i.1)

lemma historyPrefix_length (b : History) (n : ℕ) :
    (historyPrefix b n).length = n := by simp [historyPrefix]

lemma historyPrefix_length_eq {b c : History} {n m : ℕ}
    (h : historyPrefix b n = historyPrefix c m) : n = m := by
  simpa [historyPrefix_length] using congrArg List.length h

lemma mk_node_le : Cardinal.mk Node ≤ Cardinal.continuum := by
  change Cardinal.mk (Σ a : Level, Set.Iio a → Label) ≤ Cardinal.continuum
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun a : Level => Cardinal.mk (Set.Iio a → Label)) ≤
        Cardinal.sum (fun _ : Level => Cardinal.continuum) := by
      apply Cardinal.sum_le_sum
      intro a
      rw [Cardinal.mk_arrow, mk_label]
      simpa only [Cardinal.lift_id] using (Cardinal.power_le_power_left Cardinal.continuum_ne_zero
        (Cardinal.mk_le_aleph0_iff.mpr (level_initial_countable a))).trans_eq
          Cardinal.continuum_power_aleph0
    _ = Cardinal.mk Level * Cardinal.continuum := Cardinal.sum_const' _ _
    _ ≤ Cardinal.continuum * Cardinal.continuum := by
      apply mul_le_mul'
      · rw [mk_level]
        exact Cardinal.aleph_one_le_continuum
      · exact le_rfl
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

lemma mk_vertex_le : Cardinal.mk Vertex ≤ Cardinal.mk Letter := by
  rw [mk_letter]
  calc
    Cardinal.mk Vertex = Cardinal.mk Node * Cardinal.mk History := by
      simp [Vertex]
    _ ≤ Cardinal.continuum * Cardinal.continuum :=
      mul_le_mul' mk_node_le mk_history.le
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

theorem vertex_cardinality : Cardinal.mk Vertex = Cardinal.continuum := by
  apply le_antisymm
  · simpa only [mk_letter] using mk_vertex_le
  · rw [← mk_history]
    exact Cardinal.mk_le_of_injective
      (f := fun b : History => ((⟨levelZero, fun _ => []⟩ : Node), b))
      (fun _ _ h => congrArg Prod.snd h)

def vertexCode : Vertex ↪ Letter :=
  Classical.choice ((Cardinal.le_def Vertex Letter).mp mk_vertex_le)

def targetPoint (t : Node) (s : Label) (a : Letter) :
    {v : Vertex // Child t s v.1} := by
  classical
  letI : Nonempty {v : Vertex // Child t s v.1} :=
    ⟨⟨(extendNode t s, fun _ => ∅), extendNode_child t s⟩⟩
  exact Function.invFun (fun v : {v : Vertex // Child t s v.1} => vertexCode v.1) a

def target (t : Node) (s : Label) (a : Letter) : Vertex := (targetPoint t s a).1

lemma target_child (t : Node) (s : Label) (a : Letter) : Child t s (target t s a).1 :=
  (targetPoint t s a).2

lemma target_hits (t : Node) (s : Label) (v : Vertex) (hv : Child t s v.1) :
    ∃ a, target t s a = v := by
  classical
  let _ : Nonempty {v : Vertex // Child t s v.1} :=
    ⟨⟨(extendNode t s, fun _ => ∅), extendNode_child t s⟩⟩
  refine ⟨vertexCode v, ?_⟩
  change (Function.invFun (fun w : {v : Vertex // Child t s v.1} => vertexCode w.1)
    (vertexCode v)).1 = v
  have hi : Function.Injective (fun w : {v : Vertex // Child t s v.1} => vertexCode w.1) :=
    vertexCode.injective.comp Subtype.val_injective
  exact congrArg Subtype.val (Function.leftInverse_invFun hi ⟨v, hv⟩)

def Forward (u v : Vertex) : Prop :=
  ∃ n : ℕ, v = target u.1 (historyPrefix u.2 n) (u.2 n)

lemma forward_child {u v : Vertex} (h : Forward u v) :
    ∃ n, Child u.1 (historyPrefix u.2 n) v.1 := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n, target_child _ _ _⟩

lemma forward_height {u v : Vertex} (h : Forward u v) : u.1.1 < v.1.1 := by
  obtain ⟨n, hn⟩ := forward_child h
  exact child_height hn

def graph : SimpleGraph Vertex where
  Adj u v := Forward u v ∨ Forward v u
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by
    intro u h
    exact lt_irrefl u.1.1 (forward_height (h.elim id id))⟩

lemma adjacent_comparable {u v : Vertex} (h : graph.Adj u v) :
    Prefix u.1 v.1 ∨ Prefix v.1 u.1 := by
  rcases h with h | h
  · exact Or.inl (forward_child h).choose_spec.1
  · exact Or.inr (forward_child h).choose_spec.1

lemma adjacent_different_heights {u v : Vertex} (h : graph.Adj u v) : u.1.1 ≠ v.1.1 := by
  rcases h with h | h
  · exact (forward_height h).ne
  · exact (forward_height h).ne'

lemma adjacent_forward_of_height {u v : Vertex} (h : graph.Adj u v)
    (huv : u.1.1 < v.1.1) : Forward u v := by
  rcases h with h | h
  · exact h
  · exact False.elim (lt_asymm huv (forward_height h))

def chainLabel (t : ℕ → Node) (a : Level) : Label := by
  classical
  exact if h : ∃ n, a < (t n).1 then (t h.choose).2 ⟨a, h.choose_spec⟩ else []

lemma chainLabel_eq (t : ℕ → Node) (ht : ∀ n m, n ≤ m → Prefix (t n) (t m))
    (n : ℕ) (a : Level) (ha : a < (t n).1) :
    chainLabel t a = (t n).2 ⟨a, ha⟩ := by
  classical
  have hex : ∃ m, a < (t m).1 := ⟨n, ha⟩
  dsimp [chainLabel]
  rw [dif_pos hex]
  rcases le_total hex.choose n with h | h
  · exact (ht hex.choose n h).2 a hex.choose_spec ha
  · exact ((ht n hex.choose h).2 a ha hex.choose_spec).symm

def chainUpper (t : ℕ → Node) : Node :=
  ⟨(level_bound (fun n => (t n).1)).choose, fun a => chainLabel t a.1⟩

lemma prefix_chainUpper (t : ℕ → Node)
    (ht : ∀ n m, n ≤ m → Prefix (t n) (t m)) (n : ℕ) :
    Prefix (t n) (chainUpper t) := by
  refine ⟨((level_bound (fun n => (t n).1)).choose_spec n).le, ?_⟩
  intro a ha hb
  exact (chainLabel_eq t ht n a ha).symm

def Drops (c : Vertex → ℕ) (k : ℕ) (t : Node) : Prop :=
  ∀ v : Vertex, Prefix t v.1 → c v ≠ k

def trimColor (c : Vertex → ℕ) (k : ℕ) (t : Node) : Node := by
  classical
  exact if h : ∃ u, Prefix t u ∧ Drops c k u then h.choose else t

lemma trimColor_extends (c : Vertex → ℕ) (k : ℕ) (t : Node) :
    Prefix t (trimColor c k t) := by
  classical
  unfold trimColor
  split
  · exact Exists.choose_spec ‹∃ u, Prefix t u ∧ Drops c k u› |>.1
  · exact prefix_refl t

lemma trimColor_drops (c : Vertex → ℕ) (k : ℕ) (t : Node)
    (h : ∃ u, Prefix t u ∧ Drops c k u) : Drops c k (trimColor c k t) := by
  classical
  unfold trimColor
  rw [dif_pos h]
  exact h.choose_spec.2

def paletteChain (c : Vertex → ℕ) : ℕ → Node
  | 0 => ⟨levelZero, fun _ => []⟩
  | n + 1 => trimColor c n (paletteChain c n)

lemma paletteChain_increasing (c : Vertex → ℕ) (n m : ℕ) (h : n ≤ m) :
    Prefix (paletteChain c n) (paletteChain c m) := by
  induction m, h using Nat.le_induction with
  | base => exact prefix_refl _
  | succ m hm ih => exact prefix_trans ih (trimColor_extends c m _)

def StablePalette (c : Vertex → ℕ) (t : Node) : Prop :=
  ∀ u : Node, Prefix t u → ∀ k : ℕ,
    (∃ v : Vertex, Prefix t v.1 ∧ c v = k) →
      ∃ v : Vertex, Prefix u v.1 ∧ c v = k

lemma exists_stablePalette (c : Vertex → ℕ) : ∃ t : Node, StablePalette c t := by
  classical
  let t := chainUpper (paletteChain c)
  have ht (n : ℕ) : Prefix (paletteChain c n) t :=
    prefix_chainUpper _ (paletteChain_increasing c) n
  refine ⟨t, ?_⟩
  intro u htu k hk
  have hnot : ¬ ∃ w, Prefix (paletteChain c k) w ∧ Drops c k w := by
    intro hex
    obtain ⟨v, htv, hcv⟩ := hk
    have hd : Drops c k (paletteChain c (k + 1)) := trimColor_drops c k _ hex
    exact hd v (prefix_trans (ht (k + 1)) htv) hcv
  by_contra hmissing
  apply hnot
  refine ⟨u, prefix_trans (ht k) htu, ?_⟩
  intro v huv hcv
  exact hmissing ⟨v, huv, hcv⟩

lemma stablePalette_child_color (c : Vertex → ℕ) (t : Node) (ht : StablePalette c t)
    (s : Label) (k : ℕ) (hk : ∃ v : Vertex, Prefix t v.1 ∧ c v = k) :
    ∃ a : Letter, c (target t s a) = k := by
  obtain ⟨v, hv, hcv⟩ := ht (extendNode t s) (extendNode_child t s).1 k hk
  obtain ⟨a, ha⟩ := target_hits t s v (child_upwards (extendNode_child t s) hv)
  exact ⟨a, ha ▸ hcv⟩

def paletteSchedule (c : Vertex → ℕ) (t : Node) (n : ℕ) : ℕ := by
  classical
  exact if ∃ v : Vertex, Prefix t v.1 ∧ c v = n then n else c (t, fun _ => ∅)

lemma paletteSchedule_present (c : Vertex → ℕ) (t : Node) (n : ℕ) :
    ∃ v : Vertex, Prefix t v.1 ∧ c v = paletteSchedule c t n := by
  classical
  unfold paletteSchedule
  split
  · exact ‹∃ v : Vertex, Prefix t v.1 ∧ c v = n›
  · exact ⟨(t, fun _ => ∅), prefix_refl t, rfl⟩

def diagonalHistory (select : Label → Letter) : ℕ → Letter :=
  WellFounded.fix (wellFounded_lt : WellFounded ((· < ·) : ℕ → ℕ → Prop))
    (fun n previous => select (List.ofFn fun i : Fin n => previous i.1 i.2))

lemma diagonalHistory_eq (select : Label → Letter) (n : ℕ) :
    diagonalHistory select n = select (historyPrefix (diagonalHistory select) n) := by
  rw [diagonalHistory, WellFounded.fix_eq]
  rfl

lemma every_nat_coloring_conflict (c : Vertex → ℕ) :
    ∃ u v : Vertex, graph.Adj u v ∧ c u = c v := by
  classical
  obtain ⟨t, ht⟩ := exists_stablePalette c
  have possible (s : Label) :
      ∃ a : Letter, c (target t s a) = paletteSchedule c t s.length :=
    stablePalette_child_color c t ht s _ (paletteSchedule_present c t _)
  let select : Label → Letter := fun s => (possible s).choose
  let b : History := diagonalHistory select
  let u : Vertex := (t, b)
  let k : ℕ := c u
  let v : Vertex := target t (historyPrefix b k) (b k)
  have hk : ∃ w : Vertex, Prefix t w.1 ∧ c w = k := ⟨u, prefix_refl t, rfl⟩
  have hb : b k = select (historyPrefix b k) := diagonalHistory_eq select k
  have hv : c v = k := by
    change c (target t (historyPrefix b k) (b k)) = k
    rw [hb]
    have h : c (target t (historyPrefix b k) (select (historyPrefix b k))) =
        paletteSchedule c t (historyPrefix b k).length :=
      (possible (historyPrefix b k)).choose_spec
    have hschedule : paletteSchedule c t (historyPrefix b k).length = k := by
      rw [historyPrefix_length]
      simp [paletteSchedule, hk]
    exact h.trans hschedule
  exact ⟨u, v, Or.inl ⟨k, rfl⟩, hv.symm⟩

def Agree (b c : History) (k : ℕ) : Prop := ∀ i, i < k → b i = c i

lemma agree_refl (b : History) (k : ℕ) : Agree b b k := fun _ _ => rfl

lemma agree_mono {b c : History} {k n : ℕ} (h : Agree b c k) (hn : n ≤ k) :
    Agree b c n := fun i hi => h i (hi.trans_le hn)

lemma agree_trans {b c d : History} {k : ℕ} (hbc : Agree b c k) (hcd : Agree c d k) :
    Agree b d k := fun i hi => (hbc i hi).trans (hcd i hi)

lemma historyPrefix_eq_of_agree {b c : History} {k : ℕ} (h : Agree b c k) :
    historyPrefix b k = historyPrefix c k := by
  apply congrArg List.ofFn
  funext i
  exact h i.1 i.2

lemma agree_of_historyPrefix_eq {b c : History} {k : ℕ}
    (h : historyPrefix b k = historyPrefix c k) : Agree b c k := by
  intro i hi
  exact congrFun (List.ofFn_injective h) ⟨i, hi⟩

def Inside (t : Node) (b : History) (k : ℕ) (v : Vertex) : Prop :=
  (v.1 = t ∧ Agree v.2 b k) ∨
    ∃ c : History, ∃ n : ℕ, k ≤ n ∧ Agree c b k ∧ Child t (historyPrefix c n) v.1

def Frontier (t : Node) (b : History) (k : ℕ) : Set Vertex :=
  Set.range (fun i : Fin k => target t (historyPrefix b i.1) (b i.1))

lemma frontier_finite (t : Node) (b : History) (k : ℕ) : (Frontier t b k).Finite :=
  Set.finite_range _

lemma frontier_misses_bag (t : Node) (b : History) (k : ℕ) (v : Vertex)
    (hv : v.1 = t) : v ∉ Frontier t b k := by
  rintro ⟨i, hi⟩
  change target t (historyPrefix b i.1) (b i.1) = v at hi
  have h := child_height (target_child t (historyPrefix b i.1) (b i.1))
  rw [hi, hv] at h
  exact lt_irrefl _ h

lemma inside_base (t : Node) (b : History) (k : ℕ) : Inside t b k (t, b) :=
  Or.inl ⟨rfl, agree_refl b k⟩

lemma not_inside_bag {t : Node} {b c : History} {k : ℕ} (h : ¬ Agree c b k) :
    ¬ Inside t b k (t, c) := by
  rintro (⟨_, hc⟩ | ⟨d, n, _, _, hd⟩)
  · exact h hc
  · exact lt_irrefl _ (child_height hd)

lemma inside_boundary {t : Node} {b : History} {k : ℕ} {u v : Vertex}
    (hu : Inside t b k u) (hv : Prefix t v.1) (hadj : graph.Adj u v) :
    Inside t b k v ∨ v ∈ Frontier t b k := by
  classical
  rcases hadj with hforward | hbackward
  · obtain ⟨n, rfl⟩ := hforward
    rcases hu with ⟨hnode, hagree⟩ | ⟨c, m, hkm, hagree, hc⟩
    · by_cases hn : n < k
      · right
        have hp := historyPrefix_eq_of_agree (agree_mono hagree hn.le)
        have ha := hagree n hn
        change target u.1 (historyPrefix u.2 n) (u.2 n) ∈ Frontier t b k
        rw [hnode, hp, ha]
        exact ⟨⟨n, hn⟩, rfl⟩
      · left
        right
        refine ⟨u.2, n, Nat.le_of_not_gt hn, hagree, ?_⟩
        simpa [hnode] using target_child u.1 (historyPrefix u.2 n) (u.2 n)
    · left
      right
      exact ⟨c, m, hkm, hagree,
        child_upwards hc (target_child u.1 (historyPrefix u.2 n) (u.2 n)).1⟩
  · obtain ⟨n, hn⟩ := hbackward
    have hvu : Child v.1 (historyPrefix v.2 n) u.1 := by
      rw [hn]
      exact target_child _ _ _
    rcases hu with ⟨hnode, _⟩ | ⟨c, m, hkm, hagree, hc⟩
    · have hlt := child_height hvu
      rw [hnode] at hlt
      exact False.elim ((not_lt_of_ge hv.1) hlt)
    · by_cases hnode : v.1 = t
      · have hlabels : historyPrefix v.2 n = historyPrefix c m := by
          apply child_unique (t := t) (u := u.1)
          · simpa [hnode] using hvu
          · exact hc
        have hnm := historyPrefix_length_eq hlabels
        subst m
        left
        left
        exact ⟨hnode, agree_trans
          (agree_mono (agree_of_historyPrefix_eq hlabels) hkm) hagree⟩
      · have hlt : t.1 < v.1.1 := by
          apply lt_of_le_of_ne hv.1
          intro hlevels
          exact hnode (prefix_eq_of_height_eq hv hlevels).symm
        left
        right
        exact ⟨c, m, hkm, hagree, child_downwards hc hv hvu.1 hlt⟩

lemma walk_preserves_on {α : Type*} {G : SimpleGraph α} {S P : α → Prop}
    (hstep : ∀ a b, S a → S b → G.Adj a b → P a → P b)
    {a b : α} (p : G.Walk a b) (hs : ∀ x ∈ p.support, S x) (ha : P a) : P b := by
  induction p with
  | nil => exact ha
  | @cons a c b hac p ih =>
    apply ih
    · intro x hx
      exact hs x (by simp [SimpleGraph.Walk.support_cons, hx])
    · exact hstep a c (hs a (by simp [SimpleGraph.Walk.support_cons]))
        (hs c (by simp [SimpleGraph.Walk.support_cons])) hac ha

lemma mem_support_dropLast {α : Type*} {G : SimpleGraph α} {v : α} :
    ∀ {w : α} (q : G.Walk w v) {x : α},
      x ∈ q.support → x ≠ v → x ∈ q.support.dropLast := by
  intro w q
  induction q with
  | nil =>
    intro x hx hxv
    rw [SimpleGraph.Walk.support_nil] at hx
    exact absurd (List.mem_singleton.mp hx) hxv
  | cons _ r ih =>
    intro x hx hxv
    rw [SimpleGraph.Walk.support_cons] at hx ⊢
    rw [List.dropLast_cons_of_ne_nil r.support_ne_nil]
    rcases List.mem_cons.mp hx with h1 | h1
    · exact List.mem_cons.mpr (Or.inl h1)
    · exact List.mem_cons.mpr (Or.inr (ih h1 hxv))

lemma mem_interior {α : Type*} {G : SimpleGraph α} {u v x : α}
    (p : G.Walk u v) (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    x ∈ p.support.tail.dropLast := by
  rw [← SimpleGraph.Walk.cons_tail_support p] at hx
  rcases List.mem_cons.mp hx with h1 | h1
  · exact absurd h1 hxu
  · cases p with
    | nil => simp at h1
    | cons _ q =>
      rw [SimpleGraph.Walk.support_cons] at h1
      rw [SimpleGraph.Walk.support_cons]
      simpa using mem_support_dropLast q (by simpa using h1) hxv

lemma infinite_connected_avoids {α : Type*} {G : SimpleGraph α}
    (hG : G.InfinitelyConnected) {u v : α} (huv : u ≠ v)
    (S : Set α) (hS : S.Finite) (hu : u ∉ S) (hv : v ∉ S) :
    ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ S := by
  classical
  obtain ⟨P, hP, _, hdisjoint⟩ := @hG.2 u v huv
  let badAt (x : α) : Set (G.Walk u v) :=
    {p | p ∈ P ∧ x ∈ p.support.tail.dropLast}
  have hbadAt (x : α) : (badAt x).Finite := by
    apply Set.Subsingleton.finite
    intro p hp q hq
    by_contra hpq
    exact List.disjoint_left.mp (hdisjoint hp.1 hq.1 hpq) hp.2 hq.2
  have hbad : (⋃ x ∈ S, badAt x).Finite := hS.biUnion (fun x _ => hbadAt x)
  obtain ⟨p, hp, hgood⟩ := hP.exists_notMem_finite hbad
  refine ⟨p, ?_⟩
  intro x hx hxs
  apply hgood
  apply Set.mem_iUnion.mpr
  refine ⟨x, Set.mem_iUnion.mpr ⟨hxs, ?_⟩⟩
  exact ⟨hp, mem_interior p hx (fun h => hu (h ▸ hxs)) (fun h => hv (h ▸ hxs))⟩

lemma infinite_connected_connected {α : Type*} {G : SimpleGraph α}
    (hG : G.InfinitelyConnected) : G.Connected := by
  classical
  let _ : Nontrivial α := hG.1
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, inferInstance⟩
  rcases eq_or_ne u v with rfl | huv
  · exact SimpleGraph.Reachable.refl u
  · obtain ⟨P, hP, _, _⟩ := @hG.2 u v huv
    obtain ⟨p, _⟩ := hP.nonempty
    exact ⟨p⟩

lemma infinite_connected_infinite {α : Type*} {G : SimpleGraph α}
    (hG : G.InfinitelyConnected) : Infinite α := by
  classical
  rcases finite_or_infinite α with hfinite | hinfinite
  · let _ : Finite α := hfinite
    let _ : Fintype α := Fintype.ofFinite α
    let _ : Nontrivial α := hG.1
    obtain ⟨u, v, huv⟩ := exists_pair_ne α
    obtain ⟨P, hP, hp, _⟩ := @hG.2 u v huv
    have hfinitePaths : {p : G.Walk u v | p.IsPath}.Finite :=
      Set.finite_def.mpr ⟨SimpleGraph.Path.instFintype G⟩
    exact False.elim (hP (hfinitePaths.subset hp))
  · exact hinfinite

lemma infinite_connected_neighbors {α : Type*} {G : SimpleGraph α}
    (hG : G.InfinitelyConnected) (u : α) : (G.neighborSet u).Infinite := by
  classical
  let _ : Infinite α := infinite_connected_infinite hG
  intro hfinite
  obtain ⟨v, hv⟩ := (hfinite.insert u).exists_notMem
  have hvprops : v ≠ u ∧ v ∉ G.neighborSet u := by
    simpa only [Set.mem_insert_iff, not_or] using hv
  have hvu : v ≠ u := hvprops.1
  obtain ⟨p, hp⟩ := infinite_connected_avoids hG hvu.symm (G.neighborSet u)
    hfinite (by simp) hvprops.2
  cases p with
  | nil => exact hvu rfl
  | @cons a b c hab p => exact hp b (by simp [SimpleGraph.Walk.support_cons]) hab

lemma adjacent_preserves_cone {t : Node} {u v : Vertex}
    (htu : Prefix t u.1) (hmin : t.1 ≤ v.1.1) (hadj : graph.Adj u v) : Prefix t v.1 := by
  rcases adjacent_comparable hadj with huv | hvu
  · exact prefix_trans htu huv
  · rcases prefixes_comparable htu hvu with htv | hvt
    · exact htv
    · have heq : v.1 = t := prefix_eq_of_height_eq hvt (le_antisymm hvt.1 hmin)
      simpa [heq] using prefix_refl t

lemma adjacent_preserves_child {t : Node} {s : Label} {u v : Vertex}
    (hu : Child t s u.1) (hv : Prefix t v.1) (hne : v.1 ≠ t)
    (hadj : graph.Adj u v) : Child t s v.1 := by
  rcases hadj with hforward | hbackward
  · exact child_upwards hu (forward_child hforward).choose_spec.1
  · apply child_downwards hu hv (forward_child hbackward).choose_spec.1
    by_contra h
    have heq : t = v.1 := prefix_eq_of_height_eq hv (le_antisymm hv.1 (not_lt.mp h))
    exact hne heq.symm

lemma forward_same_child_unique {r u v : Vertex} {s : Label}
    (hru : Forward r u) (hrv : Forward r v)
    (hu : Child r.1 s u.1) (hv : Child r.1 s v.1) : u = v := by
  obtain ⟨n, hn⟩ := hru
  obtain ⟨m, hm⟩ := hrv
  have hlabeln : historyPrefix r.2 n = s := by
    apply child_unique _ hu
    rw [hn]
    exact target_child _ _ _
  have hlabelm : historyPrefix r.2 m = s := by
    apply child_unique _ hv
    rw [hm]
    exact target_child _ _ _
  have hnm : n = m := historyPrefix_length_eq (hlabeln.trans hlabelm.symm)
  subst m
  exact hn.trans hm.symm

theorem no_infinitelyConnected_induce (W : Set Vertex) :
    ¬ (graph.induce W).InfinitelyConnected := by
  classical
  intro hG
  let _ : Nontrivial W := hG.1
  obtain ⟨a, ha, hminimal⟩ := (wellFounded_lt : WellFounded ((· < ·) : Level → Level → Prop)).has_min
    (Set.range (fun v : W => v.1.1.1)) (Set.range_nonempty _)
  obtain ⟨r, rfl⟩ := ha
  let t : Node := r.1.1
  have hmin (v : W) : t.1 ≤ v.1.1.1 := le_of_not_gt (hminimal _ ⟨v, rfl⟩)
  have hcone (v : W) : Prefix t v.1.1 := by
    obtain ⟨p⟩ := (infinite_connected_connected hG) r v
    exact walk_preserves_on
      (S := fun _ : W => True) (P := fun w : W => Prefix t w.1.1)
      (fun _ y _ _ hadj hx => adjacent_preserves_cone hx (hmin y) hadj)
      p (fun _ _ => trivial) (prefix_refl t)
  have hbag (w : W) (hw : w.1.1 = t) : w = r := by
    by_contra hne
    have hhist : w.1.2 ≠ r.1.2 := by
      intro h
      apply hne
      apply Subtype.ext
      exact Prod.ext hw h
    obtain ⟨n, hn⟩ : ∃ n, w.1.2 n ≠ r.1.2 n := by
      by_contra h
      push Not at h
      exact hhist (funext h)
    have hnotAgree : ¬ Agree w.1.2 r.1.2 (n + 1) :=
      fun hagree => hn (hagree n (Nat.lt_succ_self n))
    let F : Set Vertex := Frontier t r.1.2 (n + 1)
    let S : Set W := {x | x.1 ∈ F}
    have hS : S.Finite := (frontier_finite t r.1.2 (n + 1)).preimage
      Subtype.val_injective.injOn
    have hrS : r ∉ S := frontier_misses_bag t r.1.2 (n + 1) r.1 rfl
    have hwS : w ∉ S := frontier_misses_bag t r.1.2 (n + 1) w.1 hw
    obtain ⟨p, hp⟩ := infinite_connected_avoids hG (Ne.symm hne) S hS hrS hwS
    have hinside : Inside t r.1.2 (n + 1) w.1 := by
      apply walk_preserves_on
        (S := fun x : W => x.1 ∉ F)
        (P := fun x : W => Inside t r.1.2 (n + 1) x.1)
        (fun x y _ hy hadj hx => (inside_boundary hx (hcone y) hadj).resolve_right hy)
        p hp (inside_base t r.1.2 (n + 1))
    rcases hinside with ⟨_, hagree⟩ | ⟨c, m, _, _, hc⟩
    · exact hnotAgree hagree
    · have hlt := child_height hc
      rw [hw] at hlt
      exact lt_irrefl t.1 hlt
  obtain ⟨u, hu, v, hv, huv⟩ := (infinite_connected_neighbors hG r).nontrivial
  have hforward (w : W) (hw : (graph.induce W).Adj r w) : Forward r.1 w.1 := by
    change Forward r.1 w.1 ∨ Forward w.1 r.1 at hw
    rcases hw with h | h
    · exact h
    · exact False.elim ((not_lt_of_ge (hmin w)) (forward_height h))
  obtain ⟨n, hchild⟩ := forward_child (hforward u hu)
  have hru : r ≠ u := (graph.induce W).ne_of_adj hu
  have hrv : r ≠ v := (graph.induce W).ne_of_adj hv
  obtain ⟨p, hp⟩ := infinite_connected_avoids hG huv {r} (Set.finite_singleton r)
    (fun h => hru (Set.mem_singleton_iff.mp h).symm)
    (fun h => hrv (Set.mem_singleton_iff.mp h).symm)
  have hchildv : Child t (historyPrefix r.1.2 n) v.1.1 := by
    apply walk_preserves_on
      (S := fun x : W => x ≠ r)
      (P := fun x : W => Child t (historyPrefix r.1.2 n) x.1.1)
      (fun x y _ hy hadj hx => adjacent_preserves_child hx (hcone y)
        (fun hyt => hy (hbag y hyt)) hadj)
      p (fun x hx hxr => hp x hx (by simp [hxr])) hchild
  exact huv (Subtype.ext (forward_same_child_unique (hforward u hu) (hforward v hv)
    hchild hchildv))

theorem chromaticCardinal_eq : graph.chromaticCardinal = Cardinal.aleph 1 := by
  classical
  have hupper : graph.chromaticCardinal ≤ Cardinal.aleph 1 := by
    rw [← mk_level]
    apply csInf_le (OrderBot.bddBelow _)
    refine ⟨Level, rfl, ?_⟩
    exact ⟨SimpleGraph.Coloring.mk (fun v : Vertex => v.1.1)
      (fun h => adjacent_different_heights h)⟩
  have hlower : ¬ graph.chromaticCardinal ≤ Cardinal.aleph0 := by
    intro h
    have hnonempty : {κ : Cardinal | ∃ (C : Type) (_ : Cardinal.mk C = κ),
        Nonempty (graph.Coloring C)}.Nonempty :=
      ⟨Cardinal.mk Vertex, Vertex, rfl, ⟨graph.selfColoring⟩⟩
    obtain ⟨C, hC, hcolor⟩ := csInf_mem hnonempty
    have hsmall : Cardinal.mk C ≤ Cardinal.aleph0 := hC.trans_le h
    let _ : Countable C := Cardinal.mk_le_aleph0_iff.mp hsmall
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat C
    obtain ⟨color⟩ := hcolor
    let coloring : graph.Coloring ℕ := graph.recolorOfEmbedding ⟨f, hf⟩ color
    obtain ⟨u, v, huv, heq⟩ := every_nat_coloring_conflict coloring
    exact coloring.valid huv heq
  exact le_antisymm hupper (Cardinal.aleph_one_le_iff.mpr (lt_of_not_ge hlower))

end Erdos1068Counterexample

theorem OMA.disproof : ¬ (type_of% @Erdos1068.erdos_1068) := by
  intro h
  obtain ⟨s, _, hs⟩ := h Erdos1068Counterexample.Vertex
    Erdos1068Counterexample.graph Erdos1068Counterexample.chromaticCardinal_eq
  exact Erdos1068Counterexample.no_infinitelyConnected_induce s hs

end

