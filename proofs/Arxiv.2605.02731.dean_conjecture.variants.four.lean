import FormalConjectures.Arxiv.«2605.02731».DeanCycles
-- Problem: Dean's conjecture on cycles of length divisible by `k` — four
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2605.02731/DeanCycles.lean:79 (declaration Arxiv.«2605.02731».dean_conjecture.variants.four)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Team skeleton for Arxiv.2605.02731.dean_conjecture.variants.four
(min degree >= 4 implies a cycle of length divisible by 4).
Route: .oma/scratch/dean4/adv2/ROUTE.md (max cut, suppress degree-2 vertices,
weighted parity lemma, lift).  Each lemma below is assigned to one agent.
Do not change any definition or lemma statement; prove only your own lemma.
-/

namespace OMA.Dean4

open SimpleGraph Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Weight of a walk: sum of `wt` over its darts. -/
noncomputable def walkWt {G : SimpleGraph V} {R : Type} [AddCommMonoid R] (wt : V → V → R)
    {u v : V} (p : G.Walk u v) : R :=
  (p.darts.map (fun d => wt d.fst d.snd)).sum

/-! ## L1 + L2: maximum cut (agent L12) -/

/-- Number of neighbours of `v` on the other side of the cut `c`. -/
noncomputable def opp (G : SimpleGraph V) (c : V → Bool) (v : V) : ℕ :=
  ((Finset.univ.filter (fun w => G.Adj v w)).filter (fun w => c w ≠ c v)).card

/-- Number of neighbours of `v` on the same side of the cut `c`. -/
noncomputable def same (G : SimpleGraph V) (c : V → Bool) (v : V) : ℕ :=
  ((Finset.univ.filter (fun w => G.Adj v w)).filter (fun w => c w = c v)).card

/-- The bipartite subgraph of cut edges. -/
def cutGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ c v ≠ c w
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun e => h.2 e.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem opp_eq_sum (G : SimpleGraph V) (c : V → Bool) (v : V) :
    opp G c v = ∑ u, if G.Adj v u ∧ c u ≠ c v then 1 else 0 := by
  unfold opp
  rw [Finset.filter_filter, Finset.card_filter]

theorem same_eq_sum (G : SimpleGraph V) (c : V → Bool) (v : V) :
    same G c v = ∑ u, if G.Adj v u ∧ c u = c v then 1 else 0 := by
  unfold same
  rw [Finset.filter_filter, Finset.card_filter]

theorem sum_flip_aux {W : Type} [Fintype W] [DecidableEq W] (g g' : W → ℕ) (x : W)
    (h : ∀ u, u ≠ x → g' u = g u) :
    ∑ u, g' u + g x = ∑ u, g u + g' x := by
  rw [← Finset.add_sum_erase Finset.univ g' (Finset.mem_univ x),
    ← Finset.add_sum_erase Finset.univ g (Finset.mem_univ x)]
  have hs : ∑ u ∈ Finset.univ.erase x, g' u = ∑ u ∈ Finset.univ.erase x, g u :=
    Finset.sum_congr rfl (fun u hu => h u (Finset.ne_of_mem_erase hu))
  omega

/-- Total of the opposite-side degrees (twice the number of cut edges). -/
noncomputable def tot (G : SimpleGraph V) (c : V → Bool) : ℕ := ∑ v, opp G c v

/-- Flipping the colour of `x` changes `opp` at a vertex `w ≠ x` as expected. -/
theorem opp_flip_vertex (G : SimpleGraph V) (c c' : V → Bool) (x w : V)
    (hc : ∀ u, u ≠ x → c' u = c u) (hw : w ≠ x) :
    opp G c' w + (if G.Adj w x ∧ c x ≠ c w then 1 else 0) =
      opp G c w + (if G.Adj w x ∧ c' x ≠ c w then 1 else 0) := by
  have hcw : c' w = c w := hc w hw
  have := sum_flip_aux (fun u => if G.Adj w u ∧ c u ≠ c w then 1 else 0)
    (fun u => if G.Adj w u ∧ c' u ≠ c' w then 1 else 0) x
    (fun u hu => by simp only [hc u hu, hcw])
  simp only [hcw] at this
  rw [opp_eq_sum, opp_eq_sum, hcw]
  omega

/-- Flipping the colour of `x` changes `same` at a vertex `w ≠ x` as expected. -/
theorem same_flip_vertex (G : SimpleGraph V) (c c' : V → Bool) (x w : V)
    (hc : ∀ u, u ≠ x → c' u = c u) (hw : w ≠ x) :
    same G c' w + (if G.Adj w x ∧ c x = c w then 1 else 0) =
      same G c w + (if G.Adj w x ∧ c' x = c w then 1 else 0) := by
  have hcw : c' w = c w := hc w hw
  have := sum_flip_aux (fun u => if G.Adj w u ∧ c u = c w then 1 else 0)
    (fun u => if G.Adj w u ∧ c' u = c' w then 1 else 0) x
    (fun u hu => by simp only [hc u hu, hcw])
  simp only [hcw] at this
  rw [same_eq_sum, same_eq_sum, hcw]
  omega

/-- Total effect of flipping the colour of `x`. -/
theorem tot_flip (G : SimpleGraph V) (c c' : V → Bool) (x : V)
    (hc : ∀ u, u ≠ x → c' u = c u) (hx : c' x = !c x) :
    tot G c' + 2 * opp G c x = tot G c + 2 * same G c x := by
  have hrow : opp G c' x = same G c x := by
    rw [opp_eq_sum, same_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u = x
    · subst hu; simp
    · rw [hc u hu, hx]
      by_cases hadj : G.Adj x u
      · cases c u <;> cases c x <;> simp [hadj]
      · simp [hadj]
  have hS : ∑ w ∈ Finset.univ.erase x, opp G c' w +
      ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c x ≠ c w then 1 else 0) =
      ∑ w ∈ Finset.univ.erase x, opp G c w +
      ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c' x ≠ c w then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w hw => by
      have := opp_flip_vertex G c c' x w hc (Finset.ne_of_mem_erase hw)
      omega)
  have e1 : ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c x ≠ c w then 1 else 0) =
      opp G c x := by
    rw [Finset.sum_erase _ (by simp), opp_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp [G.adj_comm, eq_comm]
  have e2 : ∑ w ∈ Finset.univ.erase x, (if G.Adj w x ∧ c' x ≠ c w then 1 else 0) =
      same G c x := by
    rw [Finset.sum_erase _ (by simp), same_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [G.adj_comm, hx]
    cases c u <;> cases c x <;> simp
  have hT' : tot G c' = opp G c' x + ∑ w ∈ Finset.univ.erase x, opp G c' w := by
    unfold tot
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  have hT : tot G c = opp G c x + ∑ w ∈ Finset.univ.erase x, opp G c w := by
    unfold tot
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  omega

/-- If `c` maximises `tot`, then `same v <= opp v` for every `v`. -/
theorem max_same_le (G : SimpleGraph V) (c : V → Bool)
    (hmax : ∀ d : V → Bool, tot G d ≤ tot G c) (v : V) :
    same G c v ≤ opp G c v := by
  have hx : (Function.update c v (!c v)) v = !c v := Function.update_self _ _ _
  have h := tot_flip G c (Function.update c v (!c v)) v
    (fun u hu => Function.update_of_ne hu _ _) hx
  have := hmax (Function.update c v (!c v))
  omega

/-- If `c` maximises `tot`, then the neighbour condition (M2) holds. -/
theorem max_nbr (G : SimpleGraph V) (c : V → Bool)
    (hmax : ∀ d : V → Bool, tot G d ≤ tot G c) (v w : V)
    (hv : same G c v = opp G c v) (hadj : G.Adj v w) (hwc : c w ≠ c v) :
    same G c w + 2 ≤ opp G c w := by
  have hx : (Function.update c v (!c v)) v = !c v := Function.update_self _ _ _
  have hc : ∀ u, u ≠ v → Function.update c v (!c v) u = c u :=
    fun u hu => Function.update_of_ne hu _ _
  have h := tot_flip G c (Function.update c v (!c v)) v hc hx
  have hT : tot G (Function.update c v (!c v)) = tot G c := by omega
  have hmax' : ∀ d : V → Bool, tot G d ≤ tot G (Function.update c v (!c v)) := by
    intro d
    rw [hT]
    exact hmax d
  have hM1 := max_same_le G (Function.update c v (!c v)) hmax' w
  have hw : w ≠ v := hadj.ne.symm
  have ho := opp_flip_vertex G c (Function.update c v (!c v)) v w hc hw
  have hs := same_flip_vertex G c (Function.update c v (!c v)) v w hc hw
  have hcw : c w = !c v := by
    cases h1 : c v <;> cases h2 : c w <;> simp_all
  have hne : c v ≠ c w := by
    rw [hcw]
    cases c v <;> simp
  have i1 : (if G.Adj w v ∧ c v ≠ c w then 1 else 0) = 1 := if_pos ⟨hadj.symm, hne⟩
  have i2 : (if G.Adj w v ∧ (Function.update c v (!c v)) v ≠ c w then 1 else 0) = 0 :=
    if_neg (fun h => h.2 (by rw [hx, hcw]))
  have i3 : (if G.Adj w v ∧ c v = c w then 1 else 0) = 0 := if_neg (fun h => hne h.2)
  have i4 : (if G.Adj w v ∧ (Function.update c v (!c v)) v = c w then 1 else 0) = 1 :=
    if_pos ⟨hadj.symm, by rw [hx, hcw]⟩
  rw [i1, i2] at ho
  rw [i3, i4] at hs
  omega

/-- L1: a locally optimal (maximum) cut. -/
theorem L1_maxcut (G : SimpleGraph V) :
    ∃ c : V → Bool, (∀ v, same G c v ≤ opp G c v) ∧
      (∀ v w, same G c v = opp G c v → G.Adj v w → c w ≠ c v →
        same G c w + 2 ≤ opp G c w) := by
  obtain ⟨c, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool)) (tot G)
    ⟨fun _ => true, Finset.mem_univ _⟩
  have hmax' : ∀ d : V → Bool, tot G d ≤ tot G c := fun d => hmax d (Finset.mem_univ d)
  exact ⟨c, fun v => max_same_le G c hmax' v,
    fun v w hv hadj hwc => max_nbr G c hmax' v w hv hadj hwc⟩

/-- L2: degrees in the cut graph; the only place where `4 ≤ minDegree` is used. -/
theorem L2_cut_degrees (G : SimpleGraph V) [DecidableRel G.Adj] (hG : 4 ≤ G.minDegree)
    (c : V → Bool) (h1 : ∀ v, same G c v ≤ opp G c v)
    (h2 : ∀ v w, same G c v = opp G c v → G.Adj v w → c w ≠ c v →
        same G c w + 2 ≤ opp G c w) :
    (∀ v, 2 ≤ (cutGraph G c).degree v) ∧
      (∀ y w, (cutGraph G c).degree y = 2 → (cutGraph G c).Adj y w →
        3 ≤ (cutGraph G c).degree w) := by
  have hdeg : ∀ v, (cutGraph G c).degree v = opp G c v := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    unfold opp
    congr 1
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    simp [cutGraph, ne_comm]
  have hsum : ∀ v, same G c v + opp G c v = G.degree v := by
    intro v
    have key := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun w => G.Adj v w))
      (fun w => c w = c v)
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    unfold same opp
    simp only [Finset.filter_filter, ne_eq]
    convert key using 2
    all_goals (congr 1; ext a; simp)
  have hdeg4 : ∀ v, 4 ≤ G.degree v := fun v => le_trans hG (G.minDegree_le_degree v)
  refine ⟨fun v => ?_, fun y w hy hadj => ?_⟩
  · rw [hdeg v]
    have := hsum v
    have := hdeg4 v
    have := h1 v
    omega
  · have hadj' : G.Adj y w ∧ c y ≠ c w := hadj
    rw [hdeg] at hy
    rw [hdeg w]
    have hsy : same G c y = opp G c y := by
      have := hsum y
      have := hdeg4 y
      have := h1 y
      omega
    have hw := h2 y w hsy hadj'.1 (fun e => hadj'.2 e.symm)
    have := hsum w
    have := hdeg4 w
    omega

/- ## The suppressed graph K -/

/-- Join good vertices that are adjacent in `H` or share a bad `H`-neighbour. -/
def supp (H : SimpleGraph V) (good : V → Prop) : SimpleGraph V where
  Adj v w := v ≠ w ∧ good v ∧ good w ∧ (H.Adj v w ∨ ∃ y, ¬ good y ∧ H.Adj v y ∧ H.Adj y w)
  symm := ⟨by
    rintro v w ⟨hne, hv, hw, h⟩
    refine ⟨hne.symm, hw, hv, ?_⟩
    rcases h with h | ⟨y, hy, h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨y, hy, h2.symm, h1.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Edge weight: 1 for an edge of `H`, 2 for a suppressed path of length 2. -/
noncomputable def wt1 (H : SimpleGraph V) (v w : V) : ℕ := if H.Adj v w then 1 else 2

/-- L3 (agent L3): good vertices keep degree at least 3 in the suppressed graph,
given no 4-cycle in `H`. -/
theorem L3_supp_degree (H : SimpleGraph V) (c : V → Bool)
    (hc : ∀ v w, H.Adj v w → c v ≠ c w)
    (h2 : ∀ v, 2 ≤ H.degree v)
    (hbad : ∀ y w, H.degree y = 2 → H.Adj y w → 3 ≤ H.degree w)
    (hno4 : ∀ a b c' d, H.Adj a b → H.Adj b c' → H.Adj c' d → H.Adj d a →
        a ≠ c' → b ≠ d → False) :
    ∀ v, 3 ≤ H.degree v → 3 ≤ (supp H (fun x => 3 ≤ H.degree x)).degree v := by
  intro v hv
  have hb3 : ∀ a b d : Bool, a ≠ b → a ≠ d → b ≠ d → False := by decide
  have rep : ∀ y, H.Adj v y → ∃ z, z ≠ v ∧ 3 ≤ H.degree z ∧
      (supp H (fun x => 3 ≤ H.degree x)).Adj v z ∧
      (z = y ∨ (¬ 3 ≤ H.degree y ∧ H.Adj y z)) := by
    intro y hy
    by_cases hg : 3 ≤ H.degree y
    · refine ⟨y, hy.ne.symm, hg, ?_, Or.inl rfl⟩
      show v ≠ y ∧ 3 ≤ H.degree v ∧ 3 ≤ H.degree y ∧
        (H.Adj v y ∨ ∃ x, ¬ 3 ≤ H.degree x ∧ H.Adj v x ∧ H.Adj x y)
      exact ⟨hy.ne, hv, hg, Or.inl hy⟩
    · have hd : H.degree y = 2 := by
        have := h2 y
        omega
      have hcard : 1 < (H.neighborFinset y).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hd]; norm_num
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
      rw [SimpleGraph.mem_neighborFinset] at ha hb
      have hw : ∃ w, H.Adj y w ∧ w ≠ v := by
        by_cases hav : a = v
        · exact ⟨b, hb, fun h => hab (hav.trans h.symm)⟩
        · exact ⟨a, ha, hav⟩
      obtain ⟨w, hyw, hwv⟩ := hw
      have hwg : 3 ≤ H.degree w := hbad y w hd hyw
      refine ⟨w, hwv, hwg, ?_, Or.inr ⟨hg, hyw⟩⟩
      exact ⟨hwv.symm, hv, hwg, Or.inr ⟨y, hg, hy, hyw⟩⟩
  have key : ∀ y1 y2 z1 z2 : V, H.Adj v y1 → H.Adj v y2 → y1 ≠ y2 → z1 ≠ v → z2 ≠ v →
      (z1 = y1 ∨ (¬ 3 ≤ H.degree y1 ∧ H.Adj y1 z1)) →
      (z2 = y2 ∨ (¬ 3 ≤ H.degree y2 ∧ H.Adj y2 z2)) → z1 ≠ z2 := by
    intro y1 y2 z1 z2 k1 k2 hne hz1 hz2 r1 r2 heq
    rcases r1 with e1 | ⟨-, a1⟩ <;> rcases r2 with e2 | ⟨-, a2⟩
    · exact hne (e1.symm.trans (heq.trans e2))
    · have hz : z2 = y1 := heq.symm.trans e1
      rw [hz] at a2
      exact hb3 (c v) (c y1) (c y2) (hc v y1 k1) (hc v y2 k2) (hc y1 y2 a2.symm)
    · have hz : z1 = y2 := heq.trans e2
      rw [hz] at a1
      exact hb3 (c v) (c y1) (c y2) (hc v y1 k1) (hc v y2 k2) (hc y1 y2 a1)
    · have hcd : H.Adj z1 y2 := by rw [heq]; exact a2.symm
      exact hno4 v y1 z1 y2 k1 a1 hcd k2.symm hz1.symm hne
  have hcard : 2 < (H.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
  obtain ⟨y1, h1, y2, h2m, y3, h3, n12, n13, n23⟩ := Finset.two_lt_card.1 hcard
  rw [SimpleGraph.mem_neighborFinset] at h1 h2m h3
  obtain ⟨z1, hz1v, -, hK1, r1⟩ := rep y1 h1
  obtain ⟨z2, hz2v, -, hK2, r2⟩ := rep y2 h2m
  obtain ⟨z3, hz3v, -, hK3, r3⟩ := rep y3 h3
  have k12 := key y1 y2 z1 z2 h1 h2m n12 hz1v hz2v r1 r2
  have k13 := key y1 y3 z1 z3 h1 h3 n13 hz1v hz3v r1 r3
  have k23 := key y2 y3 z2 z3 h2m h3 n23 hz2v hz3v r2 r3
  have hsub : 2 < ((supp H (fun x => 3 ≤ H.degree x)).neighborFinset v).card := by
    apply Finset.two_lt_card.2
    refine ⟨z1, ?_, z2, ?_, z3, ?_, k12, k13, k23⟩ <;>
      rw [SimpleGraph.mem_neighborFinset] <;> assumption
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hsub
  omega

/- ## L4: Theorem W (agent L4) -/

theorem walkWt_nil' {K : SimpleGraph V} (wt : V → V → ZMod 4) (a : V) :
    walkWt wt (Walk.nil : K.Walk a a) = 0 := by
  simp [walkWt]

theorem walkWt_cons' {K : SimpleGraph V} (wt : V → V → ZMod 4) {a b c : V} (h : K.Adj a b)
    (p : K.Walk b c) : walkWt wt (Walk.cons h p) = wt a b + walkWt wt p := by
  simp [walkWt]

theorem walkWt_append' {K : SimpleGraph V} (wt : V → V → ZMod 4) {a b c : V} (p : K.Walk a b)
    (q : K.Walk b c) : walkWt wt (p.append q) = walkWt wt p + walkWt wt q := by
  simp [walkWt, Walk.darts_append]

theorem walkWt_reverse' {K : SimpleGraph V} (wt : V → V → ZMod 4)
    (hsym : ∀ x y, wt x y = wt y x) {a b : V} (p : K.Walk a b) :
    walkWt wt p.reverse = walkWt wt p := by
  induction p with
  | nil => simp [walkWt]
  | @cons a' b' c' h p ih =>
    rw [Walk.reverse_cons, walkWt_append', ih, walkWt_cons', walkWt_cons', walkWt_nil']
    linear_combination hsym b' a'

theorem path_join {K : SimpleGraph V} {a c d b : V} (p : K.Walk a c) (h : K.Adj c d)
    (q : K.Walk d b) (hp : p.IsPath) (hq : q.IsPath) (hd : ∀ w ∈ p.support, w ∉ q.support) :
    (p.append (Walk.cons h q)).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons]
  exact List.Nodup.append hp.support_nodup hq.support_nodup (fun w h1 h2 => hd w h1 h2)

theorem path_split {K : SimpleGraph V} {a c d b : V} (p : K.Walk a c) (h : K.Adj c d)
    (q : K.Walk d b) (hP : (p.append (Walk.cons h q)).IsPath) :
    p.IsPath ∧ q.IsPath ∧ ∀ w ∈ p.support, w ∉ q.support := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
    List.nodup_append] at hP
  exact ⟨(Walk.isPath_def _).2 hP.1, (Walk.isPath_def _).2 hP.2.1,
    fun w h1 h2 => hP.2.2 w h1 w h2 rfl⟩

theorem path_ne {K : SimpleGraph V} {a b : V} (p : K.Walk a b) (hp : p.IsPath)
    (hl : 0 < p.length) : a ≠ b := by
  cases p with
  | nil => simp at hl
  | cons h q =>
    rw [Walk.cons_isPath_iff] at hp
    intro e
    subst e
    exact hp.2 q.end_mem_support

theorem pos_of_ne {K : SimpleGraph V} {a b : V} (p : K.Walk a b) (h : a ≠ b) :
    0 < p.length :=
  Nat.pos_of_ne_zero fun h0 => h (Walk.eq_of_length_eq_zero h0)

theorem cyc {K : SimpleGraph V} {a b : V} (p : K.Walk b a) (h : K.Adj a b) (hp : p.IsPath)
    (hl : 2 ≤ p.length) : (Walk.cons h p).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp, fun he => ?_⟩
  cases p with
  | nil => simp at hl
  | cons h' p' =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 h.ne
      subst h1
      cases p' with
      | nil => simp at hl
      | cons h'' p'' =>
        rw [Walk.cons_isPath_iff] at hp
        exact hp.1.2 p''.end_mem_support
    · exact hp.2 (Walk.snd_mem_support_of_mem_edges p' he)

theorem fan {K : SimpleGraph V} (wt : V → V → ZMod 4) (hsym : ∀ x y, wt x y = wt y x)
    (hall : ∀ (v : V) (p : K.Walk v v), p.IsCycle → walkWt wt p = 2)
    {x c y w : V} (R1 : K.Walk x c) (hcy : K.Adj c y) (R2 : K.Walk y w)
    (hxy : K.Adj x y) (hxw : K.Adj x w) (h1 : R1.IsPath) (h2 : R2.IsPath)
    (hd : ∀ a ∈ R1.support, a ∉ R2.support) (l1 : 0 < R1.length) (l2 : 0 < R2.length) :
    2 * wt x y = 2 := by
  have e1 := hall _ _ (cyc (R1.append (Walk.cons hcy Walk.nil)) hxy.symm
    (path_join R1 hcy Walk.nil h1 Walk.IsPath.nil
      (fun a ha hb => hd a ha (by
        simp at hb
        subst hb
        exact R2.start_mem_support)))
    (by simp [Walk.length_append]; omega))
  have e2 := hall _ _ (cyc (R1.append (Walk.cons hcy R2)) hxw.symm
    (path_join R1 hcy R2 h1 h2 hd) (by simp [Walk.length_append]; omega))
  have e3 := hall _ _ (cyc (Walk.cons hxy R2) hxw.symm
    ((Walk.cons_isPath_iff _ _).2 ⟨h2, hd x R1.start_mem_support⟩) (by simp; omega))
  simp only [walkWt_cons', walkWt_append', walkWt_nil'] at e1 e2 e3
  linear_combination e1 + e3 - e2 - hsym y x

theorem theta {K : SimpleGraph V} (wt : V → V → ZMod 4) (hsym : ∀ x y, wt x y = wt y x)
    (hall : ∀ (v : V) (p : K.Walk v v), p.IsCycle → walkWt wt p = 2)
    {x u z t1 t2 : V} (S1 : K.Walk x u) (T : K.Walk z t1) (Q : K.Walk t1 t2)
    (huz : K.Adj u z) (hxz : K.Adj x z) (hx1 : K.Adj x t1) (hu2 : K.Adj u t2)
    (hS : S1.IsPath) (lS : 0 < S1.length) (hTQ : (T.append Q).IsPath) (lT : 0 < T.length)
    (hd : ∀ w ∈ S1.support, w ∉ (T.append Q).support) : False := by
  have hT : T.IsPath := hTQ.of_append_left
  have hQ : Q.IsPath := hTQ.of_append_right
  have hdT : ∀ w ∈ S1.support, w ∉ T.support := fun w hw h =>
    hd w hw ((Walk.mem_support_append_iff _ _).2 (Or.inl h))
  have hdQ : ∀ w ∈ S1.support, w ∉ Q.support := fun w hw h =>
    hd w hw ((Walk.mem_support_append_iff _ _).2 (Or.inr h))
  have hzQ : z ∉ Q.support := by
    intro hz
    have hn := hTQ.support_nodup
    rw [Walk.support_append] at hn
    have hzt : z ≠ t1 := path_ne T hT lT
    have hz' : z ∈ Q.support.tail := by
      rw [← Walk.cons_tail_support Q] at hz
      rcases List.mem_cons.1 hz with h | h
      · exact absurd h hzt
      · exact h
    exact (List.nodup_append.1 hn).2.2 z T.start_mem_support z hz' rfl
  have hxu : x ≠ u := path_ne S1 hS lS
  have hSr : S1.reverse.IsPath := (Walk.isPath_reverse_iff _).2 hS
  have f1 := fan wt hsym hall S1 huz T hxz hx1 hS hT hdT lS lT
  have f2 := fan wt hsym hall S1.reverse hxz (T.append Q) huz hu2 hSr hTQ
    (fun w hw => hd w (by simpa using hw)) (by simpa using lS)
    (by simp [Walk.length_append]; omega)
  have c1 := hall _ _ (cyc (S1.append (Walk.cons huz Walk.nil)) hxz.symm
    (path_join S1 huz Walk.nil hS Walk.IsPath.nil
      (fun a ha hb => hdT a ha (by
        simp at hb
        subst hb
        exact T.start_mem_support)))
    (by simp [Walk.length_append]; omega))
  have c7 := hall _ _ (cyc (Q.append (Walk.cons hu2.symm S1.reverse)) hx1
    (path_join Q hu2.symm S1.reverse hQ hSr
      (fun a ha hb => hdQ a (by simpa using hb) ha))
    (by simp [Walk.length_append]; omega))
  have hp6 : (Walk.cons huz (Walk.cons hxz.symm Walk.nil)).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩
    · simpa using hxz.ne'
    · simpa using ⟨huz.ne, hxu.symm⟩
  have c6 := hall _ _ (cyc
    (Q.append (Walk.cons hu2.symm (Walk.cons huz (Walk.cons hxz.symm Walk.nil)))) hx1
    (path_join Q hu2.symm _ hQ hp6 (fun a ha hb => by
      simp at hb
      rcases hb with rfl | rfl | rfl
      · exact hdQ _ S1.end_mem_support ha
      · exact hzQ ha
      · exact hdQ _ S1.start_mem_support ha))
    (by simp [Walk.length_append]))
  simp only [walkWt_cons', walkWt_append', walkWt_nil', walkWt_reverse' wt hsym]
    at f1 f2 c1 c6 c7
  have h24 : (2 : ZMod 4) = 4 := by
    linear_combination f1 + f2 - (c6 - c7 + c1) + 2 * hsym z x
  exact absurd h24 (by decide)

/-- A configuration: a longest path `S1 . (u z) . D` from `x` with a chord `x z`,
where `S1` has `n` edges. -/
def IsCfg (K : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (x u z y : V) (S1 : K.Walk x u) (D : K.Walk z y) (huz : K.Adj u z),
    K.Adj x z ∧ 0 < S1.length ∧ (S1.append (Walk.cons huz D)).IsPath ∧
    (∀ (a b : V) (q : K.Walk a b), q.IsPath → q.length ≤ S1.length + D.length + 1) ∧
    S1.length = n

theorem exists_concat {K : SimpleGraph V} {a b : V} (p : K.Walk a b) (hl : 0 < p.length) :
    ∃ (c : V) (q : K.Walk a c) (h : K.Adj c b), p = q.append (Walk.cons h Walk.nil) := by
  cases p with
  | nil => simp at hl
  | cons h p' =>
    obtain ⟨c, q, h', e⟩ := Walk.exists_cons_eq_concat h p'
    exact ⟨c, q, h', by rw [e, Walk.concat_eq_append]⟩

theorem key {K : SimpleGraph V} {x v u z y : V} (h : K.Adj x v) (S' : K.Walk v u)
    (D : K.Walk z y) (huz : K.Adj u z)
    (hP : ((Walk.cons h S').append (Walk.cons huz D)).IsPath)
    (hmax : ∀ (a b : V) (q : K.Walk a b), q.IsPath →
      q.length ≤ (Walk.cons h S').length + D.length + 1)
    (hmin : ∀ n, n < (Walk.cons h S').length → ¬ IsCfg K n) :
    ∀ w, K.Adj x w → w ∈ S'.support → w = v := by
  intro w hxw hw
  by_contra hwv
  obtain ⟨A, B, spec⟩ : ∃ (A : K.Walk v w) (B : K.Walk w u), A.append B = S' :=
    ⟨_, _, S'.take_spec hw⟩
  subst spec
  obtain ⟨c, q, hcw, eA⟩ := exists_concat A (pos_of_ne A (Ne.symm hwv))
  subst eA
  refine hmin (q.length + 1) ?_ ⟨x, c, w, y, Walk.cons h q, B.append (Walk.cons huz D), hcw,
    hxw, by simp, ?_, ?_, by simp⟩
  · simp [Walk.length_append]
  · have e : (Walk.cons h q).append (Walk.cons hcw (B.append (Walk.cons huz D))) =
        (Walk.cons h ((q.append (Walk.cons hcw Walk.nil)).append B)).append
          (Walk.cons huz D) := by
      simp only [Walk.cons_append, ← Walk.append_assoc, Walk.nil_append]
    rw [e]
    exact hP
  · intro a b p hp
    have := hmax a b p hp
    simp [Walk.length_append] at this ⊢
    omega

theorem far_nbr {K : SimpleGraph V} (hdeg : ∀ v, 0 < K.degree v → 3 ≤ K.degree v)
    {x u z y : V} (S1 : K.Walk x u) (D : K.Walk z y) (huz : K.Adj u z) (hxz : K.Adj x z)
    (lS : 0 < S1.length) (hP : (S1.append (Walk.cons huz D)).IsPath)
    (hmax : ∀ (a b : V) (q : K.Walk a b), q.IsPath → q.length ≤ S1.length + D.length + 1)
    (hmin : ∀ n, n < S1.length → ¬ IsCfg K n) :
    ∃ t, K.Adj x t ∧ t ∈ D.support ∧ t ≠ z := by
  by_contra hno
  push Not at hno
  have hon : ∀ w, K.Adj x w → w ∈ S1.support ∨ w ∈ D.support := by
    intro w hxw
    by_contra hc
    push Not at hc
    have hPw : (Walk.cons hxw.symm (S1.append (Walk.cons huz D))).IsPath := by
      rw [Walk.cons_isPath_iff]
      refine ⟨hP, ?_⟩
      rw [Walk.mem_support_append_iff]
      rintro (h1 | h1)
      · exact hc.1 h1
      · rw [Walk.support_cons, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact hc.1 S1.end_mem_support
        · exact hc.2 h1
    have := hmax _ _ _ hPw
    simp [Walk.length_append] at this
  have huniq : ∀ w w', K.Adj x w → K.Adj x w' → w ∈ S1.support → w' ∈ S1.support →
      w = w' := by
    cases S1 with
    | nil => simp at lS
    | cons h S' =>
      have k := key h S' D huz hP hmax hmin
      intro w w' hw hw' m m'
      rw [Walk.support_cons, List.mem_cons] at m m'
      rcases m with rfl | m
      · exact absurd hw (K.irrefl)
      rcases m' with rfl | m'
      · exact absurd hw' (K.irrefl)
      exact (k w hw m).trans (k w' hw' m').symm
  have h3 : 3 ≤ K.degree x := hdeg x ((K.degree_pos_iff_exists_adj x).2 ⟨z, hxz⟩)
  rw [← K.card_neighborFinset_eq_degree] at h3
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 h3
  rw [mem_neighborFinset] at ha hb hc
  have cl : ∀ w, K.Adj x w → w ∈ S1.support ∨ w = z := fun w hw =>
    (hon w hw).imp id (hno w hw)
  rcases cl a ha with pa | pa <;> rcases cl b hb with pb | pb <;> rcases cl c hc with pc | pc
  all_goals first
    | exact hab (huniq a b ha hb pa pb)
    | exact hac (huniq a c ha hc pa pc)
    | exact hbc (huniq b c hb hc pb pc)
    | exact hab (pa.trans pb.symm)
    | exact hac (pa.trans pc.symm)
    | exact hbc (pb.trans pc.symm)

theorem exists_cfg {K : SimpleGraph V} (hdeg : ∀ v, 0 < K.degree v → 3 ≤ K.degree v)
    (hedge : ∃ v w, K.Adj v w) : ∃ n, IsCfg K n := by
  obtain ⟨v0, w0, h0⟩ := hedge
  have hex : ∃ N, (∃ (a b : V) (q : K.Walk a b), q.IsPath ∧ q.length = N) ∧
      ∀ (a b : V) (q : K.Walk a b), q.IsPath → q.length ≤ N := by
    refine ⟨Nat.findGreatest (fun n => ∃ (a b : V) (q : K.Walk a b), q.IsPath ∧ q.length = n)
      (Fintype.card V), ?_, ?_⟩
    · exact Nat.findGreatest_spec (P := fun n => ∃ (a b : V) (q : K.Walk a b),
        q.IsPath ∧ q.length = n) (Nat.zero_le _) ⟨v0, v0, Walk.nil, Walk.IsPath.nil, rfl⟩
    · intro a b q hq
      exact Nat.le_findGreatest (P := fun n => ∃ (a b : V) (q : K.Walk a b),
        q.IsPath ∧ q.length = n) hq.length_lt.le ⟨a, b, q, hq, rfl⟩
  obtain ⟨N, ⟨a, b, P, hPp, hPl⟩, hle⟩ := hex
  have hN : 1 ≤ N := by
    have := hle _ _ (Walk.cons h0 Walk.nil) (by
      rw [Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simpa using h0.ne⟩)
    simpa using this
  cases P with
  | nil =>
    simp at hPl
    omega
  | @cons _ v1 _ h P' =>
    have hon : ∀ w, K.Adj a w → w ∈ P'.support := by
      intro w hw
      by_contra hc
      have hpw : (Walk.cons hw.symm (Walk.cons h P')).IsPath := by
        rw [Walk.cons_isPath_iff]
        refine ⟨hPp, ?_⟩
        rw [Walk.support_cons, List.mem_cons]
        rintro (e | e)
        · exact hw.ne e.symm
        · exact hc e
      have := hle _ _ _ hpw
      simp at this hPl
      omega
    have h3 : 3 ≤ K.degree a := hdeg a ((K.degree_pos_iff_exists_adj a).2 ⟨_, h⟩)
    rw [← K.card_neighborFinset_eq_degree] at h3
    obtain ⟨z, hz, hzv⟩ : ∃ z, K.Adj a z ∧ z ≠ v1 := by
      obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.1 h3
      rw [mem_neighborFinset] at hp hq
      by_cases e : p = v1
      · exact ⟨q, hq, fun e' => hpq (e.trans e'.symm)⟩
      · exact ⟨p, hp, e⟩
    obtain ⟨A, D, spec⟩ : ∃ (A : K.Walk v1 z) (D : K.Walk z b), A.append D = P' :=
      ⟨_, _, P'.take_spec (hon z hz)⟩
    subst spec
    obtain ⟨c, q, hcz, eA⟩ := exists_concat A (pos_of_ne A (Ne.symm hzv))
    subst eA
    refine ⟨q.length + 1, a, c, z, b, Walk.cons h q, D, hcz, hz, by simp, ?_, ?_, by simp⟩
    · have e : (Walk.cons h q).append (Walk.cons hcz D) =
          Walk.cons h ((q.append (Walk.cons hcz Walk.nil)).append D) := by
        simp only [Walk.cons_append, ← Walk.append_assoc, Walk.nil_append]
      rw [e]
      exact hPp
    · intro a' b' p hp
      have := hle a' b' p hp
      simp [Walk.length_append] at hPl ⊢
      omega

/-- L4: in a graph with an edge whose non-isolated vertices have degree at least 3,
some cycle has weight different from 2 modulo 4. -/
theorem L4_thmW (K : SimpleGraph V) (wt : V → V → ZMod 4) (hsym : ∀ x y, wt x y = wt y x)
    (hdeg : ∀ v, 0 < K.degree v → 3 ≤ K.degree v) (hedge : ∃ v w, K.Adj v w) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ walkWt wt p ≠ 2 := by
  by_contra hcon
  have hall : ∀ (v : V) (p : K.Walk v v), p.IsCycle → walkWt wt p = 2 := by
    intro v p hp
    by_contra h
    exact hcon ⟨v, p, hp, h⟩
  have hex := exists_cfg hdeg hedge
  obtain ⟨x, u, z, y, S1, D, huz, hxz, lS, hP, hmax, hn⟩ := Nat.find_spec hex
  have hmin : ∀ n, n < S1.length → ¬ IsCfg K n := fun n hlt =>
    Nat.find_min hex (hn ▸ hlt)
  obtain ⟨hS, hD, hd⟩ := path_split S1 huz D hP
  have hSr : S1.reverse.IsPath := (Walk.isPath_reverse_iff _).2 hS
  have hP' : (S1.reverse.append (Walk.cons hxz D)).IsPath :=
    path_join _ _ _ hSr hD (fun w hw => hd w (by simpa using hw))
  obtain ⟨t1, hx1, m1, n1⟩ := far_nbr hdeg S1 D huz hxz lS hP hmax hmin
  obtain ⟨t2, hu2, m2, n2⟩ := far_nbr hdeg S1.reverse D hxz huz (by simpa using lS) hP'
    (by simpa using hmax) (by simpa using hmin)
  obtain ⟨T, R, spec⟩ : ∃ (T : K.Walk z t1) (R : K.Walk t1 y), T.append R = D :=
    ⟨_, _, D.take_spec m1⟩
  have lT : 0 < T.length := pos_of_ne T (Ne.symm n1)
  subst spec
  rw [Walk.mem_support_append_iff] at m2
  rcases m2 with m2 | m2
  · obtain ⟨T', Q', spec'⟩ : ∃ (T' : K.Walk z t2) (Q' : K.Walk t2 t1), T'.append Q' = T :=
      ⟨_, _, T.take_spec m2⟩
    subst spec'
    exact theta wt hsym hall S1.reverse T' Q' hxz huz hu2 hx1 hSr (by simpa using lS)
      hD.of_append_left (pos_of_ne T' (Ne.symm n2))
      (fun w hw h => hd w (by simpa using hw)
        ((Walk.mem_support_append_iff _ _).2 (Or.inl h)))
  · obtain ⟨Q, R', spec'⟩ : ∃ (Q : K.Walk t1 t2) (R' : K.Walk t2 y), Q.append R' = R :=
      ⟨_, _, R.take_spec m2⟩
    subst spec'
    have hTQ : (T.append Q).IsPath := by
      rw [Walk.append_assoc] at hD
      exact hD.of_append_left
    exact theta wt hsym hall S1 T Q huz hxz hx1 hu2 hS lS hTQ lT
      (fun w hw h => hd w hw (by
        rw [Walk.append_assoc]
        exact (Walk.mem_support_append_iff _ _).2 (Or.inl h)))

/- ## L5: lifting cycles (agent L5) -/

omit [Fintype V] [DecidableEq V] in
/-- The weight of `cons h p` is the weight of the first dart plus the weight of `p`. -/
theorem walkWt_cons {G : SimpleGraph V} {R : Type} [AddCommMonoid R] (wt : V → V → R)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkWt wt (Walk.cons h p) = wt u v + walkWt wt p := by
  simp [walkWt]

omit [Fintype V] [DecidableEq V] in
/-- A walk of the suppressed graph that starts at a good vertex visits only good vertices. -/
theorem good_of_mem_support (H : SimpleGraph V) (good : V → Prop) :
    ∀ {u t : V} (p : (supp H good).Walk u t), good u → ∀ x ∈ p.support, good x := by
  intro u t p
  induction p with
  | nil =>
    intro hu x hx
    rw [Walk.support_nil, List.mem_singleton] at hx
    rw [hx]
    exact hu
  | cons h p ih =>
    intro hu x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact hu
    · exact ih h.2.2.1 x hx

omit [Fintype V] [DecidableEq V] in
/-- A path of the suppressed graph lifts to a path of `H` whose length is its weight.
Each vertex of the lift is a vertex of the path or a bad midpoint of one of its edges.
Each edge of the lift is an edge of the path or has a bad endpoint. -/
theorem lift_path (H : SimpleGraph V) (good : V → Prop)
    (htwo : ∀ y, ¬ good y → ∀ a b c', H.Adj y a → H.Adj y b → H.Adj y c' →
        a = b ∨ a = c' ∨ b = c') :
    ∀ {u t : V} (p : (supp H good).Walk u t), p.IsPath →
      ∃ q : H.Walk u t, q.IsPath ∧ q.length = walkWt (wt1 H) p ∧
        (∀ x ∈ q.support, x ∈ p.support ∨
          (¬ good x ∧ ∃ a b, s(a, b) ∈ p.edges ∧ H.Adj x a ∧ H.Adj x b)) ∧
        (∀ e ∈ q.edges, e ∈ p.edges ∨ ∃ x ∈ e, ¬ good x) := by
  intro u t p
  induction p with
  | nil =>
    intro _
    exact ⟨Walk.nil, Walk.IsPath.nil, by simp [walkWt], by simp, by simp⟩
  | @cons u u' t h p ih =>
    intro hp
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨q, hq, hlen, hi, hii⟩ := ih hp.1
    have hu : good u := h.2.1
    have hu' : good u' := h.2.2.1
    have huq : u ∉ q.support := by
      intro hx
      rcases hi u hx with h1 | h1
      · exact hp.2 h1
      · exact h1.1 hu
    have hi' : ∀ x ∈ q.support, x ∈ (Walk.cons h p).support ∨
        (¬ good x ∧ ∃ a b, s(a, b) ∈ (Walk.cons h p).edges ∧ H.Adj x a ∧ H.Adj x b) := by
      intro x hx
      rcases hi x hx with h1 | ⟨h1, a, b, hab, h2, h3⟩
      · left
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ h1
      · right
        refine ⟨h1, a, b, ?_, h2, h3⟩
        rw [Walk.edges_cons]
        exact List.mem_cons_of_mem _ hab
    have hii' : ∀ e ∈ q.edges, e ∈ (Walk.cons h p).edges ∨ ∃ x ∈ e, ¬ good x := by
      intro e he
      rcases hii e he with h1 | h1
      · left
        rw [Walk.edges_cons]
        exact List.mem_cons_of_mem _ h1
      · exact Or.inr h1
    by_cases hadj : H.Adj u u'
    · refine ⟨Walk.cons hadj q, ?_, ?_, ?_, ?_⟩
      · rw [Walk.cons_isPath_iff]
        exact ⟨hq, huq⟩
      · rw [Walk.length_cons, walkWt_cons, hlen, wt1, if_pos hadj, add_comm]
      · intro x hx
        rw [Walk.support_cons, List.mem_cons] at hx
        rcases hx with hx | hx
        · left
          rw [hx, Walk.support_cons]
          exact List.mem_cons_self
        · exact hi' x hx
      · intro e he
        rw [Walk.edges_cons, List.mem_cons] at he
        rcases he with he | he
        · left
          rw [he, Walk.edges_cons]
          exact List.mem_cons_self
        · exact hii' e he
    · obtain ⟨y, hy, huy, hyu'⟩ : ∃ y, ¬ good y ∧ H.Adj u y ∧ H.Adj y u' := by
        rcases h.2.2.2 with h1 | h1
        · exact absurd h1 hadj
        · exact h1
      have hyq : y ∉ q.support := by
        intro hx
        rcases hi y hx with h1 | ⟨_, a, b, hab, h2, h3⟩
        · exact hy (good_of_mem_support H good p hu' y h1)
        · have hne : a ≠ b := (p.adj_of_mem_edges hab).ne
          rcases htwo y hy a b u h2 h3 huy.symm with h4 | h4 | h4
          · exact hne h4
          · exact hp.2 (h4 ▸ p.fst_mem_support_of_mem_edges hab)
          · exact hp.2 (h4 ▸ p.snd_mem_support_of_mem_edges hab)
      refine ⟨Walk.cons huy (Walk.cons hyu' q), ?_, ?_, ?_, ?_⟩
      · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.support_cons, List.mem_cons]
        refine ⟨⟨hq, hyq⟩, ?_⟩
        rintro (h1 | h1)
        · exact huy.ne h1
        · exact huq h1
      · rw [Walk.length_cons, Walk.length_cons, walkWt_cons, hlen, wt1, if_neg hadj]
        omega
      · intro x hx
        rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hx
        rcases hx with hx | hx | hx
        · left
          rw [hx, Walk.support_cons]
          exact List.mem_cons_self
        · right
          rw [hx]
          refine ⟨hy, u, u', ?_, huy.symm, hyu'⟩
          rw [Walk.edges_cons]
          exact List.mem_cons_self
        · exact hi' x hx
      · intro e he
        rw [Walk.edges_cons, Walk.edges_cons, List.mem_cons, List.mem_cons] at he
        rcases he with he | he | he
        · right
          rw [he]
          exact ⟨y, Sym2.mem_mk_right u y, hy⟩
        · right
          rw [he]
          exact ⟨y, Sym2.mem_mk_left y u', hy⟩
        · exact hii' e he

/-- L5: a cycle of the suppressed graph lifts to a cycle of `H` whose length is its weight. -/
theorem L5_lift (H : SimpleGraph V) (good : V → Prop)
    (htwo : ∀ y, ¬ good y → ∀ a b c', H.Adj y a → H.Adj y b → H.Adj y c' →
        a = b ∨ a = c' ∨ b = c') :
    ∀ (v : V) (C : (supp H good).Walk v v), C.IsCycle →
      ∃ (u : V) (D : H.Walk u u), D.IsCycle ∧ D.length = walkWt (wt1 H) C := by
  intro v C hC
  cases C with
  | nil => exact absurd rfl hC.ne_nil
  | @cons _ u' _ h p =>
    rw [Walk.cons_isCycle_iff] at hC
    obtain ⟨q, hq, hlen, hi, hii⟩ := lift_path H good htwo p hC.1
    have hv : good v := h.2.1
    have hu' : good u' := h.2.2.1
    by_cases hadj : H.Adj v u'
    · refine ⟨v, Walk.cons hadj q, ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff]
        refine ⟨hq, fun he => ?_⟩
        rcases hii _ he with h1 | ⟨x, hx, hxg⟩
        · exact hC.2 h1
        · rw [Sym2.mem_iff] at hx
          rcases hx with hx | hx
          · exact hxg (hx ▸ hv)
          · exact hxg (hx ▸ hu')
      · rw [Walk.length_cons, walkWt_cons, hlen, wt1, if_pos hadj, add_comm]
    · obtain ⟨y, hy, hvy, hyu'⟩ : ∃ y, ¬ good y ∧ H.Adj v y ∧ H.Adj y u' := by
        rcases h.2.2.2 with h1 | h1
        · exact absurd h1 hadj
        · exact h1
      have hvu : v ≠ u' := h.1
      have hyq : y ∉ q.support := by
        intro hx
        rcases hi y hx with h1 | ⟨_, a, b, hab, h2, h3⟩
        · exact hy (good_of_mem_support H good p hu' y h1)
        · have hne : a ≠ b := (p.adj_of_mem_edges hab).ne
          apply hC.2
          rcases htwo y hy a b v h2 h3 hvy.symm with h4 | h4 | h4
          · exact absurd h4 hne
          · rcases htwo y hy a b u' h2 h3 hyu' with h5 | h5 | h5
            · exact absurd h5 hne
            · exact absurd (h4.symm.trans h5) hvu
            · have e : s(v, u') = s(a, b) := by rw [h4, h5]
              rw [e]
              exact hab
          · rcases htwo y hy a b u' h2 h3 hyu' with h5 | h5 | h5
            · exact absurd h5 hne
            · have e : s(v, u') = s(a, b) := by rw [h4, h5, Sym2.eq_swap]
              rw [e]
              exact hab
            · exact absurd (h4.symm.trans h5) hvu
      refine ⟨v, Walk.cons hvy (Walk.cons hyu' q), ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Walk.edges_cons, List.mem_cons]
        refine ⟨⟨hq, hyq⟩, ?_⟩
        rintro (h1 | h1)
        · rw [Sym2.eq_iff] at h1
          rcases h1 with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hvy.ne h1
          · exact hvu h1
        · exact hyq (q.snd_mem_support_of_mem_edges h1)
      · rw [Walk.length_cons, Walk.length_cons, walkWt_cons, hlen, wt1, if_neg hadj]
        omega

/-! ## Assembly helpers (proved) -/

theorem len_mem_cycleLengths {H G : SimpleGraph V} (hle : H ≤ G) {u : V} (D : H.Walk u u)
    (hD : D.IsCycle) : D.length ∈ G.cycleLengths := by
  show ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.length = D.length
  exact ⟨u, D.mapLe hle, hD.mapLe hle, by simp⟩

theorem walkWt_natCast {G : SimpleGraph V} (f : V → V → ℕ) {u v : V} (p : G.Walk u v) :
    walkWt (fun a b => ((f a b : ℕ) : ZMod 4)) p = ((walkWt f p : ℕ) : ZMod 4) := by
  unfold walkWt
  rw [Nat.cast_list_sum, List.map_map]
  rfl

theorem walk_parity_of_cut {H : SimpleGraph V} (c : V → Bool)
    (hc : ∀ v w, H.Adj v w → c v ≠ c w) {u v : V} (p : H.Walk u v) :
    (p.length % 2 = 0 ∧ c u = c v) ∨ (p.length % 2 = 1 ∧ c u ≠ c v) := by
  induction p with
  | nil => left; simp
  | @cons a x b h p ih =>
    have hax : c a ≠ c x := hc a x h
    rw [SimpleGraph.Walk.length_cons]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      refine ⟨by omega, ?_⟩
      rw [← h2]
      exact hax
    · left
      refine ⟨by omega, ?_⟩
      revert hax h2
      cases c a <;> cases c x <;> cases c b <;> simp

theorem core_false {G H : SimpleGraph V} (c : V → Bool) (hle : H ≤ G)
    (hc : ∀ v w, H.Adj v w → c v ≠ c w) (h2 : ∀ v, 2 ≤ H.degree v)
    (hbad : ∀ y w, H.degree y = 2 → H.Adj y w → 3 ≤ H.degree w)
    (hV : Nonempty V) (hNC : ∀ m ∈ G.cycleLengths, ¬ 4 ∣ m) : False := by
  have hno4 : ∀ a b c' d, H.Adj a b → H.Adj b c' → H.Adj c' d → H.Adj d a →
      a ≠ c' → b ≠ d → False := by
    intro a b c' d hab hbc hcd hda hac hbd
    have hpc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      simp [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.edges, Sym2.eq_iff,
        hab.ne, hbc.ne, hcd.ne, hda.ne, hac, hbd, hac.symm, hbd.symm, hda.ne.symm,
        hab.ne.symm, hbc.ne.symm, hcd.ne.symm]
    exact hNC _ (len_mem_cycleLengths hle _ hpc) (by simp)
  obtain ⟨v0⟩ := hV
  have hgood : ∃ g, 3 ≤ H.degree g := by
    by_cases hv : 3 ≤ H.degree v0
    · exact ⟨v0, hv⟩
    · have hd : H.degree v0 = 2 := by have := h2 v0; omega
      have hpos : 0 < H.degree v0 := by omega
      obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj H v0).1 hpos
      exact ⟨w, hbad v0 w hd hw⟩
  set K := OMA.Dean4.supp H (fun x => 3 ≤ H.degree x) with hK
  have hK3 : ∀ v, 3 ≤ H.degree v → 3 ≤ K.degree v :=
    L3_supp_degree H c hc h2 hbad hno4
  have hdegK : ∀ v, 0 < K.degree v → 3 ≤ K.degree v := by
    intro v hv
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj K v).1 hv
    obtain ⟨-, hgv, -, -⟩ := hw
    exact hK3 v hgv
  have hedge : ∃ v w, K.Adj v w := by
    obtain ⟨g, hg⟩ := hgood
    have hpos : 0 < K.degree g := by have := hK3 g hg; omega
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj K g).1 hpos
    exact ⟨g, w, hw⟩
  have hsym : ∀ x y, ((wt1 H x y : ℕ) : ZMod 4) = ((wt1 H y x : ℕ) : ZMod 4) := by
    intro x y
    unfold wt1
    rw [H.adj_comm]
  obtain ⟨v, p, hpc, hne⟩ := L4_thmW K (fun x y => ((wt1 H x y : ℕ) : ZMod 4)) hsym hdegK hedge
  have htwo : ∀ y, ¬ (fun x => 3 ≤ H.degree x) y → ∀ a b c', H.Adj y a → H.Adj y b →
      H.Adj y c' → a = b ∨ a = c' ∨ b = c' := by
    intro y hy a b c' ha hb hc'
    by_contra hcon'
    push_neg at hcon'
    have hsub : ({a, b, c'} : Finset V) ⊆ H.neighborFinset y := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [SimpleGraph.mem_neighborFinset]
      rcases hx with rfl | rfl | rfl <;> assumption
    have hcard := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
    have h3 : 2 < ({a, b, c'} : Finset V).card :=
      Finset.two_lt_card.2 ⟨a, by simp, b, by simp, c', by simp, hcon'.1, hcon'.2.1, hcon'.2.2⟩
    have hy' : ¬ 3 ≤ H.degree y := hy
    omega
  obtain ⟨u, D, hD, hlen⟩ := L5_lift H (fun x => 3 ≤ H.degree x) htwo v p hpc
  have hpar := walk_parity_of_cut c hc D
  have hev : D.length % 2 = 0 := by
    rcases hpar with h | h
    · exact h.1
    · exact absurd rfl h.2
  have hcast : ((D.length : ℕ) : ZMod 4) = walkWt (fun x y => ((wt1 H x y : ℕ) : ZMod 4)) p := by
    rw [hlen]
    exact (walkWt_natCast (wt1 H) p).symm
  have hn2 : ((D.length : ℕ) : ZMod 4) ≠ 2 := by
    rw [hcast]
    exact hne
  have h4 : 4 ∣ D.length := by
    rcases (by omega : D.length % 4 = 0 ∨ D.length % 4 = 2) with h | h
    · exact Nat.dvd_of_mod_eq_zero h
    · exfalso
      apply hn2
      have e : ((D.length % 4 : ℕ) : ZMod 4) = ((2 : ℕ) : ZMod 4) := by rw [h]
      rw [ZMod.natCast_mod] at e
      rw [e]
      decide
  exact hNC _ (len_mem_cycleLengths hle D hD) h4

end OMA.Dean4

open OMA.Dean4

theorem OMA.solution : type_of% @Arxiv.«2605.02731».dean_conjecture.variants.four := by
  intro V _ _ G _ hG
  by_contra hcon
  have hNC : ∀ m ∈ G.cycleLengths, ¬ 4 ∣ m := fun m hm hd => hcon ⟨m, hm, hd⟩
  have hV : Nonempty V := by
    rcases isEmpty_or_nonempty V with hE | hN
    · exfalso
      haveI : Subsingleton V := ⟨fun a => isEmptyElim a⟩
      have h0 : G.minDegree = 0 := SimpleGraph.minDegree_of_subsingleton G
      omega
    · exact hN
  obtain ⟨c, h1, h2⟩ := L1_maxcut G
  obtain ⟨hd2, hbad⟩ := L2_cut_degrees G hG c h1 h2
  exact core_false c (fun v w h => (show G.Adj v w ∧ c v ≠ c w from h).1)
    (fun v w h => (show G.Adj v w ∧ c v ≠ c w from h).2) hd2 hbad hV hNC
