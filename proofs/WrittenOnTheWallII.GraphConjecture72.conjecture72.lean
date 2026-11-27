import FormalConjectures.WrittenOnTheWallII.GraphConjecture72

-- Problem: Written on the Wall II - Conjecture 72
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture72.lean:53 (declaration WrittenOnTheWallII.GraphConjecture72.conjecture72)
-- Credit: @jonas-klesen (the owner of the agent is credited as the solver)
--
-- DISPROOF. Counterexample on 19 vertices: a path of five layers of sizes 7, 2, 1, 2, 7 in which
-- consecutive layers are completely joined, the two outer layers are cliques and the three inner
-- layers are independent sets.
--   * eccentricities are 4, 3, 2, 3, 4 on the layers, so the average eccentricity is 70 / 19;
--   * the middle vertex has four pairwise non-adjacent neighbours, so max_v l(v) >= 4;
--   * every induced tree has at most 5 vertices.
-- Hence ceil (70 / 19 + 4 / 3) = 6 > 5.

open SimpleGraph

universe u

namespace OMA72

/-- The layer of a vertex index: sizes 7, 2, 1, 2, 7. -/
def lay (i : ℕ) : ℕ :=
  if i < 7 then 0 else if i < 9 then 1 else if i < 10 then 2 else if i < 12 then 3 else 4

/-- The vertex type, lifted to an arbitrary universe. -/
abbrev V : Type u := ULift.{u} (Fin 19)

/-- The layer of a vertex. -/
def L (x : V.{u}) : ℕ := lay x.down.val

/-- The counterexample graph. -/
def G : SimpleGraph V.{u} where
  Adj x y := x ≠ y ∧ (L x + 1 = L y ∨ L y + 1 = L x ∨ (L x = L y ∧ (L x = 0 ∨ L x = 4)))
  symm := ⟨by
    rintro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | ⟨h, h'⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h.symm, by omega⟩)⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The middle vertex. -/
def c : V.{u} := ULift.up 9

lemma val_ne {x y : V.{u}} (h : x ≠ y) : x.down.val ≠ y.down.val := by
  intro h'
  apply h
  cases x
  cases y
  simp only [ULift.up.injEq]
  exact Fin.ext h'

lemma L_le (x : V.{u}) : L x ≤ 4 := by
  unfold L lay
  split_ifs <;> omega

lemma L_eq0 (x : V.{u}) : L x = 0 ↔ x.down.val < 7 := by
  unfold L lay
  split_ifs <;> constructor <;> intro h <;> first | omega | exact h.elim

lemma L_eq1 (x : V.{u}) : L x = 1 ↔ (x.down.val = 7 ∨ x.down.val = 8) := by
  unfold L lay
  split_ifs <;> constructor <;> intro h <;> first | omega | exact h.elim

lemma L_eq2 (x : V.{u}) : L x = 2 ↔ x.down.val = 9 := by
  unfold L lay
  split_ifs <;> constructor <;> intro h <;> first | omega | exact h.elim

lemma L_eq3 (x : V.{u}) : L x = 3 ↔ (x.down.val = 10 ∨ x.down.val = 11) := by
  unfold L lay
  split_ifs <;> constructor <;> intro h <;> first | omega | exact h.elim

lemma L_eq4 (x : V.{u}) : L x = 4 ↔ 12 ≤ x.down.val := by
  unfold L lay
  split_ifs <;> constructor <;> intro h <;> first | omega | exact h.elim

lemma eq_c {x : V.{u}} (h : L x = 2) : x = c := by
  have h9 := (L_eq2 x).1 h
  cases x with
  | up a =>
    simp only [c, ULift.up.injEq]
    exact Fin.ext h9

lemma L_c : L (c : V.{u}) = 2 := by
  rw [L_eq2]
  rfl

lemma ne_of_L {x y : V.{u}} (h : L x ≠ L y) : x ≠ y := by
  intro hxy
  exact h (by rw [hxy])

lemma adj_lay {x y : V.{u}} (h : G.Adj x y) : L y ≤ L x + 1 ∧ L x ≤ L y + 1 := by
  rcases h.2 with h | h | ⟨h, _⟩ <;> omega

lemma adj_up {x y : V.{u}} (h : L x + 1 = L y) : G.Adj x y :=
  ⟨ne_of_L (by omega), Or.inl h⟩

lemma adj_down {x y : V.{u}} (h : L y + 1 = L x) : G.Adj x y :=
  ⟨ne_of_L (by omega), Or.inr (Or.inl h)⟩

lemma adj_zero {x y : V.{u}} (hne : x ≠ y) (hx : L x = 0) (hy : L y = 0) : G.Adj x y :=
  ⟨hne, Or.inr (Or.inr ⟨by omega, Or.inl hx⟩)⟩

lemma adj_four {x y : V.{u}} (hne : x ≠ y) (hx : L x = 4) (hy : L y = 4) : G.Adj x y :=
  ⟨hne, Or.inr (Or.inr ⟨by omega, Or.inr hx⟩)⟩

/- ### Connectedness -/

lemma reach_c (x : V.{u}) : G.Reachable c x := by
  have hx := L_le x
  have hc : L (c : V.{u}) = 2 := L_c
  have h7 : L (ULift.up 7 : V.{u}) = 1 := by rw [L_eq1]; left; rfl
  have h10 : L (ULift.up 10 : V.{u}) = 3 := by rw [L_eq3]; left; rfl
  have hx' : L x = 0 ∨ L x = 1 ∨ L x = 2 ∨ L x = 3 ∨ L x = 4 := by omega
  rcases hx' with h | h | h | h | h
  · exact ((adj_down (x := c) (y := ULift.up 7) (by omega)).reachable).trans
      ((adj_down (x := ULift.up 7) (y := x) (by omega)).reachable)
  · exact (adj_down (x := c) (y := x) (by omega)).reachable
  · rw [eq_c h]
  · exact (adj_up (x := c) (y := x) (by omega)).reachable
  · exact ((adj_up (x := c) (y := ULift.up 10) (by omega)).reachable).trans
      ((adj_up (x := ULift.up 10) (y := x) (by omega)).reachable)

lemma connected : (G : SimpleGraph V.{u}).Connected where
  preconnected := fun x y => (reach_c x).symm.trans (reach_c y)
  nonempty := ⟨c⟩

/- ### Eccentricities -/

lemma walk_lay {x y : V.{u}} (p : G.Walk x y) :
    L y ≤ L x + p.length ∧ L x ≤ L y + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := adj_lay h
    rw [Walk.length_cons]
    omega

lemma eccent_ne_top (x : V.{u}) : G.eccent x ≠ ⊤ := by
  obtain ⟨v, hv⟩ := (G : SimpleGraph V.{u}).exists_edist_eq_eccent_of_finite x
  rw [← hv, ← (connected.preconnected x v).coe_dist_eq_edist]
  exact ENat.natCast_ne_top _

lemma dist_le_eccent (x y : V.{u}) : G.dist x y ≤ (G.eccent x).toNat := by
  have h2 : (G.dist x y : ℕ∞) ≤ G.eccent x := by
    rw [(connected.preconnected x y).coe_dist_eq_edist]
    exact edist_le_eccent
  have h4 := ENat.toNat_le_toNat h2 (eccent_ne_top x)
  simpa using h4

lemma lay_le_dist (x y : V.{u}) : L y ≤ L x + G.dist x y ∧ L x ≤ L y + G.dist x y := by
  obtain ⟨p, hp⟩ := connected.exists_walk_length_eq_dist x y
  rw [← hp]
  exact walk_lay p

/-- The eccentricity of a vertex of layer `i` is at least `max i (4 - i)`. -/
lemma eccent_ge (x : V.{u}) : max (L x) (4 - L x) ≤ (G.eccent x).toNat := by
  have h0 : L (ULift.up 0 : V.{u}) = 0 := by rw [L_eq0]; decide
  have h18 : L (ULift.up 18 : V.{u}) = 4 := by rw [L_eq4]; decide
  have a := (lay_le_dist x (ULift.up 0)).2
  have b := (lay_le_dist x (ULift.up 18)).1
  have a' := dist_le_eccent x (ULift.up 0)
  have b' := dist_le_eccent x (ULift.up 18)
  omega

lemma sum_bound : ∑ x : V.{u}, max (L x) (4 - L x) = 70 := by
  rw [← Equiv.sum_comp Equiv.ulift.symm]
  decide

lemma avg_ge : (70 : ℝ) / 19 ≤ (G : SimpleGraph V.{u}).averageEccentricity := by
  unfold averageEccentricity
  have hcard : (Fintype.card V.{u} : ℝ) = 19 := by simp
  rw [hcard]
  have hsum : (70 : ℕ) ≤ ∑ x : V.{u}, (G.eccent x).toNat := by
    rw [← sum_bound]
    exact Finset.sum_le_sum (fun x _ => eccent_ge x)
  have hsum' : (70 : ℝ) ≤ ((∑ x : V.{u}, (G.eccent x).toNat : ℕ) : ℝ) := by exact_mod_cast hsum
  have h19 : (0 : ℝ) < 19 := by norm_num
  have := div_le_div_of_nonneg_right hsum' h19.le
  simpa using this

/- ### Local independence of the middle vertex -/

/-- Four neighbours of the middle vertex. -/
def idx : Fin 4 → Fin 19 := ![7, 8, 10, 11]

lemma idx_inj : Function.Injective idx := by decide

lemma adj_c_idx (i : Fin 4) : G.Adj (c : V.{u}) (ULift.up (idx i)) := by
  have hc : L (c : V.{u}) = 2 := L_c
  fin_cases i
  · exact adj_down (by rw [hc, (L_eq1 _).2 (Or.inl rfl)])
  · exact adj_down (by rw [hc, (L_eq1 _).2 (Or.inr rfl)])
  · exact adj_up (by rw [hc, (L_eq3 _).2 (Or.inl rfl)])
  · exact adj_up (by rw [hc, (L_eq3 _).2 (Or.inr rfl)])

lemma four_le_indep : 4 ≤ indepNeighborsCard (G : SimpleGraph V.{u}) c := by
  unfold indepNeighborsCard
  let f : Fin 4 ↪ ↥((G : SimpleGraph V.{u}).neighborSet c) :=
    ⟨fun i => ⟨ULift.up (idx i), adj_c_idx i⟩, by
      intro i j h
      have h' := congrArg (fun z : ↥((G : SimpleGraph V.{u}).neighborSet c) => z.1.down) h
      exact idx_inj h'⟩
  have hind : ((G : SimpleGraph V.{u}).induce (G.neighborSet c)).IsIndepSet
      ((Finset.univ.map f : Finset ↥((G : SimpleGraph V.{u}).neighborSet c)) : Set _) := by
    intro x _ y _ _ hadj
    have hx : G.Adj c x.1 := x.2
    have hy : G.Adj c y.1 := y.2
    have hxy : G.Adj x.1 y.1 := hadj
    have hc : L (c : V.{u}) = 2 := L_c
    have h1 := adj_lay hx
    have h2 := adj_lay hy
    have h3 := adj_lay hxy
    rcases hx.2 with h | h | ⟨h, h'⟩ <;> rcases hy.2 with k | k | ⟨k, k'⟩ <;>
      rcases hxy.2 with m | m | ⟨m, m'⟩ <;> omega
  have := hind.card_le_indepNum
  simpa using this

lemma four_le_maxL (hne : (Finset.univ.image
    (fun v => indepNeighborsCard (G : SimpleGraph V.{u}) v)).Nonempty) :
    4 ≤ (Finset.univ.image (fun v => indepNeighborsCard (G : SimpleGraph V.{u}) v)).max' hne :=
  le_trans four_le_indep
    (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ c)))

/- ### Induced trees have at most five vertices -/

lemma acyc_no_triangle {W : Type u} {H : SimpleGraph W} (h : H.IsAcyclic) {x y z : W}
    (hxy : H.Adj x y) (hyz : H.Adj y z) (hxz : H.Adj x z) : False := by
  have hp : (Walk.cons hxy (Walk.cons hyz Walk.nil)).IsPath := by
    simp [Walk.cons_isPath_iff, hxy.ne, hyz.ne, hxz.ne]
  have hq : (Walk.cons hxz Walk.nil).IsPath := by
    simp [Walk.cons_isPath_iff, hxz.ne]
  have := (h.subsingleton_path x z).elim ⟨_, hp⟩ ⟨_, hq⟩
  have h2 := congrArg (fun P : H.Path x z => P.1.length) this
  simp at h2

lemma acyc_no_square {W : Type u} {H : SimpleGraph W} (h : H.IsAcyclic) {x y z w : W}
    (hxy : H.Adj x y) (hyz : H.Adj y z) (hxw : H.Adj x w) (hwz : H.Adj w z)
    (hxz : x ≠ z) (hyw : y ≠ w) : False := by
  have hp : (Walk.cons hxy (Walk.cons hyz Walk.nil)).IsPath := by
    simp [Walk.cons_isPath_iff, hxy.ne, hyz.ne, hxz]
  have hq : (Walk.cons hxw (Walk.cons hwz Walk.nil)).IsPath := by
    simp [Walk.cons_isPath_iff, hxw.ne, hwz.ne, hxz]
  have := (h.subsingleton_path x z).elim ⟨_, hp⟩ ⟨_, hq⟩
  have h2 := congrArg (fun P : H.Path x z => P.1.support) this
  simp at h2
  exact hyw h2

lemma tree_card_le (s : Finset V.{u})
    (hT : ((G : SimpleGraph V.{u}).induce (s : Set V.{u})).IsTree) : s.card ≤ 5 := by
  classical
  have tri : ∀ x y z : V.{u}, x ∈ s → y ∈ s → z ∈ s →
      G.Adj x y → G.Adj y z → G.Adj x z → False := by
    intro x y z hx hy hz hxy hyz hxz
    exact acyc_no_triangle hT.isAcyclic (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (z := ⟨z, hz⟩) hxy hyz hxz
  have sq : ∀ x y z w : V.{u}, x ∈ s → y ∈ s → z ∈ s → w ∈ s →
      G.Adj x y → G.Adj y z → G.Adj x w → G.Adj w z → x ≠ z → y ≠ w → False := by
    intro x y z w hx hy hz hw hxy hyz hxw hwz hxz hyw
    exact acyc_no_square hT.isAcyclic (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (z := ⟨z, hz⟩) (w := ⟨w, hw⟩)
      hxy hyz hxw hwz (fun h => hxz (congrArg Subtype.val h)) (fun h => hyw (congrArg Subtype.val h))
  have cut : c ∉ s → ∀ x ∈ s, ∀ y ∈ s, L x ≤ 1 → 3 ≤ L y → False := by
    intro hc x hx y hy hLx hLy
    obtain ⟨p⟩ := hT.connected.preconnected ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨d, _, hd1, hd2⟩ := p.exists_boundary_dart
      {v : ↥(s : Set V.{u}) | L v.1 ≤ 1} (by simpa using hLx) (by simp; omega)
    have hadj : G.Adj d.fst.1 d.snd.1 := d.adj
    have h1 := adj_lay hadj
    simp only [Set.mem_ofPred_eq, not_le] at hd1 hd2
    have h2 : L d.snd.1 = 2 := by omega
    have h3 : d.snd.1 = c := eq_c h2
    exact hc (h3 ▸ d.snd.2)
  -- layer counts
  set N : ℕ → ℕ := fun i => (s.filter (fun v => L v = i)).card with hN
  have hcard : s.card = N 0 + N 1 + N 2 + N 3 + N 4 := by
    have := Finset.card_eq_sum_card_fiberwise (f := L) (s := s) (t := Finset.range 5)
      (fun x _ => by have := L_le x; simp; omega)
    rw [this]
    simp [Finset.sum_range_succ, hN]
  have ex1 : ∀ i, 1 ≤ N i → ∃ x ∈ s, L x = i := by
    intro i hi
    obtain ⟨x, hx⟩ := Finset.card_pos.1 hi
    exact ⟨x, (Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩
  have ex2 : ∀ i, 2 ≤ N i → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ L x = i ∧ L y = i := by
    intro i hi
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hi
    exact ⟨x, (Finset.mem_filter.1 hx).1, y, (Finset.mem_filter.1 hy).1, hxy,
      (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2⟩
  have ex3 : ∀ i, 3 ≤ N i → ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ L x = i ∧ L y = i ∧ L z = i := by
    intro i hi
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 hi
    exact ⟨x, (Finset.mem_filter.1 hx).1, y, (Finset.mem_filter.1 hy).1, z,
      (Finset.mem_filter.1 hz).1, hxy, hxz, hyz,
      (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2, (Finset.mem_filter.1 hz).2⟩
  have b0 : N 0 ≤ 2 := by
    by_contra hcon
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, lx, ly, lz⟩ := ex3 0 (by omega)
    exact tri x y z hx hy hz (adj_zero hxy lx ly) (adj_zero hyz ly lz) (adj_zero hxz lx lz)
  have b4 : N 4 ≤ 2 := by
    by_contra hcon
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, lx, ly, lz⟩ := ex3 4 (by omega)
    exact tri x y z hx hy hz (adj_four hxy lx ly) (adj_four hyz ly lz) (adj_four hxz lx lz)
  have b1 : N 1 ≤ 2 := by
    by_contra hcon
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, lx, ly, lz⟩ := ex3 1 (by omega)
    have := val_ne hxy
    have := val_ne hxz
    have := val_ne hyz
    rw [L_eq1] at lx ly lz
    omega
  have b3 : N 3 ≤ 2 := by
    by_contra hcon
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, lx, ly, lz⟩ := ex3 3 (by omega)
    have := val_ne hxy
    have := val_ne hxz
    have := val_ne hyz
    rw [L_eq3] at lx ly lz
    omega
  have b2 : N 2 ≤ 1 := by
    by_contra hcon
    obtain ⟨x, hx, y, hy, hxy, lx, ly⟩ := ex2 2 (by omega)
    exact hxy ((eq_c lx).trans (eq_c ly).symm)
  have b2' : c ∉ s → N 2 = 0 := by
    intro hc
    by_contra hcon
    obtain ⟨x, hx, lx⟩ := ex1 2 (by omega)
    exact hc (eq_c lx ▸ hx)
  have t01 : 2 ≤ N 0 → 1 ≤ N 1 → False := by
    intro h0 h1
    obtain ⟨x, hx, y, hy, hxy, lx, ly⟩ := ex2 0 h0
    obtain ⟨a, ha, la⟩ := ex1 1 h1
    exact tri x y a hx hy ha (adj_zero hxy lx ly) (adj_up (by omega)) (adj_up (by omega))
  have t34 : 2 ≤ N 4 → 1 ≤ N 3 → False := by
    intro h0 h1
    obtain ⟨x, hx, y, hy, hxy, lx, ly⟩ := ex2 4 h0
    obtain ⟨a, ha, la⟩ := ex1 3 h1
    exact tri x y a hx hy ha (adj_four hxy lx ly) (adj_down (by omega)) (adj_down (by omega))
  have s01 : c ∈ s → 1 ≤ N 0 → 2 ≤ N 1 → False := by
    intro hc h0 h1
    obtain ⟨q, hq, lq⟩ := ex1 0 h0
    obtain ⟨a, ha, b, hb, hab, la, lb⟩ := ex2 1 h1
    have lc : L (c : V.{u}) = 2 := L_c
    exact sq q a c b hq ha hc hb (adj_up (by omega)) (adj_up (by omega)) (adj_up (by omega))
      (adj_up (by omega)) (ne_of_L (by omega)) hab
  have s34 : c ∈ s → 1 ≤ N 4 → 2 ≤ N 3 → False := by
    intro hc h0 h1
    obtain ⟨q, hq, lq⟩ := ex1 4 h0
    obtain ⟨a, ha, b, hb, hab, la, lb⟩ := ex2 3 h1
    have lc : L (c : V.{u}) = 2 := L_c
    exact sq q a c b hq ha hc hb (adj_down (by omega)) (adj_down (by omega)) (adj_down (by omega))
      (adj_down (by omega)) (ne_of_L (by omega)) hab
  have cut' : c ∉ s → 1 ≤ N 0 + N 1 → 1 ≤ N 3 + N 4 → False := by
    intro hc hl hr
    have hl' : ∃ x ∈ s, L x ≤ 1 := by
      by_cases h0 : 1 ≤ N 0
      · obtain ⟨x, hx, lx⟩ := ex1 0 h0
        exact ⟨x, hx, by omega⟩
      · obtain ⟨x, hx, lx⟩ := ex1 1 (by omega)
        exact ⟨x, hx, by omega⟩
    have hr' : ∃ y ∈ s, 3 ≤ L y := by
      by_cases h0 : 1 ≤ N 3
      · obtain ⟨x, hx, lx⟩ := ex1 3 h0
        exact ⟨x, hx, by omega⟩
      · obtain ⟨x, hx, lx⟩ := ex1 4 (by omega)
        exact ⟨x, hx, by omega⟩
    obtain ⟨x, hx, lx⟩ := hl'
    obtain ⟨y, hy, ly⟩ := hr'
    exact cut hc x hx y hy lx ly
  have t01' : N 0 ≤ 1 ∨ N 1 = 0 := by
    by_contra hh
    exact t01 (by omega) (by omega)
  have t34' : N 4 ≤ 1 ∨ N 3 = 0 := by
    by_contra hh
    exact t34 (by omega) (by omega)
  by_cases hc : c ∈ s
  · have s01' : N 0 = 0 ∨ N 1 ≤ 1 := by
      by_contra hh
      exact s01 hc (by omega) (by omega)
    have s34' : N 4 = 0 ∨ N 3 ≤ 1 := by
      by_contra hh
      exact s34 hc (by omega) (by omega)
    omega
  · have h2 := b2' hc
    have cut'' : N 0 + N 1 = 0 ∨ N 3 + N 4 = 0 := by
      by_contra hh
      exact cut' hc (by omega) (by omega)
    omega

lemma tree_le : (G : SimpleGraph V.{u}).largestInducedTreeSize ≤ 5 := by
  unfold largestInducedTreeSize
  rcases Set.eq_empty_or_nonempty
    {n | ∃ s : Finset V.{u}, s.card = n ∧ ((G : SimpleGraph V.{u}).induce (s : Set V.{u})).IsTree}
    with h | h
  · rw [h]
    simp
  · apply csSup_le h
    rintro n ⟨s, rfl, hs⟩
    exact tree_card_le s hs

end OMA72

theorem OMA.disproof : ¬ (type_of% @WrittenOnTheWallII.GraphConjecture72.conjecture72) := by
  intro h
  have h1 := h (α := OMA72.V) OMA72.G OMA72.connected
  simp only at h1
  have hL := OMA72.four_le_maxL (by simp)
  have hA := OMA72.avg_ge
  have hT := OMA72.tree_le
  have hT' : ((OMA72.G).largestInducedTreeSize : ℝ) ≤ 5 := by exact_mod_cast hT
  have hL' : (4 : ℝ) ≤ ((Finset.univ.image
      (fun v => indepNeighborsCard OMA72.G v)).max' (by simp) : ℕ) := by exact_mod_cast hL
  have hx : (5 : ℝ) < (OMA72.G).averageEccentricity +
      (((Finset.univ.image (fun v => indepNeighborsCard OMA72.G v)).max' (by simp) : ℕ) : ℝ) / 3 := by
    have : (5 : ℝ) < 70 / 19 + 4 / 3 := by norm_num
    linarith
  have hceil : (5 : ℤ) < ⌈(OMA72.G).averageEccentricity +
      (((Finset.univ.image (fun v => indepNeighborsCard OMA72.G v)).max' (by simp) : ℕ) : ℝ) / 3⌉ :=
    Int.lt_ceil.2 (by exact_mod_cast hx)
  have hceil' : (6 : ℝ) ≤ (⌈(OMA72.G).averageEccentricity +
      (((Finset.univ.image (fun v => indepNeighborsCard OMA72.G v)).max' (by simp) : ℕ) : ℝ) / 3⌉ : ℤ) := by
    exact_mod_cast hceil
  linarith
