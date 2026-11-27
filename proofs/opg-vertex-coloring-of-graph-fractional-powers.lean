import OMAStatements.S_opg_vertex_coloring_of_graph_fractional_powers
import Mathlib

namespace FracPowDisproof

open OMA.S_opg_vertex_coloring_of_graph_fractional_powers

private def prismAdj (u v : Fin 6) : Prop :=
  u ≠ v ∧ (u.val / 3 = v.val / 3 ∨ u.val % 3 = v.val % 3)

private instance (u v : Fin 6) : Decidable (prismAdj u v) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

private def prism : SimpleGraph (Fin 6) where
  Adj := prismAdj
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ Eq.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance (u v : Fin 6) : Decidable (prism.Adj u v) :=
  inferInstanceAs (Decidable (prismAdj u v))

private theorem prism_connected : prism.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := prism)).2
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact ⟨.nil⟩
  · exact ⟨.cons (by decide) .nil⟩
  · exact ⟨.cons (by decide) .nil⟩
  · exact ⟨.cons (by decide) .nil⟩
  · exact ⟨.cons (v := 1) (by decide) (.cons (by decide) .nil)⟩
  · exact ⟨.cons (v := 2) (by decide) (.cons (by decide) .nil)⟩

private theorem prism_degree : 3 ≤ prism.maxDegree := by
  calc
    3 = prism.degree 0 := by decide
    _ ≤ prism.maxDegree := prism.degree_le_maxDegree 0

-- An internal vertex records its edge and its offset from the smaller endpoint.
private abbrev W := Fin 6 ⊕ (Fin 9 × Fin 4)
private abbrev Q := SubdivVert prism 5
private abbrev S := subdivision prism 5
private abbrev H := fractionalPower prism 3 5

private def leftEnd (i : Fin 9) : Fin 6 := ![0, 0, 1, 3, 3, 4, 0, 1, 2] i
private def rightEnd (i : Fin 9) : Fin 6 := ![1, 2, 2, 4, 5, 5, 3, 4, 5] i

private theorem end_adj : ∀ i, prism.Adj (leftEnd i) (rightEnd i) := by decide

private def edgeIndex (u v : Fin 6) : Fin 9 :=
  match u.val, v.val with
  | 0, 1 => 0
  | 0, 2 => 1
  | 1, 2 => 2
  | 3, 4 => 3
  | 3, 5 => 4
  | 4, 5 => 5
  | 0, 3 => 6
  | 1, 4 => 7
  | 2, 5 => 8
  | _, _ => 0

private def inner (u v : Fin 6) (k : Fin 4) : W :=
  if u < v then .inr (edgeIndex u v, k) else .inr (edgeIndex v u, k.rev)

private theorem inner_flip :
    ∀ (u v : Fin 6) (k : Fin 4), u ≠ v → inner u v k = inner v u k.rev := by decide

private def branch (u : Fin 6) : Q := Quotient.mk _ (Sum.inl u)

private def along (u v : Fin 6) (k : Fin 4) (h : prism.Adj u v) : Q :=
  Quotient.mk _ (Sum.inr ⟨⟨u, v, k⟩, h⟩)

private def vertex : W → Q
  | .inl u => branch u
  | .inr (i, k) => along (leftEnd i) (rightEnd i) k (end_adj i)

private def encodePre : SubdivPre prism 5 → W
  | .inl u => .inl u
  | .inr ⟨⟨u, v, k⟩, _⟩ => inner u v k

private def encode : Q → W :=
  Quotient.lift encodePre (by
    intro x y h
    change subdivRel prism 5 x y at h
    cases x with
    | inl u =>
      cases y with
      | inl v => exact congrArg Sum.inl h
      | inr t => exact h.elim
    | inr t =>
      cases y with
      | inl v => exact h.elim
      | inr s =>
        rcases t with ⟨⟨u, v, k⟩, ht⟩
        rcases s with ⟨⟨a, b, l⟩, hs⟩
        rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · rfl
        · change inner u v l.rev = inner v u l
          simpa only [Fin.rev_rev] using inner_flip u v l.rev ht.ne)

private theorem inner_end :
    ∀ (i : Fin 9) (k : Fin 4), inner (leftEnd i) (rightEnd i) k = Sum.inr (i, k) := by
  decide

private theorem encode_vertex (x : W) : encode (vertex x) = x := by
  cases x with
  | inl u => rfl
  | inr p =>
    rcases p with ⟨i, k⟩
    exact inner_end i k

private theorem align :
    ∀ u v, prism.Adj u v → u < v →
      leftEnd (edgeIndex u v) = u ∧ rightEnd (edgeIndex u v) = v := by decide

private theorem along_flip (u v : Fin 6) (k : Fin 4) (h : prism.Adj u v) :
    along u v k h = along v u k.rev h.symm := by
  apply Quotient.sound
  exact Or.inr ⟨rfl, rfl, (Fin.rev_rev k).symm⟩

private theorem vertex_inner (u v : Fin 6) (k : Fin 4) (h : prism.Adj u v) :
    vertex (inner u v k) = along u v k h := by
  by_cases huv : u < v
  · obtain ⟨hl, hr⟩ := align u v h huv
    rw [inner, if_pos huv]
    simp only [vertex, along]
    apply Quotient.sound
    exact Or.inl ⟨hl, hr, rfl⟩
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) h.ne.symm
    obtain ⟨hl, hr⟩ := align v u h.symm hvu
    rw [inner, if_neg huv, along_flip u v k h]
    simp only [vertex, along]
    apply Quotient.sound
    exact Or.inl ⟨hl, hr, rfl⟩

private theorem vertex_encode (x : Q) : vertex (encode x) = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    cases x with
    | inl u => rfl
    | inr t =>
      rcases t with ⟨⟨u, v, k⟩, h⟩
      exact vertex_inner u v k h

private theorem vertex_injective : Function.Injective vertex := fun x y h =>
  (encode_vertex x).symm.trans ((congrArg encode h).trans (encode_vertex y))

private def neighbor (u : Fin 6) (i : Fin 3) : Fin 6 :=
  (![![1, 2, 3], ![0, 2, 4], ![0, 1, 5],
      ![4, 5, 0], ![3, 5, 1], ![3, 4, 2]] u) i

private theorem neighbor_adj : ∀ u i, prism.Adj u (neighbor u i) := by decide

private def next : W → List W
  | .inl u => List.ofFn (fun i => inner u (neighbor u i) 0)
  | .inr (e, k) =>
    ![[Sum.inl (leftEnd e), .inr (e, 1)],
      [.inr (e, 0), .inr (e, 2)],
      [.inr (e, 1), .inr (e, 3)],
      [.inr (e, 2), Sum.inl (rightEnd e)]] k

private instance (x : W) (xs : List W) : Decidable (x ∈ xs) :=
  decidable_of_iff (xs.any (fun y => decide (x = y)) = true) (by simp [List.any_eq_true])

private theorem next_symm : ∀ (x y : W), y ∈ next x → x ∈ next y := by decide

private theorem next_branch :
    ∀ u v, prism.Adj u v → inner u v 0 ∈ next (.inl u) := by decide

private theorem next_inner :
    ∀ u v (k : Fin 3), prism.Adj u v →
      inner u v k.succ ∈ next (inner u v k.castSucc) := by decide

private theorem step_next {x y : Q} (h : subdivStep prism 5 x y) :
    encode y ∈ next (encode x) := by
  rcases h with h | h | h
  · exact (by decide : (5 : ℕ) ≠ 1) h.1 |>.elim
  · obtain ⟨u, v, huv, _, rfl, rfl⟩ := h
    exact next_branch u v huv
  · obtain ⟨u, v, huv, k, hk, rfl, rfl⟩ := h
    exact next_inner u v ⟨k, by omega⟩ huv

private theorem adj_next {x y : Q} (h : S.Adj x y) : encode y ∈ next (encode x) :=
  h.2.elim step_next (fun h' => next_symm _ _ (step_next h'))

private theorem branch_step (u v : Fin 6) (h : prism.Adj u v) :
    S.Adj (branch u) (along u v 0 h) := by
  exact ⟨fun e => Quotient.exact e, Or.inl (Or.inr (Or.inl ⟨u, v, h, by decide, rfl, rfl⟩))⟩

private theorem along_step (u v : Fin 6) (h : prism.Adj u v) (k : Fin 3) :
    S.Adj (along u v k.castSucc h) (along u v k.succ h) := by
  constructor
  · intro eq
    have hr : subdivRel prism 5 (Sum.inr ⟨⟨u, v, k.castSucc⟩, h⟩)
        (Sum.inr ⟨⟨u, v, k.succ⟩, h⟩) := Quotient.exact eq
    rcases hr with ⟨_, _, hk⟩ | ⟨huv, _, _⟩
    · have hv := congrArg Fin.val hk
      simp at hv
    · exact h.ne huv
  · exact Or.inl (Or.inr (Or.inr ⟨u, v, h, k.val, by omega, rfl, rfl⟩))

private theorem end_step (i : Fin 9) : S.Adj (vertex (.inr (i, 3))) (branch (rightEnd i)) := by
  change S.Adj (along (leftEnd i) (rightEnd i) 3 (end_adj i)) (branch (rightEnd i))
  rw [along_flip]
  exact (branch_step (rightEnd i) (leftEnd i) (end_adj i).symm).symm

private theorem next_adj {x y : W} (hy : y ∈ next x) : S.Adj (vertex x) (vertex y) := by
  cases x with
  | inl u =>
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    rw [vertex_inner u (neighbor u i) 0 (neighbor_adj u i)]
    exact branch_step u (neighbor u i) (neighbor_adj u i)
  | inr p =>
    obtain ⟨e, k⟩ := p
    fin_cases k
    · change y ∈ [Sum.inl (leftEnd e), .inr (e, 1)] at hy
      rcases List.mem_pair.mp hy with rfl | rfl
      · exact (branch_step _ _ (end_adj e)).symm
      · exact along_step _ _ (end_adj e) 0
    · change y ∈ [Sum.inr (e, 0), .inr (e, 2)] at hy
      rcases List.mem_pair.mp hy with rfl | rfl
      · exact (along_step _ _ (end_adj e) 0).symm
      · exact along_step _ _ (end_adj e) 1
    · change y ∈ [Sum.inr (e, 1), .inr (e, 3)] at hy
      rcases List.mem_pair.mp hy with rfl | rfl
      · exact (along_step _ _ (end_adj e) 1).symm
      · exact along_step _ _ (end_adj e) 2
    · change y ∈ [Sum.inr (e, 2), .inl (rightEnd e)] at hy
      rcases List.mem_pair.mp hy with rfl | rfl
      · exact (along_step _ _ (end_adj e) 2).symm
      · exact end_step e

-- List the endpoints reachable by a walk of at most n steps.
private def within (x : W) : ℕ → List W
  | 0 => [x]
  | n + 1 => x :: (next x).flatMap (fun y => within y n)

private theorem walk_within {a b : Q} (p : S.Walk a b) {n : ℕ} (hp : p.length ≤ n) :
    encode b ∈ within (encode a) n := by
  induction n generalizing a b with
  | zero =>
    cases p with
    | nil => simp [within]
    | cons h p => simp at hp
  | succ n ih =>
    cases p with
    | nil => exact List.mem_cons_self
    | cons h p =>
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, adj_next h, ih p (by simpa using hp)⟩)

private theorem within_walk {x y : W} {n : ℕ} (hy : y ∈ within x n) :
    ∃ p : S.Walk (vertex x) (vertex y), p.length ≤ n := by
  induction n generalizing x with
  | zero =>
    have h : y = x := List.mem_singleton.mp hy
    subst y
    exact ⟨.nil, Nat.le_refl _⟩
  | succ n ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨.nil, Nat.zero_le _⟩
    · obtain ⟨z, hz, hzy⟩ := List.mem_flatMap.mp hy
      obtain ⟨p, hp⟩ := ih hzy
      exact ⟨.cons (next_adj hz) p, by simpa using hp⟩

private def adjacent (x y : W) : Bool :=
  decide (x ≠ y ∧ y ∈ within x 3)

private theorem adjacent_iff (x y : W) :
    adjacent x y = true ↔ H.Adj (vertex x) (vertex y) := by
  change adjacent x y = true ↔ vertex x ≠ vertex y ∧ S.edist (vertex x) (vertex y) ≤ 3
  rw [adjacent, decide_eq_true_eq]
  constructor
  · rintro ⟨hne, hy⟩
    obtain ⟨p, hp⟩ := within_walk hy
    exact ⟨fun hxy => hne (vertex_injective hxy), p.edist_le.trans (ENat.natCast_le_natCast.mpr hp)⟩
  · rintro ⟨hne, hd⟩
    have htop : S.edist (vertex x) (vertex y) ≠ ⊤ := by
      intro ht
      simp [ht] at hd
    obtain ⟨p, hp⟩ := (SimpleGraph.reachable_of_edist_ne_top htop).exists_walk_length_eq_edist
    refine ⟨hne ∘ congrArg vertex, ?_⟩
    have hlen : p.length ≤ 3 := ENat.natCast_le_natCast.mp (hp.trans_le hd)
    simpa only [encode_vertex] using walk_within p hlen

local instance : BEq W := ⟨fun x y => decide (x = y)⟩

local instance : LawfulBEq W where
  eq_of_beq := of_decide_eq_true
  rfl := by intro x; exact decide_eq_true rfl

private def radiusNeighbors (x : W) : List W :=
  (within x 3).eraseDups.filter (fun y => decide (x ≠ y))

private theorem mem_radiusNeighbors {x y : W} :
    y ∈ radiusNeighbors x ↔ adjacent x y = true := by
  simp [radiusNeighbors, adjacent, and_comm]

private def scan (test : W → List W → Bool) : List W → Bool
  | [] => false
  | x :: xs => test x xs || scan test xs

private def hasClique : ℕ → List W → Bool
  | 0, _ => true
  | n + 1, xs => scan (fun x tail => hasClique n (tail.filter (adjacent x))) xs

private theorem hasClique_sound {s : Finset W} {xs : List W}
    (hc : (s : Set W).Pairwise (fun x y => adjacent x y = true))
    (hs : ∀ x ∈ s, x ∈ xs) : hasClique s.card xs = true := by
  generalize he : s.card = n
  induction n generalizing s xs with
  | zero => rfl
  | succ n ih =>
    induction xs with
    | nil =>
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      exact (List.not_mem_nil (hs x hx)).elim
    | cons x xs ihxs =>
      rw [hasClique, scan, Bool.or_eq_true]
      by_cases hx : x ∈ s
      · left
        refine ih (s := s.erase x) (hc.mono (Finset.erase_subset x s)) ?_ ?_
        · intro y hy
          obtain ⟨hne, hys⟩ := Finset.mem_erase.mp hy
          exact List.mem_filter.mpr
            ⟨(List.mem_cons.mp (hs y hys)).resolve_left hne, hc hx hys hne.symm⟩
        · rw [Finset.card_erase_of_mem hx, he, Nat.add_sub_cancel]
      · right
        exact ihxs (fun y hy => (List.mem_cons.mp (hs y hy)).resolve_left (fun h => hx (h ▸ hy)))

private theorem no_neighbor_clique : ∀ x : W, hasClique 5 (radiusNeighbors x) = false := by
  decide

private def modelEquiv : Q ≃ W :=
  ⟨encode, vertex, vertex_encode, encode_vertex⟩

private theorem clique_free : H.CliqueFree 6 := by
  classical
  intro s hc
  let t := s.map modelEquiv.toEmbedding
  have ht : t.card = 6 := (Finset.card_map _).trans hc.card_eq
  have hadj : (t : Set W).Pairwise (fun x y => adjacent x y = true) := by
    intro x hx y hy hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    apply (adjacent_iff _ _).2
    change H.Adj (vertex (encode a)) (vertex (encode b))
    rw [vertex_encode, vertex_encode]
    exact hc.isClique ha hb (hne ∘ congrArg modelEquiv.toEmbedding)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  have hmem (y : W) (hy : y ∈ t.erase x) : y ∈ radiusNeighbors x := by
    obtain ⟨hne, hy'⟩ := Finset.mem_erase.mp hy
    exact mem_radiusNeighbors.mpr (hadj hx hy' hne.symm)
  have hcheck := hasClique_sound (hadj.mono (Finset.erase_subset x t)) hmem
  rw [Finset.card_erase_of_mem hx, ht, no_neighbor_clique x] at hcheck
  exact Bool.noConfusion hcheck

private theorem clique_bound : H.cliqueNum ≤ 5 := by
  by_contra! h
  obtain ⟨s, hs⟩ := H.exists_isNClique_cliqueNum
  exact (clique_free.mono (by omega : 6 ≤ H.cliqueNum)) s hs

private def ball (u : Fin 6) (i : Fin 4) : W :=
  ![Sum.inl u, inner u (neighbor u 0) 0, inner u (neighbor u 1) 0, inner u (neighbor u 2) 0] i

private def crust (u : Fin 6) (i : Fin 3) : W :=
  inner u (neighbor u i) 1

private def cell (u : Fin 6) (i : Fin 5) : W :=
  if hi : i.val < 4 then ball u ⟨i.val, hi⟩ else crust u 0

private theorem cell_adj :
    ∀ u (i j : Fin 5), i ≠ j → adjacent (cell u i) (cell u j) = true := by decide

private theorem ball_crust_adj :
    ∀ u (i : Fin 4) (j : Fin 3), adjacent (ball u i) (crust u j) = true := by decide

private theorem crust_edges :
    ∀ u v, prism.Adj u v → ∃ i j : Fin 3, adjacent (crust u i) (crust v j) = true := by
  decide

private def initial (u v : Fin 6) : List W :=
  List.ofFn (crust u) ++ List.ofFn (crust v)

-- A vertex cannot receive the shared color of known vertices if it is adjacent to one.
private def survivors (u : Fin 6) (known : List W) : List W :=
  (List.ofFn (ball u)).filter (fun x => !(known.any (adjacent x)))

private def mate (u : Fin 6) : Fin 6 :=
  ⟨(u.val + 3) % 6, Nat.mod_lt _ (by decide)⟩

private def third (u v : Fin 6) : Fin 6 :=
  ⟨(3 * (u.val / 3) + (3 - u.val % 3 - v.val % 3)) % 6, Nat.mod_lt _ (by decide)⟩

-- Label the two triangles (u,b,c) and (d,e,v) with matching edges ud, be, cv.
private theorem forcing_layout :
    ∀ u v, u ≠ v → ¬ prism.Adj u v →
      let b := third u v
      let c := mate v
      let d := mate u
      let e := mate b
      let known := initial u v
      (prism.Adj b u ∧ prism.Adj c u ∧ prism.Adj d u ∧ prism.Adj e v) ∧
        survivors c known = [inner c b 0] ∧
        survivors d known = [inner d e 0] ∧
        survivors e (inner d e 0 :: known) = [inner e b 0] ∧
        survivors b (inner c b 0 :: inner e b 0 :: known) = [] := by
  decide

-- The crust-color argument follows Proposition 5.2 of arXiv:1212.3898.
private theorem no_coloring : ¬ H.Colorable 5 := by
  rintro ⟨color⟩
  let f : W → Fin 5 := fun x => color (vertex x)
  let c : Fin 6 → Fin 5 := fun u => f (crust u 0)
  have proper {x y : W} (h : adjacent x y = true) : f x ≠ f y :=
    color.valid ((adjacent_iff x y).mp h)
  have cell_surjective (u : Fin 6) : Function.Surjective (fun i => f (cell u i)) :=
    Finite.surjective_of_injective (fun i j eq => by
      by_contra h
      exact proper (cell_adj u i j h) eq)
  have on_ball (u : Fin 6) (a : Fin 5) (ha : a ≠ c u) :
      ∃ i : Fin 4, f (ball u i) = a := by
    obtain ⟨i, hi⟩ := cell_surjective u a
    by_cases h : i.val < 4
    · exact ⟨⟨i.val, h⟩, by simpa only [cell, dif_pos h] using hi⟩
    · have he : i = 4 := Fin.ext (by change i.val = 4; have := i.isLt; omega)
      subst i
      exact (ha hi.symm).elim
  have crust_color (u : Fin 6) (j : Fin 3) : f (crust u j) = c u := by
    by_contra h
    obtain ⟨i, hi⟩ := on_ball u _ h
    exact proper (ball_crust_adj u i j) hi
  have prism_color {u v : Fin 6} (h : prism.Adj u v) : c u ≠ c v := by
    obtain ⟨i, j, hij⟩ := crust_edges u v h
    simpa only [crust_color] using proper hij
  obtain ⟨u, v, huv, hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt c (by decide)
  have hnon : ¬ prism.Adj u v := fun h => prism_color h hcol
  obtain ⟨⟨hb, hc, hd, he⟩, hc1, hd1, he1, hb0⟩ := forcing_layout u v huv hnon
  have known_colors (x : W) (hx : x ∈ initial u v) : f x = c u := by
    simp only [initial, List.mem_append, List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact crust_color u i
    · exact (crust_color v i).trans hcol.symm
  have extend {x : W} {known : List W} (hx : f x = c u)
      (hk : ∀ y ∈ known, f y = c u) : ∀ y ∈ x :: known, f y = c u := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hk y hy
  have pick {w : Fin 6} {known : List W} (hw : c u ≠ c w)
      (hk : ∀ y ∈ known, f y = c u) : ∃ x ∈ survivors w known, f x = c u := by
    obtain ⟨i, hi⟩ := on_ball w (c u) hw
    refine ⟨ball w i, List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩, hi⟩
    cases h : known.any (adjacent (ball w i)) with
    | false => rfl
    | true =>
      obtain ⟨y, hy, hadj⟩ := List.any_eq_true.mp h
      exact (proper hadj (hi.trans (hk y hy).symm)).elim
  have forced {w : Fin 6} {known : List W} {x : W} (hw : c u ≠ c w)
      (hk : ∀ y ∈ known, f y = c u) (hs : survivors w known = [x]) : f x = c u := by
    obtain ⟨y, hy, hcolor⟩ := pick hw hk
    rw [hs, List.mem_singleton] at hy
    exact hy ▸ hcolor
  have c_forced := forced (prism_color hc).symm known_colors hc1
  have d_forced := forced (prism_color hd).symm known_colors hd1
  have e_forced := forced (hcol.trans_ne (prism_color he).symm)
    (extend d_forced known_colors) he1
  obtain ⟨x, hx, _⟩ :=
    pick (prism_color hb).symm (extend c_forced (extend e_forced known_colors))
  simp only [hb0, List.not_mem_nil] at hx

end FracPowDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_vertex_coloring_of_graph_fractional_powers.main) := by
  open FracPowDisproof in
  intro claim
  apply no_coloring
  apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
  rw [claim (Fin 6) prism prism_connected prism_degree 3 5 (by decide) (by decide)]
  exact ENat.natCast_le_natCast.mpr clique_bound