import FormalConjectures.WrittenOnTheWallII.GraphConjecture96

/-!
An independent proof of the pointwise bound for Graffiti.pc Conjecture 96.
Rhett previously proved and formalized this theorem in October 2026.
-/

namespace OMA.W96

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem neighbor_bound (G : SimpleGraph α) (v : α) (s : Finset α)
    (hs : G.IsIndepSet (s : Set α)) (hn : ∀ x ∈ s, G.Adj v x) :
    s.card ≤ G.indepNeighborsCard v := by
  classical
  let f : s ↪ G.neighborSet v :=
    ⟨fun x => ⟨x.val, hn x.val x.property⟩, fun a b h => Subtype.ext (congrArg (fun z : G.neighborSet v => (z : α)) h)⟩
  have ht : (G.induce (G.neighborSet v)).IsIndepSet (s.attach.map f : Finset _) := by
    intro a ha b hb hne
    obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', _, rfl⟩ := Finset.mem_map.mp hb
    exact hs a'.property b'.property (fun e => hne (Subtype.ext e))
  simpa [indepNeighborsCard] using ht.card_le_indepNum

theorem pred_exists (G : SimpleGraph α) (hG : G.Connected) (r x : α) (hx : x ≠ r) :
    ∃ y, G.Adj x y ∧ G.dist r y + 1 = G.dist r x := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x r
  have hn : ¬ p.Nil := Walk.not_nil_of_ne hx
  have hsub : p.tail.IsSubwalk p := (show p.IsSubwalk p by simp).tail
  refine ⟨p.snd, p.adj_snd hn, ?_⟩
  rw [G.dist_comm (u := r) (v := p.snd), G.dist_comm (u := r) (v := x), ← length_eq_dist_of_subwalk hp hsub, ← hp]
  exact Walk.length_tail_add_one hn

variable [Nontrivial α]

theorem low_case (G : SimpleGraph α) (hG : G.Connected) (L : ℕ)
    (hL : ∀ v, G.indepNeighborsCard v ≤ L) (hlow : L < 2) :
    G.indepNum ≤ 1 ∧ 1 ≤ L := by
  classical
  have twoStep {a b c : α} (hab : G.Adj a b) (hbc : G.Adj b c) :
      a = c ∨ G.Adj a c := by
    by_cases hac : a = c
    · exact Or.inl hac
    right
    by_contra hnac
    have independent : G.IsIndepSet (({a, c} : Finset α) : Set α) := by
      intro u hu v hv huv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (huv rfl).elim
      · exact hnac
      · exact fun h => hnac h.symm
      · exact (huv rfl).elim
    have hb := neighbor_bound G b {a,c} independent (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hab.symm
      · exact hbc)
    have hcard : ({a,c} : Finset α).card = 2 := by simp [hac]
    rw [hcard] at hb
    have := hL b
    omega
  have walk_short {a b : α} (w : G.Walk a b) : a = b ∨ G.Adj a b := by
    induction w with
    | nil => exact Or.inl rfl
    | cons h w ih =>
      rcases ih with rfl | hadj
      · exact Or.inr h
      · exact twoStep h hadj
  have complete (a b : α) (hne : a ≠ b) : G.Adj a b := by
    obtain ⟨w⟩ := hG a b
    exact (walk_short w).resolve_left hne
  constructor
  · obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
    rw [← hs.card_eq]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    exact hs.isIndepSet ha hb hab (complete a b hab)
  · obtain ⟨a, b, hne⟩ := exists_pair_ne α
    have bound := neighbor_bound G a {b} (by
      simp [SimpleGraph.IsIndepSet]) (by
      intro x hx
      simpa only [Finset.mem_singleton.mp hx] using complete a b hne)
    simpa using bound.trans (hL a)

theorem count_from_root (G : SimpleGraph α) (hG : G.Connected)
    (s : Finset α) (hs : G.IsIndepSet (s : Set α)) (r : α)
    (L : ℕ) (hL : ∀ v, G.indepNeighborsCard v ≤ L) (hlarge : 2 ≤ L) :
    s.card ≤ 1 + G.distEven r * (L - 1) := by
  classical
  let pred (x : α) : α := if hx : x = r then r else (pred_exists G hG r x hx).choose
  have hp (x : α) (hx : x ≠ r) :
      G.Adj x (pred x) ∧ G.dist r (pred x) + 1 = G.dist r x := by
    simpa [pred, hx] using (pred_exists G hG r x hx).choose_spec
  let owner (x : α) := if Even (G.dist r x) then x else pred x
  let E := Finset.univ.filter fun x => Even (G.dist r x)
  have hr : r ∈ E := by simp [E]
  have cover : (s : Set α).MapsTo owner E := by
    intro x _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases he : Even (G.dist r x)
    · simpa [owner, he] using he
    · have hx : x ≠ r := by rintro rfl; simp at he
      have hd := (hp x hx).2
      simp only [owner, if_neg he]
      rw [Nat.even_iff] at he ⊢
      omega
  have bound (v : α) (_hv : v ∈ E) :
      (s.filter fun x => owner x = v).card ≤ (L - 1) + (if v = r then 1 else 0) := by
    let F := s.filter fun x => owner x = v
    change F.card ≤ _
    have hsub {x} (hx : x ∈ F) : x ∈ s := (Finset.mem_filter.mp hx).1
    have hchild {x} (hx : x ∈ F) (hne : x ≠ v) :
        G.Adj v x ∧ G.dist r v + 1 = G.dist r x := by
      have ho := (Finset.mem_filter.mp hx).2
      by_cases he : Even (G.dist r x)
      · simp [owner, he] at ho
        exact (hne ho).elim
      · have hxr : x ≠ r := by rintro rfl; simp at he
        have heq : pred x = v := by simpa [owner, he] using ho
        rw [← heq]
        exact ⟨(hp x hxr).1.symm, (hp x hxr).2⟩
    by_cases hvs : v ∈ s
    · have hsingle : F ⊆ {v} := by
        intro x hx
        apply Finset.mem_singleton.mpr
        by_contra hne
        exact hs (hsub hx) hvs hne (hchild hx hne).1.symm
      have hcard : F.card ≤ 1 := by simpa using Finset.card_le_card hsingle
      omega
    · have hne {x} (hx : x ∈ F) : x ≠ v := fun heq => hvs (heq ▸ hsub hx)
      have hFI : G.IsIndepSet (F : Set α) := fun _ hx _ hy hxy => hs (hsub hx) (hsub hy) hxy
      have hFN : ∀ x ∈ F, G.Adj v x := fun _ hx => (hchild hx (hne hx)).1
      by_cases hvr : v = r
      · have hcard := (neighbor_bound G v F hFI hFN).trans (hL v)
        simp [hvr]
        omega
      · obtain ⟨hadj, hd⟩ := hp v hvr
        have hnot : pred v ∉ F := by
          intro hm
          have hd' := (hchild hm (hne hm)).2
          omega
        have hsep {x} (hx : x ∈ F) : ¬ G.Adj (pred v) x := by
          intro ha
          have hd' := (hchild hx (hne hx)).2
          have htri : G.dist r x ≤ G.dist r (pred v) + G.dist (pred v) x := hG.dist_triangle
          rw [dist_eq_one_iff_adj.mpr ha] at htri
          omega
        have hI : G.IsIndepSet (↑(insert (pred v) F) : Set α) := by
          intro x hx y hy hxy
          change x ∈ insert (pred v) F at hx
          change y ∈ insert (pred v) F at hy
          rcases Finset.mem_insert.mp hx with rfl | hx
          · rcases Finset.mem_insert.mp hy with rfl | hy
            · exact fun _ => hxy rfl
            · exact hsep hy
          · rcases Finset.mem_insert.mp hy with rfl | hy
            · exact fun ha => hsep hx ha.symm
            · exact hFI hx hy hxy
        have hN : ∀ x ∈ insert (pred v) F, G.Adj v x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hadj
          · exact hFN _ hx
        have hcard := (neighbor_bound G v _ hI hN).trans (hL v)
        rw [Finset.card_insert_of_notMem hnot] at hcard
        simp [hvr]
        omega
  calc
    s.card = ∑ v ∈ E, (s.filter fun x => owner x = v).card := Finset.card_eq_sum_card_fiberwise cover
    _ ≤ ∑ v ∈ E, ((L - 1) + (if v = r then 1 else 0)) := Finset.sum_le_sum bound
    _ = 1 + G.distEven r * (L - 1) := by
      simp [Finset.sum_add_distrib, hr, Nat.add_comm, E, distEven]

end OMA.W96

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture96.conjecture96 := by
  classical
  intro α _ _ _ G hG
  let E := Finset.univ.image (SimpleGraph.distEven G)
  let N := Finset.univ.image (fun v => SimpleGraph.indepNeighborsCard G v)
  have hE : E.Nonempty := by simp [E]
  have hN : N.Nonempty := by simp [N]
  let L := N.max' hN
  have hL (v) : G.indepNeighborsCard v ≤ L :=
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  change (G.indepNum : ℝ) ≤ 1 + (E.min' hE : ℝ) * ((L : ℝ) - 1)
  by_cases hh : 2 ≤ L
  · obtain ⟨r, _, hr⟩ := Finset.mem_image.mp (E.min'_mem hE)
    obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
    have h := OMA.W96.count_from_root G hG s hs.isIndepSet r L hL hh
    rw [hs.card_eq, hr] at h
    have hh' : 1 ≤ L := by omega
    have hreal : (G.indepNum : ℝ) ≤ ((1 + E.min' hE * (L - 1) : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sub hh'] using hreal
  · obtain ⟨hi, hl⟩ := OMA.W96.low_case G hG L hL (by omega)
    have heq : L = 1 := by omega
    simp only [heq, Nat.cast_one, sub_self, mul_zero, add_zero]
    exact_mod_cast hi
