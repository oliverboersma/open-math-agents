import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H1: hypothesis H1 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @jagong-cmu

/-!
# Step H1 of the reduction R1 for WOWII Conjecture 372 (regularized)

A tree with path cover number at most two is two vertex-disjoint paths
`f 0, ..., f (m-1)` and `g 0, ..., g (l-1)` plus one bridge edge `f i - g j`
(a single path is split as `m = 1`). An edge count (a tree has `n - 1` edges) shows
that there are no other edges. Pull a minimum total dominating set back to index sets
`SA`, `SB`. Then `core` gives index covers `CA`, `CB` with `|CA| + |CB| <= |SA| + |SB|`,
built from parity classes. The counting is: `S` totally dominates `X` on a path, so
`|X| <= 2 |S|`, applied to the whole path, to the path less the bridge vertex, and to
the two segments on each side of the bridge vertex.
-/

namespace OMA.WOW372H1

open Finset

lemma cnt_le (X S : Finset ℕ) (h : ∀ x ∈ X, x + 1 ∈ S ∨ (1 ≤ x ∧ x - 1 ∈ S)) :
    X.card ≤ 2 * S.card := by
  have hsub : X ⊆ S.image (fun s => s - 1) ∪ S.image (fun s => s + 1) := by
    intro x hx
    rcases h x hx with h1 | ⟨h0, h1⟩
    · exact mem_union_left _ (mem_image.mpr ⟨x + 1, h1, by omega⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨x - 1, h1, by omega⟩)
  calc X.card ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ S.card + S.card := add_le_add card_image_le card_image_le
    _ = 2 * S.card := by ring

/-- The vertices of a path `0, ..., m - 1` with a given parity. -/
def par (m r : ℕ) : Finset ℕ := (range m).filter (fun a => a % 2 = r)

lemma card_par (m : ℕ) : (par m 1).card ≤ m / 2 ∧ (par m 0).card ≤ (m + 1) / 2 := by
  induction m with
  | zero => simp [par]
  | succ k ih =>
    simp only [par, range_add_one, filter_insert] at ih ⊢
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [if_neg (by omega), if_pos h]
      exact ⟨by omega, (card_insert_le _ _).trans (by omega)⟩
    · rw [if_pos h, if_neg (by omega)]
      exact ⟨(card_insert_le _ _).trans (by omega), by omega⟩

lemma par_cover (m r a : ℕ) (hr : r < 2) (h : a + 1 < m) : a ∈ par m r ∨ a + 1 ∈ par m r := by
  simp only [par, mem_filter, mem_range]
  omega

/-- Lower bounds for a total dominating set of a path, where one vertex `i`
may be dominated from outside. -/
lemma side (m i : ℕ) (hi : i < m) (S : Finset ℕ)
    (dom : ∀ a < m, a + 1 ∈ S ∨ (1 ≤ a ∧ a - 1 ∈ S) ∨ a = i) :
    m ≤ 2 * S.card + 1 ∧
    ((i + 1 ∈ S ∨ (1 ≤ i ∧ i - 1 ∈ S)) → m ≤ 2 * S.card) ∧
    (i ∈ S → ∃ x y : ℕ, i - 1 ≤ 2 * x ∧ m - (i + 2) ≤ 2 * y ∧ x + y + 1 ≤ S.card) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := cnt_le ((range m).erase i) S (by
      intro x hx
      rw [mem_erase, mem_range] at hx
      rcases dom x hx.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hx.1)
    rw [card_erase_of_mem (mem_range.mpr hi), card_range] at h1
    omega
  · intro hd
    have h1 := cnt_le (range m) S (by
      intro x hx
      rw [mem_range] at hx
      rcases dom x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · subst h; exact hd)
    rwa [card_range] at h1
  · intro hiS
    refine ⟨(S.filter (· < i)).card, (S.filter (i < ·)).card, ?_, ?_, ?_⟩
    · have h1 := cnt_le (range (i - 1)) (S.filter (· < i)) (by
        intro x hx
        rw [mem_range] at hx
        rcases dom x (by omega) with h | h | h
        · exact Or.inl (mem_filter.mpr ⟨h, by omega⟩)
        · exact Or.inr ⟨h.1, mem_filter.mpr ⟨h.2, by omega⟩⟩
        · omega)
      rwa [card_range] at h1
    · have h1 := cnt_le (Ico (i + 2) m) (S.filter (i < ·)) (by
        intro x hx
        rw [mem_Ico] at hx
        rcases dom x (by omega) with h | h | h
        · exact Or.inl (mem_filter.mpr ⟨h, by omega⟩)
        · exact Or.inr ⟨h.1, mem_filter.mpr ⟨h.2, by omega⟩⟩
        · omega)
      rwa [Nat.card_Ico] at h1
    · have hR : (insert i (S.filter (i < ·))).card = (S.filter (i < ·)).card + 1 :=
        card_insert_of_notMem (by simp)
      have hsub : insert i (S.filter (i < ·)) ⊆ S.filter (fun x => ¬ x < i) := by
        intro x hx
        rw [mem_insert, mem_filter] at hx
        rw [mem_filter]
        rcases hx with rfl | hx
        · exact ⟨hiS, by omega⟩
        · exact ⟨hx.1, by omega⟩
      have h2 := card_le_card hsub
      have h3 := card_filter_add_card_filter_not (s := S) (fun x => x < i)
      omega

/-- The arithmetic core: two paths `0..m-1` and `0..l-1` joined by the edge `i - j`. -/
lemma core (m l i j : ℕ) (hi : i < m) (hj : j < l) (SA SB : Finset ℕ)
    (domA : ∀ a < m, a + 1 ∈ SA ∨ (1 ≤ a ∧ a - 1 ∈ SA) ∨ (a = i ∧ j ∈ SB))
    (domB : ∀ b < l, b + 1 ∈ SB ∨ (1 ≤ b ∧ b - 1 ∈ SB) ∨ (b = j ∧ i ∈ SA)) :
    ∃ CA CB : Finset ℕ, CA.card + CB.card ≤ SA.card + SB.card ∧
      (∀ a, a + 1 < m → a ∈ CA ∨ a + 1 ∈ CA) ∧
      (∀ b, b + 1 < l → b ∈ CB ∨ b + 1 ∈ CB) ∧ (i ∈ CA ∨ j ∈ CB) := by
  obtain ⟨A1, A2, A3⟩ := side m i hi SA (fun a ha => by
    rcases domA a ha with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.1))
  obtain ⟨B1, B2, B3⟩ := side l j hj SB (fun a ha => by
    rcases domB a ha with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.1))
  have pA := card_par m
  have pB := card_par l
  -- option 1: the class of `i` on the first path, the odd class on the second path
  have opt1 : (m + 1 - i % 2) / 2 + l / 2 ≤ SA.card + SB.card →
      ∃ CA CB : Finset ℕ, CA.card + CB.card ≤ SA.card + SB.card ∧
      (∀ a, a + 1 < m → a ∈ CA ∨ a + 1 ∈ CA) ∧
      (∀ b, b + 1 < l → b ∈ CB ∨ b + 1 ∈ CB) ∧ (i ∈ CA ∨ j ∈ CB) := by
    intro hle
    refine ⟨par m (i % 2), par l 1, ?_, fun a ha => par_cover m _ a (by omega) ha,
      fun b hb => par_cover l 1 b (by omega) hb, Or.inl ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> rw [h] at hle <;> omega
    · simp only [par, mem_filter, mem_range]; exact ⟨hi, trivial⟩
  have opt2 : m / 2 + (l + 1 - j % 2) / 2 ≤ SA.card + SB.card →
      ∃ CA CB : Finset ℕ, CA.card + CB.card ≤ SA.card + SB.card ∧
      (∀ a, a + 1 < m → a ∈ CA ∨ a + 1 ∈ CA) ∧
      (∀ b, b + 1 < l → b ∈ CB ∨ b + 1 ∈ CB) ∧ (i ∈ CA ∨ j ∈ CB) := by
    intro hle
    refine ⟨par m 1, par l (j % 2), ?_, fun a ha => par_cover m 1 a (by omega) ha,
      fun b hb => par_cover l _ b (by omega) hb, Or.inr ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one j with h | h <;> rw [h] <;> rw [h] at hle <;> omega
    · simp only [par, mem_filter, mem_range]; exact ⟨hj, trivial⟩
  by_cases dA : i + 1 ∈ SA ∨ (1 ≤ i ∧ i - 1 ∈ SA)
  · exact opt1 (by have := A2 dA; omega)
  by_cases dB : j + 1 ∈ SB ∨ (1 ≤ j ∧ j - 1 ∈ SB)
  · exact opt2 (by have := B2 dB; omega)
  have hiS : i ∈ SA := by
    rcases domB j hj with h | h | h
    · exact absurd (Or.inl h) dB
    · exact absurd (Or.inr h) dB
    · exact h.2
  have hjS : j ∈ SB := by
    rcases domA i hi with h | h | h
    · exact absurd (Or.inl h) dA
    · exact absurd (Or.inr h) dA
    · exact h.2
  obtain ⟨x1, y1, hx1, hy1, hxy1⟩ := A3 hiS
  obtain ⟨x2, y2, hx2, hy2, hxy2⟩ := B3 hjS
  by_cases h1 : m % 2 = 0 ∨ i % 2 = 1
  · exact opt1 (by omega)
  by_cases h2 : l % 2 = 0 ∨ j % 2 = 1
  · exact opt2 (by omega)
  exact opt1 (by omega)

open SimpleGraph

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Two paths `f 0, ..., f (m-1)` and `g 0, ..., g (l-1)` that partition the vertices,
and every edge is a path edge or the bridge `f i - g j`. -/
def Str (T : SimpleGraph α) (m l i j : ℕ) (f g : ℕ → α) : Prop :=
  i < m ∧ j < l ∧ Set.InjOn f (Set.Iio m) ∧ Set.InjOn g (Set.Iio l) ∧
  (∀ a < m, ∀ b < l, f a ≠ g b) ∧
  (∀ v, (∃ a < m, f a = v) ∨ (∃ b < l, g b = v)) ∧
  (∀ u v, T.Adj u v → (∃ a, a + 1 < m ∧ s(u, v) = s(f a, f (a + 1))) ∨
     (∃ b, b + 1 < l ∧ s(u, v) = s(g b, g (b + 1))) ∨ s(u, v) = s(f i, g j))

lemma sym2_cover {C : Finset α} {u v x y : α} (h : s(u, v) = s(x, y)) (hc : x ∈ C ∨ y ∈ C) :
    u ∈ C ∨ v ∈ C := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

lemma dom_side {T : SimpleGraph α} {m l i j : ℕ} {f g : ℕ → α}
    (hfi : Set.InjOn f (Set.Iio m)) (hfg : ∀ a < m, ∀ b < l, f a ≠ g b)
    (hE : ∀ u v, T.Adj u v → (∃ a, a + 1 < m ∧ s(u, v) = s(f a, f (a + 1))) ∨
      (∃ b, b + 1 < l ∧ s(u, v) = s(g b, g (b + 1))) ∨ s(u, v) = s(f i, g j))
    (hi : i < m) (hj : j < l) (D : Finset α) (hD : ∀ v, ∃ w ∈ D, T.Adj v w) :
    ∀ a < m, a + 1 ∈ (range m).filter (fun a => f a ∈ D) ∨
      (1 ≤ a ∧ a - 1 ∈ (range m).filter (fun a => f a ∈ D)) ∨
      (a = i ∧ j ∈ (range l).filter (fun b => g b ∈ D)) := by
  intro a ha
  obtain ⟨w, hwD, hadj⟩ := hD (f a)
  rcases hE _ _ hadj with ⟨a', ha', he⟩ | ⟨b', hb', he⟩ | he
  · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : a = a' := hfi (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr (by omega)) h1
      subst this
      left
      simp only [mem_filter, mem_range]
      exact ⟨ha', h2 ▸ hwD⟩
    · have : a = a' + 1 := hfi (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr ha') h1
      subst this
      right; left
      simp only [mem_filter, mem_range, Nat.add_sub_cancel]
      exact ⟨by omega, by omega, h2 ▸ hwD⟩
  · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd h1 (hfg a ha b' (by omega))
    · exact absurd h1 (hfg a ha (b' + 1) hb')
  · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, _⟩
    · have : a = i := hfi (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr hi) h1
      right; right
      simp only [mem_filter, mem_range]
      exact ⟨this, hj, h2 ▸ hwD⟩
    · exact absurd h1 (hfg a ha j hj)

lemma tds_exists (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, (∀ v, ∃ w ∈ D, T.Adj v w) ∧ D.card = T.totalDominationNumber := by
  classical
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hne : ∃ n, ∃ D : Finset α, T.IsTotalNDominatingSet n D := by
    refine ⟨Finset.univ.card, Finset.univ, ⟨?_, rfl⟩⟩
    intro v
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p, hp, _⟩ := (hT.connected v w).exists_path_of_dist
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, by simp, h⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  exact ⟨D, hD.1, hD.2⟩

lemma main_of_str (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    {m l i j : ℕ} {f g : ℕ → α} (h : Str T m l i j f g) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  obtain ⟨hi, hj, hfi, hgi, hfg, hcov, hE⟩ := h
  obtain ⟨D, hD, hDc⟩ := tds_exists T hT hn
  have hgf : ∀ b < l, ∀ a < m, g b ≠ f a := fun b hb a ha e => hfg a ha b hb e.symm
  have hE' : ∀ u v, T.Adj u v → (∃ b, b + 1 < l ∧ s(u, v) = s(g b, g (b + 1))) ∨
      (∃ a, a + 1 < m ∧ s(u, v) = s(f a, f (a + 1))) ∨ s(u, v) = s(g j, f i) := by
    intro u v huv
    rcases hE u v huv with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (h.trans Sym2.eq_swap))
  set SA := (range m).filter (fun a => f a ∈ D) with hSA
  set SB := (range l).filter (fun b => g b ∈ D) with hSB
  have domA := dom_side hfi hfg hE hi hj D hD
  have domB := dom_side hgi hgf hE' hj hi D hD
  obtain ⟨CA, CB, hcard, hcA, hcB, hbr⟩ := core m l i j hi hj SA SB domA domB
  let C : Finset α := CA.image f ∪ CB.image g
  have hcover : T.IsVertexCover (C : Set α) := by
    intro u v huv
    simp only [Finset.mem_coe]
    rcases hE u v huv with ⟨a, ha, he⟩ | ⟨b, hb, he⟩ | he
    · refine sym2_cover he ?_
      rcases hcA a ha with h | h
      · exact Or.inl (mem_union_left _ (mem_image_of_mem f h))
      · exact Or.inr (mem_union_left _ (mem_image_of_mem f h))
    · refine sym2_cover he ?_
      rcases hcB b hb with h | h
      · exact Or.inl (mem_union_right _ (mem_image_of_mem g h))
      · exact Or.inr (mem_union_right _ (mem_image_of_mem g h))
    · refine sym2_cover he ?_
      rcases hbr with h | h
      · exact Or.inl (mem_union_left _ (mem_image_of_mem f h))
      · exact Or.inr (mem_union_right _ (mem_image_of_mem g h))
  have hC : C.card ≤ CA.card + CB.card :=
    (card_union_le _ _).trans (add_le_add card_image_le card_image_le)
  have hS : SA.card + SB.card ≤ D.card := by
    have h1 : (SA.image f).card = SA.card := card_image_of_injOn (fun a ha b hb e =>
      hfi (Set.mem_Iio.mpr (mem_range.mp (mem_filter.mp ha).1))
        (Set.mem_Iio.mpr (mem_range.mp (mem_filter.mp hb).1)) e)
    have h2 : (SB.image g).card = SB.card := card_image_of_injOn (fun a ha b hb e =>
      hgi (Set.mem_Iio.mpr (mem_range.mp (mem_filter.mp ha).1))
        (Set.mem_Iio.mpr (mem_range.mp (mem_filter.mp hb).1)) e)
    have hdis : Disjoint (SA.image f) (SB.image g) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      obtain ⟨b, hb, hb'⟩ := mem_image.mp hx'
      exact hfg a (mem_range.mp (mem_filter.mp ha).1) b (mem_range.mp (mem_filter.mp hb).1) hb'.symm
    have hsub : SA.image f ∪ SB.image g ⊆ D := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp ha).2
      · obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp ha).2
    have := card_le_card hsub
    rw [card_union_of_disjoint hdis, h1, h2] at this
    exact this
  have hle : T.vertexCoverNum ≤ (C.card : ℕ∞) := by
    have := hcover.vertexCoverNum_le
    rwa [Set.encard_coe_eq_coe_finsetCard] at this
  have h3 : T.vertexCoverNum.toNat ≤ C.card := ENat.toNat_le_of_le_natCast hle
  omega

lemma path_seq (T : SimpleGraph α) (s : Finset α) {x y : α} (p : T.Walk x y) (hp : p.IsPath)
    (hs : s = p.support.toFinset) :
    ∃ (m : ℕ) (f : ℕ → α), 1 ≤ m ∧ s.card = m ∧ Set.InjOn f (Set.Iio m) ∧
      (∀ v, v ∈ s ↔ ∃ a < m, f a = v) ∧ (∀ a, a + 1 < m → T.Adj (f a) (f (a + 1))) := by
  refine ⟨p.length + 1, p.getVert, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hs, List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  · intro a ha b hb e
    simp only [Set.mem_Iio] at ha hb
    exact hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) e
  · intro v
    rw [hs, List.mem_toFinset, Walk.mem_support_iff_exists_getVert]
    constructor
    · rintro ⟨n, h1, h2⟩; exact ⟨n, by omega, h1⟩
    · rintro ⟨n, h1, h2⟩; exact ⟨n, h2, by omega⟩
  · intro a ha
    exact p.adj_getVert_succ (by omega)

lemma pe_card {f : ℕ → α} {m : ℕ} (hf : Set.InjOn f (Set.Iio m)) :
    ((range (m - 1)).image (fun a => s(f a, f (a + 1)))).card = m - 1 := by
  rw [card_image_of_injOn, card_range]
  intro a ha b hb e
  simp only [coe_range, Set.mem_Iio] at ha hb
  dsimp only at e
  rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hf (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) h1
  · have := hf (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) h1
    have := hf (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) h2
    omega

lemma pe_sub (T : SimpleGraph α) [DecidableRel T.Adj] {f : ℕ → α} {m : ℕ}
    (hadj : ∀ a, a + 1 < m → T.Adj (f a) (f (a + 1))) :
    (range (m - 1)).image (fun a => s(f a, f (a + 1))) ⊆ T.edgeFinset := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := mem_image.mp he
  rw [mem_edgeFinset]
  exact hadj a (by rw [mem_range] at ha; omega)

lemma all_edges (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (E : Finset (Sym2 α))
    (hE : E ⊆ T.edgeFinset) (hc : Fintype.card α ≤ E.card + 1) :
    ∀ u v, T.Adj u v → s(u, v) ∈ E := by
  have h1 := hT.card_edgeFinset
  have heq : E = T.edgeFinset := eq_of_subset_of_card_le hE (by omega)
  intro u v huv
  rw [heq, mem_edgeFinset]
  exact huv

lemma str_exists (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    (hp : T.pathCoverNumber ≤ 2) : ∃ m l i j : ℕ, ∃ f g : ℕ → α, Str T m l i j f g := by
  letI : DecidableRel T.Adj := Classical.decRel _
  have hne : ∃ k, ∃ P : Finset (Finset α), P.card = k ∧ T.IsPathCover P := by
    refine ⟨_, univ.image (fun v => ({v} : Finset α)), rfl, ?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      obtain ⟨a, -, rfl⟩ := mem_image.mp hs1
      obtain ⟨b, -, rfl⟩ := mem_image.mp hs2
      rw [Finset.disjoint_singleton]
      rintro rfl
      exact hne rfl
    · intro v _
      exact mem_biUnion.mpr ⟨{v}, mem_image_of_mem _ (mem_univ v), mem_singleton_self v⟩
    · intro s hs
      obtain ⟨a, -, rfl⟩ := mem_image.mp hs
      exact ⟨a, a, Walk.nil, Walk.IsPath.nil, by simp⟩
  obtain ⟨P, hPc, hP⟩ := Nat.sInf_mem hne
  obtain ⟨hdisj, hcovP, hpath⟩ := hP
  have hP2 : P.card ≤ 2 := by rw [hPc]; exact hp
  have hP0 : P.card ≠ 0 := by
    intro h0
    rw [card_eq_zero] at h0
    subst h0
    have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v⟩ := this
    have := hcovP (mem_univ v)
    simp at this
  rcases (by omega : P.card = 1 ∨ P.card = 2) with h | h
  · obtain ⟨s, rfl⟩ := card_eq_one.mp h
    have hsu : ∀ v, v ∈ s := fun v => by
      have := hcovP (mem_univ v)
      simpa using this
    obtain ⟨x, y, p, hpp, hs⟩ := hpath s (mem_singleton_self s)
    obtain ⟨m, f, hm1, hsm, hfi, hfmem, hfadj⟩ := path_seq T s p hpp hs
    have hmn : m = Fintype.card α := by
      rw [← hsm, ← card_univ]
      congr 1
      exact eq_univ_of_forall hsu
    have hE := all_edges T hT _ (pe_sub T hfadj) (by rw [pe_card hfi]; omega)
    refine ⟨1, m - 1, 0, 0, f, fun k => f (k + 1), by omega, by omega,
      hfi.mono (Set.Iio_subset_Iio (by omega)), ?_, ?_, ?_, ?_⟩
    · intro a ha b hb e
      simp only [Set.mem_Iio] at ha hb
      have := hfi (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) e
      omega
    · intro a ha b hb e
      have := hfi (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) e
      omega
    · intro v
      obtain ⟨a, ha, rfl⟩ := (hfmem v).mp (hsu v)
      rcases a with _ | k
      · exact Or.inl ⟨0, by omega, rfl⟩
      · exact Or.inr ⟨k, by omega, rfl⟩
    · intro u v huv
      obtain ⟨a, ha, he⟩ := mem_image.mp (hE u v huv)
      rw [mem_range] at ha
      rcases a with _ | k
      · exact Or.inr (Or.inr he.symm)
      · exact Or.inr (Or.inl ⟨k, by omega, he.symm⟩)
  · obtain ⟨s1, s2, hne12, rfl⟩ := card_eq_two.mp h
    have hd12 : Disjoint s1 s2 := hdisj s1 (by simp) s2 (by simp) hne12
    have hsu : ∀ v, v ∈ s1 ∨ v ∈ s2 := fun v => by
      have := hcovP (mem_univ v)
      simpa using this
    obtain ⟨x1, y1, p1, hp1, hs1⟩ := hpath s1 (by simp)
    obtain ⟨x2, y2, p2, hp2, hs2⟩ := hpath s2 (by simp)
    obtain ⟨m, f, hm1, hsm, hfi, hfmem, hfadj⟩ := path_seq T s1 p1 hp1 hs1
    obtain ⟨l, g, hl1, hsl, hgi, hgmem, hgadj⟩ := path_seq T s2 p2 hp2 hs2
    have hmn : m + l = Fintype.card α := by
      rw [← hsm, ← hsl, ← card_union_of_disjoint hd12, ← card_univ]
      congr 1
      exact eq_univ_of_forall (fun v => mem_union.mpr (hsu v))
    have hfg : ∀ a < m, ∀ b < l, f a ≠ g b := fun a ha b hb e =>
      Finset.disjoint_left.mp hd12 ((hfmem _).mpr ⟨a, ha, rfl⟩) ((hgmem _).mpr ⟨b, hb, e.symm⟩)
    have hf0 : f 0 ∈ (s1 : Set α) := (hfmem _).mpr ⟨0, by omega, rfl⟩
    have hg0 : g 0 ∉ (s1 : Set α) := fun h =>
      Finset.disjoint_left.mp hd12 h ((hgmem _).mpr ⟨0, by omega, rfl⟩)
    obtain ⟨d, -, hd1, hd2⟩ :=
      (hT.connected (f 0) (g 0)).some.exists_boundary_dart (s1 : Set α) hf0 hg0
    obtain ⟨i, hi, hfd⟩ := (hfmem _).mp (Finset.mem_coe.mp hd1)
    obtain ⟨j, hj, hgd⟩ := (hgmem _).mp ((hsu _).resolve_left hd2)
    have hbr : T.Adj (f i) (g j) := by rw [hfd, hgd]; exact d.adj
    have hdisjE : Disjoint ((range (m - 1)).image (fun a => s(f a, f (a + 1))))
        ((range (l - 1)).image (fun b => s(g b, g (b + 1)))) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨a, ha, rfl⟩ := mem_image.mp he
      obtain ⟨b, hb, hbe⟩ := mem_image.mp he'
      rw [mem_range] at ha hb
      rcases Sym2.eq_iff.mp hbe with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hfg a (by omega) b (by omega) h1.symm
      · exact hfg (a + 1) (by omega) b (by omega) h1.symm
    have hnot : s(f i, g j) ∉ ((range (m - 1)).image (fun a => s(f a, f (a + 1)))) ∪
        ((range (l - 1)).image (fun b => s(g b, g (b + 1)))) := by
      intro hmem
      rcases mem_union.mp hmem with h' | h'
      · obtain ⟨a, ha, he⟩ := mem_image.mp h'
        rw [mem_range] at ha
        rcases Sym2.eq_iff.mp he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hfg (a + 1) (by omega) j hj h2
        · exact hfg a (by omega) j hj h1
      · obtain ⟨b, hb, he⟩ := mem_image.mp h'
        rw [mem_range] at hb
        rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hfg i hi b (by omega) h1.symm
        · exact hfg i hi (b + 1) (by omega) h2.symm
    have hsubE : insert s(f i, g j) (((range (m - 1)).image (fun a => s(f a, f (a + 1)))) ∪
        ((range (l - 1)).image (fun b => s(g b, g (b + 1))))) ⊆ T.edgeFinset := by
      intro e he
      rcases mem_insert.mp he with rfl | he
      · rw [mem_edgeFinset]; exact hbr
      · rcases mem_union.mp he with he | he
        · exact pe_sub T hfadj he
        · exact pe_sub T hgadj he
    have hE := all_edges T hT _ hsubE (by
      rw [card_insert_of_notMem hnot, card_union_of_disjoint hdisjE, pe_card hfi, pe_card hgi]
      omega)
    refine ⟨m, l, i, j, f, g, hi, hj, hfi, hgi, hfg, ?_, ?_⟩
    · intro v
      rcases hsu v with h' | h'
      · exact Or.inl ((hfmem v).mp h')
      · exact Or.inr ((hgmem v).mp h')
    · intro u v huv
      rcases mem_insert.mp (hE u v huv) with he | he
      · exact Or.inr (Or.inr he)
      · rcases mem_union.mp he with he | he
        · obtain ⟨a, ha, he⟩ := mem_image.mp he
          rw [mem_range] at ha
          exact Or.inl ⟨a, by omega, he.symm⟩
        · obtain ⟨b, hb, he⟩ := mem_image.mp he
          rw [mem_range] at hb
          exact Or.inr (Or.inl ⟨b, by omega, he.symm⟩)

end OMA.WOW372H1

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H1 := by
  intro α _ _ T hT hn hp
  obtain ⟨m, l, i, j, f, g, h⟩ := OMA.WOW372H1.str_exists T hT hn hp
  exact OMA.WOW372H1.main_of_str T hT hn h
