import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1

/-!
This reduction proves the real-valued bound l ≤ 3 at radius at most two
when there is no induced path on six vertices. It also formalizes Fan
Chung's induced path bound for radius at least three, following Erdős,
Saks and Sós, Maximum Induced Trees in Graphs, Theorem 2.2.

The geodesic, escape and gap-two machinery is adapted from @jagong-cmu's
merged reduction and gap-two proof. The antipodal contact observation
for an induced six-cycle also appears in Haoyu Chen's Partial Results
on the WOWII-133 Graffiti Conjecture.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R2

open SimpleGraph
open scoped BigOperators

variable {α : Type} [Fintype α] [DecidableEq α]
lemma le_path_of_fun (G : SimpleGraph α) (f : ℕ → α) (m : ℕ)
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    (hadj : ∀ i j, i < m → j < m → (G.Adj (f i) (f j) ↔ i + 1 = j ∨ j + 1 = i)) :
    m ≤ SimpleGraph.path G := by
  have h := length_le_path_of_isInducedPath G (List.ofFn (fun i : Fin m => f i)) ?_
  · simpa using h
  refine ⟨?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro i j hij
    exact Fin.ext (hinj i j i.2 j.2 hij)
  · intro i j
    have hi : (i : ℕ) < m := by simpa using i.2
    have hj : (j : ℕ) < m := by simpa using j.2
    simpa [List.get_eq_getElem, List.getElem_ofFn] using hadj i j hi hj

omit [Fintype α] [DecidableEq α] in
lemma exists_geodesic (G : SimpleGraph α) (hconn : G.Connected) (v z : α) :
    ∃ f : ℕ → α, f 0 = v ∧ (∀ i, i ≤ G.dist v z → G.dist v (f i) = i) ∧
      (∀ i, i < G.dist v z → G.Adj (f i) (f (i + 1))) := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v z
  refine ⟨p.getVert, p.getVert_zero, ?_, ?_⟩
  · intro i hi
    have h1 : G.dist v (p.getVert i) ≤ i := by
      have := dist_le (p.take i)
      rw [Walk.take_length] at this
      omega
    have h2 : G.dist (p.getVert i) z ≤ G.dist v z - i := by
      have := dist_le (p.drop i)
      rw [Walk.drop_length] at this
      omega
    have h3 := hconn.dist_triangle (u := v) (v := p.getVert i) (w := z)
    omega
  · intro i hi
    exact p.adj_getVert_succ (by omega)

omit [Fintype α] [DecidableEq α] in
lemma dist_le_of_adj (G : SimpleGraph α) (hconn : G.Connected) {v x y : α} (h : G.Adj x y) :
    G.dist v y ≤ G.dist v x + 1 := by
  have := hconn.dist_triangle (u := v) (v := x) (w := y)
  rw [dist_eq_one_iff_adj.mpr h] at this
  exact this

omit [Fintype α] [DecidableEq α] in
lemma geodesic_iff (G : SimpleGraph α) (hconn : G.Connected) (v : α) (d : ℕ) (f : ℕ → α)
    (hd : ∀ i, i ≤ d → G.dist v (f i) = i) (ha : ∀ i, i < d → G.Adj (f i) (f (i + 1)))
    (i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    G.Adj (f i) (f j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro h
    have h1 := dist_le_of_adj G hconn (v := v) h
    have h2 := dist_le_of_adj G hconn (v := v) h.symm
    rw [hd i hi, hd j hj] at h1 h2
    have hne : i ≠ j := by
      rintro rfl
      exact G.irrefl h
    omega
  · rintro (h | h)
    · subst h
      exact ha i (by omega)
    · subst h
      exact (ha j (by omega)).symm

lemma add_one_le_path (G : SimpleGraph α) (hconn : G.Connected) (v z : α) :
    G.dist v z + 1 ≤ SimpleGraph.path G := by
  obtain ⟨f, -, hd, ha⟩ := exists_geodesic G hconn v z
  apply le_path_of_fun G f
  · intro i j hi hj hij
    have := hd i (by omega)
    rw [hij, hd j (by omega)] at this
    exact this.symm
  · intro i j hi hj
    exact geodesic_iff G hconn v _ f hd ha i j (by omega) (by omega)
lemma le_path_of_fun' (G : SimpleGraph α) (f : ℕ → α) (n : ℕ)
    (hadj : ∀ i, i + 1 < n → G.Adj (f i) (f (i + 1)))
    (hfar : ∀ i j, j < n → i + 2 ≤ j → ¬ G.Adj (f i) (f j) ∧ f i ≠ f j) :
    n ≤ SimpleGraph.path G := by
  apply le_path_of_fun G f n
  · intro i j hi hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · by_cases h1 : i + 1 = j
      · subst h1
        exact G.ne_of_adj (hadj i hj) hij
      · exact (hfar i j hj (by omega)).2 hij
    · by_cases h1 : j + 1 = i
      · subst h1
        exact G.ne_of_adj (hadj j hi) hij.symm
      · exact (hfar j i hi (by omega)).2 hij.symm
  · intro i j hi hj
    constructor
    · intro h
      by_contra hc
      rcases Nat.lt_trichotomy i j with hl | rfl | hl
      · exact (hfar i j hj (by omega)).1 h
      · exact G.irrefl h
      · exact (hfar j i hi (by omega)).1 h.symm
    · rintro (h | h)
      · subst h
        exact hadj i hj
      · subst h
        exact (hadj j hi).symm

lemma glue (G : SimpleGraph α) (h : ℕ → α) (K : ℕ) (_hK : 1 ≤ K) (t : ℕ → α) (s m : ℕ)
    (hsm : s ≤ m)
    (hHa : ∀ i, i + 1 < K → G.Adj (h i) (h (i + 1)))
    (hHf : ∀ i j, j < K → i + 2 ≤ j → ¬ G.Adj (h i) (h j) ∧ h i ≠ h j)
    (hTa : ∀ b, s ≤ b → b < m → G.Adj (t b) (t (b + 1)))
    (hTf : ∀ a b, s ≤ a → b ≤ m → a + 2 ≤ b → ¬ G.Adj (t a) (t b) ∧ t a ≠ t b)
    (hlast : G.Adj (h (K - 1)) (t s))
    (hX : ∀ i b, i < K → s ≤ b → b ≤ m → (i + 1 < K ∨ s < b) → ¬ G.Adj (h i) (t b))
    (hXne : ∀ i b, i < K → s ≤ b → b ≤ m → h i ≠ t b) :
    K + (m + 1 - s) ≤ SimpleGraph.path G := by
  let f : ℕ → α := fun i => if i < K then h i else t (i - K + s)
  apply le_path_of_fun' G f
  · intro i hi
    by_cases h1 : i + 1 < K
    · simp only [f, if_pos h1, if_pos (by omega : i < K)]
      exact hHa i h1
    · by_cases h2 : i < K
      · have hi' : i = K - 1 := by omega
        simp only [f, if_pos h2, if_neg h1]
        rw [show i + 1 - K + s = s by omega, hi']
        exact hlast
      · simp only [f, if_neg h2, if_neg h1]
        rw [show i + 1 - K + s = (i - K + s) + 1 by omega]
        exact hTa _ (by omega) (by omega)
  · intro i j hj hij
    by_cases hjK : j < K
    · simp only [f, if_pos hjK, if_pos (by omega : i < K)]
      exact hHf i j hjK hij
    · by_cases hiK : i < K
      · simp only [f, if_pos hiK, if_neg hjK]
        exact ⟨hX i _ hiK (by omega) (by omega) (by omega), hXne i _ hiK (by omega) (by omega)⟩
      · simp only [f, if_neg hiK, if_neg hjK]
        exact hTf _ _ (by omega) (by omega) (by omega)

omit [Fintype α] [DecidableEq α] in
lemma exists_geodesic2 (G : SimpleGraph α) (hconn : G.Connected) (v z : α) :
    ∃ f : ℕ → α, f 0 = v ∧ f (G.dist v z) = z ∧ (∀ i, i ≤ G.dist v z → G.dist v (f i) = i) ∧
      (∀ i, i ≤ G.dist v z → G.dist (f i) z = G.dist v z - i) ∧
      (∀ i, i < G.dist v z → G.Adj (f i) (f (i + 1))) := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v z
  have key : ∀ i, i ≤ G.dist v z →
      G.dist v (p.getVert i) = i ∧ G.dist (p.getVert i) z = G.dist v z - i := by
    intro i hi
    have h1 : G.dist v (p.getVert i) ≤ i := by
      have := dist_le (p.take i)
      rw [Walk.take_length] at this
      omega
    have h2 : G.dist (p.getVert i) z ≤ G.dist v z - i := by
      have := dist_le (p.drop i)
      rw [Walk.drop_length] at this
      omega
    have h3 := hconn.dist_triangle (u := v) (v := p.getVert i) (w := z)
    omega
  refine ⟨p.getVert, p.getVert_zero, ?_, fun i hi => (key i hi).1, fun i hi => (key i hi).2, ?_⟩
  · rw [← hp]
    exact p.getVert_length
  · intro i hi
    exact p.adj_getVert_succ (by omega)

omit [Fintype α] [DecidableEq α] in
lemma dist_chain_le (G : SimpleGraph α) (hconn : G.Connected) (f : ℕ → α) (d : ℕ)
    (ha : ∀ i, i < d → G.Adj (f i) (f (i + 1))) (i k : ℕ) (hk : i + k ≤ d) :
    G.dist (f i) (f (i + k)) ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := dist_le_of_adj G hconn (v := f i) (ha (i + k) (by omega))
    rw [show i + (k + 1) = i + k + 1 by omega]
    omega

/-- Three independent neighbours of `v`: one of them avoids the closed neighbourhoods of two
given neighbours `u`, `w` of `v`. -/
lemma path_induce_le (G : SimpleGraph α) (S : Set α) [Fintype S] :
    SimpleGraph.path (G.induce S) ≤ SimpleGraph.path G := by
  classical
  apply path_le_of_isInducedPath_length_le
  intro l hl
  have hmap : G.isInducedPath (l.map Subtype.val) := by
    refine ⟨hl.1.map Subtype.val_injective, ?_⟩
    intro i j
    simpa only [List.length_map, List.get_eq_getElem, List.getElem_map, induce_adj] using
      hl.2 ⟨i.val, by simpa using i.isLt⟩ ⟨j.val, by simpa using j.isLt⟩
  simpa using length_le_path_of_isInducedPath G _ hmap

omit [Fintype α] [DecidableEq α] in
lemma dist_adj_le (G : SimpleGraph α) (hc : G.Connected) {u v x y : α}
    (h : G.Adj x y) : G.dist u v ≤ G.dist u x + 1 + G.dist y v := by
  have ht := hc.dist_triangle (u := u) (v := x) (w := v)
  have hs := hc.dist_triangle (u := x) (v := y) (w := v)
  rw [dist_eq_one_iff_adj.mpr h] at hs
  omega

/- The two geodesics in Fan Chung's proof of the Induced Path Theorem. -/
private lemma chung_glue (G : SimpleGraph α) (hc : G.Connected) {r : ℕ} (hr : 3 ≤ r)
    (c v w : α) (haLen : G.dist c v = r) (hbLen : G.dist c w < r)
    (a : ℕ → α) (ha0 : a 0 = c)
    (haD : ∀ i, i ≤ r → G.dist c (a i) = i)
    (ha : ∀ i, i < r → G.Adj (a i) (a (i + 1)))
    (hfar : r ≤ G.dist (a 2) w) :
    2 * r - 1 ≤ SimpleGraph.path G := by
  obtain ⟨b, hb0, _, hbD, hbEnd, hb⟩ := exists_geodesic2 G hc c w
  let s := G.dist c w
  have hs : r - 2 ≤ s := by
    have ht := hc.dist_triangle (u := a 2) (v := c) (w := w)
    rw [dist_comm (u := a 2) (v := c), haD 2 (by omega)] at ht
    omega
  have hs0 : 1 ≤ s := by omega
  have anear : ∀ i, 1 ≤ i → i ≤ r → G.dist (a 2) (a i) ≤ (if i = 1 then 1 else i - 2) := by
    intro i hi hir
    by_cases he : i = 1
    · subst i
      exact le_of_eq (dist_eq_one_iff_adj.mpr (ha 1 (by omega)).symm)
    · simp only [if_neg he]
      have h := dist_chain_le G hc a r ha 2 (i - 2) (by omega)
      rwa [show 2 + (i - 2) = i by omega] at h
  have noOverlap : ∀ i j, i ≤ r → 1 ≤ j → j ≤ s → a i ≠ b j := by
    intro i j hi hj hjs h
    have hEq : i = j := by rw [← haD i hi, h, hbD j hjs]
    have ht := hc.dist_triangle (u := a 2) (v := b j) (w := w)
    rw [hbEnd j hjs, ← h] at ht
    have hn := anear i (by omega) hi
    split at hn <;> omega
  have noChord : ∀ i j, 1 ≤ i → i ≤ r → 1 ≤ j → j ≤ s →
      (i ≠ 1 ∨ j ≠ 1) → ¬ G.Adj (a i) (b j) := by
    intro i j hi hir hj hjs hnot hadj
    have hn := anear i hi hir
    have ht := dist_adj_le G hc (u := a 2) (v := w) hadj
    rw [hbEnd j hjs] at ht
    have hd := dist_le_of_adj G hc (v := c) hadj.symm
    rw [haD i hir, hbD j hjs] at hd
    rcases hnot with hni | hnj
    · rw [if_neg hni] at hn
      omega
    · by_cases he : i = 1
      · rw [if_pos he] at hn
        omega
      · rw [if_neg he] at hn
        omega
  have revAdj : ∀ k, k + 1 < r + 1 → G.Adj (a (r - k)) (a (r - (k + 1))) := by
    intro k hk
    have h := (ha (r - (k + 1)) (by omega)).symm
    rwa [show r - (k + 1) + 1 = r - k by omega] at h
  have revFar : ∀ k i, i < r + 1 → k + 2 ≤ i →
      ¬ G.Adj (a (r - k)) (a (r - i)) ∧ a (r - k) ≠ a (r - i) := by
    intro k i hi hki
    have h1 := haD (r - k) (by omega)
    have h2 := haD (r - i) (by omega)
    constructor
    · intro h
      have := dist_le_of_adj G hc (v := c) h.symm
      omega
    · intro h
      rw [h, h2] at h1
      omega
  have bFar : ∀ i j, 1 ≤ i → j ≤ s → i + 2 ≤ j → ¬ G.Adj (b i) (b j) ∧ b i ≠ b j := by
    intro i j hi hj hij
    have h1 := hbD i (by omega)
    have h2 := hbD j hj
    constructor
    · intro h
      have := dist_le_of_adj G hc (v := c) h
      omega
    · intro h
      rw [h, h2] at h1
      omega
  by_cases he : G.Adj (a 1) (b 1)
  · have ht := dist_adj_le G hc (u := a 2) (v := w) he
    have hn := anear 1 (by omega) (by omega)
    rw [hbEnd 1 hs0] at ht
    simp at hn
    have h := glue G (fun k => a (r - k)) r (by omega) b 1 s hs0
      (fun k hk => revAdj k (by omega))
      (fun k i hi hki => revFar k i (by omega) hki)
      (fun i _ hi => hb i hi) bFar (by simpa only [show r - (r - 1) = 1 by omega] using he)
      (fun k j hk hj hjs hd => noChord (r - k) j (by omega) (by omega) hj hjs (by omega))
      (fun k j _ hj hjs => noOverlap (r - k) j (by omega) hj hjs)
    omega
  · have h := glue G (fun k => a (r - k)) (r + 1) (by omega) b 1 s hs0
      revAdj revFar (fun i _ hi => hb i hi) bFar
      (by simpa [ha0, hb0] using hb 0 (by omega))
      (by
        intro k j hk hj hjs hd
        by_cases hz : k = r
        · subst k
          have d1 := hbD j hjs
          have d2 := dist_le_of_adj G hc (v := c) (x := c) (y := b j)
          simp only [Nat.sub_self, ha0]
          intro h
          specialize d2 h
          simp at d2
          omega
        · by_cases hh : r - k = 1 ∧ j = 1
          · simpa only [hh.1, hh.2] using he
          · exact noChord _ _ (by omega) (by omega) hj hjs (by omega))
      (fun k j _ hj hjs => noOverlap (r - k) j (by omega) hj hjs)
    omega

omit [DecidableEq α] in
private lemma dist_le_toNat_eccent (G : SimpleGraph α) (hc : G.Connected) (u v : α) :
    G.dist u v ≤ (G.eccent u).toNat := by
  have h := edist_le_eccent (G := G) (u := u) (v := v)
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite u
  rw [← hw] at h ⊢
  exact ENat.toNat_le_toNat h (edist_ne_top_iff_reachable.mpr (hc u w))

omit [DecidableEq α] in
private lemma exists_far_of_radius (G : SimpleGraph α) (hc : G.Connected) (u : α) :
    ∃ w, G.radius.toNat ≤ G.dist u w := by
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite u
  refine ⟨w, ENat.toNat_le_toNat ?_ (edist_ne_top_iff_reachable.mpr (hc u w))⟩
  rw [hw]
  exact G.radius_le_eccent

omit [Fintype α] [DecidableEq α] in
private lemma dist_induce_le (G : SimpleGraph α) (S : Set α)
    (hc : (G.induce S).Connected) (u v : S) :
    G.dist u v ≤ (G.induce S).dist u v := by
  have hne := edist_ne_top_iff_reachable.mpr (hc u v)
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  have h := dist_le (p.map (SimpleGraph.Embedding.induce S).toHom)
  rwa [Walk.length_map, hp] at h

private lemma radius_induction (n : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), Fintype.card V = n →
      G.Connected → ∀ r : ℕ, 3 ≤ r → r ≤ G.radius.toNat →
      2 * r - 1 ≤ SimpleGraph.path G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hcard hc r hr hrad
    classical
    obtain ⟨v₀⟩ := hc.nonempty
    obtain ⟨v₁, hv₁⟩ := exists_far_of_radius G hc v₀
    have hvne : v₀ ≠ v₁ := by
      intro he
      rw [← he, dist_self] at hv₁
      omega
    let : Nontrivial V := ⟨⟨v₀, v₁, hvne⟩⟩
    obtain ⟨v, hv⟩ := hc.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let S : Set V := {v}ᶜ
    let K := G.induce S
    have hK : K.Connected := hv
    have hlt : Fintype.card S < n := by
      rw [← hcard]
      apply Fintype.card_subtype_lt (x := v)
      simp [S]
    by_cases hKr : r ≤ K.radius.toNat
    · exact (ih _ hlt K rfl hK r hr hKr).trans (path_induce_le G S)
    let : Nonempty S := hK.nonempty
    obtain ⟨c, hcK⟩ := K.exists_eccent_eq_radius
    have hclose : ∀ y : V, y ≠ v → G.dist c y < r := by
      intro y hy
      let y' : S := ⟨y, by simpa [S] using hy⟩
      have hd := dist_induce_le G S hK c y'
      have he := dist_le_toNat_eccent K hK c y'
      rw [hcK] at he
      exact lt_of_le_of_lt (hd.trans he) (by omega)
    have hd : G.dist c v = r := by
      obtain ⟨w, hw⟩ := exists_far_of_radius G hc c
      have hwv : w = v := by
        by_contra hn
        have := hclose w hn
        omega
      subst w
      apply le_antisymm _ (hrad.trans hw)
      obtain ⟨q, h⟩ := hc.preconnected.exists_adj_of_nontrivial v
      have hq := hclose q h.ne.symm
      have h1 := dist_le_of_adj G hc (v := (c : V)) h.symm
      omega
    obtain ⟨f, hf0, _, hfD, hfEnd, hfA⟩ := exists_geodesic2 G hc c v
    rw [hd] at hfD hfEnd hfA
    obtain ⟨w, hw⟩ := exists_far_of_radius G hc (f 2)
    have hwv : w ≠ v := by
      rintro rfl
      have := hfEnd 2 (by omega)
      omega
    exact chung_glue G hc hr c v w hd (hclose w hwv) f hf0 hfD hfA (hrad.trans hw)

/-- Fan Chung's induced path bound in the range of radii needed here. -/
lemma twice_radius_sub_one_le (G : SimpleGraph α) (hc : G.Connected)
    (hr : 3 ≤ G.radius.toNat) : 2 * G.radius.toNat - 1 ≤ SimpleGraph.path G :=
  radius_induction _ G rfl hc _ hr le_rfl

private def C4Free (G : SimpleGraph α) : Prop :=
  ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

omit [Fintype α] [DecidableEq α] in
private lemma unique_common (G : SimpleGraph α) (hC4 : C4Free G)
    {x p s t : α} (hs : G.Adj x s) (hsp : G.Adj s p) (ht : G.Adj x t) (htp : G.Adj t p)
    (hxp : x ≠ p) : s = t := by
  by_contra hst
  exact hC4 ⟨x, s, p, t, G.ne_of_adj hs, hxp, G.ne_of_adj ht, G.ne_of_adj hsp, hst,
    (G.ne_of_adj htp).symm, hs, hsp, htp.symm, ht.symm⟩

private def Cycle {n : ℕ} (G : SimpleGraph α) (c : ZMod n → α) : Prop :=
  Function.Injective c ∧ ∀ i j, G.Adj (c i) (c j) ↔ j = i + 1 ∨ i = j + 1

omit [Fintype α] [DecidableEq α] in
private lemma Cycle.shift {n : ℕ} {G : SimpleGraph α} {c : ZMod n → α}
    (h : Cycle G c) (k : ZMod n) : Cycle G (fun i => c (i + k)) := by
  refine ⟨fun i j hij => add_right_cancel (h.1 hij), ?_⟩
  intro i j
  rw [h.2]
  rw [show i + k + 1 = (i + 1) + k by ac_rfl,
    show j + k + 1 = (j + 1) + k by ac_rfl]
  simp only [add_left_inj]

omit [Fintype α] [DecidableEq α] in
private lemma cycle_distinct {n : ℕ} {G : SimpleGraph α} {c : ZMod n → α}
    (h : Cycle G c) {i j : ZMod n} (hij : i ≠ j) : c i ≠ c j :=
  fun he => hij (h.1 he)

private lemma path6 (G : SimpleGraph α) (a b c d e f : α)
    (hn : ([a,b,c,d,e,f] : List α).Nodup)
    (h01 : G.Adj a b) (h12 : G.Adj b c) (h23 : G.Adj c d)
    (h34 : G.Adj d e) (h45 : G.Adj e f)
    (n02 : ¬ G.Adj a c) (n03 : ¬ G.Adj a d) (n04 : ¬ G.Adj a e)
    (n05 : ¬ G.Adj a f) (n13 : ¬ G.Adj b d) (n14 : ¬ G.Adj b e)
    (n15 : ¬ G.Adj b f) (n24 : ¬ G.Adj c e) (n25 : ¬ G.Adj c f)
    (n35 : ¬ G.Adj d f) : 6 ≤ SimpleGraph.path G := by
  apply length_le_path_of_isInducedPath G [a,b,c,d,e,f]
  refine ⟨hn, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [h01, h12, h23, h34, h45, n02, n03, n04, n05, n13, n14, n15, n24, n25, n35] <;>
    rw [G.adj_comm] <;>
    simp [h01, h12, h23, h34, h45, n02, n03, n04, n05, n13, n14, n15, n24, n25, n35]

omit [Fintype α] [DecidableEq α] in
private lemma cycle_nodup {n : ℕ} {G : SimpleGraph α} {c : ZMod n → α}
    (h : Cycle G c) (l : List (ZMod n)) (hl : l.Nodup) : (l.map c).Nodup :=
  hl.map h.1

omit [Fintype α] [DecidableEq α] in
private lemma cycle_adj {n : ℕ} {G : SimpleGraph α} {c : ZMod n → α}
    (h : Cycle G c) (i : ZMod n) : G.Adj (c i) (c (i + 1)) :=
  (h.2 _ _).2 (Or.inl rfl)

private lemma cycle6_forward (G : SimpleGraph α) {c : ZMod 6 → α}
    (h : Cycle G c) (x : α) (hx : ∀ i, x ≠ c i) (h0 : G.Adj x (c 0))
    (h1 : ¬ G.Adj x (c 1)) (h2 : ¬ G.Adj x (c 2))
    (h3 : ¬ G.Adj x (c 3)) (h4 : ¬ G.Adj x (c 4)) :
    6 ≤ SimpleGraph.path G := by
  apply path6 G x (c 0) (c 1) (c 2) (c 3) (c 4)
  · rw [List.nodup_cons]
    refine ⟨by simp [hx], ?_⟩
    exact cycle_nodup h [0, 1, 2, 3, 4] (by decide)
  all_goals first | assumption | (rw [h.2]; decide)

omit [Fintype α] [DecidableEq α] in
private lemma Cycle.reverse {n : ℕ} {G : SimpleGraph α} {c : ZMod n → α}
    (h : Cycle G c) : Cycle G (fun i => c (-i)) := by
  refine ⟨fun i j hij => neg_injective (h.1 hij), ?_⟩
  intro i j
  change G.Adj (c (-i)) (c (-j)) ↔ _
  rw [h.2]
  constructor
  · rintro (he | he)
    · right
      calc i = -(-i) := (neg_neg i).symm
        _ = -(-j - 1) := by rw [he]; abel
        _ = j + 1 := by abel
    · left
      calc j = -(-j) := (neg_neg j).symm
        _ = -(-i - 1) := by rw [he]; abel
        _ = i + 1 := by abel
  · rintro (he | he)
    · right
      rw [he]
      abel
    · left
      rw [he]
      abel

private lemma cycle6_contacts_zero (G : SimpleGraph α) (hC4 : C4Free G)
    (hp : SimpleGraph.path G ≤ 5) {c : ZMod 6 → α} (hc : Cycle G c)
    (x : α) (hx : ∀ i, x ≠ c i) (h0 : G.Adj x (c 0)) :
    ∀ i, G.Adj x (c i) ↔ i = 0 ∨ i = 3 := by
  have n2 : ¬ G.Adj x (c 2) := by
    intro h2
    exact hx 1 (unique_common G hC4 h0.symm h2 (cycle_adj hc 0) (cycle_adj hc 1)
      (cycle_distinct hc (by decide)))
  have n4 : ¬ G.Adj x (c 4) := by
    intro h4
    have a05 : G.Adj (c 0) (c 5) := (hc.2 _ _).2 (by decide)
    have a45 : G.Adj (c 4) (c 5) := (hc.2 _ _).2 (by decide)
    exact hx 5 (unique_common G hC4 h0.symm h4 a05 a45.symm (cycle_distinct hc (by decide)))
  have n15 : G.Adj x (c 1) → ¬ G.Adj x (c 5) := by
    intro h1 h5
    have a50 : G.Adj (c 5) (c 0) := (hc.2 _ _).2 (by decide)
    exact hx 0 (unique_common G hC4 h1.symm h5 (cycle_adj hc 0).symm a50.symm (cycle_distinct hc (by decide)))
  have n13 : G.Adj x (c 1) → ¬ G.Adj x (c 3) := by
    intro h1 h3
    exact hx 2 (unique_common G hC4 h1.symm h3 (cycle_adj hc 1) (cycle_adj hc 2)
      (cycle_distinct hc (by decide)))
  have n53 : G.Adj x (c 5) → ¬ G.Adj x (c 3) := by
    intro h5 h3
    exact hx 4 (unique_common G hC4 h5.symm h3 (cycle_adj hc 4).symm (cycle_adj hc 3).symm
      (cycle_distinct hc (by decide)))
  have n1 : ¬ G.Adj x (c 1) := by
    intro h1
    have hpath := cycle6_forward G hc.reverse x (fun i => hx (-i)) h0
      (n15 h1) n4 (n13 h1) n2
    omega
  have n5 : ¬ G.Adj x (c 5) := by
    intro h5
    have hpath := cycle6_forward G hc x hx h0 n1 n2 (n53 h5) n4
    omega
  have h3 : G.Adj x (c 3) := by
    by_contra h3
    have := cycle6_forward G hc x hx h0 n1 n2 h3 n4
    omega
  have indexCases : ∀ i : ZMod 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
  intro i
  rcases indexCases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [h0, n1, n2, h3, n4, n5] <;> decide

private lemma cycle6_contacts (G : SimpleGraph α) (hC4 : C4Free G)
    (hp : SimpleGraph.path G ≤ 5) {c : ZMod 6 → α} (hc : Cycle G c)
    (x : α) (hx : ∀ i, x ≠ c i) (i : ZMod 6) (hi : G.Adj x (c i)) :
    ∀ j, G.Adj x (c j) ↔ j = i ∨ j = i + 3 := by
  intro j
  have h := cycle6_contacts_zero G hC4 hp (hc.shift i) x (fun k => hx (k + i))
    (by simpa using hi) (j - i)
  change G.Adj x (c (j - i + i)) ↔ _ at h
  rw [sub_add_cancel] at h
  rw [h, sub_eq_zero, sub_eq_iff_eq_add, add_comm (3 : ZMod 6) i]

private lemma cycle6_no_far_edge (G : SimpleGraph α) (hp : SimpleGraph.path G ≤ 5)
    {c : ZMod 6 → α} (hc : Cycle G c) {x y z : α} (hx : ∀ i, x ≠ c i)
    (hy : ∀ i, y ≠ c i) (hz : ∀ i, z ≠ c i) (hNY : ∀ i, ¬ G.Adj y (c i))
    (hNZ : ∀ i, ¬ G.Adj z (c i)) (hax : ∀ i, G.Adj x (c i) ↔ i = 0 ∨ i = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) : G.Adj x z := by
  by_contra hxz
  have hzne : z ≠ x := by
    rintro rfl
    exact hNZ 0 ((hax 0).2 (Or.inl rfl))
  have hl := path6 G z y x (c 0) (c 1) (c 2)
  have h := hl (by
      refine List.nodup_cons.mpr ⟨by simp [hyz.ne.symm, hzne, hz], ?_⟩
      refine List.nodup_cons.mpr ⟨by simp [hxy.ne.symm, hy], ?_⟩
      refine List.nodup_cons.mpr ⟨by simp [hx], ?_⟩
      exact cycle_nodup hc [0, 1, 2] (by decide))
    hyz.symm hxy.symm ((hax 0).2 (Or.inl rfl)) ((hc.2 _ _).2 (by decide)) ((hc.2 _ _).2 (by decide))
    (fun e => hxz e.symm) (hNZ 0) (hNZ 1) (hNZ 2) (hNY 0) (hNY 1) (hNY 2)
    (fun e => (by decide : ¬ ((1 : ZMod 6) = 0 ∨ (1 : ZMod 6) = 3)) ((hax 1).1 e))
    (fun e => (by decide : ¬ ((2 : ZMod 6) = 0 ∨ (2 : ZMod 6) = 3)) ((hax 2).1 e))
    (fun e => (by decide : ¬ ((2 : ZMod 6) = 0 + 1 ∨ (0 : ZMod 6) = 2 + 1)) ((hc.2 _ _).1 e))
  omega

omit [Fintype α] [DecidableEq α] in
private lemma cycle6_touch_le_three (G : SimpleGraph α) (hC4 : C4Free G)
    {c : ZMod 6 → α} (hc : Cycle G c) (A : Finset α)
    (hA : ∀ x ∈ A, ∃ i, ∀ j, G.Adj x (c j) ↔ j = i ∨ j = i + 3) :
    A.card ≤ 3 := by
  classical
  have rep : ∀ i : ZMod 6, ∃ k : Fin 3,
      (k.val : ZMod 6) = i ∨ (k.val : ZMod 6) = i + 3 := by decide
  have hchoose : ∀ x : A, ∃ k : Fin 3,
      G.Adj x (c (k.val : ZMod 6)) ∧ G.Adj x (c ((k.val : ZMod 6) + 3)) := by
    intro x
    obtain ⟨i, hi⟩ := hA x x.property
    obtain ⟨k, hk⟩ := rep i
    refine ⟨k, (hi _).2 hk, (hi _).2 ?_⟩
    rcases hk with h | h
    · right
      rw [h]
    · left
      rw [h]
      exact (by decide : ∀ i : ZMod 6, i + 3 + 3 = i) i
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hnx : G.Adj y (c ((f x).val : ZMod 6)) ∧
        G.Adj y (c (((f x).val : ZMod 6) + 3)) := by rw [h]; exact hf y
    exact unique_common G hC4 (hf x).1.symm (hf x).2 hnx.1.symm hnx.2
      (cycle_distinct hc ((by decide : ∀ i : ZMod 6, i ≠ i + 3) _))
  have := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using this

omit [Fintype α] [DecidableEq α] in
private lemma cycle6_touch_independent (G : SimpleGraph α) (hC4 : C4Free G)
    {c : ZMod 6 → α} (hc : Cycle G c) {x y : α}
    (hx : ∀ i, x ≠ c i) (hy : ∀ i, y ≠ c i)
    (i j : ZMod 6)
    (ha : ∀ k, G.Adj x (c k) ↔ k = i ∨ k = i + 3)
    (hb : ∀ k, G.Adj y (c k) ↔ k = j ∨ k = j + 3) :
    ¬ G.Adj x y := by
  intro hxy
  have hax := (ha i).2 (Or.inl rfl)
  have hbx := (ha (i + 3)).2 (Or.inr rfl)
  have h3 : ∀ i : ZMod 6, i + 3 + 3 = i := by decide
  have hne := cycle_distinct hc ((by decide : ∀ i : ZMod 6, i ≠ i + 3) i)
  by_cases hji : j = i ∨ j = i + 3
  · have hay : G.Adj y (c i) := by
      apply (hb _).2
      rcases hji with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (h3 i).symm
    have hby : G.Adj y (c (i + 3)) := by
      apply (hb _).2
      rcases hji with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    exact hxy.ne (unique_common G hC4 hax.symm hbx hay.symm hby hne)
  have near : ∀ i j : ZMod 6, ¬ (j = i ∨ j = i + 3) →
      ∃ k, (k = i ∨ k = i + 3) ∧ (k = j + 1 ∨ j = k + 1) := by decide
  obtain ⟨k, hki, hkj⟩ := near i j hji
  have hyj := (hb j).2 (Or.inl rfl)
  have hxk := (ha k).2 hki
  have hjk := (hc.2 j k).2 hkj
  exact hC4 ⟨x, y, c j, c k, hxy.ne, hx j, hx k, hy j, hy k, hjk.ne,
    hxy, hyj, hjk, hxk.symm⟩

omit [Fintype α] [DecidableEq α] in
private lemma adjacent_closed (G : SimpleGraph α) (hc : G.Connected)
    {P : α → Prop} {u : α} (hu : P u)
    (hstep : ∀ ⦃x y⦄, P x → G.Adj x y → P y) : ∀ v, P v := by
  intro v
  obtain ⟨p⟩ := hc u v
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (hstep hu h)

private lemma separate_cycle6 (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hC4 : C4Free G) (hp : SimpleGraph.path G ≤ 5) {c : ZMod 6 → α} (hc : Cycle G c) :
    ∃ C A B : Finset α,
      Disjoint C A ∧ Disjoint (C ∪ A) B ∧ C ∪ A ∪ B = Finset.univ ∧ C.card = 6 ∧
      A.card ≤ 3 ∧
      (∀ x ∈ C, (C.filter (G.Adj x)).card = 2) ∧
      (∀ x ∈ A, (C.filter (G.Adj x)).card = 2 ∧ ∀ y ∈ A, ¬ G.Adj x y) ∧
      (∀ x ∈ B, (C.filter (G.Adj x)).card = 0 ∧ (A.filter (G.Adj x)).Nonempty) ∧
      (∀ x ∈ B, ∀ y ∈ B, G.Adj x y → A.filter (G.Adj x) = A.filter (G.Adj y)) := by
  classical
  let C : Finset α := Finset.univ.image c
  let A : Finset α := Finset.univ.filter (fun x => (∀ i, x ≠ c i) ∧ ∃ i, G.Adj x (c i))
  let B : Finset α := Finset.univ.filter (fun x => (∀ i, x ≠ c i) ∧ ∀ i, ¬ G.Adj x (c i))
  have hC : ∀ x, x ∈ C ↔ ∃ i, c i = x := by
    simp [C]
  have hA : ∀ x, x ∈ A ↔ (∀ i, x ≠ c i) ∧ ∃ i, G.Adj x (c i) := by
    simp [A]
  have hB : ∀ x, x ∈ B ↔ (∀ i, x ≠ c i) ∧ ∀ i, ¬ G.Adj x (c i) := by
    simp [B]
  have disCA : Disjoint C A := Finset.disjoint_left.mpr fun x hxc hxa => by
    obtain ⟨i, hi⟩ := (hC x).1 hxc
    exact ((hA x).1 hxa).1 i hi.symm
  have disCAB : Disjoint (C ∪ A) B := Finset.disjoint_left.mpr fun x hca hb => by
    rcases Finset.mem_union.mp hca with hxc | hxa
    · obtain ⟨i, hi⟩ := (hC x).1 hxc
      exact ((hB x).1 hb).1 i hi.symm
    · obtain ⟨i, hi⟩ := ((hA x).1 hxa).2
      exact ((hB x).1 hb).2 i hi
  have cover : C ∪ A ∪ B = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hxc : x ∈ C
    · exact Or.inl (Or.inl hxc)
    have neC : ∀ i, x ≠ c i := fun i hi => hxc ((hC x).2 ⟨i, hi.symm⟩)
    by_cases hadj : ∃ i, G.Adj x (c i)
    · exact Or.inl (Or.inr ((hA x).2 ⟨neC, hadj⟩))
    · exact Or.inr ((hB x).2 ⟨neC, fun i hi => hadj ⟨i, hi⟩⟩)
  have hcontact : ∀ x ∈ A, ∃ i, ∀ j, G.Adj x (c j) ↔ j = i ∨ j = i + 3 := by
    intro x hx
    obtain ⟨hne, i, hi⟩ := (hA x).1 hx
    exact ⟨i, cycle6_contacts G hC4 hp hc x hne i hi⟩
  have hEq : ∀ x ∈ B, ∀ y ∈ B, G.Adj x y →
      ∀ z ∈ A, G.Adj x z → G.Adj y z := by
    intro x hx y hy hxy z hz hxz
    obtain ⟨i, hi⟩ := hcontact z hz
    have hnorm : ∀ j, G.Adj z (c (j + i)) ↔ j = 0 ∨ j = 3 := by
      intro j
      rw [hi]
      rw [show i + 3 = 3 + i by ac_rfl]
      simp
    exact (cycle6_no_far_edge G hp (hc.shift i)
      (fun j => ((hA z).1 hz).1 (j + i))
      (fun j => ((hB x).1 hx).1 (j + i))
      (fun j => ((hB y).1 hy).1 (j + i))
      (fun j => ((hB x).1 hx).2 (j + i))
      (fun j => ((hB y).1 hy).2 (j + i)) hnorm hxz.symm hxy).symm
  have hSeen : ∀ y ∈ B, ∃ x ∈ A, G.Adj y x := by
    let P : α → Prop := fun x => x ∈ C ∨ x ∈ A ∨ ∃ z ∈ A, G.Adj x z
    have hs : ∀ v, P v := adjacent_closed G hconn (Or.inl ((hC (c 0)).2 ⟨0, rfl⟩)) (by
      intro x y hx hxy
      by_cases hy : y ∈ B
      · rcases hx with hxc | hxa | ⟨z, hz, hxz⟩
        · obtain ⟨i, rfl⟩ := (hC x).1 hxc
          exact (((hB y).1 hy).2 i hxy.symm).elim
        · exact Or.inr (Or.inr ⟨x, hxa, hxy.symm⟩)
        · have hxb : x ∈ B := by
            have hm := Finset.mem_univ x
            rw [← cover, Finset.mem_union, Finset.mem_union] at hm
            rcases hm with (hxc | hxa) | hxb
            · obtain ⟨i, rfl⟩ := (hC x).1 hxc
              exact (((hB y).1 hy).2 i hxy.symm).elim
            · exfalso
              obtain ⟨i, hi⟩ := hcontact x hxa
              obtain ⟨j, hj⟩ := hcontact z hz
              exact cycle6_touch_independent G hC4 hc ((hA x).1 hxa).1 ((hA z).1 hz).1 i j hi hj hxz
            · exact hxb
          exact Or.inr (Or.inr ⟨z, hz, hEq x hxb y hy hxy z hz hxz⟩)
      · have hm := Finset.mem_univ y
        rw [← cover, Finset.mem_union, Finset.mem_union] at hm
        rcases hm with (hyc | hya) | hyb
        · exact Or.inl hyc
        · exact Or.inr (Or.inl hya)
        · exact (hy hyb).elim)
    intro y hy
    rcases hs y with hyc | hya | hh
    · exact (Finset.disjoint_left.mp disCAB (Finset.mem_union_left _ hyc) hy).elim
    · exact (Finset.disjoint_left.mp disCAB (Finset.mem_union_right _ hya) hy).elim
    · exact hh
  have countC : C.card = 6 := by
    rw [Finset.card_image_of_injective _ hc.1, Finset.card_univ, ZMod.card]
  have two_of_contacts (x : α) (i j : ZMod 6) (hij : i ≠ j)
      (hij' : ∀ k, G.Adj x (c k) ↔ k = i ∨ k = j) :
      (C.filter (G.Adj x)).card = 2 := by
    have heq : C.filter (G.Adj x) = {c i, c j} := by
      ext v
      simp only [Finset.mem_filter, hC, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨k, rfl⟩, hv⟩
        rcases (hij' k).1 hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨⟨_, rfl⟩, (hij' i).2 (Or.inl rfl)⟩
        · exact ⟨⟨_, rfl⟩, (hij' j).2 (Or.inr rfl)⟩
    simp [heq, cycle_distinct hc hij]
  refine ⟨C, A, B, disCA, disCAB, cover, countC, cycle6_touch_le_three G hC4 hc A hcontact,
    ?_, ?_, ?_, ?_⟩
  · rintro x hx
    obtain ⟨i, rfl⟩ := (hC x).1 hx
    apply two_of_contacts (c i) (i + 1) (i - 1)
    · exact (by decide : ∀ i : ZMod 6, i + 1 ≠ i - 1) i
    · intro k
      rw [hc.2]
      apply or_congr Iff.rfl
      constructor
      · intro h
        exact eq_sub_iff_add_eq.mpr h.symm
      · intro h
        exact (eq_sub_iff_add_eq.mp h).symm
  · intro x hx
    obtain ⟨i, hi⟩ := hcontact x hx
    refine ⟨two_of_contacts x i (i + 3) ((by decide : ∀ i : ZMod 6, i ≠ i + 3) i) hi, ?_⟩
    intro y hy
    obtain ⟨j, hj⟩ := hcontact y hy
    exact cycle6_touch_independent G hC4 hc ((hA x).1 hx).1 ((hA y).1 hy).1 i j hi hj
  · intro x hx
    constructor
    · apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro y hy
      obtain ⟨i, rfl⟩ := (hC y).1 hy
      exact ((hB x).1 hx).2 i
    · obtain ⟨y, hy, hxy⟩ := hSeen x hx
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
  · intro x hx y hy hxy
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right fun hz => ⟨hEq x hx y hy hxy z hz, hEq y hy x hx hxy.symm z hz⟩

private def adjCount (G : SimpleGraph α) [DecidableRel G.Adj] (S T : Finset α) : ℕ :=
  ∑ x ∈ S, (T.filter (G.Adj x)).card

omit [Fintype α] in
private lemma adjCount_comm (G : SimpleGraph α) [DecidableRel G.Adj] (S T : Finset α) :
    adjCount G S T = adjCount G T S := by
  calc
    adjCount G S T = (∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then 1 else 0) := by
      simp [adjCount]
    _ = ∑ y ∈ T, ∑ x ∈ S, if G.Adj x y then 1 else 0 := Finset.sum_comm
    _ = adjCount G T S := by
      simp [adjCount, G.adj_comm]

omit [Fintype α] in
private lemma adjCount_union (G : SimpleGraph α) [DecidableRel G.Adj] {S T : Finset α}
    (h : Disjoint S T) (U : Finset α) :
    adjCount G (S ∪ T) U = adjCount G S U + adjCount G T U := by
  unfold adjCount
  rw [Finset.sum_union h]

private lemma indep_le_degree (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) :
    indepNeighborsCard G x ≤ G.degree x := by
  obtain ⟨S, hS, -, hc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G x
  rw [← hc, ← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro v hv
  exact (G.mem_neighborFinset x v).mpr (hS v hv)

omit [DecidableEq α] in
private lemma l_le_of_sum [Nonempty α] (G : SimpleGraph α) (k : ℕ)
    (h : (∑ x, indepNeighborsCard G x) ≤ k * Fintype.card α) : SimpleGraph.l G ≤ k := by
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  unfold SimpleGraph.l averageIndepNeighbors indepNeighbors
  rw [div_le_iff₀ hn]
  exact_mod_cast h

/-- A connected C4-free graph containing an induced C6 and no induced P6 has
average degree at most three. -/
private lemma cycle6_degree_sum_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hC4 : C4Free G) (hp : SimpleGraph.path G ≤ 5)
    {c : ZMod 6 → α} (hc : Cycle G c) : (∑ x, G.degree x) ≤ 3 * Fintype.card α := by
  obtain ⟨C, A, B, hCA, hCAB, hcover, hC, hA, hCC, hAC, hBC, hEq⟩ :=
    separate_cycle6 G hconn hC4 hp hc
  let F := fun x => A.filter (G.Adj x)
  let U := fun x => B.filter (G.Adj x)
  have disAB : Disjoint A B := hCAB.mono_left Finset.subset_union_right
  have hU : ∀ x ∈ B, (U x).card ≤ 1 := by
    intro x hx
    rw [Finset.card_le_one]
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hBC x hx).2
    have haA := (Finset.mem_filter.mp ha).1
    have hyB := (Finset.mem_filter.mp hy).1
    have hzB := (Finset.mem_filter.mp hz).1
    have hxy := (Finset.mem_filter.mp hy).2
    have hxz := (Finset.mem_filter.mp hz).2
    have hay : G.Adj y a := (Finset.mem_filter.mp ((hEq x hx y hyB hxy) ▸ ha)).2
    have haz : G.Adj z a := (Finset.mem_filter.mp ((hEq x hx z hzB hxz) ▸ ha)).2
    apply unique_common G hC4 hxy hay hxz haz
    intro he
    exact Finset.disjoint_left.mp disAB haA (he ▸ hx)
  have hUF : ∀ x ∈ B, (U x).Nonempty → (F x).card ≤ 1 := by
    intro x hx hne
    obtain ⟨y, hy⟩ := hne
    have hyB := (Finset.mem_filter.mp hy).1
    have hxy := (Finset.mem_filter.mp hy).2
    rw [Finset.card_le_one]
    intro a ha b hb
    have hya : a ∈ A.filter (G.Adj y) := (hEq x hx y hyB hxy) ▸ ha
    have hyb : b ∈ A.filter (G.Adj y) := (hEq x hx y hyB hxy) ▸ hb
    exact unique_common G hC4 (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hya).2.symm
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hyb).2.symm hxy.ne
  have hlocal : ∀ x ∈ B, 4 * (F x).card + 2 * (U x).card ≤ 6 + (F x).offDiag.card := by
    intro x hx
    have hk : (F x).card ≤ 3 := (Finset.card_filter_le _ _).trans hA
    have hk0 : 0 < (F x).card := Finset.card_pos.mpr (hBC x hx).2
    have hu := hU x hx
    by_cases hzero : (U x).card = 0
    · rw [Finset.offDiag_card]
      interval_cases (F x).card <;> omega
    · have hf := hUF x hx (Finset.card_pos.mp (by omega))
      omega
  have pairBound : (∑ x ∈ B, (F x).offDiag.card) ≤ A.offDiag.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn (fun v : Sigma (fun _ : α => α × α) => v.2)
    · intro u hu
      obtain ⟨x, a, b⟩ := u
      change ⟨x, (a, b)⟩ ∈ B.sigma (fun x => (F x).offDiag) at hu
      simp only [Finset.mem_sigma, Finset.mem_offDiag, F, Finset.mem_filter] at hu
      exact Finset.mem_offDiag.mpr ⟨hu.2.1.1, hu.2.2.1.1, hu.2.2.2⟩
    · intro u hu v hv he
      obtain ⟨x, a, b⟩ := u
      obtain ⟨y, d, e⟩ := v
      change (a,b) = (d,e) at he
      rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      change ⟨x, (a, b)⟩ ∈ B.sigma (fun x => (F x).offDiag) at hu
      change ⟨y, (a, b)⟩ ∈ B.sigma (fun x => (F x).offDiag) at hv
      simp only [Finset.mem_sigma, Finset.mem_offDiag, F, Finset.mem_filter] at hu hv
      have hxy := unique_common G hC4 hu.2.1.2.symm hu.2.2.1.2 hv.2.1.2.symm hv.2.2.1.2 hu.2.2.2
      subst y
      rfl
  have pairSmall : A.offDiag.card ≤ 6 := by
    rw [Finset.offDiag_card]
    interval_cases A.card <;> decide
  have hBA_BB : 4 * adjCount G B A + 2 * adjCount G B B ≤ 6 * B.card + 6 := by
    have hsum := Finset.sum_le_sum hlocal
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
    unfold adjCount
    dsimp [F, U] at hsum pairBound
    omega
  have hcc : adjCount G C C = 12 := by
    unfold adjCount
    rw [Finset.sum_congr rfl hCC]
    simp [hC]
  have hac : adjCount G A C = 2 * A.card := by
    unfold adjCount
    rw [Finset.sum_congr rfl (fun x hx => (hAC x hx).1)]
    simp [Nat.mul_comm]
  have haa : adjCount G A A = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ((hAC x hx).2))
  have hbc : adjCount G B C = 0 :=
    Finset.sum_eq_zero fun x hx => (hBC x hx).1
  have hcard : C.card + A.card + B.card = Fintype.card α := by
    have h := congrArg Finset.card hcover
    rwa [Finset.card_union_of_disjoint hCAB, Finset.card_union_of_disjoint hCA, Finset.card_univ] at h
  have htotal : (∑ x, G.degree x) = adjCount G Finset.univ Finset.univ := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp [mem_neighborFinset]
  have hsplit (T : Finset α) : adjCount G Finset.univ T =
      adjCount G C T + adjCount G A T + adjCount G B T := by
    rw [← hcover, adjCount_union G hCAB, adjCount_union G hCA]
  have hBAsymm := adjCount_comm G A B
  rw [htotal, hsplit, adjCount_comm G C Finset.univ, adjCount_comm G A Finset.univ,
    adjCount_comm G B Finset.univ, hsplit C, hsplit A, hsplit B, adjCount_comm G C A,
    adjCount_comm G C B, hcc, hac, haa, hbc]
  omega

private lemma cycle6_l_le (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : C4Free G) (hp : SimpleGraph.path G ≤ 5) {c : ZMod 6 → α} (hc : Cycle G c) :
    SimpleGraph.l G ≤ 3 := by
  classical
  let : Nonempty α := hconn.nonempty
  apply l_le_of_sum G 3
  exact (Finset.sum_le_sum fun x _ => indep_le_degree G x).trans
    (cycle6_degree_sum_le G hconn hC4 hp hc)

omit [Fintype α] [DecidableEq α] in
private lemma cycle6_of_vertices (G : SimpleGraph α) (a b c d e f : α)
    (hn : ([a,b,c,d,e,f] : List α).Nodup)
    (h01 : G.Adj a b) (h12 : G.Adj b c) (h23 : G.Adj c d)
    (h34 : G.Adj d e) (h45 : G.Adj e f) (h50 : G.Adj f a)
    (n02 : ¬ G.Adj a c) (n03 : ¬ G.Adj a d) (n04 : ¬ G.Adj a e)
    (n13 : ¬ G.Adj b d) (n14 : ¬ G.Adj b e) (n15 : ¬ G.Adj b f)
    (n24 : ¬ G.Adj c e) (n25 : ¬ G.Adj c f) (n35 : ¬ G.Adj d f) :
    ∃ g : ZMod 6 → α, Cycle G g := by
  let l : List α := [a,b,c,d,e,f]
  let g : ZMod 6 → α := fun i => l[i.val]'(ZMod.val_lt i)
  refine ⟨g, ?_, ?_⟩
  · intro i j h
    apply ZMod.val_injective 6
    exact hn.getElem_inj_iff.mp h
  · intro i j
    have hcases : ∀ i : ZMod 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
    rcases hcases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hcases j with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      constructor
      · intro h
        first
          | decide
          | exact (G.irrefl h).elim
          | exact (n02 h).elim | exact (n02 h.symm).elim
          | exact (n03 h).elim | exact (n03 h.symm).elim
          | exact (n04 h).elim | exact (n04 h.symm).elim
          | exact (n13 h).elim | exact (n13 h.symm).elim
          | exact (n14 h).elim | exact (n14 h.symm).elim
          | exact (n15 h).elim | exact (n15 h.symm).elim
          | exact (n24 h).elim | exact (n24 h.symm).elim
          | exact (n25 h).elim | exact (n25 h.symm).elim
          | exact (n35 h).elim | exact (n35 h.symm).elim
      · intro h
        first
          | exact h01 | exact h01.symm | exact h12 | exact h12.symm
          | exact h23 | exact h23.symm | exact h34 | exact h34.symm
          | exact h45 | exact h45.symm | exact h50 | exact h50.symm
          | exact ((by decide : ¬ _) h).elim

omit [Fintype α] [DecidableEq α] in
private lemma cycle5_near (G : SimpleGraph α) (hC4 : C4Free G)
    {c : ZMod 5 → α} (hc : Cycle G c) {x : α} (hx : ∀ i, x ≠ c i)
    {i j : ZMod 5} (hi : G.Adj x (c i)) (hj : G.Adj x (c j)) (hne : i ≠ j) :
    G.Adj (c i) (c j) := by
  have cases5 : ∀ i j : ZMod 5, i ≠ j →
      (j = i + 1 ∨ i = j + 1) ∨ ∃ k, (k = i + 1 ∨ i = k + 1) ∧
        (k = j + 1 ∨ j = k + 1) := by decide
  rcases cases5 i j hne with h | ⟨k, hik, hjk⟩
  · exact (hc.2 _ _).2 h
  · exact (hx k (unique_common G hC4 hi.symm hj ((hc.2 _ _).2 hik)
      ((hc.2 _ _).2 hjk).symm (cycle_distinct hc hne))).elim

private def Single (G : SimpleGraph α) {n : ℕ} (c : ZMod n → α) (x : α) (i : ZMod n) : Prop :=
  ∀ j, G.Adj x (c j) ↔ j = i

private def Double (G : SimpleGraph α) {n : ℕ} (c : ZMod n → α) (x : α) (i : ZMod n) : Prop :=
  ∀ j, G.Adj x (c j) ↔ j = i ∨ j = i + 1

private lemma cycle5_single_or_double (G : SimpleGraph α) (hC4 : C4Free G)
    {c : ZMod 5 → α} (hc : Cycle G c) {x : α} (hx : ∀ i, x ≠ c i)
    (ha : ∃ i, G.Adj x (c i)) :
    (∃ i, Single G c x i) ∨ (∃ i, Double G c x i) := by
  classical
  obtain ⟨i, hi⟩ := ha
  by_cases h : ∃ j, j ≠ i ∧ G.Adj x (c j)
  · obtain ⟨j, hji, hj⟩ := h
    have adj := (hc.2 i j).1 (cycle5_near G hC4 hc hx hi hj hji.symm)
    have pair : ∃ k, (k = i ∧ k + 1 = j) ∨ (k = j ∧ k + 1 = i) := by
      rcases adj with he | he
      · exact ⟨i, Or.inl ⟨rfl, he.symm⟩⟩
      · exact ⟨j, Or.inr ⟨rfl, he.symm⟩⟩
    obtain ⟨k, hk⟩ := pair
    have hka : G.Adj x (c k) ∧ G.Adj x (c (k + 1)) := by
      rcases hk with ⟨rfl, he⟩ | ⟨rfl, he⟩ <;> rw [he] <;> exact ⟨‹_›, ‹_›⟩
    right
    refine ⟨k, fun a => ⟨?_, ?_⟩⟩
    · intro hh
      by_contra hn
      have nk : a ≠ k := fun he => hn (Or.inl he)
      have nks : a ≠ k + 1 := fun he => hn (Or.inr he)
      have h1 := (hc.2 _ _).1 (cycle5_near G hC4 hc hx hka.1 hh nk.symm)
      have h2 := (hc.2 _ _).1 (cycle5_near G hC4 hc hx hka.2 hh nks.symm)
      exact (by decide : ∀ k a : ZMod 5,
        (a = k + 1 ∨ k = a + 1) → (a = (k + 1) + 1 ∨ k + 1 = a + 1) → False) k a h1 h2
    · rintro (rfl | rfl)
      · exact hka.1
      · exact hka.2
  · left
    refine ⟨i, fun j => ⟨fun h' => ?_, fun h' => h' ▸ hi⟩⟩
    by_contra hji
    exact h ⟨j, hji, h'⟩

private lemma cycle5_extend (G : SimpleGraph α) {c : ZMod 5 → α}
    (hc : Cycle G c) {x y : α} (hx : ∀ i, x ≠ c i) (hy : ∀ i, y ≠ c i)
    (hxy : G.Adj x y) (hNY : ∀ i, ¬ G.Adj y (c i)) (h0 : G.Adj x (c 0))
    (h1 : ¬ G.Adj x (c 1)) (h2 : ¬ G.Adj x (c 2)) (h3 : ¬ G.Adj x (c 3)) :
    6 ≤ SimpleGraph.path G := by
  apply path6 G y x (c 0) (c 1) (c 2) (c 3)
  · refine List.nodup_cons.mpr ⟨by simp [hxy.ne.symm, hy], ?_⟩
    refine List.nodup_cons.mpr ⟨by simp [hx], ?_⟩
    exact cycle_nodup hc [0,1,2,3] (by decide)
  all_goals first | assumption | exact hxy.symm | exact hNY _ | (rw [hc.2]; decide)

private lemma cycle5_all_touch (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : C4Free G) (hp : SimpleGraph.path G ≤ 5) {c : ZMod 5 → α}
    (hc : Cycle G c) (x : α) (hx : ∀ i, x ≠ c i) : ∃ i, G.Adj x (c i) := by
  let P : α → Prop := fun x => (∃ i, x = c i) ∨ ∃ i, G.Adj x (c i)
  have hall : ∀ v, P v := adjacent_closed G hconn (Or.inl ⟨0,rfl⟩) (by
    intro u v hu huv
    by_contra hv
    have hvC : ∀ i, v ≠ c i := fun i hi => hv (Or.inl ⟨i, hi⟩)
    have hvA : ∀ i, ¬ G.Adj v (c i) := fun i hi => hv (Or.inr ⟨i, hi⟩)
    have huC : ∀ i, u ≠ c i := by
      rintro i rfl
      exact hvA i huv.symm
    have huA : ∃ i, G.Adj u (c i) := by
      rcases hu with ⟨i, hi⟩ | he
      · exact (huC i hi).elim
      · exact he
    have hcases := cycle5_single_or_double G hC4 hc huC huA
    rcases hcases with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hs (j : ZMod 5) : G.Adj u (c (j + i)) ↔ j = 0 := by
        rw [hi]
        exact ⟨fun h => add_right_cancel (a := j) (b := 0) (by simpa using h), by rintro rfl; simp⟩
      have hh := cycle5_extend G (hc.shift i) (fun j => huC (j + i)) (fun j => hvC (j + i))
        huv (fun j => hvA (j + i)) ((hs 0).2 rfl)
        (fun h => (by decide : (1 : ZMod 5) ≠ 0) ((hs 1).1 h))
        (fun h => (by decide : (2 : ZMod 5) ≠ 0) ((hs 2).1 h))
        (fun h => (by decide : (3 : ZMod 5) ≠ 0) ((hs 3).1 h))
      omega
    · let d := fun j : ZMod 5 => c (-j + i)
      have hd : Cycle G d := (hc.shift i).reverse
      have hs (j : ZMod 5) : G.Adj u (d j) ↔ -j = 0 ∨ -j = 1 := by
        change G.Adj u (c (-j + i)) ↔ _
        rw [hi, show i + 1 = 1 + i by ac_rfl]
        simp
      have hh := cycle5_extend G hd (fun j => huC (-j + i)) (fun j => hvC (-j + i))
        huv (fun j => hvA (-j + i)) ((hs 0).2 (Or.inl (neg_zero)))
        (fun h => (by decide : ¬ (-(1 : ZMod 5) = 0 ∨ -(1 : ZMod 5) = 1)) ((hs 1).1 h))
        (fun h => (by decide : ¬ (-(2 : ZMod 5) = 0 ∨ -(2 : ZMod 5) = 1)) ((hs 2).1 h))
        (fun h => (by decide : ¬ (-(3 : ZMod 5) = 0 ∨ -(3 : ZMod 5) = 1)) ((hs 3).1 h))
      omega)
  exact (hall x).resolve_left (fun ⟨i, hi⟩ => hx i hi)

omit [Fintype α] [DecidableEq α] in
private lemma no_cross_cycle_edge (G : SimpleGraph α) (hC4 : C4Free G)
    {n : ℕ} {c : ZMod n → α} {x y : α}
    (hx : ∀ i, x ≠ c i) (hy : ∀ i, y ≠ c i) (hxy : G.Adj x y)
    {i j : ZMod n} (hi : G.Adj x (c i)) (hj : G.Adj y (c j)) :
    ¬ G.Adj (c i) (c j) := by
  intro h
  exact hC4 ⟨x, y, c j, c i, hxy.ne, hx j, hx i, hy j, hy i, h.ne.symm, hxy, hj, h.symm, hi.symm⟩

omit [Fintype α] [DecidableEq α] in
private lemma cycle5_double_neighbor (G : SimpleGraph α) (hC4 : C4Free G) {c : ZMod 5 → α}
    (hc : Cycle G c) {x y : α} (hx : ∀ i, x ≠ c i) (hy : ∀ i, y ≠ c i)
    (hxy : G.Adj x y) (hyC : ∃ i, G.Adj y (c i)) {i : ZMod 5} (hi : Double G c x i) :
    Single G c y (i + 3) := by
  have h : ∀ j, G.Adj y (c j) → j = i + 3 := by
    intro j hj
    have h0 := fun h => no_cross_cycle_edge G hC4 hx hy hxy (hi i |>.2 (Or.inl rfl)) hj ((hc.2 _ _).2 h)
    have h1 := fun h => no_cross_cycle_edge G hC4 hx hy hxy (hi (i+1) |>.2 (Or.inr rfl)) hj ((hc.2 _ _).2 h)
    exact (by decide : ∀ i j : ZMod 5, ¬ (j = i + 1 ∨ i = j + 1) →
      ¬ (j = i + 1 + 1 ∨ i + 1 = j + 1) → j = i + 3) i j h0 h1
  intro j
  refine ⟨h j, ?_⟩
  rintro rfl
  obtain ⟨k, hk⟩ := hyC
  rwa [h k hk] at hk

private lemma cycle5_single_edge (G : SimpleGraph α) (hC4 : C4Free G) {c : ZMod 5 → α}
    (hc : Cycle G c) (hNC6 : ¬ ∃ d : ZMod 6 → α, Cycle G d)
    {x y : α} (hx : ∀ i, x ≠ c i) (hy : ∀ i, y ≠ c i)
    (hxy : G.Adj x y) {i j : ZMod 5} (hi : Single G c x i) (hj : Single G c y j) :
    i = j := by
  by_contra hne
  have noNear := fun h => no_cross_cycle_edge G hC4 hx hy hxy ((hi i).2 rfl) ((hj j).2 rfl)
    ((hc.2 i j).2 h)
  have delta : j = i + 2 ∨ j = i + 3 :=
    (by decide : ∀ i j : ZMod 5, i ≠ j → ¬ (j = i + 1 ∨ i = j + 1) → j = i + 2 ∨ j = i + 3)
      i j hne noNear
  have aux {d : ZMod 5 → α} (hd : Cycle G d) (hnx : ∀ i, x ≠ d i) (hny : ∀ i, y ≠ d i)
      (hx0 : Single G d x 0) (hy3 : Single G d y 3) : False := by
    apply hNC6
    apply cycle6_of_vertices G x y (d 3) (d 2) (d 1) (d 0)
    · refine List.nodup_cons.mpr ⟨by simp [hxy.ne, hnx], ?_⟩
      refine List.nodup_cons.mpr ⟨by simp [hny], ?_⟩
      exact cycle_nodup hd [3,2,1,0] (by decide)
    all_goals first
      | exact hxy
      | exact (hy3 _).2 rfl
      | exact ((hx0 _).2 rfl).symm
      | (rw [hx0]; decide)
      | (rw [hy3]; decide)
      | (rw [hd.2]; decide)
  rcases delta with h | h
  · let d := fun k : ZMod 5 => c (-k + i)
    apply aux ((hc.shift i).reverse) (fun k => hx (-k+i)) (fun k => hy (-k+i))
    · intro k
      change G.Adj x (c (-k + i)) ↔ _
      rw [hi]
      simp
    · intro k
      change G.Adj y (c (-k + i)) ↔ _
      rw [hj, h, show i + 2 = 2 + i by ac_rfl]
      rw [add_left_inj]
      exact (by decide : ∀ k : ZMod 5, -k = 2 ↔ k = 3) k
  · apply aux (hc.shift i) (fun k => hx (k+i)) (fun k => hy (k+i))
    · intro k
      change G.Adj x (c (k + i)) ↔ _
      rw [hi]
      simp
    · intro k
      change G.Adj y (c (k + i)) ↔ _
      rw [hj, h, show i + 3 = 3 + i by ac_rfl]
      simp

private lemma cycle5_outside_bound (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : C4Free G) (hp : SimpleGraph.path G ≤ 5) {c : ZMod 5 → α} (hc : Cycle G c)
    (hNC6 : ¬ ∃ d : ZMod 6 → α, Cycle G d) {x : α} (hx : ∀ i, x ≠ c i) :
    indepNeighborsCard G x ≤ 2 := by
  classical
  obtain ⟨S, hSadj, hSI, hSc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G x
  rw [← hSc]
  have htouch (y : α) (hy : ∀ i, y ≠ c i) := cycle5_all_touch G hconn hC4 hp hc y hy
  have htype (y : α) (hy : ∀ i, y ≠ c i) := cycle5_single_or_double G hC4 hc hy (htouch y hy)
  rcases htype x hx with ⟨i, hi⟩ | ⟨i, hi⟩
  · let P : α → Prop := fun y => (∀ j, y ≠ c j) ∧ ∃ j, Double G c y j
    have hdouble : (S.filter P).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy z hz
      obtain ⟨hyS, hyo, j, hj⟩ := Finset.mem_filter.mp hy
      obtain ⟨hzS, hzo, k, hk⟩ := Finset.mem_filter.mp hz
      have hjx := cycle5_double_neighbor G hC4 hc hyo hx (hSadj y hyS).symm (htouch x hx) hj
      have hkx := cycle5_double_neighbor G hC4 hc hzo hx (hSadj z hzS).symm (htouch x hx) hk
      have hei := (hjx i).1 ((hi i).2 rfl)
      have hei' := (hkx i).1 ((hi i).2 rfl)
      have hjk : j = k := add_right_cancel (hei.symm.trans hei')
      subst k
      exact unique_common G hC4 ((hj j).2 (Or.inl rfl)).symm ((hj (j+1)).2 (Or.inr rfl))
        ((hk j).2 (Or.inl rfl)).symm ((hk (j+1)).2 (Or.inr rfl))
        (cycle_distinct hc ((by decide : ∀ j : ZMod 5, j ≠ j + 1) j))
    have hrest (y : α) (hy : y ∈ S.filter (fun y => ¬ P y)) :
        y = c i ∨ G.Adj y (c i) := by
      obtain ⟨hyS, hyP⟩ := Finset.mem_filter.mp hy
      by_cases hyo : ∀ j, y ≠ c j
      · rcases htype y hyo with ⟨j, hj⟩ | hj
        · have he := cycle5_single_edge G hC4 hc hNC6 hx hyo (hSadj y hyS) hi hj
          exact Or.inr ((hj i).2 he)
        · exact (hyP ⟨hyo, hj⟩).elim
      · have hye : ∃ j, y = c j := by simpa only [not_forall, not_not] using hyo
        obtain ⟨j, rfl⟩ := hye
        exact Or.inl (congrArg c ((hi j).1 (hSadj _ hyS)))
    have hother : (S.filter (fun y => ¬ P y)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy z hz
      have hys := (Finset.mem_filter.mp hy).1
      have hzs := (Finset.mem_filter.mp hz).1
      rcases hrest y hy with rfl | hyc <;> rcases hrest z hz with rfl | hzc
      · rfl
      · by_contra h
        exact hSI hys hzs h hzc.symm
      · by_contra h
        exact hSI hys hzs h hyc
      · exact unique_common G hC4 (hSadj y hys) hyc (hSadj z hzs) hzc (hx i)
    have := Finset.card_filter_add_card_filter_not (s := S) P
    omega
  · let P : α → Prop := fun y => ∃ j, y = c j
    have hinside : (S.filter P).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy z hz
      obtain ⟨hyS, j, rfl⟩ := Finset.mem_filter.mp hy
      obtain ⟨hzS, k, rfl⟩ := Finset.mem_filter.mp hz
      have hji := (hi j).1 (hSadj _ hyS)
      have hki := (hi k).1 (hSadj _ hzS)
      rcases hji with rfl | rfl <;> rcases hki with rfl | rfl
      · rfl
      · by_contra h
        exact hSI hyS hzS h (cycle_adj hc j)
      · by_contra h
        exact hSI hyS hzS h (cycle_adj hc k).symm
      · rfl
    have houtside : (S.filter (fun y => ¬ P y)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy z hz
      obtain ⟨hyS, hyP⟩ := Finset.mem_filter.mp hy
      obtain ⟨hzS, hzP⟩ := Finset.mem_filter.mp hz
      have hyo : ∀ j, y ≠ c j := fun j he => hyP ⟨j, he⟩
      have hzo : ∀ j, z ≠ c j := fun j he => hzP ⟨j, he⟩
      have hyc := cycle5_double_neighbor G hC4 hc hx hyo (hSadj y hyS) (htouch y hyo) hi
      have hzc := cycle5_double_neighbor G hC4 hc hx hzo (hSadj z hzS) (htouch z hzo) hi
      exact unique_common G hC4 (hSadj y hyS) ((hyc _).2 rfl)
        (hSadj z hzS) ((hzc _).2 rfl) (hx (i+3))
    have := Finset.card_filter_add_card_filter_not (s := S) P
    omega

private lemma cycle5_cycle_bound (G : SimpleGraph α) [DecidableRel G.Adj] (hC4 : C4Free G)
    {c : ZMod 5 → α} (hc : Cycle G c)
    (C I : Finset α) (hC : ∀ x, x ∈ C ↔ ∃ i, x = c i) (hI : ∀ x, x ∈ I ↔ x ∉ C)
    (p : α → α) (hp : ∀ x ∈ I, p x ∈ C ∧ G.Adj x (p x)) (a : α) (ha : a ∈ C) :
    indepNeighborsCard G a ≤ 2 + (I.filter (fun x => p x = a)).card := by
  classical
  obtain ⟨S, hSadj, hSI, hSc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G a
  let T := C.filter (G.Adj a) ∪ I.filter (fun x => p x = a)
  let f := fun x => if x ∈ I ∧ p x ≠ a then p x else x
  have hmaps : Set.MapsTo f (↑S : Set α) (↑T : Set α) := by
    intro x hx
    change x ∈ S at hx
    change f x ∈ T
    by_cases h : x ∈ I ∧ p x ≠ a
    · have ho : ∀ i, x ≠ c i := fun i hi => (hI x).1 h.1 ((hC x).2 ⟨i, hi⟩)
      obtain ⟨i, rfl⟩ := (hC a).1 ha
      obtain ⟨j, hj⟩ := (hC (p x)).1 (hp x h.1).1
      have hne : i ≠ j := fun he => h.2 (hj.trans (congrArg c he).symm)
      have hax : G.Adj (c i) (p x) := by
        rw [hj]
        apply cycle5_near G hC4 hc ho (hSadj x hx).symm _ hne
        exact hj ▸ (hp x h.1).2
      rw [show f x = p x by simp [f, h]]
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(hp x h.1).1, hax⟩)
    · rw [show f x = x by simp [f,h]]
      by_cases hxc : x ∈ C
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxc, hSadj x hx⟩)
      · have hxi := (hI x).2 hxc
        have hpx : p x = a := by
          by_contra hne
          exact h ⟨hxi, hne⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxi, hpx⟩)
  have hinj : Set.InjOn f (↑S : Set α) := by
    intro x hx y hy hxy
    change x ∈ S at hx
    change y ∈ S at hy
    by_cases hxp : x ∈ I ∧ p x ≠ a <;> by_cases hyp : y ∈ I ∧ p y ≠ a
    · simp only [f, if_pos hxp, if_pos hyp] at hxy
      exact unique_common G hC4 (hSadj x hx) (hp x hxp.1).2 (hSadj y hy)
        (hxy ▸ (hp y hyp.1).2) hxp.2.symm
    · simp only [f, if_pos hxp, if_neg hyp] at hxy
      by_contra hn
      exact hSI hx hy hn (hxy ▸ (hp x hxp.1).2)
    · simp only [f, if_neg hxp, if_pos hyp] at hxy
      by_contra hn
      exact hSI hx hy hn ((hxy ▸ (hp y hyp.1).2).symm)
    · simpa [f, hxp, hyp] using hxy
  have hDis : Disjoint (C.filter (G.Adj a)) (I.filter (fun x => p x = a)) :=
    Finset.disjoint_left.mpr fun x hxc hxi =>
      (hI x).1 (Finset.mem_filter.mp hxi).1 (Finset.mem_filter.mp hxc).1
  have hTwo : (C.filter (G.Adj a)).card = 2 := by
    obtain ⟨i, rfl⟩ := (hC a).1 ha
    have hEq : C.filter (G.Adj (c i)) = {c (i+1), c (i-1)} := by
      ext y
      simp only [Finset.mem_filter, hC, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨j, rfl⟩, hy⟩
        rcases (hc.2 i j).1 hy with h | h
        · exact Or.inl (congrArg c h)
        · exact Or.inr (congrArg c (eq_sub_iff_add_eq.mpr h.symm))
      · rintro (rfl | rfl)
        · exact ⟨⟨_,rfl⟩, cycle_adj hc i⟩
        · exact ⟨⟨_,rfl⟩, (hc.2 _ _).2 (Or.inr (sub_add_cancel i 1).symm)⟩
    simp [hEq, cycle_distinct hc ((by decide : ∀ i : ZMod 5, i + 1 ≠ i - 1) i)]
  have hle := Finset.card_le_card_of_injOn f hmaps hinj
  rw [← hSc]
  simpa only [T, Finset.card_union_of_disjoint hDis, hTwo] using hle

private lemma cycle5_l_le (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : C4Free G) (hp : SimpleGraph.path G ≤ 5) {c : ZMod 5 → α}
    (hc : Cycle G c) (hNC6 : ¬ ∃ d : ZMod 6 → α, Cycle G d) : SimpleGraph.l G ≤ 3 := by
  classical
  let : Nonempty α := hconn.nonempty
  let C : Finset α := Finset.univ.image c
  let I := Finset.univ \ C
  have hC (x : α) : x ∈ C ↔ ∃ i, x = c i := by simp [C, eq_comm]
  have hI (x : α) : x ∈ I ↔ x ∉ C := by simp [I]
  have hchoose : ∀ x, ∃ p, x ∈ I → p ∈ C ∧ G.Adj x p := by
    intro x
    by_cases hx : x ∈ I
    · obtain ⟨i, hi⟩ := cycle5_all_touch G hconn hC4 hp hc x
        (fun i he => (hI x).1 hx ((hC x).2 ⟨i, he⟩))
      exact ⟨c i, fun _ => ⟨(hC (c i)).2 ⟨i, rfl⟩, hi⟩⟩
    · exact ⟨c 0, fun hh => (hx hh).elim⟩
  choose p hp' using hchoose
  have dis : Disjoint C I := Finset.disjoint_left.mpr fun x hxc hxi => (hI x).1 hxi hxc
  have cover : C ∪ I = Finset.univ := by ext x; simp [hI, em]
  have cardC : C.card = 5 := by
    rw [Finset.card_image_of_injective _ hc.1, Finset.card_univ, ZMod.card]
  have hcard : C.card + I.card = Fintype.card α := by
    have h := congrArg Finset.card cover
    rwa [Finset.card_union_of_disjoint dis, Finset.card_univ] at h
  have hsumC : (∑ x ∈ C, indepNeighborsCard G x) ≤ 2 * C.card + I.card := by
    have h := Finset.sum_le_sum (fun x hx => cycle5_cycle_bound G hC4 hc C I hC hI p hp' x hx)
    have hcount := Finset.card_eq_sum_card_fiberwise (f := p) (s := I) (t := C)
      (fun x hx => (hp' x hx).1)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hcount] at h
    simpa [Nat.mul_comm] using h
  have hsumI : (∑ x ∈ I, indepNeighborsCard G x) ≤ 2 * I.card := by
    calc _ ≤ ∑ _ ∈ I, 2 := Finset.sum_le_sum (fun x hx => cycle5_outside_bound G hconn hC4 hp hc hNC6
          (fun i he => (hI x).1 hx ((hC x).2 ⟨i, he⟩)))
      _ = _ := by simp [Nat.mul_comm]
  apply l_le_of_sum G 3
  rw [← cover, Finset.sum_union dis]
  omega

/- The gap-two argument below is adapted from the merged proof by @jagong-cmu.
The prerequisite geodesic and escape lemmas are from the same author's reduction. -/
lemma add_two_le_path (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v z c : α) (f : ℕ → α) (hf0 : f 0 = v)
    (hd : ∀ i, i ≤ G.dist v z → G.dist v (f i) = i)
    (ha : ∀ i, i < G.dist v z → G.Adj (f i) (f (i + 1)))
    (hd1 : 1 ≤ G.dist v z) (hvc : G.Adj v c) (hc1 : c ≠ f 1) (hcn : ¬ G.Adj c (f 1)) :
    G.dist v z + 2 ≤ SimpleGraph.path G := by
  set d := G.dist v z with hdd
  have hdc : G.dist v c = 1 := dist_eq_one_iff_adj.mpr hvc
  -- `c` is not on the geodesic
  have hcf : ∀ j, j ≤ d → c ≠ f j := by
    intro j hj hcj
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j
      · rw [hf0] at hcj
        exact G.ne_of_adj hvc hcj.symm
      · exact hc1 hcj
    · have := hd j hj
      rw [← hcj, hdc] at this
      omega
  -- adjacency of `c` with the geodesic
  have hcadj : ∀ j, j ≤ d → (G.Adj c (f j) ↔ j = 0) := by
    intro j hj
    constructor
    · intro h
      by_contra hj0
      have hle := dist_le_of_adj G hconn (v := v) h
      rw [hdc, hd j hj] at hle
      have hj1 : 1 ≤ j := by omega
      interval_cases j
      · exact hcn h
      · apply hC4
        refine ⟨v, c, f 2, f 1, ?_, ?_, ?_, ?_, ?_, ?_, hvc, h, (ha 1 (by omega)).symm, ?_⟩
        · exact G.ne_of_adj hvc
        · intro h'
          have := hd 2 hj
          rw [← h', SimpleGraph.dist_self] at this
          omega
        · intro h'
          have := hd 1 (by omega)
          rw [← h', SimpleGraph.dist_self] at this
          omega
        · exact hcf 2 hj
        · exact hc1
        · intro h'
          have h2 := hd 2 hj
          rw [h', hd 1 (by omega)] at h2
          omega
        · have := ha 0 (by omega)
          rw [hf0] at this
          exact this.symm
    · rintro rfl
      rw [hf0]
      exact hvc.symm
  let g : ℕ → α := fun i => match i with
    | 0 => c
    | k + 1 => f k
  have hg0 : g 0 = c := rfl
  have hgs : ∀ k, g (k + 1) = f k := fun k => rfl
  have key := le_path_of_fun G g (d + 2) ?_ ?_
  · exact key
  · intro i j hi hj hij
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · rw [hg0, hgs] at hij
      exact absurd hij (hcf j (by omega))
    · rw [hg0, hgs] at hij
      exact absurd hij.symm (hcf i (by omega))
    · rw [hgs, hgs] at hij
      have h1 := hd i (by omega)
      rw [hij, hd j (by omega)] at h1
      omega
  · intro i j hi hj
    rcases i with _ | i <;> rcases j with _ | j
    · rw [hg0]
      simp
    · rw [hg0, hgs, hcadj j (by omega)]
      omega
    · rw [hg0, hgs, G.adj_comm, hcadj i (by omega)]
      omega
    · rw [hgs, hgs, geodesic_iff G hconn v d f hd ha i j (by omega) (by omega)]
      omega

lemma exists_escape (G : SimpleGraph α)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v u : α) (hvu : G.Adj v u) (h2 : 2 ≤ indepNeighborsCard G v) :
    ∃ c, G.Adj v c ∧ c ≠ u ∧ ¬ G.Adj c u := by
  obtain ⟨S, hS, hI, hc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hnab : ¬ G.Adj a b := hI ha hb hab
  by_cases hau : a = u
  · subst hau
    exact ⟨b, hS b hb, fun h => hab h.symm, fun h => hnab h.symm⟩
  by_cases hadj : G.Adj a u
  · refine ⟨b, hS b hb, ?_, ?_⟩
    · rintro rfl
      exact hnab hadj
    · intro hbu
      apply hC4
      refine ⟨v, a, u, b, G.ne_of_adj (hS a ha), G.ne_of_adj hvu, G.ne_of_adj (hS b hb),
        hau, hab, ?_, hS a ha, hadj, hbu.symm, (hS b hb).symm⟩
      rintro rfl
      exact hnab hadj
  · exact ⟨a, hS a ha, hau, hadj⟩

namespace GapTwo

omit [Fintype α] [DecidableEq α] in
lemma exists_parent (G : SimpleGraph α) (hconn : G.Connected) (c x : α) (hx : x ≠ c) :
    ∃ p, G.Adj p x ∧ G.dist c p + 1 = G.dist c x := by
  obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist x c
  cases w with
  | nil => exact absurd rfl hx
  | @cons _ u _ h q =>
    refine ⟨u, h.symm, ?_⟩
    have h1 := dist_le q
    have h3 : G.dist c x ≤ G.dist c u + 1 := dist_le_of_adj G hconn (v := c) h.symm
    rw [Walk.length_cons] at hw
    rw [dist_comm (u := x)] at hw
    rw [dist_comm (u := c) (v := u)]
    rw [dist_comm (u := c) (v := u)] at h3
    omega

/-- Local bound at a non-root vertex. -/
lemma indep_le_one_add (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hconn : G.Connected) (c x : α) (hx : x ≠ c)
    (hU : ∀ x, x ≠ c → ∀ p q, G.Adj p x → G.Adj q x → G.dist c p + 1 = G.dist c x →
      G.dist c q + 1 = G.dist c x → p = q)
    (hS : ∀ x y p, G.Adj x y → G.dist c x = G.dist c y → G.Adj p x →
      G.dist c p + 1 = G.dist c x → G.Adj p y) :
    indepNeighborsCard G x ≤
      1 + (Finset.univ.filter (fun y => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card := by
  obtain ⟨S, hSadj, hSI, hSc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G x
  obtain ⟨p, hpx, hpd⟩ := exists_parent G hconn c x hx
  rw [← hSc]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun y => G.dist c y = G.dist c x + 1)
  have hup : (S.filter (fun y => G.dist c y = G.dist c x + 1)).card ≤
      (Finset.univ.filter (fun y => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨hSadj y hy.1, hy.2⟩
  have key : ∀ y, G.Adj x y → ¬ G.dist c y = G.dist c x + 1 → y = p ∨ G.Adj p y := by
    intro y hy hny
    have h1 := dist_le_of_adj G hconn (v := c) hy
    have h2 := dist_le_of_adj G hconn (v := c) hy.symm
    rcases (by omega : G.dist c y + 1 = G.dist c x ∨ G.dist c y = G.dist c x) with h | h
    · left
      exact hU x hx y p hy.symm hpx h hpd
    · right
      exact hS x y p hy h.symm hpx hpd
  have hrest : (S.filter (fun y => ¬ G.dist c y = G.dist c x + 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro s hs t ht
    simp only [Finset.mem_filter] at hs ht
    by_contra hst
    rcases key s (hSadj s hs.1) hs.2 with rfl | hps <;>
      rcases key t (hSadj t ht.1) ht.2 with rfl | hpt
    · exact hst rfl
    · exact hSI hs.1 ht.1 hst hpt
    · exact hSI hs.1 ht.1 hst hps.symm
    · exact hst (unique_common G hC4 (hSadj s hs.1) hps.symm (hSadj t ht.1) hpt.symm
        (G.ne_of_adj hpx).symm)
  omega

/-- The counting lemma. -/
lemma sum_indep_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hconn : G.Connected) (c : α)
    (hU : ∀ x, x ≠ c → ∀ p q, G.Adj p x → G.Adj q x → G.dist c p + 1 = G.dist c x →
      G.dist c q + 1 = G.dist c x → p = q)
    (hS : ∀ x y p, G.Adj x y → G.dist c x = G.dist c y → G.Adj p x →
      G.dist c p + 1 = G.dist c x → G.Adj p y) :
    ∑ x, indepNeighborsCard G x + 2 ≤ 2 * Fintype.card α := by
  set ch : α → ℕ := fun x =>
    (Finset.univ.filter (fun y => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card with hch
  have hloc : ∀ x, indepNeighborsCard G x ≤ ch x + (if x = c then 0 else 1) := by
    intro x
    by_cases hx : x = c
    · subst hx
      simp only [if_true, add_zero, hch]
      obtain ⟨S, hSadj, -, hSc⟩ :=
        OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G x
      rw [← hSc]
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.dist_self, zero_add]
      exact ⟨hSadj y hy, dist_eq_one_iff_adj.mpr (hSadj y hy)⟩
    · simp only [hx, if_false]
      have := indep_le_one_add G hC4 hconn c x hx hU hS
      simp only [hch]
      omega
  have hsum_ch : ∑ x, ch x + 1 = Fintype.card α := by
    have h1 : ∑ x, ch x = ∑ y, (Finset.univ.filter
        (fun x => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card := by
      simp only [hch, Finset.card_filter]
      exact Finset.sum_comm
    have h2 : ∀ y, (Finset.univ.filter
        (fun x => G.Adj x y ∧ G.dist c y = G.dist c x + 1)).card = if y = c then 0 else 1 := by
      intro y
      by_cases hy : y = c
      · subst hy
        simp only [if_true, SimpleGraph.dist_self]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ h
        omega
      · simp only [hy, if_false]
        obtain ⟨p, hpy, hpd⟩ := exists_parent G hconn c y hy
        rw [Finset.card_eq_one]
        refine ⟨p, ?_⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hxy, hxd⟩
          exact hU y hy x p hxy hpy hxd.symm hpd
        · rintro rfl
          exact ⟨hpy, hpd.symm⟩
    rw [h1, Finset.sum_congr rfl (fun y _ => h2 y)]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) (fun y => y = c)
    rw [Finset.filter_eq' Finset.univ c] at this
    simp only [Finset.mem_univ, if_true, Finset.card_singleton, Finset.card_univ] at this
    omega
  calc ∑ x, indepNeighborsCard G x + 2
      ≤ ∑ x, (ch x + (if x = c then 0 else 1)) + 2 := by
        have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hloc x)
        omega
    _ = ∑ x, ch x + ∑ x : α, (if x = c then 0 else 1) + 2 := by rw [Finset.sum_add_distrib]
    _ ≤ 2 * Fintype.card α := by
        have : ∑ x : α, (if x = c then 0 else 1) + 1 = Fintype.card α := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
            mul_one]
          have := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset α)) (fun y => y = c)
          rw [Finset.filter_eq' Finset.univ c] at this
          simp only [Finset.mem_univ, if_true, Finset.card_singleton, Finset.card_univ] at this
          omega
        omega


/-- Five vertices forming an induced path give `path ≥ 5`. -/
lemma path5 (G : SimpleGraph α) (a b c d e : α)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d) (nae : ¬ G.Adj a e) (nbd : ¬ G.Adj b d)
    (nbe : ¬ G.Adj b e) (nce : ¬ G.Adj c e)
    (dac : a ≠ c) (dad : a ≠ d) (dae : a ≠ e) (dbd : b ≠ d) (dbe : b ≠ e) (dce : c ≠ e) :
    5 ≤ SimpleGraph.path G := by
  have dab := G.ne_of_adj hab
  have dbc := G.ne_of_adj hbc
  have dcd := G.ne_of_adj hcd
  have dde := G.ne_of_adj hde
  let f : ℕ → α := fun i => match i with
    | 0 => a | 1 => b | 2 => c | 3 => d | _ => e
  have nca : ¬ G.Adj c a := fun h => nac h.symm
  have nda : ¬ G.Adj d a := fun h => nad h.symm
  have nea : ¬ G.Adj e a := fun h => nae h.symm
  have ndb : ¬ G.Adj d b := fun h => nbd h.symm
  have neb : ¬ G.Adj e b := fun h => nbe h.symm
  have nec : ¬ G.Adj e c := fun h => nce h.symm
  apply le_path_of_fun G f 5
  · intro i j hi hj h
    interval_cases i <;> interval_cases j <;> first
      | rfl
      | (exfalso; simp only [f] at h; first
          | exact dab h | exact dac h | exact dad h | exact dae h | exact dbc h
          | exact dbd h | exact dbe h | exact dcd h | exact dce h | exact dde h
          | exact dab h.symm | exact dac h.symm | exact dad h.symm | exact dae h.symm
          | exact dbc h.symm | exact dbd h.symm | exact dbe h.symm | exact dcd h.symm
          | exact dce h.symm | exact dde h.symm)
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      simp [f, hab, hbc, hcd, hde, hab.symm, hbc.symm, hcd.symm, hde.symm, nac, nad, nae, nbd,
        nbe, nce, nca, nda, nea, ndb, neb, nec]

/-- An induced 5-cycle. -/
private def IC5 (G : SimpleGraph α) (u0 u1 u2 u3 u4 : α) : Prop :=
  G.Adj u0 u1 ∧ G.Adj u1 u2 ∧ G.Adj u2 u3 ∧ G.Adj u3 u4 ∧ G.Adj u4 u0 ∧
    ¬ G.Adj u0 u2 ∧ ¬ G.Adj u0 u3 ∧ ¬ G.Adj u1 u3 ∧ ¬ G.Adj u1 u4 ∧ ¬ G.Adj u2 u4

omit [Fintype α] [DecidableEq α] in
lemma IC5.rot {G : SimpleGraph α} {u0 u1 u2 u3 u4 : α} (h : IC5 G u0 u1 u2 u3 u4) :
    IC5 G u1 u2 u3 u4 u0 := by
  obtain ⟨h1, h2, h3, h4, h5, n1, n2, n3, n4, n5⟩ := h
  exact ⟨h2, h3, h4, h5, h1, n3, n4, n5, fun h => n1 h.symm, fun h => n2 h.symm⟩

omit [Fintype α] [DecidableEq α] in
lemma IC5.distinct {G : SimpleGraph α} {u0 u1 u2 u3 u4 : α} (h : IC5 G u0 u1 u2 u3 u4) :
    u0 ≠ u2 ∧ u0 ≠ u3 := by
  obtain ⟨h1, h2, h3, h4, h5, n1, n2, n3, n4, n5⟩ := h
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact n2 h3
  · rintro rfl
    exact n1 h3.symm

/-- A vertex outside an induced 5-cycle adjacent to `u0` gives an induced path on 5 vertices. -/
lemma path5_of_IC5 (G : SimpleGraph α)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {u0 u1 u2 u3 u4 w : α} (h : IC5 G u0 u1 u2 u3 u4)
    (w0 : w ≠ u0) (w1 : w ≠ u1) (w2 : w ≠ u2) (w3 : w ≠ u3) (w4 : w ≠ u4)
    (hw : G.Adj w u0) : 5 ≤ SimpleGraph.path G := by
  have hd := h.distinct
  have hd1 := h.rot.distinct
  have hd2 := h.rot.rot.distinct
  have hd3 := h.rot.rot.rot.distinct
  have hd4 := h.rot.rot.rot.rot.distinct
  obtain ⟨h1, h2, h3, h4, h5, n1, n2, n3, n4, n5⟩ := h
  have nw2 : ¬ G.Adj w u2 := fun hw2 => hC4 ⟨w, u0, u1, u2, w0, w1, w2, G.ne_of_adj h1,
    hd.1, G.ne_of_adj h2, hw, h1, h2, hw2.symm⟩
  have nw3 : ¬ G.Adj w u3 := fun hw3 => hC4 ⟨w, u0, u4, u3, w0, w4, w3, (G.ne_of_adj h5).symm,
    hd.2, (G.ne_of_adj h4).symm, hw, h5.symm, h4.symm, hw3.symm⟩
  by_cases hw1 : G.Adj w u1
  · have nw4 : ¬ G.Adj w u4 := fun hw4 => hC4 ⟨w, u1, u0, u4, w1, w0, w4,
      (G.ne_of_adj h1).symm, hd1.2, G.ne_of_adj h5.symm, hw1, h1.symm, h5.symm, hw4.symm⟩
    exact path5 G w u0 u4 u3 u2 hw h5.symm h4.symm h3.symm nw4 nw3 nw2 n2 n1
      (fun h => n5 h.symm) w4 w3 w2 hd.2 hd.1 hd2.1.symm
  · exact path5 G w u0 u1 u2 u3 hw h1 h2 h3 hw1 nw2 nw3 n1 n2 n3 w1 w2 w3 hd.1 hd.2 hd1.1

/-- With a vertex whose neighbourhood has three independent vertices, a connected C4-free graph
containing an induced 5-cycle has an induced path on 5 vertices. -/
lemma path5_of_IC5' (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {u0 u1 u2 u3 u4 : α} (h : IC5 G u0 u1 u2 u3 u4)
    (hv : ∃ v : α, 3 ≤ indepNeighborsCard G v) : 5 ≤ SimpleGraph.path G := by
  classical
  let T : Finset α := {u0, u1, u2, u3, u4}
  by_cases hall : ∀ z, z ∈ T
  · exfalso
    obtain ⟨v, hv⟩ := hv
    obtain ⟨S, -, hSI, hSc⟩ :=
      OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < S.card)
    have nab : ¬ G.Adj a b := hSI ha hb hab
    have nac : ¬ G.Adj a c := hSI ha hc hac
    have nbc : ¬ G.Adj b c := hSI hb hc hbc
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
    have ma := hall a
    have mb := hall b
    have mc := hall c
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ma mb mc
    rcases ma with rfl | rfl | rfl | rfl | rfl <;> rcases mb with rfl | rfl | rfl | rfl | rfl <;>
      rcases mc with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact hab rfl | exact hac rfl | exact hbc rfl
        | exact nab h1 | exact nab h2 | exact nab h3 | exact nab h4 | exact nab h5
        | exact nab h1.symm | exact nab h2.symm | exact nab h3.symm | exact nab h4.symm
        | exact nab h5.symm
        | exact nac h1 | exact nac h2 | exact nac h3 | exact nac h4 | exact nac h5
        | exact nac h1.symm | exact nac h2.symm | exact nac h3.symm | exact nac h4.symm
        | exact nac h5.symm
        | exact nbc h1 | exact nbc h2 | exact nbc h3 | exact nbc h4 | exact nbc h5
        | exact nbc h1.symm | exact nbc h2.symm | exact nbc h3.symm | exact nbc h4.symm
        | exact nbc h5.symm
  · push Not at hall
    obtain ⟨z, hz⟩ := hall
    have hu0 : u0 ∈ (T : Set α) := by simp [T]
    obtain ⟨d, -, hd1, hd2⟩ := (hconn u0 z).some.exists_boundary_dart (T : Set α) hu0 hz
    have hadj := d.adj
    set x := d.fst
    set w := d.snd
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hd1 hd2
    obtain ⟨w0, w1, w2, w3, w4⟩ := hd2
    rcases hd1 with hx | hx | hx | hx | hx <;> rw [hx] at hadj
    · exact path5_of_IC5 G hC4 h w0 w1 w2 w3 w4 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot w1 w2 w3 w4 w0 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot.rot w2 w3 w4 w0 w1 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot.rot.rot w3 w4 w0 w1 w2 hadj.symm
    · exact path5_of_IC5 G hC4 h.rot.rot.rot.rot w4 w0 w1 w2 w3 hadj.symm

/-- The gap-2 bound when the radius is at most 2. -/
theorem small_radius {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hP : SimpleGraph.path G = G.radius.toNat + 2)
    (hv : ∃ v : α, 3 ≤ indepNeighborsCard G v)
    (hr : G.radius.toNat ≤ 2) : SimpleGraph.l G ≤ 2 := by
  classical
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  have hrtop : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hconn
  have hecc : ∀ y, G.dist c y ≤ 2 := by
    intro y
    have hle : G.edist c y ≤ G.radius := hc ▸ edist_le_eccent
    have := ENat.toNat_le_toNat hle hrtop
    exact le_trans this hr
  have hd0 : ∀ y, G.dist c y = 0 → y = c := fun y h => ((hconn.dist_eq_zero_iff).mp h).symm
  have hd1 : ∀ y, G.dist c y = 1 → G.Adj c y := fun y h => dist_eq_one_iff_adj.mp h
  have hU : ∀ x, x ≠ c → ∀ p q, G.Adj p x → G.Adj q x → G.dist c p + 1 = G.dist c x →
      G.dist c q + 1 = G.dist c x → p = q := by
    intro x hx p q hp hq hpd hqd
    have h2 := hecc x
    rcases (by omega : G.dist c x = 1 ∨ G.dist c x = 2) with h | h
    · rw [hd0 p (by omega), hd0 q (by omega)]
    · exact unique_common G hC4 (hd1 p (by omega)) hp (hd1 q (by omega)) hq (Ne.symm hx)
  have hS : ∀ x y p, G.Adj x y → G.dist c x = G.dist c y → G.Adj p x →
      G.dist c p + 1 = G.dist c x → G.Adj p y := by
    intro x y p hxy hd hpx hpd
    have h2 := hecc x
    rcases (by omega : G.dist c x = 1 ∨ G.dist c x = 2) with h | h
    · rw [hd0 p (by omega)]
      exact hd1 y (by omega)
    · have hyc : y ≠ c := by
        rintro rfl
        rw [SimpleGraph.dist_self] at hd
        omega
      have hxc : x ≠ c := by
        rintro rfl
        rw [SimpleGraph.dist_self] at h
        omega
      obtain ⟨q, hqy, hqd⟩ := exists_parent G hconn c y hyc
      by_cases hpq : p = q
      · rw [hpq]
        exact hqy
      exfalso
      have hcp := hd1 p (by omega)
      have hcq := hd1 q (by omega)
      have ncx : ¬ G.Adj c x := fun hh => by
        have := dist_eq_one_iff_adj.mpr hh
        omega
      have ncy : ¬ G.Adj c y := fun hh => by
        have := dist_eq_one_iff_adj.mpr hh
        omega
      have npy : ¬ G.Adj p y := fun hh => hpq (hU y hyc p q hh hqy (by omega) hqd)
      have nqx : ¬ G.Adj x q := fun hh => hpq (hU x hxc q p hh.symm hpx (by omega) hpd).symm
      have npq : ¬ G.Adj p q := by
        intro hh
        apply hC4
        refine ⟨p, x, y, q, G.ne_of_adj hpx, ?_, hpq, G.ne_of_adj hxy, ?_, G.ne_of_adj hqy.symm,
          hpx, hxy, hqy.symm, hh.symm⟩
        · rintro rfl
          omega
        · rintro rfl
          omega
      have hic : IC5 G c p x y q := ⟨hcp, hpx, hxy, hqy.symm, hcq.symm, ncx, ncy, npy, npq, nqx⟩
      have := path5_of_IC5' G hconn hC4 hic hv
      omega
  have hsum := sum_indep_le G hC4 hconn c hU hS
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  unfold SimpleGraph.l averageIndepNeighbors indepNeighbors
  rw [div_le_iff₀ hn]
  have : (∑ x, (indepNeighborsCard G x : ℝ)) + 2 ≤ 2 * Fintype.card α := by exact_mod_cast hsum
  linarith

omit [Fintype α] [DecidableEq α] in
lemma nadj_of_dist (G : SimpleGraph α) (hconn : G.Connected) (v : α) {x y : α}
    (h : G.dist v x + 2 ≤ G.dist v y) : ¬ G.Adj x y := by
  intro hxy
  have := dist_le_of_adj G hconn (v := v) hxy
  omega

omit [Fintype α] [DecidableEq α] in
lemma ne_of_dist (G : SimpleGraph α) (v : α) {x y : α}
    (h : G.dist v x ≠ G.dist v y) : x ≠ y := by
  rintro rfl
  exact h rfl

omit [Fintype α] [DecidableEq α] in
lemma exists_free (G : SimpleGraph α)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (v u w a1 a2 a3 : α) (hu : G.Adj v u) (hw : G.Adj v w)
    (h1 : G.Adj v a1) (h2 : G.Adj v a2) (h3 : G.Adj v a3)
    (d12 : a1 ≠ a2) (d13 : a1 ≠ a3) (d23 : a2 ≠ a3)
    (n12 : ¬ G.Adj a1 a2) (n13 : ¬ G.Adj a1 a3) (n23 : ¬ G.Adj a2 a3) :
    ∃ b, G.Adj v b ∧ b ≠ u ∧ ¬ G.Adj b u ∧ b ≠ w ∧ ¬ G.Adj b w := by
  -- two distinct independent neighbours of `v` cannot both lie in `N[x]` for a neighbour `x`
  have two : ∀ x a b, G.Adj v x → G.Adj v a → G.Adj v b → a ≠ b → ¬ G.Adj a b →
      (a = x ∨ G.Adj a x) → (b = x ∨ G.Adj b x) → False := by
    intro x a b hx ha hb hab nab hax hbx
    rcases hax with rfl | hax <;> rcases hbx with rfl | hbx
    · exact hab rfl
    · exact nab hbx.symm
    · exact nab hax
    · exact hab (unique_common G hC4 ha hax hb hbx (G.ne_of_adj hx))
  by_cases b1 : (a1 = u ∨ G.Adj a1 u) ∨ (a1 = w ∨ G.Adj a1 w)
  · by_cases b2 : (a2 = u ∨ G.Adj a2 u) ∨ (a2 = w ∨ G.Adj a2 w)
    · by_cases b3 : (a3 = u ∨ G.Adj a3 u) ∨ (a3 = w ∨ G.Adj a3 w)
      · exfalso
        rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2 <;> rcases b3 with b3 | b3
        · exact two u a1 a2 hu h1 h2 d12 n12 b1 b2
        · exact two u a1 a2 hu h1 h2 d12 n12 b1 b2
        · exact two u a1 a3 hu h1 h3 d13 n13 b1 b3
        · exact two w a2 a3 hw h2 h3 d23 n23 b2 b3
        · exact two u a2 a3 hu h2 h3 d23 n23 b2 b3
        · exact two w a1 a3 hw h1 h3 d13 n13 b1 b3
        · exact two w a1 a2 hw h1 h2 d12 n12 b1 b2
        · exact two w a1 a2 hw h1 h2 d12 n12 b1 b2
      · push Not at b3
        exact ⟨a3, h3, b3.1.1, b3.1.2, b3.2.1, b3.2.2⟩
    · push Not at b2
      exact ⟨a2, h2, b2.1.1, b2.1.2, b2.2.1, b2.2.2⟩
  · push Not at b1
    exact ⟨a1, h1, b1.1.1, b1.1.2, b1.2.1, b1.2.2⟩

theorem large_radius (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (r : ℕ) (hr3 : 3 ≤ r) (v a1 a2 a3 : α)
    (h1 : G.Adj v a1) (h2 : G.Adj v a2) (h3 : G.Adj v a3)
    (d12 : a1 ≠ a2) (d13 : a1 ≠ a3) (d23 : a2 ≠ a3)
    (n12 : ¬ G.Adj a1 a2) (n13 : ¬ G.Adj a1 a3) (n23 : ¬ G.Adj a2 a3)
    (hecc : ∀ x, G.dist v x ≤ r) (z : α) (hz : G.dist v z = r)
    (hcent : ∀ u, ∃ y, r ≤ G.dist u y) : r + 3 ≤ SimpleGraph.path G := by
  obtain ⟨p, hp0, -, hpd, -, hpa⟩ := exists_geodesic2 G hconn v z
  rw [hz] at hpd hpa
  obtain ⟨y, hy⟩ := hcent (p 1)
  obtain ⟨t, ht0, -, htd, hty', hta⟩ := exists_geodesic2 G hconn v y
  set m := G.dist v y with hm
  have hmr : m ≤ r := hecc y
  have hp1d : G.dist v (p 1) = 1 := hpd 1 (by omega)
  have hmr' : r ≤ m + 1 := by
    have e : G.dist (p 1) v = 1 := by rw [dist_comm]; exact hp1d
    have := hconn.dist_triangle (u := p 1) (v := v) (w := y)
    omega
  have key : ∀ b, b ≤ m → r ≤ G.dist (p 1) (t b) + (m - b) := by
    intro b hb
    have := hconn.dist_triangle (u := p 1) (v := t b) (w := y)
    rw [hty' b hb] at this
    omega
  have hpp : ∀ a, 1 ≤ a → a ≤ r → G.dist (p 1) (p a) ≤ a - 1 := by
    intro a ha1 har
    have := dist_chain_le G hconn p r hpa 1 (a - 1) (by omega)
    rwa [show 1 + (a - 1) = a by omega] at this
  have chord : ∀ a b, 1 ≤ a → a ≤ r → b ≤ m → G.Adj (p a) (t b) →
      r + b ≤ a + m ∧ a ≤ b + 1 ∧ b ≤ a + 1 := by
    intro a b ha1 har hbm hadj
    have k := key b hbm
    have c1 := hpp a ha1 har
    have c2 := hconn.dist_triangle (u := p 1) (v := p a) (w := t b)
    rw [dist_eq_one_iff_adj.mpr hadj] at c2
    have l1 := dist_le_of_adj G hconn (v := v) hadj
    have l2 := dist_le_of_adj G hconn (v := v) hadj.symm
    rw [hpd a har, htd b hbm] at l1 l2
    omega
  have hdis : ∀ a b, a ≤ r → 1 ≤ b → b ≤ m → p a ≠ t b := by
    intro a b har hb1 hbm heq
    have e1 := hpd a har
    rw [heq, htd b hbm] at e1
    have k := key b hbm
    have c1 := hpp a (by omega) har
    rw [heq] at c1
    omega
  have hv_t : ∀ b, 2 ≤ b → b ≤ m → ¬ G.Adj v (t b) := by
    intro b hb2 hbm
    exact nadj_of_dist G hconn v (by rw [SimpleGraph.dist_self, htd b hbm]; omega)
  have hvp1 : G.Adj v (p 1) := by
    have := hpa 0 (by omega)
    rwa [hp0] at this
  have hvt1 : G.Adj v (t 1) := by
    have := hta 0 (by omega)
    rwa [ht0] at this
  have ht1d : G.dist v (t 1) = 1 := htd 1 (by omega)
  have hp2d : G.dist v (p 2) = 2 := hpd 2 (by omega)
  have hp3d : G.dist v (p 3) = 3 := hpd 3 (by omega)
  have ht2d : G.dist v (t 2) = 2 := htd 2 (by omega)
  obtain ⟨b, hvb, hb1, nb1, hbt, nbt⟩ :=
    exists_free G hC4 v (p 1) (t 1) a1 a2 a3 hvp1 hvt1 h1 h2 h3 d12 d13 d23 n12 n13 n23
  have hbd : G.dist v b = 1 := dist_eq_one_iff_adj.mpr hvb
  have hv0 : G.dist v v = 0 := SimpleGraph.dist_self
  have e_12 : G.Adj (p 1) (p 2) := hpa 1 (by omega)
  have e_23 : G.Adj (p 2) (p 3) := hpa 2 (by omega)
  have e_bv : G.Adj b v := hvb.symm
  have e_v1 : G.Adj v (p 1) := hvp1
  have q_12 : p 1 ≠ p 2 := G.ne_of_adj e_12
  have q_23 : p 2 ≠ p 3 := G.ne_of_adj e_23
  have q_bv : b ≠ v := (G.ne_of_adj hvb).symm
  have q_v1 : v ≠ p 1 := G.ne_of_adj hvp1
  have q_b1 : b ≠ p 1 := hb1
  have q_b2 : b ≠ p 2 := ne_of_dist G v (by omega)
  have q_b3 : b ≠ p 3 := ne_of_dist G v (by omega)
  have q_v2 : v ≠ p 2 := ne_of_dist G v (by omega)
  have q_v3 : v ≠ p 3 := ne_of_dist G v (by omega)
  have q_13 : p 1 ≠ p 3 := ne_of_dist G v (by omega)
  have n_b1 : ¬ G.Adj b (p 1) := nb1
  have n_b2 : ¬ G.Adj b (p 2) := fun hh => hC4 ⟨v, b, p 2, p 1, q_bv.symm, q_v2, q_v1, q_b2,
    q_b1, q_12.symm, hvb, hh, e_12.symm, hvp1.symm⟩
  have n_b3 : ¬ G.Adj b (p 3) := nadj_of_dist G hconn v (by omega)
  have n_v2 : ¬ G.Adj v (p 2) := nadj_of_dist G hconn v (by omega)
  have n_v3 : ¬ G.Adj v (p 3) := nadj_of_dist G hconn v (by omega)
  have n_13 : ¬ G.Adj (p 1) (p 3) := nadj_of_dist G hconn v (by omega)
  have nbt' : ∀ k, 1 ≤ k → k ≤ m → ¬ G.Adj b (t k) := by
    intro k hk1 hkm hh
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk
    · exact nbt hh
    · have q_t12 : t 1 ≠ t 2 := G.ne_of_adj (hta 1 (by omega))
      exact hC4 ⟨v, b, t 2, t 1, q_bv.symm, ne_of_dist G v (by omega), G.ne_of_adj hvt1,
        ne_of_dist G v (by omega), hbt, q_t12.symm, hvb, hh, (hta 1 (by omega)).symm,
        hvt1.symm⟩
    · exact nadj_of_dist G hconn v (by rw [htd k hkm]; omega) hh
  have nebt : ∀ k, 1 ≤ k → k ≤ m → b ≠ t k := by
    intro k hk1 hkm
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk
    · exact hbt
    · exact ne_of_dist G v (by rw [htd k hkm]; omega)
  have np2t1 : ¬ G.Adj (p 2) (t 1) := fun hh => hC4 ⟨v, p 1, p 2, t 1, q_v1, q_v2,
    G.ne_of_adj hvt1, q_12, hdis 1 1 (by omega) le_rfl (by omega),
    hdis 2 1 (by omega) le_rfl (by omega), hvp1, e_12, hh, hvt1.symm⟩
  rcases (by omega : m + 1 = r ∨ m = r) with hmc | hmc
  · by_cases hc : G.Adj (p 3) (t 2)
    · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | 3 => p 2 | _ => p 3
      have hg := glue G H 5 (by omega) t 2 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · omega
      · intro i hi
        have hi' : i < 4 := by omega
        interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
      · intro i j hj hij
        have hi' : i < 5 := by omega
        interval_cases j <;> interval_cases i <;> try omega
        all_goals simp only [H]
        all_goals first
            | exact ⟨n_b1, q_b1⟩
            | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
            | exact ⟨n_b2, q_b2⟩
            | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
            | exact ⟨n_b3, q_b3⟩
            | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
            | exact ⟨n_v2, q_v2⟩
            | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
            | exact ⟨n_v3, q_v3⟩
            | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
            | exact ⟨n_13, q_13⟩
            | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
      · intro b' h1' h2'
        exact hta b' (by omega)
      · intro a' b' h1' h2' h3'
        exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
          ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
      · simp only [H]
        exact hc
      · intro i b' hi hb1' hb2' hor
        interval_cases i <;> simp only [H]
        · exact nbt' b' (by omega) hb2'
        · exact hv_t b' (by omega) hb2'
        · intro hh
          have cc := chord 1 b' (by omega) (by omega) hb2' hh
          omega
        · intro hh
          have cc := chord 2 b' (by omega) (by omega) hb2' hh
          omega
        · intro hh
          have cc := chord 3 b' (by omega) (by omega) hb2' hh
          omega
      · intro i b' hi hb1' hb2'
        interval_cases i <;> simp only [H]
        · exact nebt b' (by omega) hb2'
        · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
        · exact hdis 1 b' (by omega) (by omega) hb2'
        · exact hdis 2 b' (by omega) (by omega) hb2'
        · exact hdis 3 b' (by omega) (by omega) hb2'
    · let H : ℕ → α := fun i => match i with | 0 => p 3 | 1 => p 2 | 2 => p 1 | _ => v
      have hg := glue G H 4 (by omega) t 1 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · omega
      · intro i hi
        have hi' : i < 3 := by omega
        interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
      · intro i j hj hij
        have hi' : i < 4 := by omega
        interval_cases j <;> interval_cases i <;> try omega
        all_goals simp only [H]
        all_goals first
            | exact ⟨n_b1, q_b1⟩
            | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
            | exact ⟨n_b2, q_b2⟩
            | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
            | exact ⟨n_b3, q_b3⟩
            | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
            | exact ⟨n_v2, q_v2⟩
            | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
            | exact ⟨n_v3, q_v3⟩
            | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
            | exact ⟨n_13, q_13⟩
            | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
      · intro b' h1' h2'
        exact hta b' (by omega)
      · intro a' b' h1' h2' h3'
        exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
          ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
      · simp only [H]
        exact hvt1
      · intro i b' hi hb1' hb2' hor
        interval_cases i <;> simp only [H]
        · intro hh
          have cc := chord 3 b' (by omega) (by omega) hb2' hh
          have : b' = 2 := by omega
          subst this
          exact hc hh
        · intro hh
          have cc := chord 2 b' (by omega) (by omega) hb2' hh
          have : b' = 1 := by omega
          subst this
          exact np2t1 hh
        · intro hh
          have cc := chord 1 b' (by omega) (by omega) hb2' hh
          omega
        · exact hv_t b' (by omega) hb2'
      · intro i b' hi hb1' hb2'
        interval_cases i <;> simp only [H]
        · exact hdis 3 b' (by omega) (by omega) hb2'
        · exact hdis 2 b' (by omega) (by omega) hb2'
        · exact hdis 1 b' (by omega) (by omega) hb2'
        · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
  · by_cases hq : G.Adj (p 1) (t 1)
    · have np2t2 : ¬ G.Adj (p 2) (t 2) := fun hh => hC4 ⟨p 1, p 2, t 2, t 1, q_12,
        hdis 1 2 (by omega) (by omega) (by omega), hdis 1 1 (by omega) le_rfl (by omega),
        hdis 2 2 (by omega) (by omega) (by omega), hdis 2 1 (by omega) le_rfl (by omega),
        ne_of_dist G v (by omega), e_12, hh, (hta 1 (by omega)).symm, hq.symm⟩
      by_cases h33 : G.Adj (p 3) (t 3)
      · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | 3 => p 2 | _ => p 3
        have hg := glue G H 5 (by omega) t 3 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · intro i hi
          have hi' : i < 4 := by omega
          interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
        · intro i j hj hij
          have hi' : i < 5 := by omega
          interval_cases j <;> interval_cases i <;> try omega
          all_goals simp only [H]
          all_goals first
              | exact ⟨n_b1, q_b1⟩
              | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
              | exact ⟨n_b2, q_b2⟩
              | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
              | exact ⟨n_b3, q_b3⟩
              | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
              | exact ⟨n_v2, q_v2⟩
              | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
              | exact ⟨n_v3, q_v3⟩
              | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
              | exact ⟨n_13, q_13⟩
              | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
        · intro b' h1' h2'
          exact hta b' (by omega)
        · intro a' b' h1' h2' h3'
          exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
            ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
        · simp only [H]
          exact h33
        · intro i b' hi hb1' hb2' hor
          interval_cases i <;> simp only [H]
          · exact nbt' b' (by omega) hb2'
          · exact hv_t b' (by omega) hb2'
          · intro hh
            have cc := chord 1 b' (by omega) (by omega) hb2' hh
            omega
          · intro hh
            have cc := chord 2 b' (by omega) (by omega) hb2' hh
            omega
          · intro hh
            have cc := chord 3 b' (by omega) (by omega) hb2' hh
            omega
        · intro i b' hi hb1' hb2'
          interval_cases i <;> simp only [H]
          · exact nebt b' (by omega) hb2'
          · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
          · exact hdis 1 b' (by omega) (by omega) hb2'
          · exact hdis 2 b' (by omega) (by omega) hb2'
          · exact hdis 3 b' (by omega) (by omega) hb2'
      · by_cases h32 : G.Adj (p 3) (t 2)
        · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | 3 => p 2 | _ => p 3
          have hg := glue G H 5 (by omega) t 2 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · omega
          · intro i hi
            have hi' : i < 4 := by omega
            interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
          · intro i j hj hij
            have hi' : i < 5 := by omega
            interval_cases j <;> interval_cases i <;> try omega
            all_goals simp only [H]
            all_goals first
                | exact ⟨n_b1, q_b1⟩
                | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
                | exact ⟨n_b2, q_b2⟩
                | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
                | exact ⟨n_b3, q_b3⟩
                | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
                | exact ⟨n_v2, q_v2⟩
                | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
                | exact ⟨n_v3, q_v3⟩
                | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
                | exact ⟨n_13, q_13⟩
                | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
          · intro b' h1' h2'
            exact hta b' (by omega)
          · intro a' b' h1' h2' h3'
            exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
              ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
          · simp only [H]
            exact h32
          · intro i b' hi hb1' hb2' hor
            interval_cases i <;> simp only [H]
            · exact nbt' b' (by omega) hb2'
            · exact hv_t b' (by omega) hb2'
            · intro hh
              have cc := chord 1 b' (by omega) (by omega) hb2' hh
              omega
            · intro hh
              have cc := chord 2 b' (by omega) (by omega) hb2' hh
              have : b' = 2 := by omega
              subst this
              exact np2t2 hh
            · intro hh
              have cc := chord 3 b' (by omega) (by omega) hb2' hh
              have : b' = 3 := by omega
              subst this
              exact h33 hh
          · intro i b' hi hb1' hb2'
            interval_cases i <;> simp only [H]
            · exact nebt b' (by omega) hb2'
            · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
            · exact hdis 1 b' (by omega) (by omega) hb2'
            · exact hdis 2 b' (by omega) (by omega) hb2'
            · exact hdis 3 b' (by omega) (by omega) hb2'
        · let H : ℕ → α := fun i => match i with | 0 => p 3 | 1 => p 2 | _ => p 1
          have hg := glue G H 3 (by omega) t 1 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · omega
          · intro i hi
            have hi' : i < 2 := by omega
            interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
          · intro i j hj hij
            have hi' : i < 3 := by omega
            interval_cases j <;> interval_cases i <;> try omega
            all_goals simp only [H]
            all_goals first
                | exact ⟨n_b1, q_b1⟩
                | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
                | exact ⟨n_b2, q_b2⟩
                | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
                | exact ⟨n_b3, q_b3⟩
                | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
                | exact ⟨n_v2, q_v2⟩
                | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
                | exact ⟨n_v3, q_v3⟩
                | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
                | exact ⟨n_13, q_13⟩
                | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
          · intro b' h1' h2'
            exact hta b' (by omega)
          · intro a' b' h1' h2' h3'
            exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
              ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
          · simp only [H]
            exact hq
          · intro i b' hi hb1' hb2' hor
            interval_cases i <;> simp only [H]
            · intro hh
              have cc := chord 3 b' (by omega) (by omega) hb2' hh
              rcases (by omega : b' = 2 ∨ b' = 3) with rfl | rfl
              · exact h32 hh
              · exact h33 hh
            · intro hh
              have cc := chord 2 b' (by omega) (by omega) hb2' hh
              rcases (by omega : b' = 1 ∨ b' = 2) with rfl | rfl
              · exact np2t1 hh
              · exact np2t2 hh
            · intro hh
              have cc := chord 1 b' (by omega) (by omega) hb2' hh
              omega
          · intro i b' hi hb1' hb2'
            interval_cases i <;> simp only [H]
            · exact hdis 3 b' (by omega) (by omega) hb2'
            · exact hdis 2 b' (by omega) (by omega) hb2'
            · exact hdis 1 b' (by omega) (by omega) hb2'
    · by_cases h22 : G.Adj (p 2) (t 2)
      · let H : ℕ → α := fun i => match i with | 0 => b | 1 => v | 2 => p 1 | _ => p 2
        have hg := glue G H 4 (by omega) t 2 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · intro i hi
          have hi' : i < 3 := by omega
          interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
        · intro i j hj hij
          have hi' : i < 4 := by omega
          interval_cases j <;> interval_cases i <;> try omega
          all_goals simp only [H]
          all_goals first
              | exact ⟨n_b1, q_b1⟩
              | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
              | exact ⟨n_b2, q_b2⟩
              | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
              | exact ⟨n_b3, q_b3⟩
              | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
              | exact ⟨n_v2, q_v2⟩
              | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
              | exact ⟨n_v3, q_v3⟩
              | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
              | exact ⟨n_13, q_13⟩
              | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
        · intro b' h1' h2'
          exact hta b' (by omega)
        · intro a' b' h1' h2' h3'
          exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
            ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
        · simp only [H]
          exact h22
        · intro i b' hi hb1' hb2' hor
          interval_cases i <;> simp only [H]
          · exact nbt' b' (by omega) hb2'
          · exact hv_t b' (by omega) hb2'
          · intro hh
            have cc := chord 1 b' (by omega) (by omega) hb2' hh
            omega
          · intro hh
            have cc := chord 2 b' (by omega) (by omega) hb2' hh
            omega
        · intro i b' hi hb1' hb2'
          interval_cases i <;> simp only [H]
          · exact nebt b' (by omega) hb2'
          · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)
          · exact hdis 1 b' (by omega) (by omega) hb2'
          · exact hdis 2 b' (by omega) (by omega) hb2'
      · let H : ℕ → α := fun i => match i with | 0 => p 2 | 1 => p 1 | _ => v
        have hg := glue G H 3 (by omega) t 1 m (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · intro i hi
          have hi' : i < 2 := by omega
          interval_cases i <;> simp only [H] <;> first | exact e_bv | exact e_bv.symm | exact e_v1 | exact e_v1.symm | exact e_12 | exact e_12.symm | exact e_23 | exact e_23.symm
        · intro i j hj hij
          have hi' : i < 3 := by omega
          interval_cases j <;> interval_cases i <;> try omega
          all_goals simp only [H]
          all_goals first
              | exact ⟨n_b1, q_b1⟩
              | exact ⟨fun hh => n_b1 hh.symm, fun hh => q_b1 hh.symm⟩
              | exact ⟨n_b2, q_b2⟩
              | exact ⟨fun hh => n_b2 hh.symm, fun hh => q_b2 hh.symm⟩
              | exact ⟨n_b3, q_b3⟩
              | exact ⟨fun hh => n_b3 hh.symm, fun hh => q_b3 hh.symm⟩
              | exact ⟨n_v2, q_v2⟩
              | exact ⟨fun hh => n_v2 hh.symm, fun hh => q_v2 hh.symm⟩
              | exact ⟨n_v3, q_v3⟩
              | exact ⟨fun hh => n_v3 hh.symm, fun hh => q_v3 hh.symm⟩
              | exact ⟨n_13, q_13⟩
              | exact ⟨fun hh => n_13 hh.symm, fun hh => q_13 hh.symm⟩
        · intro b' h1' h2'
          exact hta b' (by omega)
        · intro a' b' h1' h2' h3'
          exact ⟨nadj_of_dist G hconn v (by rw [htd a' (by omega), htd b' (by omega)]; omega),
            ne_of_dist G v (by rw [htd a' (by omega), htd b' (by omega)]; omega)⟩
        · simp only [H]
          exact hvt1
        · intro i b' hi hb1' hb2' hor
          interval_cases i <;> simp only [H]
          · intro hh
            have cc := chord 2 b' (by omega) (by omega) hb2' hh
            rcases (by omega : b' = 1 ∨ b' = 2) with rfl | rfl
            · exact np2t1 hh
            · exact h22 hh
          · intro hh
            have cc := chord 1 b' (by omega) (by omega) hb2' hh
            have : b' = 1 := by omega
            subst this
            exact hq hh
          · exact hv_t b' (by omega) hb2'
        · intro i b' hi hb1' hb2'
          interval_cases i <;> simp only [H]
          · exact hdis 2 b' (by omega) (by omega) hb2'
          · exact hdis 1 b' (by omega) (by omega) hb2'
          · exact ne_of_dist G v (by rw [SimpleGraph.dist_self, htd b' hb2']; omega)

theorem gap2 {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hP : SimpleGraph.path G = G.radius.toNat + 2)
    (hv : ∃ v : α, 3 ≤ indepNeighborsCard G v) : SimpleGraph.l G ≤ 2 := by
  classical
  by_cases hr : G.radius.toNat ≤ 2
  · exact small_radius G hconn hC4 hP hv hr
  exfalso
  set r := G.radius.toNat with hrdef
  have hfar : ∀ v : α, ∃ z, r ≤ G.dist v z := by
    intro v
    obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite v
    refine ⟨z, ?_⟩
    have hle : G.radius ≤ G.edist v z := hz ▸ radius_le_eccent
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v z
    have h2 : G.edist v z ≤ (G.dist v z : ℕ∞) := by
      rw [← hp]
      exact edist_le p
    have := ENat.toNat_le_toNat (le_trans hle h2) (by simp)
    simpa [hrdef] using this
  obtain ⟨v, hv3⟩ := hv
  have hecc : ∀ x, G.dist v x ≤ r := by
    intro x
    by_cases hx : G.dist v x = 0
    · omega
    obtain ⟨f, hf0, hd, ha⟩ := exists_geodesic G hconn v x
    have hv1 : G.Adj v (f 1) := by
      have := ha 0 (by omega)
      rwa [hf0] at this
    obtain ⟨c, hvc, hc1, hcn⟩ := exists_escape G hC4 v (f 1) hv1 (by omega)
    have := add_two_le_path G hconn hC4 v x c f hf0 hd ha (by omega) hvc hc1 hcn
    omega
  obtain ⟨z, hz⟩ := hfar v
  have hz' : G.dist v z = r := le_antisymm (hecc z) hz
  obtain ⟨S, hSadj, hSI, hSc⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < S.card)
  have := large_radius G hconn hC4 r (by omega) v a b c (hSadj a ha) (hSadj b hb) (hSadj c hc)
    hab hac hbc (hSI ha hb hab) (hSI ha hc hac) (hSI hb hc hbc) hecc z hz' hfar
  omega


end GapTwo

omit [Fintype α] [DecidableEq α] in
private lemma cycle5_of_old (G : SimpleGraph α) {a b c d e : α}
    (h : GapTwo.IC5 G a b c d e) : ∃ f : ZMod 5 → α, Cycle G f := by
  have hd0 := h.distinct
  have hd1 := h.rot.distinct
  have hd2 := h.rot.rot.distinct
  obtain ⟨h01,h12,h23,h34,h40,n02,n03,n13,n14,n24⟩ := h
  let l : List α := [a,b,c,d,e]
  have hn : l.Nodup := by
    simp [l, h01.ne, hd0.1, hd0.2, h40.ne.symm, h12.ne, hd1.1, hd1.2, h23.ne, hd2.1, h34.ne]
  let g : ZMod 5 → α := fun i => l[i.val]'(ZMod.val_lt i)
  refine ⟨g, ?_, ?_⟩
  · intro i j h
    exact ZMod.val_injective 5 (hn.getElem_inj_iff.mp h)
  · intro i j
    have hcases : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
    rcases hcases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases hcases j with rfl | rfl | rfl | rfl | rfl
    all_goals
      constructor
      · intro h
        first
          | decide
          | exact (G.irrefl h).elim
          | exact (n02 h).elim | exact (n02 h.symm).elim
          | exact (n03 h).elim | exact (n03 h.symm).elim
          | exact (n13 h).elim | exact (n13 h.symm).elim
          | exact (n14 h).elim | exact (n14 h.symm).elim
          | exact (n24 h).elim | exact (n24 h.symm).elim
      · intro h
        first
          | exact h01 | exact h01.symm | exact h12 | exact h12.symm
          | exact h23 | exact h23.symm | exact h34 | exact h34.symm
          | exact h40 | exact h40.symm
          | exact ((by decide : ¬ _) h).elim

/- Breadth-first counting used in @jagong-cmu's small-radius proof, with the
absence of an induced pentagon isolated from the gap assumption. -/
private lemma sparse_small_radius (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : C4Free G) (hr : G.radius.toNat ≤ 2)
    (hcases : G.radius.toNat ≤ 1 ∨ ¬ ∃ f : ZMod 5 → α, Cycle G f) :
    SimpleGraph.l G ≤ 2 := by
  classical
  let : Nonempty α := hconn.nonempty
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  have hecc (y : α) : G.dist c y ≤ G.radius.toNat := hc ▸ dist_le_toNat_eccent G hconn c y
  have hd0 (y : α) (h : G.dist c y = 0) : y = c := (hconn.dist_eq_zero_iff.mp h).symm
  have hd1 (y : α) (h : G.dist c y = 1) : G.Adj c y := dist_eq_one_iff_adj.mp h
  have hU : ∀ x, x ≠ c → ∀ p q, G.Adj p x → G.Adj q x → G.dist c p + 1 = G.dist c x →
      G.dist c q + 1 = G.dist c x → p = q := by
    intro x hx p q hp hq hpd hqd
    have h2 := hecc x
    rcases (by omega : G.dist c x = 1 ∨ G.dist c x = 2) with h | h
    · rw [hd0 p (by omega), hd0 q (by omega)]
    · exact unique_common G hC4 (hd1 p (by omega)) hp (hd1 q (by omega)) hq hx.symm
  have hS : ∀ x y p, G.Adj x y → G.dist c x = G.dist c y → G.Adj p x →
      G.dist c p + 1 = G.dist c x → G.Adj p y := by
    intro x y p hxy hd hpx hpd
    have h2 := hecc x
    rcases (by omega : G.dist c x = 1 ∨ G.dist c x = 2) with h | h
    · rw [hd0 p (by omega)]
      exact hd1 y (by omega)
    have hNo := hcases.resolve_left (by omega)
    have hyc : y ≠ c := by
      rintro rfl
      rw [dist_self] at hd
      omega
    have hxc : x ≠ c := by
      rintro rfl
      rw [dist_self] at h
      omega
    obtain ⟨q, hqy, hqd⟩ := GapTwo.exists_parent G hconn c y hyc
    by_cases hpq : p = q
    · simpa [hpq] using hqy
    exfalso
    have hcp := hd1 p (by omega)
    have hcq := hd1 q (by omega)
    have ncx : ¬ G.Adj c x := fun hh => by
      have := dist_eq_one_iff_adj.mpr hh
      omega
    have ncy : ¬ G.Adj c y := fun hh => by
      have := dist_eq_one_iff_adj.mpr hh
      omega
    have npy : ¬ G.Adj p y := fun hh => hpq (hU y hyc p q hh hqy (by omega) hqd)
    have nqx : ¬ G.Adj x q := fun hh => hpq (hU x hxc q p hh.symm hpx (by omega) hpd).symm
    have npq : ¬ G.Adj p q := by
      intro hh
      apply hC4
      refine ⟨p, x, y, q, hpx.ne, ?_, hpq, hxy.ne, ?_, hqy.ne.symm, hpx, hxy, hqy.symm, hh.symm⟩
      · rintro rfl
        omega
      · rintro rfl
        omega
    exact hNo (cycle5_of_old G ⟨hcp, hpx, hxy, hqy.symm, hcq.symm, ncx, ncy, npy, npq, nqx⟩)
  have hsum := GapTwo.sum_indep_le G hC4 hconn c hU hS
  apply l_le_of_sum G 2
  omega

/-- The conjectured density bound for graphs of radius at most two with no induced P6. -/
private lemma small_radius_small_path (G : SimpleGraph α) (hconn : G.Connected)
    (hC4 : C4Free G) (hr : G.radius.toNat ≤ 2) (hp : SimpleGraph.path G ≤ 5) :
    SimpleGraph.l G ≤ 3 := by
  classical
  by_cases hC6 : ∃ c : ZMod 6 → α, Cycle G c
  · obtain ⟨c, hc⟩ := hC6
    exact cycle6_l_le G hconn hC4 hp hc
  by_cases hC5 : ∃ c : ZMod 5 → α, Cycle G c
  · obtain ⟨c, hc⟩ := hC5
    exact cycle5_l_le G hconn hC4 hp hc hC6
  exact (sparse_small_radius G hconn hC4 hr (Or.inr hC5)).trans (by norm_num)

private lemma l_le_of_edges [Nonempty α] (G : SimpleGraph α) (k : ℕ)
    (h : 2 * Nat.card G.edgeSet ≤ k * Fintype.card α) : SimpleGraph.l G ≤ k := by
  classical
  apply l_le_of_sum G k
  have h2 : ∑ v, G.degree v = 2 * Nat.card G.edgeSet := by
    rw [sum_degrees_eq_twice_card_edges, edgeFinset_card, Nat.card_eq_fintype_card]
  exact (Finset.sum_le_sum (fun v _ => indep_le_degree G v)).trans (h2.symm ▸ h)

/-- The radius-two case with an induced path on at least six vertices. -/
def H1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    (¬ ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    G.radius.toNat = 2 →
    6 ≤ SimpleGraph.path G →
    (∃ v : α, SimpleGraph.path G < G.radius.toNat + indepNeighborsCard G v) →
    (SimpleGraph.path G - G.radius.toNat) * Fintype.card α < 2 * Nat.card G.edgeSet →
    (G.radius.toNat : ℝ) + SimpleGraph.l G ≤ (SimpleGraph.path G : ℝ)

/-- Radii at least three in the gap-at-least-three regime, with the radius and average restrictions from Chung's bound. -/
def H2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    (¬ ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    3 ≤ G.radius.toNat →
    G.radius.toNat + 3 ≤ SimpleGraph.path G →
    2 * G.radius.toNat - 1 ≤ SimpleGraph.path G →
    ((G.radius.toNat - 1 : ℕ) : ℝ) < SimpleGraph.l G →
    (∃ v : α, SimpleGraph.path G < G.radius.toNat + indepNeighborsCard G v) →
    (SimpleGraph.path G - G.radius.toNat) * Fintype.card α < 2 * Nat.card G.edgeSet →
    (G.radius.toNat : ℝ) + SimpleGraph.l G ≤ (SimpleGraph.path G : ℝ)

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H1 := by
  intro h1 h2 α _ _ _ G hconn hC4
  set r := G.radius.toNat with hr
  set p := SimpleGraph.path G with hp
  have hrtop : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hconn
  have hr1 : 1 ≤ r := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    rcases ENat.toNat_eq_zero.mp hz with he | he
    · exact radius_ne_zero_of_nontrivial he
    · exact hrtop he
  obtain ⟨u⟩ := hconn.nonempty
  have hp1 : r + 1 ≤ p := by
    obtain ⟨w, hw⟩ := exists_far_of_radius G hconn u
    exact (Nat.succ_le_succ hw).trans (add_one_le_path G hconn u w)
  have hg : ((p - r : ℕ) : ℝ) = (p : ℝ) - r := Nat.cast_sub (by omega)
  have finish (h : SimpleGraph.l G ≤ (p - r : ℕ)) :
      (r : ℝ) + SimpleGraph.l G ≤ p := by rw [hg] at h; linarith
  by_cases hsparse : 2 * Nat.card G.edgeSet ≤ (p - r) * Fintype.card α
  · exact finish (l_le_of_edges G (p-r) hsparse)
  by_cases hlarge : ∃ v : α, p < r + indepNeighborsCard G v
  · by_cases h3 : r + 3 ≤ p
    · by_cases hr2 : r ≤ 2
      · by_cases hp5 : p ≤ 5
        · apply finish
          exact (small_radius_small_path G hconn hC4 hr2 hp5).trans (by exact_mod_cast (by omega : 3 ≤ p-r))
        · by_cases hr1' : r ≤ 1
          · apply finish
            exact (sparse_small_radius G hconn hC4 hr2 (Or.inl hr1')).trans
              (by exact_mod_cast (by omega : 2 ≤ p-r))
          · exact h1 G hconn hC4 (by omega) (by omega) hlarge (lt_of_not_ge hsparse)
      · have hchung := twice_radius_sub_one_le G hconn (by omega : 3 ≤ r)
        by_cases hs : SimpleGraph.l G ≤ ((r - 1 : ℕ) : ℝ)
        · exact finish (hs.trans (by exact_mod_cast (by omega : r - 1 ≤ p - r)))
        · exact h2 G hconn hC4 (by omega) h3 hchung (lt_of_not_ge hs) hlarge (lt_of_not_ge hsparse)
    · obtain ⟨v, hv⟩ := hlarge
      have hv2 : 2 ≤ indepNeighborsCard G v := by omega
      obtain ⟨z, hz⟩ := exists_far_of_radius G hconn v
      obtain ⟨f, hf0, hd, ha⟩ := exists_geodesic G hconn v z
      have hv1 : G.Adj v (f 1) := by
        have := ha 0 (by omega)
        rwa [hf0] at this
      obtain ⟨a, hvc, hc1, hcn⟩ := exists_escape G hC4 v (f 1) hv1 hv2
      have h := add_two_le_path G hconn hC4 v z a f hf0 hd ha (by omega) hvc hc1 hcn
      have he : p = r + 2 := by omega
      have hl := GapTwo.gap2 G hconn hC4 he ⟨v, by omega⟩
      exact finish (hl.trans (by exact_mod_cast (by omega : 2 ≤ p-r)))
  · apply finish
    apply l_le_of_sum
    have hall (v : α) : indepNeighborsCard G v ≤ p-r := by
      have hh : ¬ p < r + indepNeighborsCard G v := fun h => hlarge ⟨v, h⟩
      omega
    calc
      (∑ v, indepNeighborsCard G v) ≤ ∑ _v : α, (p-r) :=
        Finset.sum_le_sum fun v _ => hall v
      _ = _ := by simp [Nat.mul_comm]

end OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R2
