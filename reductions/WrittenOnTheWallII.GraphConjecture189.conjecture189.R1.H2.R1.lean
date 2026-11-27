import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-!
# Written on the Wall II, Conjecture 189: the diameter four-to-five step

This file proves the triangle-free case of the step and leaves the graphs with a triangle,
split by diameter.

Triangle-free case. Take a shortest path `u0 u1 u2 u3 u4` between two vertices at distance
four, with `u1` and `u3` of degree at least `σ` (a low middle vertex can be swapped for a common
neighbour, by a count of the even set of the middle vertex). Two steps along any edge pair land
at even distance, so the even set of `u2` contains `N(u1) + u4` and `N(u3) + u0`. Both have at
least `σ + 1` vertices, so both equal the even set `E` of `u2`. Every vertex of `E` has `E` as its
own even set, so `E` is independent, and every other vertex has all its neighbours in `E`. The
neighbourhood condition, applied to each side, makes the sides equal in size. The two ends
`u0, u4` have disjoint neighbourhoods on the odd side, so one of them is a pendant vertex. Every
other odd vertex is then adjacent to all of `E` except the pendant one, and the path runs from the
pendant vertex through its neighbour and then alternates between the two sides.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H2_R1

open SimpleGraph

/-- Diameter four, with a triangle. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → G.diam = 4 →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) →
    G.minDegree + secondSmallestDegree G + 1 < Fintype.card V →
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Diameter five, with a triangle. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → G.diam = 5 →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) →
    (∀ a b, G.dist a b = 5 →
      G.degree a < G.secondSmallestDegree ∨ G.degree b < G.secondSmallestDegree) →
    G.minDegree + secondSmallestDegree G + 1 < Fintype.card V →
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

section TriangleFree

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
/-- In a triangle-free connected graph, a vertex two steps away along an edge pair is at even
distance (zero or two). -/
lemma even_step (hconn : G.Connected) (hT : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) : Even (G.dist x z) := by
  by_cases hxz : x = z
  · subst hxz
    simp
  · have h1 : G.dist x z ≠ 1 := fun h => hT x y z hxy hyz (dist_eq_one_iff_adj.mp h)
    have h0 : G.dist x z ≠ 0 := fun h => hxz ((hconn.dist_eq_zero_iff).mp h)
    have h2 : G.dist x z ≤ 2 := by
      have := hconn.dist_triangle (u := x) (v := y) (w := z)
      rw [dist_eq_one_iff_adj.mpr hxy, dist_eq_one_iff_adj.mpr hyz] at this
      exact this
    have : G.dist x z = 2 := by omega
    rw [this]
    exact ⟨1, rfl⟩

omit [Fintype V] [DecidableEq V] in
lemma exists_pred (hconn : G.Connected) (c x : V) (hx : x ≠ c) :
    ∃ p, G.Adj p x ∧ G.dist c p + 1 = G.dist c x := by
  obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist x c
  cases w with
  | nil => exact absurd rfl hx
  | @cons _ u _ h q =>
    refine ⟨u, h.symm, ?_⟩
    have h1 := dist_le q
    have h3 : G.dist c x ≤ G.dist c u + 1 := by
      have := hconn.dist_triangle (u := c) (v := u) (w := x)
      rw [dist_eq_one_iff_adj.mpr h.symm] at this
      exact this
    have h4 : G.dist x c = G.dist c x := dist_comm
    have h5 : G.dist u c = G.dist c u := dist_comm
    simp only [Walk.length_cons] at hw
    omega

omit [Fintype V] [DecidableEq V] in
lemma dist_le_two_of_adj (hconn : G.Connected) {x y z : V} (hxy : G.Adj x y)
    (hyz : G.Adj y z) : G.dist x z ≤ 2 := by
  have := hconn.dist_triangle (u := x) (v := y) (w := z)
  rw [dist_eq_one_iff_adj.mpr hxy, dist_eq_one_iff_adj.mpr hyz] at this
  exact this

omit [Fintype V] [DecidableEq V] in
lemma pos_degree [Nontrivial V] [Fintype V] [DecidableRel G.Adj] (hconn : G.Connected) (x : V) :
    1 ≤ G.degree x := by
  obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial x
  exact Finset.card_pos.mpr ⟨y, (G.mem_neighborFinset x y).mpr hy⟩

/-- The final assembly: a pendant vertex `w` hanging off `a`, an even side `E` containing `w`
and `c`, and every other odd vertex adjacent to all of `E` except `w`. -/
lemma trace_of_sides [Nontrivial V] [DecidableRel G.Adj] (E : Finset V) (w a c : V)
    (hwa : G.Adj w a) (hac : G.Adj a c) (hw : w ∈ E) (hc : c ∈ E) (hcw : c ≠ w) (ha : a ∉ E)
    (hpend : ∀ x, G.Adj w x → x = a)
    (hodd : ∀ o, o ∉ E → ∀ z, G.Adj o z → z ∈ E)
    (hcard : Eᶜ.card = E.card) (k : ℕ) (hE : E.card ≤ k + 1)
    (hdeg : ∀ x, x ≠ w → k ≤ G.degree x) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  set L := E.erase w with hL
  set R := Eᶜ.erase a with hR
  have haR : a ∈ Eᶜ := Finset.mem_compl.mpr ha
  have hsize : L.card = R.card := by
    rw [hL, hR, Finset.card_erase_of_mem hw, Finset.card_erase_of_mem haR, hcard]
  have hdis : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_compl.mp (Finset.mem_of_mem_erase hx')) (Finset.mem_of_mem_erase hx)
  have hcomp : ∀ x ∈ L, ∀ y ∈ R, G.Adj x y := by
    intro x hx y hy
    have hyE : y ∉ E := Finset.mem_compl.mp (Finset.mem_of_mem_erase hy)
    have hya : y ≠ a := Finset.ne_of_mem_erase hy
    have hyw : y ≠ w := fun h => hyE (h ▸ hw)
    have hsub : G.neighborFinset y ⊆ L := by
      intro z hz
      have hz' := (G.mem_neighborFinset y z).mp hz
      refine Finset.mem_erase.mpr ⟨?_, hodd y hyE z hz'⟩
      rintro rfl
      exact hya (hpend y hz'.symm)
    have hLc : L.card ≤ G.degree y := by
      have := hdeg y hyw
      rw [hL, Finset.card_erase_of_mem hw]
      omega
    have heq : G.neighborFinset y = L :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_neighborFinset_eq_degree]; exact hLc)
    have : x ∈ G.neighborFinset y := heq ▸ hx
    exact ((G.mem_neighborFinset y x).mp this).symm
  have hcL : c ∈ L := Finset.mem_erase.mpr ⟨hcw, hc⟩
  obtain ⟨l, hhead, hnd, hch, hset⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.alternating_chain
      (G := G) L R hsize hdis hcomp c hcL
  have hmem : ∀ x, x ∈ l ↔ x ∈ L ∪ R := by
    intro x
    rw [← hset, List.mem_toFinset]
  have hanl : a ∉ l := by
    rw [hmem]
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact ha (Finset.mem_of_mem_erase h)
    · exact Finset.ne_of_mem_erase h rfl
  have hwnl : w ∉ l := by
    rw [hmem]
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.ne_of_mem_erase h rfl
    · exact (Finset.mem_compl.mp (Finset.mem_of_mem_erase h)) hw
  have hch2 : (w :: a :: l).IsChain G.Adj := by
    refine List.isChain_cons.mpr ⟨?_, List.isChain_cons.mpr ⟨?_, hch⟩⟩
    · intro x hx
      have : x = a := by simpa [eq_comm] using hx
      rw [this]
      exact hwa
    · intro x hx
      have : x = c := by simpa [hhead, eq_comm] using hx
      rw [this]
      exact hac
  have hnd2 : (w :: a :: l).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hanl, hnd⟩⟩
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact G.ne_of_adj hwa h
    · exact hwnl h
  let p := Walk.ofSupport (w :: a :: l) (by simp) hch2
  have hsup : p.support = w :: a :: l := Walk.support_ofSupport _ _
  have hp : p.IsPath := Walk.IsPath.mk' (by rw [hsup]; exact hnd2)
  refine ⟨_, _, p, hp.isHamiltonian_of_mem ?_⟩
  intro x
  rw [hsup]
  by_cases hxw : x = w
  · simp [hxw]
  by_cases hxa : x = a
  · simp [hxa]
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  rw [hmem]
  by_cases hxE : x ∈ E
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxw, hxE⟩)
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxa, Finset.mem_compl.mpr hxE⟩)

/-- The main structure lemma: a distance-four pair whose second and fourth path vertices
have degree at least `σ` forces the bipartite pendant structure. -/
lemma trace_of_four [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hT : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hb : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hall : ∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card)
    (u0 u1 u2 u3 u4 : V) (h01 : G.Adj u0 u1) (h12 : G.Adj u1 u2) (h23 : G.Adj u2 u3)
    (h34 : G.Adj u3 u4) (hd : G.dist u0 u4 = 4)
    (hs1 : secondSmallestDegree G ≤ G.degree u1) (hs3 : secondSmallestDegree G ≤ G.degree u3) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  set s := secondSmallestDegree G with hsdef
  have hEv : ∀ x, (Finset.univ.filter (fun z => Even (G.dist x z))).card ≤ s + 1 := by
    intro x
    have h := hb x
    rw [Nat.add_comm] at h
    convert h using 1
    unfold distEven
    congr 1
  have hd04 : G.dist u4 u0 = 4 := by rw [SimpleGraph.dist_comm]; exact hd
  have tri := fun a b c => hconn.dist_triangle (u := a) (v := b) (w := c)
  have one : ∀ {a b : V}, G.Adj a b → G.dist a b = 1 := fun h => dist_eq_one_iff_adj.mpr h
  -- basic non-adjacencies from the distance four
  have n14 : ¬ G.Adj u1 u4 := by
    intro h
    have := tri u0 u1 u4
    rw [one h01, one h] at this
    omega
  have n03 : ¬ G.Adj u0 u3 := by
    intro h
    have := tri u0 u3 u4
    rw [one h, one h34] at this
    omega
  set E := Finset.univ.filter (fun z => Even (G.dist u2 z)) with hEdef
  have mem_E : ∀ z, z ∈ E ↔ Even (G.dist u2 z) := by
    intro z
    simp [hEdef]
  have S1 : insert u4 (G.neighborFinset u1) ⊆ E := by
    intro z hz
    rw [mem_E]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact even_step hconn hT h23 h34
    · exact even_step hconn hT h12.symm ((G.mem_neighborFinset _ _).mp hz)
  have S3 : insert u0 (G.neighborFinset u3) ⊆ E := by
    intro z hz
    rw [mem_E]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact even_step hconn hT h12.symm h01.symm
    · exact even_step hconn hT h23 ((G.mem_neighborFinset _ _).mp hz)
  have c1 : (insert u4 (G.neighborFinset u1)).card = G.degree u1 + 1 := by
    rw [Finset.card_insert_of_notMem (fun h => n14 ((G.mem_neighborFinset _ _).mp h)),
      card_neighborFinset_eq_degree]
  have c3 : (insert u0 (G.neighborFinset u3)).card = G.degree u3 + 1 := by
    rw [Finset.card_insert_of_notMem (fun h => n03 ((G.mem_neighborFinset _ _).mp h).symm),
      card_neighborFinset_eq_degree]
  have hEc : E.card ≤ s + 1 := hEv u2
  have E1 : insert u4 (G.neighborFinset u1) = E :=
    Finset.eq_of_subset_of_card_le S1 (by rw [c1]; omega)
  have E3 : insert u0 (G.neighborFinset u3) = E :=
    Finset.eq_of_subset_of_card_le S3 (by rw [c3]; omega)
  have hEcard : E.card = s + 1 := by
    have := Finset.card_le_card S1
    rw [c1] at this
    omega
  -- every even vertex sees `E` as its own even set
  have hEe : ∀ e ∈ E, Finset.univ.filter (fun z => Even (G.dist e z)) = E := by
    intro e he
    symm
    apply Finset.eq_of_subset_of_card_le _ (by rw [hEcard]; exact hEv e)
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← E1] at he
    rcases Finset.mem_insert.mp he with rfl | he1
    · rw [← E3] at hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rw [hd04]
        exact ⟨2, rfl⟩
      · exact even_step hconn hT h34.symm ((G.mem_neighborFinset _ _).mp hz)
    · have he1' := (G.mem_neighborFinset _ _).mp he1
      rw [← E1] at hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have he3 : e ∈ insert u0 (G.neighborFinset u3) := by
          rw [E3, ← E1]
          exact Finset.mem_insert_of_mem he1
        rcases Finset.mem_insert.mp he3 with rfl | he3
        · rw [hd]
          exact ⟨2, rfl⟩
        · rw [SimpleGraph.dist_comm]
          exact even_step hconn hT h34.symm ((G.mem_neighborFinset _ _).mp he3)
      · exact even_step hconn hT he1'.symm ((G.mem_neighborFinset _ _).mp hz)
  have hEind : ∀ e ∈ E, ∀ x, G.Adj e x → x ∉ E := by
    intro e he x hx hxE
    rw [← hEe e he] at hxE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxE
    rw [one hx] at hxE
    exact (Nat.not_even_one) hxE
  have hu2 : u2 ∈ E := by
    rw [mem_E, SimpleGraph.dist_self]
    exact ⟨0, rfl⟩
  have hodd : ∀ o, o ∉ E → ∀ z, G.Adj o z → z ∈ E := by
    intro o ho z hz
    have hne : o ≠ u2 := fun h => ho (h ▸ hu2)
    obtain ⟨p, hpo, hpd⟩ := exists_pred hconn u2 o hne
    have hpE : p ∈ E := by
      rw [mem_E]
      rw [mem_E] at ho
      rcases Nat.even_or_odd (G.dist u2 p) with h | h
      · exact h
      · exfalso
        apply ho
        rw [← hpd]
        exact h.add_one
    rw [← hEe p hpE]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact even_step hconn hT hpo hz
  -- the two sides have equal size, by the neighbourhood condition on each side
  have hindE : G.IsIndepSet (E : Set V) := by
    intro x hx y hy _ hxy
    exact hEind x hx y hxy hy
  have hindO : G.IsIndepSet ((Eᶜ : Finset V) : Set V) := by
    intro x hx y hy _ hxy
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hx hy
    exact hy (hodd x hx y hxy)
  have hle1 : E.card ≤ Eᶜ.card := by
    refine (hall E hindE).trans (Finset.card_le_card ?_)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨a, ha, hax⟩ := hx
    exact Finset.mem_compl.mpr (hEind a ha x hax)
  have hle2 : Eᶜ.card ≤ E.card := by
    refine (hall Eᶜ hindO).trans (Finset.card_le_card ?_)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨a, ha, hax⟩ := hx
    exact hodd a (Finset.mem_compl.mp ha) x hax
  have hcard : Eᶜ.card = E.card := le_antisymm hle2 hle1
  -- the two ends of the distance-four pair have disjoint odd neighbourhoods
  have hu0 : u0 ∈ E := S3 (Finset.mem_insert_self _ _)
  have hu4 : u4 ∈ E := S1 (Finset.mem_insert_self _ _)
  have hsum : G.degree u0 + G.degree u4 ≤ s + 1 := by
    have hdisj : Disjoint (G.neighborFinset u0) (G.neighborFinset u4) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have := tri u0 x u4
      rw [one ((G.mem_neighborFinset _ _).mp hx),
        one ((G.mem_neighborFinset _ _).mp hx').symm] at this
      omega
    have hsub : G.neighborFinset u0 ∪ G.neighborFinset u4 ⊆ Eᶜ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_compl.mpr (hEind u0 hu0 x ((G.mem_neighborFinset _ _).mp hx))
      · exact Finset.mem_compl.mpr (hEind u4 hu4 x ((G.mem_neighborFinset _ _).mp hx))
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, card_neighborFinset_eq_degree,
      card_neighborFinset_eq_degree, hcard, hEcard] at this
    exact this
  have hne04 : u0 ≠ u4 := by
    intro h
    rw [h, SimpleGraph.dist_self] at hd
    omega
  have hu1 : u1 ∉ E := hEind u2 hu2 u1 h12.symm
  have hu3 : u3 ∉ E := hEind u2 hu2 u3 h23
  have hne20 : u2 ≠ u0 := by
    intro h
    have := dist_le_two_of_adj hconn h23 h34
    rw [h] at this
    omega
  have hne24 : u2 ≠ u4 := by
    intro h
    have := dist_le_two_of_adj hconn h01 h12
    rw [h] at this
    omega
  -- a pendant end gives every other vertex degree at least `σ`
  have hdeg_of : ∀ w, G.degree w ≤ 1 → ∀ x, x ≠ w → s ≤ G.degree x := by
    intro w hw x hx
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair
      (G := G) x w hx with h | h
    · exact h
    · have := pos_degree hconn x
      omega
  have pend : ∀ w a, G.Adj w a → G.degree w ≤ 1 → ∀ x, G.Adj w x → x = a := by
    intro w a hwa hw x hx
    have hc := Finset.card_le_one.mp
      (show (G.neighborFinset w).card ≤ 1 by rw [card_neighborFinset_eq_degree]; exact hw)
    exact hc x ((G.mem_neighborFinset _ _).mpr hx) a ((G.mem_neighborFinset _ _).mpr hwa)
  rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair
      (G := G) u0 u4 hne04 with h | h
  · have hw4 : G.degree u4 ≤ 1 := by omega
    exact trace_of_sides E u4 u3 u2 h34.symm h23.symm hu4 hu2 hne24 hu3
      (pend u4 u3 h34.symm hw4) hodd hcard s (by omega) (hdeg_of u4 hw4)
  · have hw0 : G.degree u0 ≤ 1 := by omega
    exact trace_of_sides E u0 u1 u2 h01 h12 hu0 hu2 hne20 hu1
      (pend u0 u1 h01 hw0) hodd hcard s (by omega) (hdeg_of u0 hw0)

/-- A low middle vertex of a two-step path can be swapped for a common neighbour of degree at
least `σ`. -/
lemma swap_mid [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hT : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hb : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (u0 u1 u2 : V) (h01 : G.Adj u0 u1) (h12 : G.Adj u1 u2) (hne : u0 ≠ u2)
    (hlow : G.degree u1 < secondSmallestDegree G) :
    ∃ x, G.Adj u0 x ∧ G.Adj x u2 ∧ secondSmallestDegree G ≤ G.degree x := by
  classical
  set s := secondSmallestDegree G with hsdef
  have pair := fun x y h =>
    OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G := G) x y h
  have hd0 : s ≤ G.degree u0 := by
    rcases pair u0 u1 (G.ne_of_adj h01) with h | h
    · exact h
    · omega
  have hd2 : s ≤ G.degree u2 := by
    rcases pair u2 u1 (G.ne_of_adj h12).symm with h | h
    · exact h
    · omega
  have hdeg1 : 2 ≤ G.degree u1 := by
    rw [← card_neighborFinset_eq_degree]
    have hsub : ({u0, u2} : Finset V) ⊆ G.neighborFinset u1 := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (G.mem_neighborFinset _ _).mpr h01.symm
      · rw [Finset.mem_singleton.mp hz]
        exact (G.mem_neighborFinset _ _).mpr h12
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  have hEv : (Finset.univ.filter (fun z => Even (G.dist u1 z))).card ≤ s + 1 := by
    have h := hb u1
    rw [Nat.add_comm] at h
    convert h using 1
    unfold distEven
    congr 1
  have hsub : G.neighborFinset u0 ∪ G.neighborFinset u2 ⊆
      Finset.univ.filter (fun z => Even (G.dist u1 z)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.mp hz with hz | hz
    · exact even_step hconn hT h01.symm ((G.mem_neighborFinset _ _).mp hz)
    · exact even_step hconn hT h12 ((G.mem_neighborFinset _ _).mp hz)
  have hu := Finset.card_le_card hsub
  have hui := Finset.card_union_add_card_inter (G.neighborFinset u0) (G.neighborFinset u2)
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hui
  have hint : 1 < (G.neighborFinset u0 ∩ G.neighborFinset u2).card := by omega
  obtain ⟨x, hx, hxne⟩ := Finset.exists_mem_ne hint u1
  rcases Finset.mem_inter.mp hx with ⟨hx0, hx2⟩
  refine ⟨x, (G.mem_neighborFinset _ _).mp hx0, ((G.mem_neighborFinset _ _).mp hx2).symm, ?_⟩
  rcases pair x u1 hxne with h | h
  · exact h
  · omega

/-- The triangle-free case of the diameter four-to-five step. -/
theorem triangle_free_case [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hdiam : 4 ≤ G.diam)
    (hT : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hb : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hall : ∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  have hlen : 4 ≤ p.length := by omega
  have geo := fun i j (h : i ≤ j) (hj : j ≤ p.length) =>
    OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.geodesic hconn p hp i j h hj
  have adj : ∀ i, i < 4 → G.Adj (p.getVert i) (p.getVert (i + 1)) :=
    fun i hi => p.adj_getVert_succ (by omega)
  have hd : G.dist (p.getVert 0) (p.getVert 4) = 4 := by
    rw [geo 0 4 (by omega) hlen]
  have h02 : p.getVert 0 ≠ p.getVert 2 := by
    intro h
    have := geo 0 2 (by omega) (by omega)
    rw [h, SimpleGraph.dist_self] at this
    omega
  have h24 : p.getVert 2 ≠ p.getVert 4 := by
    intro h
    have := geo 2 4 (by omega) (by omega)
    rw [h, SimpleGraph.dist_self] at this
    omega
  have h13 : p.getVert 1 ≠ p.getVert 3 := by
    intro h
    have := geo 1 3 (by omega) (by omega)
    rw [h, SimpleGraph.dist_self] at this
    omega
  set s := secondSmallestDegree G with hsdef
  have pair := fun x y h =>
    OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G := G) x y h
  by_cases hs1 : s ≤ G.degree (p.getVert 1)
  · by_cases hs3 : s ≤ G.degree (p.getVert 3)
    · exact trace_of_four hconn hT hb hall _ _ _ _ _ (adj 0 (by omega)) (adj 1 (by omega))
        (adj 2 (by omega)) (adj 3 (by omega)) hd hs1 hs3
    · obtain ⟨y, hy4, hy2, hys⟩ := swap_mid hconn hT hb (p.getVert 4) (p.getVert 3)
        (p.getVert 2) (adj 3 (by omega)).symm (adj 2 (by omega)).symm h24.symm (by omega)
      exact trace_of_four hconn hT hb hall _ _ _ _ _ (adj 0 (by omega)) (adj 1 (by omega))
        hy2.symm hy4.symm hd hs1 hys
  · have hs3 : s ≤ G.degree (p.getVert 3) := by
      rcases pair _ _ h13 with h | h
      · exact absurd h hs1
      · exact h
    obtain ⟨x, hx0, hx2, hxs⟩ := swap_mid hconn hT hb (p.getVert 0) (p.getVert 1)
      (p.getVert 2) (adj 0 (by omega)) (adj 1 (by omega)) h02 (by omega)
    exact trace_of_four hconn hT hb hall _ _ _ _ _ hx0 hx2 (adj 2 (by omega))
      (adj 3 (by omega)) hd hxs hs3

end TriangleFree

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.H2 := by
  intro h1 h2 V _ _ _ G _ hc hd4 hd5 h5 hn1 hn2 hb hall
  by_cases tri : ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a
  · rcases (by omega : G.diam = 4 ∨ G.diam = 5) with hd | hd
    · exact h1 G hc hd tri hn1 hn2 hb hall
    · exact h2 G hc hd tri h5 hn1 hn2 hb hall
  · have hT : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c :=
      fun a b c hab hbc hac => tri ⟨a, b, c, hab, hbc, hac.symm⟩
    exact triangle_free_case hc hd4 hT hb hall

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H2_R1
