import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Reducing the diameter-three case of Written on the Wall II #189

Bipartite graphs admit alternating paths from a near-complete bipartite
structure. In a nonbipartite triangle-free graph, an incidence count around
a shortest odd closed walk shows that its cycle is spanning. The residual
graphs contain a triangle. Split the residual cases by whether the minimum
degree is at most two or at least three.

The original conjecture is due to Ermelinda DeLaViña. The order-statistic
lemma is adapted from OMA PR #2971. The list-chain assembly lemma is reused
from the Graph 199 development.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1

open SimpleGraph

namespace IndexedPath
open SimpleGraph

/-- Nonempty path segments can be linked in any order for which consecutive
endpoints are adjacent. The pieces are allowed to consist of a single vertex. -/
theorem flatten_block_chain {V : Type*} {G : SimpleGraph V} (blocks : List (List V))
    (nonempty : ∀ l ∈ blocks, l ≠ [])
    (internal : ∀ l ∈ blocks, l.IsChain G.Adj)
    (links : blocks.IsChain (fun l r =>
      ∀ a ∈ l.getLast?, ∀ b ∈ r.head?, G.Adj a b)) :
    blocks.flatten.IsChain G.Adj := by
  induction blocks with
  | nil => simp
  | cons l rest ih =>
    cases rest with
    | nil => simpa using internal l (by simp)
    | cons r tail =>
      obtain ⟨first, later⟩ := List.isChain_cons_cons.mp links
      apply (internal l (by simp)).append
        (ih (fun s hs => nonempty s (List.mem_cons_of_mem _ hs))
          (fun s hs => internal s (List.mem_cons_of_mem _ hs)) later)
      intro x hx y hy
      rw [List.flatten_cons, List.head?_append_of_ne_nil _ (nonempty r (by simp))] at hy
      exact first x hx y hy


end IndexedPath

/-! For Ermelinda DeLaViña's Written on the Wall II, Graph Conjecture 189. -/
namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- The order-statistic argument from OMA's
`WrittenOnTheWallII.GraphConjecture189.conjecture189.R1` (PR #2971). -/
lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))


omit [Fintype V] [DecidableEq V] in
/-- Parity of a walk is determined by the colors of its endpoints. -/
theorem even_walk_iff {a b : V} (C : G.Coloring (Fin 2)) (p : G.Walk a b) :
    Even p.length ↔ C a = C b := by
  induction p with
  | nil => simp
  | @cons a t b e p ih =>
    have he := C.valid e
    have hac : C a = C b ↔ C t ≠ C b := by
      generalize C a = ca at he ⊢
      generalize C t = ct at he ⊢
      generalize C b = cb
      fin_cases ca <;> fin_cases ct <;> fin_cases cb <;> simp_all
    rw [Walk.length_cons, hac]
    change Even (p.length + 1) ↔ ¬ C t = C b
    rw [← ih]
    simp [Nat.even_add_one]

omit [DecidableEq V] in
/-- The even-distance vertices are precisely the color class of the starting vertex. -/
theorem distEven_eq_card (h : G.Connected) (C : G.Coloring (Fin 2)) (a : V) :
    distEven G a = (Finset.univ.filter (fun b => C b = C a)).card := by
  classical
  unfold distEven
  congr 1
  ext b
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hp, even_walk_iff C p, eq_comm]

omit [DecidableEq V] in
/-- The opposite color class contains the neighborhood, and each color class through
a vertex has size at most one plus the original conjecture's second-smallest degree. -/
theorem color_class_bounds [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (a : V) :
    G.degree a ≤ (Finset.univ.filter (fun b => C b ≠ C a)).card ∧
      (Finset.univ.filter (fun b => C b = C a)).card ≤ 1 + secondSmallestDegree G := by
  constructor
  · rw [SimpleGraph.degree]
    apply Finset.card_le_card
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (C.valid
      (G.mem_neighborFinset a b |>.mp hb)).symm⟩
  · rw [← distEven_eq_card h C a]
    exact (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).trans hσ


omit [DecidableEq V] in
theorem mem_part (C : G.Coloring (Fin 2)) (c : Fin 2) (v : V) :
    v ∈ (Finset.univ.filter (fun x => C x = c)) ↔ C v = c := by simp

omit [DecidableEq V] in
theorem neighborFinset_subset_part [DecidableRel G.Adj]
    (C : G.Coloring (Fin 2)) {c d : Fin 2} (hcd : c ≠ d) {x : V}
    (hx : x ∈ (Finset.univ.filter (fun x => C x = c))) : G.neighborFinset x ⊆ (Finset.univ.filter (fun x => C x = d)) := by
  intro y hy
  rw [mem_part] at hx ⊢
  have ne := C.valid ((G.mem_neighborFinset x y).mp hy)
  rw [hx] at ne
  generalize C y = e at ne ⊢
  fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all

omit [DecidableEq V] in
/-- The conjecture's degree condition forces the sizes of the two parts to differ by
at most one. If they differ, at most one vertex of the larger side misses any cross edge. -/
theorem unbalanced_part_complete_off_one [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hc : ((Finset.univ.filter (fun x => C x = c))).Nonempty)
    (hsize : ((Finset.univ.filter (fun x => C x = c))).card < ((Finset.univ.filter (fun x => C x = d))).card) :
    ((Finset.univ.filter (fun x => C x = d))).card = ((Finset.univ.filter (fun x => C x = c))).card + 1 ∧
      ∃ z ∈ (Finset.univ.filter (fun x => C x = d)), ∀ y ∈ (Finset.univ.filter (fun x => C x = d)), y ≠ z → ∀ x ∈ (Finset.univ.filter (fun x => C x = c)), G.Adj y x := by
  have htwo : 1 < ((Finset.univ.filter (fun x => C x = d))).card := by
    have := Finset.card_pos.mpr hc
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp htwo
  have bound : ((Finset.univ.filter (fun x => C x = d))).card ≤ 1 + secondSmallestDegree G := by
    have hu' := (mem_part C d u).mp hu
    simpa [hu'] using (color_class_bounds h C hσ u).2
  have degUpper (y : V) (hy : y ∈ (Finset.univ.filter (fun x => C x = d))) : G.degree y ≤ ((Finset.univ.filter (fun x => C x = c))).card :=
    Finset.card_le_card (neighborFinset_subset_part C hcd.symm hy)
  have hadj (y : V) (hy : y ∈ (Finset.univ.filter (fun x => C x = d))) (hhigh : secondSmallestDegree G ≤ G.degree y)
      (x : V) (hx : x ∈ (Finset.univ.filter (fun x => C x = c))) : G.Adj y x := by
    have hdeg : ((Finset.univ.filter (fun x => C x = c))).card ≤ (G.neighborFinset y).card := by
      change ((Finset.univ.filter (fun x => C x = c))).card ≤ G.degree y
      omega
    exact (G.mem_neighborFinset y x).mp
      ((Finset.eq_of_subset_of_card_le (neighborFinset_subset_part C hcd.symm hy) hdeg).symm ▸ hx)
  have hsmall : secondSmallestDegree G ≤ ((Finset.univ.filter (fun x => C x = c))).card :=
    (degree_pair u v huv).elim (·.trans (degUpper u hu)) (·.trans (degUpper v hv))
  refine ⟨by omega, ?_⟩
  by_cases hex : ∃ z ∈ (Finset.univ.filter (fun x => C x = d)), G.degree z < secondSmallestDegree G
  · obtain ⟨z,hz,hzlow⟩ := hex
    exact ⟨z,hz,fun y hy hyz => hadj y hy ((degree_pair y z hyz).resolve_right (by omega))⟩
  · exact ⟨u,hu,fun y hy _ => hadj y hy (by
      by_contra! hylow
      exact hex ⟨y,hy,hylow⟩)⟩

/-- In equal-sized parts, the cross edges missing between vertices of degree at
least the second-smallest degree form a matching. -/
theorem balanced_missing_edges [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hsize : ((Finset.univ.filter (fun x => C x = c))).card = ((Finset.univ.filter (fun x => C x = d))).card)
    {x : V} (hx : x ∈ (Finset.univ.filter (fun x => C x = c))) (hhigh : secondSmallestDegree G ≤ G.degree x) :
    ∀ y ∈ (Finset.univ.filter (fun x => C x = d)), ∀ z ∈ (Finset.univ.filter (fun x => C x = d)), ¬ G.Adj x y → ¬ G.Adj x z → y = z := by
  have bound : ((Finset.univ.filter (fun x => C x = c))).card ≤ 1 + secondSmallestDegree G := by
    have hx' := (mem_part C c x).mp hx
    simpa [hx'] using (color_class_bounds h C hσ x).2
  have card_le : (((Finset.univ.filter (fun x => C x = d))) \ G.neighborFinset x).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset (neighborFinset_subset_part C hcd hx)]
    change ((Finset.univ.filter (fun x => C x = d))).card - G.degree x ≤ 1
    omega
  intro y hy z hz hxy hxz
  exact Finset.card_le_one.mp card_le y
    (Finset.mem_sdiff.mpr ⟨hy,fun hm => hxy ((G.mem_neighborFinset x y).mp hm)⟩) z
    (Finset.mem_sdiff.mpr ⟨hz,fun hm => hxz ((G.mem_neighborFinset x z).mp hm)⟩)

end Graph189Bipartite

namespace BipartiteMissingMatching
open SimpleGraph
open scoped Fin.CommRing Fin.NatCast

/-- On `k` left vertices and `k + 1` right vertices, with `3 ≤ k`, a graph that contains
every cross edge except possibly an indexed matching has a Hamiltonian path from the
right vertex indexed by zero to the extra right vertex. -/
theorem hamiltonian {k : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin k ⊕ Option (Fin k)))
    (hcross : ∀ i j : Fin k, i ≠ j → G.Adj (.inl i) (.inr (some j)))
    (hfree : ∀ i : Fin k, G.Adj (.inl i) (.inr none)) :
    ∃ p : G.Walk (.inr (some ⟨0, by omega⟩)) (.inr none), p.IsHamiltonian := by
  have : NeZero k := ⟨by omega⟩
  let block : Fin k → List (Fin k ⊕ Option (Fin k)) :=
    fun i => [.inr (some i), .inl (i + (2 : Fin k))]
  let last : List (Fin k ⊕ Option (Fin k)) := [.inr none]
  let base := (List.finRange k).map block
  have zero_two : (2 : Fin k) ≠ 0 := by
    intro h
    have he : (2 : Fin k).val = (0 : Fin k).val := congrArg Fin.val h
    change ((2 : ℕ) % k) = 0 at he
    rw [Nat.mod_eq_of_lt (by omega : 2 < k)] at he
    omega
  have one_two : (2 : Fin k) ≠ 1 := by
    intro h
    have he : (2 : Fin k).val = (1 : Fin k).val := congrArg Fin.val h
    change ((2 : ℕ) % k) = 1 % k at he
    rw [Nat.mod_eq_of_lt (by omega : 2 < k), Nat.mod_eq_of_lt (by omega : 1 < k)] at he
    omega
  have hparts (L : List (Fin k ⊕ Option (Fin k))) (hL : L ∈ base ++ [last]) :
      L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj := by
    rcases List.mem_append.mp hL with hh | hh
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hh
      have hn : i + (2 : Fin k) ≠ i := fun h => zero_two
        (add_left_cancel (a := i) (by simpa using h))
      simp [block, (hcross _ _ hn).symm]
    · have he : L = last := by simpa using hh
      subst L
      simp [last]
  have hdis (i j : Fin k) (hij : i ≠ j) : List.Disjoint (block i) (block j) := by
    intro x hx hy
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy
    · exact hij (Option.some.inj (Sum.inr.inj hy))
    · cases hy
    · cases hy
    · exact hij (add_right_cancel (Sum.inl.inj hy))
  have hpair : base.Pairwise List.Disjoint :=
    List.pairwise_map.mpr ((List.nodup_iff_pairwise_ne.mp (List.nodup_finRange k)).imp (fun h => hdis _ _ h))
  have hlastDisjoint (L : List (Fin k ⊕ Option (Fin k))) (hL : L ∈ base) :
      List.Disjoint L last := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hL
    intro x hx hy
    have he : x = Sum.inr none := by simpa [last] using hy
    subst x
    simp [block] at hx
  have hlinks : base.IsChain (fun L R =>
      ∀ a ∈ L.getLast?, ∀ b ∈ R.head?, G.Adj a b) := by
    rw [List.isChain_map, List.isChain_iff_getElem]
    intro i hi a ha b hb
    have hi' : i+1 < k := by simpa using hi
    let x : Fin k := ⟨i,by omega⟩
    let y : Fin k := ⟨i+1,hi'⟩
    have hx : (List.finRange k)[i] = x := by
      apply Fin.ext
      simp [List.getElem_finRange,x]
    have hy : (List.finRange k)[i+1] = y := by
      apply Fin.ext
      simp [List.getElem_finRange,y]
    have hs : y = x + (1 : Fin k) := by
      apply Fin.ext
      rw [Fin.val_add]
      change i + 1 = (i + 1 % k) % k
      rw [Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt hi']
    have hne : x + (2 : Fin k) ≠ y := by
      rw [hs]
      exact fun h => one_two (add_left_cancel h)
    have ha' : Sum.inl (x + (2 : Fin k)) = a := by simpa [hx, block] using ha
    have hb' : Sum.inr (some y) = b := by simpa [hy, block] using hb
    exact ha' ▸ hb' ▸ hcross _ _ hne
  have hfullLinks : (base ++ [last]).IsChain (fun L R =>
      ∀ a ∈ L.getLast?, ∀ b ∈ R.head?, G.Adj a b) := by
    apply hlinks.append (by simp)
    intro L hL R hR a ha b hb
    have hLm := List.mem_of_mem_getLast? hL
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hLm
    have hR' : last = R := by simpa using hR
    subst R
    have ha' : Sum.inl (i + (2 : Fin k)) = a := by simpa [block] using ha
    have hb' : Sum.inr none = b := by simpa [last] using hb
    exact ha' ▸ hb' ▸ hfree _
  have hfullDis : (base ++ [last]).Pairwise List.Disjoint := by
    refine List.pairwise_append.mpr ⟨hpair,by simp,?_⟩
    intro L hL R hR
    have hR' : R = last := by simpa using hR
    subst R
    exact hlastDisjoint L hL
  have hcover (x : Fin k ⊕ Option (Fin k)) : ∃ L ∈ base ++ [last], x ∈ L := by
    cases x with
    | inl i =>
      let j := i - (2 : Fin k)
      refine ⟨block j,List.mem_append_left _ (List.mem_map.mpr ⟨j,by simp,rfl⟩),?_⟩
      simp [block,j]
    | inr i =>
      cases i with
      | none => exact ⟨last,by simp,by simp [last]⟩
      | some j =>
        exact ⟨block j,List.mem_append_left _ (List.mem_map.mpr ⟨j,by simp,rfl⟩),by simp [block]⟩
  let route := (base ++ [last]).flatten
  have chain : route.IsChain G.Adj :=
    IndexedPath.flatten_block_chain _ (fun l hl => (hparts l hl).1)
      (fun l hl => (hparts l hl).2.2) hfullLinks
  have distinct : route.Nodup := List.nodup_flatten.mpr
    ⟨fun l hl => (hparts l hl).2.1,hfullDis⟩
  have complete (x : Fin k ⊕ Option (Fin k)) : x ∈ route :=
    List.mem_flatten.mpr (hcover x)
  have route_ne : route ≠ [] := List.ne_nil_of_mem (complete (.inr none))
  have headFin : (List.finRange k).head? = some 0 := by
    cases k with
    | zero => omega
    | succ n => rw [List.finRange_succ]; rfl
  have headBase : base.head? = some (block 0) := by
    dsimp only [base]
    rw [List.head?_map, headFin]
    rfl
  have consBase : block 0 :: base.tail = base :=
    List.cons_head?_tail (by simp [headBase])
  have headFlat : base.flatten.head? = some (.inr (some 0)) := by
    rw [← consBase, List.flatten_cons]
    simp [block]
  have hflat : base.flatten ≠ [] := by
    intro hh
    simp [hh] at headFlat
  have headRoute : route.head? = some (.inr (some 0)) := by
    change ((base ++ [last]).flatten).head? = _
    rw [List.flatten_append, List.head?_append_of_ne_nil _ hflat, headFlat]
  have tailRoute : route.getLast? = some (.inr none) := by
    simp [route, last, List.flatten_append]
  let p := Walk.ofSupport route route_ne chain
  have support : p.support = route := Walk.support_ofSupport route_ne chain
  have path : p.IsPath := Walk.IsPath.mk' (by rwa [support])
  have hh : route.head route_ne = .inr (some 0) :=
    Option.some.inj ((List.head?_eq_some_head route_ne).symm.trans headRoute)
  have ht : route.getLast route_ne = .inr none :=
    Option.some.inj ((List.getLast?_eq_some_getLast route_ne).symm.trans tailRoute)
  change ∃ p : G.Walk (.inr (some 0)) (.inr none), p.IsHamiltonian
  rw [← hh, ← ht]
  exact ⟨p, path.isHamiltonian_of_mem (fun x => by rw [support]; exact complete x)⟩


/-- Any right vertex can serve as the starting point of the alternating path. -/
theorem hamiltonian_from_right {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin k ⊕ Option (Fin k)))
    (hcross : ∀ i j : Fin k, i ≠ j → G.Adj (.inl i) (.inr (some j)))
    (hfree : ∀ i : Fin k, G.Adj (.inl i) (.inr none))
    (start : Option (Fin k)) :
    ∃ b, ∃ p : G.Walk (.inr start) b, p.IsHamiltonian := by
  classical
  cases start with
  | none =>
    obtain ⟨p,hp⟩ := hamiltonian hk G hcross hfree
    refine ⟨_,p.reverse,?_⟩
    intro a
    simpa [Walk.support_reverse] using hp a
  | some j =>
    let zero : Fin k := ⟨0,by omega⟩
    let e := Equiv.swap zero j
    let f := Equiv.sumCongr e (Equiv.optionCongr e)
    let H : SimpleGraph (Fin k ⊕ Option (Fin k)) := G.comap f
    have hf : f (.inr (some zero)) = .inr (some j) := by simp [f,e]
    have hHcross (i t : Fin k) (hit : i ≠ t) : H.Adj (.inl i) (.inr (some t)) := by
      change G.Adj (.inl (e i)) (.inr (some (e t)))
      exact hcross _ _ (fun h => hit (e.injective h))
    have hHfree (i : Fin k) : H.Adj (.inl i) (.inr none) := by
      change G.Adj (.inl (e i)) (.inr none)
      exact hfree _
    obtain ⟨p,hp⟩ := hamiltonian hk H hHcross hHfree
    let hhom : H →g G := SimpleGraph.Hom.comap f G
    have hbij : Function.Bijective hhom := f.bijective
    have hstart : hhom (.inr (some zero)) = .inr (some j) := hf
    rw [← hstart]
    exact ⟨_,p.map hhom,hp.map hhom hbij⟩

end BipartiteMissingMatching

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Alternate between equally sized sets of vertices, starting at an additional
vertex with a neighbor in the first set if that set is nonempty. -/
theorem alternating_chain (left right : Finset V) (z : V)
    (hcard : left.card = right.card)
    (hdisj : ∀ x ∈ left, x ∉ right)
    (hzl : z ∉ left) (hzr : z ∉ right)
    (hcross : ∀ y ∈ right, ∀ x ∈ left, G.Adj y x)
    (hstart : left.Nonempty → ∃ x ∈ left, G.Adj z x) :
    ∃ L : List V, L.head? = some z ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ b, b ∈ L ↔ b = z ∨ b ∈ left ∨ b ∈ right := by
  by_cases hn : left.Nonempty
  · obtain ⟨x,hxl,hzx⟩ := hstart hn
    have hright : right.Nonempty := Finset.card_pos.mp (hcard ▸ Finset.card_pos.mpr hn)
    obtain ⟨y,hyr⟩ := hright
    have hyl : y ∉ left := fun hy => hdisj y hy hyr
    have hyx : G.Adj y x := hcross y hyr x hxl
    have hc' : (left.erase x).card = (right.erase y).card := by
      rw [Finset.card_erase_of_mem hxl, Finset.card_erase_of_mem hyr, hcard]
    obtain ⟨L,hhead,hnodup,hchain,hcover⟩ :=
      alternating_chain (left.erase x) (right.erase y) y hc'
        (fun b hb hr => hdisj b (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hr))
        (fun he => hyl (Finset.mem_of_mem_erase he)) (Finset.notMem_erase _ _)
        (fun b hb a ha => hcross b (Finset.mem_of_mem_erase hb) a (Finset.mem_of_mem_erase ha))
        (fun hempty => let ⟨a,ha⟩ := hempty
                       ⟨a,ha,hcross y hyr a (Finset.mem_of_mem_erase ha)⟩)
    have hxy : x ≠ y := fun e => hyl (e ▸ hxl)
    have hxright := hdisj x hxl
    have hxnot : x ∉ L := by
      rw [hcover]
      simp [hxy, hxright]
    have hzxne : z ≠ x := fun e => hzl (e.symm ▸ hxl)
    have hzyne : z ≠ y := fun e => hzr (e.symm ▸ hyr)
    have hznot : z ∉ L := by rw [hcover]; simp [hzyne, hzl, hzr]
    have hchain' : (x :: L).IsChain G.Adj := hchain.cons (by simpa [hhead] using hyx.symm)
    refine ⟨z :: x :: L, rfl, ?_, hchain'.cons (by simpa using hzx), ?_⟩
    · simp [hzxne, hznot, hxnot, hnodup]
    · intro b
      simp only [List.mem_cons, hcover, Finset.mem_erase]
      by_cases qx : b = x <;> by_cases qy : b = y <;> simp_all
  · have el : left = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have er : right = ∅ := Finset.card_eq_zero.mp (by simpa [el] using hcard.symm)
    subst left
    subst right
    exact ⟨[z],rfl,by simp,by simp,by simp⟩
termination_by left.card
decreasing_by rw [Finset.card_erase_of_mem hxl]; have hpos := Finset.card_pos.mpr hn; omega

/-- The unbalanced bipartite case of DeLaViña's Written on the Wall II conjecture 189. -/
theorem hamiltonian_unbalanced [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hc : ((Finset.univ.filter (fun x => C x = c))).Nonempty)
    (hsize : ((Finset.univ.filter (fun x => C x = c))).card < ((Finset.univ.filter (fun x => C x = d))).card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨hcard,z,hzd,hcomplete⟩ := unbalanced_part_complete_off_one h C hσ hcd hc hsize
  have hzl : z ∉ (Finset.univ.filter (fun x => C x = c)) := fun hz =>
    hcd (((mem_part C c z).mp hz).symm.trans ((mem_part C d z).mp hzd))
  have hdisjoint (x : V) (hx : x ∈ (Finset.univ.filter (fun x => C x = c))) : x ∉ ((Finset.univ.filter (fun x => C x = d))).erase z := by
    intro hr
    exact hcd (((mem_part C c x).mp hx).symm.trans
      ((mem_part C d x).mp (Finset.mem_of_mem_erase hr)))
  obtain ⟨L,hhead,hnodup,hchain,hcover⟩ :=
    alternating_chain ((Finset.univ.filter (fun x => C x = c))) (((Finset.univ.filter (fun x => C x = d))).erase z) z
      (by rw [Finset.card_erase_of_mem hzd,hcard]; omega)
      hdisjoint hzl (Finset.notMem_erase _ _)
      (fun y hy => hcomplete y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
      (fun _ => by
        obtain ⟨x,hzx⟩ := h.preconnected.exists_adj_of_nontrivial z
        exact ⟨x, neighborFinset_subset_part C hcd.symm hzd ((G.mem_neighborFinset z x).mpr hzx), hzx⟩)
  have hne : L ≠ [] := by intro he; simp [he] at hhead
  let p := Walk.ofSupport L hne hchain
  have hs : p.support = L := Walk.support_ofSupport hne hchain
  refine ⟨_,_,p,(Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem ?_⟩
  intro v
  rw [hs,hcover]
  have hm : C v = c ∨ C v = d := by
    generalize C v = e
    fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all
  rcases hm with hv | hv
  · exact Or.inr (Or.inl ((mem_part C c v).mpr hv))
  · by_cases hvz : v = z
    · exact Or.inl hvz
    · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hvz,(mem_part C d v).mpr hv⟩))

end Graph189Bipartite

namespace Graph189Bipartite
variable {V : Type*} [DecidableEq V]

/-- Extend a partial injection of two finite parts to an injection on the entire first part. -/
theorem extend_partial_matching (left right domain : Finset V) (hdom : domain ⊆ left)
    (hcard : left.card ≤ right.card) [Nonempty V]
    (f : V → V) (hf : Set.InjOn f domain) (hfr : Set.MapsTo f domain right) :
    ∃ e : V → V, Set.InjOn e left ∧ Set.MapsTo e left right ∧
      ∀ x ∈ domain, e x = f x := by
  classical
  have himage : domain.image f ⊆ right := hfr.finsetImage_subset
  have hcard' : (left \ domain).card ≤ (right \ domain.image f).card := by
    rw [Finset.card_sdiff_of_subset hdom, Finset.card_sdiff_of_subset himage,
      Finset.card_image_of_injOn hf]
    omega
  have hencard :
      ((left \ domain : Finset V) : Set V).encard ≤
        ((right \ domain.image f : Finset V) : Set V).encard := by
    rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hcard'
  obtain ⟨g,hgr,hg⟩ := (left \ domain).finite_toSet.exists_injOn_of_encard_le hencard
  let e (x : V) := if x ∈ domain then f x else g x
  have hg' {x} (hx : x ∈ left) (hn : x ∉ domain) : g x ∈ right \ domain.image f :=
    hgr (Finset.mem_sdiff.mpr ⟨hx,hn⟩)
  have hsep {x y} (hx : x ∈ domain) (hy : y ∈ left) (hyn : y ∉ domain) :
      f x ≠ g y := fun he =>
    (Finset.mem_sdiff.mp (hg' hy hyn)).2 (he ▸ Finset.mem_image_of_mem f hx)
  refine ⟨e, ?_, ?_, fun x hx => if_pos hx⟩
  · intro x hx y hy he
    change x ∈ left at hx
    change y ∈ left at hy
    by_cases hxd : x ∈ domain <;> by_cases hyd : y ∈ domain
    · exact hf hxd hyd (by simpa [e,hxd,hyd] using he)
    · exact (hsep hxd hy hyd (by simpa [e,hxd,hyd] using he)).elim
    · exact (hsep hyd hx hxd (by simpa [e,hxd,hyd] using he.symm)).elim
    · exact hg (Finset.mem_sdiff.mpr ⟨hx,hxd⟩) (Finset.mem_sdiff.mpr ⟨hy,hyd⟩)
        (by simpa [e,hxd,hyd] using he)
  · intro x hx
    change x ∈ left at hx
    change e x ∈ right
    by_cases hxd : x ∈ domain
    · simpa [e,hxd] using hfr hxd
    · simpa [e,hxd] using (Finset.mem_sdiff.mp (hg' hx hxd)).1

end Graph189Bipartite

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Prepend the exceptional vertex to the indexed path, starting at a chosen neighbor. -/
theorem hamiltonian_of_indexed_matching {k : ℕ} (hk : 3 ≤ k) (z : V)
    (f : Fin k ⊕ Option (Fin k) → V) (hfinj : Function.Injective f)
    (hfz : ∀ a, f a ≠ z) (hfcover : ∀ a, a ≠ z → ∃ i, f i = a)
    (hcross : ∀ i j : Fin k, i ≠ j → G.Adj (f (.inl i)) (f (.inr (some j))))
    (hfree : ∀ i : Fin k, G.Adj (f (.inl i)) (f (.inr none)))
    (start : Option (Fin k)) (hstart : G.Adj z (f (.inr start))) :
    ∃ b, ∃ p : G.Walk z b, p.IsHamiltonian := by
  let H := G.comap f
  obtain ⟨b,p,hp⟩ := BipartiteMissingMatching.hamiltonian_from_right hk H hcross hfree start
  let q : G.Walk (f (.inr start)) (f b) := p.map (SimpleGraph.Hom.comap f G)
  have hqs : q.support = p.support.map f := p.support_map _
  have hzq : z ∉ q.support := by
    rw [hqs]
    intro hz
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hz
    exact hfz i hi
  have hnodup : (Walk.cons hstart q).support.Nodup := by
    simpa [hqs, hzq, List.nodup_cons] using
      And.intro hzq (hp.isPath.support_nodup.map hfinj)
  refine ⟨f b, .cons hstart q, (Walk.IsPath.mk' hnodup).isHamiltonian_of_mem ?_⟩
  intro a
  rw [Walk.support_cons]
  by_cases ha : a = z
  · simp [ha]
  · obtain ⟨i,rfl⟩ := hfcover a ha
    exact List.mem_cons_of_mem _ (hqs ▸ List.mem_map_of_mem (hp.mem_support i))


/-- In equal-sized parts of size at least four, choosing the exceptional vertex
in its own part allows the remaining graph to be indexed by a missing matching. -/
theorem hamiltonian_balanced_large [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hsize : ((Finset.univ.filter (fun x => C x = c))).card = ((Finset.univ.filter (fun x => C x = d))).card)
    (hlarge : 4 ≤ ((Finset.univ.filter (fun x => C x = c))).card) (z : V) (hz : z ∈ (Finset.univ.filter (fun x => C x = c)))
    (hhigh : ∀ x, x ≠ z → secondSmallestDegree G ≤ G.degree x) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let left := ((Finset.univ.filter (fun x => C x = c))).erase z
  let right := (Finset.univ.filter (fun x => C x = d))
  let k := left.card
  have hk' : k = ((Finset.univ.filter (fun x => C x = c))).card - 1 := Finset.card_erase_of_mem hz
  have hk : 3 ≤ k := by omega
  have hcard : right.card = k + 1 := by dsimp [right]; omega
  have hparts (v : V) : v ∈ (Finset.univ.filter (fun x => C x = c)) ∨ v ∈ right := by
    simp only [right, mem_part]
    generalize C v = e
    fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all
  have hdis (x : V) (hx : x ∈ (Finset.univ.filter (fun x => C x = c))) (hy : x ∈ right) : False :=
    hcd (((mem_part C c x).mp hx).symm.trans ((mem_part C d x).mp hy))
  have hzleft : z ∉ left := Finset.notMem_erase _ _
  have hzright : z ∉ right := hdis z hz
  let domain := left.filter fun x => ∃ y ∈ right, ¬ G.Adj x y
  have hdom := Finset.filter_subset (fun x => ∃ y ∈ right, ¬ G.Adj x y) left
  let q (x : V) := if hx : ∃ y ∈ right, ¬ G.Adj x y then hx.choose else z
  have hq (x : V) (hx : x ∈ domain) : q x ∈ right ∧ ¬ G.Adj x (q x) := by
    have hd := (Finset.mem_filter.mp hx).2
    simpa [q, hd] using hd.choose_spec
  have hqinj : Set.InjOn q domain := by
    intro x hx y hy he
    obtain ⟨hr,hm⟩ := hq x hx
    have hx' := Finset.mem_of_mem_erase (hdom hx)
    have hy' := Finset.mem_of_mem_erase (hdom hy)
    exact balanced_missing_edges h C hσ hcd.symm hsize.symm hr
      (hhigh _ (fun heq => hzright (heq ▸ hr))) x hx' y hy'
      (fun e => hm e.symm) (fun e => (hq y hy).2 (he ▸ e.symm))
  obtain ⟨e,heinj,her,heq⟩ :=
    extend_partial_matching left right domain hdom (by omega) q hqinj (fun x hx => (hq x hx).1)
  have hmatch (x : V) (hx : x ∈ left) (y : V) (hy : y ∈ right) (hm : ¬ G.Adj x y) :
      e x = y := by
    have hd : x ∈ domain := Finset.mem_filter.mpr ⟨hx,y,hy,hm⟩
    rw [heq x hd]
    exact balanced_missing_edges h C hσ hcd hsize (Finset.mem_of_mem_erase hx)
      (hhigh _ (Finset.ne_of_mem_erase hx)) (q x) (hq x hd).1 y hy (hq x hd).2 hm
  obtain ⟨w,⟨hwr,hwout⟩,hwunique⟩ :=
    Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one heinj her hcard
  let el : Fin k ≃ left :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe left)).symm
  let l (i : Fin k) : V := (el i).val
  have hl (i : Fin k) : l i ∈ left := (el i).property
  have hlinj : Function.Injective l := fun _ _ he => el.injective (Subtype.ext he)
  have hlsurj (x : V) (hx : x ∈ left) : ∃ i, l i = x := by
    obtain ⟨i,hi⟩ := el.surjective ⟨x,hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  let r (o : Option (Fin k)) : V := o.elim w (fun i => e (l i))
  have hr (o : Option (Fin k)) : r o ∈ right := by
    cases o with
    | none => exact hwr
    | some i => exact her (hl i)
  have hwne (i : Fin k) : e (l i) ≠ w := fun he =>
    hwout (he ▸ Finset.mem_image_of_mem e (hl i))
  have hrinj : Function.Injective r := by
    intro i j he
    cases i <;> cases j
    · rfl
    · exact (hwne _ he.symm).elim
    · exact (hwne _ he).elim
    · exact congrArg some (hlinj (heinj (hl _) (hl _) he))
  have hrsurj (y : V) (hy : y ∈ right) : ∃ o, r o = y := by
    by_cases him : y ∈ left.image e
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp him
      obtain ⟨i,rfl⟩ := hlsurj x hx
      exact ⟨some i,rfl⟩
    · exact ⟨none,(hwunique y ⟨hy,him⟩).symm⟩
  let f : Fin k ⊕ Option (Fin k) → V := Sum.elim l r
  have hfinj : Function.Injective f := by
    intro a b he
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hlinj he)
      | inr j =>
        have he' : l i = r j := he
        exact (hdis (l i) (Finset.mem_of_mem_erase (hl i)) (he'.symm ▸ hr j)).elim
    | inr i =>
      cases b with
      | inl j =>
        have he' : r i = l j := he
        exact (hdis (l j) (Finset.mem_of_mem_erase (hl j)) (he' ▸ hr i)).elim
      | inr j => exact congrArg Sum.inr (hrinj he)
  have hfz (a) : f a ≠ z := by
    cases a with
    | inl i => exact Finset.ne_of_mem_erase (hl i)
    | inr i => exact fun he => hzright (he ▸ hr i)
  have hfcover (v : V) (hv : v ≠ z) : ∃ a, f a = v := by
    rcases hparts v with hv' | hv'
    · obtain ⟨i,hi⟩ := hlsurj v (Finset.mem_erase.mpr ⟨hv,hv'⟩)
      exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := hrsurj v hv'
      exact ⟨.inr i,hi⟩
  have hcross (i j : Fin k) (hij : i ≠ j) : G.Adj (l i) (e (l j)) := by
    by_contra hn
    exact hij (hlinj (heinj (hl i) (hl j) (hmatch _ (hl i) _ (her (hl j)) hn)))
  have hfree (i : Fin k) : G.Adj (l i) w := by
    by_contra hn
    exact hwne i (hmatch _ (hl i) _ hwr hn)
  obtain ⟨x,hzx⟩ := h.preconnected.exists_adj_of_nontrivial z
  have hxr := neighborFinset_subset_part C hcd hz ((G.mem_neighborFinset z x).mpr hzx)
  obtain ⟨start,hs⟩ := hrsurj x hxr
  obtain ⟨b,p,hp⟩ := hamiltonian_of_indexed_matching hk z f hfinj hfz hfcover
    hcross hfree start (by change G.Adj z (r start); rwa [hs])
  exact ⟨z,b,p,hp⟩

end Graph189Bipartite

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem part_nonempty (h : G.Connected) (C : G.Coloring (Fin 2)) (c : Fin 2) :
    ((Finset.univ.filter (fun x => C x = c))).Nonempty := by
  obtain ⟨x⟩ := h.nonempty
  obtain ⟨y,hxy⟩ := h.preconnected.exists_adj_of_nontrivial x
  have hne := C.valid hxy
  have hc : C x = c ∨ C y = c := by
    generalize C x = a at hne ⊢
    generalize C y = b at hne ⊢
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  exact hc.elim (fun hx => ⟨x,(mem_part C c x).mpr hx⟩)
    (fun hy => ⟨y,(mem_part C c y).mpr hy⟩)

omit [Nontrivial V] in
theorem part_card_sum (C : G.Coloring (Fin 2)) :
    ((Finset.univ.filter (fun x => C x = 0))).card + ((Finset.univ.filter (fun x => C x = 1))).card = Fintype.card V := by
  have hd : Disjoint ((Finset.univ.filter (fun x => C x = 0))) ((Finset.univ.filter (fun x => C x = 1))) := by
    refine Finset.disjoint_left.mpr ?_
    intro v h₀ h₁
    rw [mem_part] at h₀ h₁
    have : (0 : Fin 2) = 1 := h₀.symm.trans h₁
    exact (by decide : (0 : Fin 2) ≠ 1) this
  have hu : (Finset.univ.filter (fun x => C x = 0)) ∪ (Finset.univ.filter (fun x => C x = 1)) = Finset.univ := by
    ext v
    simp only [Finset.mem_union, mem_part, Finset.mem_univ, iff_true]
    generalize C v = q
    fin_cases q <;> simp
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]

/-- DeLaViña's conjecture 189 for bipartite graphs of order at least seven.
For smaller order, the same argument handles every unbalanced bipartition. -/
theorem hamiltonian_bipartite_of_card_ge_seven [DecidableRel G.Adj]
    (h : G.Connected) (hB : G.IsBipartite) (hcard : 7 ≤ Fintype.card V)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨C⟩ := hB
  rcases lt_trichotomy ((Finset.univ.filter (fun x => C x = 0))).card ((Finset.univ.filter (fun x => C x = 1))).card with hlt | heq | hgt
  · exact hamiltonian_unbalanced h C hσ (by decide) (part_nonempty h C 0) hlt
  · have hlarge : 4 ≤ ((Finset.univ.filter (fun x => C x = 0))).card := by have := part_card_sum C; omega
    obtain ⟨z,hdeg⟩ : ∃ z : V, ∀ x, x ≠ z → secondSmallestDegree G ≤ G.degree x := by
      by_cases hlow : ∃ y, G.degree y < secondSmallestDegree G
      · obtain ⟨y,hy⟩ := hlow
        exact ⟨y,fun x hx => (degree_pair x y hx).resolve_right (by omega)⟩
      · obtain ⟨y⟩ := h.nonempty
        exact ⟨y,fun x _ => by by_contra! hx; exact hlow ⟨x,hx⟩⟩
    have hz : z ∈ (Finset.univ.filter (fun x => C x = 0)) ∨ z ∈ (Finset.univ.filter (fun x => C x = 1)) := by
      simp only [mem_part]
      generalize C z = q
      fin_cases q <;> simp
    rcases hz with hz | hz
    · exact hamiltonian_balanced_large h C hσ (by decide) heq hlarge z hz hdeg
    · exact hamiltonian_balanced_large h C hσ (by decide) heq.symm (heq ▸ hlarge) z hz hdeg
  · exact hamiltonian_unbalanced h C hσ (by decide) (part_nonempty h C 1) hgt

end Graph189Bipartite

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}

omit [Nontrivial V] in
/-- A full-length chain of distinct vertices is a Hamiltonian path. -/
theorem hamiltonian_of_chain (L : List V) (hn : L ≠ []) (hc : L.IsChain G.Adj)
    (hd : L.Nodup) (hlen : L.length = Fintype.card V) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport L hn hc
  have hs : p.support = L := Walk.support_ofSupport hn hc
  refine ⟨_,_,p,Walk.isHamiltonian_iff_isPath_and_length_eq.mpr ⟨Walk.IsPath.mk' ?_,?_⟩⟩
  · rwa [hs]
  · have he := p.length_support
    rw [hs, hlen] at he
    omega

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 500000 in
set_option synthInstance.maxSize 1024 in
/-- Finite certification of the equal parts of size three, with the degree
hypotheses derived from the original conjecture. -/
theorem hamiltonian_balanced_three [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (h0 : ((Finset.univ.filter (fun x => C x = 0))).card = 3) (h1 : ((Finset.univ.filter (fun x => C x = 1))).card = 3) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let Six := Fin 3 ⊕ Fin 3

  let table3 (a b c : Fin 8) (i j : Fin 3) : Bool :=
    (if i = 0 then a.val else if i = 1 then b.val else c.val).testBit j.val

  let row3 (T : Fin 3 → Fin 3 → Bool) (v : Six) (i : Fin 3) : Bool :=
    match v with
    | .inl j => T j i
    | .inr j => T i j

  let high3 (T : Fin 3 → Fin 3 → Bool) (v : Six) : Prop :=
    ∃ i j : Fin 3, i ≠ j ∧ row3 T v i = true ∧ row3 T v j = true

  let accept3 (T : Fin 3 → Fin 3 → Bool) : Prop :=
    (∀ v : Six, ∃ i : Fin 3, row3 T v i = true) ∧
    ∀ v w : Six, v ≠ w → high3 T v ∨ high3 T w

  let route3 (T : Fin 3 → Fin 3 → Bool) (l₀ l₁ l₂ r₀ r₁ r₂ : Fin 3) : Prop :=
    l₀ ≠ l₁ ∧ l₀ ≠ l₂ ∧ l₁ ≠ l₂ ∧ r₀ ≠ r₁ ∧ r₀ ≠ r₂ ∧ r₁ ≠ r₂ ∧
    T l₀ r₀ = true ∧ T l₁ r₀ = true ∧ T l₁ r₁ = true ∧
    T l₂ r₁ = true ∧ T l₂ r₂ = true

  have all_tables3 : ∀ a b c : Fin 8, accept3 (table3 a b c) →
      ∃ l₀ l₁ l₂ r₀ r₁ r₂, route3 (table3 a b c) l₀ l₁ l₂ r₀ r₁ r₂ := by
    dsimp [accept3, high3, route3, row3, Six, table3]
    decide +kernel


  have encode_row3 (R : Fin 3 → Bool) :
      ∃ n : Fin 8, ∀ i : Fin 3, n.val.testBit i.val = R i := by
    let num := (if R 0 then 1 else 0) + (if R 1 then 2 else 0) + (if R 2 then 4 else 0)
    have hnum : num < 8 := by
      cases h0 : R 0 <;> cases h1 : R 1 <;> cases h2 : R 2 <;> simp [num,h0,h1,h2]
    refine ⟨⟨num,hnum⟩,?_⟩
    intro i
    cases h0 : R 0 <;> cases h1 : R 1 <;> cases h2 : R 2 <;>
      fin_cases i <;> simp [num,h0,h1,h2,Nat.testBit]

  have some_route3 (T : Fin 3 → Fin 3 → Bool) (hT : accept3 T) :
      ∃ l₀ l₁ l₂ r₀ r₁ r₂, route3 T l₀ l₁ l₂ r₀ r₁ r₂ := by
    obtain ⟨a,ha⟩ := encode_row3 (T 0)
    obtain ⟨b,hb⟩ := encode_row3 (T 1)
    obtain ⟨c,hc⟩ := encode_row3 (T 2)
    have he : table3 a b c = T := by
      funext i j
      fin_cases i
      · exact ha j
      · exact hb j
      · exact hc j
    rw [← he] at hT ⊢
    exact all_tables3 a b c hT
  let e₀ : Fin 3 ≃ (Finset.univ.filter (fun x => C x = 0)) := (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h0)).symm
  let e₁ : Fin 3 ≃ (Finset.univ.filter (fun x => C x = 1)) := (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h1)).symm
  let l (i : Fin 3) : V := (e₀ i).val
  let r (i : Fin 3) : V := (e₁ i).val
  have hl (i : Fin 3) : l i ∈ (Finset.univ.filter (fun x => C x = 0)) := (e₀ i).property
  have hr (i : Fin 3) : r i ∈ (Finset.univ.filter (fun x => C x = 1)) := (e₁ i).property
  have hlinj : Function.Injective l := fun _ _ he => e₀.injective (Subtype.ext he)
  have hrinj : Function.Injective r := fun _ _ he => e₁.injective (Subtype.ext he)
  have hne (i j : Fin 3) : l i ≠ r j := by
    intro he
    have hcl := (mem_part C 0 _).mp (hl i)
    have hcr := (mem_part C 1 _).mp (hr j)
    exact (by decide : (0 : Fin 2) ≠ 1) (hcl.symm.trans (he.symm ▸ hcr))
  let φ : Six → V := Sum.elim l r
  have hφ : Function.Injective φ := by
    intro a b he
    cases a <;> cases b
    · exact congrArg Sum.inl (hlinj he)
    · exact (hne _ _ he).elim
    · exact (hne _ _ he.symm).elim
    · exact congrArg Sum.inr (hrinj he)
  let T (i j : Fin 3) := decide (G.Adj (l i) (r j))
  let opp (v : Six) : Fin 3 → V := v.elim (fun _ => r) (fun _ => l)
  have hT (v : Six) (i : Fin 3) : row3 T v i = true ↔ G.Adj (φ v) (opp v i) := by
    cases v
    · simp [T,row3,φ,opp]
    · simp [T,row3,φ,opp,adj_comm]
  have hsurj (v : Six) (y : V) (hy : G.Adj (φ v) y) : ∃ i, opp v i = y := by
    cases v with
    | inl i =>
      have hy' := neighborFinset_subset_part C (by decide : (0 : Fin 2) ≠ 1)
        (hl i) ((G.mem_neighborFinset _ _).mpr hy)
      obtain ⟨j,hj⟩ := e₁.surjective ⟨y,hy'⟩
      exact ⟨j,congrArg Subtype.val hj⟩
    | inr i =>
      have hy' := neighborFinset_subset_part C (by decide : (1 : Fin 2) ≠ 0)
        (hr i) ((G.mem_neighborFinset _ _).mpr hy)
      obtain ⟨j,hj⟩ := e₀.surjective ⟨y,hy'⟩
      exact ⟨j,congrArg Subtype.val hj⟩
  have hdeg2 : 2 ≤ secondSmallestDegree G := by
    have hcl := (mem_part C 0 _).mp (hl 0)
    have hb := (color_class_bounds h C hσ (l 0)).2
    rw [hcl] at hb
    change ((Finset.univ.filter (fun x => C x = 0))).card ≤ _ at hb
    rw [h0] at hb
    omega
  have high (v : Six) (hv : secondSmallestDegree G ≤ G.degree (φ v)) : high3 T v := by
    have ht : 1 < (G.neighborFinset (φ v)).card := by
      change 1 < G.degree (φ v)
      omega
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp ht
    have ha' := (G.mem_neighborFinset _ _).mp ha
    have hb' := (G.mem_neighborFinset _ _).mp hb
    obtain ⟨i,hi⟩ := hsurj v a ha'
    obtain ⟨j,hj⟩ := hsurj v b hb'
    refine ⟨i,j,fun e => hab (hi.symm.trans (e ▸ hj)),(hT v i).mpr ?_,(hT v j).mpr ?_⟩
    · rwa [hi]
    · rwa [hj]
  have haccept : accept3 T := by
    constructor
    · intro v
      obtain ⟨y,hy⟩ := h.preconnected.exists_adj_of_nontrivial (φ v)
      obtain ⟨i,hi⟩ := hsurj v y hy
      exact ⟨i,(hT v i).mpr (hi.symm ▸ hy)⟩
    · intro v w hvw
      exact (degree_pair (φ v) (φ w) (fun he => hvw (hφ he))).imp (high v) (high w)
  obtain ⟨a,b,c,x,y,z,hab,hac,hbc,hxy,hxz,hyz,hax,hbx,hby,hcy,hcz⟩ := some_route3 T haccept
  have ha₁ : G.Adj (l a) (r x) := of_decide_eq_true hax
  have ha₂ : G.Adj (r x) (l b) := (of_decide_eq_true hbx : G.Adj (l b) (r x)).symm
  have ha₃ : G.Adj (l b) (r y) := of_decide_eq_true hby
  have ha₄ : G.Adj (r y) (l c) := (of_decide_eq_true hcy : G.Adj (l c) (r y)).symm
  have ha₅ : G.Adj (l c) (r z) := of_decide_eq_true hcz
  refine hamiltonian_of_chain [l a,r x,l b,r y,l c,r z] (by simp) ?_ ?_ ?_
  · simp [ha₁,ha₂,ha₃,ha₄,ha₅]
  · simp [hne, ne_comm, show l a ≠ l b from fun e => hab (hlinj e),
      show l a ≠ l c from fun e => hac (hlinj e), show l b ≠ l c from fun e => hbc (hlinj e),
      show r x ≠ r y from fun e => hxy (hrinj e), show r x ≠ r z from fun e => hxz (hrinj e),
      show r y ≠ r z from fun e => hyz (hrinj e)]
  · simpa [h0,h1] using part_card_sum C


/-- A connected graph on at least three vertices contains a vertex with two distinct neighbors. -/
theorem exists_degree_gt_one [DecidableRel G.Adj] (h : G.Connected)
    (hcard : 2 < Fintype.card V) : ∃ x, 1 < G.degree x := by
  by_contra! hlow
  obtain ⟨a⟩ := h.nonempty
  obtain ⟨b,hab⟩ := h.preconnected.exists_adj_of_nontrivial a
  have next {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) : v = w :=
    Finset.card_le_one.mp (hlow u) v ((G.mem_neighborFinset u v).mpr huv)
      w ((G.mem_neighborFinset u w).mpr huw)
  have stays {u v : V} (p : G.Walk u v) (hu : u = a ∨ u = b) :
      v = a ∨ v = b := by
    induction p with
    | nil => exact hu
    | @cons u w v huw p ih =>
      apply ih
      rcases hu with rfl | rfl
      · exact Or.inr (next huw hab)
      · exact Or.inl (next huw hab.symm)
  have all (v : V) : v = a ∨ v = b := by
    obtain ⟨p⟩ := h.preconnected a v
    exact stays p (Or.inl rfl)
  have huniv : Finset.univ = ({a,b} : Finset V) := by
    ext v
    simp [all v]
  have : Fintype.card V = 2 := by
    rw [← Finset.card_univ, huniv, Finset.card_pair (G.ne_of_adj hab)]
  omega

/-- The balanced four-vertex case, using connectivity to find a vertex adjacent
to both vertices of the opposite part. -/
theorem hamiltonian_balanced_two [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (h0 : ((Finset.univ.filter (fun x => C x = 0))).card = 2) (h1 : ((Finset.univ.filter (fun x => C x = 1))).card = 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hcard : Fintype.card V = 4 := by simpa [h0,h1] using (part_card_sum C).symm
  obtain ⟨u,hu⟩ := exists_degree_gt_one h (by omega)
  let c := C u
  let d := if c = 0 then 1 else (0 : Fin 2)
  have hcd : c ≠ d := by
    dsimp [d]
    split <;> rename_i hc
    · simp [hc]
    · exact hc
  have sizes (t : Fin 2) : ((Finset.univ.filter (fun x => C x = t))).card = 2 := by fin_cases t <;> assumption
  have huc : u ∈ (Finset.univ.filter (fun x => C x = c)) := (mem_part C c u).mpr rfl
  have hsub : G.neighborFinset u ⊆ (Finset.univ.filter (fun x => C x = d)) := neighborFinset_subset_part C hcd huc
  have heq : G.neighborFinset u = (Finset.univ.filter (fun x => C x = d)) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [sizes]
    exact hu
  have hdouble (w : V) (hw : w ∈ (Finset.univ.filter (fun x => C x = d))) : G.Adj u w :=
    (G.mem_neighborFinset u w).mp (heq ▸ hw)
  obtain ⟨q,s,hqs,heven⟩ := Finset.card_eq_two.mp (sizes c)
  have hpair : u = q ∨ u = s := by simpa [heven] using huc
  obtain ⟨v,hvc,hvu⟩ : ∃ v ∈ (Finset.univ.filter (fun x => C x = c)), v ≠ u := by
    rcases hpair with he | he
    · exact ⟨s, by simp [heven], he.symm ▸ hqs.symm⟩
    · exact ⟨q, by simp [heven], he.symm ▸ hqs⟩
  obtain ⟨x,hvx⟩ := h.preconnected.exists_adj_of_nontrivial v
  have hxd : x ∈ (Finset.univ.filter (fun x => C x = d)) := neighborFinset_subset_part C hcd hvc
    ((G.mem_neighborFinset v x).mpr hvx)
  obtain ⟨q,s,hqs,heven⟩ := Finset.card_eq_two.mp (sizes d)
  have hpair : x = q ∨ x = s := by simpa [heven] using hxd
  obtain ⟨y,hyd,hyx⟩ : ∃ y ∈ (Finset.univ.filter (fun x => C x = d)), y ≠ x := by
    rcases hpair with he | he
    · exact ⟨s, by simp [heven], he.symm ▸ hqs.symm⟩
    · exact ⟨q, by simp [heven], he.symm ▸ hqs⟩
  have hsep {a b : V} (ha : a ∈ (Finset.univ.filter (fun x => C x = c))) (hb : b ∈ (Finset.univ.filter (fun x => C x = d))) : a ≠ b := by
    intro he
    subst b
    exact hcd (((mem_part C c a).mp ha).symm.trans ((mem_part C d a).mp hb))
  refine hamiltonian_of_chain [y,u,x,v] (by simp) ?_ ?_ ?_
  · simp [(hdouble y hyd).symm, hdouble x hxd, hvx.symm]
  · simp [(hsep huc hyd).symm, hyx, (hsep hvc hyd).symm, hsep huc hxd,
      hvu.symm, (hsep hvc hxd).symm]
  · simp [hcard]

/-- The two-vertex case is the single edge given by connectivity. -/
theorem hamiltonian_card_two (h : G.Connected) (hcard : Fintype.card V = 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a⟩ := h.nonempty
  obtain ⟨b,hab⟩ := h.preconnected.exists_adj_of_nontrivial a
  exact hamiltonian_of_chain [a,b] (by simp) (by simpa) (by simp [G.ne_of_adj hab])
    (by simp [hcard])

end Graph189Bipartite

/-! The bipartite case of Ermelinda DeLaViña's Written on the Wall II
Graph Conjecture 189, with its original degree and vertex-distance hypothesis. -/
namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V]

theorem hamiltonian_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.Connected) (hB : G.IsBipartite)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases hcard : 7 ≤ Fintype.card V
  · exact hamiltonian_bipartite_of_card_ge_seven h hB hcard hσ
  obtain ⟨C⟩ := hB
  have h0 := part_nonempty h C 0
  have h1 := part_nonempty h C 1
  rcases lt_trichotomy ((Finset.univ.filter (fun x => C x = 0))).card ((Finset.univ.filter (fun x => C x = 1))).card with hlt | heq | hgt
  · exact hamiltonian_unbalanced h C hσ (by decide) h0 hlt
  · have hcs := part_card_sum C
    have hpos := Finset.card_pos.mpr h0
    have hcases : ((Finset.univ.filter (fun x => C x = 0))).card = 1 ∨ ((Finset.univ.filter (fun x => C x = 0))).card = 2 ∨ ((Finset.univ.filter (fun x => C x = 0))).card = 3 := by omega
    rcases hcases with hcase | hcase | hcase
    · exact hamiltonian_card_two h (by omega)
    · exact hamiltonian_balanced_two h C hcase (heq ▸ hcase)
    · exact hamiltonian_balanced_three h C hσ hcase (heq ▸ hcase)
  · exact hamiltonian_unbalanced h C hσ (by decide) h1 hgt

end Graph189Bipartite

namespace Graph189OddCycleCount
open SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nontrivial V] in
/-- Double counting a relation between two finite sets. -/
private theorem sum_fibers (A B : Finset V) (R : V → V → Prop) [DecidableRel R] :
    ∑ a ∈ A, (B.filter (R a)).card = ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- The incidence count in the shortest-odd-cycle argument. Its hypotheses
are the three local bounds supplied by the cycle geometry. -/
theorem odd_cycle_core_spans (h : G.Connected) (C : Finset V) (hm : 5 ≤ C.card)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hAdj : ∀ v ∈ C, (C.filter (G.Adj v)).card ≤ 2)
    (hEven : ∀ v ∈ C, 3 ≤ (C.filter (fun x => Even (G.dist v x))).card)
    (hOutside : ∀ x ∉ C, 3 * (C.filter (fun v => G.Adj v x)).card ≤
      2 * (C.filter (fun v => G.dist v x = 2)).card) :
    C = Finset.univ := by
  classical
  let O := Finset.univ \ C
  let s := G.secondSmallestDegree
  let A (v : V) := (O.filter (G.Adj v)).card
  let D (v : V) := (O.filter (fun x => G.dist v x = 2)).card
  have subset_adj (v : V) : C.filter (G.Adj v) ∪ O.filter (G.Adj v) = G.neighborFinset v := by
    ext x
    simp [O, G.mem_neighborFinset v x]
    by_cases hx : x ∈ C <;> simp [hx]
  have hdisj (p : V → Prop) (q : V → Prop) [DecidablePred p] [DecidablePred q] :
      Disjoint (C.filter p) (O.filter q) := by
    apply Finset.disjoint_left.mpr
    intro x hxc hxo
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxo).1).2 (Finset.mem_filter.mp hxc).1
  have even_upper (v : V) (hv : v ∈ C) : D v ≤ s - 2 := by
    have hs : C.filter (fun x => Even (G.dist v x)) ∪
        O.filter (fun x => G.dist v x = 2) ⊆ Finset.univ.filter (fun x => Even (G.dist v x)) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
      · have he := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ (by decide : Even 2)⟩
    have hu := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint (hdisj _ _)] at hu
    change (C.filter (fun x => Even (G.dist v x))).card + D v ≤ G.distEven v at hu
    have hev := hEven v hv
    have hbound := hσ v
    dsimp [s]
    omega
  obtain ⟨v₀,hv₀⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z,hzz⟩ : ∃ z : V, ∀ x, x ≠ z → s ≤ G.degree x := by
    by_cases hex : ∃ z, G.degree z < s
    · obtain ⟨z,hz⟩ := hex
      exact ⟨z,fun x hx => (Graph189Bipartite.degree_pair (G := G) x z hx).resolve_right
        (Nat.not_le.mpr hz)⟩
    · exact ⟨v₀,fun x _ => by by_contra! hx; exact hex ⟨x,hx⟩⟩
  have adj_lower (v : V) (hv : v ∈ C.erase z) : s - 2 ≤ A v := by
    have hd := hzz v (Finset.ne_of_mem_erase hv)
    have hi := hAdj v (Finset.mem_of_mem_erase hv)
    have hcard := congrArg Finset.card (subset_adj v)
    rw [Finset.card_union_of_disjoint (hdisj _ _)] at hcard
    change (C.filter (G.Adj v)).card + A v = G.degree v at hcard
    omega
  have AS : (C.card - 1) * (s - 2) ≤ ∑ v ∈ C, A v := by
    have hsize : C.card - 1 ≤ (C.erase z).card := by
      by_cases hz : z ∈ C
      · exact le_of_eq (Finset.card_erase_of_mem hz).symm
      · rw [Finset.erase_eq_of_notMem hz]; omega
    have hpoint : ∑ v ∈ C.erase z, (s - 2) ≤ ∑ v ∈ C.erase z, A v :=
      Finset.sum_le_sum adj_lower
    have hconst : (C.erase z).card * (s - 2) ≤ ∑ v ∈ C.erase z, A v := by simpa using hpoint
    exact ((Nat.mul_le_mul_right _ hsize).trans hconst).trans
      (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  have DS : (∑ v ∈ C, D v) ≤ C.card * (s - 2) := by
    simpa using (Finset.sum_le_sum even_upper : ∑ v ∈ C, D v ≤ ∑ _v ∈ C, (s - 2))
  have incidence : 3 * (∑ v ∈ C, A v) ≤ 2 * (∑ v ∈ C, D v) := by
    dsimp only [A,D]
    rw [sum_fibers C O G.Adj, sum_fibers C O (fun v x => G.dist v x = 2)]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun x hx => hOutside x (Finset.mem_sdiff.mp hx).2)
  have hcoeff : 2 * C.card < 3 * (C.card - 1) := by omega
  have hszero : s - 2 = 0 := by
    by_contra hn
    have hbad : 3 * ((C.card - 1) * (s - 2)) ≤ 2 * (C.card * (s - 2)) :=
      ((Nat.mul_le_mul_left _ AS).trans incidence).trans (Nat.mul_le_mul_left _ DS)
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at hbad
    exact (Nat.not_lt_of_ge hbad) (Nat.mul_lt_mul_of_pos_right hcoeff (Nat.pos_of_ne_zero hn))
  have hclosed {v x : V} (hv : v ∈ C) (hx : G.Adj v x) : x ∈ C := by
    by_contra hn
    have hpos : 0 < A v := Finset.card_pos.mpr
      ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩,hx⟩⟩
    have hsum := Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _) hv
    have hzero : (∑ v ∈ C, D v) = 0 := by rw [hszero, Nat.mul_zero] at DS; omega
    omega
  have stays {a b : V} (p : G.Walk a b) (ha : a ∈ C) : b ∈ C := by
    induction p with
    | nil => exact ha
    | cons hab p ih => exact ih (hclosed ha hab)
  apply Finset.eq_univ_of_forall
  intro v
  obtain ⟨p⟩ := h.preconnected v₀ v
  exact stays p hv₀

end Graph189OddCycleCount

namespace Graph189ShortestOdd
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- In a connected nonbipartite graph, walks from a root provide an odd closed walk. -/
theorem exists_odd_closed (h : G.Connected) (hB : ¬ G.IsBipartite) :
    ∃ a : V, ∃ p : G.Walk a a, p.length % 2 = 1 := by
  by_contra! hn
  obtain ⟨a⟩ := h.nonempty
  let color (v : V) : Fin 2 := ⟨G.dist a v % 2, Nat.mod_lt _ (by decide)⟩
  apply hB
  refine ⟨Coloring.mk color ?_⟩
  intro x y hxy he
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a x
  obtain ⟨q,hq⟩ := h.exists_walk_length_eq_dist a y
  let w := (p.concat hxy).append q.reverse
  have ho := hn a w
  have hel : G.dist a x % 2 = G.dist a y % 2 := congrArg Fin.val he
  dsimp only [w] at ho
  rw [Walk.length_append, Walk.length_concat, Walk.length_reverse, hp, hq] at ho
  omega

/-- A shortest odd closed walk minimizes length among all odd closed walks. -/
theorem exists_shortest (h : G.Connected) (hB : ¬ G.IsBipartite) :
    ∃ a : V, ∃ p : G.Walk a a, p.length % 2 = 1 ∧
      ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length := by
  classical
  let P (n : ℕ) := ∃ a : V, ∃ p : G.Walk a a, p.length = n ∧ p.length % 2 = 1
  obtain ⟨a,p,hp⟩ := exists_odd_closed h hB
  have hP : ∃ n, P n := ⟨p.length,a,p,rfl,hp⟩
  obtain ⟨b,q,hq,hqo⟩ := Nat.find_spec hP
  exact ⟨b,q,hqo,fun c r hr => hq.symm ▸ Nat.find_min' hP ⟨c,r,rfl,hr⟩⟩

/-- An outside walk between two indices of a minimal odd closed walk must
be as long as the cycle arc of the same parity. -/
theorem detour_lower_bound {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (hmin : ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) (r : G.Walk (p.getVert i) (p.getVert j)) :
    (r.length % 2 = (j-i) % 2 → j-i ≤ r.length) ∧
    (r.length % 2 ≠ (j-i) % 2 → p.length-(j-i) ≤ r.length) := by
  let forward : G.Walk (p.getVert i) (p.getVert j) := ((p.drop i).take (j-i)).copy rfl (by rw [Walk.drop_getVert, show i + (j-i) = j by omega])
  let back := (p.drop j).append (p.take i)
  have hf : forward.length = j-i := by
    dsimp [forward]
    rw [Walk.length_copy, Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega)]
  have hb : back.length = p.length-(j-i) := by
    dsimp [back]
    rw [Walk.length_append, Walk.drop_length, Walk.take_length, Nat.min_eq_left (by omega)]
    omega
  constructor
  · intro he
    have hlen : (r.append back).length = r.length + (p.length-(j-i)) := by rw [Walk.length_append,hb]
    have h := hmin _ (r.append back) (by rw [hlen]; omega)
    rw [hlen] at h
    omega
  · intro he
    have hlen : (r.append forward.reverse).length = r.length + (j-i) := by
      rw [Walk.length_append,Walk.length_reverse,hf]
    have h := hmin _ (r.append forward.reverse) (by rw [hlen]; omega)
    rw [hlen] at h
    omega

theorem shortest_index_injective {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (hmin : ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length) :
    Function.Injective (fun i : Fin p.length => p.getVert i.val) := by
  have hinc (i j : Fin p.length) (hij : i < j) : p.getVert i.val ≠ p.getVert j.val := by
    intro he
    let r : G.Walk (p.getVert i.val) (p.getVert j.val) := (Walk.nil : G.Walk _ _).copy rfl he
    have hr : r.length = 0 := by simp [r]
    have h := detour_lower_bound p hp hmin (Nat.le_of_lt hij) (Nat.le_of_lt j.isLt) r
    simp only [hr, Nat.zero_mod, Nat.le_zero_eq] at h
    have hi' := i.isLt
    have hj' := j.isLt
    change i.val < j.val at hij
    omega
  intro i j he
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact (hinc i j hij he).elim
  · rfl
  · exact (hinc j i hji he.symm).elim

/-- Distance one and two detours pin the cyclic gap of their endpoints. -/
theorem short_detours {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (hmin : ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length)
    {i j : ℕ} (hij : i < j) (hj : j < p.length) :
    (G.Adj (p.getVert i) (p.getVert j) → j-i = 1 ∨ j-i = p.length-1) ∧
    ((∃ x, G.Adj (p.getVert i) x ∧ G.Adj x (p.getVert j)) → j-i = 2 ∨ j-i = p.length-2) := by
  constructor
  · intro he
    let r := Walk.cons he Walk.nil
    have hr : r.length = 1 := rfl
    have h := detour_lower_bound p hp hmin hij.le hj.le r
    rw [hr] at h
    omega
  · rintro ⟨x,hix,hxj⟩
    let r := Walk.cons hix (Walk.cons hxj Walk.nil)
    have hr : r.length = 2 := rfl
    have h := detour_lower_bound p hp hmin hij.le hj.le r
    rw [hr] at h
    omega

/-- A closed odd walk in a triangle-free simple graph has length at least five. -/
theorem odd_ge_five {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (htri : ∀ {x y z}, G.Adj x y → G.Adj y z → ¬ G.Adj x z) : 5 ≤ p.length := by
  by_contra! h
  have he : p.length = 1 ∨ p.length = 3 := by omega
  rcases he with he | he
  · have h1 := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero, show 0+1 = p.length by omega, Walk.getVert_length] at h1
    exact G.irrefl h1
  · have h1 := p.adj_getVert_succ (i := 0) (by omega)
    have h2 := p.adj_getVert_succ (i := 1) (by omega)
    have h3 := p.adj_getVert_succ (i := 2) (by omega)
    rw [Walk.getVert_zero] at h1
    rw [show 2+1 = p.length by omega, Walk.getVert_length] at h3
    exact htri h1 h2 h3.symm

end Graph189ShortestOdd

namespace Graph189CyclicGeometry
open SimpleGraph
open scoped Fin.CommRing Fin.NatCast
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
/-- Adjacent two-edge endpoints with no shortcut have distance two. -/
private theorem dist_two_of_triangle_free
    (htri : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) :
    G.dist a c = 2 := by
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  have hl : G.dist a c ≤ 2 := by simpa [p] using G.dist_le p
  have hp : 0 < G.dist a c :=
    Nat.pos_of_ne_zero (fun h => hac (p.reachable.dist_eq_zero_iff.mp h))
  have hn : G.dist a c ≠ 1 := fun h => htri hab hbc (dist_eq_one_iff_adj.mp h)
  omega

/-- Index geometry for a shortest odd cycle suffices for the incidence argument. -/
theorem traceable_of_geometry (h : G.Connected)
    (htri : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    {m : ℕ} [NeZero m] (hm : 5 ≤ m) (hodd : m % 2 = 1) (f : Fin m ↪ V)
    (hcyc : ∀ i : Fin m, G.Adj (f i) (f (i+1)))
    (h1 : ∀ i j : Fin m, G.Adj (f i) (f j) → j = i+1 ∨ i = j+1)
    (h2 : ∀ i j : Fin m, i ≠ j → (∃ x, G.Adj (f i) x ∧ G.Adj x (f j)) →
      j = i+2 ∨ i = j+2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let C := Finset.univ.map f
  have hc : C.card = m := by simp [C]
  have shift_ne (k : ℕ) (hk : 0 < k) (hk' : k < m) : (k : Fin m) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    rw [Fin.val_natCast, Nat.mod_eq_of_lt hk', Fin.val_zero] at hv
    omega
  have hn₂ : (2 : Fin m) ≠ 0 := shift_ne 2 (by omega) (by omega)
  have hn₄ : (4 : Fin m) ≠ 0 := shift_ne 4 (by omega) (by omega)
  have hn₆ : (6 : Fin m) ≠ 0 := by
    by_cases he : m = 5
    · intro heq
      have hv := congrArg Fin.val heq
      have hv' : 6 % m = 0 := by simpa [Fin.val_natCast] using hv
      rw [he] at hv'
      omega
    · exact shift_ne 6 (by omega) (by omega)
  have triple_ne (i : Fin m) : i-1 ≠ i+1 ∧ i-1 ≠ i+3 ∧ i+1 ≠ i+3 := by
    constructor
    · intro e
      apply hn₂
      apply add_left_cancel (a := i)
      calc
        i + 2 = (i+1)+1 := by ring
        _ = (i-1)+1 := congrArg (fun t => t+1) e.symm
        _ = i+0 := by ring
    · constructor
      · intro e
        apply hn₄
        apply add_left_cancel (a := i)
        calc
          i + 4 = (i+3)+1 := by ring
          _ = (i-1)+1 := congrArg (fun t => t+1) e.symm
          _ = i+0 := by ring
      · intro e
        apply hn₂
        apply add_left_cancel (a := i+1)
        calc
          (i+1)+2 = i+3 := by ring
          _ = (i+1)+0 := by simpa using e.symm
  have even_ne (i : Fin m) : i ≠ i+2 ∧ i ≠ i-2 ∧ i+2 ≠ i-2 := by
    refine ⟨fun e => hn₂ (add_left_cancel (a := i) (by simpa using e.symm)),?_,?_⟩
    · intro e
      apply hn₂
      apply add_left_cancel (a := i)
      calc
        i + 2 = (i-2)+2 := congrArg (fun t => t+2) e
        _ = i+0 := by ring
    · intro e
      apply hn₄
      apply add_left_cancel (a := i)
      calc
        i + 4 = (i+2)+2 := by ring
        _ = (i-2)+2 := congrArg (fun t => t+2) e
        _ = i+0 := by ring
  have backwards (i : Fin m) : G.Adj (f i) (f (i-1)) := by
    have hh := (hcyc (i-1)).symm
    rwa [sub_add_cancel] at hh
  have internal_neighbors (v : V) (hv : v ∈ C) : (C.filter (G.Adj v)).card ≤ 2 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
    rw [Finset.filter_map, Finset.card_map]
    have hs : (Finset.univ.filter (G.Adj (f i) ∘ f)) ⊆ ({i+1,i-1} : Finset (Fin m)) := by
      intro j hj
      rcases h1 i j (Finset.mem_filter.mp hj).2 with e | e
      · simp [e]
      · have he : j = i-1 := eq_sub_of_add_eq e.symm
        simp [he]
    have hle := Finset.card_le_card hs
    exact hle.trans Finset.card_le_two
  have internal_even (v : V) (hv : v ∈ C) :
      3 ≤ (C.filter (fun x => Even (G.dist v x))).card := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
    rw [Finset.filter_map, Finset.card_map]
    have hp : G.dist (f i) (f (i+2)) = 2 :=
      dist_two_of_triangle_free htri (hcyc i)
        (by convert hcyc (i+1) using 2; ring)
        (fun e => (even_ne i).1 (f.injective e))
    have hm' : G.dist (f i) (f (i-2)) = 2 :=
      dist_two_of_triangle_free htri (backwards i)
        (by convert backwards (i-1) using 2; ring)
        (fun e => (even_ne i).2.1 (f.injective e))
    have hsub : ({i,i+2,i-2} : Finset (Fin m)) ⊆
        Finset.univ.filter ((fun x => Even (G.dist (f i) x)) ∘ f) := by
      intro j hj
      rcases (show j = i ∨ j = i+2 ∨ j = i-2 from by simpa using hj) with e | e | e
      · subst j; simp
      · subst j; simp [hp]
      · subst j; simp [hm']
    have hle := Finset.card_le_card hsub
    have hn := even_ne i
    simpa [Finset.card_insert_of_notMem, hn.1, hn.2.1, hn.2.2] using hle
  have external (x : V) (hx : x ∉ C) : 3 * (C.filter (fun v => G.Adj v x)).card ≤
      2 * (C.filter (fun v => G.dist v x = 2)).card := by
    let T := Finset.univ.filter (fun i : Fin m => G.Adj (f i) x)
    let D := Finset.univ.filter (fun i : Fin m => G.dist (f i) x = 2)
    rw [Finset.filter_map, Finset.filter_map, Finset.card_map, Finset.card_map]
    change 3 * T.card ≤ 2 * D.card
    have htouch {i : Fin m} (hi : i ∈ T) : G.Adj (f i) x := (Finset.mem_filter.mp hi).2
    have force {i j : Fin m} (hi : i ∈ T) (hj : j ∈ T) (hne : i ≠ j) :
        j = i+2 ∨ i = j+2 := h2 i j hne ⟨x,htouch hi,(htouch hj).symm⟩
    have hvertex (i : Fin m) : f i ≠ x := fun he =>
      hx (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,he⟩)
    have dist_at {i j : Fin m} (hi : i ∈ T) (ha : G.Adj (f j) (f i)) : j ∈ D :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        dist_two_of_triangle_free htri ha (htouch hi) (hvertex j)⟩
    by_cases hlarge : 1 < T.card
    · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hlarge
      obtain ⟨i,hi,hj⟩ : ∃ i : Fin m, i ∈ T ∧ i+2 ∈ T := by
        rcases force ha hb hab with e | e
        · exact ⟨a,ha,e ▸ hb⟩
        · exact ⟨b,hb,e ▸ ha⟩
      have hnot : i-2 ∉ T := by
        intro hn
        have hneq := (even_ne i).2.2
        rcases force hj hn hneq with he | he
        · apply hn₆
          apply add_left_cancel (a := i)
          calc
            i + 6 = ((i+2)+2)+2 := by ring
            _ = (i-2)+2 := congrArg (fun t => t+2) he.symm
            _ = i+0 := by ring
        · have he' : i+2 = i := by simpa using he
          exact (even_ne i).1 he'.symm
      have hs : T ⊆ ({i,i+2} : Finset (Fin m)) := by
        intro j hj'
        by_cases he : j = i
        · simp [he]
        · rcases force hi hj' (Ne.symm he) with e | e
          · simp [e]
          · have he' : j = i-2 := eq_sub_of_add_eq e.symm
            exact (hnot (he' ▸ hj')).elim
      have hTcard : T.card ≤ 2 := (Finset.card_le_card hs).trans Finset.card_le_two
      have htriD : ({i-1,i+1,i+3} : Finset (Fin m)) ⊆ D := by
        intro j hmj
        rcases (show j = i-1 ∨ j = i+1 ∨ j = i+3 from by simpa using hmj) with e | e | e
        · subst j; exact dist_at hi (backwards i).symm
        · subst j; exact dist_at hi (hcyc i).symm
        · subst j
          apply dist_at hj
          convert (hcyc (i+2)).symm using 2; ring
      have hDcard := Finset.card_le_card htriD
      have hne := triple_ne i
      simp [Finset.card_insert_of_notMem,hne.1,hne.2.1,hne.2.2] at hDcard
      omega
    · by_cases hempty : T.Nonempty
      · obtain ⟨i,hi⟩ := hempty
        have hpairD : ({i-1,i+1} : Finset (Fin m)) ⊆ D := by
          intro j hmj
          rcases (show j = i-1 ∨ j = i+1 from by simpa using hmj) with e | e
          · subst j; exact dist_at hi (backwards i).symm
          · subst j; exact dist_at hi (hcyc i).symm
        have hl := Finset.card_le_card hpairD
        rw [Finset.card_pair (triple_ne i).1] at hl
        omega
      · have he := Finset.not_nonempty_iff_eq_empty.mp hempty
        simp [he]
  have hspans : C = Finset.univ :=
    Graph189OddCycleCount.odd_cycle_core_spans h C (hc ▸ hm) hσ
      internal_neighbors internal_even external
  let L := (List.finRange m).map f
  have hcard : Fintype.card V = m := by rw [← Finset.card_univ,← hspans,hc]
  have hnodup : L.Nodup := (List.nodup_finRange m).map f.injective
  have hlen : L.length = m := by simp [L]
  have hne : L ≠ [] := by intro hnil; simp [hnil] at hlen; omega
  have hchain : L.IsChain G.Adj := by
    dsimp [L]
    rw [List.isChain_map,List.isChain_iff_getElem]
    intro i hi
    have hi' : i+1 < m := by simpa using hi
    have he : (List.finRange m)[i+1] = (List.finRange m)[i] + (1 : Fin m) := by
      apply Fin.ext
      simp only [List.getElem_finRange,Fin.val_add,Fin.val_one',Fin.val_cast]
      rw [Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt hi']
    rw [he]
    exact hcyc _
  exact Graph189Bipartite.hamiltonian_of_chain L hne hchain hnodup (hlen.trans hcard.symm)

end Graph189CyclicGeometry

namespace Graph189TriangleFree
open SimpleGraph
open scoped Fin.CommRing Fin.NatCast

private theorem cyclic_gap {m : ℕ} [NeZero m] {r : ℕ} (hr : r < m)
    {i j : Fin m} (hij : i < j)
    (hgap : j.val - i.val = r ∨ j.val - i.val = m-r) :
    j = i + (r : Fin m) ∨ i = j + (r : Fin m) := by
  have hi := i.isLt
  have hj := j.isLt
  change i.val < j.val at hij
  rcases hgap with hl | hl
  · left
    apply Fin.ext
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : i.val + r < m)]
    omega
  · right
    apply Fin.ext
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hr,
      Nat.mod_eq_sub_mod (by omega : m ≤ j.val+r), Nat.mod_eq_of_lt (by omega : j.val + r - m < m)]
    omega

private theorem traceable_nonbipartite {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.Connected) (hb : ¬ G.IsBipartite)
    (ht : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a,p,hp,hmin⟩ := Graph189ShortestOdd.exists_shortest h hb
  have hm := Graph189ShortestOdd.odd_ge_five p hp ht
  have : NeZero p.length := ⟨by omega⟩
  let f : Fin p.length ↪ V :=
    ⟨fun i => p.getVert i.val, Graph189ShortestOdd.shortest_index_injective p hp hmin⟩
  have hcyc (i : Fin p.length) : G.Adj (f i) (f (i+1)) := by
    have hi := i.isLt
    have hstep := p.adj_getVert_succ (i := i.val) hi
    change G.Adj (p.getVert i.val) (p.getVert (i+1).val)
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < p.length)]
    by_cases he : i.val+1 < p.length
    · rw [Nat.mod_eq_of_lt he]
      exact hstep
    · have hn : i.val + 1 = p.length := by omega
      rw [hn, Nat.mod_self, Walk.getVert_zero]
      rw [hn, Walk.getVert_length] at hstep
      exact hstep
  have h1 (i j : Fin p.length) (hh : G.Adj (f i) (f j)) : j = i+1 ∨ i = j+1 := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact cyclic_gap (by omega : 1 < p.length) hij
        ((Graph189ShortestOdd.short_detours p hp hmin hij j.isLt).1 hh)
    · exact (G.irrefl hh).elim
    · exact (cyclic_gap (by omega : 1 < p.length) hji
        ((Graph189ShortestOdd.short_detours p hp hmin hji i.isLt).1 hh.symm)).symm
  have h2 (i j : Fin p.length) (hne : i ≠ j)
      (hh : ∃ x, G.Adj (f i) x ∧ G.Adj x (f j)) : j = i+2 ∨ i = j+2 := by
    rcases lt_trichotomy i j with hij | he | hji
    · exact cyclic_gap (by omega : 2 < p.length) hij
        ((Graph189ShortestOdd.short_detours p hp hmin hij j.isLt).2 hh)
    · exact (hne he).elim
    · obtain ⟨x,ha,hb⟩ := hh
      exact (cyclic_gap (by omega : 2 < p.length) hji
        ((Graph189ShortestOdd.short_detours p hp hmin hji i.isLt).2 ⟨x,hb.symm,ha.symm⟩)).symm
  exact Graph189CyclicGeometry.traceable_of_geometry h ht hσ hm hp f hcyc h1 h2

/-- The full triangle-free case of DeLaViña's Written on the Wall II conjecture 189,
including nonbipartite graphs with four-cycles. -/
theorem hamiltonian {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.Connected)
    (ht : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases hb : G.IsBipartite
  · exact Graph189Bipartite.hamiltonian_bipartite G h hb hσ
  · apply traceable_nonbipartite h hb ht
    intro x
    exact (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)).trans hσ

end Graph189TriangleFree

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → G.diam = 3 →
    G.minDegree + secondSmallestDegree G + 1 < Fintype.card V →
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) →
    G.minDegree ≤ 2 →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → G.diam = 3 →
    G.minDegree + secondSmallestDegree G + 1 < Fintype.card V →
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) →
    3 ≤ G.minDegree →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.H1 := by
  intro hlow hhigh V _ _ _ G _ hc hd hmin hmax hdist hHall
  have hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree := by
    apply (Finset.max'_le_iff _ _).mpr
    intro t ht
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ht
    exact hdist v
  by_cases htri : ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c
  · by_cases hδ : G.minDegree ≤ 2
    · exact hlow G hc hd hmin hmax hdist hHall htri hδ
    · exact hhigh G hc hd hmin hmax hdist hHall htri (by omega)
  have hno : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c := by
    intro a b c hab hbc hac
    exact htri ⟨a,b,c,hab,hbc,hac⟩
  exact Graph189TriangleFree.hamiltonian G hc hno hσ

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1
