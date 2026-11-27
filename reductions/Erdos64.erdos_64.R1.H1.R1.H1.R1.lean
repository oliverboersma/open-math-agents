import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1
import Mathlib

/-!
# The connected bridgeless cubic case of Erdős–Gyárfás

The nonbipartite case remains H1. In the bipartite case, count incidences and apply Hall's
marriage theorem three times to split the edges into perfect matchings. Identify the two sides
along the first matching. The other two matchings now give permutations of the same set, and H2
requires the permutations to disagree in their order of application on at least one third of the points.

Four local commuting squares around a point force a 4-, 8-, or 16-cycle. The finite
certificate handles repeated vertex labels; reversing the two directions and interchanging
them covers all four orientations. Double-counting visits to the exceptional set gives the
one-third threshold. The global commuting and abelian-group cases follow as corollaries.

The parent bridge decomposition is due to @JamesSlash (PR #592). Ghaffari and Mostaghim,
Aequationes Math. 92 (2018), studied the Erdős–Gyárfás conjecture for dihedral and other Cayley
graphs. The three-translation argument here also allows noncyclic abelian groups.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
open SimpleGraph

/-- Connected, bridgeless, cubic graphs with an odd cycle. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ x, G.degree x = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) → ¬ G.IsBipartite →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- The normalized bipartite matching problem with a lower bound on the number of failures of commutation. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun a b : Bool × X =>
      a.1 = false ∧ b.1 = true ∧ (b.2 = a.2 ∨ b.2 = p a.2 ∨ b.2 = q a.2))


namespace LocalCommutation
open SimpleGraph
lemma route {X : Type*} (G : SimpleGraph (Bool × X)) (x : (Fin 10) → X)
    {n : ℕ} (hn : n=4 ∨ n=8 ∨ n=16) (w : Fin n → Bool × (Fin 10))
    (edges collisions : List (Fin 10 × Fin 10))
    (hwalk : ∀ i j, (cycleGraph n).Adj i j → (if (w i).1 == (w j).1 then false else if (w i).1 then edges.contains ((w j).2,(w i).2) else edges.contains ((w i).2,(w j).2)))
    (hpair : ∀ i j, i<j → (w i).1=(w j).1 →
      ((w i).2,(w j).2) ∈ collisions ∨ ((w j).2,(w i).2) ∈ collisions)
    (adj : ∀ e ∈ edges, G.Adj (false,x e.1) (true,x e.2))
    (recur : ∀ e ∈ collisions, x e.1 = x e.2 → (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let f (i : Fin n) : Bool × X := ((w i).1,x (w i).2)
  have edge {a b : Bool × (Fin 10)} (h : (if a.1 == b.1 then false else if a.1 then edges.contains (b.2,a.2) else edges.contains (a.2,b.2))) : G.Adj (a.1,x a.2) (b.1,x b.2) := by
    obtain ⟨i,a⟩ := a; obtain ⟨j,b⟩ := b
    cases i <;> cases j <;> simp at h
    · exact adj _ h
    · exact (adj _ h).symm
  let g : cycleGraph n →g G := ⟨f, fun h => edge (hwalk _ _ h)⟩
  by_cases hi : Function.Injective g
  · have hs : cycleGraph n ⊑ G := ⟨g.toCopy hi⟩
    rcases hn with rfl|rfl|rfl
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)
  · obtain ⟨i,j,h,hn'⟩ := Function.not_injective_iff.mp hi
    have bad (a b : Fin n) (lt : a<b) (e : g a = g b) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
      have s := congrArg Prod.fst e
      have r : x (w a).2 = x (w b).2 := congrArg Prod.snd e
      rcases hpair a b lt s with h | h
      · exact recur _ h r
      · exact recur _ h r.symm
    rcases lt_or_gt_of_ne hn' with hlt|hlt
    · exact bad i j hlt h
    · exact bad j i hlt h.symm

/-- Ten vertices of four oriented squares. A node identifies vertices whose labels
coincide. Identity, horizontal and vertical edges give an explicit closed walk;
if it repeats a vertex, congruence or injectivity forces a smaller quotient. -/
theorem shape0 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (x : (Fin 10) → X)
    (edge0 : p (x 0) = x 4)
    (edge1 : q (x 0) = x 1)
    (edge2 : p (x 1) = x 5)
    (edge3 : q (x 1) = x 2)
    (edge4 : p (x 2) = x 6)
    (edge5 : q (x 2) = x 3)
    (edge6 : p (x 3) = x 7)
    (edge7 : q (x 4) = x 5)
    (edge8 : p (x 5) = x 8)
    (edge9 : q (x 5) = x 6)
    (edge10 : p (x 6) = x 9)
    (edge11 : q (x 6) = x 7)
    (edge12 : q (x 8) = x 9)
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  have node0 (eq1 : x 1 = x 0) (eq2 : x 2 = x 0) (eq3 : x 3 = x 0) (eq4 : x 4 = x 0) (eq5 : x 5 = x 0) (eq6 : x 6 = x 0) (eq7 : x 7 = x 0) (eq8 : x 8 = x 0) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node1 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq4 : x 4 = x 0) (eq5 : x 5 = x 1) (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq8 : x 8 = x 1) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node2 (eq1 : x 1 = x 0) (eq2 : x 2 = x 0) (eq3 : x 3 = x 0) (eq5 : x 5 = x 4) (eq6 : x 6 = x 4) (eq7 : x 7 = x 4) (eq8 : x 8 = x 0) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : q (x 0) = x 0 := (edge1.trans eq1)
    exact False.elim ((sep (x 0)).2.1 (hy.trans hx.symm))
  have node3 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq4 : x 4 = x 1) (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 0) (eq8 : x 8 = x 1) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : p (x 0) = x 1 := (edge0.trans eq4)
    have hy : q (x 0) = x 1 := edge1
    exact False.elim ((sep (x 0)).2.2 (hx.trans hy.symm))
  have node4 (eq1 : x 1 = x 0) (eq2 : x 2 = x 0) (eq3 : x 3 = x 0) (eq5 : x 5 = x 4) (eq6 : x 6 = x 4) (eq7 : x 7 = x 4) (eq9 : x 9 = x 8) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : q (x 0) = x 0 := (edge1.trans eq1)
    exact False.elim ((sep (x 0)).2.1 (hy.trans hx.symm))
  have node5 (eq3 : x 3 = x 0) (eq4 : x 4 = x 0) (eq5 : x 5 = x 1) (eq6 : x 6 = x 2) (eq7 : x 7 = x 0) (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node6 (eq3 : x 3 = x 0) (eq4 : x 4 = x 2) (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 2) (eq8 : x 8 = x 2) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 1) = x 0 := (edge2.trans eq5)
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      exact node0 hit.symm ((eq4.symm.trans t0).trans eq5) eq3 (t0.trans eq5) eq5 (eq6.trans hit.symm) (((eq7.trans eq4.symm).trans t0).trans eq5) (((eq8.trans eq4.symm).trans t0).trans eq5) eq9
  have node7 (eq3 : x 3 = x 0) (eq4 : x 4 = x 1) (eq5 : x 5 = x 2) (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq8 : x 8 = x 0) (eq9 : x 9 = x 1) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : p (x 0) = x 1 := (edge0.trans eq4)
    have hy : q (x 0) = x 1 := edge1
    exact False.elim ((sep (x 0)).2.2 (hx.trans hy.symm))
  have node8 (eq4 : x 4 = x 2) (eq5 : x 5 = x 3) (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,2), (true,2)]
      [(0,0), (2,0), (2,2), (0,2)] [(0,2)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 2) = x 0 := (edge4.trans eq6)
        exact e ▸ pAdj (x 2)
      · exact idAdj _
      · have e : p (x 0) = x 2 := (edge0.trans eq4)
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
      exact node1 hit.symm t0.symm (eq4.trans hit.symm) (eq5.trans t0.symm) eq6 eq7 eq8 (eq9.trans hit.symm)
  have node9 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq6 : x 6 = x 4) (eq7 : x 7 = x 5) (eq8 : x 8 = x 0) (eq9 : x 9 = x 1) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : q (x 1) = x 0 := (edge3.trans eq2)
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      exact node2 hit.symm eq2 (eq3.trans hit.symm) t0.symm eq6 (eq7.trans t0.symm) eq8 (eq9.trans hit.symm)
  have node10 (eq4 : x 4 = x 0) (eq5 : x 5 = x 1) (eq6 : x 6 = x 2) (eq7 : x 7 = x 3) (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : id (x 0) = x 0 := rfl
    have hy : p (x 0) = x 0 := (edge0.trans eq4)
    exact False.elim ((sep (x 0)).1 (hy.trans hx.symm))
  have node11 (eq4 : x 4 = x 3) (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 2) (eq8 : x 8 = x 3) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 1) = x 0 := (edge2.trans eq5)
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      have t1 : x 0 = x 2 := (p.injective (edge0.trans ((((t0.trans eq5).trans hit).trans eq6.symm).trans edge4.symm)))
      exact node0 hit.symm t1.symm ((eq4.symm.trans t0).trans eq5) (t0.trans eq5) eq5 (eq6.trans hit.symm) (eq7.trans t1.symm) (((eq8.trans eq4.symm).trans t0).trans eq5) eq9
  have node12 (eq5 : x 5 = x 0) (eq6 : x 6 = x 1) (eq7 : x 7 = x 2) (eq8 : x 8 = x 4) (eq9 : x 9 = x 0) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 1) = x 0 := (edge2.trans eq5)
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      have t1 : x 0 = x 2 := (p.injective (edge0.trans ((((t0.trans eq5).trans hit).trans eq6.symm).trans edge4.symm)))
      have t2 : x 0 = x 3 := (p.injective (edge0.trans ((((t0.trans eq5).trans t1).trans eq7.symm).trans edge6.symm)))
      exact node0 hit.symm t1.symm t2.symm (t0.trans eq5) eq5 (eq6.trans hit.symm) (eq7.trans t1.symm) ((eq8.trans t0).trans eq5) eq9
  have node13 (eq4 : x 4 = x 1) (eq5 : x 5 = x 2) (eq6 : x 6 = x 3) (eq8 : x 8 = x 3) (eq9 : x 9 = x 7) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    have hx : p (x 0) = x 1 := (edge0.trans eq4)
    have hy : q (x 0) = x 1 := edge1
    exact False.elim ((sep (x 0)).2.2 (hx.trans hy.symm))
  have node14 (eq2 : x 2 = x 0) (eq3 : x 3 = x 1) (eq6 : x 6 = x 4) (eq7 : x 7 = x 5) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,0), (false,1), (true,1)]
      [(0,0), (1,0), (1,1), (0,1)] [(0,1)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : q (x 1) = x 0 := (edge3.trans eq2)
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
      have t1 : x 8 = x 9 := (edge8.symm.trans ((congrArg p (t0.symm.trans eq6.symm)).trans edge10))
      exact node4 hit.symm eq2 (eq3.trans hit.symm) t0.symm eq6 (eq7.trans t0.symm) t1.symm
  have node15 (eq6 : x 6 = x 0) (eq7 : x 7 = x 1) (eq9 : x 9 = x 4) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,0), (false,2), (true,2), (false,1), (true,5), (false,4), (true,4)]
      [(0,0), (2,0), (2,2), (1,2), (1,5), (4,5), (4,4), (0,4)] [(0,1), (0,2), (0,4), (0,5), (1,2), (1,4), (2,4), (2,5), (4,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 2) = x 0 := (edge4.trans eq6)
        exact e ▸ pAdj (x 2)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
      · have e : q (x 4) = x 5 := edge7
        exact e ▸ qAdj (x 4)
      · exact idAdj _
      · have e : p (x 0) = x 4 := edge0
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 0 = x 5 := (q.injective (edge1.trans ((hit.symm.trans eq6.symm).trans edge9.symm)))
        have t4 : x 0 = x 8 := (q.injective (edge1.trans ((((hit.symm.trans t3).trans t0.symm).trans eq9.symm).trans edge12.symm)))
        exact node0 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) (t0.trans t3.symm) t3.symm eq6 (eq7.trans hit.symm) t4.symm ((eq9.trans t0).trans t3.symm)
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 1 = x 5 := (edge1.symm.trans ((congrArg q (eq6.symm.trans t0.symm)).trans edge7))
        have t3 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t2).trans edge8))
        exact node1 hit.symm t1.symm (t0.trans eq6) t2.symm eq6 eq7 (t3.symm.trans t2.symm) ((eq9.trans t0).trans eq6)
      · have t0 : x 0 = x 2 := (p.injective (edge0.trans ((hit.symm.trans eq6.symm).trans edge4.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 1 = x 5 := (edge1.symm.trans ((congrArg q hit).trans edge7))
        have t3 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t2).trans edge8))
        exact node1 t0.symm t1.symm hit.symm t2.symm eq6 eq7 (t3.symm.trans t2.symm) (eq9.trans hit.symm)
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 1 = x 2 := (p.injective (edge2.trans ((hit.symm.trans eq6.symm).trans edge4.symm)))
        have t3 : x 1 = x 3 := (p.injective (edge2.trans ((((hit.symm.trans eq6.symm).trans t1.symm).trans eq7.symm).trans edge6.symm)))
        have t4 : x 5 = x 8 := (edge2.symm.trans ((congrArg p ((t1.trans eq6).trans hit)).trans edge8))
        exact node0 (t1.trans eq6) ((t2.symm.trans t1).trans eq6) ((t3.symm.trans t1).trans eq6) ((t0.trans t4.symm).trans hit.symm) hit.symm eq6 ((eq7.trans t1).trans eq6) (t4.symm.trans hit.symm) (((eq9.trans t0).trans t4.symm).trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 0 = x 5 := (q.injective (edge1.trans ((t0.symm.trans eq6.symm).trans edge9.symm)))
        have t3 : x 5 = x 8 := (edge2.symm.trans ((congrArg p (t0.symm.trans t2)).trans edge8))
        have t4 : x 5 = x 9 := (edge2.symm.trans ((congrArg p (t0.symm.trans eq6.symm)).trans edge10))
        exact node0 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) ((eq9.symm.trans t4.symm).trans t2.symm) t2.symm eq6 (eq7.trans t0.symm) (t3.symm.trans t2.symm) (t4.symm.trans t2.symm)
      · have t0 : x 0 = x 3 := (p.injective (edge0.trans ((hit.symm.trans eq7.symm).trans edge6.symm)))
        have t1 : x 0 = x 8 := (q.injective (edge1.trans ((hit.trans eq9.symm).trans edge12.symm)))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q hit).trans edge7))
        exact node7 t0.symm hit.symm t2.symm eq6 eq7 t1.symm (eq9.trans hit.symm)
      · have t0 : x 1 = x 8 := (q.injective (edge3.trans ((hit.trans eq9.symm).trans edge12.symm)))
        have t1 : x 3 = x 5 := (edge5.symm.trans ((congrArg q hit).trans edge7))
        exact node8 hit.symm t1.symm eq6 eq7 t0.symm (eq9.trans hit.symm)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        exact node7 (t2.trans eq6) t0.symm hit.symm eq6 eq7 (t1.symm.trans eq6) (eq9.trans t0.symm)
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans (hit.trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans t1)).trans edge5))
        have t3 : x 0 = x 5 := (q.injective (edge1.trans ((t0.symm.trans eq6.symm).trans edge9.symm)))
        have t4 : x 0 = x 8 := (q.injective (edge1.trans ((((t0.symm.trans t3).trans hit.symm).trans eq9.symm).trans edge12.symm)))
        exact node0 t0.symm (t1.symm.trans t0.symm) (t2.symm.trans t0.symm) (hit.trans t3.symm) t3.symm eq6 (eq7.trans t0.symm) t4.symm ((eq9.trans hit).trans t3.symm)
  have node16 (eq4 : x 4 = x 2) (eq5 : x 5 = x 3) (eq8 : x 8 = x 7) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,0), (true,1), (false,1), (true,2)]
      [(0,1), (1,1), (1,2), (0,2)] [(0,1), (1,2)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 0) = x 2 := (edge0.trans eq4)
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 6 := (edge1.symm.trans ((congrArg q (((hit.trans t1).trans eq4.symm).trans t0)).trans edge9))
        have t3 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (hit.trans t2)).trans edge11))
        have t4 : x 1 = x 9 := (edge1.symm.trans ((congrArg q ((hit.trans t3).trans eq8.symm)).trans edge12))
        exact node0 hit.symm (t1.symm.trans hit.symm) ((((eq5.symm.trans t0.symm).trans eq4).trans t1.symm).trans hit.symm) ((eq4.trans t1.symm).trans hit.symm) (((t0.symm.trans eq4).trans t1.symm).trans hit.symm) (t2.symm.trans hit.symm) (t3.symm.trans hit.symm) ((eq8.trans t3.symm).trans hit.symm) (t4.symm.trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 1 = x 6 := (edge1.symm.trans ((congrArg q ((t0.trans t1).trans eq5.symm)).trans edge9))
        have t3 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (t0.trans t2)).trans edge11))
        have t4 : x 1 = x 9 := (edge1.symm.trans ((congrArg q ((t0.trans t3).trans eq8.symm)).trans edge12))
        exact node0 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) ((eq4.trans hit.symm).trans t0.symm) ((eq5.trans t1.symm).trans t0.symm) (t2.symm.trans t0.symm) (t3.symm.trans t0.symm) ((eq8.trans t3.symm).trans t0.symm) (t4.symm.trans t0.symm)
  have node17 (eq3 : x 3 = x 0) (eq7 : x 7 = x 4) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,0), (false,2), (true,2), (false,1), (true,5), (false,4), (true,4)]
      [(0,0), (2,0), (2,2), (1,2), (1,5), (4,5), (4,4), (0,4)] [(0,1), (0,2), (0,4), (0,5), (1,2), (1,4), (2,4), (2,5), (4,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : q (x 2) = x 0 := (edge5.trans eq3)
        exact e ▸ qAdj (x 2)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
      · have e : q (x 4) = x 5 := edge7
        exact e ▸ qAdj (x 4)
      · exact idAdj _
      · have e : p (x 0) = x 4 := edge0
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 hit.symm (t1.symm.trans hit.symm) eq3 t0.symm (t2.symm.trans t0.symm) eq7 t3.symm
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p ((t1.trans eq3).trans hit)).trans edge4))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 (t1.trans eq3) hit.symm eq3 (t2.trans t0.symm) t0.symm eq7 t3.symm
      · have t0 : x 1 = x 5 := (edge1.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t0).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (t0.trans t1)).trans edge12))
        exact node5 eq3 hit.symm t0.symm t2.symm (eq7.trans hit.symm) (t1.symm.trans t0.symm) t3.symm
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node6 eq3 (eq7.symm.trans t3.symm) hit.symm t1.symm t3.symm ((t0.symm.trans eq7.symm).trans t3.symm) (t2.symm.trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 5 = x 6 := (edge2.symm.trans ((congrArg p hit).trans edge4))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p (t0.symm.trans eq3.symm)).trans edge6))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t1).trans edge10))
        exact node4 t0.symm (hit.symm.trans t0.symm) eq3 (t2.trans eq7) ((t1.symm.trans t2).trans eq7) eq7 t3.symm
      · have t0 : x 0 = x 6 := (q.injective (edge1.trans ((hit.trans eq7.symm).trans edge11.symm)))
        have t1 : x 2 = x 5 := (edge3.symm.trans ((congrArg q hit).trans edge7))
        have t2 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t1).trans edge8))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p (eq3.trans t0)).trans edge10))
        exact node7 eq3 hit.symm t1.symm t0.symm (eq7.trans hit.symm) (t2.symm.trans t0.symm) ((t3.symm.trans eq7).trans hit.symm)
      · have t0 : x 1 = x 6 := (q.injective (edge3.trans ((hit.trans eq7.symm).trans edge11.symm)))
        have t1 : x 3 = x 5 := (edge5.symm.trans ((congrArg q hit).trans edge7))
        have t2 : x 7 = x 8 := (edge6.symm.trans ((congrArg p t1).trans edge8))
        have t3 : x 5 = x 9 := (edge7.symm.trans ((congrArg q (eq7.symm.trans t2)).trans edge12))
        exact node6 eq3 hit.symm (t1.symm.trans eq3) t0.symm (eq7.trans hit.symm) ((t2.symm.trans eq7).trans hit.symm) ((t3.symm.trans t1.symm).trans eq3)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node7 eq3 t0.symm hit.symm (t2.symm.trans eq3) (eq7.trans t0.symm) ((t1.symm.trans t2.symm).trans eq3) ((t3.symm.trans eq7).trans t0.symm)
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans (hit.trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t3 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 t0.symm (t1.symm.trans t0.symm) eq3 hit.symm (t2.symm.trans hit.symm) eq7 t3.symm
  have node18 (eq8 : x 8 = x 0) (eq9 : x 9 = x 1) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,0), (false,5), (true,6), (false,2), (true,2), (false,1), (true,1)]
      [(0,0), (5,0), (5,6), (2,6), (2,2), (1,2), (1,1), (0,1)] [(0,1), (0,2), (0,5), (0,6), (1,2), (1,5), (1,6), (2,5), (2,6)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 5) = x 0 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · have e : q (x 5) = x 6 := edge9
        exact e ▸ qAdj (x 5)
      · have e : p (x 2) = x 6 := edge4
        exact e ▸ pAdj (x 2)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t4 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t2).trans edge6))
        exact node2 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) t0.symm (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) eq8 (eq9.trans hit.symm)
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        exact node9 hit.symm t1.symm t0.symm t2.symm eq8 eq9
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 5 := (edge1.symm.trans ((congrArg q (eq8.symm.trans t0.symm)).trans edge7))
        have t2 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 1 = x 7 := (edge1.symm.trans ((congrArg q ((hit.trans t1.symm).trans t2)).trans edge11))
        have t4 : x 1 = x 2 := (p.injective (edge2.trans ((t1.symm.trans t2).trans edge4.symm)))
        have t5 : x 1 = x 3 := (p.injective (edge2.trans ((t1.symm.trans t3).trans edge6.symm)))
        exact node0 (t1.trans hit.symm) ((t4.symm.trans t1).trans hit.symm) ((t5.symm.trans t1).trans hit.symm) (t0.trans eq8) hit.symm ((t2.symm.trans t1).trans hit.symm) ((t3.symm.trans t1).trans hit.symm) eq8 ((eq9.trans t1).trans hit.symm)
      · have t0 : x 4 = x 9 := (edge0.symm.trans ((congrArg p hit).trans edge10))
        have t1 : x 1 = x 7 := (edge1.symm.trans ((congrArg q hit).trans edge11))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q (eq9.symm.trans t0.symm)).trans edge7))
        have t3 : x 3 = x 6 := (edge5.symm.trans ((congrArg q t2).trans edge9))
        exact node7 (t3.trans hit.symm) (t0.trans eq9) t2.symm hit.symm t1.symm eq8 eq9
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p hit).trans edge4))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t2.trans edge9.symm)))
        exact node2 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) t4.symm (t2.symm.trans t4.symm) (t3.symm.trans t4.symm) eq8 (eq9.trans t0.symm)
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 1 = x 6 := (p.injective (edge2.trans ((hit.symm.trans eq9.symm).trans edge10.symm)))
        have t3 : x 2 = x 5 := (edge3.symm.trans ((congrArg q (((hit.trans t1).trans eq8).trans t0)).trans edge7))
        have t4 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t2).trans edge11))
        have t5 : x 2 = x 3 := (p.injective (edge4.trans ((((t2.symm.trans hit).trans t3.symm).trans t4).trans edge6.symm)))
        exact node0 ((hit.trans t1).trans eq8) ((t3.trans t1).trans eq8) (((t5.symm.trans t3).trans t1).trans eq8) t0.symm (t1.trans eq8) (((t2.symm.trans hit).trans t1).trans eq8) (((t4.symm.trans t3).trans t1).trans eq8) eq8 (((eq9.trans hit).trans t1).trans eq8)
      · have t0 : x 0 = x 5 := (q.injective (edge1.trans (hit.trans edge9.symm)))
        have t1 : x 1 = x 5 := (p.injective (edge2.trans ((t0.symm.trans eq8.symm).trans edge8.symm)))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t1).trans edge9))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q hit).trans edge11))
        have t4 : x 2 = x 3 := (p.injective (edge4.trans ((t2.symm.trans t3).trans edge6.symm)))
        have t5 : x 2 = x 4 := (q.injective (edge5.trans ((((t4.symm.trans t2).trans hit.symm).trans t1).trans edge7.symm)))
        exact node0 (t1.trans t0.symm) (((t2.trans hit.symm).trans t1).trans t0.symm) ((((t4.symm.trans t2).trans hit.symm).trans t1).trans t0.symm) ((((t5.symm.trans t2).trans hit.symm).trans t1).trans t0.symm) t0.symm ((hit.symm.trans t1).trans t0.symm) ((((t3.symm.trans t2).trans hit.symm).trans t1).trans t0.symm) eq8 ((eq9.trans t1).trans t0.symm)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node7 ((t2.trans t1).trans eq8) t0.symm hit.symm (t1.trans eq8) (t3.trans eq9) eq8 eq9
      · have t0 : x 1 = x 5 := (q.injective (edge3.trans (hit.trans edge9.symm)))
        have t1 : x 6 = x 9 := (edge4.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q (((hit.trans t1).trans eq9).trans t0)).trans edge9))
        have t3 : x 3 = x 7 := (edge5.symm.trans ((congrArg q hit).trans edge11))
        have t4 : x 2 = x 8 := (q.injective (edge5.trans ((t2.trans t1).trans edge12.symm)))
        have t5 : x 4 = x 5 := (q.injective (edge7.trans (((t0.symm.trans eq9.symm).trans t1.symm).trans edge9.symm)))
        exact node0 ((((eq9.symm.trans t1.symm).trans hit.symm).trans t4).trans eq8) (t4.trans eq8) (((t2.trans hit.symm).trans t4).trans eq8) ((((((t5.trans t0.symm).trans eq9.symm).trans t1.symm).trans hit.symm).trans t4).trans eq8) (((((t0.symm.trans eq9.symm).trans t1.symm).trans hit.symm).trans t4).trans eq8) ((hit.symm.trans t4).trans eq8) ((((t3.symm.trans t2).trans hit.symm).trans t4).trans eq8) eq8 (((t1.symm.trans hit.symm).trans t4).trans eq8)
  have node19 (eq8 : x 8 = x 1) (eq9 : x 9 = x 2) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,1), (true,1), (false,5), (true,5)]
      [(1,1), (5,1), (5,5), (1,5)] [(1,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact idAdj _
      · have e : p (x 5) = x 1 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · exact idAdj _
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl
      have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
      have t1 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
      have t2 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t1).trans edge11))
      exact node10 t0.symm hit.symm t1.symm t2.symm eq8 eq9
  have node20 (eq8 : x 8 = x 2) (eq9 : x 9 = x 3) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,1), (true,2), (false,5), (true,5)]
      [(1,2), (5,2), (5,5), (1,5)] [(1,5), (2,5)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · have e : p (x 5) = x 2 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · exact idAdj _
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 2 = x 3 := (edge3.symm.trans ((congrArg q ((hit.trans t1).trans eq8)).trans edge5))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans ((eq8.symm.trans t1.symm).trans edge7.symm)))
        have t4 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
        have t5 : x 2 = x 7 := (edge3.symm.trans ((congrArg q (((hit.trans t1).trans eq8).trans t4)).trans edge11))
        exact node0 (t3.trans t0.symm) ((((eq8.symm.trans t1.symm).trans hit.symm).trans t3).trans t0.symm) (((((t2.symm.trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm) t0.symm ((hit.symm.trans t3).trans t0.symm) (((((t4.symm.trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm) (((((t5.symm.trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm) (((t1.symm.trans hit.symm).trans t3).trans t0.symm) ((((((eq9.trans t2.symm).trans eq8.symm).trans t1.symm).trans hit.symm).trans t3).trans t0.symm)
      · have t0 : x 1 = x 5 := (p.injective (edge2.trans ((hit.symm.trans eq8.symm).trans edge8.symm)))
        have t1 : x 2 = x 3 := (edge3.symm.trans ((congrArg q (t0.trans hit.symm)).trans edge5))
        have t2 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t3 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t4 : x 2 = x 7 := (edge3.symm.trans ((congrArg q ((t0.trans hit.symm).trans t3)).trans edge11))
        have t5 : x 0 = x 1 := (p.injective (edge0.trans ((t2.symm.trans t0).trans edge2.symm)))
        exact node0 t5.symm ((hit.trans t0.symm).trans t5.symm) (((t1.symm.trans hit).trans t0.symm).trans t5.symm) (t2.symm.trans t5.symm) (t0.symm.trans t5.symm) (((t3.symm.trans hit).trans t0.symm).trans t5.symm) (((t4.symm.trans hit).trans t0.symm).trans t5.symm) (((eq8.trans hit).trans t0.symm).trans t5.symm) ((((eq9.trans t1.symm).trans hit).trans t0.symm).trans t5.symm)
  have node21 (eq8 : x 8 = x 3) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=4) (by decide) ![(false,2), (true,3), (false,5), (true,6)]
      [(2,3), (5,3), (5,6), (2,6)] [(2,5), (3,6)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · have e : q (x 2) = x 3 := edge5
        exact e ▸ qAdj (x 2)
      · have e : p (x 5) = x 3 := (edge8.trans eq8)
        exact e ▸ pAdj (x 5)
      · have e : q (x 5) = x 6 := edge9
        exact e ▸ qAdj (x 5)
      · have e : p (x 2) = x 6 := edge4
        exact e ▸ pAdj (x 2)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 7 = x 9 := (edge6.symm.trans ((congrArg p (eq8.symm.trans t1.symm)).trans edge10))
        exact node13 t0.symm hit.symm (t1.trans eq8) eq8 t2.symm
      · have t0 : x 2 = x 5 := (p.injective (edge4.trans ((hit.symm.trans eq8.symm).trans edge8.symm)))
        have t1 : x 7 = x 9 := (edge6.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 1 = x 4 := (q.injective (edge3.trans (t0.trans edge7.symm)))
        exact node13 t2.symm t0.symm hit.symm eq8 t1.symm
  have node22 (eq4 : x 4 = x 3) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=8) (by decide) ![(false,0), (true,1), (false,1), (true,5), (false,5), (true,6), (false,2), (true,3)]
      [(0,1), (1,1), (1,5), (5,5), (5,6), (2,6), (2,3), (0,3)] [(0,1), (0,2), (0,5), (1,2), (1,3), (1,5), (1,6), (2,5), (3,5), (3,6), (5,6)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
      · exact idAdj _
      · have e : p (x 1) = x 5 := edge2
        exact e ▸ pAdj (x 1)
      · exact idAdj _
      · have e : q (x 5) = x 6 := edge9
        exact e ▸ qAdj (x 5)
      · have e : p (x 2) = x 6 := edge4
        exact e ▸ pAdj (x 2)
      · have e : q (x 2) = x 3 := edge5
        exact e ▸ qAdj (x 2)
      · have e : p (x 0) = x 3 := (edge0.trans eq4)
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 1 = x 6 := (edge1.symm.trans ((congrArg q (((hit.trans t2).trans eq4.symm).trans t0)).trans edge9))
        have t4 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (hit.trans t3)).trans edge11))
        have t5 : x 5 = x 8 := (edge2.symm.trans ((congrArg p ((t2.trans eq4.symm).trans t0)).trans edge8))
        have t6 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t3).trans edge10))
        exact node0 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) ((eq4.trans t2.symm).trans hit.symm) (((t0.symm.trans eq4).trans t2.symm).trans hit.symm) (t3.symm.trans hit.symm) (t4.symm.trans hit.symm) ((((t5.symm.trans t0.symm).trans eq4).trans t2.symm).trans hit.symm) ((((t6.symm.trans t0.symm).trans eq4).trans t2.symm).trans hit.symm)
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 0 = x 5 := (q.injective (edge1.trans (((t1.trans eq4.symm).trans t0).trans edge9.symm)))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 5 = x 9 := (edge2.symm.trans ((congrArg p ((t1.trans eq4.symm).trans t0)).trans edge10))
        have t5 : x 1 = x 8 := (q.injective (edge3.trans (((hit.symm.trans t2).trans t4).trans edge12.symm)))
        exact node3 hit.symm t1.symm (eq4.trans t1.symm) t2.symm ((t0.symm.trans eq4).trans t1.symm) (t3.symm.trans t2.symm) t5.symm (t4.symm.trans t2.symm)
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node11 eq4 hit.symm t1.symm t3.symm (t0.symm.trans eq4) (t2.symm.trans hit.symm)
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 1 = x 5 := (edge1.symm.trans ((congrArg q ((t0.trans t1).trans eq4.symm)).trans edge7))
        have t3 : x 1 = x 6 := (edge1.symm.trans ((congrArg q (t0.trans t2)).trans edge9))
        have t4 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (t0.trans t3)).trans edge11))
        have t5 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t2).trans edge8))
        have t6 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t3).trans edge10))
        exact node0 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) ((eq4.trans t1.symm).trans t0.symm) (t2.symm.trans t0.symm) (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) ((t5.symm.trans t2.symm).trans t0.symm) ((t6.symm.trans t2.symm).trans t0.symm)
      · have t0 : x 0 = x 2 := (q.injective (edge1.trans (hit.trans edge5.symm)))
        have t1 : x 5 = x 7 := (edge2.symm.trans ((congrArg p hit).trans edge6))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q (hit.trans eq4.symm)).trans edge7))
        have t3 : x 1 = x 6 := (q.injective (edge3.trans ((t2.trans t1).trans edge11.symm)))
        have t4 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t2).trans edge8))
        have t5 : x 7 = x 9 := (edge6.symm.trans ((congrArg p (hit.symm.trans t3)).trans edge10))
        exact node3 t0.symm hit.symm (eq4.trans hit.symm) (t2.symm.trans t0.symm) t3.symm ((t1.symm.trans t2.symm).trans t0.symm) (t4.symm.trans t3.symm) (((t5.symm.trans t1.symm).trans t2.symm).trans t0.symm)
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (hit.trans t1)).trans edge12))
        have t4 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t2).trans edge11))
        exact node5 (eq4.symm.trans t0.symm) t0.symm hit.symm t2.symm ((t4.symm.trans eq4.symm).trans t0.symm) (t1.symm.trans hit.symm) t3.symm
      · have t0 : x 0 = x 5 := (q.injective (edge1.trans (hit.trans edge9.symm)))
        have t1 : x 5 = x 9 := (edge2.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 2 = x 7 := (edge3.symm.trans ((congrArg q hit).trans edge11))
        have t3 : x 4 = x 8 := (q.injective (edge7.trans (t1.trans edge12.symm)))
        exact node11 eq4 t0.symm hit.symm t2.symm (t3.symm.trans eq4) (t1.symm.trans t0.symm)
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        have t4 : x 5 = x 7 := (edge7.symm.trans ((congrArg q (eq4.trans t2)).trans edge11))
        have t5 : x 0 = x 2 := (p.injective (edge0.trans ((eq4.trans t2).trans edge4.symm)))
        exact node3 t5.symm (eq4.symm.trans t0.symm) t0.symm (hit.symm.trans t5.symm) ((t2.symm.trans eq4.symm).trans t0.symm) ((t4.symm.trans hit.symm).trans t5.symm) (((t1.symm.trans t2.symm).trans eq4.symm).trans t0.symm) (((t3.symm.trans t4.symm).trans hit.symm).trans t5.symm)
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans ((eq4.trans hit).trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans t1)).trans edge5))
        have t3 : x 1 = x 6 := (edge1.symm.trans ((congrArg q ((t0.trans t2).trans hit)).trans edge9))
        have t4 : x 1 = x 7 := (edge1.symm.trans ((congrArg q (t0.trans t3)).trans edge11))
        have t5 : x 5 = x 8 := (edge2.symm.trans ((congrArg p (t2.trans hit)).trans edge8))
        have t6 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t3).trans edge10))
        exact node0 t0.symm (t1.symm.trans t0.symm) (t2.symm.trans t0.symm) ((eq4.trans t2.symm).trans t0.symm) ((hit.symm.trans t2.symm).trans t0.symm) (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) (((t5.symm.trans hit.symm).trans t2.symm).trans t0.symm) (((t6.symm.trans hit.symm).trans t2.symm).trans t0.symm)
      · have t0 : x 0 = x 2 := (p.injective (edge0.trans ((eq4.trans hit).trans edge4.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 0 = x 5 := (q.injective (edge1.trans ((t1.trans hit).trans edge9.symm)))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 5 = x 9 := (edge2.symm.trans ((congrArg p (t1.trans hit)).trans edge10))
        have t5 : x 1 = x 8 := (q.injective (edge3.trans (((t0.symm.trans t2).trans t4).trans edge12.symm)))
        exact node3 t0.symm t1.symm (eq4.trans t1.symm) t2.symm (hit.symm.trans t1.symm) (t3.symm.trans t2.symm) t5.symm (t4.symm.trans t2.symm)
      · have t0 : x 1 = x 2 := (p.injective (edge2.trans (hit.trans edge4.symm)))
        have t1 : x 2 = x 3 := (edge3.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 2 = x 5 := (edge3.symm.trans ((congrArg q ((t0.trans t1).trans eq4.symm)).trans edge7))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q ((t0.trans t2).trans hit)).trans edge11))
        have t4 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t2).trans edge8))
        have t5 : x 6 = x 9 := (edge4.symm.trans ((congrArg p (t2.trans hit)).trans edge10))
        have t6 : x 0 = x 1 := (p.injective (edge0.trans (((eq4.trans t1.symm).trans t2).trans edge2.symm)))
        exact node0 t6.symm (t0.symm.trans t6.symm) ((t1.symm.trans t0.symm).trans t6.symm) (((eq4.trans t1.symm).trans t0.symm).trans t6.symm) ((t2.symm.trans t0.symm).trans t6.symm) (((hit.symm.trans t2.symm).trans t0.symm).trans t6.symm) ((t3.symm.trans t0.symm).trans t6.symm) ((((t4.symm.trans hit.symm).trans t2.symm).trans t0.symm).trans t6.symm) ((((t5.symm.trans hit.symm).trans t2.symm).trans t0.symm).trans t6.symm)
  have node23 : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    apply route G x (n:=16) (by decide) ![(false,0), (true,1), (false,1), (true,2), (false,2), (true,3), (false,3), (true,7), (false,6), (true,9), (false,8), (true,8), (false,5), (true,5), (false,4), (true,4)]
      [(0,1), (1,1), (1,2), (2,2), (2,3), (3,3), (3,7), (6,7), (6,9), (8,9), (8,8), (5,8), (5,5), (4,5), (4,4), (0,4)] [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,8), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (4,5), (4,6), (4,7), (4,8), (4,9), (5,6), (5,7), (5,8), (5,9), (6,8), (7,8), (7,9), (8,9)] (by decide) (by decide)
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have e : q (x 0) = x 1 := edge1
        exact e ▸ qAdj (x 0)
      · exact idAdj _
      · have e : q (x 1) = x 2 := edge3
        exact e ▸ qAdj (x 1)
      · exact idAdj _
      · have e : q (x 2) = x 3 := edge5
        exact e ▸ qAdj (x 2)
      · exact idAdj _
      · have e : p (x 3) = x 7 := edge6
        exact e ▸ pAdj (x 3)
      · have e : q (x 6) = x 7 := edge11
        exact e ▸ qAdj (x 6)
      · have e : p (x 6) = x 9 := edge10
        exact e ▸ pAdj (x 6)
      · have e : q (x 8) = x 9 := edge12
        exact e ▸ qAdj (x 8)
      · exact idAdj _
      · have e : p (x 5) = x 8 := edge8
        exact e ▸ pAdj (x 5)
      · exact idAdj _
      · have e : q (x 4) = x 5 := edge7
        exact e ▸ qAdj (x 4)
      · exact idAdj _
      · have e : p (x 0) = x 4 := edge0
        exact e ▸ pAdj (x 0)
    · intro e he hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have t0 : x 4 = x 5 := (edge0.symm.trans ((congrArg p hit).trans edge2))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q hit).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (hit.trans t1)).trans edge5))
        have t3 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t4 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t2).trans edge6))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t3).trans edge10))
        exact node4 hit.symm (t1.symm.trans hit.symm) (t2.symm.trans hit.symm) t0.symm (t3.symm.trans t0.symm) (t4.symm.trans t0.symm) t5.symm
      · have t0 : x 4 = x 6 := (edge0.symm.trans ((congrArg p hit).trans edge4))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q hit).trans edge5))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        exact node14 hit.symm t1.symm t0.symm t2.symm
      · have t0 : x 4 = x 7 := (edge0.symm.trans ((congrArg p hit).trans edge6))
        exact node17 hit.symm t0.symm
      · have t0 : x 1 = x 5 := (edge1.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p t0).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (t0.trans t1)).trans edge12))
        have t4 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t2).trans edge11))
        exact node10 hit.symm t0.symm t2.symm t4.symm (t1.symm.trans t0.symm) t3.symm
      · have t0 : x 4 = x 8 := (edge0.symm.trans ((congrArg p hit).trans edge8))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q hit).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node12 hit.symm t1.symm t3.symm t0.symm (t2.symm.trans hit.symm)
      · have t0 : x 4 = x 9 := (edge0.symm.trans ((congrArg p hit).trans edge10))
        have t1 : x 1 = x 7 := (edge1.symm.trans ((congrArg q hit).trans edge11))
        exact node15 hit.symm t1.symm t0.symm
      · have t0 : x 1 = x 9 := (edge1.symm.trans ((congrArg q hit).trans edge12))
        exact node18 hit.symm t0.symm
      · have t0 : x 0 = x 1 := (q.injective (edge1.trans (hit.trans edge3.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans hit)).trans edge5))
        have t2 : x 5 = x 6 := (edge2.symm.trans ((congrArg p hit).trans edge4))
        have t3 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t2.trans edge9.symm)))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 t0.symm (hit.symm.trans t0.symm) (t1.symm.trans t0.symm) t4.symm (t2.symm.trans t4.symm) (t3.symm.trans t4.symm) t5.symm
      · have t0 : x 0 = x 2 := (q.injective (edge1.trans (hit.trans edge5.symm)))
        have t1 : x 5 = x 7 := (edge2.symm.trans ((congrArg p hit).trans edge6))
        have t2 : x 4 = x 6 := (q.injective (edge7.trans (t1.trans edge11.symm)))
        exact node14 t0.symm hit.symm t2.symm t1.symm
      · have t0 : x 2 = x 5 := (edge3.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p t0).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q t0).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node13 hit.symm t0.symm t2.symm (t1.symm.trans t2.symm) t3.symm
      · have t0 : x 0 = x 4 := (q.injective (edge1.trans (hit.trans edge7.symm)))
        have t1 : x 5 = x 8 := (edge2.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 2 = x 6 := (edge3.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (hit.trans t1)).trans edge12))
        have t4 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t2).trans edge11))
        exact node10 t0.symm hit.symm t2.symm t4.symm (t1.symm.trans hit.symm) t3.symm
      · have t0 : x 0 = x 5 := (q.injective (edge1.trans (hit.trans edge9.symm)))
        have t1 : x 5 = x 9 := (edge2.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 2 = x 7 := (edge3.symm.trans ((congrArg q hit).trans edge11))
        have t3 : x 4 = x 8 := (q.injective (edge7.trans (t1.trans edge12.symm)))
        exact node12 t0.symm hit.symm t2.symm t3.symm (t1.symm.trans t0.symm)
      · have t0 : x 0 = x 6 := (q.injective (edge1.trans (hit.trans edge11.symm)))
        have t1 : x 4 = x 9 := (edge0.symm.trans ((congrArg p t0).trans edge10))
        exact node15 t0.symm hit.symm t1.symm
      · have t0 : x 2 = x 9 := (edge3.symm.trans ((congrArg q hit).trans edge12))
        exact node19 hit.symm t0.symm
      · have t0 : x 0 = x 8 := (q.injective (edge1.trans (hit.trans edge12.symm)))
        exact node18 t0.symm hit.symm
      · have t0 : x 1 = x 2 := (q.injective (edge3.trans (hit.trans edge5.symm)))
        have t1 : x 6 = x 7 := (edge4.symm.trans ((congrArg p hit).trans edge6))
        have t2 : x 5 = x 6 := (q.injective (edge9.trans (t1.trans edge11.symm)))
        have t3 : x 0 = x 1 := (q.injective (edge1.trans (t0.trans edge3.symm)))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t2.trans edge9.symm)))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t2).trans edge10))
        exact node4 t3.symm (t0.symm.trans t3.symm) ((hit.symm.trans t0.symm).trans t3.symm) t4.symm (t2.symm.trans t4.symm) ((t1.symm.trans t2.symm).trans t4.symm) t5.symm
      · have t0 : x 3 = x 5 := (edge5.symm.trans ((congrArg q hit).trans edge7))
        have t1 : x 7 = x 8 := (edge6.symm.trans ((congrArg p t0).trans edge8))
        exact node16 hit.symm t0.symm t1.symm
      · have t0 : x 1 = x 4 := (q.injective (edge3.trans (hit.trans edge7.symm)))
        have t1 : x 6 = x 8 := (edge4.symm.trans ((congrArg p hit).trans edge8))
        have t2 : x 3 = x 6 := (edge5.symm.trans ((congrArg q hit).trans edge9))
        have t3 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t2).trans edge10))
        exact node13 t0.symm hit.symm t2.symm (t1.symm.trans t2.symm) t3.symm
      · have t0 : x 1 = x 5 := (q.injective (edge3.trans (hit.trans edge9.symm)))
        have t1 : x 6 = x 9 := (edge4.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 3 = x 7 := (edge5.symm.trans ((congrArg q hit).trans edge11))
        have t3 : x 5 = x 8 := (q.injective (edge9.trans (t1.trans edge12.symm)))
        have t4 : x 0 = x 4 := (q.injective (edge1.trans (t0.trans edge7.symm)))
        exact node10 t4.symm t0.symm hit.symm t2.symm (t3.symm.trans t0.symm) (t1.symm.trans hit.symm)
      · have t0 : x 1 = x 6 := (q.injective (edge3.trans (hit.trans edge11.symm)))
        have t1 : x 0 = x 5 := (q.injective (edge1.trans (t0.trans edge9.symm)))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t0).trans edge10))
        have t3 : x 4 = x 8 := (q.injective (edge7.trans (t2.trans edge12.symm)))
        exact node12 t1.symm t0.symm hit.symm t3.symm (t2.symm.trans t1.symm)
      · have t0 : x 3 = x 9 := (edge5.symm.trans ((congrArg q hit).trans edge12))
        exact node20 hit.symm t0.symm
      · have t0 : x 1 = x 8 := (q.injective (edge3.trans (hit.trans edge12.symm)))
        exact node19 t0.symm hit.symm
      · exact node22 hit.symm
      · have t0 : x 2 = x 4 := (q.injective (edge5.trans (hit.trans edge7.symm)))
        have t1 : x 7 = x 8 := (edge6.symm.trans ((congrArg p hit).trans edge8))
        exact node16 t0.symm hit.symm t1.symm
      · have t0 : x 2 = x 5 := (q.injective (edge5.trans (hit.trans edge9.symm)))
        have t1 : x 7 = x 9 := (edge6.symm.trans ((congrArg p hit).trans edge10))
        have t2 : x 6 = x 8 := (q.injective (edge11.trans (t1.trans edge12.symm)))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans (t0.trans edge7.symm)))
        exact node13 t3.symm t0.symm hit.symm (t2.symm.trans hit.symm) t1.symm
      · have t0 : x 2 = x 6 := (q.injective (edge5.trans (hit.trans edge11.symm)))
        have t1 : x 1 = x 5 := (q.injective (edge3.trans (t0.trans edge9.symm)))
        have t2 : x 6 = x 9 := (edge4.symm.trans ((congrArg p t0).trans edge10))
        have t3 : x 5 = x 8 := (q.injective (edge9.trans (t2.trans edge12.symm)))
        have t4 : x 0 = x 4 := (q.injective (edge1.trans (t1.trans edge7.symm)))
        exact node10 t4.symm t1.symm t0.symm hit.symm (t3.symm.trans t1.symm) (t2.symm.trans t0.symm)
      · exact node21 hit.symm
      · have t0 : x 2 = x 8 := (q.injective (edge5.trans (hit.trans edge12.symm)))
        exact node20 t0.symm hit.symm
      · have t0 : x 0 = x 1 := (p.injective (edge0.trans (hit.trans edge2.symm)))
        have t1 : x 1 = x 2 := (edge1.symm.trans ((congrArg q t0).trans edge3))
        have t2 : x 1 = x 3 := (edge1.symm.trans ((congrArg q (t0.trans t1)).trans edge5))
        have t3 : x 5 = x 6 := (edge2.symm.trans ((congrArg p t1).trans edge4))
        have t4 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t2).trans edge6))
        have t5 : x 8 = x 9 := (edge8.symm.trans ((congrArg p t3).trans edge10))
        exact node4 t0.symm (t1.symm.trans t0.symm) (t2.symm.trans t0.symm) hit.symm (t3.symm.trans hit.symm) (t4.symm.trans hit.symm) t5.symm
      · have t0 : x 0 = x 2 := (p.injective (edge0.trans (hit.trans edge4.symm)))
        have t1 : x 1 = x 3 := (edge1.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 5 = x 7 := (edge2.symm.trans ((congrArg p t1).trans edge6))
        exact node14 t0.symm t1.symm hit.symm t2.symm
      · have t0 : x 0 = x 3 := (p.injective (edge0.trans (hit.trans edge6.symm)))
        exact node17 t0.symm hit.symm
      · have t0 : x 0 = x 5 := (p.injective (edge0.trans (hit.trans edge8.symm)))
        have t1 : x 1 = x 6 := (edge1.symm.trans ((congrArg q t0).trans edge9))
        have t2 : x 5 = x 9 := (edge2.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t1).trans edge11))
        exact node12 t0.symm t1.symm t3.symm hit.symm (t2.symm.trans t0.symm)
      · have t0 : x 0 = x 6 := (p.injective (edge0.trans (hit.trans edge10.symm)))
        have t1 : x 1 = x 7 := (edge1.symm.trans ((congrArg q t0).trans edge11))
        exact node15 t0.symm t1.symm hit.symm
      · have t0 : x 1 = x 2 := (p.injective (edge2.trans (hit.trans edge4.symm)))
        have t1 : x 2 = x 3 := (edge3.symm.trans ((congrArg q t0).trans edge5))
        have t2 : x 6 = x 7 := (edge4.symm.trans ((congrArg p t1).trans edge6))
        have t3 : x 4 = x 5 := (q.injective (edge7.trans (hit.trans edge9.symm)))
        have t4 : x 8 = x 9 := (edge8.symm.trans ((congrArg p hit).trans edge10))
        have t5 : x 0 = x 1 := (p.injective (edge0.trans (t3.trans edge2.symm)))
        exact node4 t5.symm (t0.symm.trans t5.symm) ((t1.symm.trans t0.symm).trans t5.symm) t3.symm (hit.symm.trans t3.symm) ((t2.symm.trans hit.symm).trans t3.symm) t4.symm
      · have t0 : x 1 = x 3 := (p.injective (edge2.trans (hit.trans edge6.symm)))
        have t1 : x 4 = x 6 := (q.injective (edge7.trans (hit.trans edge11.symm)))
        have t2 : x 0 = x 2 := (p.injective (edge0.trans (t1.trans edge4.symm)))
        exact node14 t2.symm t0.symm t1.symm hit.symm
      · have t0 : x 1 = x 5 := (p.injective (edge2.trans (hit.trans edge8.symm)))
        have t1 : x 2 = x 6 := (edge3.symm.trans ((congrArg q t0).trans edge9))
        have t2 : x 2 = x 9 := (edge3.symm.trans ((congrArg q (t0.trans hit)).trans edge12))
        have t3 : x 3 = x 7 := (edge5.symm.trans ((congrArg q t1).trans edge11))
        have t4 : x 0 = x 4 := (q.injective (edge1.trans (t0.trans edge7.symm)))
        exact node10 t4.symm t0.symm t1.symm t3.symm (hit.symm.trans t0.symm) t2.symm
      · have t0 : x 1 = x 6 := (p.injective (edge2.trans (hit.trans edge10.symm)))
        have t1 : x 2 = x 7 := (edge3.symm.trans ((congrArg q t0).trans edge11))
        have t2 : x 4 = x 8 := (q.injective (edge7.trans (hit.trans edge12.symm)))
        have t3 : x 0 = x 5 := (p.injective (edge0.trans (t2.trans edge8.symm)))
        exact node12 t3.symm t0.symm t1.symm t2.symm (hit.symm.trans t3.symm)
      · have t0 : x 2 = x 5 := (p.injective (edge4.trans (hit.trans edge8.symm)))
        have t1 : x 3 = x 6 := (edge5.symm.trans ((congrArg q t0).trans edge9))
        have t2 : x 7 = x 9 := (edge6.symm.trans ((congrArg p t1).trans edge10))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans (t0.trans edge7.symm)))
        exact node13 t3.symm t0.symm t1.symm (hit.symm.trans t1.symm) t2.symm
      · have t0 : x 3 = x 5 := (p.injective (edge6.trans (hit.trans edge8.symm)))
        have t1 : x 2 = x 4 := (q.injective (edge5.trans (t0.trans edge7.symm)))
        exact node16 t1.symm t0.symm hit.symm
      · have t0 : x 3 = x 6 := (p.injective (edge6.trans (hit.trans edge10.symm)))
        have t1 : x 6 = x 8 := (q.injective (edge11.trans (hit.trans edge12.symm)))
        have t2 : x 2 = x 5 := (p.injective (edge4.trans (t1.trans edge8.symm)))
        have t3 : x 1 = x 4 := (q.injective (edge3.trans (t2.trans edge7.symm)))
        exact node13 t3.symm t2.symm t0.symm (t1.symm.trans t0.symm) hit.symm
      · have t0 : x 5 = x 6 := (p.injective (edge8.trans (hit.trans edge10.symm)))
        have t1 : x 6 = x 7 := (edge9.symm.trans ((congrArg q t0).trans edge11))
        have t2 : x 1 = x 2 := (p.injective (edge2.trans (t0.trans edge4.symm)))
        have t3 : x 1 = x 3 := (p.injective (edge2.trans ((t0.trans t1).trans edge6.symm)))
        have t4 : x 4 = x 5 := (q.injective (edge7.trans (t0.trans edge9.symm)))
        have t5 : x 0 = x 1 := (p.injective (edge0.trans (t4.trans edge2.symm)))
        exact node4 t5.symm (t2.symm.trans t5.symm) (t3.symm.trans t5.symm) t4.symm (t0.symm.trans t4.symm) ((t1.symm.trans t0.symm).trans t4.symm) hit.symm
  exact node23

/-- Exchanging sides reverses every matching edge. -/
private theorem unflip {X : Type*} (G : SimpleGraph (Bool × X))
    (h : cycleGraph 4 ⊑ (G.comap (fun a : Bool × X => (!a.1,a.2))) ∨ cycleGraph 8 ⊑ (G.comap (fun a : Bool × X => (!a.1,a.2))) ∨ cycleGraph 16 ⊑ (G.comap (fun a : Bool × X => (!a.1,a.2)))) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let flip : Bool × X ↪ Bool × X := ⟨(fun a : Bool × X => (!a.1,a.2)), fun a b h => by
    simpa using congrArg (fun a : Bool × X => (!a.1,a.2)) h⟩
  have sub : G.comap flip ⊑ G := isContained_iff_exists_le_comap.mpr ⟨flip,le_rfl⟩
  rcases h with h|h|h
  · exact Or.inl (h.trans sub)
  · exact Or.inr (Or.inl (h.trans sub))
  · exact Or.inr (Or.inr (h.trans sub))

private theorem inverseSep {X : Type*} (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) (x : X) :
    p.symm x ≠ x ∧ q.symm x ≠ x ∧ p.symm x ≠ q.symm x := by
  refine ⟨fun h => (sep x).1 (p.symm_apply_eq.mp h).symm, fun h => (sep x).2.1 (q.symm_apply_eq.mp h).symm, ?_⟩
  intro h
  exact (sep (p.symm x)).2.2 (by rw [p.apply_symm_apply, h, q.apply_symm_apply])

theorem shape1 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (x : (Fin 10) → X)
    (edge0 : p (x 0) = x 3)
    (edge1 : q (x 0) = x 1)
    (edge2 : p (x 1) = x 4)
    (edge3 : p (x 2) = x 6)
    (edge4 : q (x 2) = x 3)
    (edge5 : p (x 3) = x 7)
    (edge6 : q (x 3) = x 4)
    (edge7 : p (x 4) = x 8)
    (edge8 : q (x 4) = x 5)
    (edge9 : p (x 5) = x 9)
    (edge10 : q (x 6) = x 7)
    (edge11 : q (x 7) = x 8)
    (edge12 : q (x 8) = x 9)
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply unflip G
  apply shape0 (G.comap (fun a : Bool × X => (!a.1,a.2))) p.symm q.symm (inverseSep p q sep)
    (fun t => (idAdj t).symm)
    (fun t => by change G.Adj (true,t) (false,p.symm t); simpa using (pAdj (p.symm t)).symm)
    (fun t => by change G.Adj (true,t) (false,q.symm t); simpa using (qAdj (q.symm t)).symm) ![x 9, x 8, x 7, x 6, x 5, x 4, x 3, x 2, x 1, x 0]
  · exact p.symm_apply_eq.mpr edge9.symm
  · exact q.symm_apply_eq.mpr edge12.symm
  · exact p.symm_apply_eq.mpr edge7.symm
  · exact q.symm_apply_eq.mpr edge11.symm
  · exact p.symm_apply_eq.mpr edge5.symm
  · exact q.symm_apply_eq.mpr edge10.symm
  · exact p.symm_apply_eq.mpr edge3.symm
  · exact q.symm_apply_eq.mpr edge8.symm
  · exact p.symm_apply_eq.mpr edge2.symm
  · exact q.symm_apply_eq.mpr edge6.symm
  · exact p.symm_apply_eq.mpr edge0.symm
  · exact q.symm_apply_eq.mpr edge4.symm
  · exact q.symm_apply_eq.mpr edge1.symm

theorem shape2 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (x : (Fin 10) → X)
    (edge0 : p (x 0) = x 2)
    (edge1 : q (x 0) = x 1)
    (edge2 : p (x 1) = x 3)
    (edge3 : p (x 2) = x 5)
    (edge4 : q (x 2) = x 3)
    (edge5 : p (x 3) = x 6)
    (edge6 : q (x 3) = x 4)
    (edge7 : p (x 4) = x 7)
    (edge8 : p (x 5) = x 8)
    (edge9 : q (x 5) = x 6)
    (edge10 : p (x 6) = x 9)
    (edge11 : q (x 6) = x 7)
    (edge12 : q (x 8) = x 9)
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply shape0 G q p (fun u => ⟨(sep u).2.1,(sep u).1,(sep u).2.2.symm⟩) idAdj qAdj pAdj ![x 0, x 2, x 5, x 8, x 1, x 3, x 6, x 9, x 4, x 7]
  · exact edge1
  · exact edge0
  · exact edge4
  · exact edge3
  · exact edge9
  · exact edge8
  · exact edge12
  · exact edge2
  · exact edge6
  · exact edge5
  · exact edge11
  · exact edge10
  · exact edge7

theorem shape3 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (x : (Fin 10) → X)
    (edge0 : p (x 0) = x 3)
    (edge1 : q (x 0) = x 1)
    (edge2 : p (x 1) = x 4)
    (edge3 : p (x 2) = x 5)
    (edge4 : q (x 2) = x 3)
    (edge5 : p (x 3) = x 6)
    (edge6 : q (x 3) = x 4)
    (edge7 : p (x 4) = x 7)
    (edge8 : q (x 5) = x 6)
    (edge9 : p (x 6) = x 8)
    (edge10 : q (x 6) = x 7)
    (edge11 : p (x 7) = x 9)
    (edge12 : q (x 8) = x 9)
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  apply unflip G
  apply shape0 (G.comap (fun a : Bool × X => (!a.1,a.2))) q.symm p.symm (inverseSep q p (fun u => ⟨(sep u).2.1,(sep u).1,(sep u).2.2.symm⟩))
    (fun t => (idAdj t).symm)
    (fun t => by change G.Adj (true,t) (false,q.symm t); simpa using (qAdj (q.symm t)).symm)
    (fun t => by change G.Adj (true,t) (false,p.symm t); simpa using (pAdj (p.symm t)).symm) ![x 9, x 7, x 4, x 1, x 8, x 6, x 3, x 0, x 5, x 2]
  · exact q.symm_apply_eq.mpr edge12.symm
  · exact p.symm_apply_eq.mpr edge11.symm
  · exact q.symm_apply_eq.mpr edge10.symm
  · exact p.symm_apply_eq.mpr edge7.symm
  · exact q.symm_apply_eq.mpr edge6.symm
  · exact p.symm_apply_eq.mpr edge2.symm
  · exact q.symm_apply_eq.mpr edge1.symm
  · exact p.symm_apply_eq.mpr edge9.symm
  · exact q.symm_apply_eq.mpr edge8.symm
  · exact p.symm_apply_eq.mpr edge5.symm
  · exact q.symm_apply_eq.mpr edge4.symm
  · exact p.symm_apply_eq.mpr edge0.symm
  · exact p.symm_apply_eq.mpr edge3.symm

theorem near0 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (z : X)
    (center : p (q (z)) = q (p (z)))
    (c1 : p (q (p z)) = q (p (p z)))
    (c2 : p (q (q.symm z)) = q (p (q.symm z)))
    (c3 : p (q (q z)) = q (p (q z)))
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let labels : (Fin 10) → X := ![q.symm z, z, q (z), q (q z), p (q.symm z), p (z), p (q (z)), p (q (q z)), p (p z), p (q (p z))]
  apply shape0 G p q sep idAdj pAdj qAdj labels
  · change p (q.symm z) = p (q.symm z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (q.symm z) = z
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (z) = p (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (z) = q (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (q (z)) = q (q z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (q z)) = p (q (q z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (q.symm z)) = p (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (p (z)) = p (p z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (p (q (z))) = p (q (p z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (q (z))) = p (q (q z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (p z)) = p (q (p z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
theorem near1 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (z : X)
    (center : p (q (z)) = q (p (z)))
    (c0 : p (q (p.symm z)) = q (p (p.symm z)))
    (c2 : p (q (q.symm z)) = q (p (q.symm z)))
    (c3 : p (q (q z)) = q (p (q z)))
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let labels : (Fin 10) → X := ![p.symm z, q (p.symm z), q.symm z, z, q (z), q (q z), p (q.symm z), p (z), p (q (z)), p (q (q z))]
  apply shape1 G p q sep idAdj pAdj qAdj labels
  · change p (p.symm z) = z
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p.symm z) = q (p.symm z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (p.symm z)) = q (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q.symm z) = p (q.symm z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (q.symm z) = z
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (z) = p (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (z) = q (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (q (z)) = q (q z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (q z)) = p (q (q z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (q.symm z)) = p (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (q (z))) = p (q (q z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
theorem near2 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (z : X)
    (center : p (q (z)) = q (p (z)))
    (c0 : p (q (p.symm z)) = q (p (p.symm z)))
    (c1 : p (q (p z)) = q (p (p z)))
    (c3 : p (q (q z)) = q (p (q z)))
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let labels : (Fin 10) → X := ![p.symm z, q (p.symm z), z, q (z), q (q z), p (z), p (q (z)), p (q (q z)), p (p z), p (q (p z))]
  apply shape2 G p q sep idAdj pAdj qAdj labels
  · change p (p.symm z) = z
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p.symm z) = q (p.symm z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (p.symm z)) = q (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (z) = p (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (z) = q (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (q (z)) = q (q z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (q z)) = p (q (q z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (p (z)) = p (p z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (p (q (z))) = p (q (p z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (q (z))) = p (q (q z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (p z)) = p (q (p z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
theorem near3 {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (z : X)
    (center : p (q (z)) = q (p (z)))
    (c0 : p (q (p.symm z)) = q (p (p.symm z)))
    (c1 : p (q (p z)) = q (p (p z)))
    (c2 : p (q (q.symm z)) = q (p (q.symm z)))
    : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  let labels : (Fin 10) → X := ![p.symm z, q (p.symm z), q.symm z, z, q (z), p (q.symm z), p (z), p (q (z)), p (p z), p (q (p z))]
  apply shape3 G p q sep idAdj pAdj qAdj labels
  · change p (p.symm z) = z
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p.symm z) = q (p.symm z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (p.symm z)) = q (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q.symm z) = p (q.symm z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (q.symm z) = z
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (z) = p (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (z) = q (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (q (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (q.symm z)) = p (z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (p (z)) = p (p z)
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (z)) = p (q (z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change p (p (q (z))) = p (q (p z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
  · change q (p (p z)) = p (q (p z))
    simp only [Equiv.apply_symm_apply] at * <;> grind
end LocalCommutation


namespace CommutationDensity
open Finset

/-- Count visits to a set at the four positions p x, p⁻¹ x, q x, q⁻¹ x with
multiplicity. Permutations preserve the total number of visits in each slot. -/
theorem one_third {X : Type*} [Fintype X] [DecidableEq X] (D : Finset X) (p q : Equiv.Perm X)
    (hit : ∀ x ∉ D, 2 ≤ (if p x ∈ D then 1 else 0 : ℕ) +
      (if p.symm x ∈ D then 1 else 0) + (if q x ∈ D then 1 else 0) +
      (if q.symm x ∈ D then 1 else 0)) :
    Fintype.card X ≤ 3 * D.card := by
  classical
  let w (x : X) : ℕ := if x ∈ D then 1 else 0
  have base : ∑ x, w x = D.card := by simp [w]
  have total (f : Equiv.Perm X) : ∑ x, w (f x) = D.card := (Equiv.sum_comp f w).trans base
  have localBound (x : X) : 2 ≤ 2*w x + w (p x) + w (p.symm x) + w (q x) + w (q.symm x) := by
    by_cases h : x ∈ D
    · have : w x = 1 := if_pos h; omega
    · have : w x = 0 := if_neg h
      simpa only [this,Nat.mul_zero,Nat.zero_add] using (show 2 ≤ w (p x) + w (p.symm x) + w (q x) + w (q.symm x) from hit x h)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ => localBound x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, base,total, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  omega

end CommutationDensity


namespace LocalCommutation
open SimpleGraph Finset
/-- In the matching presentation of a bipartite graph, the absence of 4-, 8- and
16-cycles forces the two relative permutations to fail to commute on at least a third of X. -/
theorem defectDensity {X : Type*} [Fintype X] [DecidableEq X] (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idAdj : ∀ u, G.Adj (false,u) (true,u))
    (pAdj : ∀ u, G.Adj (false,u) (true,p u))
    (qAdj : ∀ u, G.Adj (false,u) (true,q u)) (noCycle : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) :
    Fintype.card X ≤ 3 * (Finset.univ.filter fun x => p (q x) ≠ q (p x)).card := by
  classical
  let D := Finset.univ.filter fun x => p (q x) ≠ q (p x)
  change Fintype.card X ≤ 3 * D.card
  apply CommutationDensity.one_third D p q
  intro z hz
  have center : p (q z) = q (p z) := by simpa [D] using hz
  have impossible0 : (p (q (p z)) = q (p (p z)) ∧ p (q (q.symm z)) = q (p (q.symm z)) ∧ p (q (q z)) = q (p (q z))) → False :=
    fun h => noCycle (near0 G p q sep idAdj pAdj qAdj z center h.1 h.2.1 h.2.2)
  have impossible1 : (p (q (p.symm z)) = q (p (p.symm z)) ∧ p (q (q.symm z)) = q (p (q.symm z)) ∧ p (q (q z)) = q (p (q z))) → False :=
    fun h => noCycle (near1 G p q sep idAdj pAdj qAdj z center h.1 h.2.1 h.2.2)
  have impossible2 : (p (q (p.symm z)) = q (p (p.symm z)) ∧ p (q (p z)) = q (p (p z)) ∧ p (q (q z)) = q (p (q z))) → False :=
    fun h => noCycle (near2 G p q sep idAdj pAdj qAdj z center h.1 h.2.1 h.2.2)
  have impossible3 : (p (q (p.symm z)) = q (p (p.symm z)) ∧ p (q (p z)) = q (p (p z)) ∧ p (q (q.symm z)) = q (p (q.symm z))) → False :=
    fun h => noCycle (near3 G p q sep idAdj pAdj qAdj z center h.1 h.2.1 h.2.2)
  by_cases c0 : p (q (p.symm z)) = q (p (p.symm z)) <;>
  by_cases c1 : p (q (p z)) = q (p (p z)) <;>
  by_cases c2 : p (q (q.symm z)) = q (p (q.symm z)) <;>
  by_cases c3 : p (q (q z)) = q (p (q z)) <;>
  simp_all [D]

end LocalCommutation

namespace HaarShort
open SimpleGraph
variable {A : Type*} [AddCommGroup A]

/-- An abelian Haar graph with three distinct shifts contains a 4-, 8-, or
16-cycle. Translate the right part to normalize one of the shifts to zero. -/
theorem haar_short_cycle (G : SimpleGraph (Bool × A)) (u v : A)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (h0 : ∀ x, G.Adj (false, x) (true, x))
    (h1 : ∀ x, G.Adj (false, x) (true, x + u))
    (h2 : ∀ x, G.Adj (false, x) (true, x + v)) :
    SimpleGraph.cycleGraph 4 ⊑ G ∨ SimpleGraph.cycleGraph 8 ⊑ G ∨ SimpleGraph.cycleGraph 16 ⊑ G := by
  let p : Equiv.Perm A := Equiv.addRight u
  let q : Equiv.Perm A := Equiv.addRight v
  have sep (x : A) : p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x := by simpa [p,q] using And.intro hu (And.intro hv huv)
  have comm (x : A) : p (q x) = q (p x) := by change x+v+u=x+u+v; abel
  exact LocalCommutation.near0 G p q sep h0 h1 h2 0 (comm _) (comm _) (comm _) (comm _)

end HaarShort
namespace HaarTransfer
open SimpleGraph

/-- Choose one orbit of the commuting relative permutations of two matchings.
The action on that orbit factors faithfully through an abelian quotient of ℤ². -/
theorem commuting_matchings {V X : Type*} (G : SimpleGraph V) (s t : Equiv.Perm X)
    (comm : Commute s t) (z : X) (hs : s z ≠ z) (ht : t z ≠ z) (hst : s z ≠ t z)
    (f : (Bool × X) ↪ V)
    (h0 : ∀ x, G.Adj (f (false,x)) (f (true,x)))
    (h1 : ∀ x, G.Adj (f (false,x)) (f (true,s x)))
    (h2 : ∀ x, G.Adj (f (false,x)) (f (true,t x))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let act (a : ℤ × ℤ) : Equiv.Perm X := s ^ a.1 * t ^ a.2
  have add (a b : ℤ × ℤ) : act (a+b) = act a * act b := by
    change s ^ (a.1+b.1) * t ^ (a.2+b.2) = (s ^ a.1 * t ^ a.2) * (s ^ b.1 * t ^ b.2)
    rw [zpow_add, zpow_add]
    simp only [mul_assoc]
    rw [← mul_assoc (s ^ b.1), (comm.zpow_zpow b.1 a.2).eq, mul_assoc]
  letI : AddAction (ℤ × ℤ) X := {
    vadd a x := act a x
    zero_vadd x := by change act 0 x = x; simp [act]
    add_vadd a b x := congrArg (fun p : Equiv.Perm X => p x) (add a b) }
  let K := AddAction.stabilizer (ℤ × ℤ) z
  let e : ((ℤ × ℤ) ⧸ K) ↪ X := ⟨AddAction.ofQuotientStabilizer _ z, AddAction.injective_ofQuotientStabilizer _ z⟩
  let u : (ℤ × ℤ) ⧸ K := QuotientAddGroup.mk (1,0)
  let v : (ℤ × ℤ) ⧸ K := QuotientAddGroup.mk (0,1)
  have zero : e 0 = z := by change act 0 z = z; simp [act]
  have eU (x : (ℤ × ℤ) ⧸ K) : e (x+u) = s (e x) := by
    induction x using Quotient.inductionOn' with | _ a =>
      change act (a+(1,0)) z = s (act a z)
      rw [add_comm a, add]; simp [act, Equiv.Perm.mul_apply]
  have eV (x : (ℤ × ℤ) ⧸ K) : e (x+v) = t (e x) := by
    induction x using Quotient.inductionOn' with | _ a =>
      change act (a+(0,1)) z = t (act a z)
      rw [add_comm a, add]; simp [act, Equiv.Perm.mul_apply]
  have eu : e u = s z := by simpa [zero] using eU 0
  have ev : e v = t z := by simpa [zero] using eV 0
  let j := (Function.Embedding.refl Bool |>.prodMap e).trans f
  let J := G.comap j
  have sub : J ⊑ G := (isContained_iff_exists_le_comap).mpr ⟨j, le_rfl⟩
  have small := HaarShort.haar_short_cycle J u v
    (fun h => hs (eu.symm.trans ((congrArg e h).trans zero)))
    (fun h => ht (ev.symm.trans ((congrArg e h).trans zero)))
    (fun h => hst (eu.symm.trans ((congrArg e h).trans ev)))
    (fun x => h0 (e x))
    (fun x => by change G.Adj _ (f (true, e (x+u))); rw [eU]; exact h1 _)
    (fun x => by change G.Adj _ (f (true, e (x+v))); rw [eV]; exact h2 _)
  rcases small with h | h | h
  · exact Or.inl (h.trans sub)
  · exact Or.inr (Or.inl (h.trans sub))
  · exact Or.inr (Or.inr (h.trans sub))

end HaarTransfer

namespace RegularMatchings
open Finset

/-- Hall's condition follows by counting incidences between any rows and their neighbors. -/
lemma regularHall {X Y : Type*} [Fintype X] [Fintype Y] (R : X → Y → Prop) [DecidableRel R]
    {d : ℕ} (hd : 0 < d) (row : ∀ x, (univ.filter (R x)).card = d)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = d) : ∃ f : X → Y, Function.Injective f ∧ ∀ x, R x (f x) := by
  classical
  let B := fun x => univ.filter (R x)
  suffices hall : ∀ s : Finset X, s.card ≤ (s.biUnion B).card by
    obtain ⟨f,hinj,hf⟩ := (all_card_le_biUnion_card_iff_exists_injective B).mp hall
    exact ⟨f,hinj,fun x => (mem_filter.mp (hf x)).2⟩
  intro s
  have total := sum_card_eq_sum_biUnion_card B s
  have le : ∀ y, (s.filter fun x => y ∈ B x).card ≤ d := by
    intro y
    rw [← col y]
    apply card_le_card
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_filter.mp hx).2).2⟩
  have bound := sum_le_sum (s := s.biUnion B) (fun y _ => le y)
  have hrow (x : X) : (B x).card = d := row x
  simp only [hrow, sum_const, smul_eq_mul] at total
  have same (y : Y) : (univ.filter fun x => x ∈ s ∧ y ∈ B x) = s.filter (fun x => y ∈ B x) := by
    ext; simp
  simp_rw [same] at total
  rw [sum_const, smul_eq_mul, ← total] at bound
  exact Nat.le_of_mul_le_mul_right bound hd

lemma regularEquiv {X Y : Type*} [Fintype X] [Fintype Y] (R : X → Y → Prop) [DecidableRel R]
    {d : ℕ} (hd : 0 < d) (row : ∀ x, (univ.filter (R x)).card = d)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = d) : ∃ f : X ≃ Y, ∀ x, R x (f x) := by
  obtain ⟨f, hf, hR⟩ := regularHall R hd row col
  obtain ⟨g, hg, _⟩ := regularHall (fun y x => R x y) hd col row
  have hcard := Nat.le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective g hg)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),hR⟩

lemma removeMatching {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (R : X → Y → Prop) [DecidableRel R] (f : X ≃ Y) (hf : ∀ x, R x (f x))
    (d : ℕ) (row : ∀ x, (univ.filter (R x)).card = d+1)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = d+1) :
    (∀ x, (univ.filter fun y => R x y ∧ y ≠ f x).card = d) ∧
    (∀ y, (univ.filter fun x => R x y ∧ y ≠ f x).card = d) := by
  constructor
  · intro x
    have h : (univ.filter fun y => R x y ∧ y ≠ f x) = (univ.filter (R x)).erase (f x) := by
      ext; simp [and_comm]
    rw [h,card_erase_of_mem (mem_filter.mpr ⟨mem_univ _,hf x⟩),row]; omega
  · intro y
    have h : (univ.filter fun x => R x y ∧ y ≠ f x) = (univ.filter fun x => R x y).erase (f.symm y) := by
      ext x; simp [ne_comm, Equiv.eq_symm_apply, and_comm]
    rw [h,card_erase_of_mem (mem_filter.mpr ⟨mem_univ _,by simpa using hf (f.symm y)⟩),col]; omega

lemma cubicMatchings {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) [DecidableRel R] (row : ∀ x, (univ.filter (R x)).card = 3)
    (col : ∀ y, (univ.filter (fun x => R x y)).card = 3) :
    ∃ f g h : X ≃ Y, ∀ x, R x (f x) ∧ R x (g x) ∧ R x (h x) ∧
      g x ≠ f x ∧ h x ≠ f x ∧ h x ≠ g x := by
  classical
  obtain ⟨f,hf⟩ := regularEquiv R (by decide : 0<3) row col
  obtain ⟨r,c⟩ := removeMatching R f hf 2 row col
  let S := fun x y => R x y ∧ y ≠ f x
  obtain ⟨g,hg⟩ := regularEquiv S (by decide : 0<2) r c
  obtain ⟨r',c'⟩ := removeMatching S g hg 1 r c
  obtain ⟨h,hh⟩ := regularEquiv (fun x y => S x y ∧ y ≠ g x) (by decide : 0<1) r' c'
  exact ⟨f,g,h,fun x => ⟨hf x,(hg x).1,(hh x).1.1,(hg x).2,(hh x).1.2,(hh x).2⟩⟩

end RegularMatchings
namespace RegularMatchings
open SimpleGraph Finset

lemma countSide {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [Fintype S] (x : V) (h : ∀ y, G.Adj x y → y ∈ S) :
    (univ.filter (fun y : S => G.Adj x y.val)).card = G.degree x := by
  rw [← card_neighborFinset_eq_degree]
  apply card_bij (fun y _ => y.val)
  · intro y hy; exact (G.mem_neighborFinset x y).mpr (mem_filter.mp hy).2
  · intro a _ b _ e; exact Subtype.ext e
  · intro y hy; have adj := (G.mem_neighborFinset x y).mp hy
    exact ⟨⟨y,h y adj⟩,mem_filter.mpr ⟨mem_univ _,adj⟩,rfl⟩

lemma present {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (bip : G.IsBipartite) (deg : ∀ v, G.degree v=3) :
    ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (f : Bool × X ↪ V) (p q : Equiv.Perm X),
      ∀ x, (p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) ∧
      G.Adj (f (false,x)) (f (true,x)) ∧ G.Adj (f (false,x)) (f (true,p x)) ∧
      G.Adj (f (false,x)) (f (true,q x)) := by
  classical
  obtain ⟨L,R,b⟩ := bip.exists_isBipartiteWith
  obtain ⟨a⟩ := ‹Nonempty V›
  have pos : 0 < (G.neighborFinset a).card := by rw [card_neighborFinset_eq_degree,deg]; decide
  obtain ⟨c,hc⟩ := card_pos.mp pos
  have left : Nonempty L := by
    rcases b.mem_of_adj ((G.mem_neighborFinset a c).mp hc) with h|h
    · exact ⟨⟨a,h.1⟩⟩
    · exact ⟨⟨c,h.2⟩⟩
  let r := fun (x : L) (y : R) => G.Adj x.val y.val
  have row (x : L) : (univ.filter (r x)).card = 3 :=
    (countSide G R x.val fun _ adj => b.mem_of_mem_adj x.property adj).trans (deg x.val)
  have col (y : R) : (univ.filter (fun x => r x y)).card = 3 := by
    have t := countSide G L y.val (fun _ adj => b.symm.mem_of_mem_adj y.property adj)
    simpa only [r, G.adj_comm y.val] using t.trans (deg y.val)
  obtain ⟨a,d,e,he⟩ := cubicMatchings r row col
  let f : Bool × L → V := fun z => if z.1 then (a z.2).val else z.2.val
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ hij
    cases i <;> cases j <;> simp [f] at hij ⊢
    · exact Subtype.ext hij
    · exact (Set.disjoint_left.mp b.disjoint x.property (hij ▸ (a y).property)).elim
    · exact (Set.disjoint_left.mp b.disjoint y.property (hij ▸ (a x).property)).elim
    · exact a.injective (Subtype.ext hij)
  refine ⟨L,inferInstance,left,⟨f,inj⟩,d.trans a.symm,e.trans a.symm,?_⟩
  intro x
  obtain ⟨ha,hd,he',hda,hea,hed⟩ := he x
  simp only [Function.Embedding.coeFn_mk, Equiv.trans_apply, f, Bool.false_eq_true, ↓reduceIte,
    Equiv.apply_symm_apply]
  exact ⟨⟨fun h => hda (a.symm_apply_eq.mp h), fun h => hea (a.symm_apply_eq.mp h),
    fun h => hed (a.symm.injective h).symm⟩,ha,hd,he'⟩

end RegularMatchings
theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1.H1 := by
  intro nonbip noncomm V G _ _ conn deg bridge
  classical
  by_cases bip : G.IsBipartite
  · letI : Nonempty V := conn.nonempty
    obtain ⟨X,fin,inh,f,p,q,h⟩ := RegularMatchings.present G bip deg
    letI := fin
    letI := inh
    have solve (k : ℕ) (hk : 2 ≤ k) (hc : cycleGraph (2^k) ⊑ G) :
        ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
      obtain ⟨v,c,hc',hl⟩ := (cycleGraph_isContained_iff (by calc
        2 < 2^2 := by decide
        _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk)).mp hc
      exact ⟨k,v,c,hk,hc',hl⟩
    let J := G.comap f
    have sub : J ⊑ G := isContained_iff_exists_le_comap.mpr ⟨f, le_rfl⟩
    by_cases short : cycleGraph 4 ⊑ J ∨ cycleGraph 8 ⊑ J ∨ cycleGraph 16 ⊑ J
    · rcases short with a | a | a
      · exact solve 2 (by decide) (a.trans sub)
      · exact solve 3 (by decide) (a.trans sub)
      · exact solve 4 (by decide) (a.trans sub)
    · have bound := LocalCommutation.defectDensity J p q (fun x => (h x).1)
        (fun x => (h x).2.1) (fun x => (h x).2.2.1) (fun x => (h x).2.2.2) short
      have count : (Finset.univ.filter (fun x => p (q x) ≠ q (p x))).card =
          {x : X | p (q x) ≠ q (p x)}.ncard := by rw [← Set.ncard_coe_finset]; congr 1; ext; simp
      obtain ⟨k,hk,hkG⟩ := noncomm X p q (fun x => (h x).1) (count ▸ bound)
      apply solve k hk (hkG.trans _)
      refine isContained_iff_exists_le_comap.mpr ⟨f,?_⟩
      have forward (a b : Bool × X) (ha : a.1 = false) (hb : b.1 = true)
          (edge : b.2 = a.2 ∨ b.2 = p a.2 ∨ b.2 = q a.2) : G.Adj (f a) (f b) := by
        obtain ⟨i,x⟩ := a; obtain ⟨j,y⟩ := b
        subst_vars
        rcases edge with rfl | rfl | rfl
        · exact (h _).2.1
        · exact (h x).2.2.1
        · exact (h x).2.2.2
      intro a b edge
      rcases edge.2 with ⟨ha,hb,e⟩ | ⟨hb,ha,e⟩
      · exact forward a b ha hb e
      · exact (forward b a hb ha e).symm
  · exact nonbip V G conn deg bridge bip

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
