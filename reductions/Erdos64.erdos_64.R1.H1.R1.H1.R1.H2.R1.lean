import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
import Mathlib

/-!
# Central commutators in the Erdős–Gyárfás matching problem

The parent reduction represents a cubic bipartite graph by three matchings. If the
relative permutations p and q commute with their commutator, the resulting graph has
a simple cycle of length 4, 8 or 16, including when the action has point stabilizers.

In integer Heisenberg coordinates the two words 2010120121010210 and 1020210212020120
close. The digits denote the identity, p and q matching edges. A repeated vertex in
one trace gives a stabilizer relation. The short-word certificates handle relations
conjugate to four- or eight-step cyclically nonbacktracking walks. A central generator
fixing a point gives four commuting squares on its orbit by the parent reduction.
The remaining horizontal and vertical relations together force the eighth power of
p to fix a point, giving an alternating cycle of length 4, 8 or 16.

For noncentral commutators, a free action of the generated group embeds the regular
left-translation graph in a point orbit. This leaves the group-translation problem
and the case of a nonidentity permutation fixing a point.

The matching presentation and commuting-square lemma are from PR 5246, building on
the bridge reduction in PR 592. Ghaffari and Mostaghim (Aequationes Math. 92, 2018)
and Burkhart (arXiv:2611.05060) give related power-cycle results for Cayley graphs.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1
open SimpleGraph
open scoped commutatorElement

/-- The three matchings given by identity and two left translations on a finite group. -/
def H1 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    a ≠ 1 → b ≠ 1 → a ≠ b → ¬ (Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = a*u.2 ∨ v.2 = b*u.2))

/-- A faithful matching action with a noncentral commutator and a nontrivial point stabilizer. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ¬ (Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆) →
    (∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ ∃ x : X, g x=x) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))

/- A cyclically nonbacktracking bipartite walk of length four or eight gives a short cycle. -/

namespace NonfreeWalk
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- An oriented cyclic list of four vertices with no immediate reversal is a C4. -/
theorem square {a b c d : V} (ab : G.Adj a b) (bc : G.Adj b c)
    (cd : G.Adj c d) (da : G.Adj d a) (ac : a ≠ c) (bd : b ≠ d) :
    cycleGraph 4 ⊑ G := by
  let p : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
  apply (cycleGraph_isContained_iff (by decide : 2 < 4)).mpr
  refine ⟨a,p,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨Walk.IsPath.mk' ?_, by change 3 ≤ 4; decide⟩,rfl⟩
  change [b,c,d,a].Nodup
  have hab := ab.ne
  have hbc := bc.ne
  have hcd := cd.ne
  have hda := da.ne
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]
  grind

theorem fourOfTrace (v : Fin 4 → V) (edge : ∀ i, G.Adj (v i) (v (i+1)))
    (turn : ∀ i, v i ≠ v (i+2)) : cycleGraph 4 ⊑ G :=
  square (edge 0) (edge 1) (edge 2) (edge 3) (turn 0) (turn 1)

/-- A parity-respecting, cyclically nonbacktracking eight-step trace either embeds C8
or contains a four-step closed segment. The graph itself may have additional edges. -/
theorem eightOfTrace (v : Fin 8 → V) (edge : ∀ i, G.Adj (v i) (v (i+1)))
    (turn : ∀ i, v i ≠ v (i+2))
    (parity : ∀ i j, v i = v j → i.val % 2 = j.val % 2) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G := by
  classical
  by_cases inj : Function.Injective v
  · have numerical : ∀ i j : Fin 8, (cycleGraph 8).Adj i j → j = i+1 ∨ i = j+1 := by decide
    let hom : cycleGraph 8 →g G := ⟨v, fun {i j} h => by
      rcases numerical i j h with hj|hi
      · exact hj ▸ edge i
      · exact hi ▸ (edge j).symm⟩
    exact .inr ⟨hom.toCopy inj⟩
  · obtain ⟨i,j,hit,ij⟩ := Function.not_injective_iff.mp inj
    have near : ∀ k m : Fin 8, k.val % 2 = m.val % 2 → k ≠ m →
        m = k+2 ∨ k = m+2 ∨ m = k+4 := by decide
    rcases near i j (parity i j hit) ij with e|e|e
    · exact (turn i (e ▸ hit)).elim
    · exact (turn j (e ▸ hit.symm)).elim
    have opp : v (i+4) = v i := e ▸ hit.symm
    have hops : ∀ k : Fin 8,
        (k+1)+1=k+2 ∧ (k+2)+1=k+3 ∧ (k+3)+1=k+4 ∧ (k+1)+2=k+3 := by decide
    obtain ⟨h1,h2,h3,h4⟩ := hops i
    exact .inl (square (edge i) (h1 ▸ edge (i+1)) (h2 ▸ edge (i+2))
      (opp ▸ h3 ▸ edge (i+3)) (turn i) (h4 ▸ turn (i+1)))

/-- Direct interface for explicit matching traces. Each i is counted cyclically.
A Boolean coloring records the two alternating sides of the trace. -/
theorem eightOfAlternatingTrace (v : Fin 8 → V) (edge : ∀ i, G.Adj (v i) (v (i+1)))
    (turn : ∀ i, v i ≠ v (i+2)) (side : V → Bool)
    (alternate : ∀ i, side (v i) ≠ side (v (i+1))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G := by
  apply eightOfTrace v edge turn
  let s (i : Fin 8) := side (v i)
  have trans {a b c : Bool} (ab : a ≠ b) (bc : b ≠ c) : a = c := by
    cases a <;> cases b <;> cases c <;> simp_all
  have s0 : s 0 ≠ s 1 := alternate 0
  have s2 : s 2 = s 0 := (trans (alternate 0) (alternate 1)).symm
  have s3 : s 3 = s 1 := (trans (alternate 1) (alternate 2)).symm
  have s4 : s 4 = s 0 := (trans (alternate 2) (alternate 3)).symm.trans s2
  have s5 : s 5 = s 1 := (trans (alternate 3) (alternate 4)).symm.trans s3
  have s6 : s 6 = s 0 := (trans (alternate 4) (alternate 5)).symm.trans s4
  have s7 : s 7 = s 1 := (trans (alternate 5) (alternate 6)).symm.trans s5
  have table (i : Fin 8) : s i = if i.val % 2 = 0 then s 0 else s 1 := by
    fin_cases i <;> first | rfl | exact s2 | exact s3 | exact s4 | exact s5 | exact s6 | exact s7
  intro i j eq
  have h : s i = s j := congrArg side eq
  rw [table i, table j] at h
  split at h <;> split at h <;> first | contradiction | (exfalso; exact s0 h.symm) | omega

end NonfreeWalk

namespace NonfreePort
open SimpleGraph
variable {T A : Type*} (M : A → A → A) (I : A → A) (one : A) (shifts : List A)
    (φ : A → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hone : φ one = 1) (hmul : ∀ g h, φ (M g h) = φ g * φ h)
    (hinv : ∀ g, φ (I g) = (φ g)⁻¹)

theorem fixedResidue (hone : φ one = 1) (hmul : ∀ g h, φ (M g h) = φ g * φ h) (hinv : ∀ g, φ (I g) = (φ g)⁻¹)
    (x : T) (r : A) (fix : φ r x = x) (d a b : A)
    (h : M (I (M d a)) b = one ∨ M (I (M d a)) b = r ∨ M (I (M d a)) b = I r) :
    φ b x = φ d (φ a x) := by
  have hfix : φ (M (I (M d a)) b) x = x := by
    rcases h with e|e|e
    · rw [e,hone]; rfl
    · rw [e,fix]
    · rw [e,hinv]
      have undo := congrArg (fun z => (φ r).symm z) fix
      simpa using undo.symm
  rw [hmul,hinv,Equiv.Perm.mul_apply] at hfix
  have h' := congrArg (φ (M d a)) hfix
  simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply,hmul,Equiv.Perm.mul_apply] using h'

theorem stepImage (hone : φ one = 1) (hmul : ∀ g h, φ (M g h) = φ g * φ h) (hinv : ∀ g, φ (I g) = (φ g)⁻¹)
    (x : T) (r : A) (fix : φ r x = x) {n : ℕ} [NeZero n] (p : Fin n → Bool × A) (l : Fin n → A)
    (valid : ∀ i, (p i).1 ≠ (p (i+1)).1 ∧ l i ∈ shifts ∧ l i ≠ l (i+1) ∧
      (let a := if (p i).1 then (p (i+1)).2 else (p i).2
       let b := if (p i).1 then (p i).2 else (p (i+1)).2
       let v := M (I (M (l i) a)) b
       v = one ∨ v = r ∨ v = I r)) (i : Fin n) :
    if (p i).1 then φ (p i).2 x = φ (l i) (φ (p (i+1)).2 x)
    else φ (p (i+1)).2 x = φ (l i) (φ (p i).2 x) := by
  have h := (valid i).2.2.2
  cases hi : (p i).1 <;> simp only [hi,Bool.false_eq_true,if_false,if_true] at h ⊢
  · exact fixedResidue M I one φ hone hmul hinv x r fix _ _ _ h
  · exact fixedResidue M I one φ hone hmul hinv x r fix _ _ _ h

theorem stepEdge (hone : φ one = 1) (hmul : ∀ g h, φ (M g h) = φ g * φ h) (hinv : ∀ g, φ (I g) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ shifts → G.Adj (false,z) (true,φ d z)) (x : T) (r : A) (fix : φ r x = x) {n : ℕ} [NeZero n] (p : Fin n → Bool × A) (l : Fin n → A)
    (valid : ∀ i, (p i).1 ≠ (p (i+1)).1 ∧ l i ∈ shifts ∧ l i ≠ l (i+1) ∧
      (let a := if (p i).1 then (p (i+1)).2 else (p i).2
       let b := if (p i).1 then (p i).2 else (p (i+1)).2
       let v := M (I (M (l i) a)) b
       v = one ∨ v = r ∨ v = I r)) (i : Fin n) :
    G.Adj ((p i).1, φ (p i).2 x) ((p (i+1)).1, φ (p (i+1)).2 x) := by
  have h := stepImage M I one shifts φ hone hmul hinv x r fix p l valid i
  have si := (valid i).1
  cases hi : (p i).1 <;> cases hj : (p (i+1)).1 <;>
    simp only [hi,hj,Bool.false_eq_true,if_false,if_true] at si h ⊢
  · exact (si rfl).elim
  · rw [h]; exact edges _ _ (valid i).2.1
  · rw [h]; exact (edges _ _ (valid i).2.1).symm
  · exact (si rfl).elim

theorem oriented {n : ℕ} [NeZero n] {i j : Fin n} (h : (cycleGraph n).Adj i j) :
    j=i+1 ∨ i=j+1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    cases n with
    | zero => exact (cycleGraph_one_adj h).elim
    | succ n =>
      rcases cycleGraph_adj.mp h with e|e
      · exact .inr (sub_eq_iff_eq_add'.mp e)
      · exact .inl (sub_eq_iff_eq_add'.mp e)

theorem genericHom (hone : φ one = 1) (hmul : ∀ g h, φ (M g h) = φ g * φ h) (hinv : ∀ g, φ (I g) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ shifts → G.Adj (false,z) (true,φ d z)) (x : T) (r : A) (fix : φ r x = x) {n : ℕ} [NeZero n] (p : Fin n → Bool × A) (l : Fin n → A)
    (valid : ∀ i, (p i).1 ≠ (p (i+1)).1 ∧ l i ∈ shifts ∧ l i ≠ l (i+1) ∧
      (let a := if (p i).1 then (p (i+1)).2 else (p i).2
       let b := if (p i).1 then (p i).2 else (p (i+1)).2
       let v := M (I (M (l i) a)) b
       v = one ∨ v = r ∨ v = I r)) {i j : Fin n} (h : (cycleGraph n).Adj i j) :
    G.Adj ((p i).1,φ (p i).2 x) ((p j).1,φ (p j).2 x) := by
  rcases oriented h with e|e
  · exact e ▸ stepEdge M I one shifts φ G hone hmul hinv edges x r fix p l valid i
  · exact e ▸ (stepEdge M I one shifts φ G hone hmul hinv edges x r fix p l valid j).symm

theorem stepTurn (hone : φ one = 1) (hmul : ∀ g h, φ (M g h) = φ g * φ h) (hinv : ∀ g, φ (I g) = (φ g)⁻¹)
    (sep : ∀ z d e, d ∈ shifts → e ∈ shifts → φ d z = φ e z → d=e) (x : T) (r : A) (fix : φ r x = x) {n : ℕ} [NeZero n] (p : Fin n → Bool × A) (l : Fin n → A)
    (valid : ∀ i, (p i).1 ≠ (p (i+1)).1 ∧ l i ∈ shifts ∧ l i ≠ l (i+1) ∧
      (let a := if (p i).1 then (p (i+1)).2 else (p i).2
       let b := if (p i).1 then (p i).2 else (p (i+1)).2
       let v := M (I (M (l i) a)) b
       v = one ∨ v = r ∨ v = I r)) (i : Fin n) :
    ((p i).1,φ (p i).2 x) ≠ ((p (i+2)).1,φ (p (i+2)).2 x) := by
  intro hit
  have same := congrArg Prod.snd hit
  change φ (p i).2 x = φ (p (i+2)).2 x at same
  have first := stepImage M I one shifts φ hone hmul hinv x r fix p l valid i
  have second := stepImage M I one shifts φ hone hmul hinv x r fix p l valid (i+1)
  have add2 : i+1+1 = i+2 := by
    rw [add_assoc]; congr 1; apply Fin.ext; exact (Nat.add_mod 1 1 n).symm
  rw [add2] at second
  have si := (valid i).1
  apply (valid i).2.2.1
  cases hi : (p i).1 <;> cases hj : (p (i+1)).1 <;>
    simp only [hi,hj,Bool.false_eq_true,if_false,if_true] at si first second
  · exact (si rfl).elim
  · exact sep _ _ _ (valid i).2.1 (valid (i+1)).2.1
      (first.symm.trans (second.trans (congrArg (φ (l (i+1))) same.symm)))
  · exact sep _ _ _ (valid i).2.1 (valid (i+1)).2.1
      (first.symm.trans (same.trans second))
  · exact (si rfl).elim

theorem genericShort (hone : φ one = 1) (hmul : ∀ g h, φ (M g h) = φ g * φ h) (hinv : ∀ g, φ (I g) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ shifts → G.Adj (false,z) (true,φ d z)) (sep : ∀ z d e, d ∈ shifts → e ∈ shifts → φ d z = φ e z → d=e) (x : T) (r : A) (fix : φ r x = x) {n : ℕ} [NeZero n] (hn : n=4 ∨ n=8) (p : Fin n → Bool × A) (l : Fin n → A)
    (valid : ∀ i, (p i).1 ≠ (p (i+1)).1 ∧ l i ∈ shifts ∧ l i ≠ l (i+1) ∧
      (let a := if (p i).1 then (p (i+1)).2 else (p i).2
       let b := if (p i).1 then (p i).2 else (p (i+1)).2
       let v := M (I (M (l i) a)) b
       v = one ∨ v = r ∨ v = I r)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  rcases hn with rfl|rfl
  · exact .inl (NonfreeWalk.fourOfTrace _ (stepEdge M I one shifts φ G hone hmul hinv edges x r fix p l valid)
      (stepTurn M I one shifts φ hone hmul hinv sep x r fix p l valid))
  · have h := NonfreeWalk.eightOfAlternatingTrace _
      (stepEdge M I one shifts φ G hone hmul hinv edges x r fix p l valid)
      (stepTurn M I one shifts φ hone hmul hinv sep x r fix p l valid)
      Prod.fst (fun i => (valid i).1)
    exact h.imp_right Or.inl

theorem traceHom (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hone : φ (0,0,0) = 1)
    (hmul : ∀ g h : (ℤ × ℤ × ℤ), φ (g.1+h.1, g.2.1+h.2.1, g.2.2+h.2.2+g.1*h.2.1) = φ g * φ h)
    (hinv : ∀ g : (ℤ × ℤ × ℤ), φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → G.Adj (false,z) (true,φ d z))
    (x : T) (r : (ℤ × ℤ × ℤ)) (fix : φ r x = x) {n : ℕ} [NeZero n] (p : Fin n → Bool × (ℤ × ℤ × ℤ)) (l : Fin n → (ℤ × ℤ × ℤ))
    (valid : ∀ i, (p i).1 ≠ (p (i+1)).1 ∧ l i ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) ∧ l i ≠ l (i+1) ∧
      (let M := (fun g h : (ℤ × ℤ × ℤ) => (g.1+h.1, g.2.1+h.2.1, g.2.2+h.2.2+g.1*h.2.1))
       let I := (fun g : (ℤ × ℤ × ℤ) => (-g.1, -g.2.1, -g.2.2+g.1*g.2.1))
       let a := if (p i).1 then (p (i+1)).2 else (p i).2
       let b := if (p i).1 then (p i).2 else (p (i+1)).2
       let v := M (I (M (l i) a)) b
       v = ((0,0,0) : (ℤ × ℤ × ℤ)) ∨ v = r ∨ v = I r)) {i j : Fin n} (h : (cycleGraph n).Adj i j) :
    G.Adj ((p i).1,φ (p i).2 x) ((p j).1,φ (p j).2 x) :=
  genericHom (fun g h : (ℤ × ℤ × ℤ) => (g.1+h.1, g.2.1+h.2.1, g.2.2+h.2.2+g.1*h.2.1)) (fun g : (ℤ × ℤ × ℤ) => (-g.1, -g.2.1, -g.2.2+g.1*g.2.1)) ((0,0,0) : (ℤ × ℤ × ℤ)) ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) φ G hone hmul hinv edges x r fix p l valid h

theorem shortWord (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hone : φ (0,0,0) = 1)
    (hmul : ∀ g h : (ℤ × ℤ × ℤ), φ (g.1+h.1, g.2.1+h.2.1, g.2.2+h.2.2+g.1*h.2.1) = φ g * φ h)
    (hinv : ∀ g : (ℤ × ℤ × ℤ), φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → G.Adj (false,z) (true,φ d z))
    (sep : ∀ z d e, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → e ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → φ d z = φ e z → d=e)
    (x : T) (r : (ℤ × ℤ × ℤ)) (fix : φ r x = x) {n : ℕ} [NeZero n] (hn : n=4 ∨ n=8) (p : Fin n → Bool × (ℤ × ℤ × ℤ)) (l : Fin n → (ℤ × ℤ × ℤ))
    (valid : ∀ i, (p i).1 ≠ (p (i+1)).1 ∧ l i ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) ∧ l i ≠ l (i+1) ∧
      (let M := (fun g h : (ℤ × ℤ × ℤ) => (g.1+h.1, g.2.1+h.2.1, g.2.2+h.2.2+g.1*h.2.1))
       let I := (fun g : (ℤ × ℤ × ℤ) => (-g.1, -g.2.1, -g.2.2+g.1*g.2.1))
       let a := if (p i).1 then (p (i+1)).2 else (p i).2
       let b := if (p i).1 then (p i).2 else (p (i+1)).2
       let v := M (I (M (l i) a)) b
       v = ((0,0,0) : (ℤ × ℤ × ℤ)) ∨ v = r ∨ v = I r)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G :=
  genericShort (fun g h : (ℤ × ℤ × ℤ) => (g.1+h.1, g.2.1+h.2.1, g.2.2+h.2.2+g.1*h.2.1)) (fun g : (ℤ × ℤ × ℤ) => (-g.1, -g.2.1, -g.2.2+g.1*g.2.1)) ((0,0,0) : (ℤ × ℤ × ℤ)) ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) φ G hone hmul hinv edges sep x r fix hn p l valid

end NonfreePort


namespace NonfreePortEnd
open SimpleGraph
variable {A T : Type*} [Group A]

lemma movePowers (a b c : A) (ab : a*b = b*a*c) (ac : Commute a c) (bc : Commute b c)
    (x y : ℤ) : a^x*b^y = b^y*a^x*c^(x*y) := by
  have hr : SemiconjBy b (a*c) a := by simpa only [SemiconjBy,mul_assoc] using ab.symm
  have hh := (hr.zpow_right x).eq.symm
  rw [ac.mul_zpow] at hh
  have hx : SemiconjBy (a^x) b (b*c^x) := by
    change a^x*b = b*c^x*a^x
    rw [hh,mul_assoc,(ac.zpow_zpow x x).symm.eq]
  have hy := (hx.zpow_right y).eq
  rw [(bc.zpow_right x).mul_zpow, ← zpow_mul] at hy
  calc
    a^x*b^y = b^y*c^(x*y)*a^x := hy
    _ = b^y*a^x*c^(x*y) := by rw [mul_assoc,(ac.zpow_zpow x (x*y)).symm.eq,mul_assoc]

lemma subgroup_eighth (a b c : A) (ab : a*b=b*a*c)
    (ac : Commute a c) (bc : Commute b c) (K : Subgroup A) (j k : ℤ)
    (hu : a^(2:ℤ)*c^j ∈ K) (hv : b^(2:ℤ)*c^k ∈ K) : a^8 ∈ K := by
  let u := a^(2:ℤ)*c^j
  let v := b^(2:ℤ)*c^k
  have pair (i m : ℤ) : (a^(2:ℤ)*c^i)*(b^(2:ℤ)*c^m) =
      (a^(2:ℤ)*b^(2:ℤ))*(c^i*c^m) := by
    have h := (bc.zpow_zpow 2 i).symm.eq
    simpa only [mul_assoc] using congrArg (fun w => a^(2:ℤ)*w*c^m) h
  have pair' (i m : ℤ) : (b^(2:ℤ)*c^m)*(a^(2:ℤ)*c^i) =
      (b^(2:ℤ)*a^(2:ℤ))*(c^m*c^i) := by
    have h := (ac.zpow_zpow 2 m).symm.eq
    simpa only [mul_assoc] using congrArg (fun w => b^(2:ℤ)*w*c^i) h
  have correction : u*v = (v*u) * c^(4:ℤ) := by
    change (a^(2:ℤ)*c^j)*(b^(2:ℤ)*c^k) = ((b^(2:ℤ)*c^k)*(a^(2:ℤ)*c^j))*c^(4:ℤ)
    rw [pair,pair',movePowers a b c ab ac bc 2 2]
    norm_num only [Int.reduceMul]
    simp only [mul_assoc, ←zpow_add]
    congr 3
    omega
  have h4 : c^(4:ℤ) ∈ K := by
    have e : (v*u)⁻¹*(u*v)=c^(4:ℤ) := by rw [correction]; group
    exact e ▸ K.mul_mem (K.inv_mem (K.mul_mem hv hu)) (K.mul_mem hu hv)
  have hcj : (c^j)^4 ∈ K := by
    have e : (c^j)^4 = (c^(4:ℤ))^j := by
      rw [← zpow_natCast,← zpow_mul,← zpow_mul]
      congr 1
      ring
    exact e ▸ K.zpow_mem h4 j
  have e : u^4*((c^j)^4)⁻¹ = a^8 := by
    change (a^(2:ℤ)*c^j)^4*((c^j)^4)⁻¹ = a^8
    rw [(ac.zpow_zpow 2 j).mul_pow, mul_inv_cancel_right]
    norm_num [← pow_mul]
  exact e ▸ K.mul_mem (K.pow_mem hu 4) (K.inv_mem hcj)

lemma normalize_square (a c : A) (ac : Commute a c) (K : Subgroup A) (j : ℤ)
    (h : a^(2:ℤ)*c^j ∈ K ∨ a^(-2:ℤ)*c^j ∈ K) :
    ∃ j' : ℤ, a^(2:ℤ)*c^j' ∈ K := by
  rcases h with h|h
  · exact ⟨j,h⟩
  · refine ⟨-j,?_⟩
    have e : (a^(-2:ℤ)*c^j)⁻¹ = a^(2:ℤ)*c^(-j) := by
      rw [mul_inv_rev,←zpow_neg,←zpow_neg]
      norm_num
      simpa using (ac.zpow_zpow 2 (-j)).symm.eq
    exact e ▸ K.inv_mem h

lemma action_eighth (a b c : Equiv.Perm T) (ab : a*b=b*a*c)
    (ac : Commute a c) (bc : Commute b c) (x : T) (j k : ℤ)
    (hu : (a^(2:ℤ)*c^j) x=x ∨ (a^(-2:ℤ)*c^j) x=x)
    (hv : (b^(2:ℤ)*c^k) x=x ∨ (b^(-2:ℤ)*c^k) x=x) : (a^8) x=x := by
  let K := MulAction.stabilizer (Equiv.Perm T) x
  have toK (g : Equiv.Perm T) : g ∈ K ↔ g x=x := Iff.rfl
  obtain ⟨j',ha⟩ := normalize_square a c ac K j (hu.imp (toK _).mpr (toK _).mpr)
  obtain ⟨k',hb⟩ := normalize_square b c bc K k (hv.imp (toK _).mpr (toK _).mpr)
  exact (toK _).mp (subgroup_eighth a b c ab ac bc K j' k' ha hb)
lemma matching_orbit_shape (p : Equiv.Perm T) (x : T)
    (G : SimpleGraph (Bool × T))
    (h0 : ∀ t, G.Adj (false,t) (true,t)) (hp : ∀ t, G.Adj (false,t) (true,p t))
    (d n : ℕ) (per : Function.minimalPeriod p x = d)
    (shape : Fin n → Bool × Fin d) (inject : Function.Injective shape)
    (adj : ∀ i j, (cycleGraph n).Adj i j → ((shape i).1 != (shape j).1 && ((shape i).2 == (shape j).2 ||
      if (shape i).1 then (shape i).2.val == ((shape j).2.val+1)%d
      else (shape j).2.val == ((shape i).2.val+1)%d))) :
    cycleGraph n ⊑ G := by
  let f (i : Fin d) := p^[i.val] x
  have inj : Function.Injective f := by
    intro i j e
    apply Fin.ext
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (per ▸ i.isLt) (per ▸ j.isLt)).mp e
  have next (i j : Fin d) (h : j.val = (i.val+1)%d) : f j = p (f i) := by
    change p^[j.val] x = p (p^[i.val] x)
    have hf (k : ℕ) : p^[(k+1)%d] x = p (p^[k] x) := by
      rw [← per,Function.iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']
    rw [h]; exact hf i.val
  let lift (i : Bool × Fin d) : Bool × T := (i.1,f i.2)
  have ok (a b : Bool × Fin d) (e :
      (a.1 != b.1 && (a.2 == b.2 || if a.1 then a.2.val == (b.2.val+1)%d
        else b.2.val == (a.2.val+1)%d)) = true) : G.Adj (lift a) (lift b) := by
    rcases a with ⟨a,i⟩; rcases b with ⟨b,j⟩
    cases a <;> cases b <;> simp at e
    · rcases e with rfl|h
      · exact h0 _
      · change G.Adj (false,f i) (true,f j)
        rw [next i j h]; exact hp _
    · rcases e with rfl|h
      · exact (h0 _).symm
      · change G.Adj (true,f i) (false,f j)
        rw [next j i h]; exact (hp _).symm
  refine ⟨⟨⟨fun i => lift (shape i), fun {i j} h => ok _ _ (adj _ _ h)⟩,?_⟩⟩
  intro i j e
  apply inject
  exact Prod.ext (congrArg (fun t : Bool × T => t.1) e) (inj (congrArg (fun t : Bool × T => t.2) e))

lemma eighth_fix_short (p : Equiv.Perm T) (x : T)
    (G : SimpleGraph (Bool × T)) (h0 : ∀ t, G.Adj (false,t) (true,t))
    (hp : ∀ t, G.Adj (false,t) (true,p t)) (ne : p x ≠ x) (hf : (p^8) x = x) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have hper : Function.IsPeriodicPt (p : T → T) 8 x := hf
  have div : Function.minimalPeriod p x ∣ 2^3 := hper.minimalPeriod_dvd
  obtain ⟨d,hd,eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp div
  interval_cases d
  · have he := Function.isPeriodicPt_minimalPeriod p x
    rw [eq] at he
    exact (ne (by simpa [Function.IsPeriodicPt,Function.IsFixedPt] using he)).elim
  · apply (Or.inl)
    exact matching_orbit_shape p x G h0 hp 2 4 eq ![(true,0), (false,0), (true,1), (false,1)] (by decide) (by decide)
  · apply (fun h => Or.inr (Or.inl h))
    exact matching_orbit_shape p x G h0 hp 4 8 eq ![(true,0), (false,0), (true,1), (false,1), (true,2), (false,2), (true,3), (false,3)] (by decide) (by decide)
  · apply (fun h => Or.inr (Or.inr h))
    exact matching_orbit_shape p x G h0 hp 8 16 eq ![(true,0), (false,0), (true,1), (false,1), (true,2), (false,2), (true,3), (false,3), (true,4), (false,4), (true,5), (false,5), (true,6), (false,6), (true,7), (false,7)] (by decide) (by decide)


lemma axis_powers (f : ℤ → A) (hz : f 0 = 1) (ha : ∀ i j, f (i+j) = f i * f j)
    (n : ℤ) : f n = (f 1)^n := by
  let F : Multiplicative ℤ →* A := {
    toFun := fun v => f v.toAdd
    map_one' := hz
    map_mul' := fun i j => ha _ _ }
  have h := map_zpow F (Multiplicative.ofAdd 1) n
  change f (n • (1:ℤ)) = (f 1)^n at h
  simpa using h

lemma action_eighth_from_coords (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T)
    (hone : φ (0,0,0) = 1)
    (hmul : ∀ g h : ℤ × ℤ × ℤ,
      φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1) = φ g * φ h)
    (_hinv : ∀ g : ℤ × ℤ × ℤ, φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1) = (φ g)⁻¹)
    (x : T) (j k : ℤ)
    (hu : φ (2,0,j) x=x ∨ φ (-2,0,j) x=x)
    (hv : φ (0,2,k) x=x ∨ φ (0,-2,k) x=x) : (φ (1,0,0)^8) x=x := by
  let a := φ (1,0,0)
  let b := φ (0,1,0)
  let c := φ (0,0,1)
  have ap (n : ℤ) : φ (n,0,0) = a^n := by
    exact axis_powers (fun i => φ (i,0,0)) hone (fun i j => by simpa using hmul (i,0,0) (j,0,0)) n
  have bp (n : ℤ) : φ (0,n,0) = b^n := by
    exact axis_powers (fun i => φ (0,i,0)) hone (fun i j => by simpa using hmul (0,i,0) (0,j,0)) n
  have cp (n : ℤ) : φ (0,0,n) = c^n := by
    exact axis_powers (fun i => φ (0,0,i)) hone (fun i j => by simpa using hmul (0,0,i) (0,0,j)) n
  have ax (i z : ℤ) : a^i*c^z = φ (i,0,z) := by rw [←ap,←cp,←hmul]; simp
  have by' (i z : ℤ) : b^i*c^z = φ (0,i,z) := by rw [←bp,←cp,←hmul]; simp
  have ab : a*b=b*a*c := by dsimp only [a,b,c]; simp only [←hmul]; rfl
  have ac : Commute a c := by change φ (1,0,0)*φ (0,0,1)=φ (0,0,1)*φ (1,0,0); rw [←hmul,←hmul]; rfl
  have bc : Commute b c := by change φ (0,1,0)*φ (0,0,1)=φ (0,0,1)*φ (0,1,0); rw [←hmul,←hmul]; rfl
  apply action_eighth a b c ab ac bc x j k
  · simpa only [ax] using hu
  · simpa only [by'] using hv

end NonfreePortEnd

namespace NonfreeMain
open SimpleGraph
variable {T : Type*}

lemma force_conj (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hmul : ∀ g h : ℤ × ℤ × ℤ,
      φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1)=φ g*φ h)
    (_hinv : ∀ g : ℤ × ℤ × ℤ, φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1)=(φ g)⁻¹)
    {v w : ℤ × ℤ × ℤ} (t : ℤ × ℤ × ℤ)
    (eq : w=(v.1,v.2.1,v.2.2+t.1*v.2.1-v.1*t.2.1))
    (h : ∀ x, φ w x=x → cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) :
    ∀ x, φ v x=x → cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have conj : φ w * φ t = φ t * φ v := by
    rw [←hmul,←hmul,eq]
    congr 1
    ext <;> dsimp <;> ring
  intro x fix
  apply h (φ t x)
  simpa only [Equiv.Perm.mul_apply,fix] using congrArg (fun u : Equiv.Perm T => u x) conj

lemma root_collision (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hmul : ∀ g h : ℤ × ℤ × ℤ,
      φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1)=φ g*φ h)
    (x : T) (p : Fin 16 → Bool × (ℤ × ℤ × ℤ))
    (bad : List (ℤ × ℤ × ℤ)) (f : cycleGraph 16 →g G)
    (projection : ∀ i, f i = ((p i).1, φ (p i).2 x))
    (badPairs : ∀ i j : Fin 16, i<j → (p i).1=(p j).1 →
      let a := (p i).2
      let b := (p j).2
      (b.1-a.1,b.2.1-a.2.1,b.2.2-a.2.2+a.1*(a.2.1-b.2.1)) ∈ bad) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) ∨
      ∃ v ∈ bad, φ v x=x := by
  by_cases inj : Function.Injective f
  · exact Or.inl (Or.inr (Or.inr ⟨f.toCopy inj⟩))
  right
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp inj
  have collision (i j : Fin 16) (lt : i<j) (he : f i=f j) :
      ∃ v ∈ bad, φ v x=x := by
    rw [projection i,projection j] at he
    have side := congrArg Prod.fst he
    let a := (p i).2
    let b := (p j).2
    have coord : φ a x=φ b x := congrArg Prod.snd he
    let d : ℤ × ℤ × ℤ := (b.1-a.1,b.2.1-a.2.1,b.2.2-a.2.2+a.1*(a.2.1-b.2.1))
    refine ⟨d,badPairs i j lt side,?_⟩
    have prod : φ a * φ d = φ b := by
      rw [← hmul]
      congr 1
      ext <;> dsimp [d] <;> ring
    apply (φ a).injective
    exact (congrArg (fun u : Equiv.Perm T => u x) prod).trans coord.symm
  exact (lt_or_gt_of_ne hne).elim (fun h => collision i j h hij) (fun h => collision j i h hij.symm)

lemma center_neg (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hinv : ∀ g : ℤ × ℤ × ℤ, φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1)=(φ g)⁻¹)
    (center_case : ∀ x, φ (0,0,1) x=x → cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)
    (x : T) (fix : φ (0,0,-1) x=x) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have inv : φ (0,0,-1) = (φ (0,0,1))⁻¹ := by simpa using hinv (0,0,1)
  rw [inv, Equiv.Perm.inv_def] at fix
  exact center_case x ((φ (0,0,1)).symm_apply_eq.mp fix).symm

end NonfreeMain

/- The two sixteen-step words use the three matching labels 0, 1 and 2.
Both close in the integer Heisenberg group. If neither embeds, equal vertices on the same
side give stabilizer elements. The tables below use conjugacy to replace most collisions
by four- or eight-step cyclically nonbacktracking words. The remaining collisions force a
central generator or translations of horizontal and vertical displacement two to fix a point. -/
namespace NonfreeMain
open SimpleGraph
variable {T : Type*}

/- For each listed displacement, a fixed point closes the indicated cyclically
nonbacktracking matching word. The certificate checks its edges and labels. -/
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem closedWords (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hone : φ (0,0,0) = 1) (hmul : ∀ g h, φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1) = φ g * φ h)
    (hinv : ∀ g, φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → G.Adj (false,z) (true,φ d z))
    (sep : ∀ z d e, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → e ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → φ d z=φ e z → d=e)
    (r : (ℤ × ℤ × ℤ)) (known : r ∈ [(-3,0,-2), (-3,1,-4), (-2,-1,0), (-2,0,0), (-2,1,-1), (-1,-1,0), (-1,0,-1), (-1,1,-2), (0,-1,-1), (0,1,1), (1,-1,-1), (1,0,1), (1,1,1), (2,-1,0), (2,0,0), (-1,-2,2), (-1,2,-2), (0,-3,2), (0,-2,0), (0,2,0), (1,-3,1), (1,-2,-1)]) (x : T) (fix : φ r x=x) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- Matching labels 01210102
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-3,0,-2) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(-1,0,0)), (true,(-1,1,0)), (false,(-2,1,-1)), (true,(-2,1,-1)), (false,(-3,1,-2)), (true,(-3,1,-2))]
      ![(0,0,0), (1,0,0), (0,1,0), (1,0,0), (0,0,0), (1,0,0), (0,0,0), (0,1,0)] (by decide)
  · -- Matching labels 21210201
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-3,1,-4) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(0,1,0)), (false,(-1,1,-1)), (true,(-1,2,-1)), (false,(-2,2,-3)), (true,(-2,2,-3)), (false,(-2,1,-3)), (true,(-2,1,-3))]
      ![(0,1,0), (1,0,0), (0,1,0), (1,0,0), (0,0,0), (0,1,0), (0,0,0), (1,0,0)] (by decide)
  · -- Matching labels 21020201
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-2,-1,0) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(0,1,0)), (false,(-1,1,-1)), (true,(-1,1,-1)), (false,(-1,0,-1)), (true,(-1,0,-1)), (false,(-1,-1,-1)), (true,(-1,-1,-1))]
      ![(0,1,0), (1,0,0), (0,0,0), (0,1,0), (0,0,0), (0,1,0), (0,0,0), (1,0,0)] (by decide)
  · -- Matching labels 0101
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-2,0,0) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(-1,0,0)), (true,(-1,0,0))]
      ![(0,0,0), (1,0,0), (0,0,0), (1,0,0)] (by decide)
  · -- Matching labels 0121
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-2,1,-1) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(-1,0,0)), (true,(-1,1,0))]
      ![(0,0,0), (1,0,0), (0,1,0), (1,0,0)] (by decide)
  · -- Matching labels 0102
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-1,-1,0) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(-1,0,0)), (true,(-1,0,0))]
      ![(0,0,0), (1,0,0), (0,0,0), (0,1,0)] (by decide)
  · -- Matching labels 01021021
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-1,0,-1) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(-1,0,0)), (true,(-1,0,0)), (false,(-1,-1,0)), (true,(0,-1,-1)), (false,(0,-1,-1)), (true,(0,0,-1))]
      ![(0,0,0), (1,0,0), (0,0,0), (0,1,0), (1,0,0), (0,0,0), (0,1,0), (1,0,0)] (by decide)
  · -- Matching labels 02102121
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-1,1,-2) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(0,-1,0)), (true,(1,-1,-1)), (false,(1,-1,-1)), (true,(1,0,-1)), (false,(0,0,-1)), (true,(0,1,-1))]
      ![(0,0,0), (0,1,0), (1,0,0), (0,0,0), (0,1,0), (1,0,0), (0,1,0), (1,0,0)] (by decide)
  · -- Matching labels 02021021
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (0,-1,-1) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(0,-1,0)), (true,(0,-1,0)), (false,(0,-2,0)), (true,(1,-2,-2)), (false,(1,-2,-2)), (true,(1,-1,-2))]
      ![(0,0,0), (0,1,0), (0,0,0), (0,1,0), (1,0,0), (0,0,0), (0,1,0), (1,0,0)] (by decide)
  · -- Matching labels 12012020
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (0,1,1) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,-1,0)), (true,(1,-1,0)), (false,(0,-1,1)), (true,(0,0,1)), (false,(0,0,1)), (true,(0,1,1))]
      ![(1,0,0), (0,1,0), (0,0,0), (1,0,0), (0,1,0), (0,0,0), (0,1,0), (0,0,0)] (by decide)
  · -- Matching labels 10210212
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (1,-1,-1) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,0,0)), (true,(1,1,0)), (false,(0,1,-1)), (true,(0,1,-1)), (false,(0,0,-1)), (true,(1,0,-1))]
      ![(1,0,0), (0,0,0), (0,1,0), (1,0,0), (0,0,0), (0,1,0), (1,0,0), (0,1,0)] (by decide)
  · -- Matching labels 10120120
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (1,0,1) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,0,0)), (true,(2,0,0)), (false,(2,-1,0)), (true,(2,-1,0)), (false,(1,-1,1)), (true,(1,0,1))]
      ![(1,0,0), (0,0,0), (1,0,0), (0,1,0), (0,0,0), (1,0,0), (0,1,0), (0,0,0)] (by decide)
  · -- Matching labels 2010
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (1,1,1) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,1,0)), (false,(0,1,0)), (true,(1,1,1))]
      ![(0,1,0), (0,0,0), (1,0,0), (0,0,0)] (by decide)
  · -- Matching labels 1012
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (2,-1,0) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,0,0)), (true,(2,0,0))]
      ![(1,0,0), (0,0,0), (1,0,0), (0,1,0)] (by decide)
  · -- Matching labels 1010
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (2,0,0) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,0,0)), (true,(2,0,0))]
      ![(1,0,0), (0,0,0), (1,0,0), (0,0,0)] (by decide)
  · -- Matching labels 12010102
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-1,-2,2) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,-1,0)), (true,(1,-1,0)), (false,(0,-1,1)), (true,(0,-1,1)), (false,(-1,-1,2)), (true,(-1,-1,2))]
      ![(1,0,0), (0,1,0), (0,0,0), (1,0,0), (0,0,0), (1,0,0), (0,0,0), (0,1,0)] (by decide)
  · -- Matching labels 2021
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (-1,2,-2) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,1,0)), (false,(0,1,0)), (true,(0,2,0))]
      ![(0,1,0), (0,0,0), (0,1,0), (1,0,0)] (by decide)
  · -- Matching labels 02120201
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (0,-3,2) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(0,-1,0)), (true,(1,-1,-1)), (false,(1,-2,-1)), (true,(1,-2,-1)), (false,(1,-3,-1)), (true,(1,-3,-1))]
      ![(0,0,0), (0,1,0), (1,0,0), (0,1,0), (0,0,0), (0,1,0), (0,0,0), (1,0,0)] (by decide)
  · -- Matching labels 0202
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (0,-2,0) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(0,-1,0)), (true,(0,-1,0))]
      ![(0,0,0), (0,1,0), (0,0,0), (0,1,0)] (by decide)
  · -- Matching labels 2020
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (0,2,0) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,1,0)), (false,(0,1,0)), (true,(0,2,0))]
      ![(0,1,0), (0,0,0), (0,1,0), (0,0,0)] (by decide)
  · -- Matching labels 12120102
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (1,-3,1) fix (n := 8) (by decide)
      ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,-1,0)), (true,(2,-1,-1)), (false,(2,-2,-1)), (true,(2,-2,-1)), (false,(1,-2,1)), (true,(1,-2,1))]
      ![(1,0,0), (0,1,0), (1,0,0), (0,1,0), (0,0,0), (1,0,0), (0,0,0), (0,1,0)] (by decide)
  · -- Matching labels 0212
    exact NonfreePort.shortWord φ G hone hmul hinv edges sep x (1,-2,-1) fix (n := 4) (by decide)
      ![(false,(0,0,0)), (true,(0,0,0)), (false,(0,-1,0)), (true,(1,-1,-1))]
      ![(0,0,0), (0,1,0), (1,0,0), (0,1,0)] (by decide)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem axis0 (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hone : φ (0,0,0) = 1) (hmul : ∀ g h, φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1) = φ g * φ h)
    (hinv : ∀ g, φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → G.Adj (false,z) (true,φ d z))
    (sep : ∀ z d e, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → e ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → φ d z=φ e z → d=e)
    (center_case : ∀ x, φ (0,0,1) x=x → (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) (x : T) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) ∨ ∃ j : ℤ, φ (2,0,j) x=x ∨ φ (-2,0,j) x=x := by
  let p : Fin 16 → Bool × (ℤ × ℤ × ℤ) := ![(false,(0,0,0)), (true,(0,1,0)), (false,(0,1,0)), (true,(1,1,1)), (false,(1,1,1)), (true,(2,1,2)), (false,(2,0,2)), (true,(2,0,2)), (false,(1,0,2)), (true,(1,1,2)), (false,(0,1,1)), (true,(0,1,1)), (false,(-1,1,0)), (true,(-1,1,0)), (false,(-1,0,0)), (true,(0,0,0))]
  let l : Fin 16 → (ℤ × ℤ × ℤ) := ![(0,1,0), (0,0,0), (1,0,0), (0,0,0), (1,0,0), (0,1,0), (0,0,0), (1,0,0), (0,1,0), (1,0,0), (0,0,0), (1,0,0), (0,0,0), (0,1,0), (1,0,0), (0,0,0)]
  let bad : List (ℤ × ℤ × ℤ) := [(-3,0,-2), (-3,1,-4), (-2,-1,0), (-2,0,-2), (-2,0,-1), (-2,1,-3), (-1,-1,-1), (-1,-1,0), (-1,0,-1), (-1,0,0), (-1,1,-2), (-1,1,0), (0,-1,-1), (0,-1,0), (0,-1,2), (0,0,1), (0,1,0), (0,1,1), (1,-1,-1), (1,-1,2), (1,0,1), (1,0,2), (1,1,1), (2,-1,2), (2,0,2)]
  let f : cycleGraph 16 →g G := ⟨fun i => ((p i).1, φ (p i).2 x), fun h =>
    NonfreePort.traceHom φ G hone hmul hinv edges x (0,0,0) (by simp [hone]) p l (by decide) h⟩
  rcases root_collision φ G hmul x p bad f (fun _ => rfl) (by decide) with win | ⟨v,hv,hx⟩
  · exact Or.inl win
  simp only [bad, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (force_conj φ G hmul hinv (v := (-3,0,-2)) (w := (-3,0,-2)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-3,0,-2) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-3,1,-4)) (w := (-3,1,-4)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-3,1,-4) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-2,-1,0)) (w := (-2,-1,0)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-2,-1,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-2,0,-2)) (w := (-2,0,0)) (-1,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-2,0,0) (by decide)) x hx)
  · exact Or.inr ⟨-1, Or.inr hx⟩
  · exact Or.inl (force_conj φ G hmul hinv (v := (-2,1,-3)) (w := (-2,1,-1)) (0,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-2,1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,-1,-1)) (w := (-1,-1,0)) (-1,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,-1,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,-1,0)) (w := (-1,-1,0)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,-1,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,0,-1)) (w := (-1,0,-1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,0,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,0,0)) (w := (-1,0,-1)) (-1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,0,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,1,-2)) (w := (-1,1,-2)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,1,-2) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,1,0)) (w := (-1,1,-2)) (-1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,1,-2) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,-1,-1)) (w := (0,-1,-1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,-1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,-1,0)) (w := (0,-1,-1)) (1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,-1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,-1,2)) (w := (0,-1,-1)) (3,-3,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,-1,-1) (by decide)) x hx)
  · exact Or.inl (center_case x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,1,0)) (w := (0,1,1)) (1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,1,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,1,1)) (w := (0,1,1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,1,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,-1,-1)) (w := (1,-1,-1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,-1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,-1,2)) (w := (1,-1,-1)) (1,2,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,-1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,0,1)) (w := (1,0,1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,0,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,0,2)) (w := (1,0,1)) (-1,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,0,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,1,1)) (w := (1,1,1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,1,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (2,-1,2)) (w := (2,-1,0)) (0,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (2,-1,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (2,0,2)) (w := (2,0,0)) (-1,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (2,0,0) (by decide)) x hx)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem axis1 (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hone : φ (0,0,0) = 1) (hmul : ∀ g h, φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1) = φ g * φ h)
    (hinv : ∀ g, φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → G.Adj (false,z) (true,φ d z))
    (sep : ∀ z d e, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → e ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → φ d z=φ e z → d=e)
    (center_case : ∀ x, φ (0,0,1) x=x → (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) (x : T) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) ∨ ∃ j : ℤ, φ (0,2,j) x=x ∨ φ (0,-2,j) x=x := by
  let p : Fin 16 → Bool × (ℤ × ℤ × ℤ) := ![(false,(0,0,0)), (true,(1,0,0)), (false,(1,0,0)), (true,(1,1,0)), (false,(1,1,0)), (true,(1,2,0)), (false,(0,2,-2)), (true,(0,2,-2)), (false,(0,1,-2)), (true,(1,1,-1)), (false,(1,0,-1)), (true,(1,0,-1)), (false,(1,-1,-1)), (true,(1,-1,-1)), (false,(0,-1,0)), (true,(0,0,0))]
  let l : Fin 16 → (ℤ × ℤ × ℤ) := ![(1,0,0), (0,0,0), (0,1,0), (0,0,0), (0,1,0), (1,0,0), (0,0,0), (0,1,0), (1,0,0), (0,1,0), (0,0,0), (0,1,0), (0,0,0), (1,0,0), (0,1,0), (0,0,0)]
  let bad : List (ℤ × ℤ × ℤ) := [(-1,-2,2), (-1,-1,1), (-1,-1,2), (-1,0,-2), (-1,0,0), (-1,0,1), (-1,1,-3), (-1,1,0), (-1,2,-4), (0,-3,2), (0,-2,1), (0,-2,2), (0,-1,0), (0,-1,1), (0,0,-1), (0,1,-2), (0,1,-1), (0,2,-2), (1,-3,1), (1,-2,1), (1,-1,-1), (1,-1,1), (1,0,-1), (1,0,0), (1,1,0)]
  let f : cycleGraph 16 →g G := ⟨fun i => ((p i).1, φ (p i).2 x), fun h =>
    NonfreePort.traceHom φ G hone hmul hinv edges x (0,0,0) (by simp [hone]) p l (by decide) h⟩
  rcases root_collision φ G hmul x p bad f (fun _ => rfl) (by decide) with win | ⟨v,hv,hx⟩
  · exact Or.inl win
  simp only [bad, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,-2,2)) (w := (-1,-2,2)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,-2,2) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,-1,1)) (w := (-1,-1,0)) (0,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,-1,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,-1,2)) (w := (-1,-1,0)) (1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,-1,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,0,-2)) (w := (-1,0,-1)) (-1,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,0,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,0,0)) (w := (-1,0,-1)) (-1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,0,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,0,1)) (w := (-1,0,-1)) (-2,-2,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,0,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,1,-3)) (w := (-1,1,-2)) (0,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,1,-2) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,1,0)) (w := (-1,1,-2)) (-1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,1,-2) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (-1,2,-4)) (w := (-1,2,-2)) (1,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (-1,2,-2) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,-3,2)) (w := (0,-3,2)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,-3,2) (by decide)) x hx)
  · exact Or.inr ⟨1, Or.inr hx⟩
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,-2,2)) (w := (0,-2,0)) (1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,-2,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,-1,0)) (w := (0,-1,-1)) (1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,-1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,-1,1)) (w := (0,-1,-1)) (2,-2,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,-1,-1) (by decide)) x hx)
  · exact Or.inl (center_neg φ G hinv center_case x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,1,-2)) (w := (0,1,1)) (3,-3,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,1,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,1,-1)) (w := (0,1,1)) (2,-2,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,1,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (0,2,-2)) (w := (0,2,0)) (1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (0,2,0) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,-3,1)) (w := (1,-3,1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,-3,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,-2,1)) (w := (1,-2,-1)) (1,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,-2,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,-1,-1)) (w := (1,-1,-1)) (0,0,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,-1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,-1,1)) (w := (1,-1,-1)) (1,1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,-1,-1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,0,-1)) (w := (1,0,1)) (-2,-2,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,0,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,0,0)) (w := (1,0,1)) (-1,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,0,1) (by decide)) x hx)
  · exact Or.inl (force_conj φ G hmul hinv (v := (1,1,0)) (w := (1,1,1)) (0,-1,0) (by decide)
      (closedWords φ G hone hmul hinv edges sep (1,1,1) (by decide)) x hx)

/-- If the commutator of the two matching permutations is central, one of the two
sixteen-step words embeds, or its repeated vertices force a four-, eight- or sixteen-cycle. -/
theorem classTwo_short [Nonempty T] (φ : (ℤ × ℤ × ℤ) → Equiv.Perm T) (G : SimpleGraph (Bool × T))
    (hone : φ (0,0,0) = 1) (hmul : ∀ g h, φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1) = φ g * φ h)
    (hinv : ∀ g, φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1) = (φ g)⁻¹)
    (edges : ∀ z d, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → G.Adj (false,z) (true,φ d z))
    (sep : ∀ z d e, d ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → e ∈ ([(0,0,0),(1,0,0),(0,1,0)] : List (ℤ × ℤ × ℤ)) → φ d z=φ e z → d=e)
    (center_case : ∀ x, φ (0,0,1) x=x → (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
  obtain ⟨x⟩ := ‹Nonempty T›
  rcases axis0 φ G hone hmul hinv edges sep center_case x with win | ⟨j,hj⟩
  · exact win
  rcases axis1 φ G hone hmul hinv edges sep center_case x with win | ⟨k,hk⟩
  · exact win
  have hf := NonfreePortEnd.action_eighth_from_coords φ hone hmul hinv x j k hj hk
  apply NonfreePortEnd.eighth_fix_short (φ (1,0,0)) x G _ _ _ hf
  · intro z; simpa [hone] using edges z (0,0,0) (by decide)
  · intro z; exact edges z (1,0,0) (by decide)
  · intro h
    have eq := sep x (1,0,0) (0,0,0) (by decide) (by decide) (by simpa [hone] using h)
    exact (by decide : ((1,0,0) : ℤ × ℤ × ℤ) ≠ (0,0,0)) eq
end NonfreeMain

namespace NonfreePerm
open SimpleGraph
open scoped commutatorElement
variable {A : Type*} [Group A]

lemma commutatorCorrection {A : Type*} [Group A] (p q : A)
    (pc : Commute p ⁅p,q⁆) (qc : Commute q ⁅p,q⁆) : p*q = q*p*⁅p,q⁆ := by
  calc
    p*q = ⁅p,q⁆*(q*p) := by simp [commutatorElement_def, mul_assoc]
    _ = q*p*⁅p,q⁆ := (qc.symm.mul_right pc.symm).eq


theorem normalForm_mul (a b c : A) (ab : a*b = b*a*c) (ac : Commute a c) (bc : Commute b c)
    (g h : ℤ × ℤ × ℤ) :
    b^(g.2.1+h.2.1)*a^(g.1+h.1)*c^(g.2.2+h.2.2+g.1*h.2.1) =
      (b^g.2.1*a^g.1*c^g.2.2)*(b^h.2.1*a^h.1*c^h.2.2) := by
  rw [zpow_add,zpow_add,zpow_add,zpow_add]
  symm
  calc
    (b^g.2.1*a^g.1*c^g.2.2)*(b^h.2.1*a^h.1*c^h.2.2) =
      (b^g.2.1*a^g.1)*(b^h.2.1*a^h.1)*c^g.2.2*c^h.2.2 := by
        have hc := ((bc.symm.zpow_zpow g.2.2 h.2.1).mul_right (ac.symm.zpow_zpow g.2.2 h.1)).eq
        simpa only [mul_assoc] using congrArg (fun v => (b^g.2.1*a^g.1)*v*c^h.2.2) hc
    _ = b^g.2.1*(b^h.2.1*a^g.1*c^(g.1*h.2.1))*a^h.1*c^g.2.2*c^h.2.2 := by
        rw [← NonfreePortEnd.movePowers a b c ab ac bc]; simp only [mul_assoc]
    _ = _ := by
        have hc := (ac.symm.zpow_zpow (g.1*h.2.1) h.1).eq
        calc
          _ = (b^g.2.1*b^h.2.1*a^g.1)*(c^(g.1*h.2.1)*a^h.1)*c^g.2.2*c^h.2.2 := by simp only [mul_assoc]
          _ = (b^g.2.1*b^h.2.1*a^g.1)*(a^h.1*c^(g.1*h.2.1))*c^g.2.2*c^h.2.2 := by rw [hc]
          _ = _ := by
            have eq := ((Commute.zpow_zpow_self c (g.1*h.2.1) g.2.2).mul_right
              (Commute.zpow_zpow_self c (g.1*h.2.1) h.2.2)).eq
            simpa only [mul_assoc] using congrArg (fun v => b^g.2.1*b^h.2.1*a^g.1*a^h.1*v) eq


theorem fixed_short {T : Type*} (G : SimpleGraph (Bool × T)) (p q c : Equiv.Perm T)
    (ab : p*q=q*p*c) (pc : Commute p c) (qc : Commute q c)
    (separated : ∀ z, p z ≠ z ∧ q z ≠ z ∧ p z ≠ q z)
    (idAdj : ∀ z, G.Adj (false,z) (true,z))
    (pAdj : ∀ z, G.Adj (false,z) (true,p z))
    (qAdj : ∀ z, G.Adj (false,z) (true,q z))
    (x : T) (fix : c x=x) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have at_fixed (y : T) (hy : c y=y) : p (q y)=q (p y) := by
    simpa only [Equiv.Perm.mul_apply,hy] using congrArg (fun v : Equiv.Perm T => v y) ab
  have member (u : Equiv.Perm T) (cu : Commute c u) : c (u x)=u x := by
    simpa only [Equiv.Perm.mul_apply,fix] using congrArg (fun v : Equiv.Perm T => v x) cu.eq
  apply OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0 G p q separated idAdj pAdj qAdj x
  · exact at_fixed x fix
  · exact at_fixed (p x) (member p pc.symm)
  · apply at_fixed
    simpa only [Equiv.Perm.inv_def] using member q⁻¹ qc.symm.inv_right
  · exact at_fixed (q x) (member q qc.symm)

end NonfreePerm

open SimpleGraph
open scoped commutatorElement

theorem classTwoPerm_short {T : Type*} [Nonempty T]
    (G : SimpleGraph (Bool × T)) (p q : Equiv.Perm T)
    (separated : ∀ z, p z ≠ z ∧ q z ≠ z ∧ p z ≠ q z)
    (idAdj : ∀ z, G.Adj (false,z) (true,z))
    (pAdj : ∀ z, G.Adj (false,z) (true,p z))
    (qAdj : ∀ z, G.Adj (false,z) (true,q z))
    (pc : Commute p ⁅p,q⁆) (qc : Commute q ⁅p,q⁆) :
    SimpleGraph.cycleGraph 4 ⊑ G ∨ SimpleGraph.cycleGraph 8 ⊑ G ∨
      SimpleGraph.cycleGraph 16 ⊑ G := by

  let c := ⁅p,q⁆
  have ab : p*q=q*p*c := NonfreePerm.commutatorCorrection p q pc qc
  let φ (g : ℤ × ℤ × ℤ) : Equiv.Perm T := q^g.2.1*p^g.1*c^g.2.2
  have one : φ (0,0,0)=1 := by simp [φ]
  have mul (g h : ℤ × ℤ × ℤ) :
      φ (g.1+h.1,g.2.1+h.2.1,g.2.2+h.2.2+g.1*h.2.1)=φ g * φ h :=
    NonfreePerm.normalForm_mul p q c ab pc qc g h
  have inv (g : ℤ × ℤ × ℤ) :
      φ (-g.1,-g.2.1,-g.2.2+g.1*g.2.1)=(φ g)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← mul]
    convert one using 2
    ext <;> dsimp <;> ring
  have actX : φ (1,0,0) = p := by simp [φ]
  have actY : φ (0,1,0) = q := by simp [φ]
  have actC : φ (0,0,1) = c := by simp [φ]
  apply NonfreeMain.classTwo_short φ G one mul inv
  · intro z d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · simpa only [one, Equiv.Perm.one_apply] using idAdj z
    · simpa only [actX] using pAdj z
    · simpa only [actY] using qAdj z
  · intro z d e hd he eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd he
    obtain ⟨hp,hq,hpq⟩ := separated z
    rcases hd with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl
    · rfl
    · exact (hp (by simpa only [one, Equiv.Perm.one_apply, actX] using eq.symm)).elim
    · exact (hq (by simpa only [one, Equiv.Perm.one_apply, actY] using eq.symm)).elim
    · exact (hp (by simpa only [one, Equiv.Perm.one_apply, actX] using eq)).elim
    · rfl
    · exact (hpq (by simpa only [actX,actY] using eq)).elim
    · exact (hq (by simpa only [one, Equiv.Perm.one_apply, actY] using eq)).elim
    · exact (hpq (by simpa only [actX,actY] using eq.symm)).elim
    · rfl
  · intro z hz
    exact NonfreePerm.fixed_short G p q c ab pc qc separated idAdj pAdj qAdj z (actC ▸ hz)

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.H2 := by
  intro regular nonfree X _ _ p q separated density
  classical
  let G := SimpleGraph.fromRel (fun u v : Bool × X =>
    u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))
  change ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G
  by_cases central : Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆
  · have small := classTwoPerm_short G p q separated
      (fun z => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩)
      (fun z => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩)
      (fun z => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩) central.1 central.2
    rcases small with h | h | h
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩
    · exact ⟨4,by decide,h⟩
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  by_cases hasFix : ∃ g ∈ K, g ≠ 1 ∧ ∃ x : X, g x=x
  · exact nonfree X p q separated density central hasFix
  let a : K := ⟨p, Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q, Subgroup.subset_closure (by simp)⟩
  obtain ⟨z⟩ := ‹Nonempty X›
  let ev (g : K) := (g : Equiv.Perm X) z
  have an : a ≠ 1 := fun eq => (separated z).1 (congrArg ev eq)
  have bn : b ≠ 1 := fun eq => (separated z).2.1 (congrArg ev eq)
  have ab : a ≠ b := fun eq => (separated z).2.2 (congrArg ev eq)
  have nc : ¬(Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆) := by
    rintro ⟨ac,bc⟩
    apply central
    exact ⟨ac.map K.subtype,bc.map K.subtype⟩
  obtain ⟨k,hk,subcycle⟩ := regular K a b an bn ab nc
  have inj : Function.Injective ev := by
    intro g h eq
    have trivial : h⁻¹*g = 1 := by
      by_contra nontrivial
      apply hasFix
      refine ⟨↑(h⁻¹*g), (h⁻¹*g).property, fun t => nontrivial (Subtype.ext t), z, ?_⟩
      change (h.val).symm (ev g) = z
      rw [eq]
      exact h.val.symm_apply_apply _
    exact (inv_mul_eq_one.mp trivial).symm
  let j : Bool × K ↪ Bool × X := (Function.Embedding.refl Bool).prodMap ⟨ev,inj⟩
  have transfer (s t : Bool × K) (hs : s.1=false) (ht : t.1=true)
      (edge : t.2=s.2 ∨ t.2=a*s.2 ∨ t.2=b*s.2) :
      (j s).1=false ∧ (j t).1=true ∧
        ((j t).2=(j s).2 ∨ (j t).2=p (j s).2 ∨ (j t).2=q (j s).2) := by
    refine ⟨hs,ht,?_⟩
    rcases edge with h|h|h
    · exact Or.inl (congrArg ev h)
    · exact Or.inr (Or.inl (congrArg ev h))
    · exact Or.inr (Or.inr (congrArg ev h))
  refine ⟨k,hk,subcycle.trans (isContained_iff_exists_le_comap.mpr ⟨j,?_⟩)⟩
  intro s t edge
  refine ⟨fun eq => edge.1 (j.injective eq),?_⟩
  rcases edge.2 with ⟨hs,ht,e⟩ | ⟨ht,hs,e⟩
  · exact Or.inl (transfer s t hs ht e)
  · exact Or.inr (transfer t s ht hs e)

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1
