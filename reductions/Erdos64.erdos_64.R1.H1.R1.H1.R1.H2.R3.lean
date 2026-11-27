import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1

/-!
Deleting a hexagon leaves six distinct degree-two terminals. Complete them by a
matching and use induction on the graph order to constrain every terminal linkage.
The girth split also appears in Julius Tranquilli, arXiv:2608.02675. The argument
below does not use a finite census.
-/
namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R3
open SimpleGraph Finset
open scoped Classical


/-- The high-girth case of the uncolored cubic bipartite graph problem. -/
def H1 : Prop := ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (s : V → Bool),
  (∀ {a b}, G.Adj a b → s a ≠ s b) → (∀ x, (G.neighborSet x).ncard = 3) →
  (¬ cycleGraph 4 ⊑ G) → (¬ cycleGraph 6 ⊑ G) → (¬ cycleGraph 8 ⊑ G) →
  ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G

/-- Six-terminal linkage problem after deleting a hexagon. Every simple bipartite
perfect matching completion of the terminals has a power cycle. Find disjoint
exterior stretches and hexagon arcs in cyclic order. The positions of the latter
use at most the six distinct labels in S. -/
def H2 : Prop := ∀ (W : Type) [Fintype W] (H : SimpleGraph W) (s : W → Bool) (t : Fin 6 ↪ W),
  (∀ {a b}, H.Adj a b → s a ≠ s b) →
  (∀ x, (H.neighborSet x).ncard + (if x ∈ Set.range t then 1 else 0) = 3) →
  (∀ i, s (t i) ≠ s (t (i+1))) →
  (∀ i j, H.Adj (t i) (t j) → j=i+3) →
  (∀ i, ¬ (H.Adj (t i) (t (i+3)) ∧ H.Adj (t (i+1)) (t (i+4)))) →
  (∀ k : ℕ, 2 ≤ k → ¬ cycleGraph (2^k) ⊑ H) →
  (∀ (i j : Fin 6), i ≠ j → ∀ (P : H.Walk (t j) (t i)) (A : (cycleGraph 6).Walk i j),
    P.IsPath → A.IsPath → ∀ k : ℕ, 2 ≤ k → P.length+A.length+2 ≠ 2^k) →
  (∀ σ : Fin 6 → Fin 6, Function.Involutive σ →
    (∀ i, s (t i) ≠ s (t (σ i))) → (∀ i, ¬ H.Adj (t i) (t (σ i))) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ fromRel (fun a b =>
      H.Adj a b ∨ ∃ i, a=t i ∧ b=t (σ i))) →
  ∃ (k : ℕ) (_ : 2 ≤ k) (S : Finset (Fin (2^k)))
    (a : {i // i ∉ S} ↪ W) (b : {i // i ∈ S} ↪ Fin 6),
    (∀ i j, (cycleGraph (2^k)).Adj i.val j.val → H.Adj (a i) (a j)) ∧
    (∀ i j, (cycleGraph (2^k)).Adj i.val j.val → (cycleGraph 6).Adj (b i) (b j)) ∧
    (∀ i j, (cycleGraph (2^k)).Adj i.val j.val → a j=t (b i))



section
variable {V : Type} {G : SimpleGraph V}

/-- In a graph without a square, two distinct vertices have at most one common neighbor. -/
private theorem common (no4 : ¬ cycleGraph 4 ⊑ G) {a b c d : V}
    (ab : a ≠ b) (ac : G.Adj a c) (bc : G.Adj b c)
    (ad : G.Adj a d) (bd : G.Adj b d) : c = d := by
  by_contra cd
  let f : Fin 4 → V := ![a,c,b,d]
  have inj : Function.Injective f := by
    intro i j eq
    have ca := ac.ne
    have cb := bc.ne
    have da := ad.ne
    have db := bd.ne
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let h : cycleGraph 4 →g G := ⟨f,by
    intro i j e
    fin_cases i <;> fin_cases j <;> first | exact (of_decide_eq_false rfl e).elim | assumption | exact ac | exact ac.symm | exact bc | exact bc.symm | exact ad | exact ad.symm | exact bd | exact bd.symm⟩
  exact no4 ⟨h.toCopy inj⟩

/-- A hexagon and its six outgoing edges in a cubic bipartite graph without 4- and
8-cycles. The exterior endpoints are distinct. Only one opposite pair can be adjacent. -/
private theorem frame (s : V → Bool) (color : ∀ {a b}, G.Adj a b → s a ≠ s b)
    (no4 : ¬ cycleGraph 4 ⊑ G) (no8 : ¬ cycleGraph 8 ⊑ G)
    (f : Fin 6 ↪ V) (along : ∀ i, G.Adj (f i) (f (i+1)))
    (t : Fin 6 → V) (spoke : ∀ i, G.Adj (f i) (t i))
    (left : ∀ i, t i ≠ f (i-1)) (right : ∀ i, t i ≠ f (i+1)) :
    (∀ i j, t i ≠ f j) ∧ Function.Injective t ∧
    (∀ i j, G.Adj (t i) (t j) → j=i+3) ∧
    (∀ i, ¬(G.Adj (t i) (t (i+3)) ∧ G.Adj (t (i+1)) (t (i+4)))) := by
  have sides (i j : Fin 6) : s (f i)=s (f j) ↔ i.val%2=j.val%2 := by
    let b := fun i : Fin 6 => s (f i)
    have alt (i : Fin 6) : b i ≠ b (i+1) := color (along i)
    have one := alt 0
    have two := alt 1
    have three := alt 2
    have four := alt 3
    have five := alt 4
    change b i = b j ↔ _
    change b 0 ≠ b 1 at one
    change b 1 ≠ b 2 at two
    change b 2 ≠ b 3 at three
    change b 3 ≠ b 4 at four
    change b 4 ≠ b 5 at five
    have pat := (by decide : ∀ a b c d e f : Bool, a≠b → b≠c → c≠d → d≠e → e≠f → b=(!a) ∧ c=a ∧ d=(!a) ∧ e=a ∧ f=(!a)) _ _ _ _ _ _ one two three four five
    have rep : ∀ i : Fin 6, b i = if i.val%2=0 then b 0 else !(b 0) := by
      intro a
      fin_cases a <;> first | rfl | exact pat.1 | exact pat.2.1 | exact pat.2.2.1 | exact pat.2.2.2.1 | exact pat.2.2.2.2
    rw [rep i,rep j]
    split <;> split <;> cases b 0 <;> simp <;> omega
  have odd (i j : Fin 6) (h : i.val%2≠j.val%2) : j=i+1 ∨ i=j+1 ∨ j=i+3 :=
    (by decide : ∀ a b : Fin 6, a.val%2≠b.val%2 → b=a+1 ∨ a=b+1 ∨ b=a+3) i j h
  have even (i j : Fin 6) (h : i.val%2=j.val%2) : i=j ∨ j=i+2 ∨ i=j+2 :=
    (by decide : ∀ a b : Fin 6, a.val%2=b.val%2 → a=b ∨ b=a+2 ∨ a=b+2) i j h
  have step (i : Fin 6) : G.Adj (f (i+1)) (f (i+2)) := by simpa [add_assoc] using along (i+1)
  have step' (i : Fin 6) : G.Adj (f (i+2)) (f (i+3)) := by simpa [add_assoc] using along (i+2)
  have distinct (i : Fin 6) : f i ≠ f (i+2) :=
    fun h => (by decide : ∀ a : Fin 6, a≠a+2) i (f.injective h)
  have chord (i) : ¬ G.Adj (f i) (f (i+3)) := by
    intro h
    have same := common no4 (distinct i) (along i) (step i).symm h (step' i)
    exact (by decide : ∀ a : Fin 6, a+1≠a+3) i (f.injective same)
  have disjoint (i j : Fin 6) : t i ≠ f j := by
    intro eq
    have e := spoke i
    rw [eq] at e
    have o := odd i j (fun h => color e ((sides i j).mpr h))
    rcases o with rfl|back|rfl
    · exact right i eq
    · have h : j=i-1 := by rw [back]; simp
      exact left i (eq.trans (congrArg f h))
    · exact chord i e
  have sameSide {a b c : Bool} (h : a ≠ c) (g : b ≠ c) : a=b := by
    cases a <;> cases b <;> cases c <;> simp_all
  have apart (i : Fin 6) : t i ≠ t (i+2) := by
    intro eq
    have h := spoke (i+2)
    rw [←eq] at h
    exact disjoint i (i+1) (common no4 (distinct i) (spoke i) h (along i) (step i).symm)
  have ti : Function.Injective t := by
    intro i j eq
    have a := color (spoke i)
    have b := color (spoke j)
    rw [←eq] at b
    rcases even i j ((sides i j).mp (sameSide a b)) with h|rfl|rfl
    · exact h
    · exact (apart i eq).elim
    · exact (apart j eq.symm).elim
  have nextPort (i) : ¬ G.Adj (t i) (t (i+1)) := by
    intro e
    have h := common no4 (Ne.symm (disjoint (i+1) i)) (spoke i) e.symm (along i) (spoke (i+1)).symm
    exact disjoint i (i+1) h
  have opposite (i j) (e : G.Adj (t i) (t j)) : j=i+3 := by
    have a := color (spoke i)
    have b := color (spoke j)
    have c := color e
    have diff : s (f i) ≠ s (f j) := by
      intro h
      rw [←h] at b
      exact c (sameSide (Ne.symm a) (Ne.symm b))
    rcases odd i j (fun h => diff ((sides i j).mpr h)) with rfl|rfl|h
    · exact (nextPort i e).elim
    · exact (nextPort j e.symm).elim
    · exact h
  refine ⟨disjoint,ti,opposite,?_⟩
  intro i ⟨first,second⟩
  let v : Bool × Fin 6 → V := fun (b,j) => if b then t (i+j) else f (i+j)
  have injv : Function.Injective v := by
    rintro ⟨b,j⟩ ⟨c,k⟩ eq
    cases b <;> cases c <;> simp only [v,Bool.false_eq_true,if_false,if_true] at eq
    · exact Prod.ext rfl (add_left_cancel (f.injective eq))
    · exact (disjoint _ _ eq.symm).elim
    · exact (disjoint _ _ eq).elim
    · exact Prod.ext rfl (add_left_cancel (ti eq))
  let w : Fin 8 → Bool × Fin 6 := ![(false,0),(true,0),(true,3),(false,3),
    (false,4),(true,4),(true,1),(false,1)]
  have winj : Function.Injective w := by decide
  have edge : ∀ j : Fin 8, G.Adj (v (w j)) (v (w (j+1))) := by
    intro j
    fin_cases j
    · simpa [w,v] using spoke i
    · simpa [w,v] using first
    · exact (spoke (i+3)).symm
    · simpa [w,v,add_assoc] using along (i+3)
    · exact spoke (i+4)
    · exact second.symm
    · exact (spoke (i+1)).symm
    · simpa [v,w] using (along i).symm
  let φ : cycleGraph 8 →g G := ⟨v ∘ w,by
    intro a b h
    rcases cycleGraph_adj.mp h with h|h
    · have k : a=b+1 := by grind
      rw [k]; exact (edge b).symm
    · have k : b=a+1 := by grind
      rw [k]; exact edge a⟩
  exact no8 ⟨φ.toCopy (injv.comp winj)⟩

end


section
variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- List all three neighbors at each vertex of the chosen hexagon. -/
private theorem third (cubic : ∀ x, (G.neighborSet x).ncard = 3) (f : Fin 6 ↪ V)
    (along : ∀ i, G.Adj (f i) (f (i+1))) (i : Fin 6) :
    ∃ t, G.Adj (f i) t ∧ t ≠ f (i-1) ∧ t ≠ f (i+1) ∧
      ∀ w, G.Adj (f i) w ↔ w=f (i-1) ∨ w=f (i+1) ∨ w=t := by
  classical
  let N := (G.neighborSet (f i)).toFinset
  have size : N.card=3 := by simpa [N,Set.ncard_eq_toFinset_card'] using cubic (f i)
  let pair : Finset V := {f (i-1),f (i+1)}
  have ne : f (i-1)≠f (i+1) := fun h =>
    (by decide : ∀ j : Fin 6, j-1≠j+1) i (f.injective h)
  have two : pair.card=2 := by simp [pair,ne]
  have sub : pair ⊆ N := by
    intro w h
    simp only [pair,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl
    · simpa [N] using (along (i-1)).symm
    · simpa [N] using along i
  obtain ⟨t,ht,hn⟩ := Finset.not_subset.mp (show ¬N ⊆ pair by
    intro h; have := card_le_card h; omega)
  have newN : insert t pair=N := eq_of_subset_of_card_le (insert_subset ht sub)
    (by rw [card_insert_of_notMem hn,two,size])
  have nt : t≠f (i-1) ∧ t≠f (i+1) := by simpa [pair] using hn
  refine ⟨t,by simpa [N] using ht,nt.1,nt.2,?_⟩
  intro w
  change w ∈ G.neighborSet (f i) ↔ _
  rw [←Set.mem_toFinset,show (G.neighborSet (f i)).toFinset=N from rfl,←newN]
  simp only [pair,mem_insert,mem_singleton]; tauto

/-- Restore cubic degree by joining the six ports in any allowable matching. -/
private theorem completePorts {W : Type} [Fintype W] {H : SimpleGraph W} (s : W → Bool)
    (color : ∀ {a b}, H.Adj a b → s a ≠ s b) (t : Fin 6 ↪ W)
    (deg : ∀ x, (H.neighborSet x).ncard + (if x ∈ Set.range t then 1 else 0) = 3)
    (σ : Fin 6 → Fin 6) (inv : Function.Involutive σ)
    (diff : ∀ i, s (t i) ≠ s (t (σ i))) (fresh : ∀ i, ¬ H.Adj (t i) (t (σ i))) :
    let J := fromRel (fun a b => H.Adj a b ∨ ∃ i, a=t i ∧ b=t (σ i))
    (∀ {a b}, J.Adj a b → s a ≠ s b) ∧ (∀ x, (J.neighborSet x).ncard=3) := by
  classical
  let R (a b : W) := H.Adj a b ∨ ∃ i, a=t i ∧ b=t (σ i)
  let J := fromRel R
  have rs {a b} (h : R a b) : R b a := by
    rcases h with e|⟨i,rfl,rfl⟩
    · exact Or.inl e.symm
    · exact Or.inr ⟨σ i,rfl,by rw [inv]⟩
  have rc {a b} (h : R a b) : s a ≠ s b := by
    rcases h with e|⟨i,rfl,rfl⟩
    · exact color e
    · exact diff i
  have eqAdj (a b) : J.Adj a b ↔ R a b := by
    change (a≠b ∧ (R a b ∨ R b a)) ↔ _
    exact ⟨fun h => h.2.elim id rs,fun h => ⟨fun e => rc h (congrArg s e),Or.inl h⟩⟩
  refine ⟨fun {a b} e => rc ((eqAdj a b).mp e),?_⟩
  intro x
  by_cases mem : x ∈ Set.range t
  · obtain ⟨i,rfl⟩ := mem
    have N : J.neighborSet (t i)=insert (t (σ i)) (H.neighborSet (t i)) := by
      ext y
      rw [SimpleGraph.mem_neighborSet,eqAdj]
      change (H.Adj _ _ ∨ _) ↔ y=t (σ i) ∨ H.Adj _ _
      constructor
      · rintro (e|⟨j,hj,h⟩)
        · exact Or.inr e
        · exact Or.inl (by rwa [←t.injective hj] at h)
      · rintro (rfl|e)
        · exact Or.inr ⟨i,rfl,rfl⟩
        · exact Or.inl e
    have d := deg (t i)
    rw [if_pos ⟨i,rfl⟩] at d
    rw [N,Set.ncard_insert_of_notMem (s:=H.neighborSet (t i)) (fresh i)]
    exact d
  · have N : J.neighborSet x=H.neighborSet x := by
      ext y
      rw [SimpleGraph.mem_neighborSet,eqAdj,SimpleGraph.mem_neighborSet]
      exact ⟨fun h => h.elim id (fun ⟨i,e,_⟩ => (mem ⟨i,e.symm⟩).elim),Or.inl⟩
    have d := deg x
    change (J.neighborSet x).ncard=3
    rw [N]; simpa [mem] using d

end


/-- One exterior path and one hexagon arc already produce a simple cycle whose
length is the sum of their lengths plus the two spokes. -/
theorem twoSpokes {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : (cycleGraph 6).Copy G) (e : H.Copy G) (t : Fin 6 → W)
    (disjoint : ∀ i w, f i ≠ e w) (spoke : ∀ i, G.Adj (f i) (e (t i)))
    {i j : Fin 6} (P : H.Walk (t j) (t i)) (A : (cycleGraph 6).Walk i j)
    (hP : P.IsPath) (hA : A.IsPath) {m : ℕ} (hm : 2 < m) (len : P.length+A.length+2=m) :
    cycleGraph m ⊑ G := by
  let p := P.map e.toHom
  let a := A.map f.toHom
  let middle := a.append (Walk.cons (spoke j) p)
  let closed := Walk.cons (spoke i).symm middle
  have nonoverlap : a.support.Disjoint p.support := by
    intro x hx hy
    rw [show a.support=A.support.map f.toHom from Walk.support_map _ _] at hx
    rw [show p.support=P.support.map e.toHom from Walk.support_map _ _] at hy
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨w,_,eq⟩ := List.mem_map.mp hy
    exact disjoint v w eq.symm
  have simple : middle.IsPath := by
    rw [Walk.isPath_def]
    have nod := ((Walk.isPath_map_iff_of_injective f.injective).mpr hA).support_nodup
    have nod' := ((Walk.isPath_map_iff_of_injective e.injective).mpr hP).support_nodup
    simpa only [middle,Walk.support_append,Walk.support_cons,List.tail_cons] using
      List.nodup_append'.mpr ⟨nod,nod',nonoverlap⟩
  have length : closed.length=m := by
    simp only [closed,middle,p,a,Walk.length_cons,Walk.length_append,Walk.length_map]
    omega
  apply (cycleGraph_isContained_iff hm).mpr
  refine ⟨_,closed,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,by omega⟩,length⟩
  simpa [closed] using simple


/-- The order induction uses every legal matching completion on the smaller exterior. -/
private theorem byOrder (h1 : H1) (h2 : H2) (n : ℕ) :
    ∀ (V : Type) [Fintype V] [Nonempty V], Fintype.card V=n →
    ∀ (G : SimpleGraph V) (s : V → Bool), (∀ {a b}, G.Adj a b → s a ≠ s b) →
    (∀ x, (G.neighborSet x).ncard=3) → ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ size G s color cubic
    by_cases c4 : cycleGraph 4 ⊑ G
    · exact ⟨2,le_rfl,c4⟩
    by_cases c8 : cycleGraph 8 ⊑ G
    · exact ⟨3,by decide,c8⟩
    by_cases c6 : cycleGraph 6 ⊑ G
    swap
    · exact h1 V G s color cubic c4 c6 c8
    obtain ⟨hex⟩ := c6
    let f := hex.toEmbedding
    have along (i : Fin 6) : G.Adj (f i) (f (i+1)) :=
      hex.toHom.map_rel' ((by decide : ∀ j : Fin 6, (cycleGraph 6).Adj j (j+1)) i)
    choose u spoke left right neighbors using third cubic f along
    obtain ⟨off,inj,opp,onlyOne⟩ := frame s color c4 c8 f along u spoke left right
    let D := (Set.range f)ᶜ
    let W := ↥D
    let H := G.induce D
    let t : Fin 6 ↪ W := ⟨fun i => ⟨u i,fun ⟨j,e⟩ => off i j e.symm⟩,
      fun i j e => inj (congrArg Subtype.val e)⟩
    let sw (w : W) := s w.val
    have scol {a b : W} (e : H.Adj a b) : sw a ≠ sw b := color e
    have adjCore (x : W) (i : Fin 6) : G.Adj x.val (f i) ↔ x=t i := by
      constructor
      · intro e
        rcases (neighbors i x.val).mp e.symm with e|e|e
        · exact (x.property ⟨i-1,e.symm⟩).elim
        · exact (x.property ⟨i+1,e.symm⟩).elim
        · exact Subtype.ext e
      · rintro rfl; exact (spoke i).symm
    have deg (x : W) : (H.neighborSet x).ncard + (if x ∈ Set.range t then 1 else 0) = 3 := by
      have imageEq : Subtype.val '' H.neighborSet x = G.neighborSet x.val \ Set.range f := by
        ext y
        exact ⟨fun ⟨w,hw,e⟩ => e ▸ ⟨hw,w.property⟩,
          fun ⟨adj,mem⟩ => ⟨⟨y,mem⟩,adj,rfl⟩⟩
      have cnt := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet x.val) (Set.range f)
      rw [←imageEq,Set.ncard_image_of_injective _ Subtype.val_injective,cubic] at cnt
      by_cases p : x ∈ Set.range t
      · obtain ⟨i,rfl⟩ := p
        have cap : G.neighborSet (t i).val ∩ Set.range f = {f i} := by
          ext y
          constructor
          · rintro ⟨h,⟨j,rfl⟩⟩
            have e := t.injective ((adjCore (t i) j).mp h)
            simp [e]
          · rintro rfl
            exact ⟨(spoke i).symm,⟨i,rfl⟩⟩
        rw [cap,Set.ncard_singleton] at cnt
        rw [if_pos ⟨i,rfl⟩]; omega
      · have cap : G.neighborSet x.val ∩ Set.range f = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro y ⟨h,⟨j,rfl⟩⟩
          exact p ⟨j,((adjCore x j).mp h).symm⟩
        simpa [cap,p] using cnt
    have alt (i : Fin 6) : sw (t i) ≠ sw (t (i+1)) := by
      have a := color (spoke i)
      have b := color (spoke (i+1))
      have c := color (along i)
      exact (by decide : ∀ a b c d : Bool, a≠b → c≠d → a≠c → b≠d) _ _ _ _ a b c
    have smaller : Fintype.card W<n := by
      rw [←size]
      exact Fintype.card_subtype_lt (x:=f 0) (fun h => h ⟨0,rfl⟩)
    have : Nonempty W := ⟨t 0⟩
    by_cases inner : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ H
    · obtain ⟨k,hk,⟨c⟩⟩ := inner
      exact ⟨k,hk,⟨(Copy.induce G D).comp c⟩⟩
    have noInner (k : ℕ) (hk : 2 ≤ k) (c : cycleGraph (2^k) ⊑ H) : False := inner ⟨k,hk,c⟩
    by_contra denied
    have none (k : ℕ) (hk : 2 ≤ k) (w : cycleGraph (2^k) ⊑ G) : False := denied ⟨k,hk,w⟩
    have exclude (i j : Fin 6) (_ : i ≠ j) (P : H.Walk (t j) (t i)) (A : (cycleGraph 6).Walk i j)
        (hP : P.IsPath) (hA : A.IsPath) (k : ℕ) (hk : 2 ≤ k) (len : P.length+A.length+2=2^k) : False := by
      have size : 2^2 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
      exact none k hk (twoSpokes hex (Copy.induce G D) t (fun l w eq => w.property ⟨l,eq⟩) spoke
        P A hP hA (by omega) len)
    have filled := fun σ inv diff fresh => completePorts (W:=W) sw (H:=H) scol t (by
      intro x; have z := deg x; by_cases e : x ∈ Set.range t <;> simpa [e] using z) σ inv diff fresh
    obtain ⟨k,hk,S,a,b,external,internal,cross⟩ := h2 W H sw t scol (by
      intro x; have z := deg x; by_cases e : x ∈ Set.range t <;> simpa [e] using z) alt opp onlyOne noInner exclude (by
      intro σ inv diff fresh
      obtain ⟨c,d⟩ := filled σ inv diff fresh
      exact ih _ smaller W rfl _ sw c d)
    let v (i : Fin (2^k)) : V := if h : i ∈ S then f (b ⟨i,h⟩) else (a ⟨i,h⟩).val
    have inside (i) (h : i ∈ S) : v i=f (b ⟨i,h⟩) := dif_pos h
    have outside (i) (h : i ∉ S) : v i=(a ⟨i,h⟩).val := dif_neg h
    have vi : Function.Injective v := by
      intro i j e
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> (first | rw [inside i hi] at e | rw [outside i hi] at e) <;>
        (first | rw [inside j hj] at e | rw [outside j hj] at e)
      · exact congrArg Subtype.val (b.injective (f.injective e))
      · exact ((a ⟨j,hj⟩).property ⟨_,e⟩).elim
      · exact ((a ⟨i,hi⟩).property ⟨_,e.symm⟩).elim
      · exact congrArg Subtype.val (a.injective (Subtype.ext e))
    let g : cycleGraph (2^k) →g G := ⟨v,by
      intro i j e
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> (first | rw [inside i hi] | rw [outside i hi]) <;>
        (first | rw [inside j hj] | rw [outside j hj])
      · exact hex.toHom.map_rel' (internal ⟨i,hi⟩ ⟨j,hj⟩ e)
      · rw [cross ⟨i,hi⟩ ⟨j,hj⟩ e]; exact spoke _
      · rw [cross ⟨j,hj⟩ ⟨i,hi⟩ e.symm]; exact (spoke _).symm
      · exact external ⟨i,hi⟩ ⟨j,hj⟩ e⟩
    exact none k hk ⟨g.toCopy vi⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.H2 := by
  classical
  intro h1 h2 X _ _ p q sep _
  let G := fromRel (fun a b : Bool × X => a.1=false ∧ b.1=true ∧
    (b.2=a.2 ∨ b.2=p a.2 ∨ b.2=q a.2))
  apply byOrder h1 h2 _ (Bool × X) rfl G Prod.fst
  · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨_,h|h⟩ <;> simp_all
  · rintro ⟨b,x⟩
    cases b
    · have N : G.neighborSet (false,x)={(true,x),(true,p x),(true,q x)} := by
        ext ⟨b,y⟩
        cases b <;> simp [G,SimpleGraph.fromRel,Prod.ext_iff]
      have ⟨a,b,c⟩ := sep x
      simp [N,Set.ncard_insert_of_notMem,c,Ne.symm a,Ne.symm b]
    · have N : G.neighborSet (true,x)={(false,x),(false,p.symm x),(false,q.symm x)} := by
        ext ⟨b,y⟩
        cases b <;> simp [G,SimpleGraph.fromRel,Prod.ext_iff,Equiv.eq_symm_apply] <;> grind
      have a : p.symm x≠x := fun h => (sep x).1 (by simpa only [h] using p.apply_symm_apply x)
      have b : q.symm x≠x := fun h => (sep x).2.1 (by simpa only [h] using q.apply_symm_apply x)
      have c : p.symm x≠q.symm x := by
        intro e
        exact (sep (p.symm x)).2.2 ((p.apply_symm_apply x).trans (by rw [e,q.apply_symm_apply]))
      simp [N,Set.ncard_insert_of_notMem,c,Ne.symm a,Ne.symm b]

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R3
