import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1
import Mathlib

/-!
# Three regular matchings with abelian commutator subgroup

In a bipartite matching graph over a group, left multiplication by each of
three shifts acts between fibers of its abelianization. Coset representatives
give one voltage for each oriented quotient edge, even for a nonsplit
extension. Distinct quotient shifts give the abelian voltage problem below.
When two quotient shifts agree, two consecutive fibers give a short cycle
unless the parallel voltage differences agree up to sign. Orienting these
differences consistently then gives commuting relative permutations.
This proves the coincident-offset bound even for groups of even order.

@JamesSlash's PR #592 gives the cubic branch of Erdős–Gyárfás. PR #5246
provides the three-matching presentation and the local commutation lemma
used below. PR #5820 separates regular translations and actions with
stabilizers. PR #7828 proves the odd-order abelian-normal index-eleven
case and gives the regular odd target of this reduction. Its rectangle
argument also yields an 8- or 16-cycle for noncommuting generators with a
repeated quotient shift in odd order.

Christine Kelley and Judy Walker, “LDPC codes from voltage graphs”, §IV
(doi:10.1109/ISIT.2008.4595095), describe abelian-forcing walks.
Friedman, Izsak and Silberman, “Abelian girth and girth”, §2.2
(arXiv:1511.03678), give the edge-neutral theta and barbell walks. The first
hypothesis asks for vertex-simple cycles at the specified lengths.
Codex, gpt-6.2-astra.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1
open SimpleGraph

/-- Three distinct offsets generating a finite abelian base, with an independent
voltage at each base point and matching label. -/
def H1 : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Finite B] (a b : B),
    a ≠ 0 → b ≠ 0 → a ≠ b → AddSubgroup.closure ({a,b} : Set B) = ⊤ →
    ∀ (V : Type) [AddCommGroup V] (w : B → Fin 3 → V),
    let G := SimpleGraph.fromRel fun l r : Bool × B × V =>
      ∃ (i : B) (k : Fin 3) (g : V),
        l = (false,i,g) ∧ r = (true,i + (![0,a,b] : Fin 3 → B) k,g + w i k)
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G

/-- The regular odd-order residual with two noncommuting elements in the
commutator subgroup. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ → a ≠ 1 → b ≠ 1 → a ≠ b → Odd (Nat.card A) →
    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∃ x y : commutator A, x * y ≠ y * x) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

section RegularCoordinates

private theorem ladder_walk {V T X : Type*} [AddCommGroup V] (a b : V)
    (G : SimpleGraph X) (ι : (Bool × Bool × V) ↪ X)
    (id : ∀ r g,G.Adj (ι (false,r,g)) (ι (true,r,g)))
    (rung : ∀ g,G.Adj (ι (false,false,g)) (ι (true,true,g)))
    (top : ∀ g,G.Adj (ι (false,false,g)) (ι (true,false,g+a)))
    (bottom : ∀ g,G.Adj (ι (false,true,g)) (ι (true,true,g+b)))
    (v : T → V) (inj : Function.Injective v) (L U : T → T → Prop)
    (low : ∀ i j,L i j → v j=v i+a) (high : ∀ i j,U i j → v j=v i+b)
    {n : ℕ} (p : Fin n → Bool × Bool × T) (distinct : Function.Injective p) :
    let forward (z w : Bool × Bool × T) : Prop :=
      z.1=false ∧ w.1=true ∧ (z.2=w.2 ∨ (z.2.1=false ∧ w.2.1=true ∧ z.2.2=w.2.2) ∨
        (z.2.1=false ∧ w.2.1=false ∧ L z.2.2 w.2.2) ∨ (z.2.1=true ∧ w.2.1=true ∧ U z.2.2 w.2.2))
    (∀ i j,(cycleGraph n).Adj i j → forward (p i) (p j) ∨ forward (p j) (p i)) →
    cycleGraph n ⊑ G := by
  intro forward edges
  let f := ((Function.Embedding.refl Bool).prodMap ((Function.Embedding.refl Bool).prodMap ⟨v,inj⟩)).trans ι
  have oriented (z w : Bool × Bool × T) (e : forward z w) : G.Adj (f z) (f w) := by
    obtain ⟨s,r,i⟩ := z
    obtain ⟨t,q,j⟩ := w
    obtain ⟨rfl,rfl,eq|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,hl⟩|⟨rfl,rfl,hu⟩⟩ := e
    · change (r,i)=(q,j) at eq
      cases eq
      exact id _ _
    · exact rung _
    · change G.Adj (ι (false,false,v i)) (ι (true,false,v j))
      rw [low _ _ hl]; exact top _
    · change G.Adj (ι (false,true,v i)) (ι (true,true,v j))
      rw [high _ _ hu]; exact bottom _
  exact ⟨⟨⟨fun i => f (p i),fun {i j} h => (edges i j h).elim (oriented _ _) (fun e => (oriented _ _ e).symm)⟩,
    f.injective.comp distinct⟩⟩

private theorem ladder {V X : Type*} [AddCommGroup V] (a b : V) (a0 : a ≠ 0) (b0 : b ≠ 0)
    (G : SimpleGraph X) (ι : (Bool × Bool × V) ↪ X)
    (id : ∀ r g,G.Adj (ι (false,r,g)) (ι (true,r,g)))
    (rung : ∀ g,G.Adj (ι (false,false,g)) (ι (true,true,g)))
    (top : ∀ g,G.Adj (ι (false,false,g)) (ι (true,false,g+a)))
    (bottom : ∀ g,G.Adj (ι (false,true,g)) (ι (true,true,g+b)))
    (distinct : a≠b ∧ a≠ -b) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  by_cases b2 : b+b=0
  · left
    let v : Bool → V := fun i => if i then b else 0
    have vi : Function.Injective v := by
      intro i j eq; cases i <;> cases j <;> simp_all [v]
    let p : Fin 4 → Bool × Bool × Bool := ![(false,true,false),(true,true,false),(false,true,true),(true,true,true)]
    have high (i j : Bool) (e : i≠j) : v j=v i+b := by cases i <;> cases j <;> simp_all [v]
    apply ladder_walk a b G ι id rung top bottom v vi (fun _ _ => False) (fun i j => i≠j)
      (fun _ _ e => e.elim) high p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]; decide
    · dsimp only [p]; decide
  let t : Fin 3 → V := ![0,b,b+b]
  have ti : Function.Injective t := by
    have notEqual : b+b≠b := by simpa using b0
    intro i j eq
    fin_cases i <;> fin_cases j <;> first | rfl | exact (b0 eq).elim | exact (b0 eq.symm).elim | exact (b2 eq).elim | exact (b2 eq.symm).elim | exact (notEqual eq).elim | exact (notEqual eq.symm).elim
  let adj (i j : Fin 3) := (i=0 ∧ j=1) ∨ (i=1 ∧ j=2)
  have up (i j : Fin 3) (e : adj i j) : t j=t i+b := by
    rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (zero_add b).symm
    · rfl
  by_cases plus : a=b+b
  · right; left
    let L (i j : Fin 3) := i=0 ∧ j=2
    have low (i j : Fin 3) (e : L i j) : t j=t i+a := by
      obtain ⟨rfl,rfl⟩ := e; change b+b=0+a; simp [plus]
    let p : Fin 8 → Bool × Bool × Fin 3 := ![(false,false,0),(true,false,2),(false,false,2),(true,true,2),
      (false,true,1),(true,true,1),(false,true,0),(true,true,0)]
    apply ladder_walk a b G ι id rung top bottom t ti L adj low up p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]; decide
    · dsimp only [p,L,adj]; decide
  by_cases minus : a= -(b+b)
  · right; left
    let L (i j : Fin 3) := i=2 ∧ j=0
    have low (i j : Fin 3) (e : L i j) : t j=t i+a := by
      obtain ⟨rfl,rfl⟩ := e; change 0=b+b+a; simp [minus]
    let p : Fin 8 → Bool × Bool × Fin 3 := ![(false,false,2),(true,false,0),(false,false,0),(true,true,0),
      (false,true,0),(true,true,1),(false,true,1),(true,true,2)]
    apply ladder_walk a b G ι id rung top bottom t ti L adj low up p
    · change ∀ i j,p i=p j → i=j
      dsimp only [p]; decide
    · dsimp only [p,L,adj]; decide
  right;right
  have dj (i j : Fin 3) : t i ≠ a+t j := by
    intro eq
    fin_cases i <;> fin_cases j <;> dsimp [t] at eq
    all_goals first
      | solve | apply a0; linear_combination (norm := abel) -eq
      | solve | apply distinct.1; linear_combination (norm := abel) -eq
      | solve | apply distinct.2; linear_combination (norm := abel) -eq
      | solve | apply plus; linear_combination (norm := abel) -eq
      | solve | apply minus; linear_combination (norm := abel) -eq
  let v (z : Bool × Fin 3) := if z.1 then a+t z.2 else t z.2
  have vi : Function.Injective v := by
    rintro ⟨r,i⟩ ⟨s,j⟩ eq
    cases r <;> cases s
    · exact Prod.ext rfl (ti eq)
    · exact (dj _ _ eq).elim
    · exact (dj _ _ eq.symm).elim
    · exact Prod.ext rfl (ti (add_left_cancel eq))
  let L (z w : Bool × Fin 3) := z.1=false ∧ w.1=true ∧ z.2=w.2
  let U (z w : Bool × Fin 3) := z.1=w.1 ∧ adj z.2 w.2
  have low (i j : Bool × Fin 3) (e : L i j) : v j=v i+a := by
    obtain ⟨r,k⟩ := i; obtain ⟨s,l⟩ := j
    obtain ⟨rfl,rfl,rfl⟩ := e; exact add_comm _ _
  have high (i j : Bool × Fin 3) (e : U i j) : v j=v i+b := by
    obtain ⟨r,k⟩ := i; obtain ⟨s,l⟩ := j
    obtain ⟨rfl,h⟩ := e; cases r <;> simp [v,up k l h,add_assoc]
  let p : Fin 16 → Bool × Bool × Bool × Fin 3 := ![
    (false,false,false,0),(true,false,true,0),(false,false,true,0),(true,true,true,0),
    (false,true,true,0),(true,true,true,1),(false,true,true,1),(true,true,true,2),
    (false,false,true,2),(true,false,true,2),(false,false,false,2),(true,true,false,2),
    (false,true,false,1),(true,true,false,1),(false,true,false,0),(true,true,false,0)]
  apply ladder_walk a b G ι id rung top bottom v vi L U low high p
  · change ∀ i j,p i=p j → i=j
    dsimp only [p]; decide
  · dsimp only [p,L,U,adj]; decide


/-- Choose one orientation of every unordered pair {v,-v}. -/
private theorem orientation {V : Type*} [AddCommGroup V] :
    ∃ o : V → V, (∀ v,v=o v ∨ v= -o v) ∧ ∀ v,o (-v)=o v := by
  classical
  let pick (S : Set V) := if h : S.Nonempty then h.choose else 0
  have mem (v : V) : pick {v,-v} ∈ ({v,-v} : Set V) := by
    have h : ({v,-v} : Set V).Nonempty := ⟨v, by simp⟩
    simpa only [pick,dif_pos h] using h.choose_spec
  refine ⟨fun v => pick {v,-v},?_,?_⟩
  · intro v
    have h := mem v
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with h|h
    · exact Or.inl h.symm
    · exact Or.inr (by change v = -(pick {v,-v}); rw [h,neg_neg])
  · intro v
    apply congrArg pick
    ext z
    simp [or_comm]

/-- Two parallel quotient matchings and one fixed-point-free permutation of the
layers force a short cycle. No finiteness or transitivity is required. -/
theorem parallel_cover {I V X : Type*} [AddCommGroup V] (root : I)
    (σ : Equiv.Perm I) (free : ∀ i,σ i≠i) (w : I → Fin 3 → V)
    (sep : ∀ i,w i 0≠w i 1) (G : SimpleGraph X) (ι : (Bool × I × V) ↪ X)
    (edge : ∀ (i : I) (k : Fin 3) (g : V),
      G.Adj (ι (false,i,g)) (ι (true,(![i,i,σ i] : Fin 3 → I) k,g+w i k))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let x (i : I) := w i 1-w i 0
  have nz (i : I) : x i ≠ 0 := sub_ne_zero.mpr (sep i).symm
  by_cases pair : ∃ i,x i ≠ x (σ i) ∧ x i ≠ -x (σ i)
  · obtain ⟨i,different⟩ := pair
    let row (r : Bool) : I := if r then σ i else i
    have ri : Function.Injective row := by
      intro s t eq
      cases s <;> cases t <;> first | rfl | exact (free i eq).elim | exact (free i eq.symm).elim
    let c := w i 2-w (σ i) 0
    let e : (Bool × Bool × V) ↪ X := {
      toFun z := ι (z.1,row z.2.1,z.2.2+(if z.2.1 then c else 0)+(if z.1 then w (row z.2.1) 0 else 0))
      inj' := by
        rintro ⟨s,r,u⟩ ⟨t,j,v⟩ eq
        have h := ι.injective eq
        have side : s=t := congrArg Prod.fst h
        have layer : row r=row j := congrArg (fun z : Bool × I × V => z.2.1) h
        have rj := ri layer
        subst t; subst j
        have hv := congrArg (fun z : Bool × I × V => z.2.2) h
        exact Prod.ext rfl (Prod.ext rfl (add_right_cancel (add_right_cancel hv))) }
    apply ladder (x i) (x (σ i)) (nz _) (nz _) G e _ _ _ _ different
    · intro r g
      cases r
      · simpa [e,row] using edge i 0 g
      · simpa [e,row] using edge (σ i) 0 (g+c)
    · intro g
      simpa [e,row,c,sub_eq_add_neg,add_assoc] using edge i 2 g
    · intro g
      simpa [e,row,x,sub_eq_add_neg,add_assoc] using edge i 1 g
    · intro g
      simpa [e,row,x,sub_eq_add_neg,add_assoc,add_left_comm,add_comm] using edge (σ i) 1 (g+c)
  obtain ⟨orient,orient_cases,orient_neg⟩ := orientation (V:=V)
  let a (i : I) := orient (x i)
  have sign (i : I) : x i=a i ∨ x i= -(a i) := orient_cases _
  have nonzero (i : I) : a i≠0 := by
    intro eq
    rcases sign i with h|h <;> exact nz i (by simpa [eq] using h)
  have invariant (i : I) : a (σ i)=a i := by
    change orient (x (σ i))=orient (x i)
    by_cases h : x i=x (σ i)
    · rw [h]
    · have e : x i= -x (σ i) := by
        by_contra ne
        exact pair ⟨i,h,ne⟩
      rw [e,orient_neg]
  let r (i : I) := if x i=a i then w i 0 else w i 1
  let j : (Bool × I × V) ↪ X := {
    toFun z := ι (z.1,z.2.1,z.2.2+(if z.1 then r z.2.1 else 0))
    inj' := by
      rintro ⟨s,i,u⟩ ⟨t,k,v⟩ eq
      have z := ι.injective eq
      have side : s=t := congrArg Prod.fst z
      have row : i=k := congrArg (fun q : Bool × I × V => q.2.1) z
      subst t; subst k
      exact Prod.ext rfl (Prod.ext rfl (add_right_cancel (congrArg (fun q : Bool × I × V => q.2.2) z))) }
  let p : Equiv.Perm (I × V) := {
    toFun z := (z.1,z.2+a z.1)
    invFun z := (z.1,z.2-a z.1)
    left_inv z := by simp
    right_inv z := by simp }
  let t (i : I) := w i 2-r (σ i)
  let q : Equiv.Perm (I × V) := {
    toFun z := (σ z.1,z.2+t z.1)
    invFun z := (σ.symm z.1,z.2-t (σ.symm z.1))
    left_inv z := by simp
    right_inv z := by simp }
  have separated (z : I × V) : p z≠z ∧ q z≠z ∧ p z≠q z := by
    refine ⟨?_,fun h => free _ (congrArg Prod.fst h),fun h => free _ (congrArg Prod.fst h).symm⟩
    intro h
    have e : z.2+a z.1=z.2 := congrArg Prod.snd h
    exact nonzero z.1 (by simpa using e)
  have idE (z : I × V) : (G.comap j).Adj (false,z) (true,z) := by
    obtain ⟨i,g⟩ := z
    by_cases h : x i=a i
    · simpa [j,r,h] using edge i 0 g
    · simpa [j,r,h] using edge i 1 g
  have pE (z : I × V) : (G.comap j).Adj (false,z) (true,p z) := by
    obtain ⟨i,g⟩ := z
    change G.Adj (ι (false,i,g+0)) (ι (true,i,g+a i+r i))
    by_cases h : x i=a i
    · have eq : g+a i+r i=g+w i 1 := by
        rw [show r i=w i 0 by simp [r,h],←h]
        simp [x,sub_eq_add_neg,add_assoc]
      simpa [eq] using edge i 1 g
    · have e := (sign i).resolve_left h
      have eq : g+a i+r i=g+w i 0 := by
        rw [show r i=w i 1 by simp [r,h]]
        change w i 1 - w i 0= -(a i) at e
        linear_combination (norm := abel) e
      simpa [eq] using edge i 0 g
  have qE (z : I × V) : (G.comap j).Adj (false,z) (true,q z) := by
    obtain ⟨i,g⟩ := z
    change G.Adj (ι (false,i,g+0)) (ι (true,σ i,g+t i+r (σ i)))
    simpa [t,sub_eq_add_neg,add_assoc] using edge i 2 g
  have comm (z : I × V) : p (q z)=q (p z) := by
    exact Prod.ext rfl (show z.2+t z.1+a (σ z.1)=z.2+a z.1+t z.1 by rw [invariant]; abel)
  have hit := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0
    (G.comap j) p q separated idE pE qE (root,0) (comm _) (comm _) (comm _) (comm _)
  have down : G.comap j ⊑ G := ⟨(SimpleGraph.Embedding.comap j G).toCopy⟩
  rcases hit with h|h|h
  · exact .inl (h.trans down)
  · exact .inr (.inl (h.trans down))
  · exact .inr (.inr (h.trans down))

open scoped IsMulCommutative

/-- With left coset representatives on both shores, each matching translates
the kernel coordinate by a fixed element for each oriented base edge. -/
private theorem regular_coordinates {A : Type} {Q I : Type*} [Group A] [Group Q]
    (f : A →* Q) (comm : ∀ g h : f.ker, g*h=h*g)
    (r : Bool → I → A) (separate : ∀ s, Function.Injective (fun i => f (r s i)))
    (shifts : Fin 3 → A) (δ : I → Fin 3 → I)
    (align : ∀ i k, f (shifts k*r false i)=f (r true (δ i k)))
    (G : SimpleGraph (Bool × A)) (edges : ∀ k y, G.Adj (false,y) (true,shifts k*y)) :
    ∃ (V : Type) (_ : AddCommGroup V) (w : I → Fin 3 → V) (e : (Bool × I × V) ↪ Bool × A),
      (∀ i k g, G.Adj (e (false,i,g)) (e (true,δ i k,g+w i k))) ∧
      (∀ i k l, δ i k=δ i l → shifts k≠shifts l → w i k≠w i l) := by
  have : IsMulCommutative f.ker := IsMulCommutative.of_comm comm
  let h (i : I) (k : Fin 3) : f.ker := ⟨(r true (δ i k))⁻¹*(shifts k*r false i),by
    change f _ = 1
    rw [map_mul,map_inv,align,inv_mul_cancel]⟩
  let w (i : I) (k : Fin 3) := Additive.ofMul (h i k)
  let e : (Bool × I × Additive f.ker) ↪ Bool × A := {
    toFun z := (z.1,r z.1 z.2.1*(z.2.2.toMul : A))
    inj' := by
      rintro ⟨s,i,g⟩ ⟨t,j,g'⟩ eq
      obtain rfl : s=t := congrArg Prod.fst eq
      have z : r s i*(g.toMul : A)=r s j*(g'.toMul : A) := congrArg Prod.snd eq
      obtain rfl : i=j := separate s (by
        simpa only [map_mul,show f (g.toMul : A)=1 from g.toMul.property,
          show f (g'.toMul : A)=1 from g'.toMul.property,mul_one] using congrArg f z)
      exact Prod.ext rfl (Prod.ext rfl (Additive.toMul.injective (Subtype.ext (mul_left_cancel z)))) }
  refine ⟨Additive f.ker,inferInstance,w,e,?_,?_⟩
  · intro i k g
    change G.Adj (false,r false i*(g.toMul : A))
      (true,r true (δ i k)*((g.toMul*h i k : f.ker) : A))
    rw [comm g.toMul (h i k),Subgroup.coe_mul]
    simpa [h,mul_assoc] using edges k (r false i*(g.toMul : A))
  · intro i k l same ne eq
    have z := congrArg (fun v : Additive f.ker => (v.toMul : A)) eq
    change (r true (δ i k))⁻¹*(shifts k*r false i) =
      (r true (δ i l))⁻¹*(shifts l*r false i) at z
    rw [same] at z
    exact ne (mul_right_cancel (mul_left_cancel z))

/-- Normalize the two equal quotient labels to the stationary parallel pair. -/
private theorem ordered_regular {A Q : Type} [Group A] [Group Q]
    (f : A →* Q) (onto : Function.Surjective f) (comm : ∀ g h : f.ker, g*h=h*g)
    (s t u : A) (same : f s=f t) (diff : f u≠f s) (sep : s≠t)
    (G : SimpleGraph (Bool × A)) (hs : ∀ y,G.Adj (false,y) (true,s*y))
    (ht : ∀ y,G.Adj (false,y) (true,t*y)) (hu : ∀ y,G.Adj (false,y) (true,u*y)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let σ : Equiv.Perm Q := Equiv.mulLeft ((f s)⁻¹*f u)
  have free (i : Q) : σ i≠i := by
    intro eq
    change ((f s)⁻¹*f u)*i=i at eq
    have z : ((f s)⁻¹*f u)*i=1*i := eq.trans (one_mul i).symm
    exact diff (inv_mul_eq_one.mp (mul_right_cancel z)).symm
  choose lift hl using onto
  let r (side : Bool) (i : Q) := lift ((if side then f s else 1)*i)
  have sepQ (side : Bool) : Function.Injective (fun i => f (r side i)) := by
    intro i j eq
    simp only [r,hl] at eq
    exact mul_left_cancel eq
  let S : Fin 3 → A := ![s,t,u]
  let δ (i : Q) : Fin 3 → Q := ![i,i,σ i]
  have align (i : Q) (k : Fin 3) : f (S k*r false i)=f (r true (δ i k)) := by
    fin_cases k <;> simp [δ,S,r,σ,hl,←same]
  have edges (k : Fin 3) (y : A) : G.Adj (false,y) (true,S k*y) := by
    fin_cases k <;> first | exact hs y | exact ht y | exact hu y
  obtain ⟨V,inst,w,e,adj,apart⟩ := regular_coordinates f comm r sepQ S δ align G edges
  exact parallel_cover 1 σ free w (fun i => apart i 0 1 rfl sep) G e adj

/-- Coincident quotient offsets force a cycle of length at most sixteen
in every regular three-matching graph with abelian kernel. -/
theorem coincident_regular {A Q : Type} [Group A] [Group Q]
    (f : A →* Q) (onto : Function.Surjective f) (comm : ∀ g h : f.ker, g*h=h*g)
    (a b : A) (a1 : a≠1) (b1 : b≠1) (ab : a≠b) (same : f a=1 ∨ f b=1 ∨ f a=f b)
    (G : SimpleGraph (Bool × A)) (e0 : ∀ x,G.Adj (false,x) (true,x))
    (ea : ∀ x,G.Adj (false,x) (true,a*x)) (eb : ∀ x,G.Adj (false,x) (true,b*x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have one (y : A) : G.Adj (false,y) (true,1*y) := by simpa using e0 y
  by_cases ha : f a=1
  · by_cases hb : f b=1
    · have cm : a*b=b*a := congrArg Subtype.val (comm ⟨a,ha⟩ ⟨b,hb⟩)
      let p := Equiv.mulLeft a
      let q := Equiv.mulLeft b
      have sep (x : A) : p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x := by
        simpa [p,q] using And.intro a1 (And.intro b1 ab)
      have commute (x : A) : p (q x)=q (p x) := by
        change a*(b*x)=b*(a*x)
        rw [←mul_assoc,cm,mul_assoc]
      exact OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0 G p q sep
        e0 ea eb 1 (commute _) (commute _) (commute _) (commute _)
    · exact ordered_regular f onto comm 1 a b (by simpa using ha.symm)
        (by simpa using hb) a1.symm G one ea eb
  · by_cases hb : f b=1
    · exact ordered_regular f onto comm 1 b a (by simpa using hb.symm)
        (by simpa using ha) b1.symm G one eb ea
    · exact ordered_regular f onto comm a b 1 ((same.resolve_left ha).resolve_left hb)
        (by simpa using Ne.symm ha) ab G ea eb one

/-- An abelian kernel and a finite abelian quotient suffice. The input voltage
theorem applies on the subgroup generated by the two quotient shifts. -/
theorem regular_abelian_quotient (voltage : H1) {A Q : Type} [Group A] [CommGroup Q] [Finite Q]
    (f : A →* Q) (onto : Function.Surjective f) (comm : ∀ g h : f.ker, g*h=h*g)
    (a b : A) (a1 : a≠1) (b1 : b≠1) (ab : a≠b)
    (G : SimpleGraph (Bool × A)) (e0 : ∀ x,G.Adj (false,x) (true,x))
    (ea : ∀ x,G.Adj (false,x) (true,a*x)) (eb : ∀ x,G.Adj (false,x) (true,b*x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  by_cases same : f a=1 ∨ f b=1 ∨ f a=f b
  · rcases coincident_regular f onto comm a b a1 b1 ab same G e0 ea eb with h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  let U := AddSubgroup.closure ({Additive.ofMul (f a),Additive.ofMul (f b)} : Set (Additive Q))
  let α : U := ⟨Additive.ofMul (f a),AddSubgroup.subset_closure (by simp)⟩
  let β : U := ⟨Additive.ofMul (f b),AddSubgroup.subset_closure (by simp)⟩
  have gen : AddSubgroup.closure ({α,β} : Set U)=⊤ := by
    apply top_unique
    rintro ⟨z,hz⟩ _
    obtain ⟨m,n,he⟩ := AddSubgroup.mem_closure_pair.mp hz
    exact AddSubgroup.mem_closure_pair.mpr ⟨m,n,Subtype.ext he⟩
  let δ : Fin 3 → U := ![0,α,β]
  let shifts : Fin 3 → A := ![1,a,b]
  choose lift image using onto
  let r (_ : Bool) (i : U) := lift i.val.toMul
  have separate (s : Bool) : Function.Injective (fun i => f (r s i)) := by
    intro i j he
    apply Subtype.ext
    exact Additive.toMul.injective (by simpa only [r,image] using he)
  have align (i : U) (k : Fin 3) : f (shifts k*r false i)=f (r true (i+δ k)) := by
    rw [map_mul]
    simp only [r,image]
    fin_cases k <;> simp [shifts,δ,α,β,mul_comm]
  have edges (k : Fin 3) (y : A) : G.Adj (false,y) (true,shifts k*y) := by
    fin_cases k
    · simpa [shifts] using e0 y
    · exact ea y
    · exact eb y
  obtain ⟨V,inst,w,e,adj,_⟩ := regular_coordinates f comm r separate shifts
    (fun i k => i+δ k) align G edges
  have az : α≠0 := fun h => same (.inl (congrArg (fun t : U => t.val.toMul) h))
  have bz : β≠0 := fun h => same (.inr (.inl (congrArg (fun t : U => t.val.toMul) h)))
  have nz : α≠β := fun h => same (.inr (.inr (congrArg (fun t : U => t.val.toMul) h)))
  let D := SimpleGraph.fromRel fun l r : Bool × U × V =>
    ∃ (i : U) (k : Fin 3) (g : V), l=(false,i,g) ∧ r=(true,i+δ k,g+w i k)
  have inside : D ⊑ G := by
    refine ⟨⟨⟨e,?_⟩,e.injective⟩⟩
    intro l r h
    rcases h.2 with ⟨i,k,g,rfl,rfl⟩|⟨i,k,g,rfl,rfl⟩
    · exact adj _ _ _
    · exact (adj _ _ _).symm
  have short : cycleGraph 4 ⊑ D ∨ cycleGraph 8 ⊑ D ∨ cycleGraph 16 ⊑ D ∨ cycleGraph 32 ⊑ D :=
    voltage U α β az bz nz gen V w
  exact short.imp (·.trans inside) (fun t => t.imp (·.trans inside)
    (fun t => t.imp (·.trans inside) (·.trans inside)))

end RegularCoordinates

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1.H2 := by
  intro voltage residual A _ _ a b gen a1 b1 ab odd absent
  by_cases noncomm : ∃ x y : commutator A, x*y≠y*x
  · exact residual A a b gen a1 b1 ab odd absent noncomm
  let f : A →* Abelianization A := Abelianization.of
  have onto : Function.Surjective f := QuotientGroup.mk'_surjective _
  have : Finite (Abelianization A) := Finite.of_surjective f onto
  have comm : ∀ g h : f.ker, g*h=h*g := by
    change ∀ g h : (@Abelianization.of A _).ker, g*h=h*g
    rw [Abelianization.ker_of]
    intro g h
    exact Classical.byContradiction (fun ne => noncomm ⟨g,h,ne⟩)
  let G := SimpleGraph.fromRel (fun u v : Bool × A =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))
  rcases regular_abelian_quotient voltage f onto comm a b a1 b1 ab G
    (fun x => ⟨by simp, .inl ⟨rfl,rfl,.inl rfl⟩⟩)
    (fun x => ⟨by simp, .inl ⟨rfl,rfl,.inr (.inl rfl)⟩⟩)
    (fun x => ⟨by simp, .inl ⟨rfl,rfl,.inr (.inr rfl)⟩⟩) with h|h|h|h
  · exact ⟨2,by decide,h⟩
  · exact ⟨3,by decide,h⟩
  · exact ⟨4,by decide,h⟩
  · exact ⟨5,by decide,h⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1
