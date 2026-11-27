import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2
import Mathlib

/-!
# The involution quotient case of the even matching step

A finite orbit with abelian kernel covering three successive square cells has
a simple 4- or 16-cycle. The cuts between cells each consist of two edges.
This extends the matching reductions of JamesSlash (PR 592), PR 5246 and the
normal two-subgroup descent in PR 6375. The orbit coordinates generalize the
index-eleven construction in PR 8157.
-/

/- Any abelian lift of three square cells arranged in a chain contains a simple
4- or 16-cycle. Number the four sites of cell i in the order left, left, right,
right. The interface joins like-numbered left and right sites in consecutive cells.
The balanced theta traversal is classical; see Friedman, Izsak and Silberman,
Abelian Girth and Girth, 2015, section 2.2. -/
namespace NecklaceReduction
open SimpleGraph

set_option maxHeartbeats 4000000 in
theorem necklace_voltage_cycle {A X : Type*} [AddCommGroup A] (G : SimpleGraph X)
    (raw : (Fin 12 × A) ↪ X) (weights : Fin 3 → Fin 2 → Fin 2 → A)
    (links : Fin 2 → Fin 2 → A)
    (rawCell : ∀ (i : Fin 3) (x y : Fin 2) (z : A),
      G.Adj (raw ((⟨4*i.val+x.val,by omega⟩ : Fin 12),z))
        (raw ((⟨4*i.val+2+y.val,by omega⟩ : Fin 12),z+weights i x y)))
    (rawLink : ∀ (i : Fin 2) (x : Fin 2) (z : A),
      G.Adj (raw ((⟨4*i.castSucc.val+x.val,by omega⟩ : Fin 12),z))
        (raw ((⟨4*i.succ.val+2+x.val,by omega⟩ : Fin 12),z+links i x))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let L (i : Fin 3) (x : Fin 2) : Fin 12 := ⟨4*i.val+x.val, by omega⟩
  let R (i : Fin 3) (y : Fin 2) : Fin 12 := ⟨4*i.val+2+y.val, by omega⟩

  let Norm (e : (Fin 12 × A) ↪ X) (a : Fin 3 → A) (b : Fin 2 → A) : Prop :=
    (∀ (i : Fin 3) (x y : Fin 2) (z : A),
      G.Adj (e (L i x,z)) (e (R i y,z+if x=1 ∧ y=1 then a i else 0))) ∧
    (∀ (i : Fin 2) (x : Fin 2) (z : A),
      G.Adj (e (L i.castSucc x,z)) (e (R i.succ x,z+if x=1 then b i else 0)))

  let tail : Fin 8 → Fin 7 := ![0,2,0,3,0,4,5,6]
  let head : Fin 8 → Fin 7 := ![2,1,3,1,4,5,6,1]


  let net  (w : Fin 8 → A) : Fin 3 → A :=
    ![w 0+w 1,w 2+w 3,w 4+w 5+w 6+w 7]

  let prefixSum  (w : Fin 8 → A) : Fin 7 → A :=
    ![0,0,w 0,w 2,w 4,w 4+w 5,w 4+w 5+w 6]

  let position : Fin 16 → Fin 7 × Fin 3 := ![
    (0,1),(2,1),(1,2),(3,0),(0,0),(4,0),(5,0),(6,0),
    (1,1),(2,2),(0,2),(3,2),(1,0),(6,1),(5,1),(4,1)]

  let label : Fin 16 → Fin 8 := ![0,1,3,2,4,5,6,7,1,0,2,3,7,6,5,4]
  let forward : Fin 16 → Bool := ![
    true,true,false,false,true,true,true,true,false,false,true,true,false,false,false,false]
  let src (k : Fin 16) := if forward k then position k else position (k+1)
  let dst (k : Fin 16) := if forward k then position (k+1) else position k

  let fiber  (w : Fin 8 → A) (v : Fin 7 × Fin 3) : A :=
    if v.1=1 then net w 0+net w 2-net w v.2
    else net w v.2-net w 1+prefixSum w v.1

  have layout : ∀ k,(src k).1=tail (label k) ∧ (dst k).1=head (label k) := by decide

  have increment  (w : Fin 8 → A) (k : Fin 16) :
      fiber w (dst k)=fiber w (src k)+w (label k) := by
    fin_cases k <;> dsimp [fiber,src,dst,position,forward,net,prefixSum,label] <;> abel


  have thetaCycle
      (e : (Fin 7 × A) ↪ X) (w : Fin 8 → A) (distinct : Function.Injective (net w))
      (edge : ∀ (i : Fin 8) (z : A),G.Adj (e (tail i,z)) (e (head i,z+w i))) :
      cycleGraph 16 ⊑ G := by
    let f (v : Fin 7 × Fin 3) := e (v.1,fiber w v)
    have inject : Function.Injective f := by
      rintro ⟨x,i⟩ ⟨y,j⟩ eq
      have same := e.injective eq
      obtain rfl : x=y := congrArg Prod.fst same
      have h : fiber w (x,i)=fiber w (x,j) := congrArg Prod.snd same
      refine Prod.ext rfl (distinct ?_)
      by_cases terminal : x=1
      · simpa [fiber,terminal] using h
      · simpa [fiber,terminal] using h
    have walk (k : Fin 16) : G.Adj (f (position k)) (f (position (k+1))) := by
      have oriented : G.Adj (f (src k)) (f (dst k)) := by
        change G.Adj (e ((src k).1,fiber w (src k))) (e ((dst k).1,fiber w (dst k)))
        rw [(layout k).1,(layout k).2,increment]
        exact edge _ _
      cases h : forward k
      · simpa [src,dst,h] using oriented.symm
      · simpa [src,dst,h] using oriented
    have simple : Function.Injective position := by decide
    refine ⟨⟨⟨fun k => f (position k),?_⟩,inject.comp simple⟩⟩
    intro i j h
    rcases cycleGraph_adj.mp h with hij|hji
    · have eq : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hij
      rw [eq]; exact (walk _).symm
    · have eq : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hji
      rw [eq]; exact walk _

  let sites (i : Fin 2) (x : Fin 2) : Fin 7 → Fin 12 :=
    ![L i.castSucc 0,L i.castSucc 1,R i.castSucc 0,R i.castSucc 1,
      R i.succ 0,L i.succ x,R i.succ 1]

  have sites_injective : ∀ i x,Function.Injective (sites i x) := by decide

  have theta_at_interface  {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A}
      (H : Norm e a b) (i x : Fin 2) (nonzero : a i.castSucc≠0)
      (hz : (if x=1 then a i.succ else 0)-b i≠0)
      (hn : (if x=1 then a i.succ else 0)-b i≠-a i.castSucc) :
      cycleGraph 16 ⊑ G := by
    let c := if x=1 then a i.succ else 0
    let w : Fin 8 → A := ![0,0,0,-a i.castSucc,0,0,c,-b i]
    have nets : net w=![0,-a i.castSucc,c-b i] := by
      funext k; fin_cases k <;> simp [net,w,sub_eq_add_neg]
    have nz : -a i.castSucc≠0 := neg_ne_zero.mpr nonzero
    have distinct : Function.Injective (net w) := by
      rw [nets]
      intro j k h
      fin_cases j <;> fin_cases k <;>
        first | rfl | exact (nz h).elim | exact (nz h.symm).elim
              | exact (hz h).elim | exact (hz h.symm).elim
              | exact (hn h).elim | exact (hn h.symm).elim
    let s : Fin 7 ↪ Fin 12 := ⟨sites i x,sites_injective i x⟩
    let f := (s.prodMap (Function.Embedding.refl A)).trans e
    have reverseCell (j : Fin 3) (u v : Fin 2) (z : A) :
        G.Adj (e (R j v,z)) (e (L j u,z-(if u=1 ∧ v=1 then a j else 0))) := by
      simpa using (H.1 j u v (z-(if u=1 ∧ v=1 then a j else 0))).symm
    have reverseLink (j : Fin 2) (u : Fin 2) (z : A) :
        G.Adj (e (R j.succ u,z)) (e (L j.castSucc u,z-(if u=1 then b j else 0))) := by
      simpa using (H.2 j u (z-(if u=1 then b j else 0))).symm
    apply thetaCycle f w distinct
    intro k z
    fin_cases k
    · simpa [f,s,sites,tail,head,w] using H.1 i.castSucc 0 0 z
    · simpa [f,s,sites,tail,head,w] using reverseCell i.castSucc 1 0 z
    · simpa [f,s,sites,tail,head,w] using H.1 i.castSucc 0 1 z
    · simpa [f,s,sites,tail,head,w,sub_eq_add_neg] using reverseCell i.castSucc 1 1 z
    · simpa [f,s,sites,tail,head,w] using H.2 i 0 z
    · simpa [f,s,sites,tail,head,w] using reverseCell i.succ x 0 z
    · simpa [f,s,sites,tail,head,w,c] using H.1 i.succ x 1 z
    · simpa [f,s,sites,tail,head,w,sub_eq_add_neg] using reverseLink i 1 z


  have interface_constraints  {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A}
      (H : Norm e a b) (nonzero : ∀ j,a j≠0) :
      cycleGraph 16 ⊑ G ∨ ∀ i : Fin 2,
        (b i=0 ∧ a i.succ= -a i.castSucc) ∨ (b i=a i.castSucc ∧ a i.succ=a i.castSucc) := by
    classical
    by_cases cycle : cycleGraph 16 ⊑ G
    · exact Or.inl cycle
    right
    intro i
    have obstruct (x : Fin 2) : (if x=1 then a i.succ else 0)-b i=0 ∨
        (if x=1 then a i.succ else 0)-b i= -a i.castSucc := by
      by_contra! h
      exact cycle (theta_at_interface H i x (nonzero _) h.1 h.2)
    have first : b i=0 ∨ b i=a i.castSucc := by simpa using obstruct 0
    have second : a i.succ-b i=0 ∨ a i.succ-b i= -a i.castSucc := by simpa using obstruct 1
    rcases first with bz|ba
    · left; refine ⟨bz,?_⟩
      rw [bz,sub_zero] at second
      exact second.resolve_left (nonzero _)
    · right; refine ⟨ba,?_⟩
      rw [ba] at second
      rcases second with h|h
      · exact sub_eq_zero.mp h
      · exact ((nonzero i.succ) (by linear_combination (norm := abel) h)).elim

  have cycleOfSteps  {n : ℕ}
      (f : Fin (n+2) → X) (inj : Function.Injective f)
      (step : ∀ i,G.Adj (f i) (f (i+1))) : cycleGraph (n+2) ⊑ G := by
    refine ⟨⟨⟨f,?_⟩,inj⟩⟩
    intro i j h
    rcases cycleGraph_adj.mp h with hij|hji
    · have eq : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hij
      rw [eq]; exact (step _).symm
    · have eq : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hji
      rw [eq]; exact step _

  have square_of_zero
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A}
      (H : Norm e a b) (i : Fin 3) (hi : a i = 0) : cycleGraph 4 ⊑ G := by
    let v : Fin 4 → Fin 12 := ![L i 0,R i 0,L i 1,R i 1]
    have inj : Function.Injective v := by
      exact (by decide : ∀ j : Fin 3, Function.Injective (![L j 0,R j 0,L j 1,R j 1] : Fin 4 → Fin 12)) i
    refine cycleOfSteps (n := 2) (fun j => e (v j,0)) ?_ ?_
    · intro k l eq; exact inj (congrArg Prod.fst (e.injective eq))
    · intro k
      have edge (x y : Fin 2) : G.Adj (e (L i x,0)) (e (R i y,0)) := by
        simpa [hi] using H.1 i x y 0
      fin_cases k
      · exact edge 0 0
      · exact (edge 1 0).symm
      · exact edge 1 1
      · exact (edge 0 1).symm

  let Dir (s : Fin 3 → ℤ) (t : Fin 2 → ℤ) (v w : Fin 12 × ℤ) : Prop :=
    (∃ (i : Fin 3) (x y : Fin 2), v.1=L i x ∧ w.1=R i y ∧
      w.2=v.2+(if x=1 ∧ y=1 then s i else 0)) ∨
    (∃ (i : Fin 2) (x : Fin 2), v.1=L i.castSucc x ∧ w.1=R i.succ x ∧
      w.2=v.2+(if x=1 then t i else 0))

  have template
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A}
      (H : Norm e a b) (d : A) (ne : d≠0)
      (s : Fin 3 → ℤ) (t : Fin 2 → ℤ) (ha : ∀ i, a i = s i • d) (hb : ∀ i, b i = t i • d)
      (v : Fin 16 → Fin 12 × ℤ)
      (apart : ∀ i j, i≠j → (v i).1=(v j).1 → (v i).2-(v j).2=1 ∨ (v j).2-(v i).2=1)
      (steps : ∀ i, Dir s t (v i) (v (i+1)) ∨ Dir s t (v (i+1)) (v i)) :
      cycleGraph 16 ⊑ G := by
    let map (u : Fin 12 × ℤ) := e (u.1,u.2 • d)
    have forward (u w : Fin 12 × ℤ) (edge : Dir s t u w) : G.Adj (map u) (map w) := by
      rcases edge with ⟨i,x,y,hu,hw,hr⟩|⟨i,x,hu,hw,hr⟩
      · change G.Adj (e (u.1,u.2 • d)) (e (w.1,w.2 • d))
        rw [hu,hw,hr,add_zsmul]
        convert H.1 i x y (u.2 • d) using 1
        split_ifs <;> simp [ha]
      · change G.Adj (e (u.1,u.2 • d)) (e (w.1,w.2 • d))
        rw [hu,hw,hr,add_zsmul]
        convert H.2 i x (u.2 • d) using 1
        split_ifs <;> simp [hb]
    refine cycleOfSteps (n := 14) (map ∘ v) ?_ ?_
    · intro i j eq
      by_contra h
      have pair := e.injective eq
      have val : (v i).2 • d = (v j).2 • d := congrArg Prod.snd pair
      obtain hp|hp := apart i j h (congrArg (fun x : Fin 12 × A => x.1) pair)
      · apply ne; simpa only [sub_zsmul,val,sub_self,add_neg_cancel,one_zsmul] using (congrArg (fun k : ℤ => k • d) hp).symm
      · apply ne; simpa only [sub_zsmul,val,sub_self,add_neg_cancel,one_zsmul] using (congrArg (fun k : ℤ => k • d) hp).symm
    · intro i
      obtain h|h := steps i
      · exact forward _ _ h
      · exact (forward _ _ h).symm

  let pathPNN : Fin 16 → Fin 12 × ℤ := ![(0,0),(2,0),(1,0),(3,1),(0,1),(2,1),(1,1),(7,1),(4,1),(6,1),(5,1),(11,0),(8,0),(10,0),(4,0),(6,0)]

  have shortPNN
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A} (H : Norm e a b)
      (d : A) (ne : d≠0) (ha : ∀ i,a i=(![1,-1,-1] : Fin 3 → ℤ) i • d)
      (hb : ∀ i,b i=(![0,-1] : Fin 2 → ℤ) i • d) : cycleGraph 16 ⊑ G :=
    template H d ne _ _ ha hb pathPNN (by decide) (by decide)

  let pathPNP : Fin 16 → Fin 12 × ℤ := ![(0,0),(2,0),(1,0),(3,1),(0,1),(2,1),(1,1),(7,1),(4,1),(6,1),(5,1),(11,1),(9,0),(10,0),(4,0),(6,0)]

  have shortPNP
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A} (H : Norm e a b)
      (d : A) (ne : d≠0) (ha : ∀ i,a i=(![1,-1,1] : Fin 3 → ℤ) i • d)
      (hb : ∀ i,b i=(![0,0] : Fin 2 → ℤ) i • d) : cycleGraph 16 ⊑ G :=
    template H d ne _ _ ha hb pathPNP (by decide) (by decide)

  let pathPPN : Fin 16 → Fin 12 × ℤ := ![(0,0),(2,0),(1,0),(3,1),(0,1),(2,1),(1,1),(7,2),(5,1),(6,1),(4,1),(10,1),(9,1),(11,0),(5,0),(6,0)]

  have shortPPN
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A} (H : Norm e a b)
      (d : A) (ne : d≠0) (ha : ∀ i,a i=(![1,1,-1] : Fin 3 → ℤ) i • d)
      (hb : ∀ i,b i=(![1,0] : Fin 2 → ℤ) i • d) : cycleGraph 16 ⊑ G :=
    template H d ne _ _ ha hb pathPPN (by decide) (by decide)

  let pathPPP : Fin 16 → Fin 12 × ℤ := ![(0,0),(2,0),(1,0),(3,1),(0,1),(2,1),(1,1),(7,2),(5,1),(6,1),(4,1),(10,1),(8,1),(11,1),(5,0),(6,0)]

  have shortPPP
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A} (H : Norm e a b)
      (d : A) (ne : d≠0) (ha : ∀ i,a i=(![1,1,1] : Fin 3 → ℤ) i • d)
      (hb : ∀ i,b i=(![1,1] : Fin 2 → ℤ) i • d) : cycleGraph 16 ⊑ G :=
    template H d ne _ _ ha hb pathPPP (by decide) (by decide)


  have aligned_short
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A} (H : Norm e a b)
      (ne : a 0≠0)
      (align : ∀ i : Fin 2, (b i=0 ∧ a i.succ= -a i.castSucc) ∨
        (b i=a i.castSucc ∧ a i.succ=a i.castSucc)) : cycleGraph 16 ⊑ G := by
    have h0 : (b 0=0 ∧ a 1= -a 0) ∨ (b 0=a 0 ∧ a 1=a 0) := align 0
    have h1 : (b 1=0 ∧ a 2= -a 1) ∨ (b 1=a 1 ∧ a 2=a 1) := align 1
    rcases h0 with ⟨k0,d1⟩|⟨k0,d1⟩ <;> rcases h1 with ⟨k1,d2⟩|⟨k1,d2⟩
    · apply shortPNP H (a 0) ne <;> intro i <;> fin_cases i <;> simp [k0,k1,d2,d1]
    · apply shortPNN H (a 0) ne <;> intro i <;> fin_cases i <;> simp [k0,k1,d2,d1]
    · apply shortPPN H (a 0) ne <;> intro i <;> fin_cases i <;> simp [k0,k1,d2,d1]
    · apply shortPPP H (a 0) ne <;> intro i <;> fin_cases i <;> simp [k0,k1,d2,d1]

  let squareDefect (w : Fin 3 → Fin 2 → Fin 2 → A) (i : Fin 3) : A :=
    w i 0 0-w i 1 0+w i 1 1-w i 0 1


  let linkDefect (w : Fin 3 → Fin 2 → Fin 2 → A) (k : Fin 2 → Fin 2 → A) (i : Fin 2) : A :=
    w i.castSucc 0 0-w i.castSucc 1 0+k i 1-k i 0+w i.succ 0 0-w i.succ 0 1


  have gauge_explicit (e : (Fin 12 × A) ↪ X)
      (w : Fin 3 → Fin 2 → Fin 2 → A) (k : Fin 2 → Fin 2 → A)
      (cell : ∀ i x y z, G.Adj (e (L i x,z)) (e (R i y,z+w i x y)))
      (link : ∀ (i : Fin 2) x z, G.Adj (e (L i.castSucc x,z)) (e (R i.succ x,z+k i x))) :
      ∃ e' : (Fin 12 × A) ↪ X, Norm e' (squareDefect w) (linkDefect w k) := by
    let o : Fin 3 → A := ![0,k 0 0-w 1 0 0,(k 0 0-w 1 0 0)+k 1 0-w 2 0 0]
    have succ (i : Fin 2) : o i.succ = o i.castSucc + k i 0 - w i.succ 0 0 := by
      fin_cases i <;> simp [o]
    let l (i : Fin 3) (x : Fin 2) := if x=0 then o i else o i+w i 0 0-w i 1 0
    let r (i : Fin 3) (y : Fin 2) := o i+w i 0 y
    let pot : Fin 12 → A :=
      ![l 0 0,l 0 1,r 0 0,r 0 1,l 1 0,l 1 1,r 1 0,r 1 1,l 2 0,l 2 1,r 2 0,r 2 1]
    have left (i : Fin 3) (x : Fin 2) : pot (L i x) = l i x := by
      fin_cases i <;> fin_cases x <;> rfl
    have right (i : Fin 3) (x : Fin 2) : pot (R i x) = r i x := by
      fin_cases i <;> fin_cases x <;> rfl
    let e' : (Fin 12 × A) ↪ X := ⟨fun p => e (p.1,p.2+pot p.1),by
      rintro ⟨t,v⟩ ⟨u,z⟩ eq
      have pair := e.injective eq
      obtain rfl : t=u := congrArg Prod.fst pair
      have shift : v+pot t=z+pot t := congrArg Prod.snd pair
      exact Prod.ext rfl (add_right_cancel shift)⟩
    refine ⟨e',⟨?_,?_⟩⟩
    · intro i x y z
      change G.Adj (e (L i x,z+pot (L i x)))
        (e (R i y,(z+if x=1 ∧ y=1 then squareDefect w i else 0)+pot (R i y)))
      rw [left,right]
      have c := cell i x y (z+l i x)
      convert c using 2
      congr 1
      fin_cases x <;> fin_cases y <;> simp [l,r,squareDefect] <;> abel
    · intro i x z
      change G.Adj (e (L i.castSucc x,z+pot (L i.castSucc x)))
        (e (R i.succ x,(z+if x=1 then linkDefect w k i else 0)+pot (R i.succ x)))
      rw [left,right]
      have c := link i x (z+l i.castSucc x)
      convert c using 2
      congr 1
      fin_cases x <;> simp [l,r,linkDefect,succ] <;> abel

  have normalized_cycle
      {e : (Fin 12 × A) ↪ X} {a : Fin 3 → A} {b : Fin 2 → A}
      (H : Norm e a b) : cycleGraph 4 ⊑ G ∨ cycleGraph 16 ⊑ G := by
    classical
    by_cases someZero : ∃ i,a i=0
    · obtain ⟨i,hi⟩ := someZero
      exact Or.inl (square_of_zero H i hi)
    have ne : ∀ i,a i≠0 := not_exists.mp someZero
    right
    obtain cycle|align := interface_constraints H ne
    · exact cycle
    · exact aligned_short H (ne 0) align

  obtain ⟨e,normalized⟩ := gauge_explicit raw weights links rawCell rawLink
  exact normalized_cycle normalized

/-- Any host containing the three weighted Haar matchings contains the entire
three-cell strip. The voltage functions may vary independently from edge to edge. -/
theorem haar_involution_short {A B X : Type*} [AddCommGroup A] [AddCommGroup B]
    {G : SimpleGraph X} (e : (Bool × B × A) ↪ X) (h d : B)
    (inv : h+h=0) (distinct : Function.Injective (fun p : Fin 3 × Fin 2 => p.1.val • d+p.2.val • h))
    (w0 wh wd : B → A)
    (idEdge : ∀ p z,G.Adj (e (false,p,z)) (e (true,p,z+w0 p)))
    (hEdge : ∀ p z,G.Adj (e (false,p,z)) (e (true,p+h,z+wh p)))
    (dEdge : ∀ p z,G.Adj (e (false,p,z)) (e (true,p+d,z+wd p))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let L (i : Fin 3) (x : Fin 2) : Fin 12 := ⟨4*i.val+x.val,by omega⟩
  let R (i : Fin 3) (x : Fin 2) : Fin 12 := ⟨4*i.val+2+x.val,by omega⟩
  let level (h d : B) (p : Fin 3 × Fin 2) := p.1.val • d+p.2.val • h
  let chart : Fin 12 → Bool × Fin 3 × Fin 2 := ![
  (false,0,0),(false,0,1),(true,0,0),(true,0,1),
  (false,1,0),(false,1,1),(true,1,0),(true,1,1),
  (false,2,0),(false,2,1),(true,2,0),(true,2,1)]

  have chart_injective : Function.Injective chart := by decide +revert
  have chart_L : ∀ i x,chart (L i x)=(false,i,x) := by decide +revert
  have chart_R : ∀ i x,chart (R i x)=(true,i,x) := by decide +revert

  let f : (Fin 12 × A) ↪ X := {
    toFun v := e ((chart v.1).1,level h d (chart v.1).2,v.2)
    inj' := by
      rintro ⟨u,z⟩ ⟨v,y⟩ eq
      have same := e.injective eq
      have sites : chart u=chart v := Prod.ext (congrArg (fun a : Bool × B × A => a.1) same)
        (distinct (congrArg (fun a : Bool × B × A => a.2.1) same))
      exact Prod.ext (chart_injective sites) (congrArg (fun a : Bool × B × A => a.2.2) same) }
  have atL (i : Fin 3) (x : Fin 2) (z : A) : f (L i x,z)=e (false,level h d (i,x),z) := by
    change e ((chart (L i x)).1,level h d (chart (L i x)).2,z)=_; rw [chart_L]
  have atR (i : Fin 3) (x : Fin 2) (z : A) : f (R i x,z)=e (true,level h d (i,x),z) := by
    change e ((chart (R i x)).1,level h d (chart (R i x)).2,z)=_; rw [chart_R]
  have across (i : Fin 3) (x y : Fin 2) (ne : x≠y) : level h d (i,y)=level h d (i,x)+h := by
    fin_cases x <;> fin_cases y <;> simp_all [level,add_assoc]
  have next (i : Fin 2) (x : Fin 2) : level h d (i.succ,x)=level h d (i.castSucc,x)+d := by
    change (i.val+1) • d+x.val • h=(i.val • d+x.val • h)+d
    rw [add_nsmul,one_nsmul]; abel
  let w (i : Fin 3) (x y : Fin 2) := if x=y then w0 (level h d (i,x)) else wh (level h d (i,x))
  let k (i : Fin 2) (x : Fin 2) := wd (level h d (i.castSucc,x))
  apply necklace_voltage_cycle G f w k
  · intro i x y z
    rw [atL,atR]
    by_cases eq : x=y
    · subst y; simpa [w] using idEdge (level h d (i,x)) z
    · rw [across i x y eq]
      simpa [w,eq] using hEdge (level h d (i,x)) z
  · intro i x z
    rw [atL,atR,next]
    exact dEdge _ _

end NecklaceReduction

universe u
namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H2_R1
open SimpleGraph

/-- The generated permutation group has no abelian quotient with abelian kernel
in which one matching difference is an involution spanning three cells with a second. -/
def H1 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    Even (Nat.card (Subgroup.closure ({p,q} : Set (Equiv.Perm X)))) →
    (∀ K : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))),
      K.Normal → IsPGroup 2 K → K = ⊥) →
    let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
    let s : Fin 3 → K := ![1,⟨p,Subgroup.subset_closure (by simp)⟩,
      ⟨q,Subgroup.subset_closure (by simp)⟩]
    (∀ (B : Type) [AddCommGroup B] (f : K →* Multiplicative B),
      Function.Surjective f → (∀ i j : f.ker, i*j=j*i) →
      ∀ σ : Equiv.Perm (Fin 3),
        let h := (f (s (σ 1))).toAdd - (f (s (σ 0))).toAdd
        let d := (f (s (σ 2))).toAdd - (f (s (σ 0))).toAdd
        h+h=0 → ¬ Function.Injective (fun z : Fin 3 × Fin 2 => z.1.val • d + z.2.val • h)) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))

/-- A qualifying quotient exists, but every point stabilizer has nontrivial image in it. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    Even (Nat.card (Subgroup.closure ({p,q} : Set (Equiv.Perm X)))) →
    (∀ K : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))),
      K.Normal → IsPGroup 2 K → K = ⊥) →
    let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
    let s : Fin 3 → K := ![1,⟨p,Subgroup.subset_closure (by simp)⟩,
      ⟨q,Subgroup.subset_closure (by simp)⟩]
    ∀ (B : Type) [AddCommGroup B] (f : K →* Multiplicative B),
      Function.Surjective f → (∀ i j : f.ker, i*j=j*i) →
      ∀ σ : Equiv.Perm (Fin 3),
        let h := (f (s (σ 1))).toAdd - (f (s (σ 0))).toAdd
        let d := (f (s (σ 2))).toAdd - (f (s (σ 0))).toAdd
        h+h=0 → Function.Injective (fun z : Fin 3 × Fin 2 => z.1.val • d + z.2.val • h) →
        (∀ x : X, ∃ g : K, g • x=x ∧ f g≠1) →
        ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))

/-- Left coset fibers along a normal abelian kernel. The stabilizer may be
nonnormal in the acting group; normality inside the abelian kernel suffices. -/
theorem abelian_orbit_coordinates {A : Type u} {X Q : Type*} {I : Type*} [Add I] [Group A] [Group Q] [MulAction A X]
    (f : A →* Q) (comm : ∀ a b : f.ker, a*b=b*a) (x : X)
    (stab : ∀ a : A, a • x=x → f a=1)
    (r : Bool → I → A) (sep : ∀ b, Function.Injective (fun i => f (r b i)))
    (shift : Fin 3 → A) (δ : Fin 3 → I)
    (matchQ : ∀ i k, f (shift k * r false i)=f (r true (i+δ k)))
    (G : SimpleGraph (Bool × X))
    (adj : ∀ k y, G.Adj (false,y) (true,shift k • y)) :
    ∃ (V : Type u) (_ : AddCommGroup V) (w : I → Fin 3 → V)
      (ι : (Bool × I × V) ↪ (Bool × X)),
      (∀ i k g, G.Adj (ι (false,i,g)) (ι (true,i+δ k,g+w i k))) ∧
      (∀ i k l, δ k=δ l → (∀ y : X,shift k • y ≠ shift l • y) → w i k ≠ w i l) := by
  classical
  let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := comm }
  let H := MulAction.stabilizer f.ker x
  let D := f.ker ⧸ H
  let point (g : D) : X := MulAction.ofQuotientStabilizer f.ker x g
  have pinj : Function.Injective point := MulAction.injective_ofQuotientStabilizer f.ker x
  let h (i : I) (k : Fin 3) : f.ker := ⟨(r true (i+δ k))⁻¹*(shift k*r false i),by
    change f _ = 1
    rw [map_mul,map_inv,matchQ,inv_mul_cancel]⟩
  let w (i : I) (k : Fin 3) : Additive D := Additive.ofMul (QuotientGroup.mk (h i k))
  let v (b : Bool) (i : I) (g : D) := r b i • point g
  have distinct (b : Bool) {i j : I} {g g' : D} (same : v b i g=v b j g') : i=j := by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective H g
    obtain ⟨a',ha'⟩ := QuotientGroup.mk'_surjective H g'
    subst g; subst g'
    change r b i • ((a : A) • x)=r b j • ((a' : A) • x) at same
    rw [smul_smul,smul_smul] at same
    have fixed : ((r b j*(a':A))⁻¹*(r b i*(a:A))) • x=x := by
      rw [mul_smul,same,inv_smul_smul]
    have he := stab _ fixed
    have fa : f (a:A)=1 := a.property
    have fb : f (a':A)=1 := a'.property
    simp only [map_mul,map_inv,fa,fb,mul_one,inv_mul_eq_one] at he
    exact sep b he.symm
  let embed : (Bool × I × Additive D) ↪ (Bool × X) := {
    toFun z := (z.1,v z.1 z.2.1 z.2.2.toMul)
    inj' := by
      rintro ⟨b,i,g⟩ ⟨c,j,g'⟩ eq
      obtain rfl : b=c := congrArg Prod.fst eq
      have h' : v b i g.toMul=v b j g'.toMul := congrArg Prod.snd eq
      obtain rfl : i=j := distinct b h'
      have hv : point g.toMul=point g'.toMul := (MulAction.injective (r b i)) h'
      have hg : g=g' := congrArg Additive.ofMul (pinj hv)
      cases hg
      rfl }
  have transport (i : I) (k : Fin 3) (g : Additive D) :
      shift k • v false i g.toMul = v true (i+δ k) (g+w i k).toMul := by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective H g.toMul
    change shift k • (r false i • point g.toMul) =
      r true (i+δ k) • point (g.toMul*QuotientGroup.mk (h i k))
    rw [← ha]
    change shift k • (r false i • ((a:A) • x)) =
      r true (i+δ k) • point ((QuotientGroup.mk' H a)*(QuotientGroup.mk' H (h i k)))
    rw [← map_mul]
    change shift k • (r false i • ((a:A) • x)) =
      r true (i+δ k) • (((a*(h i k):f.ker):A) • x)
    rw [comm a (h i k),Subgroup.coe_mul,smul_smul,smul_smul]
    simp [h,mul_smul]
  refine ⟨Additive D,inferInstance,w,embed,?_,?_⟩
  · intro i k g
    change G.Adj (false,v false i g.toMul) (true,v true (i+δ k) (g+w i k).toMul)
    rw [←transport]; exact adj _ _
  · intro i k l same separate eq
    apply separate (v false i (0 : Additive D).toMul)
    rw [transport i k 0,transport i l 0,same,eq]

/-- Pull an involution-difference quotient patch back to the given permutation action. -/
theorem orbit_short {A X B : Type} [Group A] [MulAction A X] [AddCommGroup B]
    (f : A →* Multiplicative B) (onto : Function.Surjective f)
    (comm : ∀ i j : f.ker,i*j=j*i) (x : X) (stab : ∀ g : A,g • x=x → f g=1)
    (t : Fin 3 → A) (G : SimpleGraph (Bool × X))
    (edge : ∀ k y, G.Adj (false,y) (true,t k • y))
    (inv : ((f (t 1)).toAdd-(f (t 0)).toAdd)+((f (t 1)).toAdd-(f (t 0)).toAdd)=0)
    (distinct : Function.Injective (fun z : Fin 3 × Fin 2 =>
      z.1.val • ((f (t 2)).toAdd-(f (t 0)).toAdd)+z.2.val • ((f (t 1)).toAdd-(f (t 0)).toAdd))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let off (k : Fin 3) := (f (t k)).toAdd
  let δ (k : Fin 3) := off k-off 0
  let c (b : Bool) := if b then off 0 else 0
  let rep (b : Bool) (i : B) := (onto (Multiplicative.ofAdd (i+c b))).choose
  have image (b : Bool) (i : B) : f (rep b i)=Multiplicative.ofAdd (i+c b) :=
    (onto _).choose_spec
  have separate (b : Bool) : Function.Injective (fun i => f (rep b i)) := by
    intro i j h
    simp only [image] at h
    exact add_right_cancel (congrArg Multiplicative.toAdd h)
  have align (i : B) (k : Fin 3) : f (t k*rep false i)=f (rep true (i+δ k)) := by
    rw [map_mul,image,image]
    apply Multiplicative.toAdd.injective
    change off k+(i+c false)=i+δ k+c true
    simp [c,δ]
    abel
  obtain ⟨V,_,w,e,edges,_⟩ := abelian_orbit_coordinates f comm x stab rep separate t δ align G edge
  apply NecklaceReduction.haar_involution_short e (δ 1) (δ 2) inv distinct
    (fun i => w i 0) (fun i => w i 1) (fun i => w i 2)
  · intro i v; simpa [δ] using edges i 0 v
  · exact fun i v => edges i 1 v
  · exact fun i v => edges i 2 v

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2.H2 := by
  intro missing moving X _ _ p q sep density even core
  classical
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  let s : Fin 3 → K := ![1,⟨p,Subgroup.subset_closure (by simp)⟩,
    ⟨q,Subgroup.subset_closure (by simp)⟩]
  let G := SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))
  by_contra noCycle
  apply noCycle
  apply missing X p q sep density even core
  intro B _ f onto comm σ h d inv distinct
  apply noCycle
  by_cases outside : ∀ x : X, ∃ g : K, g • x=x ∧ f g≠1
  · exact moving X p q sep density even core B f onto comm σ inv distinct outside
  push Not at outside
  obtain ⟨x,stays⟩ := outside
  have edge (k : Fin 3) (y : X) : G.Adj (false,y) (true,(s k) • y) := by
    fin_cases k
    · exact ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩
    · exact ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩
  obtain short|long := orbit_short f onto comm x stays (s ∘ σ) G
    (fun k => edge (σ k)) inv distinct
  · exact ⟨2,by decide,short⟩
  · exact ⟨4,by decide,long⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H2_R1
