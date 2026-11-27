import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1

/-! Upper certificates for the dense triangle-good graphs in Brandt,
Brinkmann and Harmuth (1998), Table 2. For orders four through six a
single explicit triangle-free host bounds the edge count on every image
of the vertices. Two incompatible squared-degree sums settle order seven.
For orders eight and nine we specify finite host
families: a common graph embeds in the intersection of the complement
graphs pulled back along its vertex placements. This turns each upper
bound into a finite maximum-edge computation on a fixed vertex set. -/
namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1

open SimpleGraph Finset

/-- A common edge bound for the 2 specified hosts on 15 vertices. -/
def H1 : Prop :=
  let masks := (![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ)
  let C (a : Fin 2) : SimpleGraph (Fin 15) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*15+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 2 → Fin 8 ↪ Fin 15,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 20

/-- A common edge bound for the 3 specified hosts on 17 vertices. -/
def H2 : Prop :=
  let masks := (![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ)
  let C (a : Fin 3) : SimpleGraph (Fin 17) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 3 → Fin 9 ↪ Fin 17,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 27

/-- Finite obstruction families for the final three orders. -/
def H3 : Prop := ∀ t : Fin 3,
  let n := t.val+10
  let h := 2*n-1
  let q := (![33,41,49] : Fin 3 → ℕ) t
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin h) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*h+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ f : Fin r → Fin n ↪ Fin h,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ q

theorem density {n h q : ℕ} (G : SimpleGraph (Fin n)) (C : SimpleGraph (Fin h))
    [DecidableRel C.Adj]
    (bounds : ∀ S ∈ (univ : Finset (Fin h)).powersetCard n,
       (Cᶜ.edgeFinset ∩ S.sym2).card ≤ q)
    (count : q < G.edgeSet.ncard) : ¬ G ⊑ Cᶜ := by
  classical
  rintro ⟨e⟩
  let f := e.toEmbedding
  let S := (univ : Finset (Fin n)).map f
  have hs : S ∈ (univ : Finset (Fin h)).powersetCard n := by simp [S]
  have inc : G.edgeFinset.map f.sym2Map ⊆ Cᶜ.edgeFinset ∩ S.sym2 := by
    apply Finset.subset_inter
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
      exact SimpleGraph.mem_edgeFinset.mpr (e.mapEdgeSet ⟨y,SimpleGraph.mem_edgeFinset.mp hy⟩).property
    · change G.edgeFinset.map f.sym2Map ⊆ (univ.map f).sym2
      rw [Finset.sym2_map]
      exact Finset.map_subset_map.mpr (by simp)
  have bound := (Finset.card_le_card inc).trans (bounds S hs)
  rw [Finset.card_map] at bound
  have eq : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card G.edgeSet]
    congr 1
    ext x
    simp [SimpleGraph.edgeFinset]
  omega

theorem triangleFree {h : ℕ} (C : SimpleGraph (Fin h))
    (ht : ∀ i j l, C.Adj i j → C.Adj i l → ¬C.Adj j l) : C.CliqueFree 3 := by
  intro S hS
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hS
  exact ht x y z hxy hxz hyz


lemma common {n h r q : ℕ} (C : Fin r → SimpleGraph (Fin h)) (tri : ∀ a, (C a).CliqueFree 3)
    (cap : ∀ f : Fin r → Fin n ↪ Fin h,
      let D := ⨅ a, (C a)ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ q)
    (G : SimpleGraph (Fin n)) (gc : G.Connected) (ge : q < G.edgeSet.ncard) :
    ∃ B : SimpleGraph (Fin h), B.CliqueFree 3 ∧ ¬ G ⊑ Bᶜ := by
  classical
  by_contra! no
  let e (a) : G.Copy (C a)ᶜ := Classical.choice (no (C a) (tri a))
  let f (a) := (e a).toEmbedding
  let D := ⨅ a, (C a)ᶜ.comap (f a)
  have sub : G ≤ D := le_iInf fun a i j hij => (e a).toHom.map_rel' hij
  have ecount := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono sub)
  exact (Nat.not_le_of_lt ge) (ecount.trans (cap f (SimpleGraph.Connected.mono sub gc)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem upper4 (G : SimpleGraph (Fin 4)) (hc : 5 < G.edgeSet.ncard) :
    ∃ C : SimpleGraph (Fin 7), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let C : SimpleGraph (Fin 7) :=
    { Adj := fun i j => i ≠ j ∧ (8657448036 : ℕ).testBit ((min i j).val*7+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  refine ⟨C,triangleFree C (by decide),density G C ?_ hc⟩
  let candidates := (univ : Finset (Fin 7)).powersetCard 4
  have check : candidates.filter (fun S => 5 < (Cᶜ.edgeFinset ∩ S.sym2).card) = ∅ := by decide +kernel
  intro S hs
  exact le_of_not_gt <| fun bad => by
    have hmem : S ∈ candidates.filter (fun T => 5 < (Cᶜ.edgeFinset ∩ T.sym2).card) :=
      Finset.mem_filter.mpr ⟨hs,bad⟩
    simpa only [check,Finset.notMem_empty] using hmem

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem upper5 (G : SimpleGraph (Fin 5)) (hc : 8 < G.edgeSet.ncard) :
    ∃ C : SimpleGraph (Fin 9), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let C : SimpleGraph (Fin 9) :=
    { Adj := fun i j => i ≠ j ∧ (2365794947265971925092 : ℕ).testBit ((min i j).val*9+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  refine ⟨C,triangleFree C (by decide),density G C ?_ hc⟩
  let candidates := (univ : Finset (Fin 9)).powersetCard 5
  have check : candidates.filter (fun S => 8 < (Cᶜ.edgeFinset ∩ S.sym2).card) = ∅ := by decide +kernel
  intro S hs
  exact le_of_not_gt <| fun bad => by
    have hmem : S ∈ candidates.filter (fun T => 8 < (Cᶜ.edgeFinset ∩ T.sym2).card) :=
      Finset.mem_filter.mpr ⟨hs,bad⟩
    simpa only [check,Finset.notMem_empty] using hmem

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem upper6 (G : SimpleGraph (Fin 6)) (hc : 12 < G.edgeSet.ncard) :
    ∃ C : SimpleGraph (Fin 11), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let C : SimpleGraph (Fin 11) :=
    { Adj := fun i j => i ≠ j ∧ (649195563651347488628968623064480 : ℕ).testBit ((min i j).val*11+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  refine ⟨C,triangleFree C (by decide),density G C ?_ hc⟩
  let candidates := (univ : Finset (Fin 11)).powersetCard 6
  have check : candidates.filter (fun S => 12 < (Cᶜ.edgeFinset ∩ S.sym2).card) = ∅ := by decide +kernel
  intro S hs
  exact le_of_not_gt <| fun bad => by
    have hmem : S ∈ candidates.filter (fun T => 12 < (Cᶜ.edgeFinset ∩ T.sym2).card) :=
      Finset.mem_filter.mpr ⟨hs,bad⟩
    simpa only [check,Finset.notMem_empty] using hmem
theorem saturated {n h q : ℕ} (G : SimpleGraph (Fin n)) (B : SimpleGraph (Fin h))
    [DecidableRel B.Adj] (e : G.Copy B) (gsize : G.edgeSet.ncard = q)
    (bound : ∀ S ∈ (univ : Finset (Fin h)).powersetCard n, (B.edgeFinset ∩ S.sym2).card ≤ q) :
    ∃ S ∈ (univ : Finset (Fin h)).powersetCard n, (B.edgeFinset ∩ S.sym2).card = q ∧ Nonempty (G ≃g B.induce (S : Set (Fin h))) := by
  classical
  let f := e.toEmbedding
  let S := (univ : Finset (Fin n)).map f
  have hs : S ∈ (univ : Finset (Fin h)).powersetCard n := by simp [S]
  let fn (i : Fin n) : (S : Set (Fin h)) := ⟨f i,mem_map.mpr ⟨i,mem_univ _,rfl⟩⟩
  have fb : Function.Bijective fn := by
    constructor
    · intro i j eq
      exact f.injective (congrArg Subtype.val eq)
    · intro v
      obtain ⟨i,_,eq⟩ := mem_map.mp v.prop
      exact ⟨i,Subtype.ext eq⟩
  let σ := Equiv.ofBijective fn fb
  let T := B.induce (S : Set (Fin h))
  let D := T.comap σ
  let iso : D ≃g T := SimpleGraph.Iso.comap σ T
  have dcard : D.edgeFinset.card = (B.edgeFinset ∩ S.sym2).card := by
    calc
      _ = T.edgeFinset.card := iso.card_edgeFinset_eq
      _ = _ := by rw [← B.filter_edgeFinset_toFinset_subset, B.card_filter_edgeFinset_toFinset_subset]
  have sub : G ≤ D := fun _ _ h => e.toHom.map_rel' h
  have gc : G.edgeFinset.card = q := by
    convert gsize using 1
    rw [Set.ncard_eq_toFinset_card G.edgeSet]
    congr 1
    ext v
    simp [SimpleGraph.edgeFinset]
  have eql : G = D := SimpleGraph.edgeFinset_inj.mp <| Finset.eq_of_subset_of_card_le
    (edgeFinset_mono sub) (by rw [gc,dcard]; exact bound S hs)
  refine ⟨S,hs,?_,?_⟩
  · exact le_antisymm (bound S hs) (gc ▸ ((Finset.card_le_card (edgeFinset_mono sub)).trans_eq dcard))
  · exact ⟨eql ▸ iso⟩

lemma sq_eq {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (B : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel B.Adj] (e : G ≃g B) :
    (∑ v, G.degree v ^ 2) = ∑ w, B.degree w ^ 2 := by
  calc
    _ = ∑ i, B.degree (e i)^2 := by simp
    _ = _ := e.toEquiv.sum_comp (fun i => B.degree i ^ 2)

lemma measures {h : ℕ} (B : SimpleGraph (Fin h)) [DecidableRel B.Adj] (S : Finset (Fin h)) :
    (∑ v ∈ S, (S.filter (B.Adj v)).card) = 2*(B.edgeFinset ∩ S.sym2).card ∧
    (∑ v ∈ S, (S.filter (B.Adj v)).card ^ 2) = ∑ v : S, (B.induce (S : Set (Fin h))).degree v ^ 2 := by
  let D := B.induce (S : Set (Fin h))
  have degree (v : S) : D.degree v = (S.filter (B.Adj v.val)).card := by
    let eqv : D.neighborSet v ≃ {x // x ∈ S.filter (B.Adj v.val)} :=
      { toFun := fun w => ⟨w.1.1,Finset.mem_filter.mpr ⟨w.1.2,w.2⟩⟩
        invFun := fun w => ⟨⟨w.1,(Finset.mem_filter.mp w.2).1⟩,(Finset.mem_filter.mp w.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (D.card_neighborSet_eq_degree v).symm.trans ((Fintype.card_congr eqv).trans (Fintype.card_coe _))
  constructor
  · calc
      _ = ∑ v : S, (S.filter (B.Adj v.val)).card := (Finset.sum_coe_sort S _).symm
      _ = ∑ v : S, D.degree v := Finset.sum_congr rfl (fun v _ => (degree v).symm)
      _ = 2*D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
      _ = _ := by rw [← B.filter_edgeFinset_toFinset_subset,B.card_filter_edgeFinset_toFinset_subset]
  · calc
      _ = ∑ v : S, (S.filter (B.Adj v.val)).card^2 := (Finset.sum_coe_sort S _).symm
      _ = _ := Finset.sum_congr rfl (fun v _ => congrArg (·^2) (degree v).symm)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
lemma leftData :
  let leftHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45674714610467219645711623535978988764196899492 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel leftHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let B := leftHostᶜ
  let bad (S : Finset (Fin 13)) :=
    let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
    !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) = 172)))
  ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
lemma rightData :
  let rightHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45677501523083455278743916298545253931614405028 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel rightHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let B := rightHostᶜ
  let bad (S : Finset (Fin 13)) :=
    let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
    !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) ≤ 170)))
  ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 16000000 in
theorem upperSeven (G : SimpleGraph (Fin 7)) (hg : G.edgeSet.ncard = 17) :
    ∃ C : SimpleGraph (Fin 13), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ := by
  let leftHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45674714610467219645711623535978988764196899492 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel leftHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  have leftBound : ∀ S ∈ (univ : Finset (Fin 13)).powersetCard 7,
      let B := leftHostᶜ
      let v := (B.edgeFinset ∩ S.sym2).card
      v < 17 ∨ (v = 17 ∧ (∑ v, (B.induce (S : Set (Fin 13))).degree v ^ 2) = 172) := by
    let B := leftHostᶜ
    let bad (S : Finset (Fin 13)) :=
      let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
      !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) = 172)))
    have check : ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := leftData
    intro S hs
    have allowed : bad S = false := by
      by_contra! hy
      have hx : S ∈ ((univ : Finset (Fin 13)).powersetCard 7).filter (fun T => bad T=true) :=
        Finset.mem_filter.mpr ⟨hs,by simpa using hy⟩
      simp [check] at hx
    have ⟨total,moment⟩ := measures B S
    simp only [bad,Bool.not_eq_false',decide_eq_true_eq,total,moment] at allowed
    rcases allowed with small|⟨tight,hval⟩
    · left; change (B.edgeFinset ∩ S.sym2).card < 17; omega
    · right; exact ⟨by change (B.edgeFinset ∩ S.sym2).card = 17; omega,hval⟩
  let rightHost : SimpleGraph (Fin 13) :=
    { Adj := fun i j => i ≠ j ∧ (45677501523083455278743916298545253931614405028 : ℕ).testBit ((min i j).val*13+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel rightHost.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  have rightBound : ∀ S ∈ (univ : Finset (Fin 13)).powersetCard 7,
      let B := rightHostᶜ
      let v := (B.edgeFinset ∩ S.sym2).card
      v < 17 ∨ (v = 17 ∧ (∑ v, (B.induce (S : Set (Fin 13))).degree v ^ 2) ≤ 170) := by
    let B := rightHostᶜ
    let bad (S : Finset (Fin 13)) :=
      let v := ∑ a ∈ S, (S.filter (B.Adj a)).card
      !(decide (v < 34 ∨ (v = 34 ∧ (∑ a ∈ S, (S.filter (B.Adj a)).card^2) ≤ 170)))
    have check : ((univ : Finset (Fin 13)).powersetCard 7).filter (fun S => bad S = true) = ∅ := rightData
    intro S hs
    have allowed : bad S = false := by
      by_contra! hy
      have hx : S ∈ ((univ : Finset (Fin 13)).powersetCard 7).filter (fun T => bad T=true) :=
        Finset.mem_filter.mpr ⟨hs,by simpa using hy⟩
      simp [check] at hx
    have ⟨total,moment⟩ := measures B S
    simp only [bad,Bool.not_eq_false',decide_eq_true_eq,total,moment] at allowed
    rcases allowed with small|⟨tight,hval⟩
    · left; change (B.edgeFinset ∩ S.sym2).card < 17; omega
    · right; exact ⟨by change (B.edgeFinset ∩ S.sym2).card = 17; omega,hval⟩
  classical
  by_cases hl : G ⊑ leftHostᶜ
  · refine ⟨rightHost,triangleFree rightHost (by decide),?_⟩
    rintro ⟨r⟩
    obtain ⟨l⟩ := hl
    obtain ⟨S,hs,sc,⟨iso⟩⟩ := saturated G leftHostᶜ l hg
      (fun s h => (leftBound s h).elim Nat.le_of_lt (fun z => z.1.le))
    obtain ⟨T,ht,tc,⟨iso'⟩⟩ := saturated G rightHostᶜ r hg
      (fun s h => (rightBound s h).elim Nat.le_of_lt (fun z => z.1.le))
    have h₁ := ((leftBound S hs).resolve_left (by omega)).2
    have h₂ := ((rightBound T ht).resolve_left (by omega)).2
    have x := sq_eq _ _ iso
    have y := sq_eq _ _ iso'
    omega
  · exact ⟨leftHost,triangleFree leftHost (by decide),hl⟩

theorem main : H1 → H2 → H3 → OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1.H2 := by
  intro b c d k
  fin_cases k <;> dsimp only <;> intro G gc ge
  · exact upper4 G (by rw [ge]; exact Nat.lt_succ_self _)
  · exact upper5 G (by rw [ge]; exact Nat.lt_succ_self _)
  · exact upper6 G (by rw [ge]; exact Nat.lt_succ_self _)
  · exact upperSeven G ge
  · let masks := (![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ)
    let C (a : Fin 2) : SimpleGraph (Fin 15) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*15+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    have tr : ∀ t : Fin 2, ∀ i j l : Fin 15, (i ≠ j ∧ ((![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ) t).testBit ((min i j).val*15+(max i j).val) = true) → (i ≠ l ∧ ((![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ) t).testBit ((min i l).val*15+(max i l).val) = true) → ¬ (j ≠ l ∧ ((![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ) t).testBit ((min j l).val*15+(max j l).val) = true) := by decide
    exact common C (fun t => triangleFree _ (tr t)) b G gc (by rw [ge]; exact Nat.lt_succ_self _)
  · let masks := (![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ)
    let C (a : Fin 3) : SimpleGraph (Fin 17) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    have tr : ∀ t : Fin 3, ∀ i j l : Fin 17, (i ≠ j ∧ ((![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ) t).testBit ((min i j).val*17+(max i j).val) = true) → (i ≠ l ∧ ((![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ) t).testBit ((min i l).val*17+(max i l).val) = true) → ¬ (j ≠ l ∧ ((![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ) t).testBit ((min j l).val*17+(max j l).val) = true) := by decide
    exact common C (fun t => triangleFree _ (tr t)) c G gc (by rw [ge]; exact Nat.lt_succ_self _)
  · obtain ⟨r,m,tr,lim⟩ := d 0
    exact common _ tr lim G gc ((Nat.lt_succ_self 33).trans_eq ge.symm)
  · obtain ⟨r,m,tr,lim⟩ := d 1
    exact common _ tr lim G gc ((Nat.lt_succ_self 41).trans_eq ge.symm)
  · obtain ⟨r,m,tr,lim⟩ := d 2
    exact common _ tr lim G gc ((Nat.lt_succ_self 49).trans_eq ge.symm)
end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1
