import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1

/-! Sparse thresholds for triangle-good connected graphs. The upper bound at
every order uses an explicit obstruction. Each assignment of a source
vertex to a twin class consumes one occurrence of that class. The lower
bounds are reduced to coverings by dense spanning templates. The templates
of orders ten through twelve are the covering lists drawn on pp. 18–19 of
Brandt, Brinkmann and Harmuth (1998). -/
namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1
open SimpleGraph Finset


/-- Cover every connected sparse graph of the specified size by one
of the tabulated dense graphs on the same vertices. -/
def H1 : Prop := ∀ k : Fin 6,
  let n := k.val+7
  let q := (![11,11,16,18,23,23] : Fin 6 → ℕ) k
  let masks := (![[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 6 → List ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q →
    ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val) = false

/-- Embed each of the explicitly listed dense templates in the complement
of every triangle-free host of the critical order. -/
def H2 : Prop := ∀ k : Fin 9,
  let n := k.val+4
  let masks := (![[2048],[540672],[541065248],[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 9 → List ℕ) k
  ∀ m ∈ masks, ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ e : Fin n ↪ Fin (2*n-1), ∀ i j, i≠j → m.testBit ((min (i) (j)).val*n+(max (i) (j)).val) = false → ¬ C.Adj (e i) (e j)

lemma eraseTail {A : Type} [DecidableEq A] {x : A} {xs ys : List A}
    (h : (x::xs).Subperm ys) : xs.Subperm (ys.erase x) := by
  apply List.subperm_iff_count.mpr
  intro a
  have ha := List.subperm_iff_count.mp h a
  by_cases he : a = x
  · subst a
    simp only [List.count_cons_self,List.count_erase_self] at *
    omega
  · simpa [List.count_cons,List.count_erase_of_ne he,he,Ne.symm he] using ha

theorem search_complete {V A : Type} [DecidableEq A] (edge : V → V → Bool) (red : A → A → Bool)
    (colors : List A) (allColors : ∀ c, c ∈ colors) (label : V → A)
    (valid : ∀ v w, edge v w = true → red (label v) (label w) = false)
    (order : List V) (used : List (V × A)) (supply : List A)
    (prior : ∀ p ∈ used, p.2=label p.1) (enough : (order.map label).Subperm supply) :
    (order.foldr (fun v cont seen stock => colors.any (fun c =>
      stock.contains c && (seen.all fun p => !(edge v p.1 && red c p.2)) &&
        cont ((v,c)::seen) (stock.erase c))) (fun _ _ => true)) used supply=true := by
  induction order generalizing used supply with
  | nil => rfl
  | cons v vs ih =>
    apply List.any_eq_true.mpr
    refine ⟨label v,allColors _,?_⟩
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_,?_⟩,?_⟩
    · apply List.contains_iff_mem.mpr
      obtain ⟨l,hp,hs⟩ := enough
      exact hs.subset (hp.mem_iff.mpr (by simp))
    · apply List.all_eq_true.mpr
      intro p hp
      rw [prior p hp]
      cases he : edge v p.1 with
      | false => simp
      | true => simp [valid _ _ he]
    · apply ih _ _ _ (eraseTail enough)
      intro p hp
      rcases List.mem_cons.mp hp with rfl|h
      · rfl
      · exact prior p h
theorem excludes {n h t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : SimpleGraph (Fin t)) [DecidableRel R.Adj] (group : Fin h → Fin t)
    (check : ((List.finRange n).foldr (fun v cont seen stock => (List.finRange t).any (fun c =>
      stock.contains c && (seen.all fun p => !(decide (G.Adj v p.1) && decide (R.Adj c p.2))) &&
        cont ((v,c)::seen) (stock.erase c))) (fun _ _ => true)) ([] : List (Fin n × Fin t)) ((List.finRange h).map group) = false) :
    ¬ G ⊑ (R.comap group)ᶜ := by
  rintro ⟨e⟩
  let label (i : Fin n) := group (e i)
  have enoughVertices : ((List.finRange n).map (fun v => e v)).Subperm (List.finRange h) :=
    ((List.nodup_finRange _).map e.injective).subperm (by intro x _; simp)
  obtain ⟨l,hp,hs⟩ := enoughVertices
  have en : ((List.finRange n).map label).Subperm ((List.finRange h).map group) := by
    refine ⟨l.map group,?_,hs.map group⟩
    simpa [List.map_map,label,Function.comp_def] using hp.map group
  have ok := search_complete (fun i j => decide (G.Adj i j)) (fun i j => decide (R.Adj i j))
    (List.finRange t) (by simp) label (by
      intro i j hij
      apply decide_eq_false
      exact (e.toHom.map_rel' (of_decide_eq_true hij)).2) (List.finRange n) [] _ (by simp) en
  exact Bool.noConfusion (ok.symm.trans check)

lemma forces_copy {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (good : Erdos1182.IsTriangleGood G)
    (C : SimpleGraph (Fin (2*n-1))) (ht : C.CliqueFree 3) : G ⊑ Cᶜ := by
  classical
  let S : Set ℕ := {m | ∀ B : SimpleGraph (Fin m), (⊤ : SimpleGraph (Fin 3)) ⊑ B ∨ G ⊑ Bᶜ}
  change sInf S = 2*n-1 at good
  have ne : S.Nonempty := by
    by_contra hs
    rw [Set.not_nonempty_iff_eq_empty.mp hs,Nat.sInf_empty] at good
    omega
  have hit := Nat.sInf_mem ne
  rw [good] at hit
  exact (hit C).resolve_left (by simpa only [← completeGraph_eq_top,← not_cliqueFree_iff_top_isContained] using not_not_intro ht)

lemma blocks_upper {n q : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (gc : G.Connected)
    (size : G.edgeSet.ncard=q+1) (C : SimpleGraph (Fin (2*n-1))) (tr : C.CliqueFree 3)
    (no : ¬ G ⊑ Cᶜ) : Erdos1182.F n ≤ q := by
  unfold Erdos1182.F
  apply csSup_le'
  rintro z ⟨_,hz⟩
  by_contra! hlt
  exact no (forces_copy hn G (hz G gc (by omega)) C tr)

lemma triangle_free_comap {h t : ℕ} (R : SimpleGraph (Fin t)) (group : Fin h → Fin t)
    (tr : ∀ i j k, R.Adj i j → R.Adj i k → ¬R.Adj j k) : (R.comap group).CliqueFree 3 := by
  intro S hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact tr (group a) (group b) (group c) hab hac hbc

lemma radius {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (ball : ∀ w, v=w ∨ G.Adj v w ∨ ∃ k, G.Adj v k ∧ G.Adj k w) : G.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
  refine ⟨v,?_⟩
  intro w
  rcases ball w with h|a|⟨k,b,c⟩
  · subst w; exact Reachable.refl _
  · exact a.reachable
  · exact b.reachable.trans c.reachable

lemma edgeNumber {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.edgeSet.ncard=G.edgeFinset.card := Set.ncard_eq_toFinset_card' _

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper3 : Erdos1182.F 3 ≤ 2 := by
  let G : SimpleGraph (Fin 3) := 
    { Adj := fun i j => i≠j ∧ (38 : ℕ).testBit ((min i j).val*3+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 5 → Fin 5 := ![0, 1, 2, 3, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper4 : Erdos1182.F 4 ≤ 5 := by
  let G : SimpleGraph (Fin 4) := 
    { Adj := fun i j => i≠j ∧ (2254 : ℕ).testBit ((min i j).val*4+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 7 → Fin 5 := ![0, 1, 2, 3, 3, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper5 : Erdos1182.F 5 ≤ 7 := by
  let G : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (533150 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 9 → Fin 5 := ![0, 1, 1, 2, 2, 3, 3, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper6 : Erdos1182.F 6 ≤ 8 := by
  let G : SimpleGraph (Fin 6) := 
    { Adj := fun i j => i≠j ∧ (545360154 : ℕ).testBit ((min i j).val*6+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 11) := 
    { Adj := fun i j => i≠j ∧ (649195563651347488628968623064480 : ℕ).testBit ((min i j).val*11+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 11 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper7 : Erdos1182.F 7 ≤ 11 := by
  let G : SimpleGraph (Fin 7) := 
    { Adj := fun i j => i≠j ∧ (235277854 : ℕ).testBit ((min i j).val*7+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 13) := 
    { Adj := fun i j => i≠j ∧ (45674713929892103111903021731849029443312095648 : ℕ).testBit ((min i j).val*13+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 13 → Fin 13 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  apply blocks_upper (by decide) G (radius G 3 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper8 : Erdos1182.F 8 ≤ 11 := by
  let G : SimpleGraph (Fin 8) := 
    { Adj := fun i j => i≠j ∧ (36099853235266634 : ℕ).testBit ((min i j).val*8+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 15 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper9 : Erdos1182.F 9 ≤ 16 := by
  let G : SimpleGraph (Fin 9) := 
    { Adj := fun i j => i≠j ∧ (2363493607849974646870 : ℕ).testBit ((min i j).val*9+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 17 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper10 : Erdos1182.F 10 ≤ 18 := by
  let G : SimpleGraph (Fin 10) := 
    { Adj := fun i j => i≠j ∧ (619272841609893681163702414 : ℕ).testBit ((min i j).val*10+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 19 → Fin 5 := ![0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper11 : Erdos1182.F 11 ≤ 23 := by
  let G : SimpleGraph (Fin 11) := 
    { Adj := fun i j => i≠j ∧ (649354097366536385312813346898726 : ℕ).testBit ((min i j).val*11+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 21 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem upper12 : Erdos1182.F 12 ≤ 23 := by
  let G : SimpleGraph (Fin 12) := 
    { Adj := fun i j => i≠j ∧ (2722923671064814990385729468407340106006 : ℕ).testBit ((min i j).val*12+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (532626 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let group : Fin 23 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4]
  apply blocks_upper (by decide) G (radius G 0 (by decide)) (by rw [edgeNumber]; decide) (R.comap group)
    (triangle_free_comap R group (by decide))
  apply excludes G R group
  decide +kernel

theorem cover {n q : ℕ} [NeZero n] (T : SimpleGraph (Fin n)) [DecidableRel T.Adj] (place : ℕ → Fin n → Fin n)
    (rows : List (ℕ × List (Sym2 (Fin n)))) (maps : rows.all (fun r => decide (Function.Injective (place r.1) ∧ ∀ i j : Fin n, i≠j → ¬ T.Adj (place r.1 i) (place r.1 j) → s(i,j) ∈ r.2))=true)
    (sets : (((⊤ : SimpleGraph (Fin n)).edgeFinset.powersetCard q).filter
      (fun S => !(rows.any (fun r => r.2.all (fun e => decide (e ∉ S)))))) = ∅)
    (hq : q≤n.choose 2) (G : SimpleGraph (Fin n)) (small : G.edgeSet.ncard≤q) : G ⊑ T := by
  classical
  have ecount : G.edgeSet.ncard=G.edgeFinset.card := Set.ncard_eq_toFinset_card' _
  obtain ⟨W,hGW,hWT,hw⟩ := Finset.exists_subsuperset_card_eq (edgeFinset_mono (show G ≤ ⊤ from le_top))
    (ecount ▸ small) (by rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin]; exact hq)
  have yes : rows.any (fun r => r.2.all (fun e => decide (e ∉ W))) = true := by
    by_contra! no
    have mem : W ∈ (((⊤ : SimpleGraph (Fin n)).edgeFinset.powersetCard q).filter
        (fun S => !(rows.any (fun r => r.2.all (fun e => decide (e ∉ S)))))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hWT,hw⟩,by simpa using no⟩
    rw [sets] at mem
    simp at mem
  obtain ⟨r,hr,hdis⟩ := List.any_eq_true.mp yes
  have ok := of_decide_eq_true (List.all_eq_true.mp maps r hr)
  refine ⟨⟨⟨place r.1,?_⟩,ok.1⟩⟩
  intro i j h
  by_contra hh
  exact (of_decide_eq_true (List.all_eq_true.mp hdis _ (ok.2 i j h.ne hh))) (hGW (SimpleGraph.mem_edgeFinset.mpr h))


set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem placed4 (G : SimpleGraph (Fin 4)) (h : G.edgeSet.ncard ≤ 5) :
    ∃ e : Fin 4 ↪ Fin 4, ∀ i j, G.Adj i j → (2048 : ℕ).testBit ((min (e i) (e j)).val*4+(max (e i) (e j)).val)=false := by
  let R : SimpleGraph (Fin 4) := 
    { Adj := fun i j => i≠j ∧ (2048 : ℕ).testBit ((min i j).val*4+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let place (code : ℕ) (i : Fin 4) := Fin.ofNat 4 ((code >>> (4*i.val))%16)
  let rows : List (ℕ × List (Sym2 (Fin 4))) := [(12816,[s(2,3)]),
  (12576,[s(1,3)]),
  (4896,[s(1,2)]),
  (12546,[s(0,3)]),
  (4866,[s(0,2)]),
  (4146,[s(0,1)])]
  obtain ⟨f⟩ := cover Rᶜ place rows (by decide +kernel) (by decide +kernel) (by decide) G h
  refine ⟨f.toEmbedding,fun i j hij => ?_⟩
  have hno := (f.toHom.map_rel' hij).2
  exact Bool.eq_false_iff.mpr (fun he => hno ⟨f.injective.ne hij.ne,he⟩)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem placed5 (G : SimpleGraph (Fin 5)) (h : G.edgeSet.ncard ≤ 7) :
    ∃ e : Fin 5 ↪ Fin 5, ∀ i j, G.Adj i j → (540672 : ℕ).testBit ((min (e i) (e j)).val*5+(max (e i) (e j)).val)=false := by
  let R : SimpleGraph (Fin 5) := 
    { Adj := fun i j => i≠j ∧ (540672 : ℕ).testBit ((min i j).val*5+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let place (code : ℕ) (i : Fin 5) := Fin.ofNat 5 ((code >>> (4*i.val))%16)
  let rows : List (ℕ × List (Sym2 (Fin 5))) := [(274960,[s(2,4),s(3,4)]),
  (82720,[s(1,3),s(2,3)]),
  (201280,[s(1,2),s(1,4)]),
  (205060,[s(0,3),s(0,4)]),
  (66340,[s(0,1),s(0,2)]),
  (213520,[s(2,3),s(3,4)]),
  (205840,[s(2,3),s(2,4)]),
  (213280,[s(1,3),s(3,4)]),
  (266290,[s(0,4),s(1,4)]),
  (66610,[s(0,2),s(1,2)]),
  (66370,[s(0,1),s(1,2)]),
  (81970,[s(0,3),s(1,3)]),
  (200770,[s(0,1),s(1,4)]),
  (213250,[s(0,3),s(3,4)]),
  (267010,[s(0,4),s(2,4)]),
  (82690,[s(0,3),s(2,3)]),
  (267040,[s(1,4),s(2,4)]),
  (274690,[s(0,4),s(3,4)]),
  (201760,[s(1,2),s(2,4)]),
  (201730,[s(0,2),s(2,4)]),
  (78850,[s(0,2),s(2,3)]),
  (77890,[s(0,1),s(1,3)]),
  (274720,[s(1,4),s(3,4)]),
  (78880,[s(1,2),s(2,3)]),
  (205120,[s(1,3),s(1,4)]),
  (78400,[s(1,2),s(1,3)]),
  (201220,[s(0,2),s(0,4)]),
  (78340,[s(0,2),s(0,3)]),
  (200740,[s(0,1),s(0,4)]),
  (77860,[s(0,1),s(0,3)])]
  obtain ⟨f⟩ := cover Rᶜ place rows (by decide +kernel) (by decide +kernel) (by decide) G h
  refine ⟨f.toEmbedding,fun i j hij => ?_⟩
  have hno := (f.toHom.map_rel' hij).2
  exact Bool.eq_false_iff.mpr (fun he => hno ⟨f.injective.ne hij.ne,he⟩)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem placed6 (G : SimpleGraph (Fin 6)) (h : G.edgeSet.ncard ≤ 8) :
    ∃ e : Fin 6 ↪ Fin 6, ∀ i j, G.Adj i j → (541065248 : ℕ).testBit ((min (e i) (e j)).val*6+(max (e i) (e j)).val)=false := by
  let R : SimpleGraph (Fin 6) := 
    { Adj := fun i j => i≠j ∧ (541065248 : ℕ).testBit ((min i j).val*6+(max i j).val)=true
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel R.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  let place (code : ℕ) (i : Fin 6) := Fin.ofNat 6 ((code >>> (4*i.val))%16)
  let rows : List (ℕ × List (Sym2 (Fin 6))) := [(5517840,[s(0,5),s(3,4),s(4,5)]),
  (4346640,[s(0,3),s(2,5),s(3,5)]),
  (2438160,[s(0,4),s(2,3),s(2,4)]),
  (3282240,[s(0,2),s(1,2),s(1,5)]),
  (2437440,[s(0,4),s(1,3),s(1,4)]),
  (2364240,[s(0,1),s(1,4),s(2,4)]),
  (2179920,[s(0,1),s(1,3),s(2,3)]),
  (4400400,[s(0,2),s(2,5),s(4,5)]),
  (5456385,[s(1,5),s(3,4),s(3,5)]),
  (5379120,[s(0,5),s(1,2),s(2,5)]),
  (5386500,[s(0,3),s(0,5),s(1,5)]),
  (2118420,[s(0,2),s(0,3),s(3,4)]),
  (2295105,[s(1,2),s(1,4),s(2,3)]),
  (336180,[s(0,1),s(0,4),s(4,5)]),
  (5374740,[s(0,2),s(0,5),s(3,5)]),
  (2110785,[s(1,2),s(1,3),s(2,4)]),
  (5448705,[s(1,5),s(2,4),s(2,5)]),
  (4534785,[s(1,4),s(3,5),s(4,5)]),
  (3167265,[s(2,3),s(2,5),s(3,4)]),
  (2175060,[s(0,1),s(0,3),s(1,2)]),
  (5255745,[s(1,3),s(1,5),s(4,5)]),
  (2425140,[s(0,1),s(0,4),s(3,4)]),
  (340500,[s(0,3),s(0,4),s(4,5)]),
  (341025,[s(2,3),s(2,4),s(4,5)]),
  (206100,[s(0,2),s(0,4),s(2,5)]),
  (3297540,[s(0,3),s(0,5),s(1,3)]),
  (4338000,[s(0,1),s(1,5),s(3,5)]),
  (2425665,[s(1,2),s(1,4),s(3,4)]),
  (2180400,[s(0,2),s(1,3),s(2,3)]),
  (3489825,[s(2,4),s(3,4),s(3,5)]),
  (5448000,[s(0,5),s(1,4),s(1,5)]),
  (2109780,[s(0,1),s(0,3),s(1,4)]),
  (3294465,[s(1,2),s(2,3),s(3,5)]),
  (2163540,[s(0,1),s(0,2),s(1,3)]),
  (2364720,[s(0,2),s(1,4),s(2,4)]),
  (4346625,[s(1,3),s(2,5),s(3,5)]),
  (3297600,[s(0,3),s(1,3),s(1,5)]),
  (2437380,[s(0,3),s(0,4),s(1,4)]),
  (2311440,[s(0,2),s(2,3),s(3,4)]),
  (5447940,[s(0,4),s(0,5),s(1,5)]),
  (3428865,[s(1,3),s(3,4),s(4,5)]),
  (5387280,[s(0,5),s(2,3),s(2,5)]),
  (5378880,[s(0,5),s(1,2),s(1,5)])]
  obtain ⟨f⟩ := cover Rᶜ place rows (by decide +kernel) (by decide +kernel) (by decide) G h
  refine ⟨f.toEmbedding,fun i j hij => ?_⟩
  have hno := (f.toHom.map_rel' hij).2
  exact Bool.eq_false_iff.mpr (fun he => hno ⟨f.injective.ne hij.ne,he⟩)

lemma sufficient {n : ℕ} (hn : 2≤n) (G : SimpleGraph (Fin n)) (gc : G.Connected)
    (all : ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 → G ⊑ Cᶜ) : Erdos1182.IsTriangleGood G := by
  classical
  let S : Set ℕ := {m | ∀ C : SimpleGraph (Fin m), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ G ⊑ Cᶜ}
  change sInf S=2*n-1
  have hm : 2*n-1 ∈ S := by
    intro C
    by_cases ht : C.CliqueFree 3
    · exact Or.inr (all C ht)
    · exact Or.inl (by simpa only [completeGraph_eq_top] using (not_cliqueFree_iff_top_isContained 3).mp ht)
  apply le_antisymm (Nat.sInf_le hm)
  apply le_csInf ⟨_,hm⟩
  intro m hh
  by_contra! hl
  obtain ⟨C,ht,no⟩ := OMA.tree_ramsey_lower_witness n m hn hl G gc
  exact (hh C).elim ht no

lemma enlarge {n q : ℕ} (G : SimpleGraph (Fin n)) (lo : G.edgeSet.ncard≤q) (hi : q≤n.choose 2) :
    ∃ D : SimpleGraph (Fin n), G≤D ∧ D.edgeSet.ncard=q := by
  classical
  obtain ⟨W,hG,hT,hq⟩ := Finset.exists_subsuperset_card_eq (edgeFinset_mono (show G≤⊤ from le_top))
    ((Set.ncard_eq_toFinset_card' _ : G.edgeSet.ncard=G.edgeFinset.card) ▸ lo)
    (by rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin]; exact hi)
  let D := fromEdgeSet (W : Set (Sym2 (Fin n)))
  have eD : D.edgeSet = (W : Set (Sym2 (Fin n))) := by
    rw [show D.edgeSet=_ from edgeSet_fromEdgeSet (W : Set (Sym2 (Fin n)))]
    ext e
    refine ⟨And.left,fun he => ⟨he,?_⟩⟩
    exact (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hT he))
  refine ⟨D,edgeSet_subset_edgeSet.mp ?_,by simpa [eD] using hq⟩
  rw [eD]
  exact fun e he => hG (SimpleGraph.mem_edgeFinset.mpr he)

lemma lower (a : H1) (b : H2) (k : Fin 9) :
    (![5,7,8,11,11,16,18,23,23] : Fin 9 → ℕ) k ≤ Erdos1182.F (k.val+4) := by
  let n := k.val+4
  let q := (![5,7,8,11,11,16,18,23,23] : Fin 9 → ℕ) k
  let masks := (![[2048],[540672],[541065248],[8757838336,33688088],[36169948434793600,70781333153792],[2251801971660822],[618970019714747783169716278,72057645653176374],[158495020111019088292975255562,9444734656926049394710],[14855280693082744087392632874,4951760378943817067685560330,604831853708092460023990,40564825856395375891792278241302]] : Fin 9 → List ℕ) k
  have hi : q≤n.choose 2 := by fin_cases k <;> decide
  apply Erdos1182.le_F hi
  intro G gc ge
  apply sufficient (by dsimp [n]; omega) G gc
  intro C ht
  have placement : ∃ m ∈ masks, ∃ e : Fin n ↪ Fin n, ∀ i j, G.Adj i j → m.testBit ((min (e i) (e j)).val*n+(max (e i) (e j)).val)=false := by
    fin_cases k
    · exact ⟨2048,by decide,placed4 G ge⟩
    · exact ⟨540672,by decide,placed5 G ge⟩
    · exact ⟨541065248,by decide,placed6 G ge⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 0 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 1 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 2 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 3 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 4 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
    · obtain ⟨D,sub,eq⟩ := enlarge G ge hi
      obtain ⟨m,hm,e,he⟩ := a 5 D (gc.mono sub) eq
      exact ⟨m,hm,e,fun i j h => he i j (sub h)⟩
  obtain ⟨m,hm,e,he⟩ := placement
  obtain ⟨f,hf⟩ := b k m hm C ht
  refine ⟨⟨⟨fun i => f (e i),?_⟩,f.injective.comp e.injective⟩⟩
  intro i j hij
  exact ⟨(f.injective.comp e.injective).ne hij.ne,hf _ _ (e.injective.ne hij.ne) (he _ _ hij)⟩

theorem main : H1 → H2 → OMA.R_Erdos1182_erdos_1182_variants_small_values_R1.H1 := by
  intro a b
  exact ⟨upper3,le_antisymm upper4 (lower a b 0),le_antisymm upper5 (lower a b 1),le_antisymm upper6 (lower a b 2),le_antisymm upper7 (lower a b 3),le_antisymm upper8 (lower a b 4),le_antisymm upper9 (lower a b 5),le_antisymm upper10 (lower a b 6),le_antisymm upper11 (lower a b 7),le_antisymm upper12 (lower a b 8)⟩
end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1
