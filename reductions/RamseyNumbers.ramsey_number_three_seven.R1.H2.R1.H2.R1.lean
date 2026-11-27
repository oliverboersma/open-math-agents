import OMAReductions.R_RamseyNumbers_ramsey_number_three_seven_R1_H2_R1

/-! A finite reduction of the regular R(3,7) case. The non-neighbours of a
root span at most 33 edges on 16 vertices. Enumerating this smaller class
and certifying a fractional packing obstruction are independent tasks.
The weighted argument comes from counting which contact sets miss an
independent five-set. The double counting of edges adapts @TheWaler's
earlier reduction for R(3,9). -/
open SimpleGraph
namespace OMA.R_RamseyNumbers_ramsey_number_three_seven_R1_H2_R1_H2_R1

private def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega

theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a + 2 ^ a.length * bits b := by
  induction a with
  | nil => simp [bits]
  | cons c a ih => simp [bits, ih, pow_succ]; ring

theorem bits_replicate_false (n : Nat) : bits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, ih]

theorem bits_replicate_true (n : Nat) : bits (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, pow_succ]; omega

private def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs

private def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss

private def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)

theorem contacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (front base : List V) (hi : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y) :
    encode G (front ++ base) =
      shifted (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) ++ encode G base := by
  induction front with
  | nil => rfl
  | cons a as ih =>
    have nh (x) (hx : x∈as) := hi a (by simp) x (by simp [hx])
    have nils : as.map (fun x => decide (G.Adj a x)) = List.replicate as.length false := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [nh b hb]⟩
    simp [encode, shifted, bits_append, nils, bits_replicate_false,
      ih (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

theorem root_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (front base : List V) (hfront : ∀ x∈front, G.Adj r x)
    (hbase : ∀ x∈base, ¬ G.Adj r x) (ht : G.CliqueFree 3) :
    encode G (r::front++base) = attach
      (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) (encode G base) := by
  have hf : front.map (fun x => decide (G.Adj r x)) = List.replicate front.length true := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hfront b hb]⟩
  have hb : base.map (fun x => decide (G.Adj r x)) = List.replicate base.length false := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hbase b hb]⟩
  have hi (x) (hx : x ∈ front) (y) (hy : y ∈ front) (h : G.Adj x y) : False :=
    G.isIndepSet_neighborSet_of_triangleFree ht r (hfront x hx) (hfront y hy) h.ne h
  simp [encode, attach, bits_append, hf, hb, bits_replicate_false, contacts G front base hi]
  have := bits_replicate_true front.length
  omega


private def mark {V : Type*} [DecidableEq V] (vs : List V) (s : Finset V) : Nat :=
  bits (vs.map fun x => decide (x ∈ s))

theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]

theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]

private def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
private def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)

private def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

theorem mark_congr {V : Type*} [DecidableEq V] (vs : List V) (s t : Finset V)
    (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun x hx => by simp only [h x hx])

theorem inds_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ inds (encode G vs)) :
    ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
  induction vs generalizing p with
  | nil =>
    simp [encode,inds] at hp
    exact ⟨∅,by simp,by simp,by simp [hp,mark,bits]⟩
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits,ha]⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
      have hi : Gᶜ.IsClique (insert a S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
        refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
        · exact fun e => ha (e ▸ hx)
        · intro adj
          have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
          exact (of_decide_eq_false this) hx
      have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
      refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
      simp [ind1,mark,bits,Finset.card_insert_of_notMem ha] at hm ⊢
      omega

theorem inds_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) (S : Finset V) (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
    (mark vs S,S.card) ∈ inds (encode G vs) := by
  induction vs generalizing S with
  | nil =>
    have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [e,encode,inds,mark,bits]
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter]
    by_cases ha : a ∈ S
    · let T := S.erase a
      have hT : T ⊆ l.toFinset := by
        intro x hx
        have m := Finset.mem_erase.mp hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
        exact List.mem_toFinset.mpr (h.resolve_left m.1)
      have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
      have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
      have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
      right
      refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
      · apply beq_iff_eq.mpr
        apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
        intro x _ hx
        apply decide_eq_false
        intro hm
        have hmem := Finset.mem_erase.mp hm
        exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
      · simp [ind1,mark,bits,ha,hcard] at hmark ⊢
        omega
    · have hT : S ⊆ l.toFinset := by
        intro x hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
        exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
      exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits,ha]⟩


private def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)

private def bump (m : Nat) : List Nat → List Nat
  | [] => []
  | x::xs => (x+m%2)::bump (m/2) xs

private def degrees : List Nat → List Nat
  | [] => []
  | m::ms => countBits ms.length m :: bump m (degrees ms)

private def sizeAt {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (x : V) :=
  (vs.filter fun y => decide (G.Adj x y)).length

theorem half_step (x : Nat) : (2*x+1)/2=x := by omega

theorem count_map {V : Type*} (vs : List V) (f : V → Bool) :
    countBits vs.length (bits (vs.map f)) = (vs.filter f).length := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [countBits,bits,ha,ih,half_step]
    omega

theorem bump_map {V : Type*} (vs : List V) (f : V → Bool) (d : V → Nat) :
    bump (bits (vs.map f)) (vs.map d) = vs.map (fun x => d x + (f x).toNat) := by
  induction vs with
  | nil => rfl
  | cons a l ih => cases ha : f a <;> simp [bump,bits,ha,ih,half_step]

theorem encode_length {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (encode G vs).length=vs.length := by induction vs with | nil => rfl | cons a as ih => simp [encode,ih]

theorem degrees_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    degrees (encode G vs) = vs.map (sizeAt G vs) := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [encode,degrees,encode_length,count_map,ih,bump_map,List.map_cons,List.cons.injEq]
    refine ⟨by simp [sizeAt], List.map_congr_left ?_⟩
    intro x _
    by_cases h : G.Adj a x <;> simp [sizeAt,h,G.adj_comm x a]

theorem sizeAt_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {vs : List V} (hn : vs.Nodup) (x : V) :
    sizeAt G vs x = (vs.toFinset.filter (G.Adj x)).card := by
  have h := List.toFinset_filter vs (fun y => decide (G.Adj x y))
  simp only [decide_eq_true_eq] at h
  rw [← h, List.toFinset_card_of_nodup (hn.filter _)]
  rfl


private def Small {V : Type*} (G : SimpleGraph V) (A : Finset V) (k : Nat) :=
  ∀ I ⊆ A, Gᶜ.IsClique (I : Set V) → I.card < k

theorem row_mark {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (base : List V) (x : V) :
    bits (base.map fun y => decide (G.Adj x y)) = mark base (base.toFinset.filter (G.Adj x)) := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun y hy => by simp [hy])

theorem neighbors_small {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (x : V) :
    Gᶜ.IsClique ((A.filter (G.Adj x) : Finset V) : Set V) := by
  rw [G.isClique_compl]
  intro y hy z hz hn
  exact G.isIndepSet_neighborSet_of_triangleFree ht x (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 hn

theorem degrees_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (k : Nat) (hs : Small G A k)
    (l : List V) (hn : l.Nodup) (hsub : l.toFinset ⊆ A) :
    (degrees (encode G l)).all (· < k) = true := by
  rw [degrees_encode, List.all_eq_true]
  intro y hy
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
  simp only [decide_eq_true_eq, sizeAt_finset G hn]
  exact hs _ ((Finset.filter_subset _ _).trans hsub) (neighbors_small G ht _ x)

private def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k

theorem ok_contacts {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : Nat) (hs : Small G A k) (front base : List V)
    (hn : (front++base).Nodup) (hsub : (front++base).toFinset ⊆ A)
    (hi : Gᶜ.IsClique (front.toFinset : Set V)) :
    okContacts k (inds (encode G base)) (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) := by
  rw [okContacts,List.all_eq_true]
  intro q hq
  obtain ⟨hh,hb,hd⟩ := List.nodup_append.mp hn
  obtain ⟨S,hS,hI,rfl⟩ := inds_sound G base hb hq
  let pred (v : V) : Bool := bits (base.map fun y => decide (G.Adj v y)) &&& mark base S == 0
  let F := front.filter pred
  have hF (x) (hx : x∈F) : x∈front := (List.mem_filter.mp hx).1
  have sep (x) (hx : x∈F) (y) (hy : y∈S) : Gᶜ.Adj x y := by
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_toFinset.mp (hS hy)
    have neq : x ≠ y := hd x hx'.1 y hy'
    exact ⟨neq,fun ha => by
      have e := (and_mask base (fun z => decide (G.Adj x z)) (fun z => decide (z ∈ S))).mp
        (beq_iff_eq.mp hx'.2) y hy' (by simpa using ha)
      exact of_decide_eq_false e hy⟩
  have sub : F.toFinset ∪ S ⊆ A := by
    apply Finset.union_subset
    · exact fun x hx => hsub (by simp [hF x (List.mem_toFinset.mp hx)])
    · exact fun x hx => hsub (by simp [List.mem_toFinset.mp (hS hx)])
  have together : Gᶜ.IsClique ((F.toFinset ∪ S : Finset V) : Set V) := by
    rw [Finset.coe_union, SimpleGraph.IsClique, Set.pairwise_union]
    refine ⟨hi.subset ?_,hI,?_⟩
    · exact fun x hx => List.mem_toFinset.mpr (hF x (List.mem_toFinset.mp hx))
    · intro x hx y hy _
      exact ⟨sep x (List.mem_toFinset.mp hx) y hy,(sep x (List.mem_toFinset.mp hx) y hy).symm⟩
  have dis : Disjoint F.toFinset S := Finset.disjoint_left.mpr fun x hx hy =>
    (sep x (List.mem_toFinset.mp hx) x hy).ne rfl
  have w := hs _ sub together
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup (hh.filter _)] at w
  simp only [decide_eq_true_eq,List.filter_map,List.length_map]
  change S.card + F.length < k
  simpa only [F, Nat.add_comm S.card] using w


private def contactsOf {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (base front : List V) :=
  front.map fun x => bits (base.map fun y => decide (G.Adj x y))


theorem sorted_neigh {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (base : List V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset=N ∧ (contactsOf G base l).Pairwise (·≤·) := by
  let key (x : V) := bits (base.map fun y => decide (G.Adj x y))
  let ord (a b : V) := decide (key a ≤ key b)
  let l := N.toList.mergeSort ord
  have h := List.mergeSort_perm N.toList ord
  refine ⟨l,h.nodup_iff.mpr N.nodup_toList,?_,?_⟩
  · ext x
    simp [l]
  · have htr (a b c) : ord a b → ord b c → ord a c := by simp only [ord,decide_eq_true_eq]; omega
    have htot (a b) : ord a b || ord b a := by simp [ord,le_total]
    have sort_ := List.pairwise_mergeSort htr htot N.toList
    apply List.pairwise_map.mpr
    simpa only [ord,decide_eq_true_eq] using sort_


private def fives (b : List Nat) := ((inds b).filter (fun p=>p.2==5)).map Prod.fst
private def score (W : List (Nat × Nat)) (x : Nat) := ((W.filter (fun w => x &&& w.1 == 0)).map Prod.snd).sum
private def weightCheck (b : List Nat) (W : List (Nat × Nat)) (lo : Nat) :=
  W.all (fun w=>decide (w.1∈fives b)) && (fives b).all (fun x=>decide (lo≤ score W x)) &&
    decide ((W.map Prod.snd).sum<6*lo)

theorem score_row (w : Nat × Nat) (W : List (Nat × Nat)) (cs : List Nat) :
    (cs.map (score (w::W))).sum =
    (cs.filter (fun x => x &&& w.1 == 0)).length*w.2 + (cs.map (score W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1 = 0
    · simp [score,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [score,e] at ih ⊢
      omega

theorem pack_bound (b cs : List Nat) (W : List (Nat × Nat))
    (valid : ∀ w∈W,w.1∈fives b) (good : okContacts 7 (inds b) cs=true) :
    (cs.map (score W)).sum ≤ (W.map Prod.snd).sum := by
  induction W with
  | nil =>
    have e : score [] = fun _ => 0 := rfl
    simp [e]
  | cons w W ih =>
    have sub := ih (fun q hq => valid q (.tail _ hq))
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp (valid w (.head _))
    obtain ⟨ht,sz⟩ := List.mem_filter.mp ht
    have sz' : t.2=5 := beq_iff_eq.mp sz
    have n := of_decide_eq_true (List.all_eq_true.mp good t ht)
    rw [eq,sz'] at n
    have le1 : (cs.filter (fun x => x &&& w.1 == 0)).length≤1 := by omega
    have lh := Nat.mul_le_mul_right w.2 le1
    rw [score_row]
    simp only [Nat.one_mul,List.map_cons,List.sum_cons] at lh ⊢
    omega

theorem pack_lower (cs : List Nat) (W : List (Nat × Nat)) (lo : Nat)
    (h : ∀ x∈cs,lo≤ score W x) : cs.length*lo≤(cs.map (score W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    have hh := ih (fun y hy => h y (.tail _ hy))
    have hx := h x (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons]
    omega

theorem no_packing (b cs : List Nat) (W : List (Nat × Nat)) (lo : Nat)
    (cert : weightCheck b W lo=true) (len : cs.length=6) (mem : ∀ x∈cs,x∈fives b)
    (good : okContacts 7 (inds b) cs=true) : False := by
  obtain ⟨both,total⟩ := Bool.and_eq_true_iff.mp cert
  obtain ⟨valid,each⟩ := Bool.and_eq_true_iff.mp both
  have up := pack_bound b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have low := pack_lower cs W lo (fun x hx => of_decide_eq_true (List.all_eq_true.mp each x (mem x hx)))
  rw [len] at low
  exact (Nat.not_lt_of_ge (low.trans up)) (of_decide_eq_true total)

private def atlas : List (List Nat) := [[3,2,30,15,560,388,274,146,3,2,6,3,2,2,1,0],
  [3,12,2113,15,560,388,274,146,3,2,6,3,2,2,1,0],
  [7,56,258,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,290,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,386,769,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,386,785,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,386,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1058,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1090,2177,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1090,2193,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1090,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1538,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1602,1153,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,1602,2177,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,3074,2241,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,56,3138,2177,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,516,284,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,516,284,804,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,528,1602,1169,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,528,1608,1169,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,536,1602,1153,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,536,1608,1153,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,560,290,801,7,24,130,145,3,2,6,3,2,2,1,0],
  [7,24,3074,2145,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,40,3138,2081,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,56,3074,2081,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,56,3074,2113,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,56,3138,2049,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,132,3092,2178,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,388,3076,2054,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,388,3092,2050,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,584,3136,2144,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,2056,3138,2113,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,2072,3074,2113,7,24,146,145,3,2,6,3,2,2,1,0],
  [7,536,578,1153,7,24,194,145,3,2,6,3,2,2,1,0],
  [7,4228,2308,2308,7,24,194,145,3,2,6,3,2,2,1,0],
  [15,4144,3076,2194,1170,3,2,6,3,2,6,3,2,2,1,0],
  [15,2192,2084,2180,1153,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2084,2180,1161,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2084,2180,1169,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2340,2180,1153,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,3108,2180,1153,3,2,70,3,2,6,3,2,2,1,0],
  [15,2192,2084,2082,1092,3,34,68,3,2,6,3,2,2,1,0],
  [15,2192,2084,2082,1094,3,34,68,3,2,6,3,2,2,1,0]]



theorem regular_non_neighbors (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (regular : ∀ i, G.degree i = 6) (v : Fin 23) :
    let B := Gᶜ.neighborFinset v
    B.card = 16 ∧ (∑ i ∈ B, (B.filter (G.Adj i)).card) ≤ 66 := by
  classical
  let U : Finset (Fin 23) := Finset.univ
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  change B.card = 16 ∧ _
  constructor
  · change Gᶜ.degree v = 16
    rw [G.degree_compl, Fintype.card_fin, regular]
  let W (S T : Finset (Fin 23)) := ∑ i ∈ S, ∑ j ∈ T, (if G.Adj i j then 1 else 0 : ℕ)
  have sym (S T) : W S T = W T S := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have split (S T) : W S T + W Sᶜ T = W U T := Finset.sum_add_sum_compl S _
  have total (S) : W S U = 6 * S.card := by
    have h : W S U = ∑ i ∈ S, G.degree i := by
      unfold W U
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    simpa [regular, Nat.mul_comm] using h
  have bsub : B ⊆ Nᶜ := by
    intro i h
    exact Finset.mem_compl.mpr fun hn => ((Gᶜ.mem_neighborFinset _ _).mp h).2
      ((G.mem_neighborFinset _ _).mp hn)
  have inc (S T V : Finset (Fin 23)) (h : S ⊆ T) : W S V ≤ W T V :=
    Finset.sum_le_sum_of_subset_of_nonneg h (by intros; omega)
  have hsub : W B B ≤ W Nᶜ Nᶜ :=
    (inc B Nᶜ B bsub).trans ((sym Nᶜ B) ▸ inc B Nᶜ Nᶜ bsub)
  have zero : W N N = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hh : ¬ G.Adj i j := by
      intro edge
      exact G.isIndepSet_neighborSet_of_triangleFree ht v
        ((G.mem_neighborFinset _ _).mp hi) ((G.mem_neighborFinset _ _).mp hj) edge.ne edge
    simp [hh]
  have a := split N U
  have b := split N N
  have c := split N Nᶜ
  have s1 := sym Nᶜ U
  have s2 := sym N U
  have s3 := sym Nᶜ N
  have nc : N.card = 6 := regular v
  have uc : U.card = 23 := by simp [U]
  have t1 := total U
  have t2 := total N
  have count : W B B ≤ 66 := by omega
  have eqn : W B B = ∑ i ∈ B, (B.filter (G.Adj i)).card := by
    unfold W
    exact Finset.sum_congr rfl fun i _ => Finset.sum_boole (R := ℕ) (G.Adj i) B
  exact eqn ▸ count

/-- A triangle-free graph on sixteen vertices, with no independent six-set
and at most thirty-three edges, has an ordering in the displayed catalogue. -/
def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj] (B : Finset (Fin 23)),
    B.card=16 → (∑ x∈B,(B.filter (G.Adj x)).card)≤66 → G.CliqueFree 3 →
    Small G B 6 → ∃ base : List (Fin 23),base.Nodup ∧ base.toFinset=B ∧ encode G base∈atlas

/-- In every catalogue entry the five-sets carry integer weights whose total
is strictly smaller than six times the weight missed by each five-set. -/
def H2 : Prop := ∀ b∈atlas,∃ W lo,weightCheck b W lo=true
theorem regular_absurd (class16 : H1) (noext : H2)
    (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7)
    (reg : ∀ x,G.degree x=6) (r : Fin 23)
    (count : let B := Gᶜ.neighborFinset r; B.card=16 ∧ (∑ x∈B,(B.filter (G.Adj x)).card)≤66) : False := by
  classical
  let A : Finset (Fin 23) := Finset.univ
  let N := G.neighborFinset r
  let B := Gᶜ.neighborFinset r
  have bc : B.card=16 := count.1
  have internal : (∑ x∈B,(B.filter (G.Adj x)).card)≤66 := count.2
  have hreg (x : Fin 23) : (A.filter (G.Adj x)).card=6 := by
    simpa only [A,← SimpleGraph.neighborFinset_eq_filter,SimpleGraph.card_neighborFinset_eq_degree] using reg x
  have bound : Small G A 7 := by
    intro I _ hI
    by_contra! h
    exact (hi.mono h) I ⟨hI,rfl⟩
  have rN : r∉N := by simp [N]
  have rB : r∉B := by simp [B]
  have small : Small G B 6 := by
    intro S hS hI
    have rn : r∉S := fun h => rB (hS h)
    have ii : Gᶜ.IsClique (insert r S : Finset (Fin 23)) := by
      rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
      exact ⟨hI,fun x hx => (Gᶜ.mem_neighborFinset ..).mp (hS hx)⟩
    have h := bound (insert r S) (Finset.subset_univ _) ii
    rw [Finset.card_insert_of_notMem rn] at h
    omega
  obtain ⟨base,hbn,hb,ab⟩ := class16 G B bc internal ht small
  obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
  have ha (x) (hx : x∈front) : G.Adj r x := (G.mem_neighborFinset ..).mp (show x∈N from hf ▸ List.mem_toFinset.mpr hx)
  have hnot (x) (hx : x∈base) : ¬G.Adj r x := ((Gᶜ.mem_neighborFinset ..).mp (show x∈B from hb ▸ List.mem_toFinset.mpr hx)).2
  have dl : front.length=6 := by rw [← List.toFinset_card_of_nodup hfn,hf]; exact reg r
  have nodup : (r::front++base).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · change r ∉ front++base
      rw [List.mem_append,not_or]
      exact ⟨fun h => rN (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
    · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
  have cover : (r::front++base).toFinset=A := by
    ext x
    simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,N,Finset.mem_insert,Finset.mem_union,
      SimpleGraph.mem_neighborFinset,SimpleGraph.compl_adj,A,Finset.mem_univ,iff_true]
    by_cases e : x=r <;> by_cases a : G.Adj r x <;> grind
  have hcount (x) (hx : x∈front) : 6≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < 7 := by
    have adj := ha x hx
    have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
      ext y
      simp only [A,B,Finset.mem_filter,Finset.mem_insert,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset,SimpleGraph.compl_adj]
      constructor
      · intro xy
        by_cases e : y=r
        · exact Or.inl e
        · refine Or.inr ⟨⟨Ne.symm e,fun ra => ?_⟩,xy⟩
          exact G.isIndepSet_neighborSet_of_triangleFree ht r adj ra xy.ne xy
      · rintro (rfl|⟨_,xy⟩)
        · exact adj.symm
        · exact xy
    have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
    have mm := hreg x
    rw [eq,Finset.card_insert_of_notMem rn] at mm
    rw [sizeAt_finset G hbn,hb]; omega
  let cs := contactsOf G base front
  have inc (a) (hh : a∈cs) : a∈fives (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    let S := base.toFinset.filter (G.Adj x)
    have ind := inds_complete G base hbn S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have sz := hcount x hx
    rw [sizeAt_finset G hbn] at sz
    have five : S.card=5 := by change (base.toFinset.filter (G.Adj x)).card=5; omega
    apply List.mem_map.mpr
    refine ⟨_,List.mem_filter.mpr ⟨ind,by simp [five]⟩,?_⟩
    exact (row_mark G base x).symm
  have indep : Gᶜ.IsClique (front.toFinset : Set (Fin 23)) := by
    rw [G.isClique_compl]
    intro x hx y hy e
    exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha x (List.mem_toFinset.mp hx)) (ha y (List.mem_toFinset.mp hy)) e
  have on : (front++base).toFinset⊆A := Finset.subset_univ _
  have ok := ok_contacts G A 7 bound front base (List.nodup_cons.mp nodup).2 on indep
  have len : cs.length=6 := by simp [cs,contactsOf,dl]
  obtain ⟨W,lo,cert⟩ := noext _ ab
  exact no_packing _ _ W lo cert len inc ok

theorem main : H1 → H2 → OMA.R_RamseyNumbers_ramsey_number_three_seven_R1_H2_R1.H2 := by
  intro classes weights G inst ht hi reg v
  exact (regular_absurd classes weights G ht hi reg v (regular_non_neighbors G ht reg v)).elim

end OMA.R_RamseyNumbers_ramsey_number_three_seven_R1_H2_R1_H2_R1
