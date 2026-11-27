import OMAReductions.R_AlspachConjecture_alspach_conjecture_R1

/-!
# Decompositions of complete graphs of odd order at most thirteen

At orders five, seven and nine we exhibit a decomposition for each admissible
partition. At order eleven, two complementary even subgraphs have 27 and 28
edges. Each has cycle decompositions for all partitions of its edge count
with parts between three and eleven. Thus every partition containing a
submultiset with sum 27 is covered by the union construction, leaving 61
partitions to check directly.

At order thirteen the two subgraphs are the Paley graph and its complement.
The Paley graph has vertex set ℤ/13 and edges at differences ±1, ±3 and ±4.
Scaling its vertices by two gives the complementary partition of the edges.
Both graphs realize every one of the 849 admissible partitions of 39.
Of the 52273 admissible partitions of 78, only 1097 do not split into two
halves of sum 39. For 1018 of those cases, we transfer the edges of the
triangle on 0, 1 and 3 between the two graphs. The resulting edge sets
have sizes 38 and 40. Two smaller tables give decompositions with the
necessary lengths, and one entry per case specifies a pair of table indices.
The remaining 79 cases use direct certificates.

Each hexadecimal entry lists the cycle vertices, least significant digit
first. The required lengths cut the list into cycles. The checker
constructs the closed walks, verifies vertex simplicity and length, and
tests that their pairwise disjoint edge sets have exactly the required union.
The complete enumeration sorts the requested multiset and recurses on its
first part. A bitset of subset sums implements the splitting tests. If the fixed
initial parts, either alone or together with every remaining part, have
a submultiset of sum 39, all completions use the Paley construction.

Credit: @Deldor14. The finite-order reduction is due to @mucoucah.
-/
namespace OMA.AlspachFinite

open SimpleGraph AlspachConjecture

private abbrev K (n : Nat) := completeGraph (Fin n)

private def chain {n : Nat} (a b : Fin n) : List (Fin n) → Bool
  | [] => a != b
  | x::xs => (a != x) && chain x b xs

private def trail {n : Nat} (a b : Fin n) : (l : List (Fin n)) → chain a b l = true → (K n).Walk a b
  | [], h => .cons (by simpa [chain] using h) .nil
  | x::xs, h => .cons (by simpa [chain] using (Bool.and_eq_true_iff.mp h).1)
      (trail x b xs ((Bool.and_eq_true_iff.mp h).2))

private def arcs {n : Nat} (a b : Fin n) : List (Fin n) → List (Fin n × Fin n)
  | [] => [(a,b)]
  | x::xs => (a,x)::arcs x b xs

private lemma trail_length {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).length=l.length+1 := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,ih]

private lemma trail_support {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).support=a::(l++[b]) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,ih]

private lemma trail_edges {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).edges=(arcs a b l).map (fun p => s(p.1,p.2)) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,arcs,ih]

private abbrev Code (n : Nat) := Fin n × List (Fin n)

private def good {n : Nat} (c : Code n) : Bool :=
  chain c.1 c.1 c.2 && decide ((c.2++[c.1]).Nodup) && decide (3≤c.2.length+1)

private def cyc {n : Nat} (c : Code n) (h : good c=true) : Cycle (K n) := by
  have facts := Bool.and_eq_true_iff.mp h
  have hface := Bool.and_eq_true_iff.mp facts.1
  refine ⟨c.1, trail c.1 c.1 c.2 hface.1, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,?_⟩⟩
  · apply (Walk.isPath_def _).mpr
    rw [Walk.support_tail_of_not_nil _ (by simp [← Walk.length_eq_zero_iff,trail_length]),trail_support]
    simpa using of_decide_eq_true hface.2
  · rw [trail_length]
    exact of_decide_eq_true facts.2

private lemma cyc_length {n : Nat} (c : Code n) (h : good c=true) :
    (cyc c h).length=c.2.length+1 := trail_length .. 

private lemma cyc_edges {n : Nat} (c : Code n) (h : good c=true) :
    (cyc c h).edges=(arcs c.1 c.1 c.2).map (fun p => s(p.1,p.2)) := trail_edges ..

private def key {n : Nat} (p : Fin n × Fin n) :=
  Nat.pair (min p.1.val p.2.val) (max p.1.val p.2.val)

private theorem key_iff {n : Nat} (p q : Fin n × Fin n) :
    key p=key q ↔ s(p.1,p.2)=s(q.1,q.2) := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  simp only [key,Nat.pair_eq_pair,Sym2.eq_iff,Fin.ext_iff]
  omega

private def bitmap {n : Nat} : List (Fin n × Fin n) → Nat
  | [] => 0
  | p::ps => (1 <<< key p) ||| bitmap ps

private lemma read_bitmap {n : Nat} (ps : List (Fin n × Fin n)) (q : Fin n × Fin n) :
    (bitmap ps).testBit (key q)=true ↔ s(q.1,q.2) ∈ ps.map (fun p => s(p.1,p.2)) := by
  induction ps with
  | nil => simp [bitmap]
  | cons p ps ih =>
    rw [bitmap,Nat.testBit_or,Bool.or_eq_true_iff]
    have bit : (1 <<< key p).testBit (key q) = decide (key p=key q) := by
      rw [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow]
    rw [bit, decide_eq_true_eq, key_iff,ih,List.map_cons,List.mem_cons]
    exact or_congr_left eq_comm

private def pack {n : Nat} : List (Code n) → Option Nat
  | [] => some 0
  | c::cs => do
    let rest ← pack cs
    let b := bitmap (arcs c.1 c.1 c.2)
    if good c && (b &&& rest == 0) then some (b ||| rest) else none

private lemma packed {n : Nat} (cs : List (Code n)) (k : Nat) (hc : pack cs=some k) :
    ∃ C : Multiset (Cycle (K n)), lengths C = ((cs.map fun c => c.2.length+1) : List Nat) ∧
      ∀ q : Fin n × Fin n, (C.filter fun c => s(q.1,q.2) ∈ c.edges).card =
        (k.testBit (key q)).toNat := by
  classical
  induction cs generalizing k with
  | nil =>
    have z : k=0 := by simpa [pack,eq_comm] using hc
    exact ⟨0,rfl,fun q => by simp [z]⟩
  | cons c cs ih =>
    cases h : pack cs with
    | none => simp [pack,h] at hc
    | some r =>
      let bits := bitmap (arcs c.1 c.1 c.2)
      have facts : (good c=true ∧ bits &&& r=0) ∧ bits ||| r=k := by
        simpa [pack,h,bits] using hc
      obtain ⟨⟨cgood,dis⟩,get'⟩ := facts
      have get := get'.symm
      obtain ⟨C,lens,count⟩ := ih r h
      refine ⟨cyc c cgood ::ₘ C,?_,?_⟩
      · simpa [lengths,cyc_length] using congrArg (Multiset.cons (c.2.length+1)) lens
      · intro q
        have mem : s(q.1,q.2) ∈ (cyc c cgood).edges ↔ bits.testBit (key q)=true := by
          rw [cyc_edges]; exact (read_bitmap _ _).symm
        have distinct := congrArg (fun m : Nat => m.testBit (key q)) dis
        rw [get,Nat.testBit_or]
        by_cases own : bits.testBit (key q)=true
        · have zero : r.testBit (key q)=false := by simpa [own] using distinct
          rw [Multiset.filter_cons_of_pos (p:=fun v : Cycle (K n) => s(q.1,q.2) ∈ v.edges) C (mem.mpr own),Multiset.card_cons,count]
          simp [own,zero]
        · rw [Multiset.filter_cons_of_neg (p:=fun v : Cycle (K n) => s(q.1,q.2) ∈ v.edges) C (fun e => own (mem.mp e)),count]
          simp [own]

private def full (n : Nat) := bitmap ((List.finRange n).flatMap fun a =>
  ((List.finRange n).filter (· != a)).map (fun b => (a,b)))

private lemma full_has {n : Nat} (a b : Fin n) (h : a≠b) : (full n).testBit (key (a,b))=true := by
  apply (read_bitmap _ _).mpr
  apply List.mem_map.mpr
  refine ⟨(a,b), List.mem_flatMap.mpr ⟨a, by simp, ?_⟩, rfl⟩
  exact List.mem_map.mpr ⟨b,by simp [h.symm],rfl⟩

private def digit {n : Nat} (hn : 0<n) (z : Nat) : Fin n :=
  ⟨(z%16)%n,Nat.mod_lt _ hn⟩

private def digits {n : Nat} (hn : 0<n) : Nat → Nat → List (Fin n)
  | 0,_ => []
  | k+1,z => digit hn z :: digits hn k (z >>> 4)

private lemma digits_length {n : Nat} (hn : 0<n) (k z : Nat) : (digits hn k z).length=k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp [digits,ih]

private def decode {n : Nat} (hn : 0<n) : List Nat → Nat → List (Code n)
  | [],_ => []
  | d::ds,z => (digit hn z,digits hn (d-1) (z >>> 4)) :: decode hn ds (z >>> (4*d))

private lemma decode_lengths {n : Nat} (hn : 0<n) (ds : List Nat) (z : Nat) (hd : ∀ d∈ds,0<d) :
    (decode hn ds z).map (fun c => c.2.length+1)=ds := by
  induction ds generalizing z with
  | nil => rfl
  | cons d ds ih =>
    simp only [decode,List.map_cons,digits_length]
    rw [ih _ (fun e he => hd e (List.mem_cons_of_mem _ he))]
    have := hd d (List.mem_cons_self ..)
    congr 1
    omega

private def realizes (n : Nat) (m : Multiset Nat) : Prop :=
  ∃ C : Multiset (Cycle (K n)), IsCycleDecomposition (K n) C ∧ lengths C=m

private def accept {n : Nat} (hn : 0<n) (ds : List Nat) (z : Nat) : Bool :=
  pack (decode hn ds z) == some (full n)

private theorem accept_sound {n : Nat} (hn : 0<n) (ds : List Nat) (z : Nat)
    (hd : ∀ d∈ds,0<d) (h : accept hn ds z=true) : realizes n ds := by
  classical
  obtain ⟨C,hl,hc⟩ := packed _ _ (eq_of_beq h)
  refine ⟨C,?_,hl.trans (congrArg (fun l : List Nat => (l : Multiset Nat)) (decode_lengths hn ds z hd))⟩
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have ab : a≠b := (SimpleGraph.mem_edgeFinset.mp he : (K n).Adj a b)
    simpa [full_has a b ab] using hc (a,b)

private def partitions (n : Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,t => if t=0 then [[]] else []
  | fuel+1,lo,t =>
    if t=0 then [[]] else
    (List.range (n+1)).flatMap (fun d => if lo≤d ∧ d≤t then
      (partitions n fuel d (t-d)).map (d::·) else [])

private theorem in_partitions {n lo t fuel : Nat} (l : List Nat) (hs : l.Pairwise (·≤·))
    (hr : ∀ d∈l,lo≤d ∧ d≤n) (hl : l.length≤fuel) (ht : l.sum=t) (hlo : 0<lo) :
    l ∈ partitions n fuel lo t := by
  induction fuel generalizing l lo t with
  | zero =>
    have : l=[] := List.length_eq_zero_iff.mp (by omega)
    subst l
    simp_all [partitions]
  | succ fuel ih =>
    cases l with
    | nil => simp_all [partitions]
    | cons d ds =>
      have hdl := hr d (List.mem_cons_self ..)
      have hlen : ds.length≤fuel := by simpa using hl
      have hsum : d+ds.sum=t := by simpa using ht
      have htpos : t≠0 := by omega
      rw [partitions,if_neg htpos]
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),?_⟩
      rw [if_pos (show lo≤d ∧ d≤t by omega)]
      apply List.mem_map.mpr
      obtain ⟨hbefore,hs'⟩ := List.pairwise_cons.mp hs
      exact ⟨ds,ih ds hs' (fun e he => ⟨hbefore e he,(hr e (List.mem_cons_of_mem _ he)).2⟩)
        hlen (by omega) (by omega),rfl⟩

private def bulk {n : Nat} (hn : 0<n) (front : List Nat) : List (List Nat) → List Nat → Bool
  | [],[] => true
  | d::ds,z::zs => accept hn (front.reverse++d) z && bulk hn front ds zs
  | _,_ => false

private def Verified (n : Nat) (front : List Nat) (fuel lo t : Nat) : Prop :=
  ∀ ds ∈ partitions n fuel lo t, (∀ d ∈ front.reverse++ds,0<d) →
    realizes n ((front.reverse++ds : List Nat) : Multiset Nat)

private theorem bulk_sound {n : Nat} {hn : 0<n} {front : List Nat} (ds : List (List Nat))
    (zs : List Nat) (ok : bulk hn front ds zs=true) :
    ∀ d∈ds,(∀ j∈front.reverse++d,0<j) → realizes n ((front.reverse++d : List Nat) : Multiset Nat) := by
  induction ds generalizing zs with
  | nil => simp
  | cons d ds ih =>
    cases zs with
    | nil => simp [bulk] at ok
    | cons z zs =>
      obtain ⟨h,hs⟩ := Bool.and_eq_true_iff.mp ok
      intro a ha hp
      rcases List.mem_cons.mp ha with rfl|hm
      · exact accept_sound hn _ z hp h
      · exact ih zs hs a hm hp

private theorem from_bulk {n : Nat} {hn : 0<n} {front : List Nat} {fuel lo t : Nat} (zs : List Nat)
    (ok : bulk hn front (partitions n fuel lo t) zs=true) : Verified n front fuel lo t :=
  bulk_sound _ _ ok

private theorem branch {n lo t fuel : Nat} {front : List Nat} (ht : 0<t)
    (kids : ∀ d : Nat, lo≤d → d≤n → d≤t → Verified n (d::front) fuel d (t-d)) :
    Verified n front (fuel+1) lo t := by
  intro ds hm hp
  rw [partitions,if_neg ht.ne'] at hm
  obtain ⟨d,hd,hd'⟩ := List.mem_flatMap.mp hm
  by_cases h : lo≤d ∧ d≤t
  · rw [if_pos h] at hd'
    obtain ⟨ds',hs,rfl⟩ := List.mem_map.mp hd'
    simpa using kids d h.1 (by simpa using hd) h.2 ds' hs (by simpa using hp)
  · simp [h] at hd'

private theorem no_parts {n lo t fuel : Nat} {front : List Nat} (empty : partitions n fuel lo t = []) :
    Verified n front fuel lo t := by
  intro ds h
  simp [empty] at h

private theorem start {n : Nat} (all : Verified n [] (n.choose 2) 3 (n.choose 2)) (m : Multiset Nat)
    (bound : ∀ d∈m,3≤d ∧ d≤n) (total : m.sum=n.choose 2) : realizes n m := by
  let l := m.sort (·≤·)
  have e : (l : Multiset Nat)=m := Multiset.sort_eq ..
  have ls : l.sum=n.choose 2 := by convert total using 1; exact congrArg Multiset.sum e
  have range' (d : Nat) (hd : d∈l) : 3≤d ∧ d≤n := bound d (by simpa [l] using hd)
  have length_le_sum (xs : List Nat) (pos : ∀ d∈xs,0<d) : xs.length≤xs.sum := by
    induction xs with
    | nil => simp
    | cons a as ih =>
      have h := ih (fun d hd => pos d (List.mem_cons_of_mem _ hd))
      have ha := pos a (List.mem_cons_self ..)
      simp only [List.length_cons,List.sum_cons]
      omega
  have hl := length_le_sum l (fun d hd => by have := range' d hd; omega)
  have has := in_partitions l (Multiset.pairwise_sort ..) range' (hl.trans_eq ls) ls (by decide)
  have done := all l has (by simpa using fun d hd => (by have := range' d hd; omega : 0<d))
  simpa [e] using done

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part5_root : Verified 5 [] 10 3 10 :=
  from_bulk (hn:=by decide) [
    0x4230413210,
    0x3142043210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part7_root : Verified 7 [] 21 3 21 :=
  from_bulk (hn:=by decide) [
    0x642352651431540630210,
    0x642351652431540630210,
    0x623515642431540630210,
    0x524165326431540630210,
    0x531624056432514630210,
    0x653241526431504630210,
    0x516234056425314630210,
    0x642531654321504630210,
    0x645325614231504630210,
    0x426531605143254630210,
    0x613505624143254630210,
    0x516324062541305643210,
    0x632514056243054613210,
    0x524630651432540613210,
    0x631506541342546203210,
    0x625134053642056143210,
    0x463152065342506143210,
    0x562431536402506143210,
    0x426531645032061543210,
    0x524613041536206543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_3_3 : Verified 9 [3,3,3,3] 32 3 24 :=
  from_bulk (hn:=by decide) [
    0x874653582642732541381671430860750210,
    0x748563827642532541381671430860750210,
    0x785634826742532541381671430860750210,
    0x876543210863572842581731641470260530,
    0x856437268742532541381671430860750210,
    0x587236417453625482381671430860750210,
    0x736584287462532541381671430860750210,
    0x846372658742532541381671430860750210,
    0x587364284726532541381671430860750210,
    0x873642584726532541381671430860750210,
    0x873627485246532541381671430860750210,
    0x876543210462731853428751861470630520,
    0x582637417846532542381671430860750210,
    0x784563726485325241381671430860750210,
    0x784637265485325241381671430860750210,
    0x357042816584307831764526372541680210,
    0x563782416485325472381671430860750210,
    0x653784285146325472381671430860750210,
    0x563287416485245372381671430860750210,
    0x562874158463245372381671430860750210,
    0x647852365482415372381671430860750210,
    0x375628140517243860764854532631870210,
    0x785648354736252413281671430860750210,
    0x634728150624145203210864576583731870,
    0x538726417456385243281671430860750210,
    0x738456264785325143281671430860750210,
    0x783654258473625143281671430860750210,
    0x874563584273625143281671430860750210,
    0x428715630673258416472354381860750210,
    0x874563625148532437281671430860750210,
    0x462785130563748241832543761860750210,
    0x846372514785623145382671430860750210,
    0x325461780582431472650863753481760210,
    0x874263514658231548372671430860750210,
    0x635874284651325418372671430860750210,
    0x856453248372625187413671430860750210,
    0x648372516582453287413671430860750210,
    0x627385156482453287413671430860750210,
    0x648251658372453287413671430860750210,
    0x738452856426153287413671430860750210,
    0x452671830856473248726351431860750210,
    0x832746516287354158423671430860750210,
    0x784536582432618527413671430860750210,
    0x356241870728451432105837764361250680,
    0x826473516587241548323671430860750210,
    0x653872418462518547323671430860750210,
    0x872465162538418547323671430860750210,
    0x623851470528768427186130643573540210,
    0x642873518365418527432671430860750210,
    0x873645165382418527432671430860750210,
    0x653824164587381527432671430860750210,
    0x784563615824725314832671430860750210,
    0x862745130418732560463582483761750210,
    0x425618730582746314532671843860750210,
    0x873652416472853154032671843860750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_3_4 : Verified 9 [4,3,3,3] 32 4 23 :=
  from_bulk (hn:=by decide) [
    0x627354167436524328178514830860750210,
    0x736452653427614328178514830860750210,
    0x746536254327614328178514830860750210,
    0x876543210283170625168504630753427841,
    0x827365416742531643278514830860750210,
    0x876543210731603642072515740835862841,
    0x825367416542316437278514830860750210,
    0x824536147652316437278514830860750210,
    0x825463147653261437278514830860750210,
    0x874325615467362413728514830860750210,
    0x874356125467362413728514830860750210,
    0x873461547623652413728514830860750210,
    0x823174560416872530483624673581750210,
    0x427165830826745314632517843860750210,
    0x456271830674253146328517843860750210,
    0x835426716527403146328517843860750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_3_5 : Verified 9 [5,3,3,3] 32 5 22 :=
  from_bulk (hn:=by decide) [
    0x852643167351654234827147830860750210,
    0x853761526431654234827147830860750210,
    0x471652830853726415423167843860750210,
    0x472856130462538154237167843860750210,
    0x461528308562473145327167843860750210,
    0x461852305624731453827167843860750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_3_6 : Verified 9 [6,3,3,3] 32 6 21 :=
  from_bulk (hn:=by decide) [
    0x472651830853642541732167843860750210,
    0x827463516583042541732167843860750210,
    0x836425185304726541732167843860750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_3_9 : Verified 9 [9,3,3,3] 32 9 18 :=
  from_bulk (hn:=by decide) [
    0x852736140624831750746518230786543210] (by rfl)

private theorem part9_3_3_3 : Verified 9 [3,3,3] 33 3 27 := by
  apply branch (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact part9_3_3_3_3
  · exact part9_3_3_3_4
  · exact part9_3_3_3_5
  · exact part9_3_3_3_6
  · exact no_parts (by rfl)
  · exact no_parts (by rfl)
  · exact part9_3_3_3_9

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_4 : Verified 9 [4,3,3] 33 4 26 :=
  from_bulk (hn:=by decide) [
    0x643852865436154231827147803760750210,
    0x648538654326154231827147803760750210,
    0x741826350657317251642085403210843768,
    0x724386516325416482358147803760750210,
    0x685324152648316543827147803760750210,
    0x726834516485316524328147803760750210,
    0x624835158643265413827147803760750210,
    0x684351854623652413827147803760750210,
    0x653281740846725130786345836241750210,
    0x843625168541653243827147803760750210,
    0x845261586341653243827147803760750210,
    0x836152740785326418654231843760750210,
    0x816352740586423165438217843760750210,
    0x816352405864723165438217843760750210,
    0x815236406245831865347217843760750210,
    0x847261586346532452831417803760750210,
    0x836152740853264186542317843760750210,
    0x815326406385274186542317843760750210,
    0x816352740568241645832317843760750210,
    0x816352405682741645832317843760750210,
    0x863524085164726541832317843760750210,
    0x826351406543816852742317843760750210,
    0x835614054362816852742317843760750210,
    0x837165240647285130453267814863750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_5 : Verified 9 [5,3,3] 33 5 25 :=
  from_bulk (hn:=by decide) [
    0x786542631542816432714853083760750210,
    0x468517230635241654823187483760750210,
    0x461725305863241654823187483760750210,
    0x486152304635826541723187483760750210,
    0x425863035164826541723187483760750210,
    0x725846186354265143203187483760750210,
    0x816372540624785130432867184653750210,
    0x852736140624781305432867184653750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_6 : Verified 9 [6,3,3] 33 6 24 :=
  from_bulk (hn:=by decide) [
    0x746351826541685231342780483760750210,
    0x638152740854267130432861784653750210,
    0x867132540627418306342851784653750210,
    0x867132406254183063472851784653750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_3_7 : Verified 9 [7,3,3] 33 7 23 :=
  from_bulk (hn:=by decide) [
    0x815236740628543041683721784653750210,
    0x815263406745823041683721784653750210] (by rfl)

private theorem part9_3_3 : Verified 9 [3,3] 34 3 30 := by
  apply branch (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact part9_3_3_3
  · exact part9_3_3_4
  · exact part9_3_3_5
  · exact part9_3_3_6
  · exact part9_3_3_7
  · exact no_parts (by rfl)
  · exact no_parts (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_4 : Verified 9 [4,3] 34 4 29 :=
  from_bulk (hn:=by decide) [
    0x658432718647862514231453083706750210,
    0x876543210148352716281586046307420753,
    0x827436516487185264231453083706750210,
    0x874365164827185264231453083706750210,
    0x856347287164815264231453083706750210,
    0x856472871634815264231453083706750210,
    0x478615230728536416542318483706750210,
    0x634852687152741864231453083706750210,
    0x427158630648253165432187483706750210,
    0x482516307246853165432187483706750210,
    0x486172530856342645132187483706750210,
    0x728463516852431654032187483706750210,
    0x725346136248518654032187483706750210,
    0x786542631542816432714853083706750210,
    0x468517230635241654823187483706750210,
    0x461725305863241654823187483706750210,
    0x486152304635826541723187483706750210,
    0x425863035164826541723187483706750210,
    0x725846186354265143203187483706750210,
    0x735816240865274130543287184636750210,
    0x735826140865274315423087184636750210,
    0x864715230658723614582431483706750210,
    0x742863514625816543132780483706750210,
    0x825364158624716543132780483706750210,
    0x746285186354165243132780483706750210,
    0x746351826541685231342780483706750210,
    0x726183540865247130432851784636750210,
    0x718356240861452303472851784636750210,
    0x835624716803254134072851784636750210,
    0x837256140742685315432810784636750210,
    0x816523740426853154382710784636750210,
    0x853261408652473154382710784636750210,
    0x852613403814270865473251784636750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_5 : Verified 9 [5,3] 34 5 28 :=
  from_bulk (hn:=by decide) [
    0x735482618564152431632704783086750210,
    0x735846182654152431632704783086750210,
    0x845261735641582431632704783086750210,
    0x738241560472581630645321784386750210,
    0x635182740738526416542310784386750210,
    0x625183740428563164532710784386750210,
    0x638251408562473164532710784386750210,
    0x471652830853264154273160784386750210,
    0x835264716582304154273160784386750210,
    0x746238514035281654273160784386750210,
    0x415283037465816354271260784386750210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_6 : Verified 9 [6,3] 34 6 27 :=
  from_bulk (hn:=by decide) [
    0x825613740463581543271260784386750210,
    0x856137404635281543271260784386750210,
    0x851374046352816543271260784386750210,
    0x738152640582741630654231780486753210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_7 : Verified 9 [7,3] 34 7 26 :=
  from_bulk (hn:=by decide) [
    0x852731460742638150654328710486753210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_3_8 : Verified 9 [8,3] 34 8 25 :=
  from_bulk (hn:=by decide) [
    0x617843250365824706451837214086753210] (by rfl)

private theorem part9_3 : Verified 9 [3] 35 3 33 := by
  apply branch (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact part9_3_3
  · exact part9_3_4
  · exact part9_3_5
  · exact part9_3_6
  · exact part9_3_7
  · exact part9_3_8
  · exact no_parts (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_4 : Verified 9 [4] 35 4 32 :=
  from_bulk (hn:=by decide) [
    0x856487263516824174314520837067503210,
    0x726358418651742864314520837067503210,
    0x748635162785142864314520837067503210,
    0x786351627485142864314520837067503210,
    0x748562368157142864314520837067503210,
    0x485361720528643165421874837067503210,
    0x728463516852043165421874837067503210,
    0x648536871527418624314520837067503210,
    0x458631720648251653421874837067503210,
    0x463517206825431658421874837067503210,
    0x728654316402516358421874837067503210,
    0x465172068254316358421874837067503210,
    0x486351720625414658231874837067503210,
    0x468517206352416548231874837067503210,
    0x724685163520416548231874837067503210,
    0x486152046358265417231874837067503210,
    0x485620864152716342531874837067503210,
    0x726581340861473520542871836467503210,
    0x735826140865274315420871836467503210,
    0x725861408265473153420871836467503210,
    0x872653401846371524168542837067503210,
    0x784356264081371524168542837067503210,
    0x743562640813871524168542837067503210,
    0x813726540716843520428517836467503210,
    0x816245370725684314028517836467503210,
    0x713526840816542043728517836467503210,
    0x813562407168452043728517836467503210,
    0x853741620865243154827107836467503210,
    0x862537416580243154827107836467503210,
    0x862547316580241534827107836467503210,
    0x628534156804718452731207836467503210,
    0x826354185643715246137027840867503210,
    0x835462658143715246137027840867503210,
    0x637451820726485316524107834867503210,
    0x637481520462853165427107834867503210,
    0x847362514602853165427107834867503210,
    0x635814205264731654827107834867503210,
    0x635271840582641654731207834867503210,
    0x728463518526041654731207834867503210,
    0x536284185604716452731207834867503210,
    0x834726150731856420635287140867543210,
    0x745816204653825143726317804867503210,
    0x835426107465825143726317804867503210,
    0x728513640537481620652417803867543210,
    0x627185340847361520564287013867543210,
    0x827165340584736206425187013867543210,
    0x847263507831564071685243182067543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_5 : Verified 9 [5] 35 5 31 :=
  from_bulk (hn:=by decide) [
    0x845362658147152461370278308675043210,
    0x735281460584263165471278308675043210,
    0x582647314253607165481278308675043210,
    0x748251360856241645371278308675043210,
    0x741825605842631645371278308675043210,
    0x741856054826316425371278308675043210,
    0x731458207463526518426178308675043210,
    0x854637207415625318426178308675043210,
    0x627184530736851420647528310876543210,
    0x748562054618241537263178038675043210,
    0x627138450736851420647528130876543210,
    0x627483150716854204637528130876543210,
    0x628147350716845204638572130876543210,
    0x718264506847352041638572130876543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_6 : Verified 9 [6] 35 6 30 :=
  from_bulk (hn:=by decide) [
    0x847261073564315286241780385760543210,
    0x461583720684253170476281308756543210,
    0x683517420648527314076281308756543210,
    0x627158407683142064735281308756543210,
    0x718536240647382051486721308756543210,
    0x735826406381742051486721308756543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_7 : Verified 9 [7] 35 7 29 :=
  from_bulk (hn:=by decide) [
    0x517846208253741408367203168576543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem part9_9 : Verified 9 [9] 35 9 27 :=
  from_bulk (hn:=by decide) [
    0x374158620648135270428361750876543210] (by rfl)

private theorem part9_root : Verified 9 [] 36 3 36 := by
  apply branch (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact part9_3
  · exact part9_4
  · exact part9_5
  · exact part9_6
  · exact part9_7
  · exact no_parts (by rfl)
  · exact part9_9

private def Covers (n mask : Nat) (m : Multiset Nat) : Prop :=
  ∃ C : Multiset (Cycle (K n)), lengths C=m ∧ ∀ q : Fin n × Fin n,
    (C.filter fun c => s(q.1,q.2) ∈ c.edges).card=(mask.testBit (key q)).toNat

private theorem raw_cover {n : Nat} (hn : 0<n) (mask : Nat) (ds : List Nat) (z : Nat)
    (pos : ∀ d∈ds,0<d) (ok : pack (decode hn ds z)=some mask) : Covers n mask ds := by
  obtain ⟨C,hl,hc⟩ := packed _ _ ok
  exact ⟨C,hl.trans (congrArg (fun l : List Nat => (l : Multiset Nat)) (decode_lengths hn ds z pos)),hc⟩

private theorem whole_of_cover {n : Nat} {m : Multiset Nat} (h : Covers n (full n) m) : realizes n m := by
  obtain ⟨C,hl,hc⟩ := h
  refine ⟨C,?_,hl⟩
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have ab : a≠b := (SimpleGraph.mem_edgeFinset.mp he : (K n).Adj a b)
    simpa [full_has a b ab] using hc (a,b)

private theorem union_cover {n a b : Nat} {s t : Multiset Nat} (dis : a &&& b=0)
    (A : Covers n a s) (B : Covers n b t) : Covers n (a ||| b) (s+t) := by
  classical
  obtain ⟨C,lc,hc⟩ := A
  obtain ⟨D,ld,hd⟩ := B
  refine ⟨C+D,by simpa [lengths] using congrArg₂ (·+·) lc ld,?_⟩
  intro q
  rw [Multiset.filter_add,Multiset.card_add,hc,hd,Nat.testBit_or]
  have h := congrArg (fun z : Nat => z.testBit (key q)) dis
  change (a &&& b).testBit (key q) = Nat.testBit 0 (key q) at h
  rw [Nat.testBit_and,Nat.zero_testBit] at h
  cases ha : a.testBit (key q) <;> cases hb : b.testBit (key q) <;> simp_all

private def sums : List Nat → Nat
  | [] => 1
  | d::ds => let f := sums ds; f ||| (f <<< d)

private theorem split_sum (ds : List Nat) (k : Nat) (h : (sums ds).testBit k=true) :
    ∃ a b : Multiset Nat, (ds : Multiset Nat)=a+b ∧ a.sum=k := by
  induction ds generalizing k with
  | nil =>
    have eq : k=0 := by
      rw [show sums []=2^0 by rfl,Nat.testBit_two_pow,decide_eq_true_eq] at h
      exact h.symm
    exact ⟨0,0,by simp,by simp [eq]⟩
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff] at h
    rcases h with h|h
    · obtain ⟨a,b,e,s⟩ := ih k h
      exact ⟨a,d::ₘ b,by change d ::ₘ (ds : Multiset Nat) = _; rw [e]; simp,s⟩
    · rw [Nat.testBit_shiftLeft,Bool.and_eq_true_iff] at h
      obtain ⟨a,b,e,s⟩ := ih (k-d) h.2
      have d_le := of_decide_eq_true h.1
      exact ⟨d::ₘ a,b,by change d ::ₘ (ds : Multiset Nat) = _; rw [e]; simp,by simp [s]; omega⟩

private def selected (k : Option Nat) (l : List Nat) : Bool :=
  match k with
  | none => true
  | some q => !(sums l).testBit q

private def certs {n : Nat} (hn : 0<n) (mask : Nat) (front : List Nat) (k : Option Nat) :
    List (List Nat) → List Nat → Bool
  | [],zs => zs.isEmpty
  | l::ls,zs =>
    let ds := front.reverse++l
    if selected k ds then
      match zs with
      | [] => false
      | z::zs' => (pack (decode hn ds z) == some mask) && certs hn mask front k ls zs'
    else certs hn mask front k ls zs

private def Region (n mask : Nat) (front : List Nat) (fuel lo t : Nat) (k : Option Nat) : Prop :=
  ∀ ds ∈ partitions n fuel lo t, (∀ d ∈ front.reverse++ds,0<d) →
    selected k (front.reverse++ds) = true → Covers n mask ((front.reverse++ds : List Nat) : Multiset Nat)

private theorem certs_sound {n : Nat} {hn : 0<n} {front : List Nat} (mask : Nat) (k : Option Nat)
    (ls : List (List Nat)) (zs : List Nat) (ok : certs hn mask front k ls zs=true) :
    ∀ l∈ls, (∀ j∈front.reverse++l,0<j) → selected k (front.reverse++l)=true →
      Covers n mask ((front.reverse++l : List Nat) : Multiset Nat) := by
  induction ls generalizing zs with
  | nil => simp
  | cons l ls ih =>
    by_cases hc : selected k (front.reverse++l)=true
    · cases zs with
      | nil => simp [certs,hc] at ok
      | cons z zs =>
        obtain ⟨this,rest⟩ := Bool.and_eq_true_iff.mp (show _ from (by simpa only [certs,if_pos hc] using ok))
        intro d hd hpos hsel
        rcases List.mem_cons.mp hd with rfl|hm
        · exact raw_cover hn mask _ z hpos (eq_of_beq this)
        · exact ih zs rest d hm hpos hsel
    · have ht : certs hn mask front k ls zs=true := by simpa [certs,hc] using ok
      intro d hd hp hs
      rcases List.mem_cons.mp hd with rfl|hm
      · exact False.elim (hc hs)
      · exact ih zs ht d hm hp hs

private theorem of_certs {n : Nat} {hn : 0<n} {front : List Nat} {fuel lo t : Nat} {mask : Nat}
    {k : Option Nat} (zs : List Nat) (ok : certs hn mask front k (partitions n fuel lo t) zs=true) :
    Region n mask front fuel lo t k := certs_sound mask k _ _ ok

private theorem split_region {n mask lo t fuel : Nat} {front : List Nat} {k : Option Nat} (ht : 0<t)
    (kids : ∀ d : Nat, lo≤d → d≤n → d≤t → Region n mask (d::front) fuel d (t-d) k) :
    Region n mask front (fuel+1) lo t k := by
  intro ds hm hp sel
  rw [partitions,if_neg ht.ne'] at hm
  obtain ⟨d,hd,hd'⟩ := List.mem_flatMap.mp hm
  by_cases h : lo≤d ∧ d≤t
  · rw [if_pos h] at hd'
    obtain ⟨ds',hs,rfl⟩ := List.mem_map.mp hd'
    simpa using kids d h.1 (by simpa using hd) h.2 ds' hs (by simpa using hp) (by simpa using sel)
  · simp [h] at hd'

private theorem absent_region {n mask lo t fuel : Nat} {front : List Nat} {k : Option Nat}
    (empty : partitions n fuel lo t = []) : Region n mask front fuel lo t k := by
  intro ds h
  simp [empty] at h

private theorem top_region {n mask t : Nat} {k : Option Nat}
    (all : Region n mask [] t 3 t k) (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤n)
    (total : m.sum=t) (sel : selected k (m.sort (·≤·))=true) : Covers n mask m := by
  let l := m.sort (·≤·)
  have e : (l : Multiset Nat)=m := Multiset.sort_eq ..
  have ls : l.sum=t := by convert total using 1; exact congrArg Multiset.sum e
  have lim (d : Nat) (hd : d∈l) : 3≤d ∧ d≤n := bound d (by simpa [l] using hd)
  have length_le_sum (xs : List Nat) (pos : ∀ d∈xs,0<d) : xs.length≤xs.sum := by
    induction xs with
    | nil => simp
    | cons a as ih =>
      have h := ih (fun d hd => pos d (List.mem_cons_of_mem _ hd))
      have ha := pos a (List.mem_cons_self ..)
      simp only [List.length_cons,List.sum_cons]
      omega
  have hl := length_le_sum l (fun d hd => by have := lim d hd; omega)
  have has := in_partitions l (Multiset.pairwise_sort ..) lim (hl.trans_eq ls) ls (by decide)
  have done := all l has (by simpa using fun d hd => (by have := lim d hd; omega : 0<d)) (by simpa [l] using sel)
  simpa [e] using done

private theorem patched {n p q left right total : Nat} (parts : left+right=total)
    (union : p ||| q=full n) (dis : p &&& q=0) (A : Region n p [] left 3 left none)
    (B : Region n q [] right 3 right none) (others : Region n (full n) [] total 3 total (some left))
    (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤n) (sm : m.sum=total) : realizes n m := by
  apply whole_of_cover
  let l := m.sort (·≤·)
  by_cases hit : (sums l).testBit left=true
  · obtain ⟨a,b,e,sa⟩ := split_sum l left hit
    have ab : m=a+b := (Multiset.sort_eq m (·≤·)).symm.trans e
    have aa := top_region A a (fun d hd => bound d (ab ▸ Multiset.mem_add.mpr (Or.inl hd))) sa rfl
    have sb : b.sum=right := by rw [ab,Multiset.sum_add,sa] at sm; omega
    have bb := top_region B b (fun d hd => bound d (ab ▸ Multiset.mem_add.mpr (Or.inr hd))) sb rfl
    rw [ab,←union]
    exact union_cover dis aa bb
  · exact top_region others m bound sm (by simpa [selected,l] using hit)

private lemma can_zero (l : List Nat) : (sums l).testBit 0=true := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff]
    exact Or.inl ih

private lemma can_total (l : List Nat) : (sums l).testBit l.sum=true := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff]
    apply Or.inr
    simpa [Nat.testBit_shiftLeft] using ih

private theorem extend_sum (u v : List Nat) (k h : Nat) (hu : (sums u).testBit k=true)
    (hv : (sums v).testBit h=true) : (sums (u++v)).testBit (k+h)=true := by
  induction u generalizing k with
  | nil =>
    have z : k=0 := by
      rw [show sums []=2^0 by rfl,Nat.testBit_two_pow,decide_eq_true_eq] at hu
      exact hu.symm
    simpa [z] using hv
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff] at hu
    rw [List.cons_append,sums,Nat.testBit_or,Bool.or_eq_true_iff]
    rcases hu with hu|hu
    · exact Or.inl (ih k hu)
    · rw [Nat.testBit_shiftLeft,Bool.and_eq_true_iff] at hu
      have le := of_decide_eq_true hu.1
      right
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true_iff]
      exact ⟨decide_eq_true (by omega),by rw [show k+h-d=(k-d)+h by omega];exact ih _ hu.2⟩

private lemma partition_sum {n fuel lo t : Nat} {l : List Nat} (hm : l∈partitions n fuel lo t) : l.sum=t := by
  induction fuel generalizing l lo t with
  | zero =>
    by_cases h : t=0
    · simp_all [partitions]
    · simp [partitions,h] at hm
  | succ fuel ih =>
    by_cases h : t=0
    · simp_all [partitions]
    · rw [partitions,if_neg h] at hm
      obtain ⟨d,_,in'⟩ := List.mem_flatMap.mp hm
      split at in'
      next cond =>
        obtain ⟨ds,hs,rfl⟩ := List.mem_map.mp in'
        have ht := ih hs
        simp only [List.sum_cons]
        omega
      next => simp at in'

private lemma pruned_left {n mask fuel lo t k : Nat} {front : List Nat}
    (h : (sums front.reverse).testBit k=true) : Region n mask front fuel lo t (some k) := by
  intro ds _ _ sel
  have ht : (sums (front.reverse++ds)).testBit k=true := by simpa using extend_sum _ ds k 0 h (can_zero ds)
  simp [selected,ht] at sel

private lemma pruned_right {n mask fuel lo t k j : Nat} {front : List Nat}
    (sum : j+t=k) (h : (sums front.reverse).testBit j=true) : Region n mask front fuel lo t (some k) := by
  intro ds hm _ sel
  have ht := extend_sum _ ds j ds.sum h (can_total ds)
  rw [partition_sum hm,sum] at ht
  simp [selected,ht] at sel

private abbrev n11a_mask : Nat := 0x18c002ea000c008c0220120b0632

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11a_3 : Region 11 n11a_mask [3] 26 3 24 none :=
  of_certs (hn:=by decide) [
    0x965a83982a72761341530490210,
    0x3498216598a3a72761410290350,
    0x67a318943695a82721410290350,
    0x67a289431596a83721410290350,
    0x8a7234983a21965761410290350,
    0x67a89431a283965721410290350,
    0xa76594316983a82721410290350,
    0xa76943165983a82721410290350,
    0x7a89431a2836721695410290350,
    0x98a76513496a382721410290350,
    0x4982a71653076928a3431210950,
    0x72831a89432a761965410290350,
    0x765943a82169831a72410290350,
    0xa765943821698a3721410290350,
    0x65982a318a76943721410290350,
    0x98a7653a2869414310721290350,
    0x98a7614956a3821340721290350,
    0x43a895671049613821a72290350,
    0x72a3495617a8963821410290350,
    0xa349567298a7163821410290350,
    0x72a89617a349563821410290350,
    0xa349567217a8369821410290350,
    0xa7659438a271369821410290350,
    0x72a8314967a3659821410290350,
    0x49567a28310698a341271290350,
    0x4967a283106598a341271290350,
    0x65982a34138a769401271290350,
    0x569437a31892a67213820590140,
    0x765983a218a7249614310290350,
    0xa38956728a71249614310290350,
    0xa89567283a71249614310290350,
    0xa38967217a82495614310290350,
    0xa8967217a382495614310290350,
    0x43a89567210382a714961290350,
    0x496728a31065983412a71290350,
    0x3a765982172a834014961290350,
    0x98a7652a3174382149610290350,
    0x495672a831043a7128961290350,
    0x438967a2103a827149561290350,
    0x765982a31438a72104961290350,
    0x38967a21043a827149561290350,
    0x49672a3107a8341289561290350,
    0x438a27104967a31289561290350,
    0x4967a3172834012a89561290350,
    0x56172a3894028a7695341031290,
    0x96727a213561982034104950a83,
    0x76598341a8273a2149201690350,
    0xa895672043827a3169411290350,
    0x438a208956727a3169411290350,
    0x98a7652a3174382069411290350,
    0x43176598a207a38269411290350,
    0x4389567a20713a8269411290350,
    0x765982a317a8340269411290350,
    0xa389567204317a8269411290350,
    0x98a765941672a31438201290350,
    0x4176598a2083a72694311290350,
    0xa76594382a89613417201290350,
    0x8a765943a289613417201290350,
    0x6598a3417a28314967201290350,
    0x7a283416598a314967201290350,
    0x43a7165982049672a8312901350,
    0x728a349561402a7698312901350,
    0x49567a8312896143a2017290350,
    0x49567a213a89614382017290350,
    0x6598a314967a214382017290350,
    0x4967a2165983143a82017290350,
    0x95617a283403a89672149201350,
    0x9617a283403a895672149201350,
    0xa769431289562a8310417290350,
    0x956712a83403a72941698201350,
    0x956712a34038a72941698201350,
    0x9217a83403a2765941698201350,
    0x956128a3407a298314967201350,
    0x7a382956134098a214967201350,
    0x76592a3169043821498a7201350] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11a_4 : Region 11 n11a_mask [4] 26 4 23 none :=
  of_certs (hn:=by decide) [
    0x956714038948a7269213a201350,
    0x95614098a3467297a2138201350,
    0x41765983a208a72961294301350,
    0x961403a894567297a2138201350,
    0x956127a340496718a2938201350,
    0x95617a340498a21672938201350,
    0x7a3495614098a21672938201350,
    0x96712a340659418a72938201350,
    0x9617a340498a215672938201350,
    0x7a349614098a215672938201350,
    0x9567140698a2143a72938201350,
    0x95617a283403a89412096721350,
    0x95612a83403a714982096721350,
    0x76598a2194382041693a7201350,
    0x92a8340896712416593a7201350,
    0x96714038a2948216593a7201350,
    0x438a71659203a21490896721350,
    0x4389617a203a821490956721350,
    0x43a896120382a71490956721350,
    0x43895617a203a82901496721350,
    0x49617a283043a89210956721350,
    0x43a7169209412a8308956721350,
    0x43a7169203821490a8956721350,
    0x943a712041692830a8956721350] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11a_5 : Region 11 n11a_mask [5] 26 5 22 none :=
  of_certs (hn:=by decide) [
    0x4382710a896765941312902a350,
    0x8956721438a716940312902a350,
    0x349567a8210413890729612a350,
    0x4967a821307298341095612a350,
    0x4928a713027698341095612a350,
    0x34967a82109271403895612a350,
    0x927a8314034967102895612a350,
    0x928a7140349672103895612a350,
    0x9672143049283107a895612a350,
    0x289567a3410496172a835031290] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11a_6 : Region 11 n11a_mask [6] 26 6 21 none :=
  of_certs (hn:=by decide) [
    0x4956721307a896143820192a350,
    0x49567130698a72143820192a350,
    0x417a8303496721659820192a350,
    0x43895617a203a82769410921350] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11a_7 : Region 11 n11a_mask [7] 26 7 20 none :=
  of_certs (hn:=by decide) [
    0x2a8349567103a72961409821350,
    0x2a3495671038a72961409821350] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11a_8 : Region 11 n11a_mask [8] 26 8 19 none :=
  of_certs (hn:=by decide) [
    0x9567a821430498317201692a350,
    0x95672831403498a71201692a350] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11a_9 : Region 11 n11a_mask [9] 26 9 18 none :=
  of_certs (hn:=by decide) [
    0x38a76921028956134094172a350] (by rfl)

private theorem n11a_root : Region 11 n11a_mask [] 27 3 27 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n11a_3
  · exact n11a_4
  · exact n11a_5
  · exact n11a_6
  · exact n11a_7
  · exact n11a_8
  · exact n11a_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

private abbrev n11b_mask : Nat := 0x2730011400f3007201d02c040800

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11b_3 : Region 11 n11b_mask [3] 27 3 25 none :=
  of_certs (hn:=by decide) [
    0xa570847a64973542632a91851860,
    0xa524870754a64973632a91851860,
    0x875a64a074397542632a91851860,
    0xa578470a64397542632a91851860,
    0xa632518470a548759736429a1860,
    0x5a64270a48754973632a91851860,
    0xa6325487075a4937642a91851860,
    0x64a5793270a63487542a91851860,
    0x64a57326a0793847542a91851860,
    0x8754a6254632a470973a91851860,
    0x6a4879325a074637542a91851860,
    0x648793275a634a07542a91851860,
    0x6a57326487934a07542a91851860,
    0xa62370974635a487542a91851860,
    0xa6425819370879a4754632a51860,
    0xa193624870379a5264a754851860,
    0xa524639706a48732754a91851860,
    0xa52463706a487932754a91851860,
    0x63978426a545732a470a91851860,
    0x9784635a6245732a470a91851860,
    0xa1936254870a9754237a64851860,
    0x7846326a5457932a470a91851860,
    0xa57846239174a630a97542851860,
    0xa524639706a47328754a91851860,
    0x5a63974264a07328754a91851860,
    0x5a648793263742a0754a91851860,
    0x63975a426a078473254a91851860,
    0x975a46326a078473254a91851860,
    0xa426370875a64793254a91851860,
    0xa462581937036a97842754a51860,
    0xa48526397037819a642754a51860,
    0xa4879136a96452473275a0851860,
    0xa5791842376a93645274a0851860,
    0xa625487391a975463274a0851860,
    0x6a9378452a1975463274a0851860,
    0xa54263916a9784573274a0851860,
    0xa54639126a9784573274a0851860,
    0x64879a5245732a639174a0851860,
    0x5a97842645732a639174a0851860,
    0x879a64263754a5239174a0851860,
    0xa1936254870379a64275a4851860,
    0xa9362548703791a64275a4851860,
    0xa64523791639a0784275a4851860,
    0x637845275a64a9324791a0851860,
    0x648752736a54a9324791a0851860,
    0xa19362548704a973275a64851860,
    0xa93625487046a5732791a4851860,
    0x648739a524570a632791a4851860,
    0xa193254870479a626375a4851860,
    0x648739a52470a6325791a4851860,
    0x5a6378426470a9325791a4851860,
    0x9a57846370a625423791a4851860,
    0xa1524863970819a5473260875a64,
    0x487326a936452975185a174a0860,
    0x6a93784524632975185a174a0860,
    0x6a93784254632975185a174a0860,
    0x637845246a932975185a174a0860,
    0x6a97542637849325185a174a0860,
    0x6375426a97849325185a174a0860,
    0xa1854623970784a6375245a91860,
    0x9a64873251639754281a574a0860,
    0x57846a9326379154281a574a0860,
    0x93245179a6364852875a174a0860,
    0xa6481932570879a536247a451860,
    0x9a64237851639752481a574a0860,
    0x9a62378515793642481a574a0860,
    0x587936426a915732481a574a0860,
    0x9a62378519754632481a574a0860,
    0x9a63785197546232481a574a0860,
    0x9a63751245879326481a574a0860,
    0xa918524637054879326a175a4860,
    0x637425a932a648197851754a0860,
    0xa58746239179a6384251754a0860,
    0xa5263748146a93297851754a0860,
    0x64739a52481a63297851754a0860,
    0x936247815a9732a64851754a0860,
    0x6379a524781932a64851754a0860,
    0xa6239185470a97364251875a4860,
    0x9a62374581a079364251875a4860,
    0x6479a52481932a637517854a0860,
    0xa1936258470879a64512375a4860,
    0xa918526470a639784512375a4860,
    0xa6391852470a97845162375a4860,
    0xa639185470a978425162375a4860,
    0xa639745819a078425162375a4860,
    0xa152364706a978542819375a4860] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11b_4 : Region 11 n11b_mask [4] 27 4 24 none :=
  of_certs (hn:=by decide) [
    0x9a63584a645247329751786081a0,
    0xa6452391a97486248751a5807360,
    0xa4523916a97486248751a5807360,
    0x54a9326a197486248751a5807360,
    0xa6479186254a93248751a5807360,
    0xa623915478058642a975a4817360,
    0xa6239784519a46817524a5807360,
    0xa462397819a684517524a5807360,
    0xa93264819786a4517524a5807360,
    0xa6481579a47862493251a5807360,
    0xa45786239179a6481524a5807360,
    0xa479326819a645187524a5807360,
    0xa9326451974a68187524a5807360,
    0x9326a451a97481687524a5807360,
    0xa6874519326481a97524a5807360,
    0xa6475239180a97862451a5847360,
    0xa9325746819780a62451a5847360,
    0x9325a648168742a9754a15807360,
    0x9326a4815a974268754a15807360,
    0x9a624815a4793268754a15807360,
    0x6479a52481932a68754a15807360,
    0xa5193264780579a6842a18547360,
    0xa9157426805a6487932a18547360,
    0xa64781a52684579324a915807360,
    0xa462391578079a685481a5247360,
    0xa462397580786a915481a5247360,
    0x68574a9326a087915481a5247360,
    0x9326a4785180a9754681a5247360,
    0x6a4857932780a9154681a5247360,
    0xa6475180586239a48791a5247360] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11b_5 : Region 11 n11b_mask [5] 27 5 23 none :=
  of_certs (hn:=by decide) [
    0xa45863912578479a64a518073260,
    0xa4863916a975425874a518073260,
    0xa4785163975486a524a918073260,
    0xa6391524780a97586481a5473260,
    0xa639742580a915786481a5473260,
    0x9786a42517580a936481a5473260,
    0xa6391524780a97584681a5473260,
    0xa639157480a978524681a5473260,
    0x936a4875179a08524681a5473260,
    0xa9364758025186a48791a5473260,
    0xa6425180758639a48791a5473260] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11b_6 : Region 11 n11b_mask [6] 27 6 22 none :=
  of_certs (hn:=by decide) [
    0xa63918457079a5246851a4873260,
    0xa918425707936a546851a4873260,
    0xa91845707936a5246851a4873260,
    0xa681547025a936485791a4873260,
    0x819a5237460793624851a0a68754] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11b_7 : Region 11 n11b_mask [7] 27 7 21 none :=
  of_certs (hn:=by decide) [
    0x846397051a6874a918524a573260,
    0xa5237918460a936247851a680754] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11b_8 : Region 11 n11b_mask [8] 27 8 20 none :=
  of_certs (hn:=by decide) [
    0xa193624758079a518460a6873254,
    0xa158463970819a574260a6873254] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11b_9 : Region 11 n11b_mask [9] 27 9 19 none :=
  of_certs (hn:=by decide) [
    0x846a519370a18574260a97863254] (by rfl)

private theorem n11b_root : Region 11 n11b_mask [] 28 3 28 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n11b_3
  · exact n11b_4
  · exact n11b_5
  · exact n11b_6
  · exact n11b_7
  · exact n11b_8
  · exact n11b_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

private abbrev n11rest_mask : Nat := 0x3ff003fe00ff00fe03f03e0f0e32

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_3_3 : Region 11 n11rest_mask [3,3,3,3] 51 3 43 (some 27) :=
  of_certs (hn:=by decide) [
    0x852364a970847561a392a86915437267a5983142817a60490350210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_3_4 : Region 11 n11rest_mask [4,3,3,3] 51 4 42 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_3_5 : Region 11 n11rest_mask [5,3,3,3] 51 5 41 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_3_6 : Region 11 n11rest_mask [6,3,3,3] 51 6 40 (some 27) :=
  of_certs (hn:=by decide) [
    0x62973a48519382a067415708a963427a64598132871a56490350210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_3_7 : Region 11 n11rest_mask [7,3,3,3] 51 7 39 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_3_8 : Region 11 n11rest_mask [8,3,3,3] 51 8 38 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_3_9 : Region 11 n11rest_mask [9,3,3,3] 51 9 37 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

private theorem n11rest_3_3_3 : Region 11 n11rest_mask [3,3,3] 52 3 46 (some 27) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n11rest_3_3_3_3
  · exact n11rest_3_3_3_4
  · exact n11rest_3_3_3_5
  · exact n11rest_3_3_3_6
  · exact n11rest_3_3_3_7
  · exact n11rest_3_3_3_8
  · exact n11rest_3_3_3_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_4 : Region 11 n11rest_mask [4,3,3] 52 4 45 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_5 : Region 11 n11rest_mask [5,3,3] 52 5 44 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_6 : Region 11 n11rest_mask [6,3,3] 52 6 43 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_7 : Region 11 n11rest_mask [7,3,3] 52 7 42 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_8 : Region 11 n11rest_mask [8,3,3] 52 8 41 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_3_9 : Region 11 n11rest_mask [9,3,3] 52 9 40 (some 27) :=
  of_certs (hn:=by decide) [
    0x9657432a80a3827914607158639a407a624598138761a5294350210] (by rfl)

private theorem n11rest_3_3 : Region 11 n11rest_mask [3,3] 53 3 49 (some 27) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n11rest_3_3_3
  · exact n11rest_3_3_4
  · exact n11rest_3_3_5
  · exact n11rest_3_3_6
  · exact n11rest_3_3_7
  · exact n11rest_3_3_8
  · exact n11rest_3_3_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_4 : Region 11 n11rest_mask [4,3] 53 4 48 (some 27) :=
  of_certs (hn:=by decide) [
    0x619475a2830859372641a07189a653240a4879637a8654319250210,
    0x93a251864708294a163750a789562413048a53271960a9768543210,
    0x6832a715940a572641398035824a61970847369a1a8765439250210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_5 : Region 11 n11rest_mask [5,3] 53 5 47 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_6 : Region 11 n11rest_mask [6,3] 53 6 46 (some 27) :=
  of_certs (hn:=by decide) [
    0x79168a354096238147a072856a94317642a598038751a4639250210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_7 : Region 11 n11rest_mask [7,3] 53 7 45 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_8 : Region 11 n11rest_mask [8,3] 53 8 44 (some 27) :=
  of_certs (hn:=by decide) [
    0x917485a326041a2759863081529a64370a42879316508a769453210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_9 : Region 11 n11rest_mask [9,3] 53 9 43 (some 27) :=
  of_certs (hn:=by decide) [
    0x98173a42650748519632a082761a9543068a579314087a649253210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_3_10 : Region 11 n11rest_mask [10,3] 53 10 42 (some 27) :=
  of_certs (hn:=by decide) [
    0x973a2451680756239148a05827a96340674a598130871a649253210] (by rfl)

private theorem n11rest_3 : Region 11 n11rest_mask [3] 54 3 52 (some 27) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n11rest_3_3
  · exact n11rest_3_4
  · exact n11rest_3_5
  · exact n11rest_3_6
  · exact n11rest_3_7
  · exact n11rest_3_8
  · exact n11rest_3_9
  · exact n11rest_3_10
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_4 : Region 11 n11rest_mask [4] 54 4 51 (some 27) :=
  of_certs (hn:=by decide) [
    0x8271a3459607689135a2408a79461a9385748736514a62092503210,
    0xa513682749083571629a402a659184370a39678524198a764503210,
    0x83914a56270248951673a049753182a6069a785471a863492503210,
    0xa75684698343a876459a29726153741285a09318071a60492503210,
    0x613a495278064853a82658397657a9142981374502a6904321071a0,
    0x983457a2617968423a87659a4653741285a09318071a60492503210,
    0xa98765432109635a1428059138497186a75173a206293047250a864,
    0x562798a3416835742a91876954637a4285a09318071a60492503210,
    0xa46279153809a3658742081695437a2a86759314871a60492503210,
    0x97a85364206159a43872a081965473a286759314871a60492503210,
    0x974a2851360a846275391670a95438173a698024187a56492503210,
    0xa4358269709a381674208a739154606a27598413871a56492503210,
    0x9a64285371683a7209418a07965431762a598048751a46392503210,
    0x96428a5317068195437a2089761a409a385748726514a6392503210,
    0x935a1427680749163a2850629518437a046a98317520a8796543210,
    0x85a637194206475182a390726895341a04a978316508a7692543210,
    0xa16835724902643a59817082a47319650679a8514087a6392543210,
    0x9743561a2806249158a370271864a950a57698314087a6392543210,
    0x72689a3415085691374a095382a7640618a579420871a6392543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_5 : Region 11 n11rest_mask [5] 54 5 50 (some 27) :=
  of_certs (hn:=by decide) [
    0x84563687a49a576a8972942615374128590a318071a603925043210,
    0x97542a83617896284a765a9465374128590a318071a603925043210,
    0xa836975427a4862198765a9465374128590a318071a603925043210,
    0x635a97814205831a492786a742a37654691398a0952807165043210,
    0x635a8972415473862a9187694657a428590a318071a603925043210,
    0x672a538941574268a91879654637a428590a318071a603925043210,
    0xa538164279026519a47808549637a298675a314871a603925043210,
    0xa4627915809a5638742081694537a298675a314871a603925043210,
    0xa4265197809583647a20816945372a98675a314871a603925043210,
    0x91867420a56372804a97851694538a26957a314871a603925043210,
    0x72a31958460a475183690628a945371a6798024187a563925043210,
    0xa38519746072a4813690628a945371a67598024187a563925043210,
    0xa3642791802a74851690628a945370a67598314871a563925043210,
    0x8973a56274a8164172a6853196849a709578302451a063925043210,
    0x8a4726173a56417982a6853196849a709578302451a063925043210,
    0x894a571620597248a1837460916530a28769a314587a63925043210,
    0x89715a4206275948a1837460916530a28769a314587a63925043210,
    0x64198a357208425a617903682a95470a49678315081a73926543210,
    0xa528764190513698a47086172a95306a38579420481a73926543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_6 : Region 11 n11rest_mask [6] 54 6 49 (some 27) :=
  of_certs (hn:=by decide) [
    0x96425317485a26a897183a941867a409578203651a0739260543210,
    0x4a6953178206472589183a941867a24a579083651a0739260543210,
    0x478196a352064a98317285941867a24a579083651a0739260543210,
    0x496a3875207619a842a1859074137a286498036517a539260543210,
    0x496a3872057619a842a1859074137a286498036517a539260543210,
    0xa379425815968027148a670914630a287a98316574a539260543210,
    0x8a536794209a485172603a28916470a69578314081a739256543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_7 : Region 11 n11rest_mask [7] 54 7 48 (some 27) :=
  of_certs (hn:=by decide) [
    0x762a13894086427a3078419a53a81695749028517a6392506543210,
    0x7a1386240894672a3078419a53a81695749028517a6392506543210,
    0x75a81624087694130a2735984791a3864a9028517a6392506543210,
    0x973a51684208726a419530749631a2850a9817640a8392576543210,
    0x73894261468027a15a8470919530a28769a318574a6392506543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_8 : Region 11 n11rest_mask [8] 54 8 47 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_9 : Region 11 n11rest_mask [9] 54 9 46 (some 27) :=
  of_certs (hn:=by decide) [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n11rest_11 : Region 11 n11rest_mask [11] 54 11 44 (some 27) :=
  of_certs (hn:=by decide) [
    0x62791583a40357a24186907316495a8208471a639250a9876543210] (by rfl)

private theorem n11rest_root : Region 11 n11rest_mask [] 55 3 55 (some 27) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n11rest_3
  · exact n11rest_4
  · exact n11rest_5
  · exact n11rest_6
  · exact n11rest_7
  · exact n11rest_8
  · exact n11rest_9
  · exact absent_region (by rfl)
  · exact n11rest_11

private theorem verified11 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤11)
    (sm : m.sum=55) : realizes 11 m := by
  apply patched (left:=27) (right:=28) (total:=55) (p:=0x18c002ea000c008c0220120b0632) (q:=0x2730011400f3007201d02c040800)
    (by decide) (by rfl) (by decide) n11a_root n11b_root
    (show Region 11 (full 11) [] 55 3 55 (some 27) from n11rest_root) m bound sm

private def double13 : Fin 13 ≃ Fin 13 where
  toFun x := 2*x
  invFun x := 7*x
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def doubleGraph : K 13 ≃g K 13 where
  toEquiv := double13
  map_rel_iff' := double13.injective.ne_iff

private def moveCycle {n : Nat} (f : K n ≃g K n) (c : Cycle (K n)) : Cycle (K n) :=
  ⟨f c.base,c.walk.map f.toHom,c.isCycle.map f.injective⟩

private lemma moveMem {n : Nat} (f : K n ≃g K n) (c : Cycle (K n)) (a b : Fin n) :
    s(f a,f b) ∈ (moveCycle f c).edges ↔ s(a,b) ∈ c.edges := by
  change s(f a,f b) ∈ (c.walk.map f.toHom).edges ↔ _
  rw [Walk.edges_map]
  change Sym2.map f s(a,b) ∈ List.map (Sym2.map f) c.edges ↔ s(a,b) ∈ c.edges
  exact List.mem_map_of_injective (Sym2.map.injective f.injective)

private theorem moveCover {n a b : Nat} (f : K n ≃g K n)
    (bits : ∀ x y : Fin n, a.testBit (key (x,y))=b.testBit (key (f x,f y)))
    {m : Multiset Nat} (h : Covers n a m) : Covers n b m := by
  classical
  obtain ⟨C,hl,hc⟩ := h
  refine ⟨C.map (moveCycle f),?_,?_⟩
  · have len (c : Cycle (K n)) : (moveCycle f c).length=c.length := Walk.length_map _ _
    simpa [lengths,Multiset.map_map,Function.comp_def,len] using hl
  · rintro ⟨x,y⟩
    obtain ⟨v,rfl⟩ := f.surjective x
    obtain ⟨w,rfl⟩ := f.surjective y
    rw [Multiset.filter_map,Multiset.card_map,←bits]
    simpa [Function.comp_def,moveMem] using hc (v,w)

private theorem complementary13
    (A : Region 13 0xb0d000b0c002c3002c200b000b002c02c0b0a22 [] 39 3 39 none) :
    Region 13 0x4f20004f20013c0013c004f004e013012040410 [] 39 3 39 none := by
  intro ds hm hp hs
  apply moveCover doubleGraph _ (A ds hm hp hs)
  decide +kernel

private def Library (n mask : Nat) (lists : List (List Nat)) : Prop :=
  ∀ ds ∈ lists, (∀ d∈ds,0<d) → Covers n mask ds

private theorem check_library {n mask : Nat} (hn : 0<n) (lists : List (List Nat)) (zs : List Nat)
    (h : certs hn mask [] none lists zs=true) : Library n mask lists := by
  intro ds hm pos
  exact certs_sound mask none lists zs h ds hm pos rfl

private def alternate {n : Nat} (hn : 0<n) (mask : Nat) (A B : List (List Nat)) (ds : List Nat) (z : Nat) : Bool :=
  if z%2=0 then pack (decode hn ds (z/2)) == some mask
  else match A[(z/2)%256]?, B[z/512]? with
    | some a,some b => (a++b).insertionSort (·≤·) == ds.insertionSort (·≤·)
    | _,_ => false

private lemma alternate_ok {n p q mask : Nat} (hn : 0<n) (dis : p &&& q=0) (fullset : p ||| q=mask)
    {A B : List (List Nat)} (ha : Library n p A) (hb : Library n q B) (ds : List Nat) (z : Nat)
    (hp : ∀ d∈ds,0<d) (ok : alternate hn mask A B ds z=true) : Covers n mask ds := by
  by_cases even : z%2=0
  · exact raw_cover hn mask ds (z/2) hp (by simpa [alternate,even] using ok)
  · cases aa : A[(z/2)%256]? with
    | none => simp [alternate,even,aa] at ok
    | some a =>
      cases bb : B[z/512]? with
      | none => simp [alternate,even,aa,bb] at ok
      | some b =>
        have e : (a++b).insertionSort (·≤·)=ds.insertionSort (·≤·) := by simpa [alternate,even,aa,bb] using ok
        have perm : (a++b).Perm ds := by
          exact (List.perm_insertionSort (·≤·) _).symm.trans (e ▸ (List.perm_insertionSort (·≤·) ds))
        have ma := List.mem_of_getElem? aa
        have mb := List.mem_of_getElem? bb
        have u := ha a ma (fun x hx => hp x (perm.mem_iff.mp (List.mem_append_left _ hx)))
        have v := hb b mb (fun x hx => hp x (perm.mem_iff.mp (List.mem_append_right _ hx)))
        have eq : (a : Multiset Nat)+(b : Multiset Nat)=(ds : Multiset Nat) := Quot.sound perm
        rw [←eq,←fullset]
        exact union_cover dis u v

private def with_library {n : Nat} (hn : 0<n) (mask : Nat) (A B : List (List Nat)) (front : List Nat) (k : Option Nat) :
    List (List Nat) → List Nat → Bool
  | [],zs => zs.isEmpty
  | l::ls,zs =>
    let ds := front.reverse++l
    if selected k ds then
      match zs with
      | [] => false
      | z::zs' => alternate hn mask A B ds z && with_library hn mask A B front k ls zs'
    else with_library hn mask A B front k ls zs

private theorem library_sound {n : Nat} {hn : 0<n} {front : List Nat} {mask p q : Nat} {A B : List (List Nat)}
    (dis : p &&& q=0) (un : p ||| q=mask) (ha : Library n p A) (hb : Library n q B) (k : Option Nat)
    (ls : List (List Nat)) (zs : List Nat) (ok : with_library hn mask A B front k ls zs=true) :
    ∀ l∈ls, (∀ j∈front.reverse++l,0<j) → selected k (front.reverse++l)=true →
      Covers n mask ((front.reverse++l : List Nat) : Multiset Nat) := by
  induction ls generalizing zs with
  | nil => simp
  | cons l ls ih =>
    by_cases hc : selected k (front.reverse++l)=true
    · cases zs with
      | nil => simp [with_library,hc] at ok
      | cons z zs =>
        obtain ⟨this,rest⟩ := Bool.and_eq_true_iff.mp (show _ from (by simpa only [with_library,if_pos hc] using ok))
        intro d hd hpos hsel
        rcases List.mem_cons.mp hd with rfl|hm
        · exact alternate_ok hn dis un ha hb _ z hpos this
        · exact ih zs rest d hm hpos hsel
    · have ht : with_library hn mask A B front k ls zs=true := by simpa [with_library,hc] using ok
      intro d hd hp hs
      rcases List.mem_cons.mp hd with rfl|hm
      · exact False.elim (hc hs)
      · exact ih zs ht d hm hp hs

private theorem from_library {n : Nat} {hn : 0<n} {front : List Nat} {mask p q : Nat} {A B : List (List Nat)}
    {k : Option Nat} {fuel lo t : Nat} (dis : p &&& q=0) (un : p ||| q=mask)
    (ha : Library n p A) (hb : Library n q B) (zs : List Nat)
    (ok : with_library hn mask A B front k (partitions n fuel lo t) zs=true) :
    Region n mask front fuel lo t k := library_sound dis un ha hb k _ _ ok

private lemma push_sum (u : List Nat) (d : Nat) : sums (u++[d]) = sums u ||| (sums u <<< d) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append,sums,ih,Nat.shiftLeft_or_distrib,←Nat.shiftLeft_add]
    rw [Nat.add_comm d a]
    ac_rfl

private def screened (n k : Nat) : Nat → Nat → Nat → Nat → List (List Nat)
  | 0,_,t,b => if t=0 ∧ b.testBit k=false then [[]] else []
  | fuel+1,lo,t,b =>
    if b.testBit k || (decide (t≤k) && b.testBit (k-t)) then [] else
    if t=0 then [[]] else
    (List.range (n+1)).flatMap (fun d => if lo≤d ∧ d≤t then
      (screened n k fuel d (t-d) (b ||| (b <<< d))).map (d::·) else [])

private theorem available_branch {n fuel lo t k : Nat} {front ds : List Nat}
    (part : ds∈partitions n fuel lo t) (sel : selected (some k) (front.reverse++ds)=true) :
    (sums front.reverse).testBit k=false ∧
      ¬(t≤k ∧ (sums front.reverse).testBit (k-t)=true) := by
  have miss : (sums (front.reverse++ds)).testBit k=false := by simpa [selected] using sel
  have first : (sums front.reverse).testBit k=false := by
    cases h : (sums front.reverse).testBit k with
    | false => rfl
    | true =>
      have res := extend_sum _ ds k 0 h (can_zero ds)
      simp [miss] at res
  have last : ¬(t≤k ∧ (sums front.reverse).testBit (k-t)=true) := by
    rintro ⟨le,h⟩
    have res := extend_sum _ ds (k-t) ds.sum h (can_total ds)
    rw [partition_sum part,Nat.sub_add_cancel le,miss] at res
    contradiction
  exact ⟨first,last⟩

private theorem screened_complete {n fuel lo t k : Nat} {front ds : List Nat}
    (part : ds∈partitions n fuel lo t) (sel : selected (some k) (front.reverse++ds)=true) :
    ds∈screened n k fuel lo t (sums front.reverse) := by
  induction fuel generalizing front lo t ds with
  | zero =>
    have first := (available_branch part sel).1
    by_cases h : t=0
    · simpa [screened,h,first] using (show ds=[] by simpa [partitions,h] using part)
    · simp [partitions,h] at part
  | succ fuel ih =>
    obtain ⟨first,last⟩ := available_branch part sel
    simp only [screened,first,Bool.false_or]
    have no : (decide (t≤k) && (sums front.reverse).testBit (k-t))=false := by
      simpa using last
    rw [no,if_neg (by decide : ¬false=true)]
    by_cases h : t=0
    · simpa [h] using (show ds=[] by simpa [partitions,h] using part)
    rw [if_neg h]
    rw [partitions,if_neg h] at part
    obtain ⟨d,hd,hin⟩ := List.mem_flatMap.mp part
    refine List.mem_flatMap.mpr ⟨d,hd,?_⟩
    split at hin
    next cond =>
      rw [if_pos cond]
      obtain ⟨ls,hm,rfl⟩ := List.mem_map.mp hin
      apply List.mem_map.mpr
      refine ⟨ls,?_,rfl⟩
      have hm' : selected (some k) ((d::front).reverse++ls)=true := by simpa using sel
      rw [←push_sum,←List.reverse_cons]
      exact ih hm hm'
    next => simp at hin

private theorem from_screened {n : Nat} {hn : 0<n} {front : List Nat} {mask p q : Nat} {A B : List (List Nat)}
    {k fuel lo t : Nat} (dis : p &&& q=0) (un : p ||| q=mask)
    (ha : Library n p A) (hb : Library n q B) (zs : List Nat)
    (ok : with_library hn mask A B front none (screened n k fuel lo t (sums front.reverse)) zs=true) :
    Region n mask front fuel lo t (some k) := by
  intro ds hm hp hs
  apply library_sound dis un ha hb none _ zs ok ds (screened_complete hm hs) hp
  rfl

private def lib38 : List (List Nat) := [
  [3,3,8,8,8,8],
  [3,3,10,10,12],
  [3,3,10,11,11],
  [3,4,10,10,11],
  [3,5,5,5,5,5,5,5],
  [3,5,10,10,10],
  [3,7,7,7,7,7],
  [3,8,8,8,11],
  [3,8,8,9,10],
  [3,8,9,9,9],
  [3,10,12,13],
  [3,11,11,13],
  [3,11,12,12],
  [4,4,4,4,4,4,4,4,6],
  [4,4,4,4,4,4,4,5,5],
  [4,4,4,4,4,4,4,10],
  [4,4,4,4,4,4,5,9],
  [4,4,4,4,4,4,6,8],
  [4,4,4,4,4,5,13],
  [4,4,4,4,4,9,9],
  [4,4,4,4,9,13],
  [4,4,4,4,11,11],
  [4,4,4,13,13],
  [4,4,5,12,13],
  [4,4,6,6,6,6,6],
  [4,4,6,12,12],
  [4,4,8,11,11],
  [4,4,9,9,12],
  [4,4,10,10,10],
  [4,5,5,8,8,8],
  [4,5,5,12,12],
  [4,5,8,8,13],
  [4,6,9,9,10],
  [4,7,7,10,10],
  [4,7,9,9,9],
  [4,8,8,8,10],
  [4,8,8,9,9],
  [4,8,13,13],
  [4,9,12,13],
  [4,10,11,13],
  [4,10,12,12],
  [4,11,11,12],
  [5,5,5,5,5,5,8],
  [5,5,5,5,5,6,7],
  [5,5,5,5,5,13],
  [5,5,5,5,6,6,6],
  [5,5,5,5,6,12],
  [5,5,5,5,7,11],
  [5,5,5,5,9,9],
  [5,5,5,6,6,11],
  [5,5,5,11,12],
  [5,5,6,11,11],
  [5,5,7,7,7,7],
  [5,5,8,8,12],
  [5,5,9,9,10],
  [5,6,6,10,11],
  [5,6,7,10,10],
  [5,6,9,9,9],
  [5,8,8,8,9],
  [5,8,12,13],
  [5,9,12,12],
  [5,10,10,13],
  [5,10,11,12],
  [5,11,11,11],
  [6,6,6,6,6,8],
  [6,6,6,6,7,7],
  [6,6,6,7,13],
  [6,6,6,10,10],
  [6,6,13,13],
  [6,7,12,13],
  [6,8,8,8,8],
  [6,8,12,12],
  [6,9,10,13],
  [6,10,10,12],
  [6,10,11,11],
  [7,7,7,7,10],
  [7,7,7,8,9],
  [7,7,8,8,8],
  [7,7,11,13],
  [7,7,12,12],
  [7,8,11,12],
  [7,9,9,13],
  [7,9,11,11],
  [7,10,10,11],
  [8,8,9,13],
  [8,8,10,12],
  [8,8,11,11],
  [8,9,9,12],
  [8,9,10,11],
  [8,10,10,10],
  [9,9,9,11],
  [9,9,10,10],
  [12,13,13]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib38_proof : Library 13 0xb0d000b0c002c3002c200b000b002c02c0b0c20 lib38 :=
  check_library (by decide) _ [
    0x6a7b8432789cba136541b2c3476958c0521a90,
    0xb2c9856347a140cb8762317ba69548c3521a90,
    0xa789cb26341b856740c2317ba69548c3521a90,
    0xbc96a78523154762c8ba14895637b2143c0a90,
    0x8b7659c3487abc85963147321b26a1452c0a90,
    0x47ab8c9631b7659843215873cb26a1452c0a90,
    0x8c956741ba7854b896237a63cb2143152c0a90,
    0x4859cba6321b26987314567b8c347a152c0a90,
    0x789cba65432b14859631267b8c347a152c0a90,
    0xbc984563278596ab1341267b8c347a152c0a90,
    0xcba6237895140a7b854369c213c847652b1a90,
    0xc21367ab89540bc96234785148c37b256a1a90,
    0xc231b876954026347abc985148c37b256a1a90,
    0xc89652ba78674337b258413cb126a1c9a04590,
    0x8ba74156349876c852b7323cb126a1c9a04590,
    0xc8ba743652987632b758413cb126a1c9a04590,
    0xc896347b2567328ba758413cb126a1c9a04590,
    0xc89674325637b28ba758413cb126a1c9a04590,
    0x958c37b26a140698437654ab875231bc21c9a0,
    0x5678c2341589637ab2b8473cb126a1c9a04590,
    0xcb743269851a05678c9ab2a736b8413c214590,
    0x5263c8ba7412cb734896a1785632b1c9a04590,
    0xc258b134769a09c87ab23651408954cb7326a1,
    0xcb851473269a03489c256a7b1c8763ab214590,
    0x8cba74b256985143782367b13c26a1c9a04590,
    0x58ba769c2341b7489a0c365278cb1326a14590,
    0x523cb769841ba743658c21378b26a1c9a04590,
    0x5698ba743c214852367b1378cb26a1c9a04590,
    0x56347b8c213258967ab14873cb26a1c9a04590,
    0x478c963158437ba1652b89a7bc321c26a04590,
    0x47ba9658c32152bc984367a1b8731c26a04590,
    0xc96734852b1a0cb789a63ab8c2147562314590,
    0x523769c84136589a7b1ab8743c21cb26a04590,
    0x43c98765215847369ab132cb7a1c8b26a04590,
    0xba9673251478563c213489cb7a1c8b26a04590,
    0x589ab763412cb847a18c965237c31b26a04590,
    0x5847abc214367b89a18c965237c31b26a04590,
    0xa9cb156237840c254136a7b890476958c3ab21,
    0xc25698431b7a058b23c9a6741abc8736214590,
    0xc9851347b26a0bc2369a7841ab8c3765214590,
    0xb7a9c263485132bc0a698741ab8c3765214590,
    0xc98b741326a0587a963c2b1abc843765214590,
    0x5487a632c85629c376b895147b21431a0cba90,
    0x6a78452c856329c376b895147b21431a0cba90,
    0x48b7a965123c07854398c25b2631476a1abc90,
    0x87a6548c36259c2376b895147b21431a0cba90,
    0xb7a6523c9841c873627459658b21431a0cba90,
    0xb8c237a6951589c3626784547b21431a0cba90,
    0xb8c236951589c37a626784547b21431a0cba90,
    0xb8c237a6951c9856326784547b21431a0cba90,
    0x548b7a69c321b2c8956374167852431a0cba90,
    0xb89562c3741548c96a7b21587632431a0cba90,
    0xc95876241b8c37963254856a7b21431a0cba90,
    0xb89c37a6254156748c21b7859632431a0cba90,
    0xb259637841c98547a621567b8c32431a0cba90,
    0x487a6259c315437698c213658b247b1a0cba90,
    0x458769c231598437a621563c8b247b1a0cba90,
    0x4895673216a78543c251369c8b247b1a0cba90,
    0x3c8b76521c985436296a784154732b1a0cba90,
    0xa1b89562c37403458c96a7b2148763251cba90,
    0xa1269c378540b7a6598c234136748b251cba90,
    0xa76231b8c95402c347856a1489637b251cba90,
    0xa762c31b854023478c956a1489637b251cba90,
    0xa78c312654047632c958b1a698437b251cba90,
    0xcb8734523c9562896a15367b21a748c041ba90,
    0xa62345178569c398bc25367b21a748c041ba90,
    0xc21347b8596a065489c378cb23a7625141ba90,
    0x367859cb215237b896a16543c2a748c041ba90,
    0xc96314852b7a09ab8c32156740789543bc26a1,
    0xc95126348b7a03cb2547896a137658c241ba90,
    0xcb7a695289c367451378b265a12348c041ba90,
    0xcb21369587a0547b89c326a1567348c241ba90,
    0xcb895476321a03c962b785156a7348c241ba90,
    0xcb87369521a06a74589c32b7651348c241ba90,
    0xcb8596237a054789c36a12b7651348c241ba90,
    0x48962cb731587a632c956743c8b21a0451ba90,
    0x48526a73136987bc2c956743c8b21a0451ba90,
    0x4896a7312cb78563c9526743c8b21a0451ba90,
    0xcb896521347a04859c2376a163c87b2451ba90,
    0x347a6598bc2148523769c0a163c87b2451ba90,
    0xc259841367a023478bc96a1658c37b2451ba90,
    0xcb874312596a048c2367a16589c37b2451ba90,
    0xc25841367a023478bc96a16598c37b2451ba90,
    0xcb8952367a013478569c26a148c37b2451ba90,
    0xa12637bc95840b896a7432c8765413c251ba90,
    0xa6237bc8954140a78569c36748b213c251ba90,
    0xa6589cb7340269541a78c36748b213c251ba90,
    0xa7b89c32654178596a0436748cb213c251ba90,
    0xa6237b8954140a78569c36748cb213c251ba90,
    0xa7b89623416a047859c376548cb213c251ba90,
    0x369547b8c21489c376a1587a0cb2643251ba90,
    0x48b7369c213c895476a1587a0cb2643251ba90,
    0xc9a7658b1234095148c37b26a036987452cba1] (by rfl)

private def lib40 : List (List Nat) := [
  [3,3,3,3,7,7,7,7],
  [3,3,4,10,10,10],
  [3,3,5,5,8,8,8],
  [3,3,5,8,8,13],
  [3,3,6,7,7,7,7],
  [3,3,7,7,7,13],
  [3,3,7,7,10,10],
  [3,3,8,8,8,10],
  [3,3,8,13,13],
  [3,4,4,7,11,11],
  [3,4,10,10,13],
  [3,4,11,11,11],
  [3,5,5,5,5,5,5,7],
  [3,5,5,5,5,5,12],
  [3,5,5,5,5,7,10],
  [3,5,5,5,10,12],
  [3,5,5,5,11,11],
  [3,5,5,7,10,10],
  [3,5,8,8,8,8],
  [3,5,10,11,11],
  [3,7,7,7,7,9],
  [3,7,7,10,13],
  [3,7,8,11,11],
  [3,7,10,10,10],
  [3,8,8,8,13],
  [3,12,12,13],
  [4,4,4,4,4,4,4,4,4,4],
  [4,4,4,4,4,4,4,4,8],
  [4,4,4,4,4,4,4,6,6],
  [4,4,4,4,4,4,4,12],
  [4,4,4,4,4,4,8,8],
  [4,4,4,4,4,6,6,8],
  [4,4,4,4,4,8,12],
  [4,4,4,4,4,10,10],
  [4,4,4,4,6,6,6,6],
  [4,4,4,4,6,6,12],
  [4,4,4,4,6,8,10],
  [4,4,4,4,8,8,8],
  [4,4,4,4,12,12],
  [4,4,4,6,6,6,10],
  [4,4,4,6,6,8,8],
  [4,4,4,6,10,12],
  [4,4,4,8,8,12],
  [4,4,4,8,10,10],
  [4,4,5,5,11,11],
  [4,4,5,9,9,9],
  [4,4,6,6,8,12],
  [4,4,6,6,10,10],
  [4,4,7,7,7,11],
  [4,4,8,8,8,8],
  [4,4,8,12,12],
  [4,4,10,10,12],
  [4,4,10,11,11],
  [4,5,5,5,5,5,11],
  [4,5,5,5,10,11],
  [4,5,7,12,12],
  [4,5,9,9,13],
  [4,5,9,11,11],
  [4,5,10,10,11],
  [4,6,6,6,6,6,6],
  [4,6,6,6,6,12],
  [4,6,6,6,8,10],
  [4,6,6,8,8,8],
  [4,6,6,12,12],
  [4,6,10,10,10],
  [4,7,7,11,11],
  [4,7,9,9,11],
  [4,8,8,8,12],
  [4,8,8,10,10],
  [4,9,9,9,9],
  [4,12,12,12],
  [5,5,5,5,5,5,5,5],
  [5,5,5,5,5,5,10],
  [5,5,5,5,5,7,8],
  [5,5,5,5,7,13],
  [5,5,5,5,9,11],
  [5,5,5,5,10,10],
  [5,5,5,7,8,10],
  [5,5,6,6,6,6,6],
  [5,5,6,6,6,12],
  [5,5,6,8,8,8],
  [5,5,6,12,12],
  [5,5,7,7,7,9],
  [5,5,7,10,13],
  [5,5,7,11,12],
  [5,5,8,11,11],
  [5,5,9,10,11],
  [5,5,10,10,10],
  [5,6,6,6,6,11],
  [5,6,6,11,12],
  [5,6,8,8,13],
  [5,7,7,7,7,7],
  [5,7,7,9,12],
  [5,7,8,10,10],
  [5,8,8,8,11],
  [5,8,9,9,9],
  [5,9,13,13],
  [5,11,11,13],
  [5,11,12,12],
  [6,6,6,6,6,10],
  [6,6,6,6,8,8],
  [6,6,6,10,12],
  [6,6,6,11,11],
  [6,6,7,7,7,7],
  [6,6,8,8,12],
  [6,6,8,10,10],
  [6,6,9,9,10],
  [6,7,7,7,13],
  [6,7,7,10,10],
  [6,7,9,9,9],
  [6,8,8,8,10],
  [6,8,8,9,9],
  [6,8,13,13],
  [6,10,12,12],
  [6,11,11,12],
  [7,7,7,7,12],
  [7,7,7,8,11],
  [7,7,7,9,10],
  [7,7,8,9,9],
  [7,7,13,13],
  [7,8,8,8,9],
  [7,9,11,13],
  [7,9,12,12],
  [7,10,10,13],
  [7,10,11,12],
  [7,11,11,11],
  [8,8,8,8,8],
  [8,8,11,13],
  [8,8,12,12],
  [8,9,11,12],
  [8,10,10,12],
  [8,10,11,11],
  [9,9,9,13],
  [9,9,10,12],
  [9,9,11,11],
  [9,10,10,11],
  [10,10,10,10]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib40_proof : Library 13 0x4f20004f20013c0013c004f004e013012040212 lib40 :=
  check_library (by decide) _ [
    0xa35c792864917238ac4b96b5a420c617503b0180,
    0x75392a4c6194b6028ac179b5a386427c503b0180,
    0x8a539b4286c194a3ca29716475b6027c503b0180,
    0x7192a835b4c60ca579461a39b682427c503b0180,
    0x9b4ca8392a5b641c68279753a420617c503b0180,
    0x79b42835ac160a46b57293a86c42917c503b0180,
    0xa3579b4682706ca83942a5b61c42917c503b0180,
    0x794b53ac6091c42a836b9275a428617c503b0180,
    0x7193a286b4c5061c79b538a420946ca5723b0180,
    0x93a5c6b42716075b92a4c197ca864382053b0180,
    0x64a5b91c72830a3975c6b4294ca86170253b0180,
    0x6c75a24b9308a46b5c197294ca386170253b0180,
    0xca3829164b5c72a4c79b6168a5039420753b0180,
    0x79283ac5b4619b6c172a4c68a5039420753b0180,
    0xa386c5b972917ca824b61c64a5039420753b0180,
    0x9b5c4683a271c7928a5061b4ac639420753b0180,
    0x9b5c468a271c79283a5061b4ac639420753b0180,
    0xc4683a27917c5a829b6105b4ac639420753b0180,
    0x6ca82930a4b91c724c5b61795a386420753b0180,
    0x5b97c64a820391c5a24b6094ca386172753b0180,
    0x75b93a8610794ca524b6c1964a283027c53b0180,
    0x716ca28394b5064c1975a30a86b92427c53b0180,
    0x7192a5b4c60579461ca830a39b682427c53b0180,
    0x7168ac49305b4a291c606b975a382427c53b0180,
    0x724b5a86c19305794ca209b64a382617c53b0180,
    0x5728ac16b493024c683a5b97064a2917c53b0180,
    0xc794a86cb4a39382a5729b6135b0817064205c10,
    0xb5ac4683b924a39497c182716c503570b6102a80,
    0xac468329b5a4b39497c182716c503570b6102a80,
    0xca5b93864271b4a3c79492816c503570b6102a80,
    0x97ca5b42c19b386493a482716c503570b6102a80,
    0xa5b4c793b94683291ca482716c503570b6102a80,
    0x864293b5ac7183a4b972c1946c503570b6102a80,
    0x8293b4ac714683a5b972c1946c503570b6102a80,
    0xb5a493827ca3864b91c429716c503570b6102a80,
    0x93b5ac724681c4b971a382946c503570b6102a80,
    0xca5b4283917c4a3b929718646c503570b6102a80,
    0x94a382714ca5b392b97c18646c503570b6102a80,
    0x683927ca4b508179b3a5c642c1943570b6102a80,
    0x83a5b94271b4c793286c1964ac503570b6102a80,
    0x83b94271a5b4c793286c1964ac503570b6102a80,
    0x682793ac4b509b3817c642a5c1943570b6102a80,
    0x64ac71829b504c683972b3a5c1943570b6102a80,
    0x824ca5b97193b4605c72a386c1943570b6102a80,
    0x6ca3b429750864a5b91c72935c438170b6102a80,
    0xc64a35b9128605c794b39275ac438170b6102a80,
    0x64275b91ca3093b4c68297c5a4538170b6102a80,
    0x6829b4ca3046c193b57297c5a4538170b6102a80,
    0x94a5b386c7205c4b93ac197536428170b6102a80,
    0x6491ca30b4c572935b97c6835a428170b6102a80,
    0x7c6824b93a503b57291ca4605c497183b6102a80,
    0x6827c49b3a5075b4ac19305c64297183b6102a80,
    0x7286c493b5064b91c75a305ca4297183b6102a80,
    0x93ac5724681c4971283b95a4b06b5307c6102a80,
    0xb9381724c5092864b3ac1975a46b5307c6102a80,
    0x681924ca3b50c5a46b9382710b497537c6102a80,
    0x6817294b5ca305a42839b0b64c197537c6102a80,
    0x68294b5ca305a4271839b0b64c197537c6102a80,
    0x68294b3ac504a5b9381720b64c197537c6102a80,
    0xb4c5a3946b53ac1724b9286079183057c6102a80,
    0xb4935c1728609b5a42ca3b6479183057c6102a80,
    0xb4a539286049b5c172ca3b6479183057c6102a80,
    0xc5b49271860b3a42ca539b6479183057c6102a80,
    0xb6824971ca30729183b5c4609b4a5357c6102a80,
    0x6b5c49183072864a39b0b42971ca5357c6102a80,
    0x682793b4a507183ac429b06b5c194357c6102a80,
    0xb4a3927186079b64ca50283b5c194357c6102a80,
    0x718294c53b60864a5b93ac197503b427c6102a80,
    0x7193ac5b60829b35a4c186497503b427c6102a80,
    0x753ac4b605c19283b0b971864a539427c6102a80,
    0x719b4ac53860579281c46b30b5a39427c6102a80,
    0xb64a392a534c68275b91b49706183027c501ca80,
    0x94c682a571b53a429b64b39706183027c501ca80,
    0xa5b4c682a35719429b64b39706183027c501ca80,
    0xb53a4c68291704b975a293b646183027c501ca80,
    0x9b4c682a5714a35b079293b646183027c501ca80,
    0xb53a429170a579b4c68293b646183027c501ca80,
    0xa3579b6c42a5b07194b3928646183027c501ca80,
    0xa4c682b5a3949b3571792460b6183027c501ca80,
    0x7193b5a24c605794a3b92864b6183027c501ca80,
    0x793b4c60a2491753a5b92864b6183027c501ca80,
    0x75a4283b9160b4c681792a30946b5327c501ca80,
    0xa4c6b5793b942a532860719b46183027c501ca80,
    0x75b4c68192a3061794283b09b64a5327c501ca80,
    0x75b4c61928306817942a3b09b64a5327c501ca80,
    0x6c4b57918307168294a3b09b642a5327c501ca80,
    0x75b38294c6186b4a307919b0642a5327c501ca80,
    0x79283a4b60394c6175b0b918642a5327c501ca80,
    0x75b6c492830a53972b4681924a3b0617c501ca80,
    0xb91864275a307935b6c4a2094b382617c501ca80,
    0x75b4c68193a2079b35a42946b0382617c501ca80,
    0xa5b468391827537924c603b94a20b617c501ca80,
    0x729183b5a460a39b4c6824975302b617c501ca80,
    0xa5b394c6827064a381924b975302b617c501ca80,
    0x729183b4c60b942a530975b64a328617c501ca80,
    0x9b42a538106c4975b39270b64a328617c501ca80,
    0x7c6194b5a38203b92a4c571860b642793501ca80,
    0x72a53819b4c60b5792864a302493b617c501ca80,
    0xb972835a4c6075b468192a302493b617c501ca80,
    0x7c46829b50381975c6b3a5394a20b4271061ca80,
    0x79283a50b9186c537c46b5394a20b4271061ca80,
    0x7c6b38194a509b5c4682a3579203b4271061ca80,
    0x93b64c5a28186c705b94a3579203b4271061ca80,
    0x7c49350c6829b5a3819753b64a20b4271061ca80,
    0x7c4683a29b50b6c5a49357918203b4271061ca80,
    0xa57c46b392a49705c6835b918203b4271061ca80,
    0x7c6b392a50a4c5b9183579468203b4271061ca80,
    0x791864c5b3a20b9283507c6b4a5394271061ca80,
    0x57c4b91820792a35c6b0b3864a5394271061ca80,
    0x7c6b53a2083b4c57920b91864a5394271061ca80,
    0x7c6b92a5305c4a3820b4681975b394271061ca80,
    0x5c6b92a307c4b53820a4681975b394271061ca80,
    0x719286b5c4a30183b97c642a50b493572061ca80,
    0x7c4a29b683503b46c5791820b5a394271061ca80,
    0xb57c4a38192035a2864b9705c6b394271061ca80,
    0x5b4a297c6830b94c5a391027536428170b61ca80,
    0x5a386c4b9203b5c791094a27536428170b61ca80,
    0x5b386c79203a5c4b91094a27536428170b61ca80,
    0x93b4a5c7205b94c683a20197536428170b61ca80,
    0x283a57c64b9103b5c4a29718605394270b61ca80,
    0x64c5729302a3b49105b97c6835a428170b61ca80,
    0x683a5b4c729103b975c64a20539428170b61ca80,
    0x386c75a4b92064c5b3a27910539428170b61ca80,
    0x2a4c683b579103a5c729460539b428170b61ca80,
    0x386c4a5729102a3b5c79460539b428170b61ca80,
    0x5c794683a20192753b4c6039b5a428170b61ca80,
    0x93b57281a4c706835c6b942035a29710b461ca80,
    0x728193a4c5b6057c683b942035a29710b461ca80,
    0x7286b93a4c506c75b381942035a29710b461ca80,
    0x724a39186c506b94c7538203b5a29710b461ca80,
    0x7c683a5b94205728193b6035c4a29710b461ca80,
    0x7c682493b50275a3819b6035c4a29710b461ca80,
    0x7c6824a5b39106b972a350b4c57183029461ca80,
    0x5b3a286c7910724c539b60b4a57183029461ca80,
    0x7286c5b391053a24c79b60b4a57183029461ca80,
    0x6827c53b910793a4c6b50b42a57183029461ca80,
    0x35b6c718205a24b938601975c4a3b0729461ca80] (by rfl)

private abbrev n13a_mask : Nat := 0xb0d000b0c002c3002c200b000b002c02c0b0a22

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_3_3 : Region 13 n13a_mask [3,3,3,3,3] 34 3 24 none :=
  of_certs (hn:=by decide) [
    0xc98b78a76965854473cb2632ab15213c0a90410,
    0x9ab1408c9b87a76965854473cb26322513c0a10,
    0xc8590bc98ba796a8746733c25625412b1430a10,
    0x9a678b140c98ba7965854473cb26322513c0a10,
    0xc9526789a651cb8ba7584743632b213c0a90410,
    0x9c87b1409ab8a76965854473cb26322513c0a10,
    0x987b140c9ab8a76965854473cb26322513c0a10,
    0xba9c879041b8a76965854473cb26322513c0a10,
    0xa965487b2c30cb87a6985473362521ba1c90410,
    0x9c8b1409a78ab76965854473cb26322513c0a10,
    0x98b1407a9c8ab76965854473cb26322513c0a10,
    0x9c8567ab1408954b78a96473cb26322513c0a10,
    0xb7841c9ab8965407a6985473cb26322513c0a10,
    0x9c876ab140b89a7659854473cb26322513c0a10,
    0x9c87ab140b89a67659854473cb26322513c0a10,
    0x987ab140b8c9a67659854473cb26322513c0a10,
    0x9c85409a78ab7648b1965473cb26322513c0a10,
    0xa9c87541b8ab764890965473cb26322513c0a10,
    0xb76a9c85418904ba78965473cb26322513c0a10,
    0x9c87ab140698b7a659854473cb26322513c0a10,
    0x9c87b140698ba7a659854473cb26322513c0a10,
    0x9c8ba76b140987a659854473cb26322513c0a10,
    0x96a7b140c8ba987659854473cb26322513c0a10,
    0x96ab140c8b7a987659854473cb26322513c0a10,
    0xc96a7b8451230c8763598473cb2652ba1a90410,
    0x9ab1408b7a69c87659854473cb26322513c0a10,
    0xab7632c9845196a785cb8743652b21c309a0410,
    0x9c8567ab140598b7346a9874cb26322513c0a10,
    0x95876ab1408b7a9654c98473cb26322513c0a10,
    0xb7a69584109ab87654c98473cb26322513c0a10,
    0xa9c87ba678965b8414590473cb26322513c0a10,
    0xb76a9c841ab8796584590473cb26322513c0a10,
    0x8c9ab765a7896b1484590473cb26322513c0a10,
    0xab78c967a9856b1484590473cb26322513c0a10,
    0x98cba732651406743c952b87a968542b1c30a10,
    0x8c9a765ab8967b1484590473cb26322513c0a10,
    0x8c9a657ab8967b1484590473cb26322513c0a10,
    0x956a78c2b1409cb76ab898547436322513c0a10,
    0x9c856a7b1408ba9549678473cb26322513c0a10,
    0x9c8567b1408ba69549a78473cb26322513c0a10,
    0xb7659c841096ab8549a78473cb26322513c0a10,
    0xab78967a956458b148c90473cb26322513c0a10,
    0xb8c956a7341ba98740967854cb26322513c0a10,
    0x9c8567b1408ba95496a78473cb26322513c0a10,
    0x9ab76584059c8b1496a78473cb26322513c0a10,
    0x9567b84058c9ab1496a78473cb26322513c0a10,
    0xb769c85418ba904956a78473cb26322513c0a10,
    0xb769c84158ba904956a78473cb26322513c0a10,
    0xb76984158ba904c956a78473cb26322513c0a10,
    0x9c856237ab1404598b763a96874cb22513c0a10,
    0xb7326a9c854167ab89043956874cb22513c0a10,
    0x9c8ba7623406a98541b73956874cb22513c0a10,
    0x7ab86a95376247b1c3409630c98854cb2251a10,
    0x7a69c8439ab8765847b19540cb26322513c0a10,
    0x7a69843c9ab8765847b19540cb26322513c0a10,
    0x7a9843c96ab8765847b19540cb26322513c0a10,
    0xb2c8569a7341ab76c98b95408746322513c0a10,
    0x7ab84389a67c965847b19540cb26322513c0a10,
    0xba9c8567341a789648b79540cb26322513c0a10,
    0xba985673419c87a648b79540cb26322513c0a10,
    0x7ba69c8431b8567489a79540cb26322513c0a10,
    0x7ba658431b8c967489a79540cb26322513c0a10,
    0xab87658c969a748437b19540cb26322513c0a10,
    0xba9c8567418b734896a79540cb26322513c0a10,
    0xb8c96734189ab74856a79540cb26322513c0a10,
    0xb85673418c9ab74896a79540cb26322513c0a10,
    0x8c9ab7658b14374896a79540cb26322513c0a10,
    0xb85674189ab7348c96a79540cb26322513c0a10,
    0x9c856237ab14067895438b74a96cb22513c0a10,
    0x9a7658c2b140596ab7849cb87436322513c0a10,
    0xb2c87a6954109cb765849ab87436322513c0a10,
    0xbc87a6954109c2b765849ab87436322513c0a10,
    0x7ba69c8437a95641b8798540cb26322513c0a10,
    0x8c956a749ab876b143798540cb26322513c0a10,
    0x8c96a7478ba956b143798540cb26322513c0a10,
    0x8c96a747ba9568b143798540cb26322513c0a10,
    0x9c856237ab140a98b7695436874cb22513c0a10,
    0x9a7658c2b1408ba69549cb784736322513c0a10,
    0xba9c8567341096a7b8478954cb26322513c0a10,
    0xb8c96a734109ab7658478954cb26322513c0a10,
    0x78c954896734b856a79ab140cb26322513c0a10,
    0x9a7658c2b140ab7896bc95487436322513c0a10,
    0x9c856a7b14078ba954896734cb26322513c0a10,
    0xba659c874158b7a904896734cb26322513c0a10,
    0xba78c95417b856a904896734cb26322513c0a10,
    0x958ba6734078c965489a7b14cb26322513c0a10,
    0x958ba6740378c965489a7b14cb26322513c0a10,
    0x9c85674059ab8734896a7b14cb26322513c0a10,
    0x9a6237bc85140c98ba7634526958742b13c0a10,
    0x9c2367ab85406a98cb7341526958742b13c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_3_4 : Region 13 n13a_mask [4,3,3,3,3] 34 4 23 none :=
  of_certs (hn:=by decide) [
    0x89cba659a767843c8b247b195406322513c0a10,
    0x9cba76a98567843c8b247b195406322513c0a10,
    0xb2c8569a741bc98a67b784395406322513c0a10,
    0x89a659cb7647ab17843c8b295406322513c0a10,
    0xc96a7348b2cba98567847b195406322513c0a10,
    0xc84376ab258bc969a7847b195406322513c0a10,
    0x76abc84358b2c969a7847b195406322513c0a10,
    0x769abc843b2c9856a7847b195406322513c0a10,
    0x769cb843c2ba9856a7847b195406322513c0a10,
    0x76a984358b2c96cba7847b195406322513c0a10,
    0xc856ab2734896bc9a7847b195406322513c0a10,
    0x9c856237ab1406a954398767b84cb22513c0a10,
    0xb2c9856a7341769ab84bc8795406322513c0a10,
    0xb2c89a673418569cb74ab8795406322513c0a10,
    0xb2c8967341856a9cb74ab8795406322513c0a10,
    0xc96a78b2cba9856748437b195406322513c0a10,
    0xc9658b2a984767abc8437b195406322513c0a10,
    0x9c856237ab140a9876345968b74cb22513c0a10,
    0xc87ab26a9847569cb8437b195406322513c0a10,
    0xb2c9a65873418cba74b896795406322513c0a10,
    0xb2c9a6587418cba734b896795406322513c0a10,
    0xbc9a6587418c2ba734b896795406322513c0a10,
    0xb2c89a74137bc965848ba6795406322513c0a10,
    0xc9a658437b278cb14ab896795406322513c0a10,
    0xc96a7348b21ba9874bc856795406322513c0a10,
    0xc9a7348b21ba69874bc856795406322513c0a10,
    0xc96a748b2378cb14ba9856795406322513c0a10,
    0x8bc96a74378c2b14ba9856795406322513c0a10,
    0x958c2637ab140bc987654328b74a962513c0a10,
    0xbc9a62378541ba7634098c28b746952513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_3_5 : Region 13 n13a_mask [5,3,3,3,3] 34 5 22 none :=
  of_certs (hn:=by decide) [
    0xc8437b289a67bc95847ab1965406322513c0a10,
    0x7bc84359c2b89a67847ab1965406322513c0a10,
    0xb2c859a673418ba74bc987965406322513c0a10,
    0xb2c859a734189cb748ba67965406322513c0a10,
    0xb2c89a7341859cb748ba67965406322513c0a10,
    0xc958437b21bc89a748ba67965406322513c0a10,
    0xc958437ab21bc874b89a67965406322513c0a10,
    0xb2c9587418cba734b89a67965406322513c0a10,
    0xbc9587418c2ba734b89a67965406322513c0a10,
    0x7abc984378c2b14b859a67965406322513c0a10,
    0x9c236587ab1408cb76a95498b264732513c0a10,
    0x9a732658b1406ab78c954389674cb22513c0a10,
    0xba6378c9541409a7b8562389674cb22513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_3_6 : Region 13 n13a_mask [6,3,3,3,3] 34 6 21 none :=
  of_certs (hn:=by decide) [
    0xc87459ab2376584bc96a798b1406322513c0a10,
    0xc8769ab2bc958473456a798b1406322513c0a10,
    0xc9547b28cba96734856a798b1406322513c0a10,
    0x9c856237ab14059a67b84789634cb22513c0a10,
    0xb2c859a6734187abc96547b89046322513c0a10,
    0xc9584376ab2569a78cb147b89046322513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_3_7 : Region 13 n13a_mask [7,3,3,3,3] 34 7 20 none :=
  of_certs (hn:=by decide) [
    0x9c856237ab140876a9547b89634cb22513c0a10,
    0xb2c9a65873417abc89548b769046322513c0a10,
    0xb2c87a96541376abc9847b859046322513c0a10,
    0xbc87a96541376ab2c9847b859046322513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_3_8 : Region 13 n13a_mask [8,3,3,3,3] 34 8 19 none :=
  of_certs (hn:=by decide) [
    0xc8965437ab28bc9a6741b7859046322513c0a10,
    0xb2c9a678415698cba7437b859046322513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_3_9 : Region 13 n13a_mask [9,3,3,3,3] 34 9 18 none :=
  of_certs (hn:=by decide) [
    0xc9a7458b21ba6987348cb7659046322513c0a10] (by rfl)

private theorem n13a_3_3_3_3 : Region 13 n13a_mask [3,3,3,3] 35 3 27 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13a_3_3_3_3_3
  · exact n13a_3_3_3_3_4
  · exact n13a_3_3_3_3_5
  · exact n13a_3_3_3_3_6
  · exact n13a_3_3_3_3_7
  · exact n13a_3_3_3_3_8
  · exact n13a_3_3_3_3_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_4 : Region 13 n13a_mask [4,3,3,3] 35 4 26 none :=
  of_certs (hn:=by decide) [
    0x6a7843bc9a8965c8b2376247b145902513c0a10,
    0x65843abc96a987c8b2376247b145902513c0a10,
    0xba98567432bc87a63769c248b145902513c0a10,
    0xc84369ab2587a69cb8376247b145902513c0a10,
    0xc8436ab2587a969cb8376247b145902513c0a10,
    0xc856ab29a784369cb8376247b145902513c0a10,
    0x69abc843a78569c2b8376247b145902513c0a10,
    0x8cba965a784369c2b8376247b145902513c0a10,
    0x956a732c8b14069843cba97854b7622513c0a10,
    0xc89ab27a6348569cb8376247b145902513c0a10,
    0xb85632c9a741abc896734867b245902513c0a10,
    0xbc9a734856236ab8c2987647b145902513c0a10,
    0xcba734896236a9c8b2785647b145902513c0a10,
    0xcba698432637a9c8b2785647b145902513c0a10,
    0x7abc8439a658369c2b876247b145902513c0a10,
    0x7a9843cba658369c2b876247b145902513c0a10,
    0xbc9a7856234189674ab736b8c245902513c0a10,
    0xbc9a73485623698c2ab87647b145902513c0a10,
    0xcba9843762369c8b2a785647b145902513c0a10,
    0xb8c9a6732cba789623485647b145902513c0a10,
    0xc9a76348b2abc89623785647b145902513c0a10,
    0xcba7896326a9c8b273485647b145902513c0a10,
    0xcba7896236a9c8b273485647b145902513c0a10,
    0xbc987632c8ba962a73485647b145902513c0a10,
    0x9a658732cb14069c8ba7438954b7622513c0a10,
    0xb8732c9a65416958cba7432b7648902513c0a10,
    0xbc87a9563417458ba69c232b7648902513c0a10,
    0xc96732ba987436a7b856248cb145902513c0a10,
    0xc9658ba7432b7362a987648cb145902513c0a10,
    0xc9a73658b2ab78962347648cb145902513c0a10,
    0xc98736ab258b7a962347648cb145902513c0a10,
    0x7ba98563a78b2c962347648cb145902513c0a10,
    0xc98b74362587a96ab237648cb145902513c0a10,
    0xc987436258b7a96ab237648cb145902513c0a10,
    0x658b7432c987a69ab237648cb145902513c0a10,
    0x9c237a658b14078cba9548963467b22513c0a10,
    0xb2c9a73658413478cba627b89645902513c0a10,
    0xbc237a65841ba9c8743627b89645902513c0a10,
    0x7a9c8563748ba6987b26432cb145902513c0a10,
    0x7ab8563748c9a6987b26432cb145902513c0a10,
    0x9856a732cb14069c87438ba95467b22513c0a10,
    0xb85632c9a74176abc8432b789645902513c0a10,
    0xba98c263741b7a65843278bc9645902513c0a10,
    0xb2637a9841c856ab743278bc9645902513c0a10,
    0xbc26589a7341b847632ab78c9645902513c0a10,
    0xba98c26734136a748b2587bc9645902513c0a10,
    0xba7362c8413476a98b2587bc9645902513c0a10,
    0xb2c89a674137ab85623487bc9645902513c0a10,
    0xba9856732c8b147a623487bc9645902513c0a10,
    0xc9a763251b840954126ab78c308965743cb2a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_5 : Region 13 n13a_mask [5,3,3,3] 35 5 25 none :=
  of_certs (hn:=by decide) [
    0xcba987456ab8762c9632b7341485902513c0a10,
    0xc89a745632abc9678b26b7341485902513c0a10,
    0xcba745632a9c87698b26b7341485902513c0a10,
    0x78cba65432c9a7698b26b7341485902513c0a10,
    0xc87456327abc96a98b26b7341485902513c0a10,
    0xcba76325478c96a98b26b7341485902513c0a10,
    0x958c2637ab140a9cb87698456347b22513c0a10,
    0xba98c237654169cb8743a7b26485902513c0a10,
    0xba9c873654147698bc23a7b26485902513c0a10,
    0xbc987365414769ab8c23a7b26485902513c0a10,
    0x78c965432cba76a98b2b76341485902513c0a10,
    0x9a658732cb14069c8437b895467ab22513c0a10,
    0xbc23789a65417ab8c96347b26485902513c0a10,
    0xb8c9a736541476abc23987b26485902513c0a10,
    0xb8c9a763417456abc23987b26485902513c0a10,
    0xcb89a74563276ab1439c87b26485902513c0a10,
    0xb8c237654147abc963a987b26485902513c0a10,
    0xbc237654147ab8c963a987b26485902513c0a10,
    0xcba765432741b8963a9c87b26485902513c0a10,
    0x48c2b1596a73043cba987652158b746329c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_6 : Region 13 n13a_mask [6,3,3,3] 35 6 24 none :=
  of_certs (hn:=by decide) [
    0xc96732458cb76a98b2ba78414365902513c0a10,
    0xb237a69c8541678bc2ba98474365902513c0a10,
    0xb23769c85416a78bc2ba98474365902513c0a10,
    0xbc26a785413769c8b2ba98474365902513c0a10,
    0xbc267854137a69c8b2ba98474365902513c0a10,
    0xbc9a678541ab8c237b2698474365902513c0a10,
    0xbc2678541b8c9a732ba698474365902513c0a10,
    0xc8b7a962378541b26abc98474365902513c0a10,
    0x9c856ab12374059a76348bc2b789624513c0a10,
    0xba76348c952137409a658bc2b789624513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_7 : Region 13 n13a_mask [7,3,3,3] 35 7 23 none :=
  of_certs (hn:=by decide) [
    0xb73698541ab2c87648bc9a743265902513c0a10,
    0x748bc9631ba67854b2c89a743265902513c0a10,
    0x9856a732cb14063459c87b28ba96742513c0a10,
    0x9ab2c87365406a7bc9584321b896742513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_8 : Region 13 n13a_mask [8,3,3,3] 35 8 22 none :=
  of_certs (hn:=by decide) [
    0x958c2637ab14087bc9a65432b896742513c0a10,
    0x9ab7658c2340bc95487a621b8963742513c0a10,
    0x9c87ab26540cb76a9584321b8963742513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_9 : Region 13 n13a_mask [9,3,3,3] 35 9 21 none :=
  of_certs (hn:=by decide) [
    0x9587abc263401b76a9c845698b23742513c0a10,
    0xbc9587a634109ab762c845698b23742513c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_3_10 : Region 13 n13a_mask [10,3,3,3] 35 10 20 none :=
  of_certs (hn:=by decide) [
    0xba9587634109c26a7b845698cb23742513c0a10] (by rfl)

private theorem n13a_3_3_3 : Region 13 n13a_mask [3,3,3] 36 3 30 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13a_3_3_3_3
  · exact n13a_3_3_3_4
  · exact n13a_3_3_3_5
  · exact n13a_3_3_3_6
  · exact n13a_3_3_3_7
  · exact n13a_3_3_3_8
  · exact n13a_3_3_3_9
  · exact n13a_3_3_3_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_4 : Region 13 n13a_mask [4,3,3] 36 4 29 none :=
  of_certs (hn:=by decide) [
    0x85674ba98cb787a63c962432152b195403c0a10,
    0xc9ab84762bc8756987a63432152b195403c0a10,
    0x748cba6358b7689a7c962432152b195403c0a10,
    0x748ba6358cb7689a7c962432152b195403c0a10,
    0xc8763459ab210bc985841b7a14730a6906523c2,
    0x78cba637b856489a7c962432152b195403c0a10,
    0x74856378cba6b89a7c962432152b195403c0a10,
    0x4856a9cb7321c89627ab8674352b195403c0a10,
    0x436987abc21a9c856b748376252b195403c0a10,
    0xcba98473629c8b7a67856432152b195403c0a10,
    0x748cba9632c98b7a67856432152b195403c0a10,
    0x89cb74ba6587a963c8762432152b195403c0a10,
    0x47abc856321a9876b843769c252b195403c0a10,
    0xc9ab8473627bc896a7856432152b195403c0a10,
    0xcb89a7362ab78c9674856432152b195403c0a10,
    0x789cba632c8b7a9674856432152b195403c0a10,
    0xc9ab873627bc896a74856432152b195403c0a10,
    0xc9ab876237bc896a74856432152b195403c0a10,
    0x78cba632c98b769a74856432152b195403c0a10,
    0x9cba763215840789a65439625c8b247b13c0a10,
    0x473658ba9c21348cb7a62789652b195403c0a10,
    0x485637abc21347b8c9a62789652b195403c0a10,
    0xabc968b7a9785633476248c2152b195403c0a10,
    0x6589cb74327a963ab87648c2152b195403c0a10,
    0x7a9cb8563ab78962347648c2152b195403c0a10,
    0x789cba6358b7a962347648c2152b195403c0a10,
    0x7bc9856347a6239ab87648c2152b195403c0a10,
    0x6ab74327a985639cb87648c2152b195403c0a10,
    0xabc23765148907a9c85436a106952c340b872b1,
    0x436589a7bc213748ba6278c9652b195403c0a10,
    0x489a637bc21347ab856278c9652b195403c0a10,
    0x4856ab7321cb89a7436278c9652b195403c0a10,
    0x67ab84358c9a698732647bc2152b195403c0a10,
    0x3cba962587410c8b7a09c23405984a651763b21,
    0x4736589abc216a784327b8c9652b195403c0a10,
    0x437ba985621c847a63278bc9652b195403c0a10,
    0xc89ab7436237a65841278bc9652b195403c0a10,
    0x437ba985621c87a632748bc9652b195403c0a10,
    0x4736ab8c2167a98432587bc9652b195403c0a10,
    0x48ba736213476a98c2587bc9652b195403c0a10,
    0x476ab8c2137a985623487bc9652b195403c0a10,
    0x9cba637852140569a7432c8b1895467b23c0a10,
    0x58cb73621ab876a9847c9652432b195403c0a10,
    0x7bc89a63785126ab847569c2432b195403c0a10,
    0x7b89a632158476abc87569c2432b195403c0a10,
    0x5847621bc89a78ba637569c2432b195403c0a10,
    0x4789c36ab2510458cb17b843a762132c0965a90,
    0x5637489abc21a7b8c9678526432b195403c0a10,
    0x5637ba98c21a748bc9678526432b195403c0a10,
    0x569a7b8c21abc98473678526432b195403c0a10,
    0x8cba74852637b89a67569c21432b195403c0a10,
    0x5637489abc219c8b76a78526432b195403c0a10,
    0xc9ab8473652a7bc896785126432b195403c0a10,
    0xcb89a73652ab748c96785126432b195403c0a10,
    0xc98b7a6523748cba96785126432b195403c0a10,
    0xc9ab873652a7bc8967485126432b195403c0a10,
    0xc98b7a652378cba967485126432b195403c0a10,
    0x78cba96352c98b76a7485126432b195403c0a10,
    0x9ab1562c87340bc95847a63298b7645213c0a10,
    0x4736589abc2152348c96a7b1678b295403c0a10,
    0x437ba9c8521678bc24896a75632b195403c0a10,
    0x4378ba9c2167bc8524896a75632b195403c0a10,
    0x67ba9c852cb8734124896a75632b195403c0a10,
    0xc9ab847625873412bc896a75632b195403c0a10,
    0x47bc8521c9ab876234896a75632b195403c0a10,
    0x9a637852cb140ba769c8432598b7456213c0a10,
    0x52376a9cb841ba743698c216587b295403c0a10,
    0x78cba9632c98b76a74125658432b195403c0a10,
    0x962158cba734036a9548b2c98765247b13c0a10,
    0x58c96ab74321cb89a7365267841b295403c0a10,
    0x58c96ab7321cb89a74365267841b295403c0a10,
    0x9a73651b2c8407ba698549cb8762543213c0a10,
    0x58b7436a9c2137abc8962567841b295403c0a10,
    0x58c9ab73621347a698bc2567841b295403c0a10,
    0x56a98cb7432637ab8512c967841b295403c0a10,
    0x6347abc85237b89a6512c967841b295403c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_5 : Region 13 n13a_mask [5,3,3] 36 5 28 none :=
  of_certs (hn:=by decide) [
    0x67abc843259a6c98b2587b147321965403c0a10,
    0x6abc8437a9526c98b2587b147321965403c0a10,
    0x8c21543096ab7a9847658b259c32a1bc0763410,
    0x6a98437abc2659c8b2587b147321965403c0a10,
    0xb7a9c2634851598cb276ab847321965403c0a10,
    0x6348cb7a952c9851b276ab847321965403c0a10,
    0xba6348c25167859cb29a7b847321965403c0a10,
    0xbc8436251c95876ab29a7b847321965403c0a10,
    0xb2c8436a9519cba785267b847321965403c0a10,
    0xbc9a6348521ba7895c267b847321965403c0a10,
    0xba63489521bc9a785c267b847321965403c0a10,
    0xb2c9a7851cba634895267b847321965403c0a10,
    0xba6348521bc87a959c267b847321965403c0a10,
    0x9c8b7a6512340cba958476298736b25413c0a10,
    0x4367abc9852159a62c847b1b8732965403c0a10,
    0x52637a9841abc876b2c958b74321965403c0a10,
    0xc859a7362789cba6b25148b74321965403c0a10,
    0xc859a7623789cba6b25148b74321965403c0a10,
    0xc98ba762a958736cb25148b74321965403c0a10,
    0x958736abc2140547a9c8b2698432567b13c0a10,
    0xb8c23476a951637abc9852b78412965403c0a10,
    0xb8c2637a9513476abc9852b78412965403c0a10,
    0xc98b7625148cb259a6378ba74321965403c0a10,
    0x9632158cba7406a9548b2c987652437b13c0a10,
    0xb8c23476a951637bc9852ba78412965403c0a10,
    0xb74362c895158bc9a6732ba78412965403c0a10,
    0xba634789c251b859a73267bc8412965403c0a10,
    0xba63789c251b859a743267bc8412965403c0a10,
    0xc958736ab251b89a743267bc8412965403c0a10,
    0x598ba67432c9a7851b2637bc8412965403c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_6 : Region 13 n13a_mask [6,3,3] 36 6 27 none :=
  of_certs (hn:=by decide) [
    0x59c847b218ba76589a637432cb19625403c0a10,
    0x5847ab2167b8c9589a637432cb19625403c0a10,
    0x587ab219c84765b89a637432cb19625403c0a10,
    0x98cba73625140b84569c29a6785b743213c0a10,
    0xb85632c9a741598437b216abc879625403c0a10,
    0xb7489c23651437a958b216abc879625403c0a10,
    0xbc30a152698476ab2c87b8563217a9543c90410,
    0xb8567a9c234159847b2136abc879625403c0a10,
    0x567a98b23412c95847b136abc879625403c0a10,
    0x58b2c9a74123489567b136abc879625403c0a10,
    0xb2c9a765841598b7321436abc879625403c0a10,
    0x48b7659c21589a732b1436abc879625403c0a10,
    0xb859a7321c984367b24156abc879625403c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_7 : Region 13 n13a_mask [7,3,3] 36 7 26 none :=
  of_certs (hn:=by decide) [
    0x436ab7859c21569a7326748cb298b15403c0a10,
    0x4369ab7852137a659c26748cb298b15403c0a10,
    0x437ba6952136587a9c26748cb298b15403c0a10,
    0x437ba695216587a9c236748cb298b15403c0a10,
    0xc9587ba621437a965236748cb298b15403c0a10,
    0xc962587ab143045123c8b76a907489563cb2a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_8 : Region 13 n13a_mask [8,3,3] 36 8 25 none :=
  of_certs (hn:=by decide) [
    0x67bc958437a98c2148ba65237962b15403c0a10,
    0x9a7362cb8514023459c876ab1b74896523c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_9 : Region 13 n13a_mask [9,3,3] 36 9 24 none :=
  of_certs (hn:=by decide) [
    0x9a736258cb1403487ba659c2b896745123c0a10,
    0x9cb7a6325840659ab14378c2b896745123c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_10 : Region 13 n13a_mask [10,3,3] 36 10 23 none :=
  of_certs (hn:=by decide) [
    0x9a785632cb1406ab7348952b8c96745123c0a10,
    0x9587a62cb140348c9ab7652b8963745123c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_3_11 : Region 13 n13a_mask [11,3,3] 36 11 22 none :=
  of_certs (hn:=by decide) [
    0x952cba67840341b7a98562b8c963745123c0a10] (by rfl)

private theorem n13a_3_3 : Region 13 n13a_mask [3,3] 37 3 33 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13a_3_3_3
  · exact n13a_3_3_4
  · exact n13a_3_3_5
  · exact n13a_3_3_6
  · exact n13a_3_3_7
  · exact n13a_3_3_8
  · exact n13a_3_3_9
  · exact n13a_3_3_10
  · exact n13a_3_3_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_4_4 : Region 13 n13a_mask [4,4,3] 36 4 28 none :=
  of_certs (hn:=by decide) [
    0xcba9678948c37a6358b2b7415621459032c0a10,
    0x76abc84389a7c96358b2b7415621459032c0a10,
    0x76a98438cba7c96358b2b7415621459032c0a10,
    0xabc8763489a7c96358b2b7415621459032c0a10,
    0xb258c369a741bc9876ab78435621459032c0a10,
    0xabc8763c9a74896358b2b7415621459032c0a10,
    0xbc9a7634852ab896c378b7415621459032c0a10,
    0xbc9a63485298ba76c378b7415621459032c0a10,
    0x67a9cb843ab25896c378b7415621459032c0a10,
    0x6a9cb8439852ba76c378b7415621459032c0a10,
    0xab8769a736489c358cb2b7415621459032c0a10,
    0xbc37a69852c9ab843678b7415621459032c0a10,
    0xba769c852a98436bc378b7415621459032c0a10,
    0xba69c8523489a76bc378b7415621459032c0a10,
    0xba69c8529a7348bc3678b7415621459032c0a10,
    0x9c8ba7652bc3489a6378b7415621459032c0a10,
    0x958c37ba621408bc967489a7654352b132c0a10,
    0xb258c96a7341cba98763b8475621459032c0a10,
    0xbc9a637485241b7698c3ab875621459032c0a10,
    0xba69c87341cb2589a763b8475621459032c0a10,
    0xbc36a7852c9ab896748b73415621459032c0a10,
    0xba63c852bc9a7896748b73415621459032c0a10,
    0xba9c852bc36a7896748b73415621459032c0a10,
    0xcb87a6352ba98c96748b73415621459032c0a10,
    0xa6321547b8c90ba73c29a14887656952cb10340,
    0xb258c9a763417ba69848bc375621459032c0a10,
    0xbc9a76348527896ab14b8c375621459032c0a10,
    0xbc96a7485236789ab14b8c375621459032c0a10,
    0xa78c969ab258473cb8b763415621459032c0a10,
    0xb258c9a76341ab789648bc375621459032c0a10,
    0xbc9a63478528967b14ab8c375621459032c0a10,
    0xb7436a98528769cb14ab8c375621459032c0a10,
    0xb74369852876a9cb14ab8c375621459032c0a10,
    0xb2587a63418bc9674ba98c375621459032c0a10,
    0xb258763418bc96a74ba98c375621459032c0a10,
    0x6a98b7439cb25876ab148c375621459032c0a10,
    0x9512637abc840543c9a678b2896547b132c0a10,
    0x952637abc8401543c9a678b2896547b132c0a10,
    0x6abc87437a9c3698b2567b148521459032c0a10,
    0x78cba6347a9c3698b2567b148521459032c0a10,
    0xa7362cb1485909c876b7452432109ab8a651c30,
    0xcba74378c9636a98b2567b148521459032c0a10,
    0x562ba9c3784198cb76347a6b8521459032c0a10,
    0xba9c87436517698bc32b7a648521459032c0a10,
    0xbc98743651769ab8c32b7a648521459032c0a10,
    0xbc98736514769ab8c32b7a648521459032c0a10,
    0xba98c3476517bc9632b87a648521459032c0a10,
    0xba9c3476517bc89632b87a648521459032c0a10,
    0xba9c3765147bc89632b87a648521459032c0a10,
    0xba98c376247b15639cb87a648521459032c0a10,
    0x698cb743762ba9c351b87a648521459032c0a10,
    0x9587abc3621407b8c9a65438967452b132c0a10,
    0x473cba69852156348c9a7b178b26459032c0a10,
    0xb847a9c362ab7896734156bc8521459032c0a10,
    0xb87a9c362ab74896734156bc8521459032c0a10,
    0xc987ba632b847a96734156bc8521459032c0a10,
    0xb789c3629ab8476a734156bc8521459032c0a10,
    0x958c37ba621408bc9a7654789634b25132c0a10,
    0x563487a9cb21ba698c37417b8526459032c0a10,
    0xbc9a78436512ba698c37417b8526459032c0a10,
    0xba736512b789a69cb847643c8521459032c0a10,
    0x9ab73c85621408bc96a745987634b25132c0a10,
    0x569c3487ab214736a98b17bc8526459032c0a10,
    0x4789c36ab21569a7348b17bc8526459032c0a10,
    0x567843c9ab21b8963741a7bc8526459032c0a10,
    0xba9c3487651473698b21a7bc8526459032c0a10,
    0xba9847365143c9678b21a7bc8526459032c0a10,
    0xba63c98741567348b219a7bc8526459032c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_4_5 : Region 13 n13a_mask [5,4,3] 36 5 27 none :=
  of_certs (hn:=by decide) [
    0x67a9543cb87358962ba65147b2148c9032c0a10,
    0x7a9543cb876358962ba65147b2148c9032c0a10,
    0x5987a62bc341745639ab76b852148c9032c0a10,
    0xbc3789a62518ba7659634547b2148c9032c0a10,
    0xbc37a698519ab87652634547b2148c9032c0a10,
    0xcb859a6731ba789652634547b2148c9032c0a10,
    0xbc378962518ba7659a634547b2148c9032c0a10,
    0xbc37896518ba76259a634547b2148c9032c0a10,
    0x673cb8526987ab159a634547b2148c9032c0a10,
    0xcba956732698b1587a634547b2148c9032c0a10,
    0x98c37ab2651406a9cb784376954b852132c0a10,
    0xbc345987a62158ba96374167b2548c9032c0a10,
    0xb87a95436215896abc374167b2548c9032c0a10,
    0xba6987451267b859a736543cb2148c9032c0a10,
    0xba96745126a7b8598736543cb2148c9032c0a10,
    0x67a985247ba6951b8736543cb2148c9032c0a10,
    0x9c8b1526a7340cba9856396784547b2132c0a10,
    0x54789abc36214376958b16a7b2548c9032c0a10,
    0x589abc3674126954378b16a7b2548c9032c0a10,
    0x9c36a78b215408cba9659847625437b132c0a10,
    0x543cb789a6217ab859636741b2548c9032c0a10,
    0x59ab8743621b7a698541673cb2548c9032c0a10,
    0xba63478951458b7a9621673cb2548c9032c0a10,
    0x459ab8736215896a7b16743cb2548c9032c0a10,
    0x59ab87362145896a7b16743cb2548c9032c0a10,
    0x458b7a621563789ab196743cb2548c9032c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_4_6 : Region 13 n13a_mask [6,4,3] 36 6 26 none :=
  of_certs (hn:=by decide) [
    0x56ab87412b7a95698437263cb1458c9032c0a10,
    0x56ab7412b87a95698437263cb1458c9032c0a10,
    0x9abc8736521406a748b2589c345967b132c0a10,
    0x4789abc36521b8437a627b1596458c9032c0a10,
    0xbc34789a652637ab84127b1596458c9032c0a10,
    0xb89a7436526abc3784127b1596458c9032c0a10,
    0x43cba9876521b847362a7b1596458c9032c0a10,
    0x4789abc3621567348b2a7b1596458c9032c0a10,
    0x43cb876521ba9847362a7b1596458c9032c0a10,
    0xbc34876521b89a7362ab741596458c9032c0a10,
    0xbc34876521b89a7362ab741596458c9032c0a10,
    0xc2b147a98563048c37ba6215909cb8763452a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_4_7 : Region 13 n13a_mask [7,4,3] 36 7 25 none :=
  of_certs (hn:=by decide) [
    0xba98437652169547b23cb87a64158c9032c0a10,
    0xba98476521695437b23cb87a64158c9032c0a10,
    0xba96745216598437b23cb87a64158c9032c0a10,
    0xba9547362cb769843521b87a64158c9032c0a10,
    0x951263cba78404376a9c852b17b8965432c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_4_8 : Region 13 n13a_mask [8,4,3] 36 8 24 none :=
  of_certs (hn:=by decide) [
    0xbc37a9526ab78412451b896743658c9032c0a10,
    0x958cba736214056a9c3478b28967b15432c0a10,
    0x9abc85263740143c956a78b28967b15432c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_4_9 : Region 13 n13a_mask [9,4,3] 36 9 23 none :=
  of_certs (hn:=by decide) [
    0x9c8ba73652140cb76a9584378962b15432c0a10,
    0x48ba9c3765216a7bc85904378962b15432c0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_4_10 : Region 13 n13a_mask [10,4,3] 36 10 22 none :=
  of_certs (hn:=by decide) [
    0x43cb76a985217ab840956378c962b15432c0a10,
    0x4376ab89521cb7a904856378c962b15432c0a10] (by rfl)

private theorem n13a_3_4 : Region 13 n13a_mask [4,3] 37 4 32 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13a_3_4_4
  · exact n13a_3_4_5
  · exact n13a_3_4_6
  · exact n13a_3_4_7
  · exact n13a_3_4_8
  · exact n13a_3_4_9
  · exact n13a_3_4_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_5 : Region 13 n13a_mask [5,3] 37 5 31 none :=
  of_certs (hn:=by decide) [
    0xb78952ab8476a9c33456258c219673041bc0a10,
    0xb847a659c3289ab75436258c219673041bc0a10,
    0xb87a659c32489ab75436258c219673041bc0a10,
    0xb847a9c328956ab75436258c219673041bc0a10,
    0x8956ab748b23c9a75436258c219673041bc0a10,
    0xb87a6543289ab7459c36258c219673041bc0a10,
    0xb7a9843256ab87459c36258c219673041bc0a10,
    0x8b7a6547895234ba9c36258c219673041bc0a10,
    0x9c8ba745126303487695289a65c37b241bc0a10,
    0x56347ab89c213c8459a62587b29673041bc0a10,
    0x56a7489c321c8ba954362587b29673041bc0a10,
    0x598ba6326587b2c9a748543c219673041bc0a10,
    0x6ab895236587b2c9a748543c219673041bc0a10,
    0x9c215847ba630b87a952698c376543241bc0a10,
    0x56347ab89c216a958c325487b29673041bc0a10,
    0x5436ab89c21659a78c325847b29673041bc0a10,
    0xc8ba9543623c987a65125847b29673041bc0a10,
    0x59c3478ba62136548c2589a7b29673041bc0a10,
    0xc956ab874321548c362589a7b29673041bc0a10,
    0xc956ab843215478c362589a7b29673041bc0a10,
    0x59ab8743215489c362c856a7b29673041bc0a10,
    0x59ab8743215489c362c856a7b29673041bc0a10,
    0xc8ba74362159041bc9a678523089654c37b2a10,
    0xc9a7843698c23526ab8567b2195473041bc0a10,
    0x45123cb87a690598c264852b1347ba0c9a10763,
    0x569c3487ab21589a63267b8c295473041bc0a10,
    0xba7843c965236a9851267b8c295473041bc0a10,
    0x569a784321589c36ab267b8c295473041bc0a10,
    0x58c9ab76321b87a65269843c295473041bc0a10,
    0x58c9ab7632156a78b269843c295473041bc0a10,
    0x58b7a6321ba9c8765269843c295473041bc0a10,
    0x589ab76321569c8b26a7843c295473041bc0a10,
    0x9637ab8c2154043c9a62587b189567432bc0a10,
    0x59ab84362156a78c23c967b2985473041bc0a10,
    0xc9ab8436256a78c3215967b2985473041bc0a10,
    0x56ab8c213487a96259c367b2985473041bc0a10,
    0x9c2156ab87430b7a9548c362589673241bc0a10,
    0x9ab2c8745630159c348b7a62589673241bc0a10,
    0x9621547ab8c3059a63487b2376589c241bc0a10,
    0x98ba7451263056a9c3487b2376958c241bc0a10,
    0x9512ba6748c3058b7a96326543789c241bc0a10,
    0x98b21547a6303c9ab785625967348c241bc0a10,
    0x9a78b2156303c98547ba625967348c241bc0a10,
    0x96ab7851230b89c37456259a76348c241bc0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_6 : Region 13 n13a_mask [6,3] 37 6 30 none :=
  of_certs (hn:=by decide) [
    0xb856329ab748c96a784376213c2590451bc0a10,
    0x47ba9c8563217698432b87a63c2590451bc0a10,
    0x47658c9ab2137b89623487a63c2590451bc0a10,
    0xba9c856732147b89623487a63c2590451bc0a10,
    0xba9856732147b8c9623487a63c2590451bc0a10,
    0x658c9ab7437698b2321487a63c2590451bc0a10,
    0x7ba9c856347698b2321487a63c2590451bc0a10,
    0x67ba98431269c87458b237a63c2590451bc0a10,
    0x9ab8567412c3059c8436a7b2698732451bc0a10,
    0x9ab8c256743014859c36a7b2698732451bc0a10,
    0xc96ab87432c89a76321485637b2590451bc0a10,
    0xc896a7432c9ab876321485637b2590451bc0a10,
    0x9ab8567412c3059c8437a6236987b2451bc0a10,
    0x9ab8c256743014859c37a6236987b2451bc0a10,
    0x9c2147ab8563059a678432698c37b2451bc0a10,
    0x9567ab841230587436a9c2698c37b2451bc0a10,
    0x9521487a630347658ba9c2698c37b2451bc0a10,
    0x9c2567ab843036a9874126958c37b2451bc0a10,
    0xc98ba743652309a6784126958c37b2451bc0a10,
    0x47ab89632156784309c26a958c37b2451bc0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_7 : Region 13 n13a_mask [7,3] 37 7 29 none :=
  of_certs (hn:=by decide) [
    0x45987b218ba6374a9c8567962c3403251bc0a10,
    0x9658c37ab2140c9548b762789a6343251bc0a10,
    0x95637ab2c840c9a67b854378962143251bc0a10,
    0xc367a9548b27ba658c904378962143251bc0a10,
    0x9a658c37b2140678459c27ab896343251bc0a10,
    0x9ab8562c37406a78c95438967b2143251bc0a10,
    0xc9ab8547362c87a6590438967b2143251bc0a10,
    0xc9ab87345626740958c3896a7b2143251bc0a10,
    0x9c2658734067459ab8c3896a7b2143251bc0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_8 : Region 13 n13a_mask [8,3] 37 8 28 none :=
  of_certs (hn:=by decide) [
    0x9c21478ba630769548c3589a7b2643251bc0a10,
    0x95412c87630748ba69c3589a7b2643251bc0a10,
    0x9c2148763074596ab8c3589a7b2643251bc0a10,
    0x4785963c2109c8ba6735489a7b2643251bc0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_9 : Region 13 n13a_mask [9,3] 37 9 27 none :=
  of_certs (hn:=by decide) [
    0x459a78b2176589c30437ba62c84963251bc0a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_10 : Region 13 n13a_mask [10,3] 37 10 26 none :=
  of_certs (hn:=by decide) [
    0xc9a621458b730432c87ab156905984763cb2a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_11 : Region 13 n13a_mask [11,3] 37 11 25 none :=
  of_certs (hn:=by decide) [
    0x9a736258cb140c215967b84303c987456ab2a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_3_12 : Region 13 n13a_mask [12,3] 37 12 24 none :=
  of_certs (hn:=by decide) [
    0xc362548b7a90321bc8596740c98734156ab2a10] (by rfl)

private theorem n13a_3 : Region 13 n13a_mask [3] 38 3 36 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13a_3_3
  · exact n13a_3_4
  · exact n13a_3_5
  · exact n13a_3_6
  · exact n13a_3_7
  · exact n13a_3_8
  · exact n13a_3_9
  · exact n13a_3_10
  · exact n13a_3_11
  · exact n13a_3_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_4 : Region 13 n13a_mask [4,4] 37 4 31 none :=
  of_certs (hn:=by decide) [
    0x59c3741ab878965b7625432bc2148c036a09a10,
    0x52b74159c34ab8789656732bc2148c036a09a10,
    0x567ab89c34178549625b732bc2148c036a09a10,
    0x69852674159c345ab87b732bc2148c036a09a10,
    0xc98ba76543158749625b732bc2148c036a09a10,
    0x58962b7419c37658ba75432bc2148c036a09a10,
    0x5962b74189c37658ba75432bc2148c036a09a10,
    0x5962ba74189c37658b75432bc2148c036a09a10,
    0x5698b7419c378562ba75432bc2148c036a09a10,
    0x598b741873c96562ba75432bc2148c036a09a10,
    0x59c37418962b7658ba75432bc2148c036a09a10,
    0xc987ab15623408596743cb7c8b2254136a09a10,
    0x587ab269c341598b7326745bc2148c036a09a10,
    0x52ba789c34137b859626745bc2148c036a09a10,
    0x5987ab234158b73c9626745bc2148c036a09a10,
    0x7ab895432b7853c96256741bc2148c036a09a10,
    0x7ab85432b78953c96256741bc2148c036a09a10,
    0x369a7458cb210487b1ab890673259c256a143c0,
    0xba7852b89c3734596256741bc2148c036a09a10,
    0x5623c98ba74145967387b25bc2148c036a09a10,
    0xba78543c962598b73267415bc2148c036a09a10,
    0x698ba734523c9587b267415bc2148c036a09a10,
    0x6958ba732543c987b267415bc2148c036a09a10,
    0xba78543c96298b765237415bc2148c036a09a10,
    0xc967ab8543987b265237415bc2148c036a09a10,
    0xc967b8543987ab265237415bc2148c036a09a10,
    0x67ab8543256987b29c37415bc2148c036a09a10,
    0x67b8543256987ab29c37415bc2148c036a09a10,
    0xc37ab89625140b7659c843278542cb136a09a10,
    0x5269c8ba7341b7659840c3278542cb136a09a10,
    0xcba7852673453c962b895147b2148c036a09a10,
    0x9cba76852c3734562b895147b2148c036a09a10,
    0xba78962c34519cb852376547b2148c036a09a10,
    0xc34598ba76269cb152378547b2148c036a09a10,
    0xb89673c2519cba7856234547b2148c036a09a10,
    0xba789c2519673cb856234547b2148c036a09a10,
    0xbc378962518ba7659c234547b2148c036a09a10,
    0xbc37896518ba76259c234547b2148c036a09a10,
    0x673cb8526987ab159c234547b2148c036a09a10,
    0xbc378951267ab8569c234547b2148c036a09a10,
    0xc37ab895621403458769c28cb7452b136a09a10,
    0x43cba785962156732c98b1b745248c036a09a10,
    0x56987abc32143762c958b1b745248c036a09a10,
    0xc98ba74521b769587326543cb2148c036a09a10,
    0xc98b74521ba769587326543cb2148c036a09a10,
    0xba789512c967458b7326543cb2148c036a09a10,
    0xc32ba789651406748c95258b7342cb136a09a10,
    0x43c96587ab21cb895476251b73248c036a09a10,
    0x458967abc21b8743c956251b73248c036a09a10,
    0xc96237ab8514059847b25678c342cb136a09a10,
    0x437ab8569c21b2678951547bc3248c036a09a10,
    0x58962ba73412c95478b1567bc3248c036a09a10,
    0x589c2ba74126954378b1567bc3248c036a09a10,
    0x52cb896734126587ab1b7459c3248c036a09a10,
    0x56987abc214376258b1b7459c3248c036a09a10,
    0x562cb7341258967ab1b87459c3248c036a09a10,
    0x7ab8438956769c3247b2152cb1458c036a09a10,
    0x48ba73c9621347b28956752cb1458c036a09a10,
    0x48b73c9621347ab28956752cb1458c036a09a10,
    0xba743c962148b7328956752cb1458c036a09a10,
    0x48ba732169c347b28956752cb1458c036a09a10,
    0x4873c9621347ab2b8956752cb1458c036a09a10,
    0x473c96213487ab2b8956752cb1458c036a09a10,
    0x48b73216987ab243c956752cb1458c036a09a10,
    0xc32ba78965140673459c28cb74b852136a09a10,
    0x5962c37ab841234789cb1567b2458c036a09a10,
    0x59cba784321473c2698b1567b2458c036a09a10,
    0x59678432147ab2b89c37562cb1458c036a09a10,
    0x59674321487ab2b89c37562cb1458c036a09a10,
    0xc37ab89562140769c85487b23452cb136a09a10,
    0xba78432c965147b89521673cb2458c036a09a10,
    0xba78432c95147b896521673cb2458c036a09a10,
    0xb78432c95147ab896521673cb2458c036a09a10,
    0x569c237ab84125987b16743cb2458c036a09a10,
    0x59c237ab841256987b16743cb2458c036a09a10,
    0x59c237b841256987ab16743cb2458c036a09a10,
    0x59c237b84126987ab156743cb2458c036a09a10,
    0xb732c96512598ba74167843cb2458c036a09a10,
    0x487ab1569c230cb895214736a0458c367b29a10,
    0xc9548732ba743cb89622567b14158c036a09a10,
    0xcba732698514078c9548b2c34b7652136a09a10,
    0xba789c3456213748bc25967b24158c036a09a10,
    0x659847abc3254378b12c967b24158c036a09a10,
    0xba734895213cb874562c967b24158c036a09a10,
    0x6987abc34523748b12c9567b24158c036a09a10,
    0xb8473c96215987abc234567b24158c036a09a10,
    0xb873c962159847abc234567b24158c036a09a10,
    0x59cb847321ba78962c34567b24158c036a09a10,
    0xa73cb26985140259c87436ab1567b8432c09a10,
    0xba7843c251459cb2137b896247658c036a09a10,
    0x5487abc21b259c34137b896247658c036a09a10,
    0x59cb234125487ab1c37b896247658c036a09a10,
    0xcba732156984043c952678b1b7458c236a09a10,
    0x526987abc341237659c048b1b7458c236a09a10,
    0xcba7326985140259c3478b1b76548c236a09a10,
    0x43cba7859621523740c98b1b76548c236a09a10,
    0xc37ab89652140bc958743267b1548c236a09a10,
    0xcba7895621403c967458b251b7348c236a09a10,
    0x4587abc96213c0476598b251b7348c236a09a10,
    0xcba789625403c958b7412b1567348c236a09a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_5 : Region 13 n13a_mask [5,4] 37 5 30 none :=
  of_certs (hn:=by decide) [
    0xabc8769c3758432b895147b21362c0456a09a10,
    0x5967ab8432789c3cb15847b21362c0456a09a10,
    0xba769c851237895bc34847b21362c0456a09a10,
    0xbc876951237ab859c34847b21362c0456a09a10,
    0xbc96785123c895ba734847b21362c0456a09a10,
    0x9cba78523c8b1596734847b21362c0456a09a10,
    0xc962158ba74303678952c37b248cb1456a09a10,
    0x58c967ab2341b74895218bc37362c0456a09a10,
    0xbc96785234159847ab21b8c37362c0456a09a10,
    0xbc98743251485967ab21b8c37362c0456a09a10,
    0x5896732cba74359c8b1487b21362c0456a09a10,
    0xcba7489512630c37852b8c967432b1456a09a10,
    0x5967abc8432147852b1b89c37362c0456a09a10,
    0x58769cb2341259847b1ab8c37362c0456a09a10,
    0x584769cb214325987b1ab8c37362c0456a09a10,
    0x59cba78432158967b241b8c37362c0456a09a10,
    0x59cba78432158967b241b8c37362c0456a09a10,
    0x59cb78432158967ab241b8c37362c0456a09a10,
    0xbc967843258ba7412b1598c37362c0456a09a10,
    0xa784159cb2630ba698c3745218b765432c09a10,
    0xc8b743abc9875963214852b13762c0456a09a10,
    0x58c9632ba7412598b143cb783762c0456a09a10,
    0x5963c847b2143258b19cba783762c0456a09a10,
    0xb74859632152b8c3419cba783762c0456a09a10,
    0xb748c3251436958b219cba783762c0456a09a10,
    0x589632b741259c8b143cba783762c0456a09a10,
    0x47b8c9521589632b143cba783762c0456a09a10,
    0x43698b2159c847b1523cba783762c0456a09a10,
    0xc267ab1598430258bc9637413c87b2456a09a10,
    0x5984367abc21b85269c037413c87b2456a09a10,
    0x59cb73621ba78c3241b896734852c0456a09a10,
    0x59cb732163c87ab241b896734852c0456a09a10,
    0xc951267ab8430bc2369874158c37b2456a09a10,
    0x5963487abc21b89c032674158c37b2456a09a10,
    0xc962158ba7430598cb7632c37841b2456a09a10,
    0xc96258ba7430367bc89512c37841b2456a09a10,
    0x6347ab8c95230cb7698512c37841b2456a09a10,
    0x58ba74369c215987bc032673c841b2456a09a10,
    0xcba7895123058b74369c2673c841b2456a09a10,
    0x5987abc32158b74369c26730c841b2456a09a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_6 : Region 13 n13a_mask [6,4] 37 6 29 none :=
  of_certs (hn:=by decide) [
    0xba789543c217bc963625847c8b2304156a09a10,
    0xba73459c216987bc3625847c8b2304156a09a10,
    0xb73459c216987abc3625847c8b2304156a09a10,
    0xcba789543b12c9673625847c8b2304156a09a10,
    0xba789c21bc3459673625847c8b2304156a09a10,
    0xc21ba7458963067b843c952bc87324156a09a10,
    0xc98547b12630c348ba76952bc87324156a09a10,
    0x67abc9528963745b843c21c87b2304156a09a10,
    0xc8459621ba730b763c9852cb874324156a09a10,
    0xc98452ba76306958cb7432c378b124156a09a10,
    0xba76348c952698547bc032c378b124156a09a10,
    0xc8459621ba73058763cb2c98b74324156a09a10,
    0xc2ba78459630589cb7432673c8b124156a09a10,
    0xcba7896345230c95847b2673c8b124156a09a10,
    0xcba789634523c95847b26730c8b124156a09a10,
    0x59cba78432c3698547b26730c8b124156a09a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_7 : Region 13 n13a_mask [7,4] 37 7 28 none :=
  of_certs (hn:=by decide) [
    0x78c9543267ab85963214847b2c30cb156a09a10,
    0x412c958ba763069873452b748c32cb156a09a10,
    0x412c958ba7305436987b26748c32cb156a09a10,
    0x437ab859c2154036987b26748c32cb156a09a10,
    0x4587ab2c963067348952147b8c32cb156a09a10,
    0x452ba7896306734859c2147b8c32cb156a09a10,
    0x4589c267305963487ab2147b8c32cb156a09a10,
    0x452c9876306958437b2147ab8c32cb156a09a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_8 : Region 13 n13a_mask [8,4] 37 8 27 none :=
  of_certs (hn:=by decide) [
    0xc3698ba745240c958731267bc8432b156a09a10,
    0xc958ba7340c254789631267bc8432b156a09a10,
    0x43c987621c047ab85259637bc8432b156a09a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_9 : Region 13 n13a_mask [9,4] 37 9 26 none :=
  of_certs (hn:=by decide) [
    0xab1478569c230437a621598bc0548c367b29a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_10 : Region 13 n13a_mask [10,4] 37 10 25 none :=
  of_certs (hn:=by decide) [
    0xc9567ab841230437bc25896a063c87451b29a10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_4_11 : Region 13 n13a_mask [11,4] 37 11 24 none :=
  of_certs (hn:=by decide) [
    0xc958ba7621430a6523cb7840c89637451b29a10,
    0xcb87a6521430ab7623c95840c89637451b29a10] (by rfl)

private theorem n13a_4 : Region 13 n13a_mask [4] 38 4 35 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13a_4_4
  · exact n13a_4_5
  · exact n13a_4_6
  · exact n13a_4_7
  · exact n13a_4_8
  · exact n13a_4_9
  · exact n13a_4_10
  · exact n13a_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_5 : Region 13 n13a_mask [5] 38 5 34 none :=
  of_certs (hn:=by decide) [
    0x5476a9c21698b258c32487b1a734095630cba10,
    0x54769c216a98b23c852487b1a734095630cba10,
    0x589a62154769c23c8b2487b1a734095630cba10,
    0xc9674523c85126a98b2487b1a734095630cba10,
    0xa7b158962c340a9c876b25484732195630cba10,
    0xb8523c9a67415489621c87b2a734095630cba10,
    0x58476a9c321452698b1c87b2a734095630cba10,
    0x584769c321b89a62541c87b2a734095630cba10,
    0x6a9c3298547652b8412c87b1a734095630cba10,
    0xb8523c9a6741548c216987b2a734095630cba10,
    0xb852c9a674154896213c87b2a734095630cba10,
    0x58476a9c21452698b13c87b2a734095630cba10,
    0x584769c214526a98b13c87b2a734095630cba10,
    0xb854769c216a98c3251487b2a734095630cba10,
    0x584769c21b8c325416a987b2a734095630cba10,
    0xb8769c21489a62513c8547b2a734095630cba10,
    0xa6541237b8c9059a7843c2b16985247630cba10,
    0xa7b843c21590456a9c8732b16985247630cba10,
    0xb237a69845167b8c2147852a9c34095630cba10,
    0xb7a62c8451b896732147852a9c34095630cba10,
    0xb8c23745148967b216a7852a9c34095630cba10,
    0x548b7a62137698c2b147852a9c34095630cba10,
    0xc896a7321548b762b147852a9c34095630cba10,
    0xa73269c8b1540c3476a9852b7841295630cba10,
    0xb8c9a6237451c340a769852b7841295630cba10,
    0x489a7b2152378b1458c967a62c34095630cba10,
    0xa967b158c2340b89c374526a7841295630cba10,
    0xa98c251b7340b854769c326a7841295630cba10,
    0xa9c258b7340b1547698c326a7841295630cba10,
    0xa67b1589c2340b8c3745269a7841295630cba10,
    0xa69c251b8740b7a985432673c841295630cba10,
    0xa69c2b7854051b89a7432673c841295630cba10,
    0xb8769c23451589a047b26a73c841295630cba10,
    0xb896743251c9a04587b26a73c841295630cba10,
    0x59a78b23412547b1698c37a658409c2630cba10,
    0x459a78b2152347b1698c37a658409c2630cba10,
    0x459a7b21523478b1698c37a658409c2630cba10,
    0x59a78b21698c347b145237a658409c2630cba10,
    0xa95673c8b214054896a7b17852349c2630cba10,
    0x459a673c8b21569840a7b17852349c2630cba10,
    0xa769512b840456a98c37b17852349c2630cba10,
    0x476952134587b26a98b15a73c8409c2630cba10,
    0xa69521b8c3740567a9841587b2349c2630cba10,
    0xa698b7321540487a952b17658c349c2630cba10,
    0x596a732b8412540a987b17658c349c2630cba10,
    0xa69851b23740487a9521567b8c349c2630cba10,
    0xa695123784047a9852b1567b8c349c2630cba10,
    0xa95123784047a69852b1567b8c349c2630cba10,
    0xb256a987415840a73215967b8c349c2630cba10,
    0xa67b843c21590569873247a9c8541b2630cba10,
    0xa6512347b8905487a9c29673c8541b2630cba10,
    0xa6512347890548b7a9c29673c8541b2630cba10,
    0xa6523478901548b7a9c29673c8541b2630cba10,
    0xa7b84512c9056a9873296743c8541b2630cba10,
    0x5698b743215487a09c29a673c8541b2630cba10,
    0xa78452c9037b8965129a6743c8541b2630cba10,
    0xc9a7b85432569874128c376a04951b2630cba10,
    0x5698b743214587a9c28c376a04951b2630cba10,
    0x458c9a621b730a78b2c341569059847632cba10,
    0x9a7652c8b14304859c37b26a0369874512cba10,
    0xa652341b78c903c267a95840b896374512cba10,
    0xa762341b8590487b256a9c30c896374512cba10,
    0x41b7a9856230a67843c2590b8c96374512cba10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_6 : Region 13 n13a_mask [6] 38 6 33 none :=
  of_certs (hn:=by decide) [
    0x437896521b84762b159a7c236a0458c903cba10,
    0x43789621b847652b159a7c236a0458c903cba10,
    0xb74896256734128b159a7c236a0458c903cba10,
    0xc21596348b7a056a987326741b2458c903cba10,
    0xc2596348b7a03789a65126741b2458c903cba10,
    0xc2598b736a03487a965126741b2458c903cba10,
    0xc21596348b7a06a9873256741b2458c903cba10,
    0xc215963487a06a98b73256741b2458c903cba10,
    0x59a7b84362137896a0c256741b2458c903cba10,
    0x59a784362137b896a0c256741b2458c903cba10,
    0xc21563789a0348b7a62596741b2458c903cba10,
    0x56a98b7321c0a784362596741b2458c903cba10,
    0x5698b732163487a0c259a6741b2458c903cba10,
    0xc26a987b154037658b25963412a748c903cba10,
    0xb89a6734521369587b265140c2a748c903cba10,
    0xb8736a95213458967b265140c2a748c903cba10,
    0xb873459621589a67b2365140c2a748c903cba10,
    0xb876a95216985437b2365140c2a748c903cba10,
    0x9a7b8c2156340c95841b2376a069874523cba10,
    0x589623741259a78b1c04567b2a6348c903cba10,
    0xa7654321b8c90c2b736a95840698741523cba10,
    0xc95412b8736a09a7658c234069847b1523cba10,
    0xc95432b876a09a73658c214069847b1523cba10,
    0xc958b214376a09a78c26540369847b1523cba10,
    0xc9a7658b2140a632c874590698437b1523cba10,
    0xa769c2b8540c87412365906a98437b1523cba10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_7 : Region 13 n13a_mask [7] 38 7 32 none :=
  of_certs (hn:=by decide) [
    0xa73c98b25406587b129a6741596348c032cba10,
    0xa678b125406589a7b29c3741596348c032cba10,
    0xb89a765216a04587b29c3741596348c032cba10,
    0xb876a9521b7a0456289c3741596348c032cba10,
    0xc8b21547369a043c98526a7b1876590432cba10,
    0x589a7b21452678b13c96a047956348c032cba10,
    0xc89634512b7a0b856a9c37418762590432cba10,
    0xc8963451b7a02b856a9c37418762590432cba10,
    0xc3476512b89a0458c9637b187a62590432cba10,
    0xc347651b89a0458c9637b2187a62590432cba10,
    0xc374126589a0548c96a7b13678b2590432cba10,
    0xc96215847a0456a98c37b13678b2590432cba10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_8 : Region 13 n13a_mask [8] 38 8 31 none :=
  of_certs (hn:=by decide) [
    0xc9a78562b14305967b8c3216a098473452cba10,
    0xc9a78b15623043c85967b216a098473452cba10,
    0xc9a7658b21430b78c3695126a098473452cba10,
    0x9a78b2651430b76958c3216a0c98473452cba10,
    0xb87a956234158c30967b216a0c98473452cba10,
    0x95678b2143058c369a7b126a0c98473452cba10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_9 : Region 13 n13a_mask [9] 38 9 30 none :=
  of_certs (hn:=by decide) [
    0x9c8b215637404859a67b1987a0c3263452cba10,
    0x9c8b21567404859a637b1987a0c3263452cba10,
    0x98b215674048c9a637b19587a0c3263452cba10] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13a_13 : Region 13 n13a_mask [13] 38 13 26 none :=
  of_certs (hn:=by decide) [
    0xc9a7658b1234095148c37b26a036987452cba10] (by rfl)

private theorem n13a_root : Region 13 n13a_mask [] 39 3 39 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13a_3
  · exact n13a_4
  · exact n13a_5
  · exact n13a_6
  · exact n13a_7
  · exact n13a_8
  · exact n13a_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact n13a_13

private abbrev n13quick_mask : Nat := 0xfff000ffe003ff003fe00ff00fe03f03e0f0e32

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_3 : Region 13 n13quick_mask [3,3,3,3,3,3,3,3,3] 69 3 51 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_4 : Region 13 n13quick_mask [4,3,3,3,3,3,3,3,3] 69 4 50 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_5 : Region 13 n13quick_mask [5,3,3,3,3,3,3,3,3] 69 5 49 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_6 : Region 13 n13quick_mask [6,3,3,3,3,3,3,3,3] 69 6 48 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_7 : Region 13 n13quick_mask [7,3,3,3,3,3,3,3,3] 69 7 47 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_8 : Region 13 n13quick_mask [8,3,3,3,3,3,3,3,3] 69 8 46 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_9 : Region 13 n13quick_mask [9,3,3,3,3,3,3,3,3] 69 9 45 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_3_10 : Region 13 n13quick_mask [10,3,3,3,3,3,3,3,3] 69 10 44 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3_3_3_3_3_3_3 : Region 13 n13quick_mask [3,3,3,3,3,3,3,3] 70 3 54 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_3_3_3_3_3_3_3
  · exact n13quick_3_3_3_3_3_3_3_3_4
  · exact n13quick_3_3_3_3_3_3_3_3_5
  · exact n13quick_3_3_3_3_3_3_3_3_6
  · exact n13quick_3_3_3_3_3_3_3_3_7
  · exact n13quick_3_3_3_3_3_3_3_3_8
  · exact n13quick_3_3_3_3_3_3_3_3_9
  · exact n13quick_3_3_3_3_3_3_3_3_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_4 : Region 13 n13quick_mask [4,3,3,3,3,3,3,3] 70 4 53 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_5 : Region 13 n13quick_mask [5,3,3,3,3,3,3,3] 70 5 52 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_6 : Region 13 n13quick_mask [6,3,3,3,3,3,3,3] 70 6 51 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_7 : Region 13 n13quick_mask [7,3,3,3,3,3,3,3] 70 7 50 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_8 : Region 13 n13quick_mask [8,3,3,3,3,3,3,3] 70 8 49 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_9 : Region 13 n13quick_mask [9,3,3,3,3,3,3,3] 70 9 48 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_10 : Region 13 n13quick_mask [10,3,3,3,3,3,3,3] 70 10 47 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_3_11 : Region 13 n13quick_mask [11,3,3,3,3,3,3,3] 70 11 46 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3_3_3_3_3_3 : Region 13 n13quick_mask [3,3,3,3,3,3,3] 71 3 57 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_3_3_3_3_3_3
  · exact n13quick_3_3_3_3_3_3_3_4
  · exact n13quick_3_3_3_3_3_3_3_5
  · exact n13quick_3_3_3_3_3_3_3_6
  · exact n13quick_3_3_3_3_3_3_3_7
  · exact n13quick_3_3_3_3_3_3_3_8
  · exact n13quick_3_3_3_3_3_3_3_9
  · exact n13quick_3_3_3_3_3_3_3_10
  · exact n13quick_3_3_3_3_3_3_3_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_4 : Region 13 n13quick_mask [4,3,3,3,3,3,3] 71 4 56 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_5 : Region 13 n13quick_mask [5,3,3,3,3,3,3] 71 5 55 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_6 : Region 13 n13quick_mask [6,3,3,3,3,3,3] 71 6 54 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_7 : Region 13 n13quick_mask [7,3,3,3,3,3,3] 71 7 53 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_8 : Region 13 n13quick_mask [8,3,3,3,3,3,3] 71 8 52 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_9 : Region 13 n13quick_mask [9,3,3,3,3,3,3] 71 9 51 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_10 : Region 13 n13quick_mask [10,3,3,3,3,3,3] 71 10 50 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_11 : Region 13 n13quick_mask [11,3,3,3,3,3,3] 71 11 49 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_3_12 : Region 13 n13quick_mask [12,3,3,3,3,3,3] 71 12 48 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3_3_3_3_3 : Region 13 n13quick_mask [3,3,3,3,3,3] 72 3 60 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_3_3_3_3_3
  · exact n13quick_3_3_3_3_3_3_4
  · exact n13quick_3_3_3_3_3_3_5
  · exact n13quick_3_3_3_3_3_3_6
  · exact n13quick_3_3_3_3_3_3_7
  · exact n13quick_3_3_3_3_3_3_8
  · exact n13quick_3_3_3_3_3_3_9
  · exact n13quick_3_3_3_3_3_3_10
  · exact n13quick_3_3_3_3_3_3_11
  · exact n13quick_3_3_3_3_3_3_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_4 : Region 13 n13quick_mask [4,3,3,3,3,3] 72 4 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_5 : Region 13 n13quick_mask [5,3,3,3,3,3] 72 5 58 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_6 : Region 13 n13quick_mask [6,3,3,3,3,3] 72 6 57 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_7 : Region 13 n13quick_mask [7,3,3,3,3,3] 72 7 56 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xd] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_8 : Region 13 n13quick_mask [8,3,3,3,3,3] 72 8 55 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_9 : Region 13 n13quick_mask [9,3,3,3,3,3] 72 9 54 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_10 : Region 13 n13quick_mask [10,3,3,3,3,3] 72 10 53 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_11 : Region 13 n13quick_mask [11,3,3,3,3,3] 72 11 52 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_3_12 : Region 13 n13quick_mask [12,3,3,3,3,3] 72 12 51 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3_3_3_3 : Region 13 n13quick_mask [3,3,3,3,3] 73 3 63 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_3_3_3_3
  · exact n13quick_3_3_3_3_3_4
  · exact n13quick_3_3_3_3_3_5
  · exact n13quick_3_3_3_3_3_6
  · exact n13quick_3_3_3_3_3_7
  · exact n13quick_3_3_3_3_3_8
  · exact n13quick_3_3_3_3_3_9
  · exact n13quick_3_3_3_3_3_10
  · exact n13quick_3_3_3_3_3_11
  · exact n13quick_3_3_3_3_3_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_4 : Region 13 n13quick_mask [4,3,3,3,3] 73 4 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_5 : Region 13 n13quick_mask [5,3,3,3,3] 73 5 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x401,
    0x601] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_6 : Region 13 n13quick_mask [6,3,3,3,3] 73 6 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_7 : Region 13 n13quick_mask [7,3,3,3,3] 73 7 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x97] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_8 : Region 13 n13quick_mask [8,3,3,3,3] 73 8 58 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xe01,
    0x1001] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_9 : Region 13 n13quick_mask [9,3,3,3,3] 73 9 57 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_10 : Region 13 n13quick_mask [10,3,3,3,3] 73 10 56 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_3_11 : Region 13 n13quick_mask [11,3,3,3,3] 73 11 55 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3_3_3 : Region 13 n13quick_mask [3,3,3,3] 74 3 66 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_3_3_3
  · exact n13quick_3_3_3_3_4
  · exact n13quick_3_3_3_3_5
  · exact n13quick_3_3_3_3_6
  · exact n13quick_3_3_3_3_7
  · exact n13quick_3_3_3_3_8
  · exact n13quick_3_3_3_3_9
  · exact n13quick_3_3_3_3_10
  · exact n13quick_3_3_3_3_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_4 : Region 13 n13quick_mask [4,3,3,3] 74 4 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_5 : Region 13 n13quick_mask [5,3,3,3] 74 5 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x40f,
    0x2401,
    0x60f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_6 : Region 13 n13quick_mask [6,3,3,3] 74 6 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x80d] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_7 : Region 13 n13quick_mask [7,3,3,3] 74 7 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xa0d,
    0xc0d] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_8 : Region 13 n13quick_mask [8,3,3,3] 74 8 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x3001,
    0xe0f,
    0x100f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_9 : Region 13 n13quick_mask [9,3,3,3] 74 9 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_10 : Region 13 n13quick_mask [10,3,3,3] 74 10 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_3_11 : Region 13 n13quick_mask [11,3,3,3] 74 11 58 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3_3 : Region 13 n13quick_mask [3,3,3] 75 3 69 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_3_3
  · exact n13quick_3_3_3_4
  · exact n13quick_3_3_3_5
  · exact n13quick_3_3_3_6
  · exact n13quick_3_3_3_7
  · exact n13quick_3_3_3_8
  · exact n13quick_3_3_3_9
  · exact n13quick_3_3_3_10
  · exact n13quick_3_3_3_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_4 : Region 13 n13quick_mask [4,4,3,3] 74 4 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x239,
    0xc39] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_5 : Region 13 n13quick_mask [5,4,3,3] 74 5 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_6 : Region 13 n13quick_mask [6,4,3,3] 74 6 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_7 : Region 13 n13quick_mask [7,4,3,3] 74 7 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xc43,
    0x2e07] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_8 : Region 13 n13quick_mask [8,4,3,3] 74 8 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x2b3] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_9 : Region 13 n13quick_mask [9,4,3,3] 74 9 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_10 : Region 13 n13quick_mask [10,4,3,3] 74 10 58 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_4_11 : Region 13 n13quick_mask [11,4,3,3] 74 11 57 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3_4 : Region 13 n13quick_mask [4,3,3] 75 4 68 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_4_4
  · exact n13quick_3_3_4_5
  · exact n13quick_3_3_4_6
  · exact n13quick_3_3_4_7
  · exact n13quick_3_3_4_8
  · exact n13quick_3_3_4_9
  · exact n13quick_3_3_4_10
  · exact n13quick_3_3_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_5 : Region 13 n13quick_mask [5,3,3] 75 5 67 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1809,
    0x1a09,
    0x1c09,
    0x1e09,
    0x2209,
    0x8e03,
    0x2e09,
    0x9003,
    0x1c0b,
    0x9803,
    0x220b,
    0xa001,
    0xaa01,
    0xae03,
    0xb401,
    0x2e0b,
    0xbc01,
    0xc201] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_6 : Region 13 n13quick_mask [6,3,3] 75 6 66 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x897,
    0xdc01,
    0xe001] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_7 : Region 13 n13quick_mask [7,3,3] 75 7 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x280d,
    0xa97,
    0x2e0d,
    0xca7,
    0xcb3] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_8 : Region 13 n13quick_mask [8,3,3] 75 8 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc01,
    0xfe01,
    0x10601,
    0x3017,
    0x10403] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_9 : Region 13 n13quick_mask [9,3,3] 75 9 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_10 : Region 13 n13quick_mask [10,3,3] 75 10 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x11003,
    0x11005] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_11 : Region 13 n13quick_mask [11,3,3] 75 11 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_3_12 : Region 13 n13quick_mask [12,3,3] 75 12 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_3 : Region 13 n13quick_mask [3,3] 76 3 72 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3_3
  · exact n13quick_3_3_4
  · exact n13quick_3_3_5
  · exact n13quick_3_3_6
  · exact n13quick_3_3_7
  · exact n13quick_3_3_8
  · exact n13quick_3_3_9
  · exact n13quick_3_3_10
  · exact n13quick_3_3_11
  · exact n13quick_3_3_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_4 : Region 13 n13quick_mask [4,4,4,3] 74 4 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x122b,
    0x162b,
    0x2c2b,
    0x1253,
    0x1635,
    0x1439] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_5 : Region 13 n13quick_mask [5,4,4,3] 74 5 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x127f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_6 : Region 13 n13quick_mask [6,4,4,3] 74 6 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_7 : Region 13 n13quick_mask [7,4,4,3] 74 7 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x2a39,
    0x2c35,
    0x2e39] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_8 : Region 13 n13quick_mask [8,4,4,3] 74 8 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_9 : Region 13 n13quick_mask [9,4,4,3] 74 9 58 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_10 : Region 13 n13quick_mask [10,4,4,3] 74 10 57 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_4_11 : Region 13 n13quick_mask [11,4,4,3] 74 11 56 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1653] (by rfl)

private theorem n13quick_3_4_4 : Region 13 n13quick_mask [4,4,3] 75 4 67 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_4_4_4
  · exact n13quick_3_4_4_5
  · exact n13quick_3_4_4_6
  · exact n13quick_3_4_4_7
  · exact n13quick_3_4_4_8
  · exact n13quick_3_4_4_9
  · exact n13quick_3_4_4_10
  · exact n13quick_3_4_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_5 : Region 13 n13quick_mask [5,4,3] 75 5 66 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x167f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_6 : Region 13 n13quick_mask [6,4,3] 75 6 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_7 : Region 13 n13quick_mask [7,4,3] 75 7 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1497,
    0x2e43,
    0x2c53,
    0x16a5,
    0xf607] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_8 : Region 13 n13quick_mask [8,4,3] 75 8 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x16ad,
    0x14b3] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_9 : Region 13 n13quick_mask [9,4,3] 75 9 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x16b5] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_10 : Region 13 n13quick_mask [10,4,3] 75 10 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x11007] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_4_11 : Region 13 n13quick_mask [11,4,3] 75 11 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3_4 : Region 13 n13quick_mask [4,3] 76 4 71 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_4_4
  · exact n13quick_3_4_5
  · exact n13quick_3_4_6
  · exact n13quick_3_4_7
  · exact n13quick_3_4_8
  · exact n13quick_3_4_9
  · exact n13quick_3_4_10
  · exact n13quick_3_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_5 : Region 13 n13quick_mask [5,3] 76 5 70 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8e09,
    0x9009,
    0x9209,
    0x9409,
    0x1a55,
    0x9809,
    0x9a09,
    0x1a59,
    0xa609,
    0x1e55,
    0xae09,
    0xba09,
    0x8e15,
    0xf609,
    0x10409,
    0x11009,
    0x920b,
    0x9015,
    0x940b,
    0x1ab3,
    0x980b,
    0x9a0b,
    0x9815,
    0x207f,
    0xa60b,
    0x20ad,
    0x1eb3,
    0xae0b,
    0xa00f,
    0xa40d,
    0xba0b,
    0x2475,
    0xaa0f,
    0xaa17,
    0xae15,
    0x267f,
    0x248d,
    0xb40f,
    0xb60d,
    0xb80d,
    0x2c7f,
    0xf60b,
    0x3075,
    0xbc0f,
    0xc20f,
    0x26ad,
    0x1040b,
    0x1100b,
    0xc217] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_6 : Region 13 n13quick_mask [6,3] 76 6 69 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xce0d,
    0xd60d,
    0xd80d,
    0x308d,
    0xdc0f,
    0xe00f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_7 : Region 13 n13quick_mask [7,3] 76 7 68 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xe60d,
    0xea0d,
    0xee0d,
    0xf40d,
    0xf60d,
    0x1100d,
    0x2e9d,
    0x2ab3,
    0x2ea7,
    0xfa0f,
    0x2eb3,
    0x32a3,
    0xf217,
    0xfa17,
    0xfa19] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_8 : Region 13 n13quick_mask [8,3] 76 8 67 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc0f,
    0xfc11,
    0xfc13,
    0x30a9,
    0xfe0f,
    0x1060f,
    0x32a9,
    0xfe17,
    0x10415,
    0x10617,
    0x10619,
    0x1230e4b7886c0b0d694f2461528ec387705138c8142ea6f61848b2d47364cb590826f8a37500420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_9 : Region 13 n13quick_mask [9,3] 76 9 66 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x10817,
    0x10a15,
    0x10c17,
    0x10c19,
    0x10e17,
    0x10e19,
    0xa4f231678c81936b0ce8744d6982f413063524c196ea90e1646b2d49262cb590486f8a37500420,
    0x138570c74e80aed669835258d4922e0b06312e4c196a90f61446b2c97262cb590486f8a37500420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_10 : Region 13 n13quick_mask [10,3] 76 10 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x11015,
    0x11017,
    0x11019,
    0xf0c547738280af64878d5218942ed6b1250326c1968a4f41706b2c92e62cb590864f8a37500420,
    0xf72346984c0b6738d0e9456c7830a8125134cea196842f41706b2c92e62cb590864f8a37500420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_11 : Region 13 n13quick_mask [11,3] 76 11 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_3_12 : Region 13 n13quick_mask [12,3] 76 12 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_3 : Region 13 n13quick_mask [3] 77 3 75 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3_3
  · exact n13quick_3_4
  · exact n13quick_3_5
  · exact n13quick_3_6
  · exact n13quick_3_7
  · exact n13quick_3_8
  · exact n13quick_3_9
  · exact n13quick_3_10
  · exact n13quick_3_11
  · exact n13quick_3_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_4 : Region 13 n13quick_mask [4,4,4,4,4,4,4,4] 70 4 46 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x341b,
    0x341d,
    0x341f,
    0x3421,
    0x361b,
    0x361d,
    0x3425,
    0x381b,
    0x3a1b,
    0x361f,
    0x3427,
    0x3a1d,
    0x3621,
    0x381f,
    0x3c1b,
    0x3429,
    0x3a1f,
    0x3c1d,
    0x3625,
    0x3a21,
    0x3e1b,
    0x401b,
    0x421b,
    0x3c1f,
    0x3627,
    0x342d,
    0x401d,
    0x3c21,
    0x3a25,
    0x441b,
    0x461b,
    0x3e1f,
    0x4a1b,
    0x4c1b,
    0x3629,
    0x401f,
    0x3a27,
    0x3439,
    0x4a1d,
    0x4c1d,
    0x3c25,
    0x4021,
    0x4e1b,
    0x501b,
    0x461f,
    0x541b,
    0x561b,
    0x4a1f,
    0x3c27,
    0x362d,
    0x3a29,
    0x4c1f,
    0x541d,
    0x4a21,
    0x4025,
    0x4c21,
    0x3631,
    0x5c1b,
    0x5e1b,
    0x501f,
    0x621b,
    0x641b,
    0x661b,
    0x3c29,
    0x541f,
    0x4027,
    0x3639,
    0x3a2d,
    0x621d,
    0x641d,
    0x4a25,
    0x5421,
    0x3a2f,
    0x761b,
    0x781b,
    0x7a1b,
    0x7c1b,
    0x7e1b,
    0x5c1f,
    0x801b,
    0x861b,
    0x881b,
    0x8c1b,
    0x621f,
    0x4a27,
    0x364b,
    0x364d,
    0x641f,
    0x3a37,
    0x661f,
    0x861d,
    0x8c1d,
    0x6221,
    0x5425,
    0x6421,
    0xc61b,
    0xc81b,
    0xca1b,
    0xd01b,
    0xd21b,
    0xdc1b,
    0xe21b,
    0xfc1b,
    0x1001b,
    0x1041b,
    0x1101b,
    0x4a29,
    0x861f,
    0x5427,
    0x881f,
    0x3a4b,
    0x3a4d,
    0x8c1f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_5 : Region 13 n13quick_mask [5,4,4,4,4,4,4,4] 70 5 45 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc1d,
    0x1001d,
    0x6225,
    0x8621,
    0x6425,
    0x8c21] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_6 : Region 13 n13quick_mask [6,4,4,4,4,4,4,4] 70 6 44 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x3e31,
    0x4031,
    0xc61f,
    0xc81f,
    0x388d,
    0x3e33,
    0xca1f,
    0xd01f,
    0xd21f,
    0x3a8d,
    0xdc1f,
    0x4033,
    0xe21f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_7 : Region 13 n13quick_mask [7,4,4,4,4,4,4,4] 70 7 43 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_8 : Region 13 n13quick_mask [8,4,4,4,4,4,4,4] 70 8 42 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc1f,
    0x6227,
    0x4a2d,
    0x3c4d,
    0x1001f,
    0x6427,
    0x1041f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_9 : Region 13 n13quick_mask [9,4,4,4,4,4,4,4] 70 9 41 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_10 : Region 13 n13quick_mask [10,4,4,4,4,4,4,4] 70 10 40 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1101f] (by rfl)

private theorem n13quick_4_4_4_4_4_4_4_11 : Region 13 n13quick_mask [11,4,4,4,4,4,4,4] 70 11 39 (some 39) := pruned_left (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_4_12 : Region 13 n13quick_mask [12,4,4,4,4,4,4,4] 70 12 38 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x3ab9] (by rfl)

private theorem n13quick_4_4_4_4_4_4_4 : Region 13 n13quick_mask [4,4,4,4,4,4,4] 71 4 50 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_4_4_4_4_4_4_4_4
  · exact n13quick_4_4_4_4_4_4_4_5
  · exact n13quick_4_4_4_4_4_4_4_6
  · exact n13quick_4_4_4_4_4_4_4_7
  · exact n13quick_4_4_4_4_4_4_4_8
  · exact n13quick_4_4_4_4_4_4_4_9
  · exact n13quick_4_4_4_4_4_4_4_10
  · exact n13quick_4_4_4_4_4_4_4_11
  · exact n13quick_4_4_4_4_4_4_4_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_5 : Region 13 n13quick_mask [5,4,4,4,4,4,4] 71 5 49 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x403b,
    0x403d,
    0xfc21,
    0x8625,
    0x10021,
    0x8c25] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_6 : Region 13 n13quick_mask [6,4,4,4,4,4,4] 71 6 48 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x4431,
    0x4631,
    0x4831,
    0x4a31,
    0x4c31,
    0xca23,
    0x4439,
    0xd023,
    0xd223,
    0x4633,
    0x3e47,
    0xe223,
    0x4639,
    0x3c8d,
    0x4a33,
    0x10423,
    0x4839,
    0x4c33] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_7 : Region 13 n13quick_mask [7,4,4,4,4,4,4] 71 7 47 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x602b] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_8 : Region 13 n13quick_mask [8,4,4,4,4,4,4] 71 8 46 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x6229,
    0x4047,
    0x8627,
    0x4a39,
    0x3cb9,
    0x6429,
    0x4051] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_9 : Region 13 n13quick_mask [9,4,4,4,4,4,4] 71 9 45 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8c27] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_4_10 : Region 13 n13quick_mask [10,4,4,4,4,4,4] 71 10 44 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x4c39,
    0x682b] (by rfl)

private theorem n13quick_4_4_4_4_4_4 : Region 13 n13quick_mask [4,4,4,4,4,4] 72 4 54 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_4_4_4_4_4_4_4
  · exact n13quick_4_4_4_4_4_4_5
  · exact n13quick_4_4_4_4_4_4_6
  · exact n13quick_4_4_4_4_4_4_7
  · exact n13quick_4_4_4_4_4_4_8
  · exact n13quick_4_4_4_4_4_4_9
  · exact n13quick_4_4_4_4_4_4_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_5 : Region 13 n13quick_mask [5,4,4,4,4,4] 72 5 53 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x4a3b,
    0x4c3b,
    0x4c3d,
    0xfc25,
    0x4075,
    0x10025,
    0x4079] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_6 : Region 13 n13quick_mask [6,4,4,4,4,4] 72 6 52 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x4e31,
    0x5031,
    0x5231,
    0x5431,
    0x5631,
    0x4447,
    0x4e33,
    0x3e8d,
    0x5033,
    0x4087,
    0x4e39,
    0x4647,
    0x5039,
    0x4651,
    0x408d,
    0x4847,
    0x5433,
    0x5633,
    0x4293] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_7 : Region 13 n13quick_mask [7,4,4,4,4,4] 72 7 51 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x822b] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_8 : Region 13 n13quick_mask [8,4,4,4,4,4] 72 8 50 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x4a47,
    0xfc27,
    0x4a4b,
    0x8629,
    0x4c47,
    0x10027,
    0x5439,
    0x42b3,
    0x642d] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_9 : Region 13 n13quick_mask [9,4,4,4,4,4] 72 9 49 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8c29] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_10 : Region 13 n13quick_mask [10,4,4,4,4,4] 72 10 48 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x4c51] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_4_11 : Region 13 n13quick_mask [11,4,4,4,4,4] 72 11 47 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_4_4_4_4_4 : Region 13 n13quick_mask [4,4,4,4,4] 73 4 58 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_4_4_4_4_4_4
  · exact n13quick_4_4_4_4_4_5
  · exact n13quick_4_4_4_4_4_6
  · exact n13quick_4_4_4_4_4_7
  · exact n13quick_4_4_4_4_4_8
  · exact n13quick_4_4_4_4_4_9
  · exact n13quick_4_4_4_4_4_10
  · exact n13quick_4_4_4_4_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_5 : Region 13 n13quick_mask [5,4,4,4,4] 73 5 57 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x543b,
    0x543d,
    0x4a75,
    0x622f,
    0x4c75,
    0x642f,
    0x4c79] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_6 : Region 13 n13quick_mask [6,4,4,4,4] 73 6 56 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x4481,
    0x4681,
    0x5e31,
    0x4881,
    0x6231,
    0x6431,
    0x6631,
    0x44ab,
    0x4887,
    0x468d,
    0x4e47,
    0x468f,
    0x5e33,
    0x5047,
    0x5051,
    0x5c39,
    0x5e39,
    0x4a8d,
    0x6233,
    0x5247,
    0x48b3,
    0x6433,
    0x6633] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_7 : Region 13 n13quick_mask [7,4,4,4,4] 73 7 55 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xe82b,
    0xfa2b] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_8 : Region 13 n13quick_mask [8,4,4,4,4] 73 8 54 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc29,
    0x5447,
    0x6237,
    0x6239,
    0x862d,
    0x10029,
    0x5451,
    0x6437,
    0x6439,
    0x1062b] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_9 : Region 13 n13quick_mask [9,4,4,4,4] 73 9 53 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_10 : Region 13 n13quick_mask [10,4,4,4,4] 73 10 52 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x6639] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_11 : Region 13 n13quick_mask [11,4,4,4,4] 73 11 51 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_4_12 : Region 13 n13quick_mask [12,4,4,4,4] 73 12 50 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8c2d] (by rfl)

private theorem n13quick_4_4_4_4 : Region 13 n13quick_mask [4,4,4,4] 74 4 62 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_4_4_4_4_4
  · exact n13quick_4_4_4_4_5
  · exact n13quick_4_4_4_4_6
  · exact n13quick_4_4_4_4_7
  · exact n13quick_4_4_4_4_8
  · exact n13quick_4_4_4_4_9
  · exact n13quick_4_4_4_4_10
  · exact n13quick_4_4_4_4_11
  · exact n13quick_4_4_4_4_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_5 : Region 13 n13quick_mask [5,4,4,4] 74 5 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x623b,
    0x643b,
    0x643d,
    0x623f,
    0x5475,
    0x862f,
    0x5479,
    0x8c2f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_6 : Region 13 n13quick_mask [6,4,4,4] 74 6 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x7631,
    0x7831,
    0x7a31,
    0x7c31,
    0x7e31,
    0x5281,
    0x8031,
    0x8631,
    0x8831,
    0x8c31,
    0x4e8d,
    0x7a33,
    0x7839,
    0x508d,
    0x7c33,
    0x5487,
    0x7a39,
    0x7e33,
    0x5c47,
    0x7c39,
    0x5c51,
    0x8033,
    0x548d,
    0x568d,
    0x8633,
    0x8833,
    0x5693,
    0x8039,
    0x8c33] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_7 : Region 13 n13quick_mask [7,4,4,4] 74 7 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x6053,
    0x8235] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_8 : Region 13 n13quick_mask [8,4,4,4] 74 8 58 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x6247,
    0x6249,
    0xfc2d,
    0x624d,
    0x6447,
    0x8637,
    0x8639,
    0x8839,
    0x1002d,
    0x644d,
    0x6451] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_9 : Region 13 n13quick_mask [9,4,4,4] 74 9 57 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8c37] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_10 : Region 13 n13quick_mask [10,4,4,4] 74 10 56 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1102d,
    0x8c39,
    0x6853] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_4_11 : Region 13 n13quick_mask [11,4,4,4] 74 11 55 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xed86b370281384f0b6d4876f8854330c7520c3968ae70562a14f2c924cb59062e98a4175006420] (by rfl)

private theorem n13quick_4_4_4 : Region 13 n13quick_mask [4,4,4] 75 4 66 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_4_4_4_4
  · exact n13quick_4_4_4_5
  · exact n13quick_4_4_4_6
  · exact n13quick_4_4_4_7
  · exact n13quick_4_4_4_8
  · exact n13quick_4_4_4_9
  · exact n13quick_4_4_4_10
  · exact n13quick_4_4_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_5 : Region 13 n13quick_mask [5,4,4] 75 5 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x5a61,
    0x5a6d,
    0x587f,
    0x5a73,
    0x863b,
    0x8c3b,
    0x8c3d,
    0x607f,
    0x6275,
    0xfc2f,
    0x6475,
    0x1002f,
    0x6479,
    0x5ab5,
    0x5ab7,
    0x687f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_6 : Region 13 n13quick_mask [6,4,4] 75 6 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xc631,
    0xc831,
    0xca31,
    0xd031,
    0xd231,
    0xdc31,
    0xe231,
    0xfc31,
    0x10031,
    0x10431,
    0x11031,
    0x7847,
    0xc839,
    0xca33,
    0x5c8d,
    0x7a47,
    0xd033,
    0xd233,
    0xca39,
    0x7c47,
    0xdc33,
    0xd039,
    0xd239,
    0xe233,
    0xd839,
    0x628d,
    0xfc33,
    0x668d,
    0xdc39,
    0x10033,
    0x10433,
    0x8a41,
    0x11033] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_7 : Region 13 n13quick_mask [7,4,4] 75 7 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xe835,
    0x8445,
    0xee39,
    0x8253,
    0xfa35,
    0x8a45,
    0xf639] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_8 : Region 13 n13quick_mask [8,4,4] 75 8 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x62a9,
    0x8647,
    0xfc37,
    0xfc39,
    0x62b9,
    0x864d,
    0x8c47,
    0x10037,
    0x10039,
    0x10635,
    0x10439,
    0x8c4b] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_9 : Region 13 n13quick_mask [9,4,4] 75 9 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8c4d] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_10 : Region 13 n13quick_mask [10,4,4] 75 10 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x11039,
    0x8c51] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_4_11 : Region 13 n13quick_mask [11,4,4] 75 11 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_4_4 : Region 13 n13quick_mask [4,4] 76 4 70 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_4_4_4
  · exact n13quick_4_4_5
  · exact n13quick_4_4_6
  · exact n13quick_4_4_7
  · exact n13quick_4_4_8
  · exact n13quick_4_4_9
  · exact n13quick_4_4_10
  · exact n13quick_4_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_5 : Region 13 n13quick_mask [5,4] 76 5 69 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x6a7f,
    0x8a59,
    0x8a61,
    0x6c7f,
    0x706d,
    0x7073,
    0xe63d,
    0xf43d,
    0xfc3b,
    0x1003b,
    0x1003d,
    0x8a6d,
    0x727f,
    0x747f,
    0x8a73,
    0x6e9f,
    0x827f,
    0x847f,
    0x6eb9,
    0xfc3f,
    0x8675,
    0x1003f,
    0x8c75,
    0x8c77,
    0x70b5,
    0x8a7b,
    0x8a7f,
    0x8c79] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_6 : Region 13 n13quick_mask [6,4] 76 6 68 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x7681,
    0x7683,
    0x7685,
    0x7881,
    0x7687,
    0x7883,
    0x7a81,
    0x7689,
    0x7885,
    0x7c81,
    0x7e81,
    0x7887,
    0x7e83,
    0x76ab,
    0x8081,
    0x7889,
    0x7e85,
    0x8681,
    0xc647,
    0x8c81,
    0xc651,
    0x8c83,
    0xc847,
    0xc851,
    0x7a93,
    0x8087,
    0x7e89,
    0x8c85,
    0x7c8d,
    0x7e8d,
    0xca47,
    0x8887,
    0x7e8f,
    0xca51,
    0x7e9f,
    0xd047,
    0xd247,
    0xd051,
    0xd251,
    0x8093,
    0x8095,
    0x8c89,
    0xd843,
    0xda45,
    0x80a7,
    0x8c8b,
    0x868d,
    0xdc47,
    0x8c8d,
    0xe247,
    0x8893,
    0x80b3,
    0x8c8f,
    0x10841,
    0xe251] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_7 : Region 13 n13quick_mask [7,4] 76 7 67 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xee43,
    0xe651,
    0xe853,
    0x82a5,
    0xf643,
    0x82ad,
    0xf245,
    0xfa45,
    0x11043,
    0x8c9f,
    0x10845,
    0x10c45,
    0xf44d,
    0xf451,
    0xf64f,
    0xfa53] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_8 : Region 13 n13quick_mask [8,4] 76 8 66 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc47,
    0xfc49,
    0xfc4b,
    0xfc4d,
    0x10047,
    0x10049,
    0x10447,
    0x11047,
    0x1004b,
    0x1004d,
    0x10051,
    0x8caf,
    0x1104b,
    0x10451,
    0x10653,
    0xd0f347896a0cf4523970876c30a4e8126d9304142ea85816e6b2d49364cb590628f8a375006420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_9 : Region 13 n13quick_mask [9,4] 76 9 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8ab5,
    0x8ab7,
    0x10a51,
    0x10c53,
    0x10e53,
    0xce9075256a12f0a4c796818c877122f45936d0340ea83816e6b2d49262cb590484f8a375006420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_10 : Region 13 n13quick_mask [10,4] 76 10 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1104f,
    0x11051,
    0x11053,
    0xc6b6f099240f4c32b16780a8c5834712152830578cea541686f2cb7262e9590c84f8a375006420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_11 : Region 13 n13quick_mask [11,4] 76 11 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_4_12 : Region 13 n13quick_mask [12,4] 76 12 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8cb9] (by rfl)

private theorem n13quick_4 : Region 13 n13quick_mask [4] 77 4 74 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_4_4
  · exact n13quick_4_5
  · exact n13quick_4_6
  · exact n13quick_4_7
  · exact n13quick_4_8
  · exact n13quick_4_9
  · exact n13quick_4_10
  · exact n13quick_4_11
  · exact n13quick_4_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_5_5 : Region 13 n13quick_mask [5,5,5] 75 5 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x8e55,
    0x8e57,
    0x8e59,
    0x8e5b,
    0x8e5d,
    0x8e5f,
    0x9055,
    0x8e63,
    0x9057,
    0x9255,
    0x9059,
    0x8e65,
    0x905b,
    0x905d,
    0x8e67,
    0x9455,
    0x905f,
    0x8e6b,
    0x9855,
    0x9063,
    0x9857,
    0x9a55,
    0x9459,
    0x8e77,
    0x9859,
    0x9065,
    0x8e7f,
    0x985b,
    0x985d,
    0x9067,
    0xa655,
    0x985f,
    0x906b,
    0xae55,
    0x8eb9,
    0x9863,
    0xae57,
    0xba55,
    0xa659,
    0x9077,
    0xae59,
    0x9865,
    0x907f,
    0xae5b,
    0xae5d,
    0x9867,
    0xf655,
    0xae5f,
    0x10455,
    0x11055,
    0x90b9,
    0xae63,
    0x11057,
    0x92b3,
    0xf659,
    0xbe61,
    0x10459,
    0x10859,
    0x967f,
    0x11059,
    0xae65,
    0x987f,
    0x1105b,
    0x1105d,
    0xae67,
    0xa469,
    0x9a7b,
    0x1105f,
    0xae6b,
    0x98b3,
    0x10861,
    0x98b9,
    0x11063,
    0xae71,
    0xb669,
    0xb869,
    0x9ab3,
    0xa67b,
    0xbe6d,
    0xae77,
    0xaa7f,
    0x10b3678c83344ead706cf2904b46330e1884c5968a3413826b6f4d362e9590c06f8a05750086420,
    0xc06d,
    0xac7f,
    0xae7b,
    0x11065,
    0xae7f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_5_6 : Region 13 n13quick_mask [6,5,5] 75 6 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x9c81,
    0x9c83,
    0x9c85,
    0x9e81,
    0x9e83,
    0x9c89,
    0x9e85,
    0xa281,
    0xa283,
    0x9e89,
    0xa285,
    0x9e8f,
    0x9e9f,
    0xae87,
    0xa289,
    0xa28b,
    0xa08d,
    0xa28f,
    0xa29f,
    0xfc67,
    0xbe73,
    0xc073,
    0xae93,
    0x11067,
    0xa2b9] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_5_7 : Region 13 n13quick_mask [7,5,5] 75 7 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xe669,
    0xea69,
    0xf469,
    0xa89f,
    0xb879,
    0xba7b,
    0xaea7,
    0xa8b9,
    0xf674528b902c0a5172f48c7808e70a334d78414392cf096a636130c4eb589262f8ca5750086420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_5_8 : Region 13 n13quick_mask [8,5,5] 75 8 60 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc6b,
    0xbc75,
    0x1006b,
    0xbc7f,
    0x1106b,
    0xaeb3,
    0xc477,
    0x17228b944c6e0a534c36f0980b674e850d3830a7968cf2143260d7184eb493062f8ca5750086420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_5_9 : Region 13 n13quick_mask [9,5,5] 75 9 59 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1086d,
    0xc07f,
    0xc479] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_5_10 : Region 13 n13quick_mask [10,5,5] 75 10 58 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xaeb9] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_5_11 : Region 13 n13quick_mask [11,5,5] 75 11 57 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xc27f] (by rfl)

private theorem n13quick_5_5 : Region 13 n13quick_mask [5,5] 76 5 68 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_5_5_5
  · exact n13quick_5_5_6
  · exact n13quick_5_5_7
  · exact n13quick_5_5_8
  · exact n13quick_5_5_9
  · exact n13quick_5_5_10
  · exact n13quick_5_5_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_6 : Region 13 n13quick_mask [6,5] 76 6 67 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x18d734e6916b9274b0572a70c4979122ce594388af02e84ac16f2d406c9441262f80a3750086420,
    0x197530eca864211874c32c58e7364eb94f70838d0522e94a628d6b21699500c70a40f28540a3660,
    0x124d86f4b1682b972907390d6a567530ce594388af02e84ac16f2d406c9441262f80a3750086420,
    0xb081,
    0xb083,
    0x108ca52e6395602a7456990ed39734c670c592d8af638e8341302e40f4b6c0851660a86420b1492,
    0xb085,
    0x186b29056cf4296b0d946e5230eb93662c597188b530e84ac16f2d406c9441262f80a3750086420,
    0xb281,
    0xb283,
    0xb089,
    0xe74a9383164c134eb8d670482d0e9724a794396b309184ecb6f2d406c9441262f80a3750086420,
    0xb285,
    0x4f68c63592a0c4839172ea617530eca8642090a58e18b6d490578c2e714a34763210d27814e924,
    0xc481,
    0xc483,
    0xb289,
    0xe790b234568c0ceb9734704830ca92f6605833890f416c6a5712d4a4e958d262f80a3750086420,
    0xc485,
    0xe70c8b7934418af476c30925698330ec06a5186cb361428516f2d4a4e958d262f80a3750086420,
    0xb28f,
    0xb29f,
    0xb48d,
    0x1106f,
    0xc489,
    0x1870b6c5228f41390964e74ac170ceb8352840f788b3054c60a772f02c9585262f8ca3750086420,
    0x11071,
    0xc48b,
    0xe499432b6c60d5250b86e9613784cf028b419290caf47640a72f7182c9453062f8ca3750086420,
    0xbc8d,
    0xc28d,
    0xc48f,
    0x10873,
    0x10c73] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_7 : Region 13 n13quick_mask [7,5] 76 7 66 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xb697,
    0xb699,
    0xb69b,
    0xb69f,
    0xb897,
    0xe679,
    0xe87f,
    0xee7f,
    0xc49f,
    0xbab3,
    0xc2a3,
    0xf479,
    0xf27f,
    0xf67b,
    0xfa7f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_8 : Region 13 n13quick_mask [8,5] 76 8 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfc75,
    0xfc77,
    0xfe75,
    0x10075,
    0xfc7f,
    0x10077,
    0x10079,
    0xfe7f,
    0xbeb5,
    0xbeb7,
    0x10279,
    0x11077,
    0x1067f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_9 : Region 13 n13quick_mask [9,5] 76 9 64 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1345166ca8372b0e78c528ed60b46f30c1884a596903413826b6f4d2e2c9590604f8a3750086420,
    0xc0b5,
    0x1087b,
    0x1087f,
    0x10c7f,
    0x10e7f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_10 : Region 13 n13quick_mask [10,5] 76 10 63 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1107b,
    0x1107d,
    0x1107f] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_11 : Region 13 n13quick_mask [11,5] 76 11 62 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xc4b9] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_5_12 : Region 13 n13quick_mask [12,5] 76 12 61 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x144c7097922ae1034d728e78a184f4770d2a8213588cf056a641912f62cb485262f8c1750a86420] (by rfl)

private theorem n13quick_5 : Region 13 n13quick_mask [5] 77 5 73 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_5_5
  · exact n13quick_5_6
  · exact n13quick_5_7
  · exact n13quick_5_8
  · exact n13quick_5_9
  · exact n13quick_5_10
  · exact n13quick_5_11
  · exact n13quick_5_12
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_6 : Region 13 n13quick_mask [6] 77 6 72 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x1890b47792506ce57318a4d70b34e832859438caf0296a6e16f2d406c9441262f80c37500a86420,
    0xb4ec537078830d792a4e918a5675312859438caf0296a6e16f2d406c9441262f80c37500a86420,
    0xb24ed787082d1738a5188f4a5675312859438caf0296a6e16f2d406c9441262f80c37500a86420,
    0xc681,
    0xc683,
    0xc881,
    0x197530eca86420f6a54392d012b08e76925074b857098ea636c74e372e4c123194094c2a078c840,
    0x14784d708eb2394ed077284a2f0b9250299658cb53096a6e16f2d406c9441262f80c37500a86420,
    0xc685,
    0x14770ce52b88394e936c4b02af059229079658cb53096a6e16f2d406c9441262f80c37500a86420,
    0xca81,
    0xcc81,
    0xc687,
    0xca83,
    0xcc83,
    0xd081,
    0xd281,
    0xc689,
    0xf4a338d6704810c569346eb828f1724a794396b309184ecb6f2d406c9441262f80c37500a86420,
    0x138b4e84d67038d0569346ea280f1724a794396b309184ecb6f2d406c9441262f80c37500a86420,
    0xca85,
    0xcc85,
    0x128e76b58c502b9257074e083530d684a783972af09184ecb6f2d406c9441262f80c37500a86420,
    0xdc81,
    0xe281,
    0xe481,
    0xca87,
    0xe283,
    0xe483,
    0xfc81,
    0x10081,
    0x10481,
    0x11081,
    0xca89,
    0xcc89,
    0x14764cf0b3828178cb523084e0ae96d250794389370d4e6a5912f6a6c9441262f80c37500a86420,
    0xae50794d72834b080ed965230e96752ac582992d1614e6a5912f6a6c9441262f80c37500a86420,
    0xe285,
    0xe485,
    0x16990324ca6e1478d2b056e80ed67093582a5936af0d42859712f4a6c9441262f80c37500a86420,
    0xca8d,
    0xdc87,
    0xca8f,
    0xcc8f,
    0xd489,
    0xe287,
    0xca9f,
    0xcc9f,
    0xd08d,
    0xfc87,
    0xd08f,
    0x10087,
    0x10487,
    0x11087,
    0xe289,
    0xe489,
    0x18336b4ce70480eb12d8745682f5290d78a605388f16142ac4b20f66c958526318ec37500a86420,
    0x98ac5734f060508e74b2d780e386b6930d4538ceb1614284a320f66c958526318ec37500a86420,
    0xce97,
    0xce99,
    0xce9b,
    0xe28b,
    0xe48b,
    0x96a78334ec406f09364ad5812d788e2b4704eb38d16142858b12f66c944126318ec37500a86420,
    0xdc8d,
    0xfc89,
    0xe28d,
    0xdc93,
    0xd2b3,
    0x10689,
    0xe28f,
    0xe48f,
    0x10a89,
    0xe293,
    0xf8d7290a4d5389654b6722854797130ce85826caf0416e6b2c12f42c8159062e18a37500a86420,
    0xd73890a4f8d529654b6722854797130ce85826caf0416e6b2c12f42c8159062e18a37500a86420,
    0xd697,
    0xd699,
    0xd897,
    0xd69b,
    0xd8a7,
    0xd8b3,
    0xdaa3,
    0xdaa5,
    0xe29f,
    0xe49f,
    0xdab5,
    0xdab7,
    0xfc8d,
    0xfe8d,
    0x1008d,
    0x1048d,
    0x1068d,
    0x1108d,
    0xe0ad,
    0x1008f,
    0xdeb5,
    0xdeb7,
    0x1048f,
    0x126e54838c14764ce92330c8196a570f2c2789850af4172a702f6d526cb590840f8a37500a86420,
    0x1108f,
    0x1478cf2b057280d0ea4d66e8334a73161884c596903413826b6f4d2e2c9590604f8a37500a86420,
    0x10891,
    0x11093,
    0x11095,
    0xe2b9,
    0xe4b9,
    0x127698b4502ec190b6d46e5281708f52c782a4d972af0142840712f62c9584a6338e1750ca86420,
    0x1276b94508ec178c93470a2e58806f4316d2582972af014c641912f62cb484a6338e1750ca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_7 : Region 13 n13quick_mask [7] 77 7 71 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x138d4af0529678ec7490a4e996552316e8582b6d12604c6b3612f42c8159062e18a37500ca86420,
    0xb874d2e8305610eca86421924b6c2b18934255076f8c491378f4970c14ae6c812a62e419563260,
    0xe697,
    0xc33949650ea616e384c74eca8642178f2542f5072a4d8770b58b730812990d60a26e84152c8300,
    0xe699,
    0xea97,
    0xe69b,
    0xee97,
    0xe69f,
    0xee99,
    0xf497,
    0xf697,
    0xee9b,
    0x11097,
    0xfa9b,
    0xeea5,
    0xf49f,
    0xf69d,
    0xf89f,
    0xfa9d,
    0xfa9f,
    0x1109b,
    0xecb5,
    0xecb7,
    0xeeb3,
    0xfaa1,
    0x137098f46c4e8c3930a58760b430ce7228596d52af056806b6f2d4412959062e18a37500ca86420,
    0x1089d,
    0x10a9f,
    0x10c9d,
    0xfaa5,
    0x1109d,
    0xf0b5,
    0xf0b7,
    0xf0b9,
    0xed85073682c934e4a6388e6d6522d1387614596af03480b16f2d4612b590840f8a37500ca86420,
    0xfaad,
    0x149672e4c30a138c74530e8196a570d282784388cf4172a702f6d526eb590840f8a37500ca86420,
    0xf6b3,
    0x108a3,
    0x10ca3,
    0x10ca5,
    0xf4b9,
    0x110a7,
    0xf8b9,
    0x18742b09256ce10778c552ae82f4b70d208582f8973014c6a4072f62c959046338a1750eca86420,
    0xfab9,
    0x19690a3472c4e107652b4d8e82eb7055280782990d7214e6a4112f62c9584c6338a1750eca86420,
    0x12d18296744e14d650af8728108e2b5378c418852b7034e60a712f62c9584c6338a1750eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_8 : Region 13 n13quick_mask [8] 77 8 70 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0xfca9,
    0xfcab,
    0xfcad,
    0xfcaf,
    0xfcb1,
    0xfcb3,
    0xfcb5,
    0xfcb7,
    0xfcb9,
    0x10c4b294e62e5370a782d68ea1527122c98566d8f05428196f2d4616b59084138a37500eca86420,
    0xfea9,
    0x100a9,
    0x100ab,
    0xfead,
    0x16930c6f44f826b36c522e8d8705340c2996784af03480b16f2d4616b59084138a37500eca86420,
    0x100af,
    0x104ab,
    0x106ad,
    0x110ab,
    0x100b9,
    0x102b9,
    0x196b0e945262c0a5074f38c96350c4f72807829857014c6b2212d66eb590842f8a17530eca86420,
    0x110b3,
    0x104b9,
    0x106b9,
    0xc4f4b7092386098d364ae7502b0d673808543968f014c6b2412f62c9590462f8a17530eca86420,
    0x122af457098c192b03476c48096b50d24e7839728f014c6a4072f62c9590462f8a17530eca86420,
    0x8f0b23874d64077388314ae4c0b78d27085432971814e6a5012f62c9584c62f8a17530eca86420,
    0xd67509832ae40b4c573870e830b78d26085432971814e6a5012f62c9584c62f8a17530eca86420,
    0x1928e4d6750a37278c090eb44996b2d43060522971814e6a5012f62c9584c62f8a17530eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_9 : Region 13 n13quick_mask [9] 77 9 69 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x108b5,
    0x108b7,
    0x10cb5,
    0x10ab9,
    0x10cb9,
    0x147830c4b2f680e589536a2c6128d970a6344192705628f4c12d66eb590842f8a175130eca86420,
    0x193694e4d0260d874516e92a28c15270a5963880f256a6d4212d66eb590842f8a175130eca86420,
    0x10eb9,
    0xe54d0a33698604d9283076b41346d708ea580857834e6b2c12f62c9590462f8a175130eca86420,
    0xf4a3364d07880d928e5430b66096d346ea582917814c6b2412f62c9590462f8a175130eca86420,
    0xd0336b44e78814e938c5670a296d3460ea582917814c6b2412f62c9590462f8a175130eca86420,
    0xe788334a56c1074eb692c582b0d936608542e917814c6b2412f62c9590462f8a175130eca86420,
    0xe50778d4b2281875256d08ea30b69380c5429917214e6a4072f62c9584c62f8a175130eca86420,
    0xeb0d525782812b478d68e502b6709380c5429917214e6a4072f62c9584c62f8a175130eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_10 : Region 13 n13quick_mask [10] 77 10 68 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x110b9,
    0x7752f828d0a40f6b850922c74172a78c543009925626f4c12d68eb590684e2a1971530eca86420,
    0x172f82c90a744076b8c50293410c784b2356e09925626f4c12d68eb590684e2a1971530eca86420,
    0x16a7850c83340f8c5430b366092f746c38a4109925626f4c12d68eb590684e2a1971530eca86420,
    0x10a56f5278c280f8b3674508c17430c592e60529836a6d4032d68eb590684e2a1971530eca86420,
    0xf8b3674502c10a56f5278c8174290c592e60529836a6d4032d68eb590684e2a1971530eca86420,
    0xf4764b38830c1374b04c6f838b6d270814434d90168ea6052f62c9587284e2a1971530eca86420,
    0x10c6f564b38833674b04c0f838b6d270814434d90168ea6052f62c9587284e2a1971530eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_11 : Region 13 n13quick_mask [11] 77 11 67 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    0x76d4b23098409564d26eb83390b6e0c7450d8e81626a5012f42c9787284e2a19517530eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n13quick_13 : Region 13 n13quick_mask [13] 77 13 65 (some 39) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib38_proof lib40_proof [
    ] (by rfl)

private theorem n13quick_root : Region 13 n13quick_mask [] 78 3 78 (some 39) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n13quick_3
  · exact n13quick_4
  · exact n13quick_5
  · exact n13quick_6
  · exact n13quick_7
  · exact n13quick_8
  · exact n13quick_9
  · exact n13quick_10
  · exact n13quick_11
  · exact absent_region (by rfl)
  · exact n13quick_13

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem verified13 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤13)
    (sm : m.sum=78) : realizes 13 m := by
  apply patched (left:=39) (right:=39) (total:=78) (p:=0xb0d000b0c002c3002c200b000b002c02c0b0a22) (q:=0x4f20004f20013c0013c004f004e013012040410)
    (by decide) (by rfl) (by decide) n13a_root (complementary13 n13a_root)
    (show Region 13 (full 13) [] 78 3 78 (some 39) from n13quick_root) m bound sm

end OMA.AlspachFinite

open AlspachConjecture OMA.AlspachFinite

theorem OMA.solution : OMA.R_AlspachConjecture_alspach_conjecture_R1.H1 := by
  intro n hn upper m hm hs
  obtain ⟨k,hk⟩ := hn
  have cases : n=1 ∨ n=3 ∨ n=5 ∨ n=7 ∨ n=9 ∨ n=11 ∨ n=13 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact alspach_conjecture.variants.one m hm hs
  · exact alspach_conjecture.variants.three m hm hs
  · exact start part5_root m hm hs
  · exact start part7_root m hm hs
  · exact start part9_root m hm hs
  · exact verified11 m hm hs
  · exact verified13 m hm hs
