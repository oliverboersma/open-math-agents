import FormalConjectures.ErdosProblems.«629»

/-!
# Proof of `n(3) = 14` (Erdős Problem 629, n = 3)

Proves that `Erdos629.n 3 = 14`:
- Upper bound `n(3) ≤ 14` via a 14-vertex bipartite (`2`-colorable) graph with Fano-plane
  lists showing list chromatic number `> 3`.
- Lower bound `14 ≤ n(3)` via palette compression to 9 colors and Hanson–MacGillivray–Toft's
  four-set cover bound (`≤ 83 < 126`).

Credits:
- Reduction `R1`: @ihateSAS
- Upper bound (`R1.H1`) and lower bound (`R1.H2`, Fano construction & palette compression):
  @steveDOTdigital and OMA contributors
-/

namespace OMA.BipartiteLists.Existence

open Finset SimpleGraph

private def line : Fin 7 → Finset (Fin 7) :=
  ![{0,1,2},{0,3,6},{0,4,5},{1,3,5},{1,4,6},{2,3,4},{2,5,6}]

private lemma size : ∀ i : Fin 7, (line i).card=3 := by decide +kernel

private lemma mono_line : ∀ S : Finset (Fin 7),
    ∃ i : Fin 7, line i ⊆ S ∨ Disjoint (line i) S := by decide +kernel

private def side (v : Fin 14) : Fin 2 := if v.val<7 then 0 else 1
private def graph : SimpleGraph (Fin 14) := (⊤ : SimpleGraph (Fin 2)).comap side
private def leftV (i : Fin 7) : Fin 14 := ⟨i.val,by omega⟩
private def rightV (i : Fin 7) : Fin 14 := ⟨i.val+7,by omega⟩
private def idx (v : Fin 14) : Fin 7 := ⟨v.val%7,Nat.mod_lt _ (by decide)⟩
private def lists (v : Fin 14) : Finset ℕ := (line (idx v)).image Fin.val

private lemma bipartite : graph.Colorable 2 := ⟨Coloring.mk side (fun h => h)⟩

private lemma impossible (C : graph.Coloring ℕ) (mem : ∀ v, C v ∈ lists v) : False := by
  classical
  let S := univ.filter (fun z : Fin 7 => ∃ i : Fin 7, C (leftV i)=z.val)
  obtain ⟨i,hit|avoid⟩ := mono_line S
  · obtain ⟨z,hz,e⟩ := mem_image.mp (mem (rightV i))
    have ix : idx (rightV i)=i := Fin.ext (by dsimp [idx,rightV]; omega)
    rw [ix] at hz
    obtain ⟨u,h⟩ := (mem_filter.mp (hit hz)).2
    have adj : graph.Adj (leftV u) (rightV i) := by
      change side (leftV u) ≠ side (rightV i)
      simp [leftV,rightV,side,u.isLt]
    exact C.valid adj (h.trans e)
  · obtain ⟨z,hz,e⟩ := mem_image.mp (mem (leftV i))
    have ix : idx (leftV i)=i := Fin.ext (by dsimp [idx,leftV]; omega)
    rw [ix] at hz
    exact disjoint_left.mp avoid hz (mem_filter.mpr ⟨mem_univ _,i,e.symm⟩)

private lemma finite_choosable : graph.IsKChoosable 14 := by
  classical
  intro L h
  have hall (s : Finset (Fin 14)) : s.card ≤ (s.biUnion L).card := by
    rcases s.eq_empty_or_nonempty with rfl|⟨v,hv⟩
    · simp
    calc
      _ ≤ 14 := by simpa using card_le_univ s
      _ = (L v).card := (h v).symm
      _ ≤ _ := card_le_card (subset_biUnion_of_mem L hv)
  obtain ⟨f,inj,hf⟩ := (all_card_le_biUnion_card_iff_exists_injective L).mp hall
  exact ⟨Coloring.mk f (fun adj e => adj.ne (inj e)),hf⟩

theorem witness : ∃ G : SimpleGraph (Fin 14), G.Colorable 2 ∧ 3<G.listChromaticNumber := by
  classical
  refine ⟨graph,bipartite,?_⟩
  have actual : graph.IsKChoosable graph.listChromaticNumber :=
    Nat.sInf_mem (s := {k : ℕ | graph.IsKChoosable k}) ⟨14,finite_choosable⟩
  by_contra! small
  have pick (v : Fin 14) : ∃ t ⊆ lists v, t.card=graph.listChromaticNumber := by
    apply exists_subset_card_eq
    simpa [lists,card_image_of_injective _ Fin.val_injective,size] using small
  choose L sub hL using pick
  obtain ⟨C,hC⟩ := actual L hL
  exact impossible C (fun v => sub v (hC v))

end OMA.BipartiteLists.Existence

namespace OMA.BipartiteLists
open Finset SimpleGraph

private lemma compressAux {m : ℕ} (hm : m≤13) (S : Finset ℕ) (L : Fin m → Finset ℕ)
    (sub : ∀ v, L v ⊆ S) (size : ∀ v, (L v).card=3) :
    ∃ f : ℕ → Fin 9, ∀ v, Set.InjOn f (L v) := by
  classical
  induction bound : S.card using Nat.strong_induction_on generalizing S L with
  | h k ih =>
    by_cases small : k≤9
    · let f (x : ℕ) : Fin 9 := if hx : x∈S then
        ⟨(Fintype.equivFin S ⟨x,hx⟩).val,by
          have ht := (Fintype.equivFin S ⟨x,hx⟩).isLt
          simp only [Fintype.card_coe] at ht
          omega⟩ else 0
      refine ⟨f,?_⟩
      intro v a ha b hb eq
      have ha' := sub v ha
      have hb' := sub v hb
      have code := congrArg Fin.val eq
      simp only [f,ha',hb',dif_pos] at code
      exact congrArg Subtype.val ((Fintype.equivFin S).injective (Fin.ext code))
    · let used := univ.biUnion (fun v => (L v).powersetCard 2)
      have used_size : used.card≤39 := calc
        _ ≤ ∑ v, ((L v).powersetCard 2).card := card_biUnion_le
        _ = m*3 := by simp [card_powersetCard,size]
        _ ≤ _ := by omega
      have all_size : 45 ≤ (S.powersetCard 2).card := by
        rw [card_powersetCard]
        exact Nat.choose_le_choose 2 (show 10≤S.card by omega)
      have missing : ¬ S.powersetCard 2 ⊆ used := by
        intro h
        have := card_le_card h
        omega
      obtain ⟨P,hP,hfree⟩ := not_subset.mp missing
      obtain ⟨Psub,Psize⟩ := mem_powersetCard.mp hP
      obtain ⟨a,b,ne,rfl⟩ := card_eq_two.mp Psize
      have ha : a ∈ S := Psub (by simp)
      have hb : b ∈ S := Psub (by simp)
      have separate (v : Fin m) (h1 : a ∈ L v) (h2 : b ∈ L v) : False := by
        apply hfree
        exact mem_biUnion.mpr ⟨v,mem_univ _,mem_powersetCard.mpr ⟨by intro x hx; simp at hx; rcases hx with rfl|rfl <;> assumption,by simp [ne]⟩⟩
      let g (x : ℕ) := if x=a then b else x
      have inj (v : Fin m) : Set.InjOn g (L v) := by
        intro x hx y hy he
        change x ∈ L v at hx
        change y ∈ L v at hy
        by_cases xa : x=a <;> by_cases ya : y=a <;> simp_all [g]
      have sub' (v : Fin m) : (L v).image g ⊆ S.erase a := by
        intro x hx
        obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
        by_cases ea : t=a
        · simp [g,ea,ne.symm,hb]
        · simp [g,ea,sub v ht]
      have smaller : (S.erase a).card < k := by rw [←bound]; exact card_erase_lt_of_mem ha
      obtain ⟨f,hf⟩ := ih _ smaller (S.erase a) (fun v => (L v).image g) sub'
        (fun v => (card_image_of_injOn (inj v)).trans (size v)) rfl
      refine ⟨f ∘ g,?_⟩
      intro v x hx y hy e
      exact inj v hx hy (hf v (mem_image_of_mem g hx) (mem_image_of_mem g hy) e)

private def occ (xs : List ℕ) (r : ℕ) := xs.countP (fun z => z.testBit r)
private def chooseFour (n : ℕ) : ℕ :=
  if n<10 then (#[0,0,0,0,1,5,15,35,70,126] : Array ℕ)[n]?.getD 0 else n.choose 4

private lemma chooseFour_eq (n : ℕ) : chooseFour n = n.choose 4 := by
  by_cases h : n<10
  · have table : ∀ i : Fin 10, chooseFour i.val=i.val.choose 4 := by decide +kernel
    exact table ⟨n,h⟩
  · simp [chooseFour,h]

private def choices (xs : List ℕ) (m : ℕ) : ℤ :=
  (chooseFour (xs.countP (fun z => z &&& m == 0)) : ℕ)
private def three (t : ℕ → ℤ) (a b c d : ℕ) :=
  t (a|||d) + t (b|||d) + t (c|||d) -
    t (a|||b|||d) - t (a|||c|||d) - t (b|||c|||d) + t (a|||b|||c|||d)
private def estimate (xs : List ℕ) : Prop :=
  let u := three (choices xs)
  let t := u 1 2 4 0
  u 1 2 8 0 ≤ t → u 1 4 8 0 ≤ t → u 2 4 8 0 ≤ t →
    t + 3*(choices xs 8 - u 1 2 4 8) ≤ 83
private instance (xs : List ℕ) : Decidable (estimate xs) := by unfold estimate; infer_instance

private def room (s : ℕ) (xs : List ℕ) := (List.range 4).all fun r =>
  decide (occ xs r ≤ 3 ∧ (s < 2^r → occ xs r = 3))
private def fits (xs : List ℕ) := ((List.range 4).all fun r => decide (occ xs r = 3))

private def verify : ℕ → ℕ → List ℕ → Bool
  | 0,n,xs => let all := List.replicate n 0 ++ xs
              if fits all then decide (estimate all) else true
  | s+1,n,xs => if room (s+1) xs then
      (List.range (n+1)).all (fun j => verify s (n-j) (List.replicate j (s+1) ++ xs))
    else true

private def initialColors (a b c : ℕ) := List.replicate c 13 ++ (List.replicate b 14 ++ (List.replicate a 15 ++ []))
private def block (a b c : ℕ) := verify 12 (9-a-b-c) (initialColors a b c)

set_option maxRecDepth 10000 in
private theorem ck000 : block 0 0 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck001 : block 0 0 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck002 : block 0 0 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck003 : block 0 0 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck010 : block 0 1 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck011 : block 0 1 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck012 : block 0 1 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck020 : block 0 2 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck021 : block 0 2 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck030 : block 0 3 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck100 : block 1 0 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck101 : block 1 0 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck102 : block 1 0 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck110 : block 1 1 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck111 : block 1 1 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck120 : block 1 2 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck200 : block 2 0 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck201 : block 2 0 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck210 : block 2 1 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem ck300 : block 3 0 0 = true := by decide +kernel

private lemma all_blocks (a b c : ℕ) : block a b c = true := by
  by_cases excess : 3<a+b+c
  · have bad : ¬ room 12 (initialColors a b c)=true := by
      intro allow
      have h := List.all_eq_true.mp allow 3 (by decide)
      have v : occ (initialColors a b c) 3=c+b+a := by
        simp [initialColors,occ,List.countP_replicate,show (13:ℕ).testBit 3=true by decide,
          show (14:ℕ).testBit 3=true by decide,show (15:ℕ).testBit 3=true by decide,add_assoc]
      have le := (of_decide_eq_true h).1
      omega
    unfold block
    rw [verify,if_neg bad]
  · have ha : a≤3 := by omega
    have hb : b≤3 := by omega
    have hc : c≤3 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      (try simp only [ck000,ck001,ck002,ck003,ck010,ck011,ck012,ck020,ck021,ck030,ck100,ck101,ck102,ck110,ck111,ck120,ck200,ck201,ck210,ck300]) <;> omega

private lemma branch_ok (s n : ℕ) (xs : List ℕ)
    (h : ∀ j, j < n+1 → verify s (n-j) (List.replicate j (s+1) ++ xs)=true) :
    verify (s+1) n xs=true := by
  rw [verify]
  split
  · simpa only [List.all_eq_true,List.mem_range] using h
  · rfl

private theorem checked : verify 15 9 [] = true := by
  apply branch_ok; intro a _
  apply branch_ok; intro b _
  apply branch_ok; intro c _
  simpa only [block,initialColors] using all_blocks a b c

private theorem verify_sound (s n : ℕ) (acc ys : List ℕ) (hy : ys.length=n)
    (bound : ∀ y ∈ ys, y ≤ s) (tot : ∀ r < 4, occ (ys++acc) r=3)
    (ok : verify s n acc=true) : estimate (ys++acc) := by
  induction s generalizing n acc ys with
  | zero =>
    have e : ys=List.replicate n 0 := List.eq_replicate_iff.mpr ⟨hy,fun y h => by have := bound y h; omega⟩
    subst ys
    have fit : fits (List.replicate n 0 ++ acc)=true := by simpa [fits] using tot
    simpa only [verify,fit,if_true,decide_eq_true_eq] using ok
  | succ s ih =>
    have room' : room (s+1) acc=true := by
      simp only [room,List.all_eq_true,List.mem_range,decide_eq_true_eq]
      intro r hr
      have e := tot r hr
      simp only [occ,List.countP_append] at e ⊢
      refine ⟨by omega,?_⟩
      intro low
      have no : ys.countP (fun z => z.testBit r)=0 := List.countP_eq_zero.mpr (by
        intro x hx
        simp [Nat.testBit_lt_two_pow (lt_of_le_of_lt (bound x hx) low)])
      omega
    let j := ys.count (s+1)
    let zs := ys.filter (fun x => !(x == s+1))
    have perm : (zs ++ List.replicate j (s+1)).Perm ys := by
      have h := List.filter_append_perm (fun x : ℕ => !(x == s+1)) ys
      simpa [zs,j,List.filter_beq] using h
    have len := perm.length_eq
    simp only [List.length_append,List.length_replicate,hy] at len
    have ok' := (List.all_eq_true.mp (by simpa only [verify,room',if_true] using ok)) j
      (List.mem_range.mpr (by omega))
    have pp : (zs ++ (List.replicate j (s+1) ++ acc)).Perm (ys ++ acc) := by
      rw [←List.append_assoc]; exact perm.append_right acc
    have ans := ih (n-j) (List.replicate j (s+1) ++ acc) zs (by omega)
      (by intro x hx; obtain ⟨hx,ne⟩ := List.mem_filter.mp hx
          have h := bound x hx; simp at ne; omega)
      (fun r hr => (pp.countP_eq _).trans (tot r hr)) ok'
    have equal : choices (zs ++ (List.replicate j (s+1) ++ acc)) = choices (ys ++ acc) := by
      funext m; unfold choices; rw [pp.countP_eq]
    simpa only [estimate,equal] using ans

private abbrev P := Fin 9
private abbrev Family := Finset (Finset P)
private def box (f : P → ℕ) (m : ℕ) : Family :=
  (univ.filter (fun i => f i &&& m = 0)).powersetCard 4

private lemma count_tuple {n : ℕ} (f : Fin n → ℕ) (p : ℕ → Bool) :
    (List.ofFn f).countP p = (univ.filter (fun i => p (f i))).card := by
  calc
    _ = ∑ i, if p (f i) then 1 else 0 := by
      induction n with
      | zero => simp
      | succ n ih => rw [List.ofFn_succ,List.countP_cons,Fin.sum_univ_succ,ih]; exact add_comm _ _
    _ = _ := by simp

private lemma box_card (f : P → ℕ) (m : ℕ) :
    ((box f m).card : ℤ) = choices (List.ofFn f) m := by
  simp only [box,choices,card_powersetCard,count_tuple,beq_iff_eq,chooseFour_eq]

private lemma box_inter (f : P → ℕ) (a b : ℕ) :
    box f a ∩ box f b = box f (a|||b) := by
  ext U
  simp only [box,mem_inter,mem_powersetCard,subset_iff,mem_filter,mem_univ,true_and,
      Nat.and_or_distrib_left,Nat.or_eq_zero_iff]
  aesop

private lemma card_three {α : Type*} [DecidableEq α] (a b c : Finset α) :
    ((a∪b∪c).card : ℤ) = a.card + b.card + c.card -
      (a∩b).card - (a∩c).card - (b∩c).card + (a∩b∩c).card := by
  have h₁ := card_union_add_card_inter a b
  have h₂ := card_union_add_card_inter (a∪b) c
  have h₃ := card_union_add_card_inter (a∩c) (b∩c)
  rw [union_inter_distrib_right] at h₂
  have e : a∩c∩(b∩c)=a∩b∩c := by ext; simp
  rw [e] at h₃
  omega

private def bundle (f : P → ℕ) (a b c d : ℕ) :=
  box f (a|||d) ∪ box f (b|||d) ∪ box f (c|||d)

private lemma bundle_card (f : P → ℕ) (a b c d : ℕ) :
    ((bundle f a b c d).card : ℤ) = three (choices (List.ofFn f)) a b c d := by
  simp only [bundle,card_three,box_inter,box_card,three]
  simp only [Nat.or_left_comm,Nat.or_comm,Nat.or_self]

private lemma card_gain (f : P → ℕ) :
    ((box f 8 \ bundle f 1 2 4 0).card : ℤ) =
       choices (List.ofFn f) 8 - three (choices (List.ofFn f)) 1 2 4 8 := by
  have eq : bundle f 1 2 4 0 ∩ box f 8 = bundle f 1 2 4 8 := by
    simp only [bundle,union_inter_distrib_right,box_inter]; rfl
  have h := card_sdiff_add_card_inter (box f 8) (bundle f 1 2 4 0)
  rw [inter_comm,eq] at h
  rw [←box_card,←bundle_card]
  omega

private def miss (a : Finset P) : Family := aᶜ.powersetCard 4
private def cover (a b c : Finset P) : Family := miss a ∪ miss b ∪ miss c
private def pack (b : Fin 4 → Bool) : ℕ :=
  (b 0).toNat+2*(b 1).toNat+4*(b 2).toNat+8*(b 3).toNat

private lemma pack_spec : ∀ b : Fin 4 → Bool, pack b ≤ 15 ∧ ∀ i : Fin 4,
    (pack b).testBit i.val = b i ∧ (pack b &&& 2^i.val = 0 ↔ b i=false) := by decide +kernel

private lemma four_lists (a b c d : Finset P) (ha : a.card=3) (hb : b.card=3)
    (hc : c.card=3) (hd : d.card=3) (chk : verify 15 9 []=true)
    (ab : (cover a b d).card ≤ (cover a b c).card)
    (ac : (cover a c d).card ≤ (cover a b c).card)
    (bc : (cover b c d).card ≤ (cover a b c).card) :
    (cover a b c).card + 3*(miss d \ cover a b c).card ≤ 83 := by
  let rows : Fin 4 → Finset P := ![a,b,c,d]
  let f (z : P) := pack (fun j => decide (z∈rows j))
  have hs (j : Fin 4) : (rows j).card=3 := by
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have count (r : Fin 4) : occ (List.ofFn f) r.val=3 := by
    rw [occ,count_tuple]
    rw [←hs r]
    apply congrArg Finset.card
    ext z
    simp only [mem_filter,mem_univ,true_and,f,((pack_spec _).2 r).1,decide_eq_true_eq]
  have val (r : Fin 4) : box f (2^r.val) = miss (rows r) := by
    unfold box miss
    apply congrArg (Finset.powersetCard 4)
    ext z
    simp only [mem_filter,mem_univ,true_and,f,((pack_spec _).2 r).2,decide_eq_false_iff_not,mem_compl]
  have e := verify_sound 15 9 [] (List.ofFn f) (by simp)
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact (pack_spec _).1)
    (fun r hr => by simpa using count ⟨r,hr⟩) chk
  simp only [List.append_nil,estimate] at e
  rw [←card_gain] at e
  have v0 : box f 1=miss a := val 0
  have v1 : box f 2=miss b := val 1
  have v2 : box f 4=miss c := val 2
  have v3 : box f 8=miss d := val 3
  simp only [←bundle_card,bundle,Nat.or_zero,v0,v1,v2,v3] at e
  exact_mod_cast e (by exact_mod_cast ab) (by exact_mod_cast ac) (by exact_mod_cast bc)

private lemma cover_six {ι : Type*} [DecidableEq ι] (A : Finset ι) (six : A.card = 6)
    (L : ι → Finset P) (hs : ∀ i, (L i).card=3) (chk : verify 15 9 []=true) :
    (A.biUnion (fun i => miss (L i))).card ≤ 83 := by
  classical
  let U (s : Finset ι) := s.biUnion (fun i => miss (L i))
  have ne : (A.powersetCard 3).Nonempty := by
    rw [powersetCard_nonempty]; omega
  obtain ⟨B,hB,best⟩ := exists_max_image (A.powersetCard 3) (fun s => (U s).card) ne
  obtain ⟨sub,threeB⟩ := mem_powersetCard.mp hB
  obtain ⟨i,j,k,ij,ik,jk,Bform⟩ := card_eq_three.mp threeB
  have max3 (x y z : ι) (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
      (hx : x∈A) (hy : y∈A) (hz : z∈A) : (cover (L x) (L y) (L z)).card ≤ (U B).card := by
    have ok : {x,y,z} ∈ A.powersetCard 3 := mem_powersetCard.mpr ⟨by
      intro v hv; simp at hv; rcases hv with rfl|rfl|rfl <;> assumption,by simp [xy,xz,yz]⟩
    simpa [U,cover,union_assoc] using best _ ok
  have eqB : U B = cover (L i) (L j) (L k) := by simp [Bform,U,cover,union_assoc]
  have hi : i∈A := sub (by simp [Bform])
  have hj : j∈A := sub (by simp [Bform])
  have hk : k∈A := sub (by simp [Bform])
  let rem := A \ B
  have rcard : rem.card=3 := by dsimp [rem]; rw [card_sdiff_of_subset sub,six,threeB]
  have gain (d : ι) (hd : d∈rem) : (U B).card+3*(miss (L d) \ U B).card ≤ 83 := by
    obtain ⟨da,db⟩ := mem_sdiff.mp hd
    rw [Bform] at db
    have di : i≠d := fun e => db (by simp [←e])
    have dj : j≠d := fun e => db (by simp [←e])
    have dk : k≠d := fun e => db (by simp [←e])
    rw [eqB]
    exact four_lists _ _ _ _ (hs i) (hs j) (hs k) (hs d) chk
      (eqB ▸ max3 i j d ij di dj hi hj da)
      (eqB ▸ max3 i k d ik di dk hi hk da)
      (eqB ▸ max3 j k d jk dj dk hj hk da)
  let g (d : ι) := (miss (L d) \ U B).card
  obtain ⟨d,hd,gm⟩ := exists_max_image rem g (card_pos.mp (show 0<rem.card by omega))
  have incl : U A ⊆ U B ∪ rem.biUnion (fun v => miss (L v) \ U B) := by
    intro t ht
    obtain ⟨v,va,vt⟩ := mem_biUnion.mp ht
    by_cases tb : t∈U B
    · exact mem_union_left _ tb
    · have vb : v∉B := fun vb => tb (mem_biUnion.mpr ⟨v,vb,vt⟩)
      exact mem_union_right _ (mem_biUnion.mpr ⟨v,mem_sdiff.mpr ⟨va,vb⟩,mem_sdiff.mpr ⟨vt,tb⟩⟩)
  calc
    _ ≤ _ := card_le_card incl
    _ ≤ _ := card_union_le _ _
    _ ≤ (U B).card + ∑ v ∈ rem, g v := Nat.add_le_add_left card_biUnion_le _
    _ ≤ (U B).card + ∑ _ ∈ rem, g d := Nat.add_le_add_left (sum_le_sum gm) _
    _ ≤ 83 := by simpa [g,rcard] using gain d hd

private def contain (a : Finset P) : Family := aᶜ.image (fun x => insert x a)

private lemma contain_of_subset {a t : Finset P} (ha : a.card=3) (ht : t.card=4)
    (sub : a⊆t) : t∈contain a := by
  have one : (t\a).card=1 := by rw [card_sdiff_of_subset sub,ht,ha]
  obtain ⟨x,e⟩ := card_eq_one.mp one
  have hx : x∈t\a := e ▸ mem_singleton_self x
  refine mem_image.mpr ⟨x,mem_compl.mpr (mem_sdiff.mp hx).2,?_⟩
  ext y
  constructor
  · intro h
    rcases mem_insert.mp h with rfl|h
    · exact (mem_sdiff.mp hx).1
    · exact sub h
  · intro h
    by_cases ya : y∈a
    · exact mem_insert_of_mem ya
    · have := mem_sdiff.mpr ⟨h,ya⟩
      rw [e,mem_singleton] at this
      simp [this]

private lemma small_side {m : ℕ} (hm : m≤13) (A : Finset (Fin m)) (order : A.card≤Aᶜ.card)
    (L : Fin m → Finset P) (hs : ∀ v,(L v).card=3) (chk : verify 15 9 []=true) :
    ∃ t : Finset P, ∀ v, ∃ z∈L v, (z∈t ↔ v∈A) := by
  classical
  let left := A.biUnion (fun v => miss (L v))
  let right := Aᶜ.biUnion (fun v => contain (L v))
  let T := (univ : Finset P).powersetCard 4
  have tc : T.card=126 := by simp [T,card_powersetCard,Fintype.card_fin]; decide
  have total : A.card+Aᶜ.card=m := by simp
  have rbound : right.card≤Aᶜ.card*6 := calc
    _ ≤ ∑ v ∈ Aᶜ, (contain (L v)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ Aᶜ, 6 := by
      apply sum_le_sum
      intro v _
      have bound : (contain (L v)).card ≤ (L v)ᶜ.card := card_image_le
      simpa only [card_compl,hs,Fintype.card_fin] using bound
    _ = _ := by simp
  have lb : left.card+right.card<126 := by
    by_cases six : A.card=6
    · have h := cover_six A six L hs chk
      change left.card≤83 at h
      omega
    · have p : left.card≤A.card*15 := calc
        _ ≤ ∑ v ∈ A, (miss (L v)).card := card_biUnion_le
        _ = _ := by simp [miss,card_powersetCard,card_compl,hs,Fintype.card_fin,show Nat.choose 6 4=15 by decide]
      omega
  have gap : ¬T ⊆ left∪right := by
    intro h
    have le := (card_le_card h).trans (card_union_le left right)
    omega
  obtain ⟨t,ht,out⟩ := not_subset.mp gap
  have cardt := (mem_powersetCard.mp ht).2
  refine ⟨t,fun v => ?_⟩
  by_cases hv : v∈A
  · by_contra! h
    have incl : t⊆(L v)ᶜ := by
      intro z hz
      apply mem_compl.mpr
      intro hl
      simpa [hv,hz] using h z hl
    exact out (mem_union_left _ (mem_biUnion.mpr ⟨v,hv,mem_powersetCard.mpr ⟨incl,cardt⟩⟩))
  · by_contra! h
    have incl : L v⊆t := by
      intro z hz; by_contra zt
      simpa [hv,zt] using h z hz
    exact out (mem_union_right _ (mem_biUnion.mpr ⟨v,mem_compl.mpr hv,contain_of_subset (hs v) cardt incl⟩))

private lemma split_lists {m : ℕ} (hm : m≤13) (A : Finset (Fin m))
    (L : Fin m → Finset P) (hs : ∀ v,(L v).card=3) (chk : verify 15 9 []=true) :
    ∃ t : Finset P, ∀ v, ∃ z∈L v, (z∈t ↔ v∈A) := by
  by_cases h : A.card≤Aᶜ.card
  · exact small_side hm A h L hs chk
  · obtain ⟨t,ht⟩ := small_side hm Aᶜ (by simpa using le_of_not_ge h) L hs chk
    refine ⟨tᶜ,fun v => ?_⟩
    obtain ⟨z,hz,e⟩ := ht v
    exact ⟨z,hz,by simpa using not_congr e⟩

private theorem choosable {m : ℕ} (hm : m≤13) (G : SimpleGraph (Fin m))
    (bip : G.Colorable 2) (chk : verify 15 9 []=true) : G.IsKChoosable 3 := by
  classical
  intro L hs
  obtain ⟨f,inj⟩ := compressAux hm (univ.biUnion L) L
    (fun i => subset_biUnion_of_mem L (mem_univ i)) hs
  let M (v : Fin m) := (L v).image f
  have size (v : Fin m) : (M v).card=3 := (card_image_of_injOn (inj v)).trans (hs v)
  obtain ⟨B⟩ := bip
  let A := univ.filter (fun v => (B v).val=0)
  obtain ⟨t,good⟩ := split_lists hm A M size chk
  have pick (v : Fin m) : ∃ x∈L v, (f x∈t ↔ (B v).val=0) := by
    obtain ⟨z,hz,side⟩ := good v
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact ⟨x,hx,by simpa [A] using side⟩
  choose C hL hside using pick
  refine ⟨Coloring.mk C ?_,hL⟩
  intro u v adj e
  have eq : (B u).val=0 ↔ (B v).val=0 := (hside u).symm.trans (e ▸ hside v)
  apply B.valid adj
  apply Fin.ext
  have hu := (B u).isLt
  have hv := (B v).isLt
  omega

theorem lower (witness : ∃ G : SimpleGraph (Fin 14), G.Colorable 2 ∧ 3<G.listChromaticNumber)
    (chk : verify 15 9 []=true) : 14 ≤ Erdos629.n 3 := by
  classical
  have dne : Set.Nonempty {m : ℕ | ∃ G : SimpleGraph (Fin m), G.Colorable 2 ∧
      3<G.listChromaticNumber} := ⟨14,witness⟩
  by_contra! small
  obtain ⟨G,bi,large⟩ := Nat.sInf_mem dne
  have h := choosable (m:=Erdos629.n 3) (by omega) G bi chk
  exact (Nat.not_lt_of_ge (Nat.sInf_le (s:={k : ℕ | G.IsKChoosable k}) h)) large

end OMA.BipartiteLists

theorem OMA.solution : type_of% @Erdos629.erdos_629.variants.n_three := by
  have h1 : Erdos629.n 3 ≤ 14 := by
    obtain ⟨G, hcol, hchi⟩ := OMA.BipartiteLists.Existence.witness
    exact Erdos629.n_le G hcol hchi
  have h2 : 14 ≤ Erdos629.n 3 :=
    OMA.BipartiteLists.lower OMA.BipartiteLists.Existence.witness OMA.BipartiteLists.checked
  exact le_antisymm h1 h2
