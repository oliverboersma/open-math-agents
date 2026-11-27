import OMAReductions.R_Erdos21_erdos_21_variants_small_values_R1_H2_R1
import Mathlib

-- Credit: @Genbox


namespace Erdos21Projection

open Finset

abbrev Point := Fin 8
abbrev Block := Finset Point

def incidence (v : Point) (t : Finset Block) : Finset Block :=
  t.filter (v ∈ ·)

def neighbors (v : Point) (t : Finset Block) : Finset Point :=
  (incidence v t).biUnion (fun b => b.erase v)

def gain (v : Point) (t : Finset Block) : Prop :=
  (incidence v t).card + 2 ≤ (neighbors v t).card

instance (v : Point) (t : Finset Block) : Decidable (gain v t) := by
  unfold gain
  infer_instance

def goodExtension (v : Point) (s : Finset Block) (b : Block) : Prop :=
  v ∈ b ∧ Disjoint (b.erase v) (neighbors v s)

instance (v : Point) (s : Finset Block) (b : Block) : Decidable (goodExtension v s b) := by
  unfold goodExtension
  infer_instance

def Valid (t : Finset Block) : Prop :=
  (∀ b ∈ t, b.card = 3) ∧
  (∀ a ∈ t, ∀ b ∈ t, ¬ Disjoint a b) ∧
  (∀ v, (incidence v t).card ≤ 5 ∧ gain v t)

lemma incident_subset (v : Point) {s t : Finset Block} (h : s ⊆ t) :
    incidence v s ⊆ incidence v t := by
  intro b hb
  exact mem_filter.mpr ⟨h (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩

lemma neighbor_subset (v : Point) {s t : Finset Block} (h : s ⊆ t) :
    neighbors v s ⊆ neighbors v t := by
  intro w hw
  obtain ⟨b,hb,hw⟩ := mem_biUnion.mp hw
  exact mem_biUnion.mpr ⟨b,incident_subset v h hb,hw⟩

lemma gain_extension {s t : Finset Block} {v : Point}
    (h : s ⊆ t) (valid : Valid t) (missing : ¬ gain v s) :
    ∃ b ∈ t, b ∉ s ∧ goodExtension v s b := by
  by_contra! none
  let lost := incidence v t \ incidence v s
  let fresh (b : Block) := b.erase v \ neighbors v s
  have each : ∀ b ∈ lost, (fresh b).card ≤ 1 := by
    intro b hb
    obtain ⟨bt,bs⟩ := mem_sdiff.mp hb
    obtain ⟨ht,hv⟩ := mem_filter.mp bt
    have out : b ∉ s := fun hs => bs (mem_filter.mpr ⟨hs,hv⟩)
    have nd : ¬ Disjoint (b.erase v) (neighbors v s) := fun disj => none b ht out ⟨hv,disj⟩
    obtain ⟨x,hx,hn⟩ := not_disjoint_iff.mp nd
    have sub : fresh b ⊂ b.erase v := by
      apply Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩
      intro same
      have hf : x ∈ fresh b := by rw [show fresh b = b.erase v from same]; exact hx
      exact (mem_sdiff.mp hf).2 hn
    have cards := card_lt_card sub
    have two := card_erase_of_mem hv
    rw [valid.1 b ht] at two
    omega
  have spread : neighbors v t \ neighbors v s ⊆ lost.biUnion fresh := by
    intro x hx
    obtain ⟨ht,hs⟩ := mem_sdiff.mp hx
    obtain ⟨b, hb, hxb⟩ := mem_biUnion.mp ht
    refine mem_biUnion.mpr ⟨b,mem_sdiff.mpr ⟨hb,?_⟩,mem_sdiff.mpr ⟨hxb,hs⟩⟩
    exact fun hbs => hs (mem_biUnion.mpr ⟨b,hbs,hxb⟩)
  have cheap : (neighbors v t \ neighbors v s).card ≤ lost.card :=
    (card_le_card spread).trans (card_biUnion_le_card_mul lost fresh 1 each |>.trans_eq (Nat.mul_one _))
  rw [card_sdiff_of_subset (neighbor_subset v h)] at cheap
  change _ ≤ (incidence v t \ incidence v s).card at cheap
  rw [card_sdiff_of_subset (incident_subset v h)] at cheap
  have ns := card_le_card (neighbor_subset v h)
  have ds := card_le_card (incident_subset v h)
  have yes := (valid.2.2 v).2
  unfold gain at yes missing
  omega

end Erdos21Projection

namespace Erdos21Projection

open Finset

private def badVertex (s : Finset Block) : Option Point :=
  (List.finRange 8).find? (fun v => !decide (gain v s))

private def tripleList : List Block :=
  let xs := List.finRange 8
  xs.flatMap (fun x => xs.flatMap (fun y => (xs.filter (fun z => x < y && y < z)).map
    (fun z => {x,y,z})))

private theorem tripleList_complete : ∀ b : Block, b.card = 3 → b ∈ tripleList := by decide +kernel

private def search : Nat → Finset Block → List Block → Bool
  | 0, _, _ => false
  | fuel+1, s, a =>
    match badVertex s with
    | none => false
    | some v =>
      match a.find? (fun b => decide (goodExtension v s b)) with
      | none => true
      | some b =>
        search fuel (insert b s) (a.filter fun c => decide (c ≠ b ∧ ¬ Disjoint b c)) &&
        search fuel s (a.filter fun c => decide (c ≠ b))

private theorem search_sound {fuel : Nat} {s t : Finset Block} {a : List Block}
    (check : search fuel s a = true) (valid : Valid t) (lo : s ⊆ t)
    (cover : ∀ b ∈ t, b ∈ s ∨ b ∈ a) : False := by
  induction fuel generalizing s a with
  | zero => simp [search] at check
  | succ fuel ih =>
    rw [search] at check
    cases hv : badVertex s with
    | none => simp [hv] at check
    | some v =>
      rw [hv] at check
      dsimp only at check
      have missing : ¬ gain v s := by
        have h := List.find?_some hv
        simpa using h
      cases hb : a.find? (fun b => decide (goodExtension v s b)) with
      | none =>
        obtain ⟨b, bt, bs, extension⟩ := gain_extension lo valid missing
        have rejection := List.find?_eq_none.mp hb b ((cover b bt).resolve_left bs)
        simp [extension] at rejection
      | some b =>
        rw [hb, Bool.and_eq_true] at check
        by_cases bt : b ∈ t
        · apply ih check.1 (insert_subset bt lo)
          intro c ct
          rcases cover c ct with cs | ca
          · exact Or.inl (mem_insert_of_mem cs)
          · by_cases same : c = b
            · subst c
              exact Or.inl (mem_insert_self _ _)
            · exact Or.inr (List.mem_filter.mpr ⟨ca,decide_eq_true ⟨same,valid.2.1 b bt c ct⟩⟩)
        · apply ih check.2 lo
          intro c ct
          rcases cover c ct with cs | ca
          · exact Or.inl cs
          · exact Or.inr (List.mem_filter.mpr ⟨ca,decide_eq_true (fun he => bt (he ▸ ct))⟩)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checked : search 57 ∅ tripleList = true := by decide +kernel

theorem noValid (t : Finset Block) (valid : Valid t) : False := by
  apply search_sound checked valid (empty_subset _)
  intro b hb
  exact Or.inr (tripleList_complete _ (valid.1 _ hb))

end Erdos21Projection



namespace Erdos21Projection

open Finset

/-- Turn the eight-label pair-cover constraints into the disjoint triples required
by the hypergraph cover. Small blocks can cover at most one neighbor of a label
per incidence, which forces the triples at that label to gain two neighbors. -/
theorem triples_of_noValid (inconsistent : ∀ t : Finset Block, Valid t → False)
    (F : Finset Block) (small : ∀ B ∈ F, B.card ≤ 3)
    (degree : ∀ i, (F.filter (i ∈ ·)).card ≤ 5)
    (pair : ∀ i j : Point, i ≠ j → ∃ B ∈ F, i ∈ B ∧ j ∈ B) :
    ∃ B ∈ F, ∃ C ∈ F, B.card = 3 ∧ C.card = 3 ∧ Disjoint B C := by
  by_contra noTriples
  let t := F.filter (fun B => B.card = 3)
  have tsub : t ⊆ F := filter_subset ..
  have ht (B : Block) (hB : B ∈ t) : B.card = 3 := (mem_filter.mp hB).2
  have pairwise (B : Block) (hB : B ∈ t) (C : Block) (hC : C ∈ t) : ¬ Disjoint B C := by
    exact fun dis => noTriples ⟨B, tsub hB, C, tsub hC, ht _ hB, ht _ hC, dis⟩
  apply inconsistent t ⟨ht, pairwise, ?_⟩
  intro i
  let incident := F.filter (i ∈ ·)
  let remaining := incident \ incidence i t
  have included : incidence i t ⊆ incident := by
    intro B hB
    obtain ⟨hB,hi⟩ := mem_filter.mp hB
    exact mem_filter.mpr ⟨tsub hB,hi⟩
  have count := card_le_card included
  have hc : incident.card ≤ 5 := degree i
  refine ⟨count.trans hc, ?_⟩
  have spread : (univ : Finset Point).erase i ⊆
      neighbors i t ∪ remaining.biUnion (fun B => B.erase i) := by
    intro j hj
    have hij : i ≠ j := Ne.symm (mem_erase.mp hj).1
    obtain ⟨B,hB,hi,hjB⟩ := pair i j hij
    have erased : j ∈ B.erase i := mem_erase.mpr ⟨hij.symm,hjB⟩
    by_cases bt : B ∈ t
    · exact mem_union_left _ (mem_biUnion.mpr ⟨B,mem_filter.mpr ⟨bt,hi⟩,erased⟩)
    · refine mem_union_right _ (mem_biUnion.mpr ⟨B,mem_sdiff.mpr ⟨mem_filter.mpr ⟨hB,hi⟩,?_⟩,erased⟩)
      exact fun h => bt (mem_filter.mp h).1
  have cheap : (remaining.biUnion (fun B => B.erase i)).card ≤ remaining.card := by
    calc
      _ ≤ remaining.card * 1 := by
        apply card_biUnion_le_card_mul
        intro B hB
        obtain ⟨hin,hout⟩ := mem_sdiff.mp hB
        obtain ⟨hBF,hi⟩ := mem_filter.mp hin
        have hsmall := small B hBF
        have hne : B.card ≠ 3 := fun h => hout (mem_filter.mpr ⟨mem_filter.mpr ⟨hBF,h⟩,hi⟩)
        have hcard := card_erase_of_mem hi
        omega
      _ = _ := Nat.mul_one _
  have h7 : ((univ : Finset Point).erase i).card = 7 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have hleft : remaining.card = incident.card - (incidence i t).card :=
    card_sdiff_of_subset included
  have reach := (card_le_card spread).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left cheap _))
  rw [h7,hleft] at reach
  unfold gain
  omega

end Erdos21Projection




namespace Erdos21Bridge

open Finset

/-- The finite certificate required after removing the four labels of an anchor vertex. -/
def TripleLemma : Prop :=
  ∀ F : Finset (Finset (Fin 8)),
    (∀ B ∈ F, B.card ≤ 3) →
    (∀ i, (F.filter (i ∈ ·)).card ≤ 5) →
    (∀ i j : Fin 8, i ≠ j → ∃ B ∈ F, i ∈ B ∧ j ∈ B) →
    ∃ B ∈ F, ∃ C ∈ F, B.card = 3 ∧ C.card = 3 ∧ Disjoint B C

private theorem hitPair {v : ℕ} (hv : 4 ≤ v) {G T : Finset (Finset (Fin v))}
    (hT : T ⊆ G) (hsmall : T.card ≤ 2)
    (huniform : ∀ A ∈ G, A.card = 5)
    (hpairs : ∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty) :
    ∃ y : Fin v, ∀ A ∈ T, y ∈ A := by
  by_cases ht : T.card = 2
  · obtain ⟨A, B, _, rfl⟩ := card_eq_two.mp ht
    obtain ⟨y,hy⟩ := hpairs A (hT (by simp)) B (hT (by simp))
    refine ⟨y, ?_⟩
    intro C hc
    rcases (show C = A ∨ C = B by simpa using hc) with rfl | rfl
    · exact (mem_inter.mp hy).1
    · exact (mem_inter.mp hy).2
  by_cases ht' : T.card = 1
  · obtain ⟨A, rfl⟩ := card_eq_one.mp ht'
    obtain ⟨y,hy⟩ := card_pos.mp (by rw [huniform A (hT (by simp))]; decide)
    exact ⟨y, by simpa⟩
  have he : T = ∅ := card_eq_zero.mp (by omega)
  exact ⟨⟨0, by omega⟩, by simp [he]⟩

private theorem coverPairs {v : ℕ} (hv : 4 ≤ v) {G : Finset (Finset (Fin v))}
    (huniform : ∀ A ∈ G, A.card = 5)
    (hpairs : ∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty)
    (k : ℕ) (T : Finset (Finset (Fin v))) (hT : T ⊆ G) (hsmall : T.card ≤ 2*k) :
    ∃ S : Finset (Fin v), S.card ≤ k ∧ ∀ A ∈ T, ¬ Disjoint S A := by
  induction k generalizing T with
  | zero =>
    have he : T = ∅ := card_eq_zero.mp (by omega)
    exact ⟨∅, by simp, by simp [he]⟩
  | succ k ih =>
    obtain ⟨P,hPT,hP⟩ := exists_subset_card_eq (s := T) (n := min 2 T.card) (min_le_right ..)
    obtain ⟨y,hy⟩ := hitPair hv (hPT.trans hT) (hP.trans_le (min_le_left ..)) huniform hpairs
    obtain ⟨S,hS,hit⟩ := ih (T \ P) (sdiff_subset.trans hT)
      (by rw [card_sdiff_of_subset hPT,hP]; omega)
    refine ⟨insert y S, (card_insert_le ..).trans (by omega), ?_⟩
    intro A hA
    by_cases h : A ∈ P
    · exact fun hd => disjoint_left.mp hd (mem_insert_self ..) (hy A h)
    · exact fun hd => hit A (mem_sdiff.mpr ⟨hA,h⟩) (hd.mono_left (subset_insert ..))

private theorem extendCover {v : ℕ} (hv : 4 ≤ v) {G : Finset (Finset (Fin v))}
    (huniform : ∀ A ∈ G, A.card = 5)
    (hpairs : ∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty)
    (S : Finset (Fin v)) (k : ℕ) (hS : S.card+k ≤ 4)
    (hleft : (G.filter (Disjoint S ·)).card ≤ 2*k) :
    ∃ T ∈ (univ : Finset (Fin v)).powersetCard 4, ∀ A ∈ G, ¬ Disjoint T A := by
  obtain ⟨U,hU,hits⟩ := coverPairs hv huniform hpairs k (G.filter (Disjoint S ·)) (filter_subset ..) hleft
  obtain ⟨T,hsub,hcard⟩ := Finset.exists_superset_card_eq (s := S ∪ U)
    ((card_union_le S U).trans (by omega : S.card + U.card ≤ 4)) (by simpa using hv)
  refine ⟨T, mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, ?_⟩
  intro A hA hdis
  have hSA : Disjoint S A := hdis.mono_left (subset_union_left.trans hsub)
  exact hits A (mem_filter.mpr ⟨hA,hSA⟩) (hdis.mono_left (subset_union_right.trans hsub))

private theorem incidenceSum {v : ℕ} (G : Finset (Finset (Fin v))) :
    ∑ y : Fin v, (G.filter (y ∈ ·)).card = ∑ A ∈ G, A.card := by
  calc
    _ = ∑ y : Fin v, ∑ A ∈ G, if y ∈ A then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro y _
      rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_one]
    _ = ∑ A ∈ G, ∑ y : Fin v, if y ∈ A then (1 : ℕ) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro A _
      rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_one]
      congr 1
      ext y
      simp

/-- Convert the eight-label certificate into the finite four-vertex cover. -/
theorem cover (certificate : TripleLemma) {v : ℕ} (hv4 : 4 ≤ v) (hv19 : v ≤ 19)
    (G : Finset (Finset (Fin v))) (hG : G.card = 12)
    (huniform : ∀ A ∈ G, A.card = 5)
    (hpairs : ∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty)
    (hdeg : ∀ y : Fin v, (G.filter (y ∈ ·)).card ≤ 4) :
    ∃ S ∈ (univ : Finset (Fin v)).powersetCard 4, ∀ A ∈ G, ¬ Disjoint S A := by
  classical
  have hAnchor : ∃ x : Fin v, (G.filter (x ∈ ·)).card = 4 := by
    by_contra! h
    have small (y : Fin v) (_ : y ∈ (univ : Finset (Fin v))) :
        (G.filter (y ∈ ·)).card ≤ (3 : ℕ) := by
      have := hdeg y
      have := h y
      omega
    have hr : ∑ A ∈ G, A.card = 60 := by
      calc
        _ = ∑ _ ∈ G, (5 : ℕ) := sum_congr rfl huniform
        _ = 60 := by simp [hG]
    have cap := sum_le_sum small
    rw [incidenceSum, hr] at cap
    simp at cap
    omega
  obtain ⟨x,hx⟩ := hAnchor
  let R := G.filter (x ∉ ·)
  have hR : R.card = 8 := by
    have h := G.card_filter_add_card_filter_not (x ∈ ·)
    change (G.filter (x ∈ ·)).card + R.card = G.card at h
    omega
  let e : Fin 8 ≃ ↥R := (R.equivFinOfCardEq hR).symm
  let label (i : Fin 8) : Finset (Fin v) := (e i).val
  have label_mem (i : Fin 8) : label i ∈ G := (mem_filter.mp (e i).property).1
  have label_inj : Function.Injective label := fun _ _ h => e.injective (Subtype.ext h)
  let block (y : Fin v) : Finset (Fin 8) := univ.filter (fun i => y ∈ label i)
  have mem_block (i : Fin 8) (y : Fin v) : i ∈ block y ↔ y ∈ label i := by simp [block]
  have block_card (y : Fin v) : (block y).card ≤ 4 := by
    let f : Fin 8 ↪ Finset (Fin v) := ⟨label,label_inj⟩
    have sub : (block y).map f ⊆ G.filter (y ∈ ·) := by
      intro A hA
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hA
      exact mem_filter.mpr ⟨label_mem i,(mem_block i y).mp hi⟩
    exact (card_map f).symm.trans_le ((card_le_card sub).trans (hdeg y))
  have uncovered (P : Finset (Fin 8)) (S : Finset (Fin v)) (hxS : x ∈ S)
      (hit : ∀ i ∈ P, ¬ Disjoint S (label i)) :
      (G.filter (Disjoint S ·)).card ≤ 8 - P.card := by
    have sub : G.filter (Disjoint S ·) ⊆ (univ \ P).image label := by
      intro A hA
      obtain ⟨hAG,hAS⟩ := mem_filter.mp hA
      have hxA : x ∉ A := fun ha => disjoint_left.mp hAS hxS ha
      obtain ⟨i,hi⟩ := e.surjective (⟨A,mem_filter.mpr ⟨hAG,hxA⟩⟩ : ↥R)
      have he : label i = A := congrArg Subtype.val hi
      exact mem_image.mpr ⟨i, mem_sdiff.mpr ⟨mem_univ _,fun hp => hit i hp (he ▸ hAS)⟩, he⟩
    exact (card_le_card sub).trans (card_image_le.trans (by
      rw [card_sdiff_of_subset (subset_univ P), card_univ, Fintype.card_fin]))
  by_contra noCover
  have projected_small (y : Fin v) : (block y).card ≤ 3 := by
    by_contra! h
    have e4 : (block y).card = 4 := by have := block_card y; omega
    have hs : ({x,y} : Finset (Fin v)).card + 2 ≤ 4 := by
      have := (card_insert_le x {y}).trans_eq (by simp : ({y} : Finset (Fin v)).card + 1 = 2)
      omega
    have hleft := uncovered (block y) {x,y} (by simp) (by
      intro i hi hd
      exact disjoint_left.mp hd (by simp : y ∈ ({x,y} : Finset (Fin v))) ((mem_block i y).mp hi))
    exact noCover (extendCover hv4 huniform hpairs {x,y} 2 hs (by omega))
  let F := (univ : Finset (Fin v)).image block
  have hsmall : ∀ B ∈ F, B.card ≤ 3 := by
    intro B hB
    obtain ⟨y,_,rfl⟩ := mem_image.mp hB
    exact projected_small y
  have hinc (i : Fin 8) : (F.filter (i ∈ ·)).card ≤ 5 := by
    have sub : F.filter (i ∈ ·) ⊆ (label i).image block := by
      intro B hB
      obtain ⟨hb,hi⟩ := mem_filter.mp hB
      obtain ⟨y,_,rfl⟩ := mem_image.mp hb
      exact mem_image.mpr ⟨y,(mem_block i y).mp hi,rfl⟩
    exact (card_le_card sub).trans (card_image_le.trans (huniform _ (label_mem i)).le)
  have hpair (i j : Fin 8) (_ : i ≠ j) : ∃ B ∈ F, i ∈ B ∧ j ∈ B := by
    obtain ⟨y,hy⟩ := hpairs _ (label_mem i) _ (label_mem j)
    obtain ⟨hyi,hyj⟩ := mem_inter.mp hy
    exact ⟨block y,mem_image_of_mem block (mem_univ y),(mem_block i y).mpr hyi,(mem_block j y).mpr hyj⟩
  obtain ⟨B,hB,C,hC,hB3,hC3,hBC⟩ := certificate F hsmall hinc hpair
  obtain ⟨y,_,rfl⟩ := mem_image.mp hB
  obtain ⟨z,_,rfl⟩ := mem_image.mp hC
  have e6 : (block y ∪ block z).card = 6 := by rw [card_union_of_disjoint hBC,hB3,hC3]
  have hs : ({x,y,z} : Finset (Fin v)).card + 1 ≤ 4 := by
    have h₁ := card_insert_le x ({y,z} : Finset (Fin v))
    have h₂ := card_insert_le y ({z} : Finset (Fin v))
    rw [card_singleton] at h₂
    omega
  have hleft := uncovered (block y ∪ block z) {x,y,z} (by simp) (by
    intro i hi hd
    rcases mem_union.mp hi with hy | hz
    · exact disjoint_left.mp hd (by simp : y ∈ ({x,y,z} : Finset (Fin v))) ((mem_block i y).mp hy)
    · exact disjoint_left.mp hd (by simp : z ∈ ({x,y,z} : Finset (Fin v))) ((mem_block i z).mp hz))
  exact noCover (extendCover hv4 huniform hpairs {x,y,z} 1 hs (by omega))

/-- The exact statement of the merged reduction's H1. -/
theorem finiteCover (certificate : TripleLemma) : ∀ v ∈ ({16, 17} : Finset ℕ),
    ∀ G ∈ (((univ : Finset (Fin v)).powersetCard 5).powersetCard 12),
    (∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty) →
    (∀ x : Fin v, 2 ≤ (G.filter (x ∈ ·)).card ∧ (G.filter (x ∈ ·)).card ≤ 4) →
    (∀ A ∈ G, (A.filter fun x => (G.filter (x ∈ ·)).card ≤ 2).card ≤ 1) →
    ∃ S ∈ (univ : Finset (Fin v)).powersetCard 4, ∀ A ∈ G, ¬ Disjoint S A := by
  intro v hv G hG hpairs hdeg _
  simp only [mem_insert, mem_singleton] at hv
  obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hG
  exact cover certificate (by omega) (by omega) G hcard
    (fun A hA => (mem_powersetCard.mp (hsub hA)).2) hpairs (fun y => (hdeg y).2)

end Erdos21Bridge



/-- A projected pair-cover on eight labels contains two disjoint triples. -/
theorem OMA.solution : OMA.R_Erdos21_erdos_21_variants_small_values_R1_H2_R1.H1 :=
  Erdos21Bridge.finiteCover (Erdos21Projection.triples_of_noValid Erdos21Projection.noValid)