import FormalConjectures.ErdosProblems.«1017»
import Mathlib

-- Credit: @grp06

/-!
# Clique edge partitions of dense graphs

The general Erdős–Goodman–Pósa bound follows by induction at a minimum-degree
vertex. If there are q missing edges, delete one endpoint of each missing edge
to obtain a clique of size at least n - q. Use this clique as one part and
partition its remaining edges individually.
-/

section

open Finset SimpleGraph

namespace OMA.DenseCliques

variable {V : Type*} [DecidableEq V]

private def MatchingIn (G : SimpleGraph V) (N : Finset V) (M : Finset (Finset V)) : Prop :=
  (∀ A ∈ M, A.card = 2 ∧ A ⊆ N ∧ G.IsClique (A : Set V)) ∧
    (M : Set (Finset V)).PairwiseDisjoint id

private theorem maxMatchingIn (G : SimpleGraph V) (N : Finset V) :
    ∃ M : Finset (Finset V), MatchingIn G N M ∧
      ∀ ⦃x y⦄, x ∈ N \ M.biUnion id → y ∈ N \ M.biUnion id → ¬G.Adj x y := by
  classical
  let F := N.powerset.powerset.filter (MatchingIn G N)
  have hF : F.Nonempty := ⟨∅, by simp [F, MatchingIn]⟩
  obtain ⟨M, hM, hmax⟩ := F.exists_max_image Finset.card hF
  have hmatch := (Finset.mem_filter.mp hM).2
  refine ⟨M, hmatch, ?_⟩
  intro x y hx hy hxy
  obtain ⟨hxN, hxM⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyN, hyM⟩ := Finset.mem_sdiff.mp hy
  let A : Finset V := {x, y}
  have hxA : x ∈ A := by simp [A]
  have hAN : A ⊆ N := Finset.insert_subset hxN (Finset.singleton_subset_iff.mpr hyN)
  have hAM : A ∉ M := fun ha => hxM (mem_biUnion.mpr ⟨A, ha, hxA⟩)
  have hM' : MatchingIn G N (insert A M) := by
    refine ⟨?_, ?_⟩
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · refine ⟨Finset.card_pair hxy.ne, hAN, ?_⟩
        simpa [A] using (isClique_pair.mpr (fun _ => hxy))
      · exact hmatch.1 B hB
    · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert_of_notMem (show A ∉ (M : Set _) from hAM)]
      refine ⟨hmatch.2, fun B hB => Finset.disjoint_left.mpr ?_⟩
      intro z hz hzB
      have hzM : z ∈ M.biUnion id := mem_biUnion.mpr ⟨B, hB, hzB⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxM hzM
      · rw [Finset.mem_singleton] at hz
        exact hyM (hz ▸ hzM)
  have hf' : insert A M ∈ F := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hM'⟩
    intro B hB
    exact Finset.mem_powerset.mpr ((hM'.1 B hB).2.1)
  have := hmax _ hf'
  rw [Finset.card_insert_of_notMem hAM] at this
  omega

private def Covered (Q : Finset (Finset V)) (a b : V) : Prop :=
  ∃ C ∈ Q, a ∈ C ∧ b ∈ C

private def cliqueRemainder (G : SimpleGraph V) (Q : Finset (Finset V)) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬Covered Q a b
  symm.symm := by
    intro a b h
    exact ⟨h.1.symm, fun ⟨C, hC, hb, ha⟩ => h.2 ⟨C, hC, ha, hb⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private theorem extendPartition {G : SimpleGraph V} {P Q : Finset (Finset V)}
    (hQ : ∀ C ∈ Q, 2 ≤ C.card ∧ G.IsClique (C : Set V))
    (hunique : ∀ ⦃C D⦄, C ∈ Q → D ∈ Q → ∀ ⦃a b⦄,
      a ≠ b → a ∈ C → b ∈ C → a ∈ D → b ∈ D → C = D)
    (hP : (cliqueRemainder G Q).IsCliqueEdgePartition P) :
    G.IsCliqueEdgePartition (Q ∪ P) := by
  refine ⟨?_, ?_⟩
  · intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact hQ C hC
    · exact ⟨(hP.1 C hC).1, fun a ha b hb hab => ((hP.1 C hC).2 ha hb hab).1⟩
  · intro a b hab
    by_cases h : Covered Q a b
    · obtain ⟨C, hC, ha, hb⟩ := h
      refine ⟨C, ⟨Finset.mem_union_left _ hC, ha, hb⟩, ?_⟩
      rintro D ⟨hD, hDa, hDb⟩
      rcases Finset.mem_union.mp hD with hD | hD
      · exact hunique hD hC hab.ne hDa hDb ha hb
      · exact False.elim (((hP.1 D hD).2 hDa hDb hab.ne).2 ⟨C, hC, ha, hb⟩)
    · obtain ⟨C, ⟨hC, ha, hb⟩, hC'⟩ := hP.2 a b ⟨hab, h⟩
      refine ⟨C, ⟨Finset.mem_union_right _ hC, ha, hb⟩, ?_⟩
      rintro D ⟨hD, hDa, hDb⟩
      rcases Finset.mem_union.mp hD with hD | hD
      · exact False.elim (h ⟨D, hD, hDa, hDb⟩)
      · exact hC' D ⟨hD, hDa, hDb⟩

private theorem square_div_four_succ (n : ℕ) :
    n * n / 4 + (n + 1) / 2 = (n + 1) * (n + 1) / 4 := by
  let t := n / 2
  have h : n = 2 * t ∨ n = 2 * t + 1 := by omega
  rcases h with h | h
  · rw [h, show 2 * t * (2 * t) = 4 * (t * t) by ring,
        show (2 * t + 1) * (2 * t + 1) = 4 * (t * t) + 4 * t + 1 by ring]
    omega
  · rw [h, show (2 * t + 1) * (2 * t + 1) = 4 * (t * t) + 4 * t + 1 by ring,
        show (2 * t + 1 + 1) * (2 * t + 1 + 1) = 4 * (t * t) + 8 * t + 4 by ring]
    omega


/-- The Erdős–Goodman–Pósa bound. At a minimum-degree vertex, pair up
its neighbors along a maximal matching to use at most half the remaining
vertices' worth of edges and triangles before applying induction. -/
private theorem egpPartition [Fintype V] (S : Finset V) (G : SimpleGraph V)
    (hS : ∀ ⦃a b⦄, G.Adj a b → a ∈ S ∧ b ∈ S) :
    ∃ P, G.IsCliqueEdgePartition P ∧ P.card ≤ S.card * S.card / 4 := by
  classical
  induction S using Finset.strongInductionOn generalizing G with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · obtain ⟨v, hvS, hvmin⟩ := S.exists_min_image (fun x => (G.neighborFinset x).card) hne
      let N := G.neighborFinset v
      have hNS (x : V) : G.neighborFinset x ⊆ S :=
        fun _ hy => (hS ((G.mem_neighborFinset _ _).mp hy)).2
      have hvN : v ∉ N := fun hv => ((G.mem_neighborFinset _ _).mp hv).ne rfl
      obtain ⟨M, hm, hindep⟩ := maxMatchingIn G N
      let T := M.biUnion id
      let U := N \ T
      have hTN : T ⊆ N := by
        intro x hx
        obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx
        exact (hm.1 A hA).2.1 hxA
      have hTS : T.card = 2 * M.card := by
        rw [show T = M.biUnion id from rfl, Finset.card_biUnion hm.2]
        calc
          ∑ A ∈ M, (id A).card = ∑ _A ∈ M, 2 :=
            Finset.sum_congr rfl (fun A hA => (hm.1 A hA).1)
          _ = 2 * M.card := by simp [Nat.mul_comm]
      have hsplit : U.card + T.card = N.card := Finset.card_sdiff_add_card_eq_card hTN
      have hUS : U ⊆ S := Finset.sdiff_subset.trans (hNS v)
      have hbound : U.card + N.card ≤ S.card := by
        by_cases hu : U.Nonempty
        · obtain ⟨w, hw⟩ := hu
          have hsub : G.neighborFinset w ⊆ S \ U := by
            intro x hx
            exact Finset.mem_sdiff.mpr
              ⟨hNS w hx, fun hxU => hindep hw hxU ((G.mem_neighborFinset _ _).mp hx)⟩
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_sdiff_of_subset hUS] at hcard
          have hmin := hvmin w (hUS hw)
          change N.card ≤ (G.neighborFinset w).card at hmin
          have hUS' := Finset.card_le_card hUS
          omega
        · rw [Finset.not_nonempty_iff_eq_empty.mp hu, Finset.card_empty, zero_add]
          exact Finset.card_le_card (hNS v)
      let B : Finset (Finset V) := M ∪ U.image (fun x => {x})
      have hB (A : Finset V) (hA : A ∈ B) :
          1 ≤ A.card ∧ A ⊆ N ∧ G.IsClique (A : Set V) := by
        rcases Finset.mem_union.mp hA with hmA | hsA
        · obtain ⟨hc, hsub, hcl⟩ := hm.1 A hmA
          exact ⟨by omega, hsub, hcl⟩
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hsA
          exact ⟨by simp, Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hx).1, by simp⟩
      have hBcover (x : V) (hx : x ∈ N) : ∃ A ∈ B, x ∈ A := by
        by_cases hxT : x ∈ T
        · obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hxT
          exact ⟨A, Finset.mem_union_left _ hA, hxA⟩
        · exact ⟨{x}, Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxT⟩, rfl⟩), Finset.mem_singleton_self x⟩
      have hBunique {A D : Finset V} (ha : A ∈ B) (hd : D ∈ B) {x : V}
          (hxa : x ∈ A) (hxd : x ∈ D) : A = D := by
        have incompatible {C : Finset V} (hC : C ∈ M) (hxC : x ∈ C)
            (hxU : x ∈ U) : False :=
          (Finset.mem_sdiff.mp hxU).2 (mem_biUnion.mpr ⟨C, hC, hxC⟩)
        rcases Finset.mem_union.mp ha with hmA | huA
        · rcases Finset.mem_union.mp hd with hmD | huD
          · by_contra h
            exact (Finset.disjoint_left.mp (hm.2 hmA hmD h)) hxa hxd
          · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp huD
            obtain rfl := Finset.mem_singleton.mp hxd
            exact (incompatible hmA hxa hz).elim
        · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp huA
          obtain rfl := Finset.mem_singleton.mp hxa
          rcases Finset.mem_union.mp hd with hmD | huD
          · exact (incompatible hmD hxd hz).elim
          · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp huD
            obtain rfl := Finset.mem_singleton.mp hxd
            rfl
      let Q := B.image (insert v)
      have hQ (C : Finset V) (hC : C ∈ Q) : 2 ≤ C.card ∧ G.IsClique (C : Set V) := by
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
        obtain ⟨hc, hsub, hcl⟩ := hB A hA
        have hva : v ∉ A := fun hv => hvN (hsub hv)
        refine ⟨by rw [Finset.card_insert_of_notMem hva]; omega, ?_⟩
        rw [Finset.coe_insert, isClique_insert]
        exact ⟨hcl, fun a ha _ => (G.mem_neighborFinset _ _).mp (hsub ha)⟩
      have hunique ⦃C D : Finset V⦄ (hC : C ∈ Q) (hD : D ∈ Q)
          ⦃a b : V⦄ (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
          (haD : a ∈ D) (hbD : b ∈ D) : C = D := by
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
        obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hD
        by_cases hav : a = v
        · have hbv : b ≠ v := fun h => hab (hav.trans h.symm)
          exact congrArg (insert v) (hBunique hA hE
            ((Finset.mem_insert.mp hbC).resolve_left hbv)
            ((Finset.mem_insert.mp hbD).resolve_left hbv))
        · exact congrArg (insert v) (hBunique hA hE
            ((Finset.mem_insert.mp haC).resolve_left hav)
            ((Finset.mem_insert.mp haD).resolve_left hav))
      have hstar (x : V) (hx : G.Adj v x) : Covered Q v x := by
        obtain ⟨A, hA, hxA⟩ := hBcover x ((G.mem_neighborFinset _ _).mpr hx)
        exact ⟨insert v A, Finset.mem_image_of_mem _ hA,
          Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hxA⟩
      let R := cliqueRemainder G Q
      have hR ⦃a b : V⦄ (hab : R.Adj a b) : a ∈ S.erase v ∧ b ∈ S.erase v := by
        obtain ⟨ha, hb⟩ := hS hab.1
        refine ⟨Finset.mem_erase.mpr ⟨?_, ha⟩, Finset.mem_erase.mpr ⟨?_, hb⟩⟩
        · rintro rfl
          exact hab.2 (hstar _ hab.1)
        · rintro rfl
          exact hab.symm.2 (hstar _ hab.1.symm)
      obtain ⟨P, hp, hcP⟩ := ih (S.erase v) (Finset.erase_ssubset hvS) R hR
      have hcardB : B.card ≤ M.card + U.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
      have hcardQ : Q.card ≤ S.card / 2 := by
        have hle : Q.card ≤ M.card + U.card := Finset.card_image_le.trans hcardB
        omega
      have hpos := Finset.card_pos.mpr hne
      have hsucc : (S.erase v).card + 1 = S.card := by
        rw [Finset.card_erase_of_mem hvS]
        omega
      have hFloor := square_div_four_succ (S.erase v).card
      rw [hsucc] at hFloor
      exact ⟨Q ∪ P, extendPartition hQ hunique hp,
        (Finset.card_union_le _ _).trans (by omega)⟩
    · have hS0 := Finset.not_nonempty_iff_eq_empty.mp hne
      have hG0 : G = ⊥ := by
        ext a b
        exact ⟨fun hab => by simpa [hS0] using (hS hab).1, by simp⟩
      subst G
      exact ⟨∅, isCliqueEdgePartition_bot_empty, by simp⟩


private theorem largeClique (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Finset (Fin n), G.IsClique (C : Set (Fin n)) ∧
      n - (n.choose 2 - G.edgeFinset.card) ≤ C.card := by
  classical
  let F := (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset
  let D := F.image fun e => e.out.1
  refine ⟨Dᶜ, ?_, ?_⟩
  · intro u hu v hv huv
    by_contra h
    have he : s(u,v) ∈ F := Finset.mem_sdiff.mpr ⟨by simpa using huv, by simpa using h⟩
    have hD : s(u,v).out.1 ∈ D := Finset.mem_image.mpr ⟨_, he, rfl⟩
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u,v)) with heq | heq
    · exact (Finset.mem_compl.mp hu) (heq ▸ hD)
    · exact (Finset.mem_compl.mp hv) (heq ▸ hD)
  · have hcF : F.card = n.choose 2 - G.edgeFinset.card := by
      rw [show F = _ from rfl, Finset.card_sdiff_of_subset (edgeFinset_mono le_top),
        card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    have hcD : D.card ≤ F.card := Finset.card_image_le
    rw [Finset.card_compl, Fintype.card_fin]
    omega

private theorem useClique (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Finset (Fin n)) (hC : G.IsClique (C : Set (Fin n))) (hc : 2 ≤ C.card) :
    ∃ P, G.IsCliqueEdgePartition P ∧ P.card ≤ G.edgeFinset.card - C.card.choose 2 + 1 := by
  classical
  let emb : C ↪ Fin n := Function.Embedding.subtype _
  let K := (⊤ : SimpleGraph C).map emb
  have hAdj (u v : Fin n) : K.Adj u v ↔ u ∈ C ∧ v ∈ C ∧ u ≠ v := by
    rw [show K = _ from rfl, map_adj]
    constructor
    · rintro ⟨a, b, hab, rfl, rfl⟩
      exact ⟨a.property, b.property, fun e => hab.ne (Subtype.ext e)⟩
    · rintro ⟨hu, hv, hne⟩
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩, fun e => hne (congrArg Subtype.val e), rfl, rfl⟩
  have hKG : K ≤ G := fun u v h => by
    obtain ⟨hu, hv, hne⟩ := (hAdj u v).mp h
    exact hC hu hv hne
  have hKcard : K.edgeFinset.card = C.card.choose 2 := by
    change #((⊤ : SimpleGraph C).map emb).edgeFinset = _
    rw [card_edgeFinset_map, card_edgeFinset_top_eq_card_choose_two]
    simp
  obtain ⟨P, hp, hcard⟩ := (G \ K).exists_isCliqueEdgePartition_card_eq
  have hrem : cliqueRemainder G {C} = G \ K := by
    ext u v
    change G.Adj u v ∧ ¬Covered {C} u v ↔ G.Adj u v ∧ ¬K.Adj u v
    rw [hAdj]
    simp only [Covered, Finset.mem_singleton, exists_eq_left]
    exact ⟨fun h => ⟨h.1, fun h' => h.2 ⟨h'.1, h'.2.1⟩⟩,
      fun h => ⟨h.1, fun h' => h.2 ⟨h'.1, h'.2, h.1.ne⟩⟩⟩
  have hQ : ∀ A ∈ ({C} : Finset _), 2 ≤ A.card ∧ G.IsClique (A : Set (Fin n)) := by
    simpa only [Finset.mem_singleton, forall_eq] using And.intro hc hC
  have hpart : G.IsCliqueEdgePartition ({C} ∪ P) :=
    extendPartition hQ
      (fun {_ _} hA hB {_ _} _ _ _ _ _ =>
        (Finset.mem_singleton.mp hA).trans (Finset.mem_singleton.mp hB).symm)
      (hrem.symm ▸ hp)
  refine ⟨{C} ∪ P, hpart, ?_⟩
  have hs : (G \ K).edgeFinset = G.edgeFinset \ K.edgeFinset := by
    ext e
    simp
  have hpEdgeSet : P.card = (G \ K).edgeSet.ncard := by
    simpa only [← Set.ncard_coe_finset, coe_edgeFinset] using hcard
  have hpEdges : P.card = (G \ K).edgeFinset.card := by
    simpa only [← Set.ncard_coe_finset, coe_edgeFinset] using hpEdgeSet
  rw [hs, Finset.card_sdiff_of_subset (edgeFinset_mono hKG), hKcard] at hpEdges
  calc
    ({C} ∪ P).card ≤ 1 + P.card := by
      simpa only [Finset.card_singleton] using Finset.card_union_le {C} P
    _ ≤ _ := by omega

end OMA.DenseCliques

def OMA.answer (n k : ℕ) : ℕ :=
  let q := n * (n - 1) / 2 - k
  let r := n - q
  min (n * n / 4) (k - r * (r - 1) / 2 + 1)

theorem OMA.solution : Erdos1017.erdos_1017.upper_bound.answer = OMA.answer →
    type_of% @Erdos1017.erdos_1017.upper_bound := by
  intro ha n k _ _
  rw [ha]
  simp only [OMA.answer, ← Nat.choose_two_right]
  apply le_min
  · apply (Erdos1017.f_le_iff n k _).mpr
    intro G _
    classical
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (OMA.DenseCliques.egpPartition Finset.univ G (fun {_ _} _ => ⟨mem_univ _, mem_univ _⟩))
  · by_cases hs : n - (n.choose 2 - k) < 2
    · rw [Nat.choose_eq_zero_of_lt hs, Nat.sub_zero]
      exact (Erdos1017.f_le n k).trans (by omega)
    · apply (Erdos1017.f_le_iff n k _).mpr
      intro G hG
      classical
      have hk : G.edgeFinset.card = k := by
        simpa [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hG
      obtain ⟨C, hC, hsize⟩ := OMA.DenseCliques.largeClique n G
      rw [hk] at hsize
      obtain ⟨P, hp, hcard⟩ := OMA.DenseCliques.useClique n G C hC (by omega)
      have hchoose := Nat.choose_le_choose 2 hsize
      rw [hk] at hcard
      exact ⟨P, hp, by omega⟩

end
