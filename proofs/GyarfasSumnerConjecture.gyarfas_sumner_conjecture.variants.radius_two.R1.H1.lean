import OMAReductions.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_variants_radius_two_R1
import Mathlib

/-! An induced-star exclusion bounds the degree by Ramsey's theorem in each neighborhood. -/

open Finset SimpleGraph

namespace GyarfasStarBound

private theorem colorable_of_degree_lt {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (hdeg : ∀ v, G.degree v < k) : G.Colorable k := by
  classical
  have aux (S : Finset V) : ∃ f : V → Fin k, ∀ a ∈ S, ∀ b ∈ S,
      G.Adj a b → f a ≠ f b := by
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0,hk⟩, by simp⟩
    | @insert v S hv ih =>
      obtain ⟨f,hf⟩ := ih
      let Used := (S.filter fun u => G.Adj v u).image f
      have hUsed : Used.card < (univ : Finset (Fin k)).card := by
        rw [card_univ, Fintype.card_fin]
        have hsub : (S.filter fun u => G.Adj v u) ⊆ G.neighborFinset v := fun u hu =>
          (G.mem_neighborFinset v u).mpr (mem_filter.mp hu).2
        have hcard := card_le_card hsub
        rw [G.card_neighborFinset_eq_degree] at hcard
        exact (card_image_le.trans hcard).trans_lt (hdeg v)
      obtain ⟨c,_,hc⟩ := exists_mem_notMem_of_card_lt_card hUsed
      refine ⟨Function.update f v c, ?_⟩
      intro a ha b hb hab
      rcases mem_insert.mp ha with hav | haS
      · subst a
        rcases mem_insert.mp hb with hbv | hbS
        · subst b
          exact (G.loopless.irrefl _ hab).elim
        · have hcb : c ≠ f b := fun e =>
            hc (mem_image.mpr ⟨b,mem_filter.mpr ⟨hbS,hab⟩,e.symm⟩)
          simpa [Function.update_of_ne (ne_of_mem_of_not_mem hbS hv)] using hcb
      · rcases mem_insert.mp hb with hbv | hbS
        · subst b
          have hca : f a ≠ c := fun e =>
            hc (mem_image.mpr ⟨a,mem_filter.mpr ⟨haS,hab.symm⟩,e⟩)
          simpa [Function.update_of_ne (ne_of_mem_of_not_mem haS hv)] using hca
        · simpa [Function.update_of_ne (ne_of_mem_of_not_mem haS hv),
            Function.update_of_ne (ne_of_mem_of_not_mem hbS hv)] using hf a haS b hbS hab
  obtain ⟨f,hf⟩ := aux univ
  exact ⟨Coloring.mk f (fun h => hf _ (mem_univ _) _ (mem_univ _) h)⟩

private theorem star_embed {W V : Type} [Fintype W]
    {T : SimpleGraph W} {G : SimpleGraph V} {c : W} (hT : T.IsTree)
    (hnear : ∀ w, T.dist c w ≤ 1) {v : V} (p : W ↪ V)
    (hAdj : ∀ w, G.Adj v (p w))
    (hInd : ∀ a b, a ≠ b → ¬ G.Adj (p a) (p b)) :
    T.IsIndContained G := by
  classical
  have hc {w : W} (h : w ≠ c) : T.Adj c w :=
    T.dist_eq_one_iff_adj.mp (by
      have hp := hT.connected.pos_dist_of_ne h.symm
      have hle := hnear w
      omega)
  have hleaves {a b : W} (ha : a ≠ c) (hb : b ≠ c) : ¬ T.Adj a b := fun h =>
    hT.isAcyclic.cliqueFree (by decide : 3 ≤ 3) _ (is3Clique_triple_iff.mpr ⟨hc ha,hc hb,h⟩)
  let f (a : W) : V := if a = c then v else p a
  have hi : Function.Injective f := by
    intro a b he
    by_cases ha : a = c <;> by_cases hb : b = c
    · exact ha.trans hb.symm
    · have he' : v = p b := by simpa [f,ha,hb] using he
      exact ((hAdj b).ne he').elim
    · have he' : p a = v := by simpa [f,ha,hb] using he
      exact ((hAdj a).ne he'.symm).elim
    · exact p.injective (by simpa [f,ha,hb] using he)
  refine ⟨⟨⟨f,hi⟩, ?_⟩⟩
  intro a b
  change G.Adj (f a) (f b) ↔ T.Adj a b
  by_cases h : a = b
  · subst b
    simp
  by_cases ha : a = c <;> by_cases hb : b = c
  · exact (h (ha.trans hb.symm)).elim
  · subst a
    simp [f,hb,hAdj b,hc hb]
  · subst b
    have ht := (hc ha).symm
    have hg := (hAdj a).symm
    simp [f,ha,ht,hg]
  · simp [f,ha,hb,hInd a b h,hleaves ha hb]

theorem main {W : Type} [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree)
    (hRad : ∃ c : W, (∀ w : W, T.dist c w ≤ 1) ∧ (∃ w : W, T.dist c w = 1)) :
    ∃ f : ℕ → ℕ, GyarfasSumnerConjecture.IsChiBoundedBy T f := by
  classical
  obtain ⟨c,hnear,_⟩ := hRad
  let k := Fintype.card W
  let f (ω : ℕ) := (k + (ω+1)).choose k
  refine ⟨f, ?_⟩
  intro V _ _ G _ hfree
  have hf : 0 < f G.cliqueNum := Nat.choose_pos (Nat.le_add_right _ _)
  apply (colorable_of_degree_lt G hf ?_).chromaticNumber_le
  intro v
  by_contra! hdeg
  let e := Fintype.equivFin V
  let N := (G.neighborFinset v).map e.toEmbedding
  let color (A : Finset (Fin (Fintype.card V))) : Bool :=
    decide (∃ a ∈ A, ∃ b ∈ A, G.Adj (e.symm a) (e.symm b))
  have hpair (a b : Fin (Fintype.card V)) :
      color {a,b} = decide (G.Adj (e.symm a) (e.symm b)) := by
    have he : (∃ x ∈ ({a,b} : Finset _), ∃ y ∈ ({a,b} : Finset _),
        G.Adj (e.symm x) (e.symm y)) ↔ G.Adj (e.symm a) (e.symm b) := by
      constructor
      · rintro ⟨x,hx,y,hy,hxy⟩
        simp only [mem_insert,mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (G.loopless.irrefl _ hxy).elim
        · exact hxy
        · exact hxy.symm
        · exact (G.loopless.irrefl _ hxy).elim
      · exact fun h => ⟨a,by simp,b,by simp,h⟩
    simp only [color, he]
  have hN : N.card = G.degree v := by simp [N, G.card_neighborFinset_eq_degree]
  have hNeighbor {a} (ha : a ∈ N) : G.Adj v (e.symm a) := by
    obtain ⟨x,hx,he⟩ := mem_map.mp ha
    have hx' := (G.mem_neighborFinset v x).mp hx
    change e x = a at he
    simpa [← he] using hx'
  have hMono {S : Finset (Fin (Fintype.card V))} {d : Bool}
      (hS : ∀ A ⊆ S, A.card = 2 → color A = d)
      {a b : Fin (Fintype.card V)} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
      decide (G.Adj (e.symm a) (e.symm b)) = d := by
    rw [← hpair]
    exact hS {a,b} (insert_subset ha (singleton_subset_iff.mpr hb))
      (by simp [card_insert_of_notMem, hne])
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose k (G.cliqueNum+1)
      color N (by rwa [hN]) with ⟨S,hSN,hS,hind⟩ | ⟨S,_,hS,hclique⟩
  · let enum := (Fintype.equivFin W).trans (Finset.equivFinOfCardEq hS).symm
    let p : W ↪ V := enum.toEmbedding.trans ((Function.Embedding.subtype _).trans e.symm.toEmbedding)
    have hp (w : W) : G.Adj v (p w) := hNeighbor (hSN (enum w).2)
    have hup (a b : W) (h : a ≠ b) : ¬ G.Adj (p a) (p b) :=
      of_decide_eq_false (hMono hind (enum a).2 (enum b).2
        (fun hb => h (enum.injective (Subtype.ext hb))))
    exact hfree (star_embed hT hnear p hp hup)
  · let S' := S.map e.symm.toEmbedding
    have hCl : G.IsClique (S' : Set V) := by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      exact of_decide_eq_true (hMono hclique ha hb (fun hb => hxy (congrArg e.symm hb)))
    have hbad := hCl.card_le_cliqueNum
    simp only [S',card_map,hS] at hbad
    omega

end GyarfasStarBound

theorem OMA.solution : OMA.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_variants_radius_two_R1.H1 :=
  GyarfasStarBound.main