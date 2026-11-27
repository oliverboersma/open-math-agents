import OMAReductions.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Standalone Lean 4 proof of Reid-Wormald (1983) for near-regular tournaments:
Every oriented tree D on n >= 2 vertices embeds in every near-regular tournament G
on 2n - 2 vertices (where every vertex has out-degree n - 1 or n - 2).
This completely closes hypothesis H2 of SumnerUniversalTournamentConjecture.sumner_conjecture.R1!
-/

namespace ProofWork.NearRegular

open SimpleGraph Digraph SumnerUniversalTournamentConjecture

lemma ne_of_adj_tourn {V : Type*} {G : Digraph V} (hG : G.IsTournament)
    {u v : V} (h : G.Adj u v) : u ≠ v :=
  fun heq => hG.1 u (heq ▸ h)

lemma not_adj_rev_tourn {V : Type*} {G : Digraph V} (hG : G.IsTournament)
    {u v : V} (h : G.Adj u v) : ¬ G.Adj v u :=
  (hG.2 u v (ne_of_adj_tourn hG h)).mp h

lemma adj_or_rev_tourn {V : Type*} {G : Digraph V} (hG : G.IsTournament)
    {u v : V} (hne : u ≠ v) : G.Adj u v ∨ G.Adj v u := by
  by_cases h : G.Adj u v
  · exact Or.inl h
  · exact Or.inr (not_not.mp ((hG.2 u v hne).not.mp h))

lemma adj_or_rev_orient {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (hT : T.Adj u v) : D.Adj u v ∨ D.Adj v u := by
  by_cases h : D.Adj u v
  · exact Or.inl h
  · exact Or.inr (not_not.mp ((hO.2 u v hT).not.mp h))

-- Every oriented tree on m vertices (1 <= m <= d + 1) embeds into any irreflexive digraph G
-- with min(outdeg, indeg) >= d, sending a prescribed root r to ANY prescribed vertex v0!
lemma embeds_rooted_of_minDeg_ge :
    ∀ (m : ℕ), 1 ≤ m →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = m → IsOrientedTree D →
        ∀ (r : W) {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          (∀ v : V, ¬ G.Adj v v) →
          ∀ (d : ℕ), m ≤ d + 1 →
          (∀ v : V, d ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card ∧
                    d ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card) →
          ∀ (v0 : V), ∃ f : D →g G, Function.Injective f ∧ f r = v0 := by
  intro m
  induction m with
  | zero => intro h0; omega
  | succ m' ih =>
    intro _ W _ _ D _ hW hD r V _ _ G _ hirr d hmd hdeg v0
    classical
    obtain ⟨T, hT, hO⟩ := hD
    by_cases hm' : m' = 0
    · -- Base case: |W| = 1, every vertex equals r!
      subst hm'
      have hall_r : ∀ w : W, w = r := by
        intro w
        by_contra hne
        have hlt : 1 < Fintype.card W := Fintype.one_lt_card_iff.mpr ⟨w, r, hne⟩
        omega
      refine ⟨⟨fun _ => v0, ?_⟩, ?_, rfl⟩
      · intro a b hab
        exact absurd ((hall_r a).trans (hall_r b).symm) (T.ne_of_adj (hO.1 a b hab))
      · intro a b _; exact (hall_r a).trans (hall_r b).symm
    · -- Inductive step: |W| = m' + 1 >= 2. Pick a leaf l != r!
      have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨l1, l2, hl12, hl1deg, hl2deg⟩ := hT.exists_ne_and_degree_eq_one
      have hex_leaf : ∃ l : W, l ≠ r ∧ T.degree l = 1 := by
        by_cases h1 : l1 = r
        · exact ⟨l2, fun h => hl12 (h1.trans h.symm), hl2deg⟩
        · exact ⟨l1, h1, hl1deg⟩
      obtain ⟨l, hlr, hldeg⟩ := hex_leaf
      -- Unique neighbor p of l in T
      have hnb_card : (T.neighborFinset l).card = 1 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hldeg
      obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hnb_card
      have hTlp : T.Adj l p := by
        have : p ∈ T.neighborFinset l := hp_eq.symm ▸ Finset.mem_singleton_self p
        exact (SimpleGraph.mem_neighborFinset T l p).mp this
      have hpl_ne : p ≠ l := (T.ne_of_adj hTlp).symm
      have hl_uniq : ∀ z : W, T.Adj l z → z = p := by
        intro z hz
        have : z ∈ ({p} : Finset W) := hp_eq ▸ (SimpleGraph.mem_neighborFinset T l z).mpr hz
        exact Finset.mem_singleton.mp this
      -- Remove l: T' = T.induce {l}ᶜ is a tree on m' vertices containing r and p!
      let S : Set W := ({l} : Set W)ᶜ
      have hT' : (T.induce S).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hldeg, hT.isAcyclic.induce S⟩
      let D' : Digraph S := ⟨fun a b => D.Adj a.1 b.1⟩
      have hO' : D'.IsOrientation (T.induce S) :=
        ⟨fun a b h => hO.1 a.1 b.1 h, fun a b h => hO.2 a.1 b.1 h⟩
      have hcardS : Fintype.card S = m' := by
        have h1 : Fintype.card S = Fintype.card ↥(Finset.univ.erase l) := by
          refine Fintype.card_of_bijective (f := fun x : S => (⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩ : Finset.univ.erase l)) ⟨?_, ?_⟩
          · intro a b h; exact Subtype.ext (congrArg (fun z : ↥(Finset.univ.erase l) => z.1) h)
          · rintro ⟨w, hw⟩; exact ⟨⟨w, (Finset.mem_erase.mp hw).1⟩, rfl⟩
        rw [h1, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, hW]; omega
      have hrS : r ∈ S := fun h => hlr (Set.mem_singleton_iff.mp h).symm
      have hpS : p ∈ S := fun h => hpl_ne (Set.mem_singleton_iff.mp h)
      obtain ⟨f', hf'_inj, hf'_r⟩ := ih (by omega) D' hcardS ⟨T.induce S, hT', hO'⟩
        ⟨r, hrS⟩ G hirr d (by omega) hdeg v0
      let img : Finset V := Finset.univ.image f'
      have himg_card : img.card = m' := by
        rw [Finset.card_image_of_injective _ hf'_inj, Finset.card_univ, hcardS]
      have hfp_mem : f' ⟨p, hpS⟩ ∈ img := Finset.mem_image_of_mem f' (Finset.mem_univ _)
      -- Choose image z of l in N+(f' p) \ img or N-(f' p) \ img!
      have hex_z : ∃ z : V, z ∉ img ∧
          (D.Adj p l → G.Adj (f' ⟨p, hpS⟩) z) ∧ (D.Adj l p → G.Adj z (f' ⟨p, hpS⟩)) := by
        rcases adj_or_rev_orient hO hTlp.symm with hDpl | hDlp
        · have hsub : (Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u)) \
              (img.erase (f' ⟨p, hpS⟩)) ⊆
              (Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u)) \ img := by
            intro u hu
            simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_erase] at hu ⊢
            refine ⟨hu.1, fun huimg => hu.2 ⟨?_, huimg⟩⟩
            intro heq; exact hirr u (heq ▸ hu.1)
          have hc1 := Finset.card_le_card hsub
          have hc2 := Finset.le_card_sdiff (img.erase (f' ⟨p, hpS⟩))
            (Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u))
          have hc3 : (img.erase (f' ⟨p, hpS⟩)).card = m' - 1 := by
            rw [Finset.card_erase_of_mem hfp_mem, himg_card]
          have hd_le := (hdeg (f' ⟨p, hpS⟩)).1
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
            0 < ((Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u)) \ img).card)
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact ⟨z, hz.2, fun _ => hz.1, fun h => absurd h ((hO.2 p l (hO.1 p l hDpl)).mp hDpl)⟩
        · have hsub : (Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩))) \
              (img.erase (f' ⟨p, hpS⟩)) ⊆
              (Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩))) \ img := by
            intro u hu
            simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_erase] at hu ⊢
            refine ⟨hu.1, fun huimg => hu.2 ⟨?_, huimg⟩⟩
            intro heq; exact hirr u (heq ▸ hu.1)
          have hc1 := Finset.card_le_card hsub
          have hc2 := Finset.le_card_sdiff (img.erase (f' ⟨p, hpS⟩))
            (Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩)))
          have hc3 : (img.erase (f' ⟨p, hpS⟩)).card = m' - 1 := by
            rw [Finset.card_erase_of_mem hfp_mem, himg_card]
          have hd_le := (hdeg (f' ⟨p, hpS⟩)).2
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
            0 < ((Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩))) \ img).card)
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact ⟨z, hz.2, fun h => absurd h ((hO.2 l p (hO.1 l p hDlp)).mp hDlp), fun _ => hz.1⟩
      obtain ⟨z, hz_not, hz_out, hz_in⟩ := hex_z
      let f : W → V := fun w => if hw : w = l then z else f' ⟨w, hw⟩
      refine ⟨⟨f, ?_⟩, ?_, ?_⟩
      · intro a b hab
        by_cases hal : a = l <;> by_cases hbl : b = l
        · exact absurd (hal.trans hbl.symm) (T.ne_of_adj (hO.1 a b hab))
        · subst hal
          have hbp : b = p := hl_uniq b (hO.1 a b hab)
          subst hbp
          simp only [f, hbl, ↓reduceDIte]
          exact hz_in hab
        · subst hbl
          have hap : a = p := hl_uniq a (hO.1 a b hab).symm
          subst hap
          simp only [f, hal, ↓reduceDIte]
          exact hz_out hab
        · simp only [f, hal, hbl, ↓reduceDIte]
          exact f'.map_adj' hab
      · intro a b hEq
        change f a = f b at hEq
        by_cases hal : a = l <;> by_cases hbl : b = l
        · exact hal.trans hbl.symm
        · simp only [f, hal, hbl, ↓reduceDIte] at hEq
          exact absurd (hEq ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨b, hbl⟩ : S))) hz_not
        · simp only [f, hal, hbl, ↓reduceDIte] at hEq
          exact absurd (hEq.symm ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨a, hal⟩ : S))) hz_not
        · simp only [f, hal, hbl, ↓reduceDIte] at hEq
          exact congrArg Subtype.val (hf'_inj hEq)
      · change f r = v0
        simp only [f, hlr.symm, ↓reduceDIte]
        exact hf'_r

-- Reid-Wormald Theorem (1983): Every oriented tree on n >= 2 vertices embeds in every
-- near-regular tournament on 2n - 2 vertices!
theorem embeds_near_regular {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNR : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card = n - 1 ∨
                    (Finset.univ.filter (fun u : V => G.Adj v u)).card = n - 2) :
    Embeds D G := by
  classical
  -- Step 1: Every vertex has outdeg + indeg = 2n - 3, so both outdeg and indeg are in {n - 2, n - 1}!
  have hdeg_sum : ∀ v : V,
      (Finset.univ.filter (fun u : V => G.Adj v u)).card +
      (Finset.univ.filter (fun u : V => G.Adj u v)).card = 2 * n - 3 := by
    intro v
    have hdisj : Disjoint (Finset.univ.filter (fun u : V => G.Adj v u))
        (Finset.univ.filter (fun u : V => G.Adj u v)) :=
      Finset.disjoint_left.mpr (fun u h1 h2 =>
        not_adj_rev_tourn hG (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
    have hunion : Finset.univ.filter (fun u : V => G.Adj v u) ∪
        Finset.univ.filter (fun u : V => G.Adj u v) = Finset.univ.erase v := by
      ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · rintro (h | h)
        · exact (ne_of_adj_tourn hG h).symm
        · exact ne_of_adj_tourn hG h
      · intro hne
        rcases adj_or_rev_tourn hG hne.symm with h | h
        · exact Or.inl h
        · exact Or.inr h
    have hc := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, hV] at hc
    exact hc
  have hmin_deg : ∀ v : V,
      n - 2 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card ∧
      n - 2 ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card := by
    intro v
    have hs := hdeg_sum v
    rcases hNR v with h1 | h2 <;> omega
  -- Step 2: Total arc sum identity: 2 * ∑ d+(v) = (2n - 2)(2n - 3)
  have hsum_out_in : ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card =
      ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card := by
    have h1 : ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card =
        ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => G.Adj p.1 p.2)).card := by
      have hpart : (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => G.Adj p.1 p.2) =
          Finset.univ.biUnion (fun v : V => (Finset.univ.filter (fun u : V => G.Adj v u)).image (fun u => (v, u))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
        exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨v, u, hvu, h1, h2⟩ => h1 ▸ h2 ▸ hvu⟩
      rw [hpart, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
      · intro v1 _ v2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro p h1 h2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2
        exact hne (congrArg Prod.fst hEq).symm
    have h2 : ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card =
        ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => G.Adj p.1 p.2)).card := by
      have hpart : (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => G.Adj p.1 p.2) =
          Finset.univ.biUnion (fun v : V => (Finset.univ.filter (fun u : V => G.Adj u v)).image (fun u => (u, v))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
        exact ⟨fun h => ⟨b, a, h, rfl, rfl⟩, fun ⟨v, u, huv, h1, h2⟩ => h1 ▸ h2 ▸ huv⟩
      rw [hpart, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
      · intro v1 _ v2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro p h1 h2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2
        exact hne (congrArg Prod.snd hEq).symm
    rw [h1, h2]
  have hsum_tot : 2 * ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card =
      (2 * n - 2) * (2 * n - 3) := by
    have hadd : ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card +
        ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card =
        ∑ _ : V, (2 * n - 3) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => hdeg_sum v)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hV] at hadd
    omega
  -- Hence ∃ v+ with d+(v+) = n - 1 and ∃ v- with d-(v-) = n - 1!
  have hex_vp : ∃ vp : V, (Finset.univ.filter (fun u : V => G.Adj vp u)).card = n - 1 := by
    by_contra hno; push Not at hno
    have hall : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card = n - 2 :=
      fun v => (hNR v).resolve_left (hno v)
    have hsum_eq : ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card =
        (2 * n - 2) * (n - 2) := by
      rw [Finset.sum_congr rfl (fun v _ => hall v)]
      simp [hV]
    have hmul : (2 * n - 2) * (2 * (n - 2)) = (2 * n - 2) * (2 * n - 3) := by
      have : (2 * n - 2) * (2 * (n - 2)) = 2 * ((2 * n - 2) * (n - 2)) := by ring
      omega
    have hcancel := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n - 2) hmul
    omega
  have hex_vm : ∃ vm : V, (Finset.univ.filter (fun u : V => G.Adj u vm)).card = n - 1 := by
    by_contra hno; push Not at hno
    have hall : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card = n - 2 := by
      intro v; have hs := hdeg_sum v; have hne := hno v; rcases hNR v with h1 | h2 <;> omega
    have hsum_eq : ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card =
        (2 * n - 2) * (n - 2) := by
      rw [Finset.sum_congr rfl (fun v _ => hall v)]
      simp [hV]
    have hmul : (2 * n - 2) * (2 * (n - 2)) = (2 * n - 2) * (2 * n - 3) := by
      have : (2 * n - 2) * (2 * (n - 2)) = 2 * ((2 * n - 2) * (n - 2)) := by ring
      omega
    have hcancel := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n - 2) hmul
    omega
  -- Step 3: Pick any leaf l of D with unique neighbor p!
  obtain ⟨T, hT, hO⟩ := hD
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨l, hldeg⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hnb_card : (T.neighborFinset l).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hldeg
  obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hnb_card
  have hTlp : T.Adj l p := by
    have : p ∈ T.neighborFinset l := hp_eq.symm ▸ Finset.mem_singleton_self p
    exact (SimpleGraph.mem_neighborFinset T l p).mp this
  have hpl_ne : p ≠ l := (T.ne_of_adj hTlp).symm
  have hl_uniq : ∀ z : W, T.Adj l z → z = p := by
    intro z hz
    have : z ∈ ({p} : Finset W) := hp_eq ▸ (SimpleGraph.mem_neighborFinset T l z).mpr hz
    exact Finset.mem_singleton.mp this
  let S : Set W := ({l} : Set W)ᶜ
  have hT' : (T.induce S).IsTree :=
    ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hldeg, hT.isAcyclic.induce S⟩
  let D' : Digraph S := ⟨fun a b => D.Adj a.1 b.1⟩
  have hO' : D'.IsOrientation (T.induce S) :=
    ⟨fun a b h => hO.1 a.1 b.1 h, fun a b h => hO.2 a.1 b.1 h⟩
  have hcardS : Fintype.card S = n - 1 := by
    have h1 : Fintype.card S = Fintype.card ↥(Finset.univ.erase l) := by
      refine Fintype.card_of_bijective (f := fun x : S => (⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩ : Finset.univ.erase l)) ⟨?_, ?_⟩
      · intro a b h; exact Subtype.ext (congrArg (fun z : ↥(Finset.univ.erase l) => z.1) h)
      · rintro ⟨w, hw⟩; exact ⟨⟨w, (Finset.mem_erase.mp hw).1⟩, rfl⟩
    rw [h1, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, hW]
  have hpS : p ∈ S := fun h => hpl_ne (Set.mem_singleton_iff.mp h)
  -- Step 4: Embed D' = D - l with p ↦ vp (if p -> l) or p ↦ vm (if l -> p), then attach l!
  rcases adj_or_rev_orient hO hTlp.symm with hDpl | hDlp
  · obtain ⟨vp, hvp⟩ := hex_vp
    obtain ⟨f', hf'_inj, hf'_p⟩ := embeds_rooted_of_minDeg_ge (n - 1) (by omega) D' hcardS
      ⟨T.induce S, hT', hO'⟩ ⟨p, hpS⟩ G hG.1 (n - 2) (by omega) hmin_deg vp
    let img : Finset V := Finset.univ.image f'
    have himg_card : img.card = n - 1 := by
      rw [Finset.card_image_of_injective _ hf'_inj, Finset.card_univ, hcardS]
    have hvp_mem : vp ∈ img := hf'_p ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨p, hpS⟩ : S))
    have hsub : (Finset.univ.filter (fun u : V => G.Adj vp u)) \ (img.erase vp) ⊆
        (Finset.univ.filter (fun u : V => G.Adj vp u)) \ img := by
      intro u hu
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase] at hu ⊢
      exact ⟨hu.1, fun huimg => hu.2 ⟨(ne_of_adj_tourn hG hu.1).symm, huimg⟩⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.le_card_sdiff (img.erase vp) (Finset.univ.filter (fun u : V => G.Adj vp u))
    have hc3 : (img.erase vp).card = n - 2 := by rw [Finset.card_erase_of_mem hvp_mem, himg_card]; omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
      0 < ((Finset.univ.filter (fun u : V => G.Adj vp u)) \ img).card)
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    let f : W → V := fun w => if hw : w = l then z else f' ⟨w, hw⟩
    refine ⟨⟨f, ?_⟩, ?_⟩
    · intro a b hab
      by_cases hal : a = l <;> by_cases hbl : b = l
      · exact absurd (hal.trans hbl.symm) (T.ne_of_adj (hO.1 a b hab))
      · subst hal
        have hbp : b = p := hl_uniq b (hO.1 a b hab)
        rw [hbp] at hab; exact absurd hab ((hO.2 p a (hO.1 p a hDpl)).mp hDpl)
      · subst hbl
        have hap : a = p := hl_uniq a (hO.1 a b hab).symm
        subst hap; simp only [f, hal, ↓reduceDIte, hf'_p]; exact hz.1
      · simp only [f, hal, hbl, ↓reduceDIte]; exact f'.map_adj' hab
    · intro a b hEq
      change f a = f b at hEq
      by_cases hal : a = l <;> by_cases hbl : b = l
      · exact hal.trans hbl.symm
      · simp only [f, hal, hbl, ↓reduceDIte] at hEq
        exact absurd (hEq ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨b, hbl⟩ : S))) hz.2
      · simp only [f, hal, hbl, ↓reduceDIte] at hEq
        exact absurd (hEq.symm ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨a, hal⟩ : S))) hz.2
      · simp only [f, hal, hbl, ↓reduceDIte] at hEq
        exact congrArg Subtype.val (hf'_inj hEq)
  · obtain ⟨vm, hvm⟩ := hex_vm
    obtain ⟨f', hf'_inj, hf'_p⟩ := embeds_rooted_of_minDeg_ge (n - 1) (by omega) D' hcardS
      ⟨T.induce S, hT', hO'⟩ ⟨p, hpS⟩ G hG.1 (n - 2) (by omega) hmin_deg vm
    let img : Finset V := Finset.univ.image f'
    have himg_card : img.card = n - 1 := by
      rw [Finset.card_image_of_injective _ hf'_inj, Finset.card_univ, hcardS]
    have hvm_mem : vm ∈ img := hf'_p ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨p, hpS⟩ : S))
    have hsub : (Finset.univ.filter (fun u : V => G.Adj u vm)) \ (img.erase vm) ⊆
        (Finset.univ.filter (fun u : V => G.Adj u vm)) \ img := by
      intro u hu
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase] at hu ⊢
      exact ⟨hu.1, fun huimg => hu.2 ⟨ne_of_adj_tourn hG hu.1, huimg⟩⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.le_card_sdiff (img.erase vm) (Finset.univ.filter (fun u : V => G.Adj u vm))
    have hc3 : (img.erase vm).card = n - 2 := by rw [Finset.card_erase_of_mem hvm_mem, himg_card]; omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
      0 < ((Finset.univ.filter (fun u : V => G.Adj u vm)) \ img).card)
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    let f : W → V := fun w => if hw : w = l then z else f' ⟨w, hw⟩
    refine ⟨⟨f, ?_⟩, ?_⟩
    · intro a b hab
      by_cases hal : a = l <;> by_cases hbl : b = l
      · exact absurd (hal.trans hbl.symm) (T.ne_of_adj (hO.1 a b hab))
      · subst hal
        have hbp : b = p := hl_uniq b (hO.1 a b hab)
        subst hbp; simp only [f, hbl, ↓reduceDIte, hf'_p]; exact hz.1
      · subst hbl
        have hap : a = p := hl_uniq a (hO.1 a b hab).symm
        rw [hap] at hab; exact absurd hab ((hO.2 b p (hO.1 b p hDlp)).mp hDlp)
      · simp only [f, hal, hbl, ↓reduceDIte]; exact f'.map_adj' hab
    · intro a b hEq
      change f a = f b at hEq
      by_cases hal : a = l <;> by_cases hbl : b = l
      · exact hal.trans hbl.symm
      · simp only [f, hal, hbl, ↓reduceDIte] at hEq
        exact absurd (hEq ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨b, hbl⟩ : S))) hz.2
      · simp only [f, hal, hbl, ↓reduceDIte] at hEq
        exact absurd (hEq.symm ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨a, hal⟩ : S))) hz.2
      · simp only [f, hal, hbl, ↓reduceDIte] at hEq
        exact congrArg Subtype.val (hf'_inj hEq)

end ProofWork.NearRegular

theorem OMA.solution : OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1.H2 := by
  intro n hn W _ _ D _ hW hTree _ _ _ _ V _ _ G _ hV hG _ hNR
  exact ProofWork.NearRegular.embeds_near_regular (by omega) D hW hTree G hV hG hNR
