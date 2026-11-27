import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1
import Mathlib

/-! Reduction closing H(n) <= 10 (all n <= 46) for K_4-free Erdos 151 via the
two-vertex adjacent-anchor deletion inequality with overlap saving. -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1

/-- Residual open core at H(n) >= 11 (n >= 47). -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    11 ≤ Erdos151.H n →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ v ∈ S, 8 ≤ (S.filter (G.Adj v)).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- Ramsey upper bound R(3,8) <= 28. -/
def H2 : Prop := 8 ≤ Erdos151.H 28

/-- Ramsey lower bounds R(3,9) >= 36 and R(3,10) >= 40. -/
def H3 : Prop :=
  (∀ n, 9 ≤ Erdos151.H n → 36 ≤ n) ∧ (∀ n, 10 ≤ Erdos151.H n → 40 ≤ n)

/-- Bikov 7-vertex link-extension lemma. -/
def H4 : Prop :=
  ∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)

section Proof

-- === BEGIN HELPERS ===
private lemma transversal_le_of_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (hB : k ≤ B.card)
    (hfree : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B)) :
    G.cliqueTransversalNumber ≤ n - k := by
  classical
  have hT : G.IsCliqueTransversal (Finset.univ \ B) := by
    intro K hK
    by_contra h
    apply hfree K hK
    intro x hx
    by_contra hxB
    exact h ⟨x, hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩⟩
  have hm : (Finset.univ \ B).card ∈
      {j : ℕ | ∃ T : Finset (Fin n), G.IsCliqueTransversal T ∧ T.card = j} :=
    ⟨_, hT, rfl⟩
  have hs := Nat.sInf_le hm
  change G.cliqueTransversalNumber ≤ (Finset.univ \ B).card at hs
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)] at hs
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  omega

private lemma free_of_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin n → Bool) (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      ¬ (c x y = c x z ∧ c x y = c y z)) :
    ∃ B : Finset (Fin n), Erdos151.H n ≤ B.card ∧
      ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B) := by
  classical
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ (c x y = true ∨ ¬ ∃ w, G.Adj x w ∧ G.Adj y w)
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inl ((hs _ _).trans h))
      (fun h => Or.inr (fun ⟨w, hw, hw'⟩ => h ⟨w, hw', hw⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hF : F.CliqueFree 3 := by
    intro t h
    obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.mp h
    have hxyt : c x y = true := hxy.2.resolve_right (fun h => h ⟨z, hxz.1, hyz.1⟩)
    have hxzt : c x z = true := hxz.2.resolve_right (fun h => h ⟨y, hxy.1, hyz.1.symm⟩)
    have hyzt : c y z = true := hyz.2.resolve_right (fun h => h ⟨x, hxy.1.symm, hxz.1.symm⟩)
    exact hc x y z hxy.1 hxz.1 hyz.1 ⟨hxyt.trans hxzt.symm, hxyt.trans hyzt.symm⟩
  have hAtt : ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
    let sizes : Set ℕ :=
      {k | ∀ Q : SimpleGraph (Fin n), Q.CliqueFree 3 → ∃ s, Q.IsNIndepSet k s}
    have hnonempty : sizes.Nonempty := ⟨0, fun _ _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
    have hfinite : sizes.Finite := (Set.finite_Iic n).subset fun k hk => by
      obtain ⟨s, hs⟩ := hk F hF
      simpa [hs.card_eq] using Finset.card_le_univ s
    exact hnonempty.csSup_mem hfinite F hF
  obtain ⟨I, hI⟩ := hAtt
  refine ⟨I, hI.card_eq.ge, ?_⟩
  intro t ht htI
  have hNo {x y : Fin n} (hx : x ∈ t) (hy : y ∈ t) (hxy : G.Adj x y) : c x y = false := by
    cases hb : c x y
    · rfl
    · exact (hI.isIndepSet (htI hx) (htI hy) hxy.ne ⟨hxy, Or.inl hb⟩).elim
  have hNotThree : t.card < 3 := by
    by_contra! hLarge
    obtain ⟨u, hu, huC⟩ := exists_subset_card_eq hLarge
    have hClique : G.IsNClique 3 u :=
      ⟨fun _ hx _ hy hxy => ht.1.1 (hu hx) (hu hy) hxy, huC⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp hClique
    have hx : x ∈ t := hu (by simp)
    have hy : y ∈ t := hu (by simp)
    have hz : z ∈ t := hu (by simp)
    have h1 := hNo hx hy hxy
    have h2 := hNo hx hz hxz
    have h3 := hNo hy hz hyz
    exact hc x y z hxy hxz hyz ⟨h1.trans h2.symm, h1.trans h3.symm⟩
  have hTwo : t.card = 2 := by have := ht.2; omega
  obtain ⟨x, y, hxy, htxy⟩ := card_eq_two.mp hTwo
  have hx : x ∈ t := by simp [htxy]
  have hy : y ∈ t := by simp [htxy]
  have hAdj := ht.1.1 hx hy hxy
  have hN : ¬ ∃ w, G.Adj x w ∧ G.Adj y w := by
    rintro ⟨w, hwx, hwy⟩
    have hSub : G.IsClique (↑(insert w t) : Set (Fin n)) := by
      rw [coe_insert]
      apply ht.1.1.insert
      intro u hu _
      have : u = x ∨ u = y := by simpa [htxy] using hu
      exact this.elim (fun h => h ▸ hwx.symm) (fun h => h ▸ hwy.symm)
    have hwMem : w ∈ t := ht.1.2 hSub (subset_insert _ _) (mem_insert_self _ _)
    have : w = x ∨ w = y := by simpa [htxy] using hwMem
    exact this.elim hwx.ne.symm hwy.ne.symm
  exact hI.isIndepSet (htI hx) (htI hy) hxy ⟨hAdj, Or.inr hN⟩

private lemma beta_of_coloring_28 (h2 : H2) (h4 : H4)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (R : Finset (Fin n)) (hR : 28 ≤ R.card) :
    ∃ B : Finset (Fin n), B ⊆ R ∧ 8 ≤ B.card ∧
      ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B) := by
  classical
  obtain ⟨S, hSR, hS⟩ := Finset.exists_subset_card_eq hR
  let E : Fin 28 ≃ ↥S := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  let e : Fin 28 ↪ Fin n :=
    ⟨fun i => (E i).val, fun _ _ h => E.injective (Subtype.ext h)⟩
  let Q : SimpleGraph (Fin 28) := {
    Adj := fun i j => G.Adj (e i) (e j)
    symm := ⟨fun _ _ h => G.symm.symm _ _ h⟩
    loopless := ⟨fun _ h => G.irrefl h⟩ }
  have mapClique (U : Finset (Fin 28)) (hU : Q.IsClique (↑U : Set (Fin 28))) :
      G.IsClique (↑(U.map e) : Set (Fin n)) := by
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (show a ∈ U.map e from ha)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (show b ∈ U.map e from hb)
    exact hU hi hj (fun h => hab (congrArg (fun k => e k) h))
  have hQ : Q.CliqueFree 4 := by
    intro U hU
    exact hG (U.map e) ⟨mapClique U hU.1, by simpa only [Finset.card_map] using hU.2⟩
  have noFour (w x y z : Fin 28) (hwx : Q.Adj w x) (hwy : Q.Adj w y)
      (hwz : Q.Adj w z) (hxy : Q.Adj x y) (hxz : Q.Adj x z) (hyz : Q.Adj y z) : False := by
    have hwN : w ∉ ({x, y, z} : Finset (Fin 28)) := by
      simp [hwx.ne, hwy.ne, hwz.ne]
    have hxN : x ∉ ({y, z} : Finset (Fin 28)) := by
      simp [hxy.ne, hxz.ne]
    have hyN : y ∉ ({z} : Finset (Fin 28)) := by simp [hyz.ne]
    apply hQ ({w, x, y, z} : Finset (Fin 28))
    constructor
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;>
        first | exact (hab rfl).elim | assumption | exact Q.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hwN, Finset.card_insert_of_notMem hxN,
        Finset.card_insert_of_notMem hyN]
      simp
  have hfree : ∃ B : Finset (Fin 28), 8 ≤ B.card ∧
      ∀ K : Finset (Fin 28), Q.IsBigMaximalClique K → ¬ (K ⊆ B) := by
    by_cases hlarge : ∃ w : Fin 28, 8 ≤ (Finset.univ.filter (Q.Adj w)).card
    · obtain ⟨w, hw⟩ := hlarge
      refine ⟨Finset.univ.filter (Q.Adj w), hw, ?_⟩
      intro K hK hKN
      have hc : Q.IsClique (↑(insert w K) : Set (Fin 28)) := by
        rw [Finset.coe_insert]
        apply hK.1.1.insert
        intro a ha _
        exact (Finset.mem_filter.mp (hKN ha)).2
      have hwK : w ∈ K := hK.1.2 hc (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
      exact Q.irrefl (Finset.mem_filter.mp (hKN hwK)).2
    · let Good (U : Finset (Fin 28)) (c : Fin 28 → Fin 28 → Bool) : Prop :=
        ∀ x y z, x ∈ U → y ∈ U → z ∈ U → Q.Adj x y → Q.Adj x z → Q.Adj y z →
          ¬ (c x y = c x z ∧ c x y = c y z)
      have build (U : Finset (Fin 28)) :
          ∃ c : Fin 28 → Fin 28 → Bool, (∀ x y, c x y = c y x) ∧ Good U c := by
        induction U using Finset.induction_on with
        | empty =>
          refine ⟨fun _ _ => false, fun _ _ => rfl, ?_⟩
          intro x y z hx
          simp at hx
        | @insert w U hw ih =>
          obtain ⟨c, hs, hc⟩ := ih
          let P := U.filter (Q.Adj w)
          have hp : P.card ≤ 7 := by
            have hsub : P ⊆ Finset.univ.filter (Q.Adj w) := by
              intro a ha
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
            have hle := Finset.card_le_card hsub
            have hlt : ¬ 8 ≤ (Finset.univ.filter (Q.Adj w)).card := fun h => hlarge ⟨w, h⟩
            omega
          let J : Fin P.card ≃ ↥P := (Fintype.equivFinOfCardEq (by simp)).symm
          let L : SimpleGraph (Fin P.card) := {
            Adj := fun i j => Q.Adj (J i).val (J j).val
            symm := ⟨fun _ _ h => Q.symm.symm _ _ h⟩
            loopless := ⟨fun _ h => Q.irrefl h⟩ }
          have hL : L.CliqueFree 3 := by
            intro T hT
            obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.mp hT
            have hn (i : Fin P.card) : Q.Adj w (J i).val :=
              (Finset.mem_filter.mp (J i).property).2
            exact noFour w (J x).val (J y).val (J z).val (hn x) (hn y) (hn z) hxy hxz hyz
          obtain ⟨d, hd⟩ := h4 P.card L hp hL
            (fun i j => c (J i).val (J j).val) (fun i j => hs (J i).val (J j).val)
          let paint (a : Fin 28) : Bool := if ha : a ∈ P then d (J.symm ⟨a, ha⟩) else false
          have valid (a b : Fin 28) (ha : a ∈ P) (hb : b ∈ P) (hab : Q.Adj a b) :
              ¬ (paint a = c a b ∧ paint b = c a b) := by
            have he : L.Adj (J.symm ⟨a, ha⟩) (J.symm ⟨b, hb⟩) := by
              change Q.Adj (J (J.symm ⟨a, ha⟩)).val (J (J.symm ⟨b, hb⟩)).val
              simpa only [Equiv.apply_symm_apply] using hab
            simpa [paint, ha, hb] using hd _ _ he
          let c' (a b : Fin 28) : Bool :=
            if a = w then paint b else if b = w then paint a else c a b
          refine ⟨c', ?_, ?_⟩
          · intro a b
            by_cases ha : a = w
            · by_cases hb : b = w
              · subst a
                subst b
                rfl
              · simp [c', ha, hb]
            · by_cases hb : b = w
              · simp [c', ha, hb]
              · simpa [c', ha, hb] using hs a b
          · intro x y z hx hy hz hxy hxz hyz hm
            have old (a : Fin 28) (ha : a ∈ insert w U) (hna : a ≠ w) : a ∈ U :=
              (Finset.mem_insert.mp ha).resolve_left hna
            have near (a : Fin 28) (ha : a ∈ insert w U) (hna : a ≠ w)
                (hwa : Q.Adj w a) : a ∈ P := Finset.mem_filter.mpr ⟨old a ha hna, hwa⟩
            by_cases ex : x = w
            · subst x
              have ey : y ≠ w := hxy.ne.symm
              have ez : z ≠ w := hxz.ne.symm
              have hh : paint y = paint z ∧ paint y = c y z := by
                simpa [c', ey, ez] using hm
              exact valid y z (near y hy ey hxy) (near z hz ez hxz) hyz
                ⟨hh.2, hh.1.symm.trans hh.2⟩
            · by_cases ey : y = w
              · subst y
                have ez : z ≠ w := hyz.ne.symm
                have hh : paint x = c x z ∧ paint x = paint z := by
                  simpa [c', ex, ez] using hm
                exact valid x z (near x hx ex (Q.symm.symm _ _ hxy)) (near z hz ez hyz) hxz
                  ⟨hh.1, hh.2.symm.trans hh.1⟩
              · by_cases ez : z = w
                · subst z
                  have hh : c x y = paint x ∧ c x y = paint y := by
                    simpa [c', ex, ey] using hm
                  exact valid x y (near x hx ex (Q.symm.symm _ _ hxz))
                    (near y hy ey (Q.symm.symm _ _ hyz)) hxy ⟨hh.1.symm, hh.2.symm⟩
                · exact hc x y z (old x hx ex) (old y hy ey) (old z hz ez) hxy hxz hyz
                    (by simpa [c', ex, ey, ez] using hm)
      obtain ⟨c, hs, hc⟩ := build Finset.univ
      obtain ⟨B, hB, havoid⟩ := free_of_coloring Q c hs (fun x y z =>
        hc x y z (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _))
      have hH : 8 ≤ Erdos151.H 28 := h2
      exact ⟨B, hH.trans hB, havoid⟩
  obtain ⟨B, hB, havoid⟩ := hfree
  refine ⟨B.map e, ?_, by simpa only [Finset.card_map] using hB, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    exact hSR (E i).property
  · intro K hK hKB
    let T := Finset.univ.filter (fun i : Fin 28 => e i ∈ K)
    have hmap : T.map e = K := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
        exact (Finset.mem_filter.mp hi).2
      · intro ha
        obtain ⟨i, _, hi⟩ := Finset.mem_map.mp (hKB ha)
        exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa only [hi] using ha⟩, hi⟩
    have hTB : T ⊆ B := by
      intro i hi
      have hiK : e i ∈ K := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp (hKB hiK)
      exact (e.injective he) ▸ hj
    apply havoid T ?_ hTB
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi j hj hij
      exact hK.1.1 (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        (fun he => hij (e.injective he))
    · intro U hU hTU i hi
      have hKU : K ⊆ U.map e := by
        rw [← hmap]
        intro a ha
        obtain ⟨j, hj, he⟩ := Finset.mem_map.mp ha
        exact Finset.mem_map.mpr ⟨j, hTU hj, he⟩
      have hiK : e i ∈ K := hK.1.2 (mapClique U hU) hKU
        (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiK⟩
    · have hcard := congrArg Finset.card hmap
      rw [Finset.card_map] at hcard
      rw [hcard]
      exact hK.2

private lemma maximal_clique_link_obstruction {n : ℕ} (G : SimpleGraph (Fin n))
    (K : Finset (Fin n)) (hK : G.IsBigMaximalClique K) (w : Fin n) (hw : w ∈ K)
    (hlink : ∀ x ∈ K, G.Adj w x → ∃ z, G.Adj w z ∧ G.Adj x z) :
    ∃ x ∈ K, ∃ y ∈ K, G.Adj w x ∧ G.Adj w y ∧ G.Adj x y := by
  classical
  have hcard : 1 ≤ (K.erase w).card := by
    rw [Finset.card_erase_of_mem hw]
    have := hK.2
    omega
  by_cases h2 : 2 ≤ (K.erase w).card
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (K.erase w).card)
    have hxK : x ∈ K := Finset.mem_of_mem_erase hx
    have hyK : y ∈ K := Finset.mem_of_mem_erase hy
    have hwx : w ≠ x := (Finset.ne_of_mem_erase hx).symm
    have hwy : w ≠ y := (Finset.ne_of_mem_erase hy).symm
    exact ⟨x, hxK, y, hyK, hK.1.1 hw hxK hwx, hK.1.1 hw hyK hwy, hK.1.1 hxK hyK hxy⟩
  · have h1 : (K.erase w).card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hxE : x ∈ K.erase w := by simp [hx]
    have hxK : x ∈ K := Finset.mem_of_mem_erase hxE
    have hwx : w ≠ x := (Finset.ne_of_mem_erase hxE).symm
    have hadj : G.Adj w x := hK.1.1 hw hxK hwx
    obtain ⟨z, hwz, hxz⟩ := hlink x hxK hadj
    have hKeq : K = {w, x} := by
      ext u
      constructor
      · intro hu
        by_cases huw : u = w
        · simp [huw]
        · have : u ∈ K.erase w := Finset.mem_erase.mpr ⟨huw, hu⟩
          rw [hx, Finset.mem_singleton] at this
          simp [this]
      · intro hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hw
        · exact hxK
    have hSub : G.IsClique (↑(insert z K) : Set (Fin n)) := by
      rw [coe_insert]
      apply hK.1.1.insert
      intro u hu _
      have : u = w ∨ u = x := by simpa [hKeq] using hu
      exact this.elim (fun h => h ▸ hwz.symm) (fun h => h ▸ hxz.symm)
    have hzK : z ∈ K := hK.1.2 hSub (subset_insert _ _) (mem_insert_self _ _)
    have : z = w ∨ z = x := by simpa [hKeq] using hzK
    exact (this.elim hwz.ne.symm hxz.ne.symm).elim

private lemma free_set_deletion {n : ℕ} (G : SimpleGraph (Fin n))
    (A D B : Finset (Fin n)) (I : Fin n → Finset (Fin n))
    (hcover : ∀ w ∈ A, (Finset.univ.filter (G.Adj w)) \ I w ⊆ D)
    (hlink : ∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z)
    (hind : ∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y)
    (hanchors : ∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w)
    (hBD : B ⊆ Finset.univ \ D)
    (hB : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B)) :
    ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ A ∪ B) := by
  classical
  intro K hK hKU
  by_cases hm : ∃ w ∈ K, w ∈ A
  · obtain ⟨w, hwK, hwA⟩ := hm
    have hKI : ∀ x ∈ K, G.Adj w x → x ∈ I w := by
      intro x hxK hwx
      rcases Finset.mem_union.mp (hKU hxK) with hxA | hxB
      · exact hanchors w hwA x hxA hwx
      · by_contra hxI
        have hxD : x ∈ D := hcover w hwA (Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwx⟩, hxI⟩)
        exact (Finset.mem_sdiff.mp (hBD hxB)).2 hxD
    obtain ⟨x, hxK, y, hyK, hwx, hwy, hxy⟩ :=
      maximal_clique_link_obstruction G K hK w hwK
        (fun x hxK hwx => (hlink w hwA x (hKI x hxK hwx)).2)
    exact hind w hwA x (hKI x hxK hwx) y (hKI y hyK hwy) hxy
  · apply hB K hK
    intro x hxK
    rcases Finset.mem_union.mp (hKU hxK) with hxA | hxB
    · exact (hm ⟨x, hxK, hxA⟩).elim
    · exact hxB

private lemma extend_from_28 (h2 : H2) (h4 : H4) {n k : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (A D : Finset (Fin n)) (I : Fin n → Finset (Fin n))
    (hk : k ≤ A.card + 8) (hbudget : D.card + 28 ≤ n) (hAD : A ⊆ D)
    (hcover : ∀ w ∈ A, (Finset.univ.filter (G.Adj w)) \ I w ⊆ D)
    (hlink : ∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z)
    (hind : ∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y)
    (hanchors : ∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) :
    G.cliqueTransversalNumber ≤ n - k := by
  classical
  have hR : 28 ≤ (Finset.univ \ D).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨B, hBD, hBcard, hB⟩ := beta_of_coloring_28 h2 h4 G hG _ hR
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr
    (fun _ hxA hxB => (Finset.mem_sdiff.mp (hBD hxB)).2 (hAD hxA))
  refine transversal_le_of_free G (A ∪ B) ?_ ?_
  · rw [Finset.card_union_of_disjoint hdisj]
    omega
  · exact free_set_deletion G A D B I hcover hlink hind hanchors hBD hB

private lemma card_two {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    ({u, v} : Finset (Fin n)).card = 2 := by
  classical
  have hn : u ∉ ({v} : Finset (Fin n)) := by simpa using huv
  rw [Finset.card_insert_of_notMem hn] <;> simp

private lemma extend_pair_from_28 (h2 : H2) (h4 : H4) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4) (hn : 40 ≤ n)
    (u v : Fin n) (huv : u ≠ v) (Iu Iv : Finset (Fin n))
    (hIu : ∀ x ∈ Iu, G.Adj u x ∧ ∃ z, G.Adj u z ∧ G.Adj x z)
    (hIv : ∀ x ∈ Iv, G.Adj v x ∧ ∃ z, G.Adj v z ∧ G.Adj x z)
    (hiu : ∀ x ∈ Iu, ∀ y ∈ Iu, ¬ G.Adj x y)
    (hiv : ∀ x ∈ Iv, ∀ y ∈ Iv, ¬ G.Adj x y)
    (hu : G.Adj u v → v ∈ Iu) (hv : G.Adj v u → u ∈ Iv)
    (hcost : ((Finset.univ.filter (G.Adj u)) \ Iu).card +
        ((Finset.univ.filter (G.Adj v)) \ Iv).card ≤ 10 +
      (((Finset.univ.filter (G.Adj u)) \ Iu) ∩
        ((Finset.univ.filter (G.Adj v)) \ Iv)).card) :
    G.cliqueTransversalNumber ≤ n - 10 := by
  classical
  let A : Finset (Fin n) := {u, v}
  let I : Fin n → Finset (Fin n) := fun w => if w = u then Iu else Iv
  let Du := (Finset.univ.filter (G.Adj u)) \ Iu
  let Dv := (Finset.univ.filter (G.Adj v)) \ Iv
  let D := A ∪ (Du ∪ Dv)
  have hA : A.card = 2 := card_two huv
  have hsum := Finset.card_union_add_card_inter Du Dv
  have hbound := Finset.card_union_le A (Du ∪ Dv)
  change D.card ≤ A.card + (Du ∪ Dv).card at hbound
  change Du.card + Dv.card ≤ 10 + (Du ∩ Dv).card at hcost
  have hbudget : D.card + 28 ≤ n := by omega
  have hcases : ∀ w ∈ A, w = u ∨ w = v := by
    intro w hw
    simpa [A] using hw
  refine extend_from_28 h2 h4 G hG A D I (k := 10) ?_ hbudget ?_ ?_ ?_ ?_ ?_
  · omega
  · intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro w hw x hx
    rcases hcases w hw with rfl | rfl
    · have hx' : x ∈ Du := by simpa [Du, I] using hx
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hx')))
    · have hx' : x ∈ Dv := by simpa [Dv, I, Ne.symm huv] using hx
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hx')))
  · intro w hw x hx
    rcases hcases w hw with rfl | rfl
    · exact hIu x (by simpa [I] using hx)
    · exact hIv x (by simpa [I, Ne.symm huv] using hx)
  · intro w hw x hx y hy
    rcases hcases w hw with rfl | rfl
    · exact hiu x (by simpa [I] using hx) y (by simpa [I] using hy)
    · exact hiv x (by simpa [I, Ne.symm huv] using hx) y
        (by simpa [I, Ne.symm huv] using hy)
  · intro w hw x hx hadj
    rcases hcases w hw with rfl | rfl <;> rcases hcases x hx with rfl | rfl
    · exfalso
      simpa using hadj
    · simpa [I] using hu hadj
    · simpa [I, Ne.symm huv] using hv hadj
    · exfalso
      simpa using hadj

private lemma case_H9 (h2 : H2) (h4 : H4) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hn : 36 ≤ n) (hH : Erdos151.H n = 9)
    (hdeg : ∀ w, (Finset.univ.filter (G.Adj w)).card < 9) :
    G.cliqueTransversalNumber ≤ n - 9 := by
  classical
  by_cases ht : ∃ w x z : Fin n, G.Adj w x ∧ G.Adj w z ∧ G.Adj x z
  · obtain ⟨w, x, z, hwx, hwz, hxz⟩ := ht
    let A : Finset (Fin n) := {w}
    let I : Fin n → Finset (Fin n) := fun _ => {x}
    let Dw := (Finset.univ.filter (G.Adj w)) \ ({x} : Finset (Fin n))
    let D := A ∪ Dw
    have hxN : ({x} : Finset (Fin n)) ⊆ Finset.univ.filter (G.Adj w) := by
      intro a ha
      have : a = x := by simpa using ha
      subst a
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwx⟩
    have hDw : Dw.card ≤ 7 := by
      dsimp [Dw]
      rw [Finset.card_sdiff_of_subset hxN, Finset.card_singleton]
      have hd := hdeg w
      omega
    have hA : A.card = 1 := by simp [A]
    have hD : D.card + 28 ≤ n := by
      have hh := Finset.card_union_le A Dw
      change D.card ≤ A.card + Dw.card at hh
      omega
    refine extend_from_28 h2 h4 G hG A D I (k := 9) ?_ hD ?_ ?_ ?_ ?_ ?_
    · omega
    · intro a ha
      exact Finset.mem_union.mpr (Or.inl ha)
    · intro a ha y hy
      have : a = w := by simpa [A] using ha
      subst a
      exact Finset.mem_union.mpr (Or.inr hy)
    · intro a ha y hy
      have ha' : a = w := by simpa [A] using ha
      have hy' : y = x := by simpa [I] using hy
      subst a
      subst y
      exact ⟨hwx, z, hwz, hxz⟩
    · intro a ha y hy t ht'
      have hy' : y = x := by simpa [I] using hy
      have ht'' : t = x := by simpa [I] using ht'
      subst y
      subst t
      simp
    · intro a ha y hy hadj
      have ha' : a = w := by simpa [A] using ha
      have hy' : y = w := by simpa [A] using hy
      subst a
      subst y
      exfalso
      simpa using hadj
  · obtain ⟨B, hB, hfree⟩ := free_of_coloring G (fun _ _ => false)
        (fun _ _ => rfl) (by
          intro a b c hab hac hbc _
          exact ht ⟨a, b, c, hab, hac, hbc⟩)
    exact transversal_le_of_free G B (by simpa [hH] using hB) hfree

private lemma r34_and_triple_in_8 {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (w : Fin n) (P : Finset (Fin n))
    (hP : P ⊆ Finset.univ.filter (G.Adj w)) (h8 : 8 ≤ P.card)
    (halpha : ∀ I : Finset (Fin n), I ⊆ P →
      (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) → I.card ≤ 3) :
    P.card = 8 ∧ ∀ v ∈ P, ∃ I : Finset (Fin n), I ⊆ P ∧
      (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧ I.card = 3 ∧ v ∈ I := by
  classical
  have noTri (x : Fin n) (hx : x ∈ P) (y : Fin n) (hy : y ∈ P)
      (z : Fin n) (hz : z ∈ P) (hxy : G.Adj x y) (hxz : G.Adj x z)
      (hyz : G.Adj y z) : False := by
    have hwx := (Finset.mem_filter.mp (hP hx)).2
    have hwy := (Finset.mem_filter.mp (hP hy)).2
    have hwz := (Finset.mem_filter.mp (hP hz)).2
    have hwN : w ∉ ({x, y, z} : Finset (Fin n)) := by
      simp [hwx.ne, hwy.ne, hwz.ne]
    have hxN : x ∉ ({y, z} : Finset (Fin n)) := by simp [hxy.ne, hxz.ne]
    have hyN : y ∉ ({z} : Finset (Fin n)) := by simp [hyz.ne]
    apply hG ({w, x, y, z} : Finset (Fin n))
    constructor
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;>
        first | exact (hab rfl).elim | assumption | exact G.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hwN, Finset.card_insert_of_notMem hxN,
        Finset.card_insert_of_notMem hyN]
      simp
  let N (S : Finset (Fin n)) (a : Fin n) := S.filter (G.Adj a)
  let M (S : Finset (Fin n)) (a : Fin n) := S.erase a \ N S a
  have memN (S : Finset (Fin n)) (a x : Fin n) :
      x ∈ N S a ↔ x ∈ S ∧ G.Adj a x := Finset.mem_filter
  have memM (S : Finset (Fin n)) (a x : Fin n) :
      x ∈ M S a ↔ x ∈ S ∧ x ≠ a ∧ ¬ G.Adj a x := by
    constructor
    · intro h
      obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp h
      obtain ⟨hne, hs⟩ := Finset.mem_erase.mp he
      exact ⟨hs, hne, fun hadj => hn ((memN S a x).mpr ⟨hs, hadj⟩)⟩
    · rintro ⟨hs, hne, hn⟩
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨hne, hs⟩, fun h => hn ((memN S a x).mp h).2⟩
  have cardM (S : Finset (Fin n)) (a : Fin n) (ha : a ∈ S) :
      (M S a).card = S.card - 1 - (N S a).card := by
    have hsub : N S a ⊆ S.erase a := by
      intro x hx
      obtain ⟨hxS, hax⟩ := (memN S a x).mp hx
      exact Finset.mem_erase.mpr ⟨hax.ne.symm, hxS⟩
    change (S.erase a \ N S a).card = _
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem ha]
  have indN (S : Finset (Fin n)) (hSP : S ⊆ P) (a : Fin n) (ha : a ∈ S) :
      ∀ x ∈ N S a, ∀ y ∈ N S a, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨hxS, hax⟩ := (memN S a x).mp hx
    obtain ⟨hyS, hay⟩ := (memN S a y).mp hy
    exact noTri a (hSP ha) x (hSP hxS) y (hSP hyS) hax hay hxy
  have noEdge (S : Finset (Fin n)) (hSP : S ⊆ P) (h3 : 3 ≤ S.card) :
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ G.Adj x y := by
    by_contra hn
    have adj (x : Fin n) (hx : x ∈ S) (y : Fin n) (hy : y ∈ S)
        (hxy : x ≠ y) : G.Adj x y := by
      by_contra h
      exact hn ⟨x, hx, y, hy, hxy, h⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hp : ({x, y} : Finset (Fin n)) ⊆ S := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hx
      · exact hy
    have hr : 0 < (S \ ({x, y} : Finset (Fin n))).card := by
      rw [Finset.card_sdiff_of_subset hp, card_two hxy]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hr
    obtain ⟨hzS, hzN⟩ := Finset.mem_sdiff.mp hz
    have hzx : z ≠ x := fun h => hzN (by simp [h])
    have hzy : z ≠ y := fun h => hzN (by simp [h])
    exact noTri x (hSP hx) y (hSP hy) z (hSP hzS)
      (adj x hx y hy hxy) (adj x hx z hzS hzx.symm) (adj y hy z hzS hzy.symm)
  have triple (S : Finset (Fin n)) (hSP : S ⊆ P) (a : Fin n) (ha : a ∈ S)
      (hm : 3 ≤ (M S a).card) :
      ∃ I : Finset (Fin n), I ⊆ S ∧
        (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧ I.card = 3 ∧ a ∈ I := by
    have hMS : M S a ⊆ S := fun x hx => ((memM S a x).mp hx).1
    obtain ⟨x, hx, y, hy, hxy, hnot⟩ := noEdge (M S a) (fun u hu => hSP (hMS hu)) hm
    obtain ⟨hxS, hxa, hax⟩ := (memM S a x).mp hx
    obtain ⟨hyS, hya, hay⟩ := (memM S a y).mp hy
    have hxa' : ¬ G.Adj x a := fun h => hax h.symm
    have hya' : ¬ G.Adj y a := fun h => hay h.symm
    have hyx : ¬ G.Adj y x := fun h => hnot h.symm
    refine ⟨{a, x, y}, ?_, ?_, ?_, by simp⟩
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact ha
      · exact hxS
      · exact hyS
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | assumption | exact (fun h => G.irrefl h)
    · have hn : a ∉ ({x, y} : Finset (Fin n)) := by simp [hxa.symm, hya.symm]
      rw [Finset.card_insert_of_notMem hn, card_two hxy]
  have six (S : Finset (Fin n)) (hSP : S ⊆ P) (h6 : 6 ≤ S.card) :
      ∃ I : Finset (Fin n), I ⊆ S ∧
        (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧ I.card = 3 := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    by_cases hn : 3 ≤ (N S a).card
    · obtain ⟨I, hIN, hIc⟩ := Finset.exists_subset_card_eq hn
      refine ⟨I, fun x hx => ((memN S a x).mp (hIN hx)).1, ?_, hIc⟩
      intro x hx y hy
      exact indN S hSP a ha x (hIN hx) y (hIN hy)
    · have hc := cardM S a ha
      obtain ⟨I, hi, hind, hic, _⟩ := triple S hSP a ha (by omega)
      exact ⟨I, hi, hind, hic⟩
  have sumConst (S : Finset (Fin n)) (j : ℕ) :
      Finset.sum S (fun _ => j) = S.card * j := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih,
        Nat.add_mul, Nat.one_mul, Nat.add_comm j]
  have parity (S : Finset (Fin n)) :
      ∃ k : ℕ, Finset.sum S (fun x => (N S x).card) = 2 * k := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert a T ha ih =>
      obtain ⟨k, hk⟩ := ih
      have step (x : Fin n) : (N (insert a T) x).card =
          (N T x).card + (if G.Adj a x then 1 else 0) := by
        have hn : a ∉ T.filter (G.Adj x) := fun h => ha (Finset.mem_filter.mp h).1
        change ((insert a T).filter (G.Adj x)).card = (T.filter (G.Adj x)).card + _
        by_cases hax : G.Adj a x
        · have hxa := hax.symm
          have he : (insert a T).filter (G.Adj x) = insert a (T.filter (G.Adj x)) := by
            simp [Finset.filter_insert, hxa]
          rw [he, Finset.card_insert_of_notMem hn, if_pos hax]
        · have hxa : ¬ G.Adj x a := fun h => hax h.symm
          simp [Finset.filter_insert, hxa, hax]
      have hself : (N (insert a T) a).card = (N T a).card := by
        have hna : ¬ G.Adj a a := fun h => G.irrefl h
        simpa [hna] using step a
      have hcount : Finset.sum T (fun x => if G.Adj a x then (1 : ℕ) else 0) =
          (N T a).card := by
        calc
          _ = Finset.sum (N T a) (fun _ => (1 : ℕ)) := by
            change _ = Finset.sum (T.filter (G.Adj a)) (fun _ => (1 : ℕ))
            rw [Finset.sum_filter]
          _ = _ := by rw [sumConst, Nat.mul_one]
      have hsum : Finset.sum T (fun x => (N (insert a T) x).card) =
          Finset.sum T (fun x => (N T x).card) + (N T a).card := by
        calc
          _ = Finset.sum T (fun x => (N T x).card + (if G.Adj a x then 1 else 0)) :=
            Finset.sum_congr rfl (fun x _ => step x)
          _ = _ := by rw [Finset.sum_add_distrib, hcount]
      refine ⟨k + (N T a).card, ?_⟩
      rw [Finset.sum_insert ha, hself, hsum, hk]
      omega
  have hcard : P.card = 8 := by
    by_contra hne
    obtain ⟨Q, hQP, hQ⟩ := Finset.exists_subset_card_eq (by omega : 9 ≤ P.card)
    have hdeg (a : Fin n) (ha : a ∈ Q) : (N Q a).card = 3 := by
      have hu : (N Q a).card ≤ 3 :=
        halpha (N Q a) (fun x hx => hQP ((memN Q a x).mp hx).1) (indN Q hQP a ha)
      by_contra hne'
      have hM := cardM Q a ha
      have hm : 6 ≤ (M Q a).card := by omega
      have hMP : M Q a ⊆ P := fun x hx => hQP ((memM Q a x).mp hx).1
      obtain ⟨I, hIM, hind, hIc⟩ := six (M Q a) hMP hm
      have hna : a ∉ I := fun h => ((memM Q a a).mp (hIM h)).2.1 rfl
      have hsub : insert a I ⊆ P := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hQP ha
        · exact hMP (hIM hx)
      have hIind : ∀ x ∈ insert a I, ∀ y ∈ insert a I, ¬ G.Adj x y := by
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hx' | hx
        · rcases Finset.mem_insert.mp hy with hy' | hy
          · rw [hx', hy'] at hxy
            exact G.irrefl hxy
          · rw [hx'] at hxy
            exact ((memM Q a y).mp (hIM hy)).2.2 hxy
        · rcases Finset.mem_insert.mp hy with hy' | hy
          · rw [hy'] at hxy
            exact ((memM Q a x).mp (hIM hx)).2.2 hxy.symm
          · exact hind x hx y hy hxy
      have hb := halpha (insert a I) hsub hIind
      rw [Finset.card_insert_of_notMem hna, hIc] at hb
      omega
    have hsum : Finset.sum Q (fun x => (N Q x).card) = 27 := by
      calc
        _ = Finset.sum Q (fun _ => (3 : ℕ)) := Finset.sum_congr rfl hdeg
        _ = _ := by rw [sumConst, hQ]
    obtain ⟨k, hk⟩ := parity Q
    omega
  refine ⟨hcard, ?_⟩
  intro v hv
  have hu : (N P v).card ≤ 3 :=
    halpha (N P v) (fun x hx => ((memN P v x).mp hx).1)
      (indN P (fun _ hx => hx) v hv)
  have hm := cardM P v hv
  exact triple P (fun _ hx => hx) v hv (by omega)

private theorem minimal_uncolorable_subgraph {n : ℕ} (G : SimpleGraph (Fin n))
    (hc : ¬ ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))) :
    ∃ Q : SimpleGraph (Fin n),
      (∀ x y, Q.Adj x y → G.Adj x y) ∧
      (¬ ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
        (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
          ¬ (c x y = c x z ∧ c x y = c y z))) ∧
      (∀ R : SimpleGraph (Fin n), (∀ x y, R.Adj x y → Q.Adj x y) →
        (∃ x y, Q.Adj x y ∧ ¬ R.Adj x y) →
        ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
          (∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z →
            ¬ (c x y = c x z ∧ c x y = c y z))) := by
  classical
  let Colorable (Q : SimpleGraph (Fin n)) : Prop :=
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))
  let E (Q : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p : Fin n × Fin n => Q.Adj p.1 p.2)
  let P (k : ℕ) : Prop := ∃ Q : SimpleGraph (Fin n),
    (∀ x y, Q.Adj x y → G.Adj x y) ∧ ¬ Colorable Q ∧ (E Q).card = k
  have hex : ∃ k, P k := ⟨(E G).card, G, fun _ _ h => h, hc, rfl⟩
  obtain ⟨Q, hQG, hQbad, hcard⟩ : P (Nat.find hex) := Nat.find_spec hex
  refine ⟨Q, hQG, hQbad, ?_⟩
  intro R hRQ hw
  change Colorable R
  by_contra hRbad
  have hsub : E R ⊆ E Q := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hRQ _ _ (Finset.mem_filter.mp hp).2⟩
  have hnsub : ¬ E Q ⊆ E R := by
    intro h
    obtain ⟨x, y, hxy, hnxy⟩ := hw
    have hp : (x, y) ∈ E Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    exact hnxy (Finset.mem_filter.mp (h hp)).2
  have hlt : (E R).card < (E Q).card := by
    apply Finset.card_lt_card
    first
    | exact ⟨hsub, hnsub⟩
    | exact lt_of_le_not_ge hsub hnsub
    | exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hnsub (he ▸ hsub)⟩
  have hp : P (E R).card := ⟨R, fun x y h => hQG x y (hRQ x y h), hRbad, rfl⟩
  have hle : Nat.find hex ≤ (E R).card := Nat.find_min' hex hp
  omega

private theorem restore_vertex_coloring (h4 : H4) {n : ℕ}
    (Q R : SimpleGraph (Fin n)) (hQ : Q.CliqueFree 4) (w : Fin n)
    (hw : (Finset.univ.filter (Q.Adj w)).card ≤ 7)
    (hR : ∀ x y, R.Adj x y ↔ Q.Adj x y ∧ x ≠ w ∧ y ≠ w)
    (hc : ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))) :
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z)) := by
  classical
  obtain ⟨c, hs, ht⟩ := hc
  let P : Finset (Fin n) := Finset.univ.filter (Q.Adj w)
  have hp : P.card ≤ 7 := by
    simpa [P] using hw
  let J : Fin P.card ≃ ↥P := (Fintype.equivFinOfCardEq (by simp)).symm
  let L : SimpleGraph (Fin P.card) := {
    Adj := fun i j => Q.Adj (J i).val (J j).val
    symm := ⟨fun _ _ h => Q.symm.symm _ _ h⟩
    loopless := ⟨fun _ h => Q.irrefl h⟩ }
  have noFour (a b q : Fin P.card)
      (hab : Q.Adj (J a).val (J b).val)
      (haq : Q.Adj (J a).val (J q).val)
      (hbq : Q.Adj (J b).val (J q).val)
      (hwa : Q.Adj w (J a).val)
      (hwb : Q.Adj w (J b).val)
      (hwq : Q.Adj w (J q).val) : False := by
    have hwN : w ∉ ({(J a).val, (J b).val, (J q).val} : Finset (Fin n)) := by
      simp [hwa.ne, hwb.ne, hwq.ne]
    have haN : (J a).val ∉ ({(J b).val, (J q).val} : Finset (Fin n)) := by
      simp [hab.ne, haq.ne]
    have hbN : (J b).val ∉ ({(J q).val} : Finset (Fin n)) := by
      simp [hbq.ne]
    apply hQ ({w, (J a).val, (J b).val, (J q).val} : Finset (Fin n))
    constructor
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;>
        first | exact (hxy rfl).elim | assumption | exact Q.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hwN, Finset.card_insert_of_notMem haN,
        Finset.card_insert_of_notMem hbN]
      simp
  have hL : L.CliqueFree 3 := by
    intro T hT
    obtain ⟨a, b, q, hab, haq, hbq, -⟩ := is3Clique_iff.mp hT
    have hn (i : Fin P.card) : Q.Adj w (J i).val :=
      (Finset.mem_filter.mp (J i).property).2
    exact noFour a b q hab haq hbq (hn a) (hn b) (hn q)
  obtain ⟨d, hd⟩ := h4 P.card L hp hL
    (fun i j => c (J i).val (J j).val) (fun i j => hs (J i).val (J j).val)
  let paint (a : Fin n) : Bool :=
    if ha : a ∈ P then d (J.symm ⟨a, ha⟩) else false
  have valid (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hab : Q.Adj a b) :
      ¬ (paint a = c a b ∧ paint b = c a b) := by
    have he : L.Adj (J.symm ⟨a, ha⟩) (J.symm ⟨b, hb⟩) := by
      change Q.Adj (J (J.symm ⟨a, ha⟩)).val (J (J.symm ⟨b, hb⟩)).val
      simpa only [Equiv.apply_symm_apply] using hab
    simpa [paint, ha, hb] using hd _ _ he
  let c' (a b : Fin n) : Bool :=
    if a = w then paint b else if b = w then paint a else c a b
  have hs' (a b : Fin n) : c' a b = c' b a := by
    by_cases ha : a = w
    · by_cases hb : b = w
      · subst a
        subst b
        rfl
      · simp [c', ha, hb]
    · by_cases hb : b = w
      · simp [c', ha, hb]
      · simpa [c', ha, hb] using hs a b
  refine ⟨c', hs', ?_⟩
  intro x y z hxy hxz hyz hm
  by_cases ex : x = w
  · subst x
    have ey : y ≠ w := hxy.ne.symm
    have ez : z ≠ w := hxz.ne.symm
    have hh : paint y = paint z ∧ paint y = c y z := by
      simpa [c', ey, ez] using hm
    exact valid y z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩) hyz
      ⟨hh.2, hh.1.symm.trans hh.2⟩
  · by_cases ey : y = w
    · subst y
      have ez : z ≠ w := hyz.ne.symm
      have hh : paint x = c x z ∧ paint x = paint z := by
        simpa [c', ex, ez] using hm
      exact valid x z
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.symm.symm _ _ hxy⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyz⟩) hxz
        ⟨hh.1, hh.2.symm.trans hh.1⟩
    · by_cases ez : z = w
      · subst z
        have hh : c x y = paint x ∧ c x y = paint y := by
          simpa [c', ex, ey] using hm
        exact valid x y
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.symm.symm _ _ hxz⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.symm.symm _ _ hyz⟩) hxy
          ⟨hh.1.symm, hh.2.symm⟩
      · exact ht x y z
          ((hR x y).mpr ⟨hxy, ex, ey⟩)
          ((hR x z).mpr ⟨hxz, ex, ez⟩)
          ((hR y z).mpr ⟨hyz, ey, ez⟩)
          (by simpa [c', ex, ey, ez] using hm)

private theorem restore_edge_coloring {n : ℕ}
    (Q R : SimpleGraph (Fin n)) (u v : Fin n)
    (hR : ∀ x y, R.Adj x y ↔ Q.Adj x y ∧
      ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)))
    (hsmall : ¬ ∃ z t : Fin n, z ≠ t ∧ Q.Adj u z ∧ Q.Adj v z ∧ Q.Adj u t ∧ Q.Adj v t)
    (hc : ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))) :
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z)) := by
  classical
  obtain ⟨c, hs, ht⟩ := hc
  obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ z, Q.Adj u z → Q.Adj v z → b ≠ c u z := by
    by_cases he : ∃ z, Q.Adj u z ∧ Q.Adj v z
    · obtain ⟨z, huz, hvz⟩ := he
      refine ⟨if c u z = true then false else true, ?_⟩
      intro t hut hvt
      have htz : t = z := by
        by_contra hne
        exact hsmall ⟨t, z, hne, hut, hvt, huz, hvz⟩
      subst t
      cases hcol : c u z <;> simp [hcol]
    · exact ⟨false, fun z huz hvz => (he ⟨z, huz, hvz⟩).elim⟩
  let E (x y : Fin n) : Prop := (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  have rev (x y : Fin n) (h : E x y) : E y x := by
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inr ⟨hy, hx⟩
    · exact Or.inl ⟨hy, hx⟩
  let d (x y : Fin n) : Bool := if E x y then b else c x y
  have ds (x y : Fin n) : d x y = d y x := by
    by_cases he : E x y
    · simp [d, he, rev x y he]
    · have hn : ¬ E y x := fun h => he (rev y x h)
      simpa [d, he, hn] using hs x y
  have avoid (x y z : Fin n) (he : E x y) (hxz : Q.Adj x z) (hyz : Q.Adj y z) :
      ¬ (d x y = d x z ∧ d x y = d y z) := by
    intro hm
    have hxy : d x y = b := if_pos he
    rcases he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst x
      subst y
      have hn : ¬ E u z := by
        rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact hyz.ne h.symm
        · exact hxz.ne h.symm
      have hside : d u z = c u z := if_neg hn
      exact hb z hxz hyz (hxy.symm.trans (hm.1.trans hside))
    · subst x
      subst y
      have hn : ¬ E u z := by
        rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact hxz.ne h.symm
        · exact hyz.ne h.symm
      have hside : d u z = c u z := if_neg hn
      exact hb z hyz hxz (hxy.symm.trans (hm.2.trans hside))
  refine ⟨d, ds, ?_⟩
  intro x y z hxy hxz hyz hm
  by_cases exy : E x y
  · exact avoid x y z exy hxz hyz hm
  by_cases exz : E x z
  · exact avoid x z y exz hxy hyz.symm
      ⟨hm.1.symm, hm.1.symm.trans (hm.2.trans (ds y z))⟩
  by_cases eyz : E y z
  · exact avoid y z x eyz hxy.symm hxz.symm
      ⟨hm.2.symm.trans (ds x y), hm.2.symm.trans (hm.1.trans (ds x z))⟩
  exact ht x y z ((hR x y).mpr ⟨hxy, exy⟩) ((hR x z).mpr ⟨hxz, exz⟩)
    ((hR y z).mpr ⟨hyz, eyz⟩) (by simpa [d, exy, exz, eyz] using hm)

private lemma arrowing_edge_outside_clique (h4 : H4) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4) (X : Finset (Fin n))
    (hX : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → G.Adj u v)
    (hc : ¬ ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))) :
    ∃ u v : Fin n, u ∉ X ∧ v ∉ X ∧ G.Adj u v ∧
      8 ≤ ((Finset.univ.filter (G.Adj u)).filter
        (fun x => ∃ z, G.Adj u z ∧ G.Adj x z)).card ∧
      8 ≤ ((Finset.univ.filter (G.Adj v)).filter
        (fun x => ∃ z, G.Adj v z ∧ G.Adj x z)).card ∧
      ∃ z t : Fin n, z ≠ t ∧ G.Adj u z ∧ G.Adj v z ∧ G.Adj u t ∧ G.Adj v t := by
  classical
  obtain ⟨Q, hQG, hQbad, hmin⟩ := minimal_uncolorable_subgraph G hc
  have hQ4 : Q.CliqueFree 4 := by
    intro K hK
    exact hG K ⟨fun _ hx _ hy hne => hQG _ _ (hK.1 hx hy hne), hK.2⟩
  have large (w a : Fin n) (hwa : Q.Adj w a) :
      8 ≤ (Finset.univ.filter (Q.Adj w)).card := by
    by_contra hlt
    let R : SimpleGraph (Fin n) := {
      Adj := fun x y => Q.Adj x y ∧ x ≠ w ∧ y ≠ w
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun _ h => Q.irrefl h.1⟩ }
    have hr := hmin R (fun _ _ h => h.1) ⟨w, a, hwa, fun h => h.2.1 rfl⟩
    exact hQbad (restore_vertex_coloring h4 Q R hQ4 w (by omega)
      (fun _ _ => Iff.rfl) hr)
  have common (a b : Fin n) (hab : Q.Adj a b) :
      ∃ z t : Fin n, z ≠ t ∧ Q.Adj a z ∧ Q.Adj b z ∧ Q.Adj a t ∧ Q.Adj b t := by
    by_contra hsmall
    let E (x y : Fin n) : Prop := (x = a ∧ y = b) ∨ (x = b ∧ y = a)
    have flip (x y : Fin n) (h : E x y) : E y x := by
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inr ⟨hy, hx⟩
      · exact Or.inl ⟨hy, hx⟩
    let R : SimpleGraph (Fin n) := {
      Adj := fun x y => Q.Adj x y ∧ ¬ E x y
      symm := ⟨fun _ _ h => ⟨h.1.symm, fun he => h.2 (flip _ _ he)⟩⟩
      loopless := ⟨fun _ h => Q.irrefl h.1⟩ }
    have hr := hmin R (fun _ _ h => h.1)
      ⟨a, b, hab, fun h => h.2 (Or.inl ⟨rfl, rfl⟩)⟩
    exact hQbad (restore_edge_coloring Q R a b (fun _ _ => Iff.rfl) hsmall hr)
  have hXcard : X.card ≤ 3 := by
    by_contra hlt
    obtain ⟨K, hKX, hK⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ X.card)
    exact hG K ⟨fun _ hx _ hy hne => hX _ (hKX hx) _ (hKX hy) hne, hK⟩
  have hedge : ∃ a b, Q.Adj a b := by
    by_contra hn
    exact hQbad ⟨fun _ _ => false, fun _ _ => rfl,
      fun x y _ hxy _ _ _ => hn ⟨x, y, hxy⟩⟩
  have outside (w a : Fin n) (hwa : Q.Adj w a) : ∃ x, x ∉ X ∧ Q.Adj w x := by
    by_contra hn
    have hs : Finset.univ.filter (Q.Adj w) ⊆ X := by
      intro x hx
      by_contra hnx
      exact hn ⟨x, hnx, (Finset.mem_filter.mp hx).2⟩
    have hl := large w a hwa
    have hu := Finset.card_le_card hs
    omega
  have liftDegree (w a : Fin n) (hwa : Q.Adj w a) :
      8 ≤ ((Finset.univ.filter (G.Adj w)).filter
        (fun x => ∃ z, G.Adj w z ∧ G.Adj x z)).card := by
    apply (large w a hwa).trans
    apply Finset.card_le_card
    intro x hx
    have hwx : Q.Adj w x := (Finset.mem_filter.mp hx).2
    obtain ⟨z, t, hzt, hwz, hxz, hwt, hxt⟩ := common w x hwx
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQG _ _ hwx⟩,
      z, hQG _ _ hwz, hQG _ _ hxz⟩
  obtain ⟨a, b, hab⟩ := hedge
  obtain ⟨u, huX, hau⟩ := outside a b hab
  obtain ⟨v, hvX, huv⟩ := outside u a hau.symm
  obtain ⟨z, t, hzt, huz, hvz, hut, hvt⟩ := common u v huv
  exact ⟨u, v, huX, hvX, hQG _ _ huv, liftDegree u v huv, liftDegree v u huv.symm,
    z, t, hzt, hQG _ _ huz, hQG _ _ hvz, hQG _ _ hut, hQG _ _ hvt⟩

private lemma case_H10 (h2 : H2) (h4 : H4) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (hn : 40 ≤ n) (hH : Erdos151.H n = 10)
    (hdeg : ∀ w, (Finset.univ.filter (G.Adj w)).card < 10) :
    G.cliqueTransversalNumber ≤ n - 10 := by
  classical
  let P : Fin n → Finset (Fin n) := fun w =>
    (Finset.univ.filter (G.Adj w)).filter (fun x => ∃ z, G.Adj w z ∧ G.Adj x z)
  have memP (w x : Fin n) : x ∈ P w ↔ G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z := by
    simp [P]
  have subN (w : Fin n) (I : Finset (Fin n)) (hI : I ⊆ P w) :
      I ⊆ Finset.univ.filter (G.Adj w) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((memP w x).mp (hI hx)).1⟩
  let X : Finset (Fin n) := Finset.univ.filter fun w =>
    ∃ I : Finset (Fin n), I ⊆ P w ∧ (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧
      ((Finset.univ.filter (G.Adj w)) \ I).card ≤ 5
  have memX (w : Fin n) : w ∈ X ↔
      ∃ I : Finset (Fin n), I ⊆ P w ∧ (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧
        ((Finset.univ.filter (G.Adj w)) \ I).card ≤ 5 := by
    simp [X]
  by_contra hbad
  have hX : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → G.Adj u v := by
    intro u hu v hv huv
    by_contra hnuv
    obtain ⟨Iu, huP, hiu, hu5⟩ := (memX u).mp hu
    obtain ⟨Iv, hvP, hiv, hv5⟩ := (memX v).mp hv
    apply hbad
    refine extend_pair_from_28 h2 h4 G hG hn u v huv Iu Iv
      (fun x hx => (memP u x).mp (huP hx)) (fun x hx => (memP v x).mp (hvP hx))
      hiu hiv (fun h => (hnuv h).elim) (fun h => (hnuv (G.symm.symm _ _ h)).elim) ?_
    omega
  have hc : ¬ ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z)) := by
    rintro ⟨c, hs, ht⟩
    obtain ⟨B, hB, hfree⟩ := free_of_coloring G c hs ht
    exact hbad (transversal_le_of_free G B (by simpa [hH] using hB) hfree)
  obtain ⟨u, v, huX, hvX, huv, hu8, hv8, z, t, hzt, huz, hvz, hut, hvt⟩ :=
    arrowing_edge_outside_clique h4 G hG X hX hc
  have alpha_bound (w : Fin n) (hwX : w ∉ X) (I : Finset (Fin n))
      (hIP : I ⊆ P w) (hII : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) : I.card ≤ 3 := by
    have hcost : 5 < ((Finset.univ.filter (G.Adj w)) \ I).card :=
      Nat.lt_of_not_ge (fun hh => hwX ((memX w).mpr ⟨I, hIP, hII, hh⟩))
    rw [Finset.card_sdiff_of_subset (subN w I hIP)] at hcost
    have hd := hdeg w
    omega
  have hvPu : v ∈ P u := (memP u v).mpr ⟨huv, z, huz, hvz⟩
  have huPv : u ∈ P v := (memP v u).mpr ⟨G.symm.symm _ _ huv, z, hvz, huz⟩
  obtain ⟨Iu, huP, hiu, hu3, hvIu⟩ :=
    (r34_and_triple_in_8 G hG u (P u) (subN u (P u) (fun _ h => h)) hu8
      (alpha_bound u huX)).2 v hvPu
  obtain ⟨Iv, hvP, hiv, hv3, huIv⟩ :=
    (r34_and_triple_in_8 G hG v (P v) (subN v (P v) (fun _ h => h)) hv8
      (alpha_bound v hvX)).2 u huPv
  let Du := (Finset.univ.filter (G.Adj u)) \ Iu
  let Dv := (Finset.univ.filter (G.Adj v)) \ Iv
  have hu6 : Du.card ≤ 6 := by
    dsimp [Du]
    rw [Finset.card_sdiff_of_subset (subN u Iu huP)]
    have hd := hdeg u
    omega
  have hv6 : Dv.card ≤ 6 := by
    dsimp [Dv]
    rw [Finset.card_sdiff_of_subset (subN v Iv hvP)]
    have hd := hdeg v
    omega
  have hcommon (a : Fin n) (hua : G.Adj u a) (hva : G.Adj v a) : a ∈ Du ∩ Dv := by
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hua⟩, fun ha => hiu v hvIu a ha hva⟩
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hva⟩, fun ha => hiv u huIv a ha hua⟩
  have hsub : ({z, t} : Finset (Fin n)) ⊆ Du ∩ Dv := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · rw [ha]; exact hcommon z huz hvz
    · rw [ha]; exact hcommon t hut hvt
  have hover : 2 ≤ (Du ∩ Dv).card := (card_two hzt).ge.trans (Finset.card_le_card hsub)
  have hne : u ≠ v := by
    intro he
    subst v
    simpa using huv
  apply hbad
  refine extend_pair_from_28 h2 h4 G hG hn u v hne Iu Iv
    (fun x hx => (memP u x).mp (huP hx)) (fun x hx => (memP v x).mp (hvP hx))
    hiu hiv (fun _ => hvIu) (fun _ => huIv) ?_
  change Du.card + Dv.card ≤ 10 + (Du ∩ Dv).card
  omega
-- === END HELPERS ===

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1.H1 := by
  classical
  intro h1 h2 h3 h4
  intro n G hG hdeg hS
  by_cases hbig : 11 ≤ Erdos151.H n
  · exact h1 n G hG hbig hdeg hS
  · by_cases h10 : Erdos151.H n = 10
    · rw [h10]
      exact case_H10 h2 h4 G hG (h3.2 n (by omega)) h10 (by simpa [h10] using hdeg)
    · by_cases h9 : Erdos151.H n = 9
      · rw [h9]
        exact case_H9 h2 h4 G hG (h3.1 n (by omega)) h9 (by simpa [h9] using hdeg)
      · obtain ⟨S, hSne, hSdeg⟩ := hS
        obtain ⟨v, hv⟩ := hSne
        have hsub : S.filter (G.Adj v) ⊆ Finset.univ.filter (G.Adj v) := by
          intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        have hc := Finset.card_le_card hsub
        have hl := hSdeg v hv
        have hu := hdeg v
        omega

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1
