import OMAReductions.R_Erdos559_erdos_559_variants_draganic_petrova_R1_H1_R1

/-!
Tree-decomposition to bounded-degree tree-partition conversion for subcubic graphs
(hypothesis H2 of the Draganic-Petrova reduction).
-/

namespace OMA.Erdos559H2Proof

open SimpleGraph Finset
open scoped Classical

section InducedFinset

variable {V : Type*}

def onSet (H : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj u v := u ∈ A ∧ v ∈ A ∧ H.Adj u v
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => H.loopless.irrefl _ h.2.2⟩

@[simp]
lemma onSet_adj (H : SimpleGraph V) (A : Finset V) (u v : V) :
    (onSet H A).Adj u v ↔ u ∈ A ∧ v ∈ A ∧ H.Adj u v :=
  Iff.rfl

lemma onSet_le (H : SimpleGraph V) (A : Finset V) : onSet H A ≤ H :=
  fun _ _ h => h.2.2

lemma onSet_mono {H : SimpleGraph V} {A B : Finset V} (h : A ⊆ B) :
    onSet H A ≤ onSet H B :=
  fun _ _ hadj => ⟨h hadj.1, h hadj.2.1, hadj.2.2⟩

lemma reachable_onSet_mono {H : SimpleGraph V} {A B : Finset V} (h : A ⊆ B)
    {u v : V} (hr : (onSet H A).Reachable u v) : (onSet H B).Reachable u v := by
  obtain ⟨p⟩ := hr
  exact ⟨p.mapLe (onSet_mono h)⟩

lemma walk_support_subset_of_onSet {H : SimpleGraph V} {A : Finset V}
    {u v : V} (hu : u ∈ A) (p : (onSet H A).Walk u v) :
    ∀ z ∈ (p.mapLe (onSet_le H A)).support, z ∈ A := by
  induction p with
  | nil =>
    intro z hz
    simp only [Walk.mapLe, Walk.map_nil, Walk.support_nil, List.mem_singleton] at hz
    rwa [hz]
  | cons hadj q ih =>
    intro z hz
    simp only [Walk.mapLe, Walk.map_cons, Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz'
    · exact hu
    · exact ih hadj.2.1 z hz'

lemma reachable_no_cross [DecidableEq V] {H : SimpleGraph V} {A B C : Finset V}
    (hsub : A ⊆ B ∪ C)
    (hno : ∀ x ∈ B, ∀ y ∈ C, ¬ H.Adj x y)
    {u v : V} (hu : u ∈ B)
    (hr : (onSet H A).Reachable u v) : v ∈ B := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hu
  | @cons x y z hadj q ih =>
    have hyA : y ∈ A := hadj.2.1
    rcases mem_union.mp (hsub hyA) with hyB | hyC
    · exact ih hyB
    · exact False.elim (hno x hu y hyC hadj.2.2)

noncomputable def compOf [DecidableEq V] (H : SimpleGraph V) (A : Finset V) (u : V) : Finset V :=
  A.filter fun v => (onSet H A).Reachable u v

lemma mem_compOf_iff [DecidableEq V] {H : SimpleGraph V} {A : Finset V} {u v : V} :
    v ∈ compOf H A u ↔ v ∈ A ∧ (onSet H A).Reachable u v :=
  mem_filter

lemma self_mem_compOf [DecidableEq V] {H : SimpleGraph V} {A : Finset V} {u : V} (hu : u ∈ A) :
    u ∈ compOf H A u :=
  mem_compOf_iff.mpr ⟨hu, Reachable.refl u⟩

lemma compOf_subset [DecidableEq V] {H : SimpleGraph V} {A : Finset V} {u : V} :
    compOf H A u ⊆ A :=
  filter_subset _ _

lemma compOf_closed [DecidableEq V] {H : SimpleGraph V} {A : Finset V} {u x y : V}
    (hx : x ∈ compOf H A u) (hy : y ∈ A) (hadj : H.Adj x y) :
    y ∈ compOf H A u := by
  obtain ⟨hxA, hux⟩ := mem_compOf_iff.mp hx
  have hadj' : (onSet H A).Adj x y := ⟨hxA, hy, hadj⟩
  exact mem_compOf_iff.mpr ⟨hy, hux.trans hadj'.reachable⟩

lemma walk_in_compOf [DecidableEq V] {H : SimpleGraph V} {A : Finset V} {u x y : V}
    (p : (onSet H A).Walk x y) (hx : x ∈ compOf H A u) :
    (onSet H (compOf H A u)).Reachable x y := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z y hadj q ih =>
    have hz : z ∈ compOf H A u := compOf_closed hx hadj.2.1 hadj.2.2
    have hadj' : (onSet H (compOf H A u)).Adj x z := ⟨hx, hz, hadj.2.2⟩
    exact hadj'.reachable.trans (ih hz)

lemma compOf_conn [DecidableEq V] {H : SimpleGraph V} {A : Finset V} {u x y : V}
    (hx : x ∈ compOf H A u) (hy : y ∈ compOf H A u) :
    (onSet H (compOf H A u)).Reachable x y := by
  have hxy : (onSet H A).Reachable x y :=
    (mem_compOf_iff.mp hx).2.symm.trans (mem_compOf_iff.mp hy).2
  obtain ⟨p⟩ := hxy
  exact walk_in_compOf p hx

lemma conn_subset_compOf [DecidableEq V] {H : SimpleGraph V} {A Z : Finset V} {u : V}
    (hZA : Z ⊆ A) (huZ : u ∈ Z)
    (hconn : ∀ x ∈ Z, ∀ y ∈ Z, (onSet H Z).Reachable x y) :
    Z ⊆ compOf H A u := by
  intro v hv
  exact mem_compOf_iff.mpr ⟨hZA hv, reachable_onSet_mono hZA (hconn u huZ v hv)⟩

lemma exists_step_from_compOf [DecidableEq V] {H : SimpleGraph V} {T₀ : Finset V} {c z : V}
    (hc : c ∈ T₀) (hz : z ∈ T₀ \ {c})
    (hTconn : ∀ x ∈ T₀, ∀ y ∈ T₀, (onSet H T₀).Reachable x y) :
    ∃ v ∈ compOf H (T₀ \ {c}) z, H.Adj c v := by
  have hzT : z ∈ T₀ := (mem_sdiff.mp hz).1
  obtain ⟨p⟩ := hTconn z hzT c hc
  have haux : ∀ {a b : V} (q : (onSet H T₀).Walk a b),
      a ∈ compOf H (T₀ \ {c}) z → b = c → ∃ v ∈ compOf H (T₀ \ {c}) z, H.Adj c v := by
    intro a b q haK hbc
    induction q with
    | nil =>
      rw [hbc] at haK
      exfalso
      have hadiff : c ∈ T₀ \ {c} := compOf_subset haK
      exact (mem_sdiff.mp hadiff).2 (mem_singleton_self c)
    | @cons a y b hadj q' ih =>
      by_cases hyc : y = c
      · subst hyc
        exact ⟨a, haK, hadj.2.2.symm⟩
      · have hy_diff : y ∈ T₀ \ {c} := mem_sdiff.mpr ⟨hadj.2.1, mem_singleton.not.mpr hyc⟩
        have hyK : y ∈ compOf H (T₀ \ {c}) z := compOf_closed haK hy_diff hadj.2.2
        exact ih hyK hbc
  exact haux p (self_mem_compOf hz) rfl

lemma exists_comps [DecidableEq V] (H : SimpleGraph V) (A : Finset V) :
    ∃ Ks : List (Finset V),
      (∀ K ∈ Ks, K.Nonempty ∧ K ⊆ A) ∧
      Ks.Pairwise Disjoint ∧
      (∀ x ∈ A, ∃ K ∈ Ks, x ∈ K) ∧
      (∀ K ∈ Ks, ∀ x ∈ K, ∀ y ∈ K, (onSet H K).Reachable x y) ∧
      (∀ K ∈ Ks, ∀ x ∈ K, ∀ y ∈ A, H.Adj x y → y ∈ K) := by
  by_cases hA : A.Nonempty
  · obtain ⟨u, hu⟩ := hA
    let K := compOf H A u
    have huK : u ∈ K := self_mem_compOf hu
    have hKsub : K ⊆ A := compOf_subset
    have hlt : (A \ K).card < A.card := by
      rw [card_sdiff_of_subset hKsub]
      have hpos : 0 < K.card := card_pos.mpr ⟨u, huK⟩
      have hle : K.card ≤ A.card := card_le_card hKsub
      omega
    obtain ⟨Ks, hne_sub, hdisj, hcov, hconn, hclosed⟩ := exists_comps H (A \ K)
    refine ⟨K :: Ks, ?_, ?_, ?_, ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL'
      · exact ⟨⟨u, huK⟩, hKsub⟩
      · exact ⟨(hne_sub L hL').1, (hne_sub L hL').2.trans sdiff_subset⟩
    · refine List.pairwise_cons.mpr ⟨fun L hL => ?_, hdisj⟩
      exact Finset.disjoint_left.mpr fun x hxK hxL =>
        (mem_sdiff.mp ((hne_sub L hL).2 hxL)).2 hxK
    · intro x hx
      by_cases hxK : x ∈ K
      · exact ⟨K, List.mem_cons_self, hxK⟩
      · obtain ⟨L, hL, hxL⟩ := hcov x (mem_sdiff.mpr ⟨hx, hxK⟩)
        exact ⟨L, List.mem_cons_of_mem _ hL, hxL⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL'
      · exact fun x hx y hy => compOf_conn hx hy
      · exact hconn L hL'
    · intro L hL x hxL y hyA hadj
      rcases List.mem_cons.mp hL with rfl | hL'
      · exact compOf_closed hxL hyA hadj
      · have hx_diff : x ∈ A \ K := (hne_sub L hL').2 hxL
        have hxA : x ∈ A := (mem_sdiff.mp hx_diff).1
        have hx_notK : x ∉ K := (mem_sdiff.mp hx_diff).2
        have hy_notK : y ∉ K := fun hyK => hx_notK (compOf_closed hyK hxA hadj.symm)
        exact hclosed L hL' x hxL y (mem_sdiff.mpr ⟨hyA, hy_notK⟩) hadj
  · rw [not_nonempty_iff_eq_empty] at hA
    subst hA
    exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
termination_by A.card

end InducedFinset

section ForestSplit

lemma unique_nbr_of_tree {t : ℕ} {S : SimpleGraph (Fin t)} (hS : S.IsTree)
    {K : Finset (Fin t)} {c u v : Fin t}
    (hc : c ∉ K) (hu : u ∈ K) (_hv : v ∈ K)
    (hconn : (onSet S K).Reachable u v)
    (hcu : S.Adj c u) (hcv : S.Adj c v) : u = v := by
  by_contra huv
  obtain ⟨p, hp⟩ := hconn.exists_isPath
  let p₁ : S.Walk u v := p.mapLe (onSet_le S K)
  have hp₁ : p₁.IsPath := hp.mapLe (onSet_le S K)
  have hc_not_p₁ : c ∉ p₁.support := fun hmem =>
    hc (walk_support_subset_of_onSet hu p c hmem)
  let p₂ : S.Walk u v := Walk.cons hcu.symm (Walk.cons hcv Walk.nil)
  have hp₂ : p₂.IsPath := by
    simp [p₂, Walk.isPath_def, hcu.ne.symm, huv, hcv.ne]
  have hc_in_p₂ : c ∈ p₂.support := by
    simp [p₂]
  obtain ⟨q, _, huniq⟩ := hS.existsUnique_path u v
  have heq : p₁ = p₂ := (huniq p₁ hp₁).trans (huniq p₂ hp₂).symm
  exact hc_not_p₁ (heq ▸ hc_in_p₂)

lemma forest_split {t : ℕ} (S : SimpleGraph (Fin t)) (hS : S.IsTree) (w : Fin t → ℕ)
    (B : ℕ) (hB : 0 < B) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (A : Finset (Fin t)), (∑ a ∈ A, w a) < k * B →
      ∃ C ⊆ A, C.card ≤ k - 1 ∧
        ∀ K : Finset (Fin t), K ⊆ A \ C →
          (∀ x ∈ K, ∀ y ∈ K, (onSet S K).Reachable x y) → (∑ a ∈ K, w a) < B := by
  intro k
  induction k with
  | zero =>
    intro hk
    omega
  | succ k ih =>
    intro _ A hsum
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨∅, empty_subset _, by simp, ?_⟩
      intro K hK _
      have hKA : K ⊆ A := by simpa using hK
      have hle : ∑ a ∈ K, w a ≤ ∑ a ∈ A, w a :=
        sum_le_sum_of_subset_of_nonneg hKA fun _ _ _ => Nat.zero_le _
      omega
    · have hk1 : 1 ≤ k := by omega
      by_cases hall : ∀ K : Finset (Fin t), K ⊆ A →
          (∀ x ∈ K, ∀ y ∈ K, (onSet S K).Reachable x y) → (∑ a ∈ K, w a) < B
      · refine ⟨∅, empty_subset _, by simp, ?_⟩
        intro K hK hconn
        exact hall K (hK.trans sdiff_subset) hconn
      · push Not at hall
        obtain ⟨K₀, hK₀A, hK₀conn, hK₀B⟩ := hall
        have hK₀ne : K₀.Nonempty := by
          by_contra hempty
          rw [not_nonempty_iff_eq_empty] at hempty
          subst hempty
          simp at hK₀B
          omega
        obtain ⟨x₀, hx₀K₀⟩ := hK₀ne
        have hx₀A : x₀ ∈ A := hK₀A hx₀K₀
        let T₀ := compOf S A x₀
        have hx₀T₀ : x₀ ∈ T₀ := self_mem_compOf hx₀A
        have hT₀A : T₀ ⊆ A := compOf_subset
        have hK₀T₀ : K₀ ⊆ T₀ := conn_subset_compOf hK₀A hx₀K₀ hK₀conn
        have hT₀B : B ≤ ∑ a ∈ T₀, w a :=
          hK₀B.trans (sum_le_sum_of_subset_of_nonneg hK₀T₀ fun _ _ _ => Nat.zero_le _)
        have hT₀conn : ∀ x ∈ T₀, ∀ y ∈ T₀, (onSet S T₀).Reachable x y :=
          fun x hx y hy => compOf_conn hx hy
        have hT₀closed : ∀ x ∈ T₀, ∀ y ∈ A, S.Adj x y → y ∈ T₀ :=
          fun x hx y hy hadj => compOf_closed hx hy hadj
        let heavyPred : Fin t × Finset (Fin t) → Prop := fun p =>
          p.1 ∈ T₀ ∧ p.2 ⊆ T₀ \ {p.1} ∧ (∃ u ∈ p.2, S.Adj p.1 u) ∧
            (∀ x ∈ p.2, ∀ y ∈ p.2, (onSet S p.2).Reachable x y) ∧
            (∀ x ∈ p.2, ∀ y ∈ T₀ \ {p.1}, S.Adj x y → y ∈ p.2) ∧
            B ≤ ∑ a ∈ p.2, w a
        let Hfin := (T₀ ×ˢ T₀.powerset).filter heavyPred
        by_cases hHne : Hfin.Nonempty
        · obtain ⟨p, hp_mem, hp_min⟩ := exists_min_image Hfin (fun q => q.2.card) hHne
          rcases p with ⟨c, K⟩
          obtain ⟨_, ⟨hcT₀, hKT₀c, ⟨u, huK, hcu⟩, hKconn, hKclosed, hKB⟩⟩ := mem_filter.mp hp_mem
          have hKB' : B ≤ ∑ a ∈ K, w a := hKB
          have hKT₀ : K ⊆ T₀ := hKT₀c.trans sdiff_subset
          have hKA : K ⊆ A := hKT₀.trans hT₀A
          have hc_notK : c ∉ K := fun hcK =>
            (mem_sdiff.mp (hKT₀c hcK)).2 (mem_singleton_self c)
          have hno_cross : ∀ x ∈ K \ {u}, ∀ y ∈ A \ K, ¬ S.Adj x y := by
            intro x hxKu y hyAK hadj
            obtain ⟨hxK, hxu⟩ := mem_sdiff.mp hxKu
            have hne_xu : x ≠ u := mem_singleton.not.mp hxu
            obtain ⟨hyA, hy_notK⟩ := mem_sdiff.mp hyAK
            have hyT₀ : y ∈ T₀ := hT₀closed x (hKT₀ hxK) y hyA hadj
            by_cases hyc : y = c
            · subst hyc
              have heq : x = u :=
                unique_nbr_of_tree hS hc_notK hxK huK (hKconn x hxK u huK) hadj.symm hcu
              exact hne_xu heq
            · have hyT₀c : y ∈ T₀ \ {c} := mem_sdiff.mpr ⟨hyT₀, mem_singleton.not.mpr hyc⟩
              exact hy_notK (hKclosed x hxK y hyT₀c hadj)
          have hsum_rest : (∑ a ∈ A \ K, w a) < k * B := by
            have hsplit : (∑ a ∈ A \ K, w a) + (∑ a ∈ K, w a) = ∑ a ∈ A, w a :=
              sum_sdiff hKA
            have hk_eq : (k + 1) * B = k * B + B := by ring
            omega
          obtain ⟨C', hC'sub, hC'card, hC'ok⟩ := ih hk1 (A \ K) hsum_rest
          refine ⟨insert u C', ?_, ?_, ?_⟩
          · intro x hx
            rcases mem_insert.mp hx with rfl | hxC'
            · exact hKA huK
            · exact (mem_sdiff.mp (hC'sub hxC')).1
          · calc (insert u C').card ≤ C'.card + 1 := card_insert_le u C'
              _ ≤ (k - 1) + 1 := Nat.add_le_add_right hC'card 1
              _ = (k + 1) - 1 := by omega
          · intro L hL hLconn
            by_cases hLne : L.Nonempty
            · obtain ⟨z, hzL⟩ := hLne
              have hL_split : L ⊆ (K \ {u}) ∪ ((A \ K) \ C') := by
                intro x hxL
                obtain ⟨hxA, hx_notC⟩ := mem_sdiff.mp (hL hxL)
                rw [mem_insert, not_or] at hx_notC
                by_cases hxK : x ∈ K
                · exact mem_union_left _ (mem_sdiff.mpr ⟨hxK, mem_singleton.not.mpr hx_notC.1⟩)
                · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hxA, hxK⟩, hx_notC.2⟩)
              rcases mem_union.mp (hL_split hzL) with hzKu | hzRest
              · have hL_in_Ku : L ⊆ K \ {u} := by
                  intro x hxL
                  refine reachable_no_cross hL_split ?_ hzKu (hLconn z hzL x hxL)
                  intro a ha b hb
                  exact hno_cross a ha b (sdiff_subset hb)
                let K' := compOf S (K \ {u}) z
                have hLK' : L ⊆ K' := conn_subset_compOf hL_in_Ku hzL hLconn
                have hK'Ku : K' ⊆ K \ {u} := compOf_subset
                have hK'T₀u : K' ⊆ T₀ \ {u} := by
                  intro x hxK'
                  obtain ⟨hxK, hxu⟩ := mem_sdiff.mp (hK'Ku hxK')
                  exact mem_sdiff.mpr ⟨hKT₀ hxK, hxu⟩
                have hK'conn : ∀ x ∈ K', ∀ y ∈ K', (onSet S K').Reachable x y :=
                  fun x hx y hy => compOf_conn hx hy
                have hK'closed : ∀ x ∈ K', ∀ y ∈ T₀ \ {u}, S.Adj x y → y ∈ K' := by
                  intro x hxK' y hyT₀u hadj
                  have hxKu : x ∈ K \ {u} := hK'Ku hxK'
                  obtain ⟨hyT₀, hyu⟩ := mem_sdiff.mp hyT₀u
                  by_cases hyK : y ∈ K
                  · exact compOf_closed hxK' (mem_sdiff.mpr ⟨hyK, hyu⟩) hadj
                  · exfalso
                    exact hno_cross x hxKu y (mem_sdiff.mpr ⟨hT₀A hyT₀, hyK⟩) hadj
                obtain ⟨v, hvK', huv⟩ := exists_step_from_compOf huK hzKu hKconn
                have hcard_lt : K'.card < K.card := by
                  have hsub_K : K \ {u} ⊂ K :=
                    sdiff_ssubset (singleton_subset_iff.mpr huK) (singleton_nonempty u)
                  exact (card_le_card hK'Ku).trans_lt (card_lt_card hsub_K)
                have hnot_heavy : ¬ (B ≤ ∑ a ∈ K', w a) := by
                  intro hB_le
                  have hmem_H : (u, K') ∈ Hfin := by
                    refine mem_filter.mpr
                      ⟨mem_product.mpr ⟨hKT₀ huK, mem_powerset.mpr (hK'T₀u.trans sdiff_subset)⟩, ?_⟩
                    exact ⟨hKT₀ huK, hK'T₀u, ⟨v, hvK', huv⟩, hK'conn, hK'closed, hB_le⟩
                  exact not_lt_of_ge (hp_min (u, K') hmem_H) hcard_lt
                have hle_K' : ∑ a ∈ L, w a ≤ ∑ a ∈ K', w a :=
                  sum_le_sum_of_subset_of_nonneg hLK' fun _ _ _ => Nat.zero_le _
                omega
              · have hL_in_Rest : L ⊆ (A \ K) \ C' := by
                  intro x hxL
                  have hswap : L ⊆ ((A \ K) \ C') ∪ (K \ {u}) := fun y hy =>
                    mem_union.mpr (mem_union.mp (hL_split hy)).symm
                  refine reachable_no_cross hswap ?_ hzRest (hLconn z hzL x hxL)
                  intro a ha b hb hadj
                  exact hno_cross b hb a (sdiff_subset ha) hadj.symm
                exact hC'ok L hL_in_Rest hLconn
            · rw [not_nonempty_iff_eq_empty] at hLne
              subst hLne
              simpa using hB
        · rw [not_nonempty_iff_eq_empty] at hHne
          have hsum_rest : (∑ a ∈ A \ T₀, w a) < k * B := by
            have hsplit : (∑ a ∈ A \ T₀, w a) + (∑ a ∈ T₀, w a) = ∑ a ∈ A, w a :=
              sum_sdiff hT₀A
            have hk_eq : (k + 1) * B = k * B + B := by ring
            omega
          obtain ⟨C', hC'sub, hC'card, hC'ok⟩ := ih hk1 (A \ T₀) hsum_rest
          refine ⟨insert x₀ C', ?_, ?_, ?_⟩
          · intro x hx
            rcases mem_insert.mp hx with rfl | hxC'
            · exact hx₀A
            · exact (mem_sdiff.mp (hC'sub hxC')).1
          · calc (insert x₀ C').card ≤ C'.card + 1 := card_insert_le x₀ C'
              _ ≤ (k - 1) + 1 := Nat.add_le_add_right hC'card 1
              _ = (k + 1) - 1 := by omega
          · intro L hL hLconn
            by_cases hLne : L.Nonempty
            · obtain ⟨z, hzL⟩ := hLne
              have hL_split : L ⊆ (T₀ \ {x₀}) ∪ ((A \ T₀) \ C') := by
                intro x hxL
                obtain ⟨hxA, hx_notC⟩ := mem_sdiff.mp (hL hxL)
                rw [mem_insert, not_or] at hx_notC
                by_cases hxT₀ : x ∈ T₀
                · exact mem_union_left _ (mem_sdiff.mpr ⟨hxT₀, mem_singleton.not.mpr hx_notC.1⟩)
                · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hxA, hxT₀⟩, hx_notC.2⟩)
              have hno_T₀ : ∀ a ∈ T₀ \ {x₀}, ∀ b ∈ (A \ T₀) \ C', ¬ S.Adj a b := by
                intro a ha b hb hadj
                have haT₀ : a ∈ T₀ := (mem_sdiff.mp ha).1
                obtain ⟨hbA, hb_notT₀⟩ := mem_sdiff.mp (sdiff_subset hb)
                exact hb_notT₀ (hT₀closed a haT₀ b hbA hadj)
              rcases mem_union.mp (hL_split hzL) with hzT₀x | hzRest
              · have hL_in_T₀x : L ⊆ T₀ \ {x₀} := fun x hxL =>
                  reachable_no_cross hL_split hno_T₀ hzT₀x (hLconn z hzL x hxL)
                let K' := compOf S (T₀ \ {x₀}) z
                have hLK' : L ⊆ K' := conn_subset_compOf hL_in_T₀x hzL hLconn
                have hK'sub : K' ⊆ T₀ \ {x₀} := compOf_subset
                obtain ⟨v, hvK', hx₀v⟩ := exists_step_from_compOf hx₀T₀ hzT₀x hT₀conn
                have hnot_heavy : ¬ (B ≤ ∑ a ∈ K', w a) := by
                  intro hB_le
                  have hmem_H : (x₀, K') ∈ Hfin := by
                    refine mem_filter.mpr
                      ⟨mem_product.mpr ⟨hx₀T₀, mem_powerset.mpr (hK'sub.trans sdiff_subset)⟩, ?_⟩
                    exact ⟨hx₀T₀, hK'sub, ⟨v, hvK', hx₀v⟩,
                      fun x hx y hy => compOf_conn hx hy,
                      fun x hx y hy hadj => compOf_closed hx hy hadj, hB_le⟩
                  rw [hHne] at hmem_H
                  exact notMem_empty _ hmem_H
                have hle_K' : ∑ a ∈ L, w a ≤ ∑ a ∈ K', w a :=
                  sum_le_sum_of_subset_of_nonneg hLK' fun _ _ _ => Nat.zero_le _
                omega
              · have hL_in_Rest : L ⊆ (A \ T₀) \ C' := by
                  intro x hxL
                  have hswap : L ⊆ ((A \ T₀) \ C') ∪ (T₀ \ {x₀}) := fun y hy =>
                    mem_union.mpr (mem_union.mp (hL_split hy)).symm
                  refine reachable_no_cross hswap ?_ hzRest (hLconn z hzL x hxL)
                  intro a ha b hb hadj
                  exact hno_T₀ b hb a ha hadj.symm
                exact hC'ok L hL_in_Rest hLconn
            · rw [not_nonempty_iff_eq_empty] at hLne
              subst hLne
              simpa using hB

end ForestSplit

section TreeDecompProps

lemma induce_conn_to_onSet {t : ℕ} {S : SimpleGraph (Fin t)} {P : Fin t → Prop} [DecidablePred P]
    (hconn : (S.induce {a : Fin t | P a}).Connected) :
    (univ.filter P).Nonempty ∧
      ∀ a ∈ univ.filter P, ∀ b ∈ univ.filter P, (onSet S (univ.filter P)).Reachable a b := by
  let A := univ.filter P
  obtain ⟨⟨a₀, ha₀⟩⟩ := hconn.nonempty
  refine ⟨⟨a₀, mem_filter.mpr ⟨mem_univ _, ha₀⟩⟩, ?_⟩
  intro a ha b hb
  have ha' : P a := (mem_filter.mp ha).2
  have hb' : P b := (mem_filter.mp hb).2
  obtain ⟨w⟩ := hconn.preconnected ⟨a, ha'⟩ ⟨b, hb'⟩
  have hwalk : ∀ {x y : {z : Fin t | P z}} (q : (S.induce {z : Fin t | P z}).Walk x y),
      (onSet S A).Reachable x.1 y.1 := by
    intro x y q
    induction q with
    | nil => exact Reachable.refl _
    | @cons x z y hadj q' ih =>
      have hxA : x.1 ∈ A := mem_filter.mpr ⟨mem_univ _, x.2⟩
      have hzA : z.1 ∈ A := mem_filter.mpr ⟨mem_univ _, z.2⟩
      have hadj' : (onSet S A).Adj x.1 z.1 := ⟨hxA, hzA, hadj⟩
      exact hadj'.reachable.trans ih
  exact hwalk w

lemma boundary_bound {n t ℓ : ℕ} {G : SimpleGraph (Fin n)} {J : Finset (Fin n)}
    {S : SimpleGraph (Fin t)} {B : Fin t → Finset (Fin n)}
    (hℓ : 5 ≤ ℓ) (hdeg : G.maxDegree ≤ 3)
    (hBcard : ∀ a, (B a).card ≤ 2 * ℓ + 1 ∧ B a ⊆ J)
    (hBedge : ∀ x ∈ J, ∀ y ∈ J, G.Adj x y → ∃ a, x ∈ B a ∧ y ∈ B a)
    (hBconn : ∀ x ∈ J, (univ.filter fun a => x ∈ B a).Nonempty ∧
      ∀ a ∈ univ.filter (fun a => x ∈ B a), ∀ b ∈ univ.filter (fun a => x ∈ B a),
        (onSet S (univ.filter fun a => x ∈ B a)).Reachable a b)
    {U R : Finset (Fin n)} (hUJ : U ⊆ J) (hRU : R ⊆ U) (hRcard : R.card ≤ 80 * ℓ)
    (φ : Fin n → Fin t) (hφ : ∀ x ∈ R, x ∈ B (φ x))
    {C : Finset (Fin t)} (hCcard : C.card ≤ 7)
    (hsplit : ∀ K : Finset (Fin t), K ⊆ univ \ C →
      (∀ x ∈ K, ∀ y ∈ K, (onSet S K).Reachable x y) →
      (∑ a ∈ K, (R.filter fun x => φ x = a).card) < R.card / 8 + 1)
    {Vcomp : Finset (Fin n)} (hVne : Vcomp.Nonempty)
    (hVU : Vcomp ⊆ U \ (R ∪ ((C.biUnion B) ∩ U)))
    (hVconn : ∀ x ∈ Vcomp, ∀ y ∈ Vcomp, (onSet G Vcomp).Reachable x y) :
    (Vcomp.filter fun y => ∃ x ∈ R ∪ ((C.biUnion B) ∩ U), G.Adj x y).card ≤ 80 * ℓ := by
  let P₀ := R ∪ ((C.biUnion B) ∩ U)
  let Ax : Fin n → Finset (Fin t) := fun x => univ.filter fun a => x ∈ B a
  have hV_disj_CB : ∀ y ∈ Vcomp, Ax y ⊆ univ \ C := by
    intro y hy a ha
    have hy_diff := mem_sdiff.mp (hVU hy)
    have hyU : y ∈ U := hy_diff.1
    have hy_notP₀ : y ∉ P₀ := hy_diff.2
    refine mem_sdiff.mpr ⟨mem_univ a, fun haC => hy_notP₀ ?_⟩
    refine mem_union_right _ (mem_inter.mpr ⟨mem_biUnion.mpr ⟨a, haC, (mem_filter.mp ha).2⟩, hyU⟩)
  obtain ⟨y₀, hy₀V⟩ := hVne
  have hy₀J : y₀ ∈ J := hUJ ((mem_sdiff.mp (hVU hy₀V)).1)
  obtain ⟨a₀, ha₀⟩ := (hBconn y₀ hy₀J).1
  have ha₀_diff : a₀ ∈ univ \ C := hV_disj_CB y₀ hy₀V ha₀
  let Ks := compOf S (univ \ C) a₀
  have ha₀Ks : a₀ ∈ Ks := self_mem_compOf ha₀_diff
  have hKs_sub : Ks ⊆ univ \ C := compOf_subset
  have hKs_conn : ∀ x ∈ Ks, ∀ y ∈ Ks, (onSet S Ks).Reachable x y :=
    fun x hx y hy => compOf_conn hx hy
  have hAx_in_Ks_of_inter : ∀ z ∈ J, Ax z ⊆ univ \ C → (∃ a ∈ Ax z, a ∈ Ks) → Ax z ⊆ Ks := by
    intro z hzJ hz_sub ⟨a, haAx, haKs⟩ b hbAx
    have hab : (onSet S (univ \ C)).Reachable a b :=
      reachable_onSet_mono hz_sub ((hBconn z hzJ).2 a haAx b hbAx)
    exact mem_compOf_iff.mpr ⟨hz_sub hbAx, (mem_compOf_iff.mp haKs).2.trans hab⟩
  have hV_in_Ks : ∀ y ∈ Vcomp, Ax y ⊆ Ks := by
    intro y hyV
    obtain ⟨p⟩ := hVconn y₀ hy₀V y hyV
    have hwalk : ∀ {u v : Fin n} (q : (onSet G Vcomp).Walk u v),
        u ∈ Vcomp → Ax u ⊆ Ks → Ax v ⊆ Ks := by
      intro u v q huV huKs
      induction q with
      | nil => exact huKs
      | @cons u z v hadj q' ih =>
        have hzV : z ∈ Vcomp := hadj.2.1
        have huJ : u ∈ J := hUJ ((mem_sdiff.mp (hVU huV)).1)
        have hzJ : z ∈ J := hUJ ((mem_sdiff.mp (hVU hzV)).1)
        obtain ⟨a, ha_u, ha_z⟩ := hBedge u huJ z hzJ hadj.2.2
        have haAxu : a ∈ Ax u := mem_filter.mpr ⟨mem_univ _, ha_u⟩
        have haAxz : a ∈ Ax z := mem_filter.mpr ⟨mem_univ _, ha_z⟩
        have hzKs : Ax z ⊆ Ks :=
          hAx_in_Ks_of_inter z hzJ (hV_disj_CB z hzV) ⟨a, haAxz, huKs haAxu⟩
        exact ih hzV hzKs
    exact hwalk p hy₀V (hAx_in_Ks_of_inter y₀ hy₀J (hV_disj_CB y₀ hy₀V) ⟨a₀, ha₀, ha₀Ks⟩)
  let Rhit := R.filter fun x => φ x ∈ Ks
  let Active := ((C.biUnion B) ∩ U) ∪ Rhit
  have hactive_cover : ∀ y ∈ Vcomp, (∃ x ∈ P₀, G.Adj x y) → ∃ x ∈ Active, G.Adj x y := by
    intro y hyV ⟨x, hxP₀, hadj⟩
    rcases mem_union.mp hxP₀ with hxR | hxCB
    · by_cases hxCB' : x ∈ (C.biUnion B) ∩ U
      · exact ⟨x, mem_union_left _ hxCB', hadj⟩
      · have hxU : x ∈ U := hRU hxR
        have hx_notCB : x ∉ C.biUnion B := fun h => hxCB' (mem_inter.mpr ⟨h, hxU⟩)
        have hxAx_sub : Ax x ⊆ univ \ C := by
          intro a ha
          exact mem_sdiff.mpr ⟨mem_univ a, fun haC =>
            hx_notCB (mem_biUnion.mpr ⟨a, haC, (mem_filter.mp ha).2⟩)⟩
        have hxJ : x ∈ J := hUJ hxU
        have hyJ : y ∈ J := hUJ ((mem_sdiff.mp (hVU hyV)).1)
        obtain ⟨a, ha_x, ha_y⟩ := hBedge x hxJ y hyJ hadj
        have haKs : a ∈ Ks := hV_in_Ks y hyV (mem_filter.mpr ⟨mem_univ _, ha_y⟩)
        have hAx_x_Ks : Ax x ⊆ Ks :=
          hAx_in_Ks_of_inter x hxJ hxAx_sub ⟨a, mem_filter.mpr ⟨mem_univ _, ha_x⟩, haKs⟩
        have hφKs : φ x ∈ Ks := hAx_x_Ks (mem_filter.mpr ⟨mem_univ _, hφ x hxR⟩)
        exact ⟨x, mem_union_right _ (mem_filter.mpr ⟨hxR, hφKs⟩), hadj⟩
    · exact ⟨x, mem_union_left _ hxCB, hadj⟩
  have hRhit_eq : Rhit.card = ∑ a ∈ Ks, (R.filter fun x => φ x = a).card := by
    rw [← card_biUnion]
    · congr 1
      ext x
      simp only [Rhit, mem_filter, mem_biUnion]
      exact ⟨fun ⟨hxR, hφKs⟩ => ⟨φ x, hφKs, hxR, rfl⟩,
        fun ⟨a, haKs, hxR, hφa⟩ => ⟨hxR, hφa ▸ haKs⟩⟩
    · intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun x hxa hxb =>
        hab ((mem_filter.mp hxa).2.symm.trans (mem_filter.mp hxb).2)
  have hRhit_le : Rhit.card ≤ R.card / 8 := by
    have hlt := hsplit Ks hKs_sub hKs_conn
    omega
  have hCB_le : ((C.biUnion B) ∩ U).card ≤ 7 * (2 * ℓ + 1) := by
    calc ((C.biUnion B) ∩ U).card ≤ (C.biUnion B).card := card_le_card inter_subset_left
      _ ≤ ∑ c ∈ C, (B c).card := card_biUnion_le
      _ ≤ ∑ _c ∈ C, (2 * ℓ + 1) := sum_le_sum fun c _ => (hBcard c).1
      _ = C.card * (2 * ℓ + 1) := by simp
      _ ≤ 7 * (2 * ℓ + 1) := Nat.mul_le_mul_right _ hCcard
  have hActive_le : Active.card ≤ 24 * ℓ + 7 := by
    dsimp only [Active]
    have hu := card_union_le ((C.biUnion B) ∩ U) Rhit
    omega
  have hdeg3 : ∀ x : Fin n, (univ.filter (G.Adj x)).card ≤ 3 := by
    intro x
    have h1 : (univ.filter (G.Adj x)).card = G.degree x := by
      rw [← G.card_neighborFinset_eq_degree x]
      congr 1
      ext z
      simp [mem_neighborFinset]
    exact h1.le.trans ((G.degree_le_maxDegree x).trans hdeg)
  have hsub_biUnion : (Vcomp.filter fun y => ∃ x ∈ P₀, G.Adj x y) ⊆
      Active.biUnion (fun x => univ.filter (G.Adj x)) := by
    intro y hy
    obtain ⟨hyV, hex⟩ := mem_filter.mp hy
    obtain ⟨x, hxAct, hadj⟩ := hactive_cover y hyV hex
    exact mem_biUnion.mpr ⟨x, hxAct, mem_filter.mpr ⟨mem_univ _, hadj⟩⟩
  calc (Vcomp.filter fun y => ∃ x ∈ P₀, G.Adj x y).card
      ≤ (Active.biUnion (fun x => univ.filter (G.Adj x))).card := card_le_card hsub_biUnion
    _ ≤ ∑ x ∈ Active, (univ.filter (G.Adj x)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ Active, 3 := sum_le_sum fun x _ => hdeg3 x
    _ = Active.card * 3 := by simp
    _ ≤ 80 * ℓ := by omega

end TreeDecompProps

section TreeGlue

structure PartData (n : ℕ) where
  M : Finset (Fin n)
  r : Fin n
  E : SimpleGraph (Fin n)
  owner : Fin n → Fin n
  r_mem : r ∈ M
  E_supp : ∀ a b, E.Adj a b → a ∈ M ∧ b ∈ M
  E_conn : ∀ a ∈ M, ∀ b ∈ M, (onSet E M).Reachable a b
  E_card : E.edgeFinset.card + 1 = M.card

def ValidOn {n : ℕ} (G : SimpleGraph (Fin n)) (D : PartData n) (U : Finset (Fin n)) : Prop :=
  D.M ⊆ U ∧
  (∀ x ∈ U, D.owner x ∈ D.M) ∧
  (∀ x ∈ U, ∀ y ∈ U, G.Adj x y → D.owner x = D.owner y ∨ D.E.Adj (D.owner x) (D.owner y))

noncomputable def singleBagData {n : ℕ} (r₀ : Fin n) : PartData n where
  M := {r₀}
  r := r₀
  E := ⊥
  owner := fun _ => r₀
  r_mem := mem_singleton_self r₀
  E_supp := fun _ _ h => False.elim h
  E_conn := by
    intro a ha b hb
    rw [mem_singleton.mp ha, mem_singleton.mp hb]
  E_card := by simp

def addBridge {n : ℕ} (E₁ E₂ : SimpleGraph (Fin n)) (r₁ r₂ : Fin n) (hne : r₁ ≠ r₂) :
    SimpleGraph (Fin n) where
  Adj a b := E₁.Adj a b ∨ E₂.Adj a b ∨ (a = r₁ ∧ b = r₂) ∨ (a = r₂ ∧ b = r₁)
  symm := ⟨fun _ _ h => by
    rcases h with h1 | h2 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inl h2.symm)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  loopless := ⟨fun a h => by
    rcases h with h1 | h2 | ⟨rfl, h12⟩ | ⟨rfl, h21⟩
    · exact E₁.loopless.irrefl a h1
    · exact E₂.loopless.irrefl a h2
    · exact hne h12
    · exact hne h21.symm⟩

@[simp]
lemma addBridge_adj {n : ℕ} (E₁ E₂ : SimpleGraph (Fin n)) (r₁ r₂ : Fin n) (hne : r₁ ≠ r₂)
    (a b : Fin n) :
    (addBridge E₁ E₂ r₁ r₂ hne).Adj a b ↔
      E₁.Adj a b ∨ E₂.Adj a b ∨ (a = r₁ ∧ b = r₂) ∨ (a = r₂ ∧ b = r₁) :=
  Iff.rfl

lemma addBridge_edgeFinset {n : ℕ} {E₁ E₂ : SimpleGraph (Fin n)} {M₁ M₂ : Finset (Fin n)}
    {r₁ r₂ : Fin n} (hdisj : Disjoint M₁ M₂)
    (hE₁ : ∀ a b, E₁.Adj a b → a ∈ M₁ ∧ b ∈ M₁)
    (hE₂ : ∀ a b, E₂.Adj a b → a ∈ M₂ ∧ b ∈ M₂)
    (hr₁ : r₁ ∈ M₁) (hr₂ : r₂ ∈ M₂) (hne : r₁ ≠ r₂) :
    (addBridge E₁ E₂ r₁ r₂ hne).edgeFinset.card =
      E₁.edgeFinset.card + E₂.edgeFinset.card + 1 := by
  let E := addBridge E₁ E₂ r₁ r₂ hne
  have heq : E.edgeFinset = insert s(r₁, r₂) (E₁.edgeFinset ∪ E₂.edgeFinset) := by
    ext e
    refine Sym2.ind (fun a b => ?_) e
    simp only [mem_edgeFinset, mem_edgeSet, mem_insert, mem_union, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Prod.swap_prod_mk, E, addBridge_adj]
    tauto
  have hnot_mem : s(r₁, r₂) ∉ E₁.edgeFinset ∪ E₂.edgeFinset := by
    intro h
    rcases mem_union.mp h with h1 | h2
    · rw [mem_edgeFinset] at h1
      exact Finset.disjoint_left.mp hdisj (hE₁ r₁ r₂ h1).2 hr₂
    · rw [mem_edgeFinset] at h2
      exact Finset.disjoint_left.mp hdisj hr₁ (hE₂ r₁ r₂ h2).1
  have hdisj_edges : Disjoint E₁.edgeFinset E₂.edgeFinset := by
    refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
    revert he1 he2
    refine Sym2.ind (fun a b he1 he2 => ?_) e
    rw [mem_edgeFinset] at he1 he2
    exact Finset.disjoint_left.mp hdisj (hE₁ a b he1).1 (hE₂ a b he2).1
  rw [heq, card_insert_of_notMem hnot_mem, card_union_of_disjoint hdisj_edges]

lemma addBridge_nbrs {n : ℕ} {E₁ E₂ : SimpleGraph (Fin n)} {M₁ M₂ : Finset (Fin n)}
    {r₁ r₂ : Fin n} (hdisj : Disjoint M₁ M₂)
    (hE₁ : ∀ a b, E₁.Adj a b → a ∈ M₁ ∧ b ∈ M₁)
    (hE₂ : ∀ a b, E₂.Adj a b → a ∈ M₂ ∧ b ∈ M₂)
    (hr₁ : r₁ ∈ M₁) (hr₂ : r₂ ∈ M₂) (hne : r₁ ≠ r₂) :
    let E := addBridge E₁ E₂ r₁ r₂ hne
    (univ.filter (E.Adj r₁)).card = (univ.filter (E₁.Adj r₁)).card + 1 ∧
    (univ.filter (E.Adj r₂)).card = (univ.filter (E₂.Adj r₂)).card + 1 ∧
    (∀ v ∈ M₁, v ≠ r₁ → (univ.filter (E.Adj v)).card = (univ.filter (E₁.Adj v)).card) ∧
    (∀ v ∈ M₂, v ≠ r₂ → (univ.filter (E.Adj v)).card = (univ.filter (E₂.Adj v)).card) := by
  intro E
  have hr₁_not2 : ∀ b, ¬ E₂.Adj r₁ b := fun b hb =>
    Finset.disjoint_left.mp hdisj hr₁ (hE₂ r₁ b hb).1
  have hr₂_not1 : ∀ b, ¬ E₁.Adj r₂ b := fun b hb =>
    Finset.disjoint_left.mp hdisj (hE₁ r₂ b hb).1 hr₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hset : univ.filter (E.Adj r₁) = insert r₂ (univ.filter (E₁.Adj r₁)) := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_insert, E, addBridge_adj]
      constructor
      · rintro (h1 | h2 | ⟨_, rfl⟩ | ⟨hEq, _⟩)
        · exact Or.inr h1
        · exact False.elim (hr₁_not2 b h2)
        · exact Or.inl rfl
        · exact False.elim (hne hEq)
      · rintro (rfl | h1)
        · simp
        · exact Or.inl h1
    have hnot : r₂ ∉ univ.filter (E₁.Adj r₁) := fun h =>
      Finset.disjoint_left.mp hdisj (hE₁ r₁ r₂ (mem_filter.mp h).2).2 hr₂
    rw [hset, card_insert_of_notMem hnot]
  · have hset : univ.filter (E.Adj r₂) = insert r₁ (univ.filter (E₂.Adj r₂)) := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_insert, E, addBridge_adj]
      constructor
      · rintro (h1 | h2 | ⟨hEq, _⟩ | ⟨_, rfl⟩)
        · exact False.elim (hr₂_not1 b h1)
        · exact Or.inr h2
        · exact False.elim (hne hEq.symm)
        · exact Or.inl rfl
      · rintro (rfl | h2)
        · simp
        · exact Or.inr (Or.inl h2)
    have hnot : r₁ ∉ univ.filter (E₂.Adj r₂) := fun h =>
      Finset.disjoint_left.mp hdisj hr₁ (hE₂ r₂ r₁ (mem_filter.mp h).2).2
    rw [hset, card_insert_of_notMem hnot]
  · intro v hvM₁ hvr₁
    have hv_not2 : ∀ b, ¬ E₂.Adj v b := fun b hb =>
      Finset.disjoint_left.mp hdisj hvM₁ (hE₂ v b hb).1
    have hvr₂ : v ≠ r₂ := fun h => Finset.disjoint_left.mp hdisj hvM₁ (h ▸ hr₂)
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, E, addBridge_adj]
    exact ⟨fun h => by
      rcases h with h1 | h2 | ⟨hEq, _⟩ | ⟨hEq, _⟩
      · exact h1
      · exact False.elim (hv_not2 b h2)
      · exact False.elim (hvr₁ hEq)
      · exact False.elim (hvr₂ hEq),
      fun h1 => Or.inl h1⟩
  · intro v hvM₂ hvr₂
    have hv_not1 : ∀ b, ¬ E₁.Adj v b := fun b hb =>
      Finset.disjoint_left.mp hdisj (hE₁ v b hb).1 hvM₂
    have hvr₁ : v ≠ r₁ := fun h => Finset.disjoint_left.mp hdisj (h ▸ hr₁) hvM₂
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, E, addBridge_adj]
    exact ⟨fun h => by
      rcases h with h1 | h2 | ⟨hEq, _⟩ | ⟨hEq, _⟩
      · exact False.elim (hv_not1 b h1)
      · exact h2
      · exact False.elim (hvr₁ hEq)
      · exact False.elim (hvr₂ hEq),
      fun h2 => Or.inr (Or.inl h2)⟩

lemma addBridge_conn {n : ℕ} {E₁ E₂ : SimpleGraph (Fin n)} {M₁ M₂ : Finset (Fin n)}
    {r₁ r₂ : Fin n} (hr₁ : r₁ ∈ M₁) (hr₂ : r₂ ∈ M₂) (hne : r₁ ≠ r₂)
    (hc₁ : ∀ a ∈ M₁, ∀ b ∈ M₁, (onSet E₁ M₁).Reachable a b)
    (hc₂ : ∀ a ∈ M₂, ∀ b ∈ M₂, (onSet E₂ M₂).Reachable a b) :
    ∀ a ∈ M₁ ∪ M₂, ∀ b ∈ M₁ ∪ M₂,
      (onSet (addBridge E₁ E₂ r₁ r₂ hne) (M₁ ∪ M₂)).Reachable a b := by
  let E := addBridge E₁ E₂ r₁ r₂ hne
  let M := M₁ ∪ M₂
  have hle1 : onSet E₁ M₁ ≤ onSet E M := fun u v h =>
    ⟨mem_union_left _ h.1, mem_union_left _ h.2.1, Or.inl h.2.2⟩
  have hle2 : onSet E₂ M₂ ≤ onSet E M := fun u v h =>
    ⟨mem_union_right _ h.1, mem_union_right _ h.2.1, Or.inr (Or.inl h.2.2)⟩
  have hadj_br : (onSet E M).Adj r₁ r₂ :=
    ⟨mem_union_left _ hr₁, mem_union_right _ hr₂, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  have hto_r₁ : ∀ a ∈ M, (onSet E M).Reachable a r₁ := by
    intro a ha
    rcases mem_union.mp ha with ha1 | ha2
    · obtain ⟨p⟩ := hc₁ a ha1 r₁ hr₁
      exact ⟨p.mapLe hle1⟩
    · obtain ⟨p⟩ := hc₂ a ha2 r₂ hr₂
      have hr : (onSet E M).Reachable a r₂ := ⟨p.mapLe hle2⟩
      exact hr.trans hadj_br.reachable.symm
  intro a ha b hb
  exact (hto_r₁ a ha).trans (hto_r₁ b hb).symm

lemma mem_foldr_union_iff {α : Type*} [DecidableEq α] (Ls : List (Finset α))
    (B₀ : Finset α) (x : α) :
    x ∈ Ls.foldr (· ∪ ·) B₀ ↔ x ∈ B₀ ∨ ∃ L ∈ Ls, x ∈ L := by
  induction Ls with
  | nil => simp
  | cons L Ls' ih =>
    simp only [List.foldr_cons, mem_union, ih, List.mem_cons]
    constructor
    · rintro (hxL | hxB₀ | ⟨L₁, hL₁, hxL₁⟩)
      · exact Or.inr ⟨L, Or.inl rfl, hxL⟩
      · exact Or.inl hxB₀
      · exact Or.inr ⟨L₁, Or.inr hL₁, hxL₁⟩
    · rintro (hxB₀ | ⟨L₁, rfl | hL₁, hxL₁⟩)
      · exact Or.inr (Or.inl hxB₀)
      · exact Or.inl hxL₁
      · exact Or.inr (Or.inr ⟨L₁, hL₁, hxL₁⟩)

lemma build_conn {n t ℓ : ℕ} {G : SimpleGraph (Fin n)} {J : Finset (Fin n)}
    {S : SimpleGraph (Fin t)} {B : Fin t → Finset (Fin n)}
    (hS : S.IsTree) (hℓ : 5 ≤ ℓ) (hdeg : G.maxDegree ≤ 3)
    (hBcard : ∀ a, (B a).card ≤ 2 * ℓ + 1 ∧ B a ⊆ J)
    (hBedge : ∀ x ∈ J, ∀ y ∈ J, G.Adj x y → ∃ a, x ∈ B a ∧ y ∈ B a)
    (hBconn : ∀ x ∈ J, (univ.filter fun a => x ∈ B a).Nonempty ∧
      ∀ a ∈ univ.filter (fun a => x ∈ B a), ∀ b ∈ univ.filter (fun a => x ∈ B a),
        (onSet S (univ.filter fun a => x ∈ B a)).Reachable a b)
    (U R : Finset (Fin n)) (hUJ : U ⊆ J) (hRU : R ⊆ U)
    (hRne : R.Nonempty) (hRcard : R.card ≤ 80 * ℓ)
    (hUconn : ∀ x ∈ U, ∀ y ∈ U, (onSet G U).Reachable x y) :
    ∃ D : PartData n,
      ValidOn G D U ∧
      (univ.filter (D.E.Adj D.r)).card ≤ 300 * ℓ ∧
      (∀ v ∈ D.M, v ≠ D.r → (univ.filter (D.E.Adj v)).card ≤ 300 * ℓ + 1) ∧
      (∀ v ∈ D.M, (U.filter fun x => D.owner x = v).card ≤ 100 * ℓ) ∧
      (∀ x ∈ R, D.owner x = D.r) := by
  obtain ⟨r₀, hr₀R⟩ := hRne
  have hr₀U : r₀ ∈ U := hRU hr₀R
  let φ : Fin n → Fin t := fun x =>
    if hx : x ∈ J then ((hBconn x hx).1).choose else ⟨0, by
      obtain ⟨a, _⟩ := (hBconn r₀ (hUJ hr₀U)).1
      exact Nat.zero_lt_of_lt a.2⟩
  have hφ : ∀ x ∈ R, x ∈ B (φ x) := by
    intro x hxR
    have hxJ : x ∈ J := hUJ (hRU hxR)
    have hmem := ((hBconn x hxJ).1).choose_spec
    dsimp only [φ]
    rw [dif_pos hxJ]
    exact (mem_filter.mp hmem).2
  let w : Fin t → ℕ := fun a => (R.filter fun x => φ x = a).card
  have hw_sum : ∑ a ∈ (univ : Finset (Fin t)), w a = R.card := by
    rw [← card_biUnion]
    · congr 1
      ext x
      simp only [mem_biUnion, mem_univ, true_and, mem_filter]
      exact ⟨fun ⟨_, hxR, _⟩ => hxR, fun hxR => ⟨φ x, hxR, rfl⟩⟩
    · intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun x hxa hxb =>
        hab ((mem_filter.mp hxa).2.symm.trans (mem_filter.mp hxb).2)
  have hB_pos : 0 < R.card / 8 + 1 := Nat.succ_pos _
  have hw_lt : (∑ a ∈ (univ : Finset (Fin t)), w a) < 8 * (R.card / 8 + 1) := by
    rw [hw_sum]
    omega
  obtain ⟨C, _, hCcard, hCsplit⟩ := forest_split S hS w (R.card / 8 + 1) hB_pos 8 (by omega) univ hw_lt
  let P₀ : Finset (Fin n) := R ∪ ((C.biUnion B) ∩ U)
  have hRP₀ : R ⊆ P₀ := subset_union_left
  have hP₀U : P₀ ⊆ U := union_subset hRU inter_subset_right
  have hr₀P₀ : r₀ ∈ P₀ := hRP₀ hr₀R
  have hP₀card : P₀.card ≤ 100 * ℓ := by
    dsimp only [P₀]
    have hCB : ((C.biUnion B) ∩ U).card ≤ 7 * (2 * ℓ + 1) := by
      calc ((C.biUnion B) ∩ U).card ≤ (C.biUnion B).card := card_le_card inter_subset_left
        _ ≤ ∑ c ∈ C, (B c).card := card_biUnion_le
        _ ≤ ∑ _c ∈ C, (2 * ℓ + 1) := sum_le_sum fun c _ => (hBcard c).1
        _ = C.card * (2 * ℓ + 1) := by simp
        _ ≤ 7 * (2 * ℓ + 1) := Nat.mul_le_mul_right _ hCcard
    have hu := card_union_le R ((C.biUnion B) ∩ U)
    omega
  obtain ⟨Ks, hKs_ne_sub, hKs_disj, hKs_cov, hKs_conn, hKs_closed⟩ := exists_comps G (U \ P₀)
  have hChild_props : ∀ K ∈ Ks,
      K.card < U.card ∧
      K ⊆ J ∧
      (K.filter fun y => ∃ x ∈ P₀, G.Adj x y).Nonempty ∧
      (K.filter fun y => ∃ x ∈ P₀, G.Adj x y).card ≤ 80 * ℓ := by
    intro K hK
    obtain ⟨hKne, hKsub⟩ := hKs_ne_sub K hK
    have hK_lt : K.card < U.card := by
      have h1 : K.card ≤ (U \ P₀).card := card_le_card hKsub
      have h2 : (U \ P₀).card < U.card := by
        rw [card_sdiff_of_subset hP₀U]
        have := card_pos.mpr ⟨r₀, hr₀P₀⟩
        have := card_le_card hP₀U
        omega
      omega
    have hKJ : K ⊆ J := (hKsub.trans sdiff_subset).trans hUJ
    have hR'_ne : (K.filter fun y => ∃ x ∈ P₀, G.Adj x y).Nonempty := by
      obtain ⟨z, hzK⟩ := hKne
      have hzU : z ∈ U := (hKsub.trans sdiff_subset) hzK
      obtain ⟨p⟩ := hUconn z hzU r₀ hr₀U
      have hwalk : ∀ {a c : Fin n} (q : (onSet G U).Walk a c),
          a ∈ K → c = r₀ → (K.filter fun y => ∃ x ∈ P₀, G.Adj x y).Nonempty := by
        intro a c q haK hcr₀
        induction q with
        | nil =>
          rw [hcr₀] at haK
          exfalso
          exact (mem_sdiff.mp (hKsub haK)).2 hr₀P₀
        | @cons a b _ hadj q' ih =>
          by_cases hbP₀ : b ∈ P₀
          · exact ⟨a, mem_filter.mpr ⟨haK, b, hbP₀, hadj.2.2.symm⟩⟩
          · have hb_diff : b ∈ U \ P₀ := mem_sdiff.mpr ⟨hadj.2.1, hbP₀⟩
            exact ih (hKs_closed K hK a haK b hb_diff hadj.2.2) hcr₀
      exact hwalk p hzK rfl
    have hR'_le : (K.filter fun y => ∃ x ∈ P₀, G.Adj x y).card ≤ 80 * ℓ :=
      boundary_bound hℓ hdeg hBcard hBedge hBconn hUJ hRU hRcard φ hφ hCcard hCsplit
        hKne hKsub (hKs_conn K hK)
    exact ⟨hK_lt, hKJ, hR'_ne, hR'_le⟩
  have hKs_len : Ks.length ≤ 300 * ℓ := by
    have hdeg3 : ∀ x : Fin n, (univ.filter (G.Adj x)).card ≤ 3 := by
      intro x
      have h1 : (univ.filter (G.Adj x)).card = G.degree x := by
        rw [← G.card_neighborFinset_eq_degree x]
        congr 1
        ext z
        simp [mem_neighborFinset]
      exact h1.le.trans ((G.degree_le_maxDegree x).trans hdeg)
    let Nbrs := P₀.biUnion (fun x => univ.filter (G.Adj x))
    have hNbrs_le : Nbrs.card ≤ 300 * ℓ := by
      calc Nbrs.card ≤ ∑ x ∈ P₀, (univ.filter (G.Adj x)).card := card_biUnion_le
        _ ≤ ∑ _x ∈ P₀, 3 := sum_le_sum fun x _ => hdeg3 x
        _ = P₀.card * 3 := by simp
        _ ≤ 300 * ℓ := by omega
    have hlen_le : ∀ (Ls : List (Finset (Fin n))),
        Ls.Pairwise Disjoint →
        (∀ K ∈ Ls, K.Nonempty) →
        Ls.length ≤ (Ls.foldr (· ∪ ·) ∅).card := by
      intro Ls hpw hne_int
      induction Ls with
      | nil => simp
      | cons K Ls' ih =>
        rw [List.pairwise_cons] at hpw
        have hdisj_K : Disjoint K (Ls'.foldr (· ∪ ·) ∅) := by
          refine Finset.disjoint_left.mpr fun x hxK hxRest => ?_
          rcases (mem_foldr_union_iff Ls' ∅ x).mp hxRest with h0 | ⟨L, hL, hxL⟩
          · exact notMem_empty x h0
          · exact Finset.disjoint_left.mp (hpw.1 L hL) hxK hxL
        simp only [List.length_cons, List.foldr_cons]
        rw [card_union_of_disjoint hdisj_K]
        have hpos : 1 ≤ K.card := card_pos.mpr (hne_int K List.mem_cons_self)
        have hrec := ih hpw.2 (fun L hL => hne_int L (List.mem_cons_of_mem _ hL))
        omega
    let Kints := Ks.map fun K => K ∩ Nbrs
    have hKints_pw : Kints.Pairwise Disjoint := by
      rw [List.pairwise_map]
      exact hKs_disj.imp fun h => Disjoint.mono inter_subset_left inter_subset_left h
    have hKints_ne : ∀ X ∈ Kints, X.Nonempty := by
      intro X hX
      obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hX
      obtain ⟨y, hy⟩ := (hChild_props K hK).2.2.1
      obtain ⟨hyK, x, hxP₀, hadj⟩ := mem_filter.mp hy
      exact ⟨y, mem_inter.mpr ⟨hyK, mem_biUnion.mpr ⟨x, hxP₀, mem_filter.mpr ⟨mem_univ _, hadj⟩⟩⟩⟩
    have hKints_sub : Kints.foldr (· ∪ ·) ∅ ⊆ Nbrs := by
      intro x hx
      rcases (mem_foldr_union_iff Kints ∅ x).mp hx with h0 | ⟨X, hX, hxX⟩
      · exact False.elim (notMem_empty x h0)
      · obtain ⟨K, _, rfl⟩ := List.mem_map.mp hX
        exact (mem_inter.mp hxX).2
    calc Ks.length = Kints.length := (List.length_map _).symm
      _ ≤ (Kints.foldr (· ∪ ·) ∅).card := hlen_le Kints hKints_pw hKints_ne
      _ ≤ Nbrs.card := card_le_card hKints_sub
      _ ≤ 300 * ℓ := hNbrs_le
  have hSub : ∀ (Ls : List (Finset (Fin n))),
      (∀ K ∈ Ls, K ∈ Ks) →
      Ls.Pairwise Disjoint →
      ∃ D : PartData n,
        ValidOn G D (Ls.foldr (· ∪ ·) P₀) ∧
        D.r = r₀ ∧
        (univ.filter (D.E.Adj r₀)).card ≤ Ls.length ∧
        (∀ v ∈ D.M, v ≠ r₀ → (univ.filter (D.E.Adj v)).card ≤ 300 * ℓ + 1) ∧
        (∀ v ∈ D.M, ((Ls.foldr (· ∪ ·) P₀).filter fun x => D.owner x = v).card ≤ 100 * ℓ) ∧
        (∀ x ∈ P₀, D.owner x = r₀) := by
    intro Ls
    induction Ls with
    | nil =>
      intro _ _
      let D₀ := singleBagData r₀
      have hval : ValidOn G D₀ P₀ :=
        ⟨singleton_subset_iff.mpr hr₀P₀,
         fun _ _ => mem_singleton_self r₀,
         fun _ _ _ _ _ => Or.inl rfl⟩
      refine ⟨D₀, hval, rfl, ?_, ?_, ?_, ?_⟩
      · simp [D₀, singleBagData]
      · intro v hv hne
        exact False.elim (hne (mem_singleton.mp hv))
      · intro v hv
        rw [mem_singleton.mp hv]
        exact (card_filter_le _ _).trans hP₀card
      · intro _ _
        rfl
    | cons K Ls' ih =>
      intro hmem_Ks hpw
      rw [List.pairwise_cons] at hpw
      have hK_in_Ks : K ∈ Ks := hmem_Ks K List.mem_cons_self
      obtain ⟨hK_lt, hKJ, hR'_ne, hR'_le⟩ := hChild_props K hK_in_Ks
      have hK_sub_diff : K ⊆ U \ P₀ := (hKs_ne_sub K hK_in_Ks).2
      have hK_conn : ∀ x ∈ K, ∀ y ∈ K, (onSet G K).Reachable x y := hKs_conn K hK_in_Ks
      let R' := K.filter fun y => ∃ x ∈ P₀, G.Adj x y
      have _ : K.card < U.card := hK_lt
      obtain ⟨DK, ⟨hDK_M, hDK_own, hDK_edge⟩, hDK_r, hDK_other, hDK_bag, hDK_R'⟩ :=
        build_conn hS hℓ hdeg hBcard hBedge hBconn K R' hKJ (filter_subset _ _) hR'_ne hR'_le hK_conn
      let W₁ := Ls'.foldr (· ∪ ·) P₀
      obtain ⟨D₁, ⟨hD₁_M, hD₁_own, hD₁_edge⟩, hD₁_r, hD₁_deg_r, hD₁_other, hD₁_bag, hD₁_P₀⟩ :=
        ih (fun L hL => hmem_Ks L (List.mem_cons_of_mem _ hL)) hpw.2
      have hP₀_sub_W₁ : P₀ ⊆ W₁ := fun x hx =>
        (mem_foldr_union_iff Ls' P₀ x).mpr (Or.inl hx)
      have hdisj_KW₁ : Disjoint K W₁ := by
        refine Finset.disjoint_left.mpr fun x hxK hxW₁ => ?_
        rcases (mem_foldr_union_iff Ls' P₀ x).mp hxW₁ with hxP₀ | ⟨L, hL, hxL⟩
        · exact (mem_sdiff.mp (hK_sub_diff hxK)).2 hxP₀
        · exact Finset.disjoint_left.mp (hpw.1 L hL) hxK hxL
      have hdisj_M : Disjoint D₁.M DK.M := Disjoint.mono hD₁_M hDK_M hdisj_KW₁.symm
      have hr₁_M₁ : r₀ ∈ D₁.M := hD₁_r ▸ D₁.r_mem
      have hne_rr : r₀ ≠ DK.r := fun h => Finset.disjoint_left.mp hdisj_M hr₁_M₁ (h ▸ DK.r_mem)
      let E' := addBridge D₁.E DK.E r₀ DK.r hne_rr
      let M' := D₁.M ∪ DK.M
      let W' := K ∪ W₁
      let owner' : Fin n → Fin n := fun x => if x ∈ W₁ then D₁.owner x else DK.owner x
      have hM'_sub : M' ⊆ W' := fun x hx => by
        rcases mem_union.mp hx with hx1 | hx2
        · exact mem_union_right _ (hD₁_M hx1)
        · exact mem_union_left _ (hDK_M hx2)
      have hE'_supp : ∀ a b, E'.Adj a b → a ∈ M' ∧ b ∈ M' := by
        intro a b hadj
        dsimp only [E'] at hadj
        rw [addBridge_adj] at hadj
        rcases hadj with h1 | h2 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨mem_union_left _ (D₁.E_supp a b h1).1, mem_union_left _ (D₁.E_supp a b h1).2⟩
        · exact ⟨mem_union_right _ (DK.E_supp a b h2).1, mem_union_right _ (DK.E_supp a b h2).2⟩
        · exact ⟨mem_union_left _ hr₁_M₁, mem_union_right _ DK.r_mem⟩
        · exact ⟨mem_union_right _ DK.r_mem, mem_union_left _ hr₁_M₁⟩
      have hE'_conn : ∀ a ∈ M', ∀ b ∈ M', (onSet E' M').Reachable a b :=
        addBridge_conn hr₁_M₁ DK.r_mem hne_rr D₁.E_conn DK.E_conn
      have hE'_card : E'.edgeFinset.card + 1 = M'.card := by
        have hc := addBridge_edgeFinset hdisj_M D₁.E_supp DK.E_supp hr₁_M₁ DK.r_mem hne_rr
        have hm := card_union_of_disjoint hdisj_M
        have c1 := D₁.E_card
        have c2 := DK.E_card
        dsimp only [E', M'] at *
        omega
      have howner'_W₁ : ∀ x ∈ W₁, owner' x = D₁.owner x := fun x hx => if_pos hx
      have howner'_K : ∀ x ∈ K, owner' x = DK.owner x := fun x hx =>
        if_neg (Finset.disjoint_left.mp hdisj_KW₁ hx)
      have howner'_mem : ∀ x ∈ W', owner' x ∈ M' := by
        intro x hx
        rcases mem_union.mp hx with hxK | hxW₁
        · rw [howner'_K x hxK]
          exact mem_union_right _ (hDK_own x hxK)
        · rw [howner'_W₁ x hxW₁]
          exact mem_union_left _ (hD₁_own x hxW₁)
      have hno_KL : ∀ x ∈ K, ∀ y ∈ W₁, G.Adj x y → y ∈ P₀ := by
        intro x hxK y hyW₁ hadj
        rcases (mem_foldr_union_iff Ls' P₀ y).mp hyW₁ with hyP₀ | ⟨L, hL, hyL⟩
        · exact hyP₀
        · exfalso
          have hL_in_Ks : L ∈ Ks := hmem_Ks L (List.mem_cons_of_mem _ hL)
          have hy_diff : y ∈ U \ P₀ := (hKs_ne_sub L hL_in_Ks).2 hyL
          have hyK : y ∈ K := hKs_closed K hK_in_Ks x hxK y hy_diff hadj
          exact Finset.disjoint_left.mp (hpw.1 L hL) hyK hyL
      have hedge_ok' : ∀ x ∈ W', ∀ y ∈ W', G.Adj x y →
          owner' x = owner' y ∨ E'.Adj (owner' x) (owner' y) := by
        intro x hx y hy hadj
        rcases mem_union.mp hx with hxK | hxW₁ <;> rcases mem_union.mp hy with hyK | hyW₁
        · rw [howner'_K x hxK, howner'_K y hyK]
          rcases hDK_edge x hxK y hyK hadj with heq | hadjE
          · exact Or.inl heq
          · right
            dsimp only [E']
            rw [addBridge_adj]
            exact Or.inr (Or.inl hadjE)
        · have hyP₀ : y ∈ P₀ := hno_KL x hxK y hyW₁ hadj
          have hxR' : x ∈ R' := mem_filter.mpr ⟨hxK, y, hyP₀, hadj.symm⟩
          rw [howner'_K x hxK, hDK_R' x hxR', howner'_W₁ y hyW₁, hD₁_P₀ y hyP₀]
          right
          dsimp only [E']
          rw [addBridge_adj]
          exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
        · have hxP₀ : x ∈ P₀ := hno_KL y hyK x hxW₁ hadj.symm
          have hyR' : y ∈ R' := mem_filter.mpr ⟨hyK, x, hxP₀, hadj⟩
          rw [howner'_W₁ x hxW₁, hD₁_P₀ x hxP₀, howner'_K y hyK, hDK_R' y hyR']
          right
          dsimp only [E']
          rw [addBridge_adj]
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · rw [howner'_W₁ x hxW₁, howner'_W₁ y hyW₁]
          rcases hD₁_edge x hxW₁ y hyW₁ hadj with heq | hadjE
          · exact Or.inl heq
          · right
            dsimp only [E']
            rw [addBridge_adj]
            exact Or.inl hadjE
      obtain ⟨hnbr_r₀, hnbr_DKr, hnbr_M₁, hnbr_MK⟩ :=
        addBridge_nbrs hdisj_M D₁.E_supp DK.E_supp hr₁_M₁ DK.r_mem hne_rr
      let D' : PartData n := {
        M := M'
        r := r₀
        E := E'
        owner := owner'
        r_mem := mem_union_left _ hr₁_M₁
        E_supp := hE'_supp
        E_conn := hE'_conn
        E_card := hE'_card
      }
      have hval' : ValidOn G D' ((K :: Ls').foldr (· ∪ ·) P₀) :=
        ⟨hM'_sub, howner'_mem, hedge_ok'⟩
      refine ⟨D', hval', rfl, ?_, ?_, ?_, ?_⟩
      · dsimp only [D', E']
        rw [hnbr_r₀]
        simp only [List.length_cons]
        omega
      · intro v hv hvr₀
        dsimp only [D', E']
        rcases mem_union.mp hv with hv1 | hv2
        · rw [hnbr_M₁ v hv1 hvr₀]
          exact hD₁_other v hv1 hvr₀
        · by_cases hvDK : v = DK.r
          · subst hvDK
            rw [hnbr_DKr]
            omega
          · rw [hnbr_MK v hv2 hvDK]
            exact hDK_other v hv2 hvDK
      · intro v hv
        dsimp only [D'] at hv ⊢
        simp only [List.foldr_cons]
        change (W'.filter fun x => owner' x = v).card ≤ 100 * ℓ
        rcases mem_union.mp hv with hv1 | hv2
        · have hfeq : (W'.filter fun x => owner' x = v) =
              (W₁.filter fun x => D₁.owner x = v) := by
            ext x
            simp only [W', mem_filter, mem_union]
            constructor
            · rintro ⟨hxK | hxW₁, hown⟩
              · exfalso
                rw [howner'_K x hxK] at hown
                exact Finset.disjoint_left.mp hdisj_M hv1 (hown ▸ hDK_own x hxK)
              · rw [howner'_W₁ x hxW₁] at hown
                exact ⟨hxW₁, hown⟩
            · rintro ⟨hxW₁, hown⟩
              exact ⟨Or.inr hxW₁, (howner'_W₁ x hxW₁).trans hown⟩
          rw [hfeq]
          exact hD₁_bag v hv1
        · have hfeq : (W'.filter fun x => owner' x = v) =
              (K.filter fun x => DK.owner x = v) := by
            ext x
            simp only [W', mem_filter, mem_union]
            constructor
            · rintro ⟨hxK | hxW₁, hown⟩
              · rw [howner'_K x hxK] at hown
                exact ⟨hxK, hown⟩
              · exfalso
                rw [howner'_W₁ x hxW₁] at hown
                exact Finset.disjoint_left.mp hdisj_M (hown ▸ hD₁_own x hxW₁) hv2
            · rintro ⟨hxK, hown⟩
              exact ⟨Or.inl hxK, (howner'_K x hxK).trans hown⟩
          rw [hfeq]
          exact hDK_bag v hv2
      · intro x hxP₀
        dsimp only [D']
        rw [howner'_W₁ x (hP₀_sub_W₁ hxP₀)]
        exact hD₁_P₀ x hxP₀
  obtain ⟨DFull, hDFull_val, hDFull_r, hDFull_deg_r, hDFull_other, hDFull_bag, hDFull_P₀⟩ :=
    hSub Ks (fun _ h => h) hKs_disj
  have hU_eq : Ks.foldr (· ∪ ·) P₀ = U := by
    ext x
    rw [mem_foldr_union_iff]
    constructor
    · rintro (hxP₀ | ⟨K, hK, hxK⟩)
      · exact hP₀U hxP₀
      · exact ((hKs_ne_sub K hK).2.trans sdiff_subset) hxK
    · intro hxU
      by_cases hxP₀ : x ∈ P₀
      · exact Or.inl hxP₀
      · obtain ⟨K, hK, hxK⟩ := hKs_cov x (mem_sdiff.mpr ⟨hxU, hxP₀⟩)
        exact Or.inr ⟨K, hK, hxK⟩
  refine ⟨DFull, hU_eq ▸ hDFull_val, ?_, ?_, ?_, ?_⟩
  · rw [hDFull_r]
    exact hDFull_deg_r.trans hKs_len
  · intro v hv hne
    rw [hDFull_r] at hne
    exact hDFull_other v hv hne
  · intro v hv
    rw [← hU_eq]
    exact hDFull_bag v hv
  · intro x hxR
    rw [hDFull_r]
    exact hDFull_P₀ x (hRP₀ hxR)
termination_by U.card

lemma chain_comps {n ℓ : ℕ} {G : SimpleGraph (Fin n)} {J : Finset (Fin n)}
    (_hℓ : 5 ≤ ℓ)
    (Cs : List (Finset (Fin n)))
    (hCs_ne_sub : ∀ C ∈ Cs, C.Nonempty ∧ C ⊆ J)
    (hCs_closed : ∀ C ∈ Cs, ∀ x ∈ C, ∀ y ∈ J, G.Adj x y → y ∈ C)
    (hBuild : ∀ C ∈ Cs, ∃ D : PartData n,
      ValidOn G D C ∧
      (univ.filter (D.E.Adj D.r)).card ≤ 300 * ℓ ∧
      (∀ v ∈ D.M, v ≠ D.r → (univ.filter (D.E.Adj v)).card ≤ 300 * ℓ + 1) ∧
      (∀ v ∈ D.M, (C.filter fun x => D.owner x = v).card ≤ 100 * ℓ)) :
    ∀ (Ls : List (Finset (Fin n))),
      Ls ≠ [] →
      (∀ C ∈ Ls, C ∈ Cs) →
      Ls.Pairwise Disjoint →
      ∃ D : PartData n,
        ValidOn G D (Ls.foldr (· ∪ ·) ∅) ∧
        (univ.filter (D.E.Adj D.r)).card ≤ 300 * ℓ + 1 ∧
        (∀ v ∈ D.M, (univ.filter (D.E.Adj v)).card ≤ 300 * ℓ + 2) ∧
        (∀ v ∈ D.M, ((Ls.foldr (· ∪ ·) ∅).filter fun x => D.owner x = v).card ≤ 100 * ℓ) := by
  intro Ls
  induction Ls with
  | nil =>
    intro hne
    exact False.elim (hne rfl)
  | cons C Ls' ih =>
    intro _ hmem hpw
    rw [List.pairwise_cons] at hpw
    have hC_in : C ∈ Cs := hmem C List.mem_cons_self
    obtain ⟨DC, hDC_val, hDC_r, hDC_other, hDC_bag⟩ := hBuild C hC_in
    by_cases hLs'_nil : Ls' = []
    · subst hLs'_nil
      have hunion : ([C] : List (Finset (Fin n))).foldr (· ∪ ·) ∅ = C := by simp
      refine ⟨DC, hunion.symm ▸ hDC_val, ?_, ?_, ?_⟩
      · omega
      · intro v hv
        by_cases hvr : v = DC.r
        · subst hvr
          omega
        · have := hDC_other v hv hvr
          omega
      · intro v hv
        rw [hunion]
        exact hDC_bag v hv
    · obtain ⟨D₁, ⟨hD₁_M, hD₁_own, hD₁_edge⟩, hD₁_r, hD₁_all, hD₁_bag⟩ :=
        ih hLs'_nil (fun L hL => hmem L (List.mem_cons_of_mem _ hL)) hpw.2
      obtain ⟨hDC_M, hDC_own, hDC_edge⟩ := hDC_val
      let W₁ := Ls'.foldr (· ∪ ·) ∅
      have hdisj_CW₁ : Disjoint C W₁ := by
        refine Finset.disjoint_left.mpr fun x hxC hxW₁ => ?_
        rcases (mem_foldr_union_iff Ls' ∅ x).mp hxW₁ with h0 | ⟨L, hL, hxL⟩
        · exact notMem_empty x h0
        · exact Finset.disjoint_left.mp (hpw.1 L hL) hxC hxL
      have hdisj_M : Disjoint D₁.M DC.M := Disjoint.mono hD₁_M hDC_M hdisj_CW₁.symm
      have hne_rr : D₁.r ≠ DC.r := fun h => Finset.disjoint_left.mp hdisj_M D₁.r_mem (h ▸ DC.r_mem)
      let E' := addBridge D₁.E DC.E D₁.r DC.r hne_rr
      let M' := D₁.M ∪ DC.M
      let W' := C ∪ W₁
      let owner' : Fin n → Fin n := fun x => if x ∈ W₁ then D₁.owner x else DC.owner x
      have hM'_sub : M' ⊆ W' := fun x hx => by
        rcases mem_union.mp hx with hx1 | hx2
        · exact mem_union_right _ (hD₁_M hx1)
        · exact mem_union_left _ (hDC_M hx2)
      have hE'_supp : ∀ a b, E'.Adj a b → a ∈ M' ∧ b ∈ M' := by
        intro a b hadj
        dsimp only [E'] at hadj
        rw [addBridge_adj] at hadj
        rcases hadj with h1 | h2 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨mem_union_left _ (D₁.E_supp a b h1).1, mem_union_left _ (D₁.E_supp a b h1).2⟩
        · exact ⟨mem_union_right _ (DC.E_supp a b h2).1, mem_union_right _ (DC.E_supp a b h2).2⟩
        · exact ⟨mem_union_left _ D₁.r_mem, mem_union_right _ DC.r_mem⟩
        · exact ⟨mem_union_right _ DC.r_mem, mem_union_left _ D₁.r_mem⟩
      have hE'_conn : ∀ a ∈ M', ∀ b ∈ M', (onSet E' M').Reachable a b :=
        addBridge_conn D₁.r_mem DC.r_mem hne_rr D₁.E_conn DC.E_conn
      have hE'_card : E'.edgeFinset.card + 1 = M'.card := by
        have hc := addBridge_edgeFinset hdisj_M D₁.E_supp DC.E_supp D₁.r_mem DC.r_mem hne_rr
        have hm := card_union_of_disjoint hdisj_M
        have c1 := D₁.E_card
        have c2 := DC.E_card
        dsimp only [E', M'] at *
        omega
      have howner'_W₁ : ∀ x ∈ W₁, owner' x = D₁.owner x := fun x hx => if_pos hx
      have howner'_C : ∀ x ∈ C, owner' x = DC.owner x := fun x hx =>
        if_neg (Finset.disjoint_left.mp hdisj_CW₁ hx)
      have howner'_mem : ∀ x ∈ W', owner' x ∈ M' := by
        intro x hx
        rcases mem_union.mp hx with hxC | hxW₁
        · rw [howner'_C x hxC]
          exact mem_union_right _ (hDC_own x hxC)
        · rw [howner'_W₁ x hxW₁]
          exact mem_union_left _ (hD₁_own x hxW₁)
      have hno_CW₁ : ∀ x ∈ C, ∀ y ∈ W₁, ¬ G.Adj x y := by
        intro x hxC y hyW₁ hadj
        rcases (mem_foldr_union_iff Ls' ∅ y).mp hyW₁ with h0 | ⟨L, hL, hyL⟩
        · exact notMem_empty y h0
        · have hL_in : L ∈ Cs := hmem L (List.mem_cons_of_mem _ hL)
          have hyJ : y ∈ J := (hCs_ne_sub L hL_in).2 hyL
          have hyC : y ∈ C := hCs_closed C hC_in x hxC y hyJ hadj
          exact Finset.disjoint_left.mp (hpw.1 L hL) hyC hyL
      have hedge_ok' : ∀ x ∈ W', ∀ y ∈ W', G.Adj x y →
          owner' x = owner' y ∨ E'.Adj (owner' x) (owner' y) := by
        intro x hx y hy hadj
        rcases mem_union.mp hx with hxC | hxW₁ <;> rcases mem_union.mp hy with hyC | hyW₁
        · rw [howner'_C x hxC, howner'_C y hyC]
          rcases hDC_edge x hxC y hyC hadj with heq | hadjE
          · exact Or.inl heq
          · right
            dsimp only [E']
            rw [addBridge_adj]
            exact Or.inr (Or.inl hadjE)
        · exact False.elim (hno_CW₁ x hxC y hyW₁ hadj)
        · exact False.elim (hno_CW₁ y hyC x hxW₁ hadj.symm)
        · rw [howner'_W₁ x hxW₁, howner'_W₁ y hyW₁]
          rcases hD₁_edge x hxW₁ y hyW₁ hadj with heq | hadjE
          · exact Or.inl heq
          · right
            dsimp only [E']
            rw [addBridge_adj]
            exact Or.inl hadjE
      obtain ⟨hnbr_r₁, hnbr_DCr, hnbr_M₁, hnbr_MC⟩ :=
        addBridge_nbrs hdisj_M D₁.E_supp DC.E_supp D₁.r_mem DC.r_mem hne_rr
      let D' : PartData n := {
        M := M'
        r := DC.r
        E := E'
        owner := owner'
        r_mem := mem_union_right _ DC.r_mem
        E_supp := hE'_supp
        E_conn := hE'_conn
        E_card := hE'_card
      }
      have hval' : ValidOn G D' ((C :: Ls').foldr (· ∪ ·) ∅) :=
        ⟨hM'_sub, howner'_mem, hedge_ok'⟩
      refine ⟨D', hval', ?_, ?_, ?_⟩
      · dsimp only [D', E']
        rw [hnbr_DCr]
        omega
      · intro v hv
        dsimp only [D', E'] at hv ⊢
        rcases mem_union.mp hv with hv1 | hv2
        · by_cases hvr₁ : v = D₁.r
          · subst hvr₁
            rw [hnbr_r₁]
            omega
          · rw [hnbr_M₁ v hv1 hvr₁]
            exact hD₁_all v hv1
        · by_cases hvrC : v = DC.r
          · subst hvrC
            rw [hnbr_DCr]
            omega
          · rw [hnbr_MC v hv2 hvrC]
            have := hDC_other v hv2 hvrC
            omega
      · intro v hv
        dsimp only [D'] at hv ⊢
        simp only [List.foldr_cons]
        change (W'.filter fun x => owner' x = v).card ≤ 100 * ℓ
        rcases mem_union.mp hv with hv1 | hv2
        · have hfeq : (W'.filter fun x => owner' x = v) =
              (W₁.filter fun x => D₁.owner x = v) := by
            ext x
            simp only [W', mem_filter, mem_union]
            constructor
            · rintro ⟨hxC | hxW₁, hown⟩
              · exfalso
                rw [howner'_C x hxC] at hown
                exact Finset.disjoint_left.mp hdisj_M hv1 (hown ▸ hDC_own x hxC)
              · rw [howner'_W₁ x hxW₁] at hown
                exact ⟨hxW₁, hown⟩
            · rintro ⟨hxW₁, hown⟩
              exact ⟨Or.inr hxW₁, (howner'_W₁ x hxW₁).trans hown⟩
          rw [hfeq]
          exact hD₁_bag v hv1
        · have hfeq : (W'.filter fun x => owner' x = v) =
              (C.filter fun x => DC.owner x = v) := by
            ext x
            simp only [W', mem_filter, mem_union]
            constructor
            · rintro ⟨hxC | hxW₁, hown⟩
              · rw [howner'_C x hxC] at hown
                exact ⟨hxC, hown⟩
              · exfalso
                rw [howner'_W₁ x hxW₁] at hown
                exact Finset.disjoint_left.mp hdisj_M (hown ▸ hD₁_own x hxW₁) hv2
            · rintro ⟨hxC, hown⟩
              exact ⟨Or.inl hxC, (howner'_C x hxC).trans hown⟩
          rw [hfeq]
          exact hDC_bag v hv2

end TreeGlue

end OMA.Erdos559H2Proof

theorem OMA.solution : OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R1_H1_R1.H2 := by
  open scoped Classical in
  open OMA.Erdos559H2Proof SimpleGraph Finset in
  intro n ℓ G J hn hℓ hdeg ⟨t, S, B, hS, hBcard, _, hBedge, hBconn_raw⟩
  open scoped Classical in
  open OMA.Erdos559H2Proof SimpleGraph Finset in
  by_cases hJne : J.Nonempty
  · have hBconn : ∀ x ∈ J, (univ.filter fun a => x ∈ B a).Nonempty ∧
        ∀ a ∈ univ.filter (fun a => x ∈ B a), ∀ b ∈ univ.filter (fun a => x ∈ B a),
          (onSet S (univ.filter fun a => x ∈ B a)).Reachable a b :=
      fun x hx => induce_conn_to_onSet (hBconn_raw x hx)
    obtain ⟨Cs, hCs_ne_sub, hCs_disj, hCs_cov, hCs_conn, hCs_closed⟩ := exists_comps G J
    have hCs_nonnil : Cs ≠ [] := by
      intro hnil
      obtain ⟨x₀, hx₀J⟩ := hJne
      obtain ⟨C, hC, _⟩ := hCs_cov x₀ hx₀J
      rw [hnil] at hC
      exact List.not_mem_nil hC
    have hBuild : ∀ C ∈ Cs, ∃ D : PartData n,
        ValidOn G D C ∧
        (univ.filter (D.E.Adj D.r)).card ≤ 300 * ℓ ∧
        (∀ v ∈ D.M, v ≠ D.r → (univ.filter (D.E.Adj v)).card ≤ 300 * ℓ + 1) ∧
        (∀ v ∈ D.M, (C.filter fun x => D.owner x = v).card ≤ 100 * ℓ) := by
      intro C hC
      obtain ⟨⟨c₀, hc₀C⟩, hCJ⟩ := hCs_ne_sub C hC
      obtain ⟨DC, hval, h1, h2, h3, _⟩ := build_conn hS hℓ hdeg hBcard hBedge hBconn C {c₀} hCJ
        (singleton_subset_iff.mpr hc₀C) (singleton_nonempty c₀) (by simp; omega) (hCs_conn C hC)
      exact ⟨DC, hval, h1, h2, h3⟩
    obtain ⟨DFull, hDFull_val, _, hDFull_deg, hDFull_bag⟩ :=
      chain_comps hℓ Cs hCs_ne_sub hCs_closed hBuild Cs hCs_nonnil (fun _ h => h) hCs_disj
    have hJ_eq : Cs.foldr (· ∪ ·) ∅ = J := by
      ext x
      rw [mem_foldr_union_iff]
      constructor
      · rintro (h0 | ⟨C, hC, hxC⟩)
        · exact False.elim (notMem_empty x h0)
        · exact (hCs_ne_sub C hC).2 hxC
      · intro hxJ
        obtain ⟨C, hC, hxC⟩ := hCs_cov x hxJ
        exact Or.inr ⟨C, hC, hxC⟩
    have hValJ : ValidOn G DFull J := hJ_eq ▸ hDFull_val
    obtain ⟨_, hDFull_ownJ, hDFull_edgeJ⟩ := hValJ
    let M := DFull.M
    let E := DFull.E
    let owner := DFull.owner
    let m := M.card
    have hm_pos : 1 ≤ m := card_pos.mpr ⟨DFull.r, DFull.r_mem⟩
    have hm_le_n : m ≤ n := by
      calc M.card ≤ (univ : Finset (Fin n)).card := card_le_univ M
        _ = n := by simp
    let eM : M ≃ Fin m := M.equivFinOfCardEq rfl
    let T : SimpleGraph (Fin m) := {
      Adj := fun i j => E.Adj (eM.symm i).1 (eM.symm j).1
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun i h => E.loopless.irrefl _ h⟩
    }
    have hT_conn : T.Connected := by
      have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
      refine Connected.mk fun i j => ?_
      have hwalk : ∀ {a b : Fin n} (p : (onSet E M).Walk a b) (ha : a ∈ M) (hb : b ∈ M),
          T.Reachable (eM ⟨a, ha⟩) (eM ⟨b, hb⟩) := by
        intro a b p ha hb
        induction p with
        | nil => exact Reachable.refl _
        | @cons a c b hadj q ih =>
          have hc : c ∈ M := hadj.2.1
          have hTadj : T.Adj (eM ⟨a, ha⟩) (eM ⟨c, hc⟩) := by
            dsimp only [T]
            rw [eM.symm_apply_apply, eM.symm_apply_apply]
            exact hadj.2.2
          exact hTadj.reachable.trans (ih hc hb)
      obtain ⟨p⟩ := DFull.E_conn (eM.symm i).1 (eM.symm i).2 (eM.symm j).1 (eM.symm j).2
      have hr := hwalk p (eM.symm i).2 (eM.symm j).2
      simpa only [Subtype.eta, eM.apply_symm_apply] using hr
    have hT_edges : T.edgeFinset.card = E.edgeFinset.card := by
      refine card_bij (fun e _ => Sym2.map (fun i => (eM.symm i).1) e) ?_ ?_ ?_
      · intro e he
        revert he
        refine Sym2.ind (fun i j he => ?_) e
        rw [mem_edgeFinset, mem_edgeSet] at he
        have hmap : Sym2.map (fun k => (eM.symm k).1) s(i, j) = s((eM.symm i).1, (eM.symm j).1) := by simp
        rw [hmap, mem_edgeFinset, mem_edgeSet]
        exact he
      · intro e₁ _ e₂ _ heq
        exact Sym2.map.injective (Subtype.val_injective.comp eM.symm.injective) heq
      · intro e he
        revert he
        refine Sym2.ind (fun a b he => ?_) e
        rw [mem_edgeFinset, mem_edgeSet] at he
        obtain ⟨ha, hb⟩ := DFull.E_supp a b he
        refine ⟨s(eM ⟨a, ha⟩, eM ⟨b, hb⟩), ?_, ?_⟩
        · rw [mem_edgeFinset, mem_edgeSet]
          dsimp only [T]
          rw [eM.symm_apply_apply, eM.symm_apply_apply]
          exact he
        · simp
    have hT_tree : T.IsTree := by
      rw [isTree_iff_connected_and_card]
      refine ⟨hT_conn, ?_⟩
      have hce : Nat.card ↑T.edgeSet = T.edgeFinset.card := by
        rw [← T.coe_edgeFinset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
      rw [hce, hT_edges, Nat.card_fin]
      exact DFull.E_card
    have hT_deg : T.maxDegree ≤ 400 * ℓ := by
      refine T.maxDegree_le_of_forall_degree_le (400 * ℓ) fun i => ?_
      rw [← T.card_neighborFinset_eq_degree i]
      have hle_filt : (T.neighborFinset i).card ≤ (univ.filter (DFull.E.Adj (eM.symm i).1)).card := by
        refine card_le_card_of_injOn (fun j => (eM.symm j).1) ?_ ?_
        · intro j hj
          rw [mem_coe, mem_neighborFinset] at hj
          exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hj⟩)
        · intro j₁ _ j₂ _ heq
          exact eM.symm.injective (Subtype.ext heq)
      have hbound := hDFull_deg (eM.symm i).1 (eM.symm i).2
      omega
    let fiber : Fin n → Finset (Fin n) := fun v => J.filter fun x => owner x = v
    have hfiber_le : ∀ v : M, (fiber v.1).card ≤ 400 * ℓ := by
      intro v
      have hb := hDFull_bag v.1 v.2
      rw [hJ_eq] at hb
      exact hb.trans (by omega)
    let eF : (v : M) → fiber v.1 ≃ Fin (fiber v.1).card :=
      fun v => (fiber v.1).equivFinOfCardEq rfl
    have howner_J : ∀ x : J, owner x.1 ∈ M := fun x => hDFull_ownJ x.1 x.2
    let idx : M → Fin n → Fin (400 * ℓ) := fun v z =>
      if hz : z ∈ fiber v.1 then Fin.castLE (hfiber_le v) (eF v ⟨z, hz⟩)
      else ⟨0, by omega⟩
    let fFun : J → Fin m × Fin (400 * ℓ) := fun x =>
      let v : M := ⟨owner x.1, howner_J x⟩
      (eM v, idx v x.1)
    have hf_inj : Function.Injective fFun := by
      intro x y hxy
      obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
      let vx : M := ⟨owner x.1, howner_J x⟩
      let vy : M := ⟨owner y.1, howner_J y⟩
      have hv_eq : vx = vy := eM.injective h1
      have hown_eq : owner x.1 = owner y.1 := congrArg Subtype.val hv_eq
      change idx vx x.1 = idx vy y.1 at h2
      rw [← hv_eq] at h2
      have hx_fib : x.1 ∈ fiber vx.1 := mem_filter.mpr ⟨x.2, rfl⟩
      have hy_fib : y.1 ∈ fiber vx.1 := mem_filter.mpr ⟨y.2, hown_eq.symm⟩
      dsimp only [idx] at h2
      rw [dif_pos hx_fib, dif_pos hy_fib] at h2
      have h3 : eF vx ⟨x.1, hx_fib⟩ = eF vx ⟨y.1, hy_fib⟩ := Fin.castLE_injective _ h2
      have h4 := (eF vx).injective h3
      have h5 : x.1 = y.1 := congrArg (Subtype.val : ↥(fiber vx.1) → Fin n) h4
      exact Subtype.ext h5
    refine ⟨m, T, hm_pos, hm_le_n, hT_tree, hT_deg, ⟨fFun, hf_inj⟩, ?_⟩
    intro x y hadj
    have hok := hDFull_edgeJ x.1 x.2 y.1 y.2 hadj
    rcases hok with heq | hadjE
    · left
      change eM ⟨owner x.1, howner_J x⟩ = eM ⟨owner y.1, howner_J y⟩
      exact congrArg eM (Subtype.ext heq)
    · right
      change T.Adj (eM ⟨owner x.1, howner_J x⟩) (eM ⟨owner y.1, howner_J y⟩)
      dsimp only [T]
      rw [eM.symm_apply_apply, eM.symm_apply_apply]
      exact hadjE
  · rw [not_nonempty_iff_eq_empty] at hJne
    let T : SimpleGraph (Fin 1) := {
      Adj := fun _ _ => False
      symm := ⟨fun _ _ h => h⟩
      loopless := ⟨fun _ h => h⟩
    }
    have hT_conn : T.Connected := by
      refine Connected.mk fun i j => ?_
      rw [Subsingleton.elim i j]
    have hT_tree : T.IsTree := by
      rw [isTree_iff_connected_and_card]
      refine ⟨hT_conn, ?_⟩
      have hce : Nat.card ↑T.edgeSet = 0 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
        refine ⟨fun e => ?_⟩
        rcases e with ⟨s, hs⟩
        revert hs
        exact Sym2.ind (fun _ _ hs => hs) s
      rw [hce, Nat.card_fin]
    have hT_deg : T.maxDegree ≤ 400 * ℓ := by
      refine T.maxDegree_le_of_forall_degree_le (400 * ℓ) fun i => ?_
      rw [← T.card_neighborFinset_eq_degree i]
      have h0 : (T.neighborFinset i).card = 0 := by
        apply card_eq_zero.mpr
        ext j
        simp [T]
      omega
    let fEmpty : J ↪ Fin 1 × Fin (400 * ℓ) :=
      ⟨fun x => False.elim (notMem_empty x.1 (hJne ▸ x.2)),
       fun x => False.elim (notMem_empty x.1 (hJne ▸ x.2))⟩
    refine ⟨1, T, le_rfl, hn, hT_tree, by convert hT_deg, fEmpty, ?_⟩
    intro x
    exact False.elim (notMem_empty x.1 (hJne ▸ x.2))
