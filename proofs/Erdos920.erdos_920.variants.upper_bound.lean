import FormalConjectures.ErdosProblems.«920»

-- Problem: Erdős Problem 920 — upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/920.lean:70 (declaration Erdos920.erdos_920.variants.upper_bound)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset

variable {V : Type*} [DecidableEq V]

/-- Independence of a finset in a graph. -/
abbrev Ind (G : SimpleGraph V) (I : Finset V) : Prop := ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (Ind G) := fun I => by
  unfold Ind; infer_instance

lemma greedy (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (D : ℕ)
    (hD : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D) :
    ∃ I ⊆ S, Ind G I ∧ S.card ≤ (D + 1) * I.card := by
  have hne : (S.powerset.filter (Ind G)).Nonempty := ⟨∅, by simp [Ind]⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [mem_filter, mem_powerset] at hI
  refine ⟨I, hI.1, hI.2, ?_⟩
  have hcover : S ⊆ I ∪ I.biUnion (fun s => S.filter (G.Adj s)) := by
    intro v hv
    by_contra hcon
    simp only [mem_union, mem_biUnion, mem_filter, not_or, not_exists, not_and] at hcon
    obtain ⟨hvI, hadj⟩ := hcon
    have hind : Ind G (insert v I) := by
      intro a ha b hb
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact G.irrefl
      · exact fun h => hadj b hb hv h.symm
      · exact fun h => hadj a ha hv h
      · exact hI.2 a ha b hb
    have := hmax (insert v I)
      (by rw [mem_filter, mem_powerset]; exact ⟨insert_subset hv hI.1, hind⟩)
    rw [card_insert_of_notMem hvI] at this
    omega
  calc S.card ≤ _ := card_le_card hcover
    _ ≤ I.card + (I.biUnion (fun s => S.filter (G.Adj s))).card := card_union_le _ _
    _ ≤ I.card + I.card * D := by
        gcongr
        refine card_biUnion_le.trans ?_
        calc ∑ s ∈ I, (S.filter (G.Adj s)).card ≤ ∑ _s ∈ I, D :=
              sum_le_sum fun s hs => hD s (hI.1 hs)
          _ = I.card * D := by simp
    _ = (D + 1) * I.card := by ring

lemma ramsey (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) : ∀ (s : ℕ) (F : Finset V),
    (∀ T ⊆ F, ¬ G.IsNClique (s + 1) T) → m ^ s ≤ F.card → ∃ I ⊆ F, Ind G I ∧ m ≤ I.card := by
  intro s
  induction s with
  | zero =>
    intro F hF hc
    exfalso
    rw [pow_zero] at hc
    obtain ⟨v, hv⟩ := card_pos.mp hc
    exact hF {v} (by simpa using hv) (by simp [SimpleGraph.isNClique_iff])
  | succ s ih =>
    intro F hF hc
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨∅, by simp, by simp [Ind], by simp⟩
    by_cases h : ∃ v ∈ F, m ^ s ≤ (F.filter (G.Adj v)).card
    · obtain ⟨v, hv, hvc⟩ := h
      obtain ⟨I, hI, hind, hcard⟩ := ih (F.filter (G.Adj v)) (by
        intro T hT hcl
        have := hcl.insert (a := v) (fun b hb => (mem_filter.mp (hT hb)).2)
        refine hF _ ?_ this
        exact insert_subset hv (hT.trans (filter_subset _ _))) hvc
      exact ⟨I, hI.trans (filter_subset _ _), hind, hcard⟩
    · push Not at h
      have hpos : 0 < m ^ s := Nat.pow_pos hm
      obtain ⟨I, hI, hind, hcard⟩ := greedy G F (m ^ s - 1)
        (fun v hv => by have := h v hv; omega)
      refine ⟨I, hI, hind, ?_⟩
      rw [Nat.sub_add_cancel hpos] at hcard
      have : m ^ s * m ≤ m ^ s * I.card := by rw [← pow_succ]; exact hc.trans hcard
      exact Nat.le_of_mul_le_mul_left this hpos

lemma card_small_subsets (F : Finset V) (k : ℕ) :
    (F.powerset.filter (fun A => A.card ≤ k)).card ≤ (F.card + 1) ^ k := by
  induction k with
  | zero =>
    have : F.powerset.filter (fun A => A.card ≤ 0) ⊆ {∅} := by
      intro A hA
      rw [mem_filter] at hA
      rw [mem_singleton]
      exact card_eq_zero.mp (by omega)
    simpa using card_le_card this
  | succ k ih =>
    have hsub : F.powerset.filter (fun A => A.card ≤ k + 1) ⊆
        F.powerset.filter (fun A => A.card ≤ k) ∪ F.powersetCard (k + 1) := by
      intro A hA
      rw [mem_filter, mem_powerset] at hA
      rw [mem_union, mem_filter, mem_powerset, mem_powersetCard]
      rcases Nat.lt_or_ge A.card (k + 1) with h | h
      · left; exact ⟨hA.1, by omega⟩
      · right; exact ⟨hA.1, by omega⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ + _ := card_union_le _ _
      _ ≤ (F.card + 1) ^ k + F.card ^ (k + 1) := by
          gcongr
          rw [card_powersetCard]; exact Nat.choose_le_pow _ _
      _ ≤ (F.card + 1) ^ (k + 1) := by
          have h1 : F.card ^ k ≤ (F.card + 1) ^ k := Nat.pow_le_pow_left (by omega) k
          have h2 := Nat.mul_le_mul_right F.card h1
          rw [pow_succ, pow_succ]; linarith

lemma fiber_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) (hv : v ∈ S)
    (Δ k m q : ℕ) (hK : G.CliqueFree (q + 2))
    (hdeg : (S.filter (G.Adj v)).card ≤ Δ)
    (H1 : k * (2 * (m ^ q) ^ k) ≤ 4 * Δ)
    (H2 : 2 * (Δ + 1) ^ k ≤ 2 ^ m) (J : Finset V) :
    k * ((S.powerset.filter (Ind G)).filter
        (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J)).card
      ≤ 4 * ∑ I ∈ (S.powerset.filter (Ind G)).filter
          (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J),
          ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
  set Φ := (S.powerset.filter (Ind G)).filter
        (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J) with hΦ
  rcases Φ.eq_empty_or_nonempty with h0 | ⟨I0, hI0⟩
  · rw [h0]; simp
  have memΦ : ∀ I, I ∈ Φ ↔
      (I ⊆ S ∧ Ind G I ∧ I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J) := by
    intro I; rw [hΦ, mem_filter, mem_filter, mem_powerset, and_assoc]
  obtain ⟨hI0S, hI0ind, hI0J⟩ := (memΦ I0).mp hI0
  have hJS : J ⊆ S := by rw [← hI0J]; exact (filter_subset _ _).trans hI0S
  have hJind : Ind G J := by
    intro a ha b hb; rw [← hI0J] at ha hb
    exact hI0ind a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
  have hJv : ∀ u ∈ J, u ≠ v ∧ ¬ G.Adj v u := by
    intro u hu; rw [← hI0J] at hu; exact (mem_filter.mp hu).2
  have hdecomp : ∀ I ∈ Φ, v ∉ I → I = J ∪ I.filter (G.Adj v) := by
    intro I hI hvI
    obtain ⟨_, _, hIJ⟩ := (memΦ I).mp hI
    rw [← hIJ]
    ext u
    simp only [mem_union, mem_filter]
    constructor
    · intro hu
      by_cases hadj : G.Adj v u
      · exact Or.inr ⟨hu, hadj⟩
      · exact Or.inl ⟨hu, fun h => hvI (h ▸ hu), hadj⟩
    · rintro (h | h) <;> exact h.1
  have hJsub : ∀ I ∈ Φ, J ⊆ I := by
    intro I hI; rw [← ((memΦ I).mp hI).2.2]; exact filter_subset _ _
  have hIvΦ : insert v J ∈ Φ := by
    rw [memΦ]
    refine ⟨insert_subset hv hJS, ?_, ?_⟩
    · intro a ha b hb
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact G.irrefl
      · exact (hJv b hb).2
      · exact fun h => (hJv a ha).2 h.symm
      · exact hJind a ha b hb
    · ext u
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨h | h, h2⟩
        · exact absurd h h2.1
        · exact h
      · intro h; exact ⟨Or.inr h, hJv u h⟩
  set Φ' := Φ.filter (fun I => ¬ v ∈ I) with hΦ'
  set Φv := Φ.filter (fun I => v ∈ I) with hΦv
  have hcardΦ : Φv.card + Φ'.card = Φ.card := card_filter_add_card_filter_not _
  have hΦv1 : Φv.card ≤ 1 := by
    rw [card_le_one]
    have key : ∀ I ∈ Φv, I = insert v J := by
      intro I hI
      rw [mem_filter] at hI
      obtain ⟨hIΦ, hvI⟩ := hI
      obtain ⟨_, hind, hIJ⟩ := (memΦ I).mp hIΦ
      rw [← hIJ]
      ext u
      simp only [mem_insert, mem_filter]
      constructor
      · intro hu
        by_cases huv : u = v
        · exact Or.inl huv
        · exact Or.inr ⟨hu, huv, hind v hvI u hu⟩
      · rintro (h | h)
        · exact h ▸ hvI
        · exact h.1
    intro a ha b hb; rw [key a ha, key b hb]
  have hsum : ∑ I ∈ Φv, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) +
      ∑ I ∈ Φ', ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) =
      ∑ I ∈ Φ, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
    sum_filter_add_sum_filter_not _ _ _
  have hsumv : Δ ≤ ∑ I ∈ Φv, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
    have hmem : insert v J ∈ Φv := mem_filter.mpr ⟨hIvΦ, mem_insert_self _ _⟩
    refine le_trans ?_ (single_le_sum
      (f := fun I => (if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card)
      (fun _ _ => Nat.zero_le _) hmem)
    simp
  have hsum' : ∑ I ∈ Φ', (I.filter (G.Adj v)).card ≤
      ∑ I ∈ Φ', ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
    sum_le_sum (fun I _ => Nat.le_add_left _ _)
  set F := Φ'.biUnion (fun I => I.filter (G.Adj v)) with hF
  have hFS : F ⊆ S.filter (G.Adj v) := by
    intro u hu
    rw [mem_biUnion] at hu
    obtain ⟨I, hI, huI⟩ := hu
    rw [mem_filter] at huI ⊢
    exact ⟨((memΦ I).mp (mem_filter.mp hI).1).1 huI.1, huI.2⟩
  have hx : F.card ≤ Δ := (card_le_card hFS).trans hdeg
  have hinj : Set.InjOn (fun I : Finset V => I.filter (G.Adj v)) (Φ' : Set (Finset V)) := by
    intro I hI I' hI' heq
    rw [mem_coe, mem_filter] at hI hI'
    have h1 := hdecomp I hI.1 hI.2
    have h2 := hdecomp I' hI'.1 hI'.2
    simp only at heq
    calc I = J ∪ I.filter (G.Adj v) := h1
      _ = J ∪ I'.filter (G.Adj v) := by rw [heq]
      _ = I' := h2.symm
  have hsmall : (Φ'.filter (fun I => (I.filter (G.Adj v)).card ≤ k)).card ≤ (F.card + 1) ^ k := by
    refine le_trans ?_ (card_small_subsets F k)
    refine card_le_card_of_injOn (fun I => I.filter (G.Adj v)) ?_ (hinj.mono ?_)
    · intro I hI
      rw [mem_coe, mem_filter] at hI
      rw [mem_coe, mem_filter, mem_powerset]
      exact ⟨subset_biUnion_of_mem (fun I => I.filter (G.Adj v)) hI.1, hI.2⟩
    · intro I hI
      rw [mem_coe, mem_filter] at hI
      exact mem_coe.mpr hI.1
  have hbig : k * Φ'.card ≤ ∑ I ∈ Φ', (I.filter (G.Adj v)).card + k * (F.card + 1) ^ k := by
    have h1 : (Φ'.filter (fun I => (I.filter (G.Adj v)).card ≤ k)).card +
        (Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k)).card = Φ'.card :=
      card_filter_add_card_filter_not _
    have h2 : k * (Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k)).card ≤
        ∑ I ∈ Φ', (I.filter (G.Adj v)).card := by
      calc _ = ∑ _I ∈ Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k), k := by
            simp [mul_comm]
        _ ≤ ∑ I ∈ Φ'.filter (fun I => ¬ (I.filter (G.Adj v)).card ≤ k),
              (I.filter (G.Adj v)).card :=
            sum_le_sum (fun I hI => by have := (mem_filter.mp hI).2; omega)
        _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
    rw [← h1, mul_add]
    have := Nat.mul_le_mul_left k hsmall
    omega
  by_cases hA : 2 * (F.card + 1) ^ k ≤ Φ'.card
  · have h1 : 2 * (k * (F.card + 1) ^ k) ≤ k * Φ'.card := by
      calc 2 * (k * (F.card + 1) ^ k) = k * (2 * (F.card + 1) ^ k) := by ring
        _ ≤ _ := Nat.mul_le_mul_left k hA
    have hk1 : k * Φ.card ≤ k * (1 + Φ'.card) := Nat.mul_le_mul_left k (by omega)
    have hpos : 0 < (F.card + 1) ^ k := Nat.pow_pos (by omega)
    have hki : k ≤ k * Φ'.card := Nat.le_mul_of_pos_right _ (by omega)
    rw [mul_add, mul_one] at hk1
    omega
  · push Not at hA
    have hk1 : k * Φ.card ≤ k * (2 * (F.card + 1) ^ k) := Nat.mul_le_mul_left k (by omega)
    by_cases hL : F.card < m ^ q
    · have hP : (F.card + 1) ^ k ≤ (m ^ q) ^ k := Nat.pow_le_pow_left hL k
      have : k * (2 * (F.card + 1) ^ k) ≤ k * (2 * (m ^ q) ^ k) :=
        Nat.mul_le_mul_left k (by omega)
      omega
    · exfalso
      push Not at hL
      obtain ⟨A, hAF, hAind, hAm⟩ := ramsey G m q F (by
        intro T hT hcl
        have := hcl.insert (a := v) (fun b hb => (mem_filter.mp (hFS (hT hb))).2)
        exact hK _ this) hL
      have key : ∀ A' ⊆ A, (J ∪ A').filter (G.Adj v) = A' := by
        intro A' hA'
        ext u
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨h | h, h2⟩
          · exact absurd h2 (hJv u h).2
          · exact h
        · intro h; exact ⟨Or.inr h, (mem_filter.mp (hFS (hAF (hA' h)))).2⟩
      have hpow : A.powerset.card ≤ Φ'.card := by
        refine card_le_card_of_injOn (fun A' => J ∪ A') ?_ ?_
        · intro A' hA'
          rw [mem_coe, mem_powerset] at hA'
          have hA'F := hA'.trans hAF
          rw [mem_coe, hΦ', mem_filter, memΦ]
          refine ⟨⟨union_subset hJS (fun u hu => (mem_filter.mp (hFS (hA'F hu))).1), ?_, ?_⟩, ?_⟩
          · intro a ha b hb
            rw [mem_union] at ha hb
            have cross : ∀ a ∈ J, ∀ b ∈ A', ¬ G.Adj a b := by
              intro a ha b hb
              obtain ⟨I, hI, hbI⟩ := mem_biUnion.mp (hA'F hb)
              have hIΦ := (mem_filter.mp hI).1
              exact ((memΦ I).mp hIΦ).2.1 a (hJsub I hIΦ ha) b (mem_filter.mp hbI).1
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact hJind a ha b hb
            · exact cross a ha b hb
            · exact fun h => cross b hb a ha h.symm
            · exact hAind a (hA' ha) b (hA' hb)
          · ext u
            simp only [mem_filter, mem_union]
            constructor
            · rintro ⟨h | h, h2⟩
              · exact h
              · exact absurd (mem_filter.mp (hFS (hA'F h))).2 h2.2
            · intro h; exact ⟨Or.inl h, hJv u h⟩
          · intro hvm
            rw [mem_union] at hvm
            rcases hvm with h | h
            · exact (hJv v h).1 rfl
            · exact G.irrefl (mem_filter.mp (hFS (hA'F h))).2
        · intro A1 h1 A2 h2 heq
          rw [mem_coe, mem_powerset] at h1 h2
          simp only at heq
          calc A1 = (J ∪ A1).filter (G.Adj v) := (key A1 h1).symm
            _ = (J ∪ A2).filter (G.Adj v) := by rw [heq]
            _ = A2 := key A2 h2
      rw [card_powerset] at hpow
      have h3 : 2 ^ m ≤ 2 ^ A.card := Nat.pow_le_pow_right (by norm_num) hAm
      have h4 : (F.card + 1) ^ k ≤ (Δ + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      omega

lemma main_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (Δ k m q : ℕ) (hK : G.CliqueFree (q + 2))
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ Δ)
    (H1 : k * (2 * (m ^ q) ^ k) ≤ 4 * Δ)
    (H2 : 2 * (Δ + 1) ^ k ≤ 2 ^ m) :
    ∃ I ⊆ S, Ind G I ∧ k * S.card ≤ 8 * Δ * I.card := by
  set 𝓘 := S.powerset.filter (Ind G) with h𝓘
  have hne : 𝓘.Nonempty := ⟨∅, by simp [h𝓘, Ind]⟩
  have hv : ∀ v ∈ S, k * 𝓘.card ≤
      4 * ∑ I ∈ 𝓘, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
    intro v hv
    have hmaps : (𝓘 : Set (Finset V)).MapsTo
        (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u))
        (𝓘.image (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)) : Finset (Finset V)) :=
      fun I hI => mem_coe.mpr (mem_image_of_mem _ hI)
    rw [card_eq_sum_card_fiberwise hmaps, ← sum_fiberwise_of_maps_to hmaps, mul_sum, mul_sum]
    exact sum_le_sum (fun J _ => fiber_bound G S v hv Δ k m q hK (hdeg v hv) H1 H2 J)
  have hI : ∀ I ∈ 𝓘, ∑ v ∈ S, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card)
      ≤ 2 * Δ * I.card := by
    intro I hI
    rw [h𝓘, mem_filter, mem_powerset] at hI
    rw [sum_add_distrib]
    have h1 : ∑ v ∈ S, (if v ∈ I then Δ else 0) = I.card * Δ := by
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hI.1]; simp
    have h2 : ∑ v ∈ S, (I.filter (G.Adj v)).card = ∑ u ∈ I, (S.filter (G.Adj u)).card := by
      simp only [card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
      simp only [SimpleGraph.adj_comm]
    have h3 : ∑ u ∈ I, (S.filter (G.Adj u)).card ≤ I.card * Δ := by
      calc _ ≤ ∑ _u ∈ I, Δ := sum_le_sum fun u hu => hdeg u (hI.1 hu)
        _ = _ := by simp
    rw [h1, h2]; linarith
  by_contra hcon
  push Not at hcon
  have hlt : ∀ I ∈ 𝓘, 8 * Δ * I.card < k * S.card := fun I hI => by
    rw [h𝓘, mem_filter, mem_powerset] at hI; exact hcon I hI.1 hI.2
  have hsumlt : ∑ I ∈ 𝓘, 8 * Δ * I.card < ∑ _I ∈ 𝓘, k * S.card :=
    sum_lt_sum_of_nonempty hne hlt
  have htot : S.card * (k * 𝓘.card) ≤ 4 * ∑ I ∈ 𝓘, 2 * Δ * I.card := by
    calc S.card * (k * 𝓘.card) = ∑ _v ∈ S, k * 𝓘.card := by simp
      _ ≤ ∑ v ∈ S, 4 * ∑ I ∈ 𝓘, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
          sum_le_sum hv
      _ = 4 * ∑ I ∈ 𝓘, ∑ v ∈ S, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
          rw [← mul_sum, sum_comm]
      _ ≤ _ := Nat.mul_le_mul_left 4 (sum_le_sum hI)
  simp only [sum_const, smul_eq_mul, ← mul_sum] at hsumlt htot
  nlinarith

lemma numerics (q D k : ℕ) (hq : 1 ≤ q) (hD : D ≠ 0)
    (hk : k = Nat.log 2 D / (8 * q * (Nat.log 2 (Nat.log 2 D) + 1))) (hk1 : 1 ≤ k) :
    k * (2 * ((1 + (Nat.log 2 D + 1) * k) ^ q) ^ k) ≤ 4 * D ∧
      2 * (D + 1) ^ k ≤ 2 ^ (1 + (Nat.log 2 D + 1) * k) := by
  set l := Nat.log 2 D with hl
  set a := Nat.log 2 l + 1 with ha
  have hl1 : 2 ^ l ≤ D := Nat.pow_log_le_self 2 hD
  have hl2 : D < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have h8 : k * (8 * q * a) ≤ l := by rw [hk]; exact Nat.div_mul_le_self _ _
  have ha1 : 1 ≤ a := by omega
  have hqa : 1 ≤ q * a := Nat.mul_pos hq ha1
  have hz1 : a ≤ q * a * k := by
    calc a = 1 * a * 1 := by ring
      _ ≤ q * a * k := Nat.mul_le_mul (Nat.mul_le_mul hq le_rfl) hk1
  have e1 : a * 2 * q * k = 2 * (q * a * k) := by ring
  have e2 : k * (8 * q * a) = 8 * (q * a * k) := by ring
  have hkz : k ≤ q * a * k := by
    calc k = 1 * k := by ring
      _ ≤ q * a * k := Nat.mul_le_mul hqa le_rfl
  have hkl : k ≤ l := by omega
  have hla : l < 2 ^ a := Nat.lt_pow_succ_log_self (by norm_num) l
  constructor
  · have hm : 1 + (l + 1) * k ≤ (2 ^ a) ^ 2 := by
      have h1 : l + 1 ≤ 2 ^ a := hla
      have h2 := Nat.mul_le_mul_left (l + 1) hkl
      have h3 := Nat.mul_le_mul h1 h1
      nlinarith
    have h1 : ((1 + (l + 1) * k) ^ q) ^ k ≤ 2 ^ (a * 2 * q * k) := by
      calc _ ≤ (((2 ^ a) ^ 2) ^ q) ^ k := Nat.pow_le_pow_left (Nat.pow_le_pow_left hm q) k
        _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
    have hexp : a + 1 + a * 2 * q * k ≤ l + 2 := by omega
    calc k * (2 * ((1 + (l + 1) * k) ^ q) ^ k) ≤ 2 ^ a * (2 * 2 ^ (a * 2 * q * k)) := by
          gcongr; omega
      _ = 2 ^ (a + 1 + a * 2 * q * k) := by ring
      _ ≤ 2 ^ (l + 2) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = 4 * 2 ^ l := by ring
      _ ≤ 4 * D := by omega
  · calc 2 * (D + 1) ^ k ≤ 2 * (2 ^ (l + 1)) ^ k := by gcongr; omega
      _ = 2 ^ (1 + (l + 1) * k) := by rw [← pow_mul, pow_add, pow_one]

lemma real_ineq (t : ℝ) (ht : 2 ≤ t) :
    Real.log t ≤ (Nat.log 2 ⌊2 * t⌋₊ : ℝ) ∧
    ((Nat.log 2 (Nat.log 2 ⌊2 * t⌋₊) : ℕ) : ℝ) + 1 ≤ 40 * Real.log (Real.log (t + 1)) ∧
    0 < Real.log (Real.log (t + 1)) := by
  set D := ⌊2 * t⌋₊ with hD
  set l := Nat.log 2 D with hl
  have hDle : (D : ℝ) ≤ 2 * t := Nat.floor_le (by linarith)
  have hDlt : 2 * t < D + 1 := Nat.lt_floor_add_one _
  have hD4 : 4 ≤ D := Nat.le_floor (by push_cast; linarith)
  have hl1 : 2 ^ l ≤ D := Nat.pow_log_le_self 2 (by omega)
  have hl2 : D < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have hl0 : l ≠ 0 := by
    intro h; rw [h] at hl2; omega
  have hlam1 : 2 ^ (Nat.log 2 l) ≤ l := Nat.pow_log_le_self 2 hl0
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2' : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hx : (12:ℝ) / 11 ≤ Real.log (t + 1) := by
    have h3 := Real.log_three_gt_d9
    have : Real.log 3 ≤ Real.log (t + 1) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set x := Real.log (t + 1) with hxdef
  have hy : (1:ℝ) / 12 ≤ Real.log x := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < x by linarith)
    have h2 : x⁻¹ ≤ 11 / 12 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
    linarith
  refine ⟨?_, ?_, by linarith⟩
  · have h1 : t < 2 ^ l := by
      have : ((D + 1 : ℕ) : ℝ) ≤ ((2 ^ (l + 1) : ℕ) : ℝ) := by exact_mod_cast hl2
      push_cast at this
      rw [pow_succ] at this; linarith
    have h2 : Real.log t ≤ Real.log (2 ^ l) := Real.log_le_log (by linarith) h1.le
    rw [Real.log_pow] at h2
    have : (l:ℝ) * Real.log 2 ≤ l * 1 := by gcongr
    linarith
  · have hlR : (l:ℝ) * Real.log 2 ≤ 2 * x := by
      have h1 : ((2 ^ l : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hl1
      push_cast at h1
      have h2 : (2:ℝ) ^ l ≤ (t + 1) ^ 2 := by nlinarith
      have h3 := Real.log_le_log (by positivity) h2
      rw [Real.log_pow, Real.log_pow] at h3
      push_cast at h3; linarith
    have hl4 : (l:ℝ) ≤ 4 * x := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) l) (by linarith : (0:ℝ) ≤ Real.log 2 - 1 / 2)]
    have hlpos : (0:ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl0
    have h5 : Real.log l ≤ Real.log (4 * x) := Real.log_le_log hlpos hl4
    rw [Real.log_mul (by norm_num) (by linarith)] at h5
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h6 : ((Nat.log 2 l : ℕ) : ℝ) * Real.log 2 ≤ Real.log l := by
      have h1 : ((2 ^ (Nat.log 2 l) : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlam1
      push_cast at h1
      have := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow] at this
    have h7 : ((Nat.log 2 l : ℕ) : ℝ) - 2 ≤ 2 * Real.log x := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ((Nat.log 2 l : ℕ) : ℝ) - 2)
        (by linarith : (0:ℝ) ≤ Real.log 2 - 1 / 2)]
    linarith



lemma deg_bound (q : ℕ) (hq : 1 ≤ q) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK : G.CliqueFree (q + 2)) (S : Finset V) (D : ℕ) (hD : D ≠ 0)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D) :
    ∃ I ⊆ S, Ind G I ∧
      Nat.log 2 D * S.card ≤ 128 * q * (Nat.log 2 (Nat.log 2 D) + 1) * D * I.card := by
  set l := Nat.log 2 D with hl
  set a := Nat.log 2 l + 1 with ha
  set k := l / (8 * q * a) with hk
  have hb : 0 < 8 * q * a := by positivity
  have hlk : l < (k + 1) * (8 * q * a) := by
    rw [← Nat.div_lt_iff_lt_mul hb]; omega
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · obtain ⟨I, hIS, hI, hc⟩ := greedy G S D hdeg
    refine ⟨I, hIS, hI, ?_⟩
    rw [hk0] at hlk
    calc l * S.card ≤ (8 * q * a) * ((D + 1) * I.card) := Nat.mul_le_mul (by omega) hc
      _ ≤ (8 * q * a) * ((2 * D) * I.card) := by gcongr; omega
      _ ≤ _ := by nlinarith [Nat.zero_le (q * a * D * I.card)]
  · obtain ⟨hH1, hH2⟩ := numerics q D k hq hD hk hk1
    obtain ⟨I, hIS, hI, hc⟩ := main_bound G S D k _ q hK hdeg hH1 hH2
    refine ⟨I, hIS, hI, ?_⟩
    have hl2k : l ≤ 2 * k * (8 * q * a) := by
      have := Nat.mul_le_mul_right (8 * q * a) (show k + 1 ≤ 2 * k by omega)
      omega
    calc l * S.card ≤ (2 * k * (8 * q * a)) * S.card := Nat.mul_le_mul_right _ hl2k
      _ = 16 * q * a * (k * S.card) := by ring
      _ ≤ 16 * q * a * (8 * D * I.card) := Nat.mul_le_mul_left _ hc
      _ = _ := by ring

/-- The graph `G` with only the edges inside `S`. -/
def restr (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := by constructor; intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by constructor; intro u h; exact G.loopless.1 u h.1

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (restr G S).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ u ∈ S ∧ v ∈ S))

lemma deg_bound_rel (q : ℕ) (hq : 1 ≤ q) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hK : ∀ T ⊆ S, ¬ G.IsNClique (q + 2) T) (D : ℕ) (hD : D ≠ 0)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D) :
    ∃ I ⊆ S, Ind G I ∧
      Nat.log 2 D * S.card ≤ 128 * q * (Nat.log 2 (Nat.log 2 D) + 1) * D * I.card := by
  have hK' : (restr G S).CliqueFree (q + 2) := by
    intro T hT
    have hTS : T ⊆ S := by
      intro v hv
      obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne (by rw [hT.card_eq]; omega : 1 < T.card) v
      exact (hT.isClique hv hw hne.symm).2.1
    refine hK T hTS ⟨?_, hT.card_eq⟩
    intro a ha b hb hab
    exact (hT.isClique ha hb hab).1
  have hdeg' : ∀ v ∈ S, (S.filter ((restr G S).Adj v)).card ≤ D := by
    intro v hv
    refine le_trans (card_le_card ?_) (hdeg v hv)
    intro w hw
    rw [mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.1⟩
  obtain ⟨I, hIS, hI, hc⟩ := deg_bound q hq (restr G S) hK' S D hD hdeg'
  refine ⟨I, hIS, ?_, hc⟩
  intro a ha b hb hab
  exact hI a ha b hb ⟨hab, hIS ha, hIS hb⟩

lemma sq_le_four_two_pow (n : ℕ) : n ^ 2 ≤ 4 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num
    · have : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := this
        _ ≤ 2 * (4 * 2 ^ n) := by omega
        _ = 4 * 2 ^ (n + 1) := by ring

lemma log_sq_le (m : ℕ) (hm : m ≠ 0) : (Nat.log 2 m) ^ 2 ≤ 4 * m :=
  (sq_le_four_two_pow _).trans (Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 2 hm))

/-- Case A: small maximum degree, greedy only. -/
lemma caseA (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (j D : ℕ) (hj : 1 ≤ j)
    (hm : S.card ≠ 0)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D) (hD : D ^ (2 * (j + 1)) < S.card) :
    ∃ I ⊆ S, Ind G I ∧ S.card * (Nat.log 2 S.card) ^ j ≤ 4 ^ (j + 1) * I.card ^ (j + 1) := by
  obtain ⟨I, hIS, hI, hc⟩ := greedy G S D hdeg
  refine ⟨I, hIS, hI, ?_⟩
  set m := S.card with hmdef
  set i := I.card with hidef
  set L := Nat.log 2 m with hL
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have h1 : (D + 1) ^ (2 * (j + 1)) ≤ 4 ^ (j + 1) * m := by
    rcases Nat.eq_zero_or_pos D with h0 | hpos
    · subst h0
      simp only [zero_add, one_pow]
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · calc (D + 1) ^ (2 * (j + 1)) ≤ (2 * D) ^ (2 * (j + 1)) :=
            Nat.pow_le_pow_left (by omega) _
        _ = 4 ^ (j + 1) * D ^ (2 * (j + 1)) := by
            rw [mul_pow, pow_mul]; norm_num
        _ ≤ 4 ^ (j + 1) * m := Nat.mul_le_mul_left _ hD.le
  have h2 : m ^ (2 * (j + 1)) ≤ 4 ^ (j + 1) * m * i ^ (2 * (j + 1)) := by
    calc m ^ (2 * (j + 1)) ≤ ((D + 1) * i) ^ (2 * (j + 1)) := Nat.pow_le_pow_left hc _
      _ = (D + 1) ^ (2 * (j + 1)) * i ^ (2 * (j + 1)) := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_right _ h1
  have h3 : m ^ (2 * j + 1) ≤ 4 ^ (j + 1) * i ^ (2 * (j + 1)) := by
    have : m * m ^ (2 * j + 1) ≤ m * (4 ^ (j + 1) * i ^ (2 * (j + 1))) := by
      calc m * m ^ (2 * j + 1) = m ^ (2 * (j + 1)) := by ring
        _ ≤ 4 ^ (j + 1) * m * i ^ (2 * (j + 1)) := h2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hmpos
  have h4 : L ^ (2 * j) ≤ 4 ^ j * m ^ j := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (log_sq_le m hm) _
  have h5 : m ^ (j + 2) ≤ m ^ (2 * j + 1) := Nat.pow_le_pow_right hmpos (by omega)
  have h6 : (m * L ^ j) ^ 2 ≤ (4 ^ (j + 1) * i ^ (j + 1)) ^ 2 := by
    calc (m * L ^ j) ^ 2 = m ^ 2 * L ^ (2 * j) := by ring
      _ ≤ m ^ 2 * (4 ^ j * m ^ j) := Nat.mul_le_mul_left _ h4
      _ = 4 ^ j * m ^ (j + 2) := by ring
      _ ≤ 4 ^ j * m ^ (2 * j + 1) := Nat.mul_le_mul_left _ h5
      _ ≤ 4 ^ j * (4 ^ (j + 1) * i ^ (2 * (j + 1))) := Nat.mul_le_mul_left _ h3
      _ ≤ 4 ^ (j + 1) * (4 ^ (j + 1) * i ^ (2 * (j + 1))) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = _ := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h6


lemma indep_bound (j : ℕ) (hj : 1 ≤ j) : ∃ C N : ℕ, 2 ≤ N ∧
    ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
      N ≤ S.card → (∀ T ⊆ S, ¬ G.IsNClique (j + 1) T) →
      ∃ I ⊆ S, Ind G I ∧ S.card * (Nat.log 2 S.card) ^ (j - 1) ≤
        C * I.card ^ j * (Nat.log 2 (Nat.log 2 S.card) + 1) ^ (j - 1) := by
  induction j, hj using Nat.le_induction with
  | base =>
    refine ⟨1, 2, le_rfl, ?_⟩
    intro V _ G _ S _ hK
    refine ⟨S, Finset.Subset.refl _, ?_, by simp⟩
    intro a ha b hb hab
    refine hK {a, b} ?_ ⟨?_, Finset.card_pair hab.ne⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.mp hx]; exact hb
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hab
      · exact hab.symm
      · exact absurd rfl hxy
  | succ j hj ih =>
    obtain ⟨C', N', hN', ih⟩ := ih
    refine ⟨4 ^ (j + 1) + (4 * (j + 1)) ^ j * (128 * j * C'), N' ^ (2 * (j + 1)) + 2,
      by omega, ?_⟩
    intro V _ G _ S hS hK
    set m := S.card with hmdef
    have hm2 : 2 ≤ m := by omega
    have hm0 : m ≠ 0 := by omega
    set LLm := Nat.log 2 (Nat.log 2 m) + 1 with hLLm
    have hLL1 : 1 ≤ LLm ^ j := Nat.one_le_pow _ _ (by omega)
    set D := S.sup (fun v => (S.filter (G.Adj v)).card) with hDdef
    have hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D := fun v hv =>
      Finset.le_sup (f := fun v => (S.filter (G.Adj v)).card) hv
    simp only [Nat.add_sub_cancel]
    rcases Nat.lt_or_ge (D ^ (2 * (j + 1))) m with hA | hB
    · obtain ⟨I, hIS, hI, hc⟩ := caseA G S j D hj hm0 hdeg hA
      refine ⟨I, hIS, hI, ?_⟩
      calc m * Nat.log 2 m ^ j ≤ 4 ^ (j + 1) * I.card ^ (j + 1) := hc
        _ ≤ (4 ^ (j + 1) + (4 * (j + 1)) ^ j * (128 * j * C')) * I.card ^ (j + 1) :=
            Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    · -- large maximum degree
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hvS, hv⟩ := Finset.exists_mem_eq_sup S hSne
        (fun v => (S.filter (G.Adj v)).card)
      set T := S.filter (G.Adj v) with hT
      have hTD : T.card = D := hv.symm
      have hTS : T ⊆ S := Finset.filter_subset _ _
      have hDm : D ≤ m := hTD ▸ Finset.card_le_card hTS
      have hD2 : 2 ≤ D := by
        by_contra hlt
        have : D ≤ 1 := by omega
        have : D ^ (2 * (j + 1)) ≤ 1 := by
          calc D ^ (2 * (j + 1)) ≤ 1 ^ (2 * (j + 1)) := Nat.pow_le_pow_left this _
            _ = 1 := one_pow _
        omega
      have hDN : N' ≤ D := by
        by_contra hlt
        have h1 : D ≤ N' := by omega
        have : D ^ (2 * (j + 1)) ≤ N' ^ (2 * (j + 1)) := Nat.pow_le_pow_left h1 _
        omega
      have hKT : ∀ T' ⊆ T, ¬ G.IsNClique (j + 1) T' := by
        intro T' hT' hcl
        have hins : G.IsNClique (j + 1 + 1) (insert v T') :=
          hcl.insert (fun b hb => (Finset.mem_filter.mp (hT' hb)).2)
        refine hK (insert v T') ?_ hins
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hvS
        · exact hTS (hT' hx)
      obtain ⟨I2, hI2T, hI2, hc2⟩ := ih G T (hTD ▸ hDN) hKT
      rw [hTD] at hc2
      obtain ⟨I1, hI1S, hI1, hc1⟩ := deg_bound_rel j hj G S hK D (by omega) hdeg
      set l := Nat.log 2 D with hl
      set a := Nat.log 2 l + 1 with ha
      have hl1 : 1 ≤ l := by
        rw [hl]; exact Nat.log_pos (by norm_num) hD2
      -- choose the larger one
      obtain ⟨I, hIS, hI, h1, h2⟩ : ∃ I ⊆ S, Ind G I ∧ I1.card ≤ I.card ∧ I2.card ≤ I.card := by
        rcases le_total I1.card I2.card with h | h
        · exact ⟨I2, hI2T.trans hTS, hI2, h, le_rfl⟩
        · exact ⟨I1, hI1S, hI1, le_rfl, h⟩
      refine ⟨I, hIS, hI, ?_⟩
      set i := I.card with hi
      have hc1' : l * m ≤ 128 * j * a * D * i :=
        hc1.trans (Nat.mul_le_mul_left _ h1)
      have hc2' : D * l ^ (j - 1) ≤ C' * i ^ j * a ^ (j - 1) :=
        hc2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)))
      have hjj : l * l ^ (j - 1) = l ^ j := by
        rw [← pow_succ']; congr 1; omega
      have hjj' : a * a ^ (j - 1) = a ^ j := by
        rw [← pow_succ']; congr 1; omega
      have hprod : D * (m * l ^ j) ≤ D * (128 * j * C' * i ^ (j + 1) * a ^ j) := by
        calc D * (m * l ^ j) = (l * m) * (D * l ^ (j - 1)) := by rw [← hjj]; ring
          _ ≤ (128 * j * a * D * i) * (C' * i ^ j * a ^ (j - 1)) := Nat.mul_le_mul hc1' hc2'
          _ = D * (128 * j * C' * i ^ (j + 1) * (a * a ^ (j - 1))) := by ring
          _ = _ := by rw [hjj']
      have hmain : m * l ^ j ≤ 128 * j * C' * i ^ (j + 1) * a ^ j :=
        Nat.le_of_mul_le_mul_left hprod (by omega)
      have hLm : Nat.log 2 m ≤ 4 * (j + 1) * l := by
        have hlt : m < 2 ^ ((l + 1) * (2 * (j + 1))) := by
          calc m ≤ D ^ (2 * (j + 1)) := hB
            _ < (2 ^ (l + 1)) ^ (2 * (j + 1)) :=
                Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) D) (by omega)
            _ = _ := by rw [← pow_mul]
        have := Nat.log_lt_of_lt_pow hm0 hlt
        nlinarith
      have haLL : a ≤ LLm := by
        rw [ha, hLLm]
        exact Nat.succ_le_succ (Nat.log_mono_right (Nat.log_mono_right hDm))
      calc m * Nat.log 2 m ^ j ≤ m * (4 * (j + 1) * l) ^ j :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLm _)
        _ = (4 * (j + 1)) ^ j * (m * l ^ j) := by rw [mul_pow]; ring
        _ ≤ (4 * (j + 1)) ^ j * (128 * j * C' * i ^ (j + 1) * a ^ j) :=
            Nat.mul_le_mul_left _ hmain
        _ ≤ (4 * (j + 1)) ^ j * (128 * j * C' * i ^ (j + 1) * LLm ^ j) := by
            gcongr
        _ = ((4 * (j + 1)) ^ j * (128 * j * C')) * i ^ (j + 1) * LLm ^ j := by ring
        _ ≤ _ := by
            gcongr
            exact Nat.le_add_left _ _


lemma concave_step (β a m i : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hm : 0 < m)
    (him : i ≤ m) (hai : a * m ^ (1 - β) ≤ i) :
    (m - i) ^ β ≤ m ^ β - β * a := by
  have h1 : (m - i) = m * (1 + (-(i / m))) := by field_simp; ring
  have hs : -1 ≤ -(i / m) := by
    rw [neg_le_neg_iff, div_le_one hm]; exact him
  have h2 := rpow_one_add_le_one_add_mul_self hs hβ0.le hβ1
  have h3 : (m - i) ^ β = m ^ β * (1 + (-(i / m))) ^ β := by
    rw [h1, Real.mul_rpow hm.le (by linarith)]
  rw [h3]
  have hmβ : 0 < m ^ β := Real.rpow_pos_of_pos hm _
  have h4 : m ^ β * (1 + (-(i / m))) ^ β ≤ m ^ β * (1 + β * (-(i / m))) :=
    mul_le_mul_of_nonneg_left h2 hmβ.le
  have h5 : a ≤ m ^ β * (i / m) := by
    have e1 : m ^ β * m ^ (1 - β) = m := by
      rw [← Real.rpow_add hm]; simp
    have e2 : m ^ β * (a * m ^ (1 - β)) = a * m := by rw [mul_left_comm, e1]
    have h6 : m ^ β * (a * m ^ (1 - β)) ≤ m ^ β * i := mul_le_mul_of_nonneg_left hai hmβ.le
    rw [← mul_div_assoc, le_div_iff₀ hm]; linarith
  calc m ^ β * (1 + (-(i / m))) ^ β ≤ m ^ β * (1 + β * (-(i / m))) := h4
    _ = m ^ β - β * (m ^ β * (i / m)) := by ring
    _ ≤ m ^ β - β * a := by linarith [mul_le_mul_of_nonneg_left h5 hβ0.le]

lemma color_bound {V : Type} [DecidableEq V] (G : SimpleGraph V) (β a : ℝ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (ha : 0 < a) (M : ℕ)
    (hind : ∀ S : Finset V, M < S.card →
      ∃ I ⊆ S, Ind G I ∧ a * (S.card : ℝ) ^ (1 - β) ≤ I.card) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → ∃ (c : V → ℕ) (t : ℕ), (∀ v ∈ S, c v < t) ∧
      (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
      (t : ℝ) ≤ (S.card : ℝ) ^ β / (β * a) + min (S.card : ℝ) (M : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS
  have hβa : 0 < β * a := mul_pos hβ0 ha
  have step : ∀ I ⊆ S, I.Nonempty → Ind G I → ∃ (c : V → ℕ) (t : ℕ), (∀ v ∈ S, c v < t) ∧
      (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
      (t : ℝ) ≤ ((S.card : ℝ) - I.card) ^ β / (β * a) +
        min ((S.card : ℝ) - I.card) (M : ℝ) + 1 := by
    intro I hIS hIne hI
    have hlt : (S \ I).card < n := by
      rw [← hS]; exact Finset.card_lt_card (Finset.sdiff_ssubset hIS hIne)
    obtain ⟨c, t, h1, h2, h3⟩ := ih _ hlt (S \ I) rfl
    have hcard : ((S \ I).card : ℝ) = (S.card : ℝ) - I.card := by
      rw [Finset.card_sdiff_of_subset hIS, Nat.cast_sub (Finset.card_le_card hIS)]
    refine ⟨fun v => if v ∈ I then t else c v, t + 1, ?_, ?_, ?_⟩
    · intro v hv
      by_cases hvI : v ∈ I
      · simp [hvI]
      · simp only [hvI, if_false]
        exact Nat.lt_succ_of_lt (h1 v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩))
    · intro u hu v hv huv
      by_cases huI : u ∈ I <;> by_cases hvI : v ∈ I
      · exact absurd huv (hI u huI v hvI)
      · simp only [huI, hvI, if_true, if_false]
        exact (h1 v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩)).ne'
      · simp only [huI, hvI, if_true, if_false]
        exact (h1 u (Finset.mem_sdiff.mpr ⟨hu, huI⟩)).ne
      · simp only [huI, hvI, if_false]
        exact h2 u (Finset.mem_sdiff.mpr ⟨hu, huI⟩) v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩) huv
    · rw [hcard] at h3
      push_cast
      linarith
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨fun _ => 0, 0, by simp [hemp], by simp [hemp], ?_⟩
    simp [hemp]
    positivity
  have hmpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne
  rcases Nat.lt_or_ge M S.card with hbig | hsmall
  · obtain ⟨I, hIS, hI, hai⟩ := hind S hbig
    have hIpos : (0 : ℝ) < I.card :=
      lt_of_lt_of_le (mul_pos ha (Real.rpow_pos_of_pos hmpos _)) hai
    have hIne : I.Nonempty := Finset.card_pos.mp (by exact_mod_cast hIpos)
    obtain ⟨c, t, h1, h2, h3⟩ := step I hIS hIne hI
    refine ⟨c, t, h1, h2, ?_⟩
    have him : (I.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hIS
    have hcs := concave_step β a S.card I.card hβ0 hβ1 hmpos him hai
    have hmin1 : min ((S.card : ℝ) - I.card) (M : ℝ) ≤ M := min_le_right _ _
    have hmin2 : min (S.card : ℝ) (M : ℝ) = M := min_eq_right (by exact_mod_cast hbig.le)
    have hdiv : ((S.card : ℝ) - I.card) ^ β / (β * a) ≤ (S.card : ℝ) ^ β / (β * a) - 1 := by
      rw [div_le_iff₀ hβa, sub_mul, div_mul_cancel₀ _ hβa.ne']
      linarith
    rw [hmin2]; linarith
  · obtain ⟨v, hv⟩ := hne
    have hI : Ind G {v} := by
      intro a ha b hb hab
      rw [Finset.mem_singleton] at ha hb
      subst ha; subst hb
      exact G.loopless.1 _ hab
    obtain ⟨c, t, h1, h2, h3⟩ := step {v} (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v) hI
    refine ⟨c, t, h1, h2, ?_⟩
    rw [Finset.card_singleton, Nat.cast_one] at h3
    have h1le : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr ⟨v, hv⟩
    have hmin1 : min ((S.card : ℝ) - 1) (M : ℝ) ≤ (S.card : ℝ) - 1 := min_le_left _ _
    have hmin2 : min (S.card : ℝ) (M : ℝ) = S.card := min_eq_left (by exact_mod_cast hsmall)
    have hpow : ((S.card : ℝ) - 1) ^ β ≤ (S.card : ℝ) ^ β :=
      Real.rpow_le_rpow (by linarith) (by linarith) hβ0.le
    have hdiv : ((S.card : ℝ) - 1) ^ β / (β * a) ≤ (S.card : ℝ) ^ β / (β * a) :=
      div_le_div_of_nonneg_right hpow hβa.le
    rw [hmin2]; linarith


lemma final_real (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    3 ≤ Real.log n ∧ 1 ≤ Real.log (Real.log n) ∧ Real.log n / 2 ≤ (Nat.log 2 n : ℝ) ∧
    ((Nat.log 2 (Nat.log 2 n) : ℕ) : ℝ) + 1 ≤ 40 * Real.log (Real.log n) ∧
    Real.log n ≤ 2 * √(n : ℝ) := by
  have hnR : (2 : ℝ) ^ 16 ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith [show (0 : ℝ) < 2 ^ 16 by norm_num]
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have h3 : 3 ≤ Real.log n := by
    have : Real.log ((2 : ℝ) ^ 16) ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogpos : 0 < Real.log n := by linarith
  have h1 : 1 ≤ Real.log (Real.log n) := by
    rw [Real.le_log_iff_exp_le hlogpos]
    linarith [Real.exp_one_lt_d9]
  have hn' : (65536 : ℝ) ≤ n := by
    have : 65536 ≤ n := le_trans (by norm_num) hn
    exact_mod_cast this
  obtain ⟨r1, r2, r3⟩ := real_ineq ((n : ℝ) / 2) (by linarith)
  have hfl : ⌊2 * ((n : ℝ) / 2)⌋₊ = n := by
    rw [show 2 * ((n : ℝ) / 2) = n by ring]; exact Nat.floor_natCast n
  rw [hfl] at r1 r2
  have hhalf : Real.log ((n : ℝ) / 2) = Real.log n - Real.log 2 :=
    Real.log_div hnpos.ne' (by norm_num)
  refine ⟨h3, h1, by rw [hhalf] at r1; linarith, ?_, ?_⟩
  · have hle : Real.log ((n : ℝ) / 2 + 1) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by linarith)
    have hpos : 0 < Real.log ((n : ℝ) / 2 + 1) := Real.log_pos (by linarith)
    have := Real.log_le_log hpos hle
    linarith
  · have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnpos
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hnpos.le] at this
    linarith


lemma chi_bound (j : ℕ) (hj2 : 2 ≤ j) (C N : ℕ)
    (hIB : ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
      N ≤ S.card → (∀ T ⊆ S, ¬ G.IsNClique (j + 1) T) →
      ∃ I ⊆ S, Ind G I ∧ S.card * (Nat.log 2 S.card) ^ (j - 1) ≤
        C * I.card ^ j * (Nat.log 2 (Nat.log 2 S.card) + 1) ^ (j - 1))
    (n : ℕ) (hn : (N + 2) ^ 4 + 2 ^ 16 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree (j + 1)) :
    ∃ t : ℕ, G.Colorable t ∧
      (t : ℝ) ≤ (1280 * ((C : ℝ) + 1) + 2) *
        ((n : ℝ) * Real.log (Real.log n) / Real.log n) ^ (1 - (j : ℝ)⁻¹) := by
  classical
  have hn16 : 2 ^ 16 ≤ n := le_trans (Nat.le_add_left _ _) hn
  have hn4 : (N + 2) ^ 4 ≤ n := le_trans (Nat.le_add_right _ _) hn
  obtain ⟨h3, h1, hLn, hμ, hsq⟩ := final_real n hn16
  have hx16 : (65536 : ℝ) ≤ (n : ℝ) := by
    have : 65536 ≤ n := le_trans (by norm_num) hn16
    exact_mod_cast this
  set x : ℝ := (n : ℝ) with hx
  have hxpos : 0 < x := by linarith
  set β : ℝ := 1 - (j : ℝ)⁻¹ with hβ
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hjpos : (0 : ℝ) < j := by linarith
  have hjinv : (j : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hjR
  have hjinv0 : 0 < (j : ℝ)⁻¹ := inv_pos.mpr hjpos
  have hβhalf : 1 / 2 ≤ β := by rw [hβ]; linarith
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  have hβ0 : 0 < β := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  set r : ℝ := Real.log (Real.log x) / Real.log x with hr
  have hrpos : 0 < r := div_pos (by linarith) hlogpos
  have hB : x * Real.log (Real.log x) / Real.log x = x * r := by rw [hr, mul_div_assoc]
  rw [hB]
  set M := Nat.sqrt (Nat.sqrt n) with hM
  have hNM : N + 2 ≤ M := by
    rw [hM, Nat.le_sqrt', Nat.le_sqrt']
    calc ((N + 2) ^ 2) ^ 2 = (N + 2) ^ 4 := by ring
      _ ≤ n := hn4
  set lam := Nat.log 2 M with hlam
  have hlam1 : 1 ≤ lam := Nat.log_pos (by norm_num) (by omega)
  set Ln := Nat.log 2 n with hLn'
  set mu := Nat.log 2 Ln + 1 with hmu
  have hLnlam : Ln ≤ 8 * lam := by
    have e1 : n < (M + 1) ^ 4 := by
      have ha : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
      have hb : Nat.sqrt n < (M + 1) ^ 2 := Nat.lt_succ_sqrt' (Nat.sqrt n)
      calc n < (Nat.sqrt n + 1) ^ 2 := ha
        _ ≤ ((M + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hb _
        _ = (M + 1) ^ 4 := by ring
    have e2 : M + 1 ≤ 2 ^ (lam + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    have e3 : n < 2 ^ ((lam + 1) * 4) := by
      calc n < (M + 1) ^ 4 := e1
        _ ≤ (2 ^ (lam + 1)) ^ 4 := Nat.pow_le_pow_left e2 _
        _ = _ := by rw [← pow_mul]
    have := Nat.log_lt_of_lt_pow (by omega) e3
    omega
  have hlamR : Real.log x / 16 ≤ (lam : ℝ) := by
    have : (Ln : ℝ) ≤ 8 * lam := by exact_mod_cast hLnlam
    linarith
  have hmuR : (mu : ℝ) ≤ 40 * Real.log (Real.log x) := by rw [hmu]; push_cast; exact hμ
  have hlampos : (0 : ℝ) < lam := by exact_mod_cast hlam1
  have hmupos : (0 : ℝ) < mu := by rw [hmu]; positivity
  have h640r : (0 : ℝ) ≤ 640 * r := mul_nonneg (by norm_num) hrpos.le
  have hratio : (mu : ℝ) / lam ≤ 640 * r := by
    rw [div_le_iff₀ hlampos]
    have h := mul_le_mul_of_nonneg_left hlamR h640r
    have e : 640 * r * (Real.log x / 16) = 40 * Real.log (Real.log x) := by
      rw [hr]; field_simp; ring
    linarith
  set C1 : ℝ := (C : ℝ) + 1 with hC1
  have hC1pos : 1 ≤ C1 := by
    rw [hC1]; have : (0 : ℝ) ≤ C := Nat.cast_nonneg _; linarith
  have hden : 0 < C1 * (mu : ℝ) ^ (j - 1) := mul_pos (by linarith) (pow_pos hmupos _)
  set A : ℝ := (lam : ℝ) ^ (j - 1) / (C1 * (mu : ℝ) ^ (j - 1)) with hA
  have hApos : 0 < A := div_pos (pow_pos hlampos _) hden
  set a : ℝ := A ^ (j : ℝ)⁻¹ with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hApos _
  have hjne : j ≠ 0 := by omega
  have h1β : 1 - β = (j : ℝ)⁻¹ := by rw [hβ]; ring
  have hind : ∀ S : Finset (Fin n), M < S.card →
      ∃ I ⊆ S, Ind G I ∧ a * (S.card : ℝ) ^ (1 - β) ≤ I.card := by
    intro S hS
    obtain ⟨I, hIS, hI, hc⟩ := hIB G S (by omega) (fun T _ => hG T)
    refine ⟨I, hIS, hI, ?_⟩
    have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hl : lam ≤ Nat.log 2 S.card := Nat.log_mono_right hS.le
    have hm : Nat.log 2 (Nat.log 2 S.card) + 1 ≤ mu :=
      Nat.succ_le_succ (Nat.log_mono_right (Nat.log_mono_right hSn))
    have hc' : S.card * lam ^ (j - 1) ≤ (C + 1) * I.card ^ j * mu ^ (j - 1) := by
      calc S.card * lam ^ (j - 1) ≤ S.card * (Nat.log 2 S.card) ^ (j - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl _)
        _ ≤ C * I.card ^ j * (Nat.log 2 (Nat.log 2 S.card) + 1) ^ (j - 1) := hc
        _ ≤ (C + 1) * I.card ^ j * mu ^ (j - 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ C)) (Nat.pow_le_pow_left hm _)
    have hcR : (S.card : ℝ) * (lam : ℝ) ^ (j - 1) ≤
        C1 * (I.card : ℝ) ^ j * (mu : ℝ) ^ (j - 1) := by
      rw [hC1]; exact_mod_cast hc'
    have hAm : A * S.card ≤ (I.card : ℝ) ^ j := by
      rw [hA, div_mul_eq_mul_div, div_le_iff₀ hden]
      linarith
    rw [h1β, ha, ← Real.mul_rpow hApos.le (Nat.cast_nonneg _)]
    calc (A * S.card) ^ (j : ℝ)⁻¹ ≤ ((I.card : ℝ) ^ j) ^ (j : ℝ)⁻¹ :=
          Real.rpow_le_rpow (mul_nonneg hApos.le (Nat.cast_nonneg _)) hAm hjinv0.le
      _ = I.card := Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hjne
  obtain ⟨c, t, hc1, hc2, hc3⟩ :=
    color_bound G β a hβ0 hβ1 hapos M hind n Finset.univ (by simp)
  refine ⟨t, ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨c v, hc1 v (Finset.mem_univ v)⟩ : Fin t)) ?_⟩, ?_⟩
  · intro u v huv h
    exact hc2 u (Finset.mem_univ u) v (Finset.mem_univ v) huv (congrArg Fin.val h)
  · have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = x := by simp [hx]
    rw [hcard] at hc3
    have hminM : min x (M : ℝ) ≤ M := min_le_right _ _
    have hrβ : 0 ≤ r ^ β := Real.rpow_nonneg hrpos.le _
    have hinva : a⁻¹ ≤ 640 * C1 * r ^ β := by
      rw [ha, ← Real.inv_rpow hApos.le]
      have hAinv : A⁻¹ = C1 * ((mu : ℝ) / lam) ^ (j - 1) := by
        rw [hA, inv_div, div_pow, mul_div_assoc]
      have hAle : A⁻¹ ≤ C1 * (640 * r) ^ (j - 1) := by
        rw [hAinv]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg hmupos.le hlampos.le) hratio _) (by linarith)
      calc A⁻¹ ^ (j : ℝ)⁻¹ ≤ (C1 * (640 * r) ^ (j - 1)) ^ (j : ℝ)⁻¹ :=
            Real.rpow_le_rpow (inv_nonneg.mpr hApos.le) hAle hjinv0.le
        _ = C1 ^ (j : ℝ)⁻¹ * ((640 * r) ^ (j - 1)) ^ (j : ℝ)⁻¹ :=
            Real.mul_rpow (by linarith) (pow_nonneg h640r _)
        _ = C1 ^ (j : ℝ)⁻¹ * (640 * r) ^ β := by
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul h640r]
            congr 1
            rw [hβ, Nat.cast_sub (by omega), Nat.cast_one]
            field_simp
        _ = C1 ^ (j : ℝ)⁻¹ * (640 ^ β * r ^ β) := by
            rw [Real.mul_rpow (by norm_num) hrpos.le]
        _ ≤ C1 * (640 * r ^ β) := by
            have e1 : C1 ^ (j : ℝ)⁻¹ ≤ C1 := by
              calc C1 ^ (j : ℝ)⁻¹ ≤ C1 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le hC1pos (by linarith)
                _ = C1 := Real.rpow_one _
            have e2 : (640 : ℝ) ^ β ≤ 640 := by
              calc (640 : ℝ) ^ β ≤ 640 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
                _ = 640 := Real.rpow_one _
            exact mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 hrβ)
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hrβ) (by linarith)
        _ = 640 * C1 * r ^ β := by ring
    have hxβ : 0 ≤ x ^ β := Real.rpow_nonneg hxpos.le _
    have hmain1 : x ^ β / (β * a) ≤ 1280 * C1 * (x * r) ^ β := by
      rw [Real.mul_rpow hxpos.le hrpos.le, div_eq_mul_inv, mul_inv]
      have hβinv : β⁻¹ ≤ 2 := by
        have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hβhalf
        simpa using this
      have hainv0 : 0 ≤ a⁻¹ := inv_nonneg.mpr hapos.le
      calc x ^ β * (β⁻¹ * a⁻¹) ≤ x ^ β * (2 * (640 * C1 * r ^ β)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hβinv hinva hainv0 (by norm_num)) hxβ
        _ = 1280 * C1 * (x ^ β * r ^ β) := by ring
    have hMle : (M : ℝ) ≤ 2 * (x * r) ^ β := by
      have hM4 : (M : ℝ) ^ 2 ≤ √x := by
        have e1 : M ^ 2 ≤ Nat.sqrt n := Nat.sqrt_le' _
        have e2 : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' _
        have e1R : (M : ℝ) ^ 2 ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast e1
        have e2R : ((Nat.sqrt n : ℝ)) ^ 2 ≤ x := by rw [hx]; exact_mod_cast e2
        exact e1R.trans ((Real.le_sqrt (Nat.cast_nonneg _) hxpos.le).mpr e2R)
      have hsx : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hxx : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have hBge : √x / 2 ≤ x * r := by
        rw [hr, ← mul_div_assoc, le_div_iff₀ hlogpos]
        calc √x / 2 * Real.log x ≤ √x / 2 * (2 * √x) :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = √x * √x := by ring
          _ = x := hxx
          _ ≤ x * Real.log (Real.log x) := le_mul_of_one_le_right hxpos.le h1
      have hs2 : 2 ≤ √x := by
        rw [Real.le_sqrt' (by norm_num)]; linarith
      have hB1 : 1 ≤ x * r := by linarith
      have hsqrtB : (M : ℝ) / 2 ≤ √(x * r) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [sq_nonneg (M : ℝ)]
      calc (M : ℝ) ≤ 2 * √(x * r) := by linarith
        _ = 2 * (x * r) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ ≤ 2 * (x * r) ^ β := by
            have := Real.rpow_le_rpow_of_exponent_le hB1 hβhalf
            linarith
    calc (t : ℝ) ≤ x ^ β / (β * a) + min x (M : ℝ) := hc3
      _ ≤ 1280 * C1 * (x * r) ^ β + 2 * (x * r) ^ β := by linarith
      _ = _ := by ring

end OMA

theorem OMA.solution : type_of% @Erdos920.erdos_920.variants.upper_bound := by
  classical
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj2 : 2 ≤ j := by omega
  obtain ⟨C, N, hN2, hIB⟩ := OMA.indep_bound j (by omega)
  have hexp : (1 : ℝ) - 1 / (((j + 1 : ℕ) : ℝ) - 1) = 1 - (j : ℝ)⁻¹ := by
    push_cast; rw [add_sub_cancel_right, one_div]
  rw [hexp]
  refine Asymptotics.IsBigO.of_bound (1280 * ((C : ℝ) + 1) + 2) ?_
  rw [Filter.eventually_atTop]
  refine ⟨(N + 2) ^ 4 + 2 ^ 16, fun n hn => ?_⟩
  set K : ℝ := 1280 * ((C : ℝ) + 1) + 2 with hK
  set Bβ : ℝ := ((n : ℝ) * Real.log (Real.log n) / Real.log n) ^ (1 - (j : ℝ)⁻¹) with hBβ
  have hBnn : 0 ≤ Bβ := by
    obtain ⟨h3, h1, -, -, -⟩ := OMA.final_real n (le_trans (Nat.le_add_left _ _) hn)
    apply Real.rpow_nonneg
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith)
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hf : Erdos920.f (j + 1) n ≤ ⌊K * Bβ⌋₊ := by
    unfold Erdos920.f
    apply csSup_le
    · have hne : (⊥ : SimpleGraph (Fin n)).chromaticNumber ≠ ⊤ :=
        SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr
          ⟨_, SimpleGraph.colorable_of_fintype _⟩
      exact ⟨_, ⊥, SimpleGraph.cliqueFree_bot (by omega), (ENat.natCast_toNat hne).symm⟩
    · rintro x ⟨G, hG, hx⟩
      obtain ⟨t, hcol, ht⟩ := OMA.chi_bound j hj2 C N hIB n hn G hG
      have h1 : G.chromaticNumber ≤ t := hcol.chromaticNumber_le
      rw [hx] at h1
      have h2 : x ≤ t := by exact_mod_cast h1
      exact h2.trans (Nat.le_floor ht)
  rw [Real.norm_natCast, Real.norm_of_nonneg hBnn]
  calc (Erdos920.f (j + 1) n : ℝ) ≤ (⌊K * Bβ⌋₊ : ℝ) := by exact_mod_cast hf
    _ ≤ K * Bβ := Nat.floor_le (mul_nonneg hKnn hBnn)
