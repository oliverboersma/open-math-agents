import FormalConjectures.Wikipedia.GyarfasSumnerConjecture
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
# Kierstead-Penrice (1994): Radius-Two Trees Specify Chi-Bounded Classes

Proof of `GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.radius_two`
via the template method of Kierstead-Penrice (1994) and Scott-Seymour (2023).
-/

open SimpleGraph

/- ## Section 1: Coloring and Ramsey Combinators on Finsets -/

private def ColorableOn {V : Type*} (G : SimpleGraph V) (S : Finset V) (c : ℕ) : Prop :=
  ∃ col : V → ℕ, (∀ v ∈ S, col v < c) ∧ ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → col u ≠ col v

private lemma colorableOn_empty {V : Type*} (G : SimpleGraph V) (c : ℕ) :
    ColorableOn G ∅ c :=
  ⟨fun _ => 0, by simp, by simp⟩

private lemma colorableOn_mono_set {V : Type*} {G : SimpleGraph V} {S₁ S₂ : Finset V} {c : ℕ}
    (hsub : S₁ ⊆ S₂) (hcol : ColorableOn G S₂ c) : ColorableOn G S₁ c := by
  obtain ⟨col, hlt, hadj⟩ := hcol
  exact ⟨col, fun v hv => hlt v (hsub hv), fun u hu v hv => hadj u (hsub hu) v (hsub hv)⟩

private lemma colorableOn_mono_num {V : Type*} {G : SimpleGraph V} {S : Finset V} {c₁ c₂ : ℕ}
    (hle : c₁ ≤ c₂) (hcol : ColorableOn G S c₁) : ColorableOn G S c₂ := by
  obtain ⟨col, hlt, hadj⟩ := hcol
  exact ⟨col, fun v hv => lt_of_lt_of_le (hlt v hv) hle, hadj⟩

private lemma colorableOn_edgeless {V : Type*} {G : SimpleGraph V} {S : Finset V}
    (hno : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) : ColorableOn G S 1 :=
  ⟨fun _ => 0, fun _ _ => Nat.zero_lt_one, fun u hu v hv huv => absurd huv (hno u hu v hv)⟩

private lemma colorableOn_of_card_le {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) {c : ℕ} (hcard : S.card ≤ c) : ColorableOn G S c := by
  induction S using Finset.induction_on generalizing c with
  | empty => exact colorableOn_empty G c
  | insert a s has ih =>
    rw [Finset.card_insert_of_notMem has] at hcard
    obtain ⟨col, hlt, hadj⟩ := ih (c := c - 1) (by omega)
    let col' : V → ℕ := fun x => if x = a then c - 1 else col x
    refine ⟨col', ?_, ?_⟩
    · intro v hv
      dsimp [col']
      rcases Finset.mem_insert.mp hv with rfl | hvs
      · rw [if_pos rfl]; omega
      · have hne : v ≠ a := fun h => has (h ▸ hvs)
        rw [if_neg hne]
        have := hlt v hvs
        omega
    · intro u hu v hv huv
      dsimp [col']
      have hne_uv : u ≠ v := G.ne_of_adj huv
      by_cases hua : u = a
      · subst hua
        have hva : v ≠ u := hne_uv.symm
        have hvs : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hva
        rw [if_pos rfl, if_neg hva]
        have := hlt v hvs
        omega
      · by_cases hva : v = a
        · subst hva
          have hus : u ∈ s := (Finset.mem_insert.mp hu).resolve_left hua
          rw [if_neg hua, if_pos rfl]
          have := hlt u hus
          omega
        · have hus : u ∈ s := (Finset.mem_insert.mp hu).resolve_left hua
          have hvs : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hva
          rw [if_neg hua, if_neg hva]
          exact hadj u hus v hvs huv

private lemma colorableOn_union_add {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} {a b : ℕ} (hA : ColorableOn G A a) (hB : ColorableOn G B b) :
    ColorableOn G (A ∪ B) (a + b) := by
  obtain ⟨colA, hltA, hadjA⟩ := hA
  obtain ⟨colB, hltB, hadjB⟩ := hB
  let col : V → ℕ := fun x => if x ∈ A then colA x else a + colB x
  refine ⟨col, ?_, ?_⟩
  · intro v hv
    dsimp [col]
    by_cases hvA : v ∈ A
    · rw [if_pos hvA]; have := hltA v hvA; omega
    · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
      rw [if_neg hvA]; have := hltB v hvB; omega
  · intro u hu v hv huv
    dsimp [col]
    by_cases huA : u ∈ A
    · by_cases hvA : v ∈ A
      · rw [if_pos huA, if_pos hvA]; exact hadjA u huA v hvA huv
      · rw [if_pos huA, if_neg hvA]; have := hltA u huA; omega
    · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
      by_cases hvA : v ∈ A
      · rw [if_neg huA, if_pos hvA]; have := hltA v hvA; omega
      · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
        rw [if_neg huA, if_neg hvA]
        have := hadjB u huB v hvB huv
        omega

private lemma colorableOn_biUnion_self {V α : Type*} [DecidableEq V] [DecidableEq α]
    {G : SimpleGraph V} (J : Finset α) (F : α → Finset V) {m : ℕ}
    (hF : ∀ j ∈ J, ColorableOn G (F j) m) :
    ColorableOn G (J.biUnion F) (J.card * m) := by
  induction J using Finset.induction_on with
  | empty => simpa using colorableOn_empty G 0
  | insert a s has ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem has, Nat.add_one_mul, add_comm]
    exact colorableOn_union_add
      (hF a (Finset.mem_insert_self a s))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

private lemma colorableOn_biUnion {V α : Type*} [DecidableEq V] [DecidableEq α]
    {G : SimpleGraph V} {S : Finset V} (J : Finset α) (F : α → Finset V) {m : ℕ}
    (hsub : S ⊆ J.biUnion F) (hF : ∀ j ∈ J, ColorableOn G (F j) m) :
    ColorableOn G S (J.card * m) :=
  colorableOn_mono_set hsub (colorableOn_biUnion_self J F hF)

private lemma colorableOn_insert_of_deg_lt {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Finset V} {v : V} {c : ℕ}
    (hcol : ColorableOn G S c) (hdeg : (S.filter (G.Adj v)).card < c) :
    ColorableOn G (insert v S) c := by
  obtain ⟨col, hlt, hadj⟩ := hcol
  let used : Finset ℕ := (S.filter (G.Adj v)).image col
  have hused_lt : used.card < (Finset.range c).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_image_le hdeg
  have hex : ∃ col_v ∈ Finset.range c, col_v ∉ used := by
    by_contra hall
    have hsub : Finset.range c ⊆ used := fun x hx => by
      by_contra hxnot
      exact hall ⟨x, hx, hxnot⟩
    exact absurd (Finset.card_le_card hsub) (not_le.mpr hused_lt)
  obtain ⟨col_v, hcv_lt, hcv_not⟩ := hex
  let col' : V → ℕ := fun x => if x = v then col_v else col x
  refine ⟨col', ?_, ?_⟩
  · intro x hx
    dsimp [col']
    by_cases hxv : x = v
    · rw [if_pos hxv]; exact Finset.mem_range.mp hcv_lt
    · rw [if_neg hxv]
      exact hlt x ((Finset.mem_insert.mp hx).resolve_left hxv)
  · intro x hx y hy hxy
    dsimp [col']
    have hne : x ≠ y := G.ne_of_adj hxy
    by_cases hxv : x = v
    · subst hxv
      have hyv : y ≠ x := hne.symm
      have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hyv
      rw [if_pos rfl, if_neg hyv]
      intro heq
      exact hcv_not (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyS, hxy⟩, heq.symm⟩)
    · by_cases hyv : y = v
      · subst hyv
        have hxS : x ∈ S := (Finset.mem_insert.mp hx).resolve_left hxv
        rw [if_neg hxv, if_pos rfl]
        intro heq
        exact hcv_not (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, hxy.symm⟩, heq⟩)
      · have hxS : x ∈ S := (Finset.mem_insert.mp hx).resolve_left hxv
        have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hyv
        rw [if_neg hxv, if_neg hyv]
        exact hadj x hxS y hyS hxy

private lemma colorableOn_max_deg {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (S : Finset V) (k : ℕ)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ k) :
    ColorableOn G S (k + 1) := by
  induction S using Finset.induction_on with
  | empty => exact colorableOn_empty G (k + 1)
  | insert v s hvs ih =>
    have hs_deg : ∀ u ∈ s, (s.filter (G.Adj u)).card ≤ k := by
      intro u hu
      refine le_trans (Finset.card_le_card ?_) (hdeg u (Finset.mem_insert_of_mem hu))
      intro z hz
      obtain ⟨hzs, hzu⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hzs, hzu⟩
    have hv_deg : (s.filter (G.Adj v)).card < k + 1 := by
      have hle : (s.filter (G.Adj v)).card ≤ ((insert v s).filter (G.Adj v)).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨hzs, hzv⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hzs, hzv⟩
      have := hdeg v (Finset.mem_insert_self v s)
      omega
    exact colorableOn_insert_of_deg_lt (ih hs_deg) hv_deg

private lemma digraph_coloring {α : Type*} [DecidableEq α] (I : Finset α)
    (D : α → α → Prop) [DecidableRel D] (k : ℕ)
    (hout : ∀ i ∈ I, (I.filter (fun j => j ≠ i ∧ D i j)).card ≤ k) :
    ∃ col : α → Fin (2 * k + 1),
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → D i j → col i ≠ col j := by
  have hstrong : ∀ m : ℕ, ∀ J : Finset α, J.card ≤ m →
      (∀ i ∈ J, (J.filter (fun j => j ≠ i ∧ D i j)).card ≤ k) →
      ∃ col : α → Fin (2 * k + 1),
        ∀ i ∈ J, ∀ j ∈ J, i ≠ j → D i j → col i ≠ col j := by
    intro m
    induction m with
    | zero =>
      intro J hcard _
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]
      exact ⟨fun _ => ⟨0, by omega⟩, by simp⟩
    | succ m ih =>
      intro J hcard houtJ
      rcases J.eq_empty_or_nonempty with rfl | hJne
      · exact ⟨fun _ => ⟨0, by omega⟩, by simp⟩
      · let E := (J ×ˢ J).filter (fun p => p.1 ≠ p.2 ∧ D p.1 p.2)
        have hE_out : E.card = ∑ i ∈ J, (J.filter (fun j => j ≠ i ∧ D i j)).card := by
          have hbij : E = J.biUnion (fun i =>
              (J.filter (fun j => j ≠ i ∧ D i j)).image (fun j => (i, j))) := by
            ext ⟨a, b⟩
            simp only [E, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
              Finset.mem_image]
            constructor
            · rintro ⟨⟨ha, hb⟩, hne, hd⟩
              exact ⟨a, ha, b, ⟨hb, hne.symm, hd⟩, rfl⟩
            · rintro ⟨a', ha', b', ⟨hb', hne, hd⟩, hab⟩
              cases hab
              exact ⟨⟨ha', hb'⟩, hne.symm, hd⟩
          rw [hbij, Finset.card_biUnion]
          · refine Finset.sum_congr rfl fun i _ => Finset.card_image_of_injective _ ?_
            intro x y hxy
            exact (Prod.mk.inj hxy).2
          · intro i _ j _ hij
            dsimp [Function.onFun]
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            obtain ⟨b1, _, rfl⟩ := Finset.mem_image.mp hp1
            obtain ⟨b2, _, heq⟩ := Finset.mem_image.mp hp2
            exact hij (Prod.mk.inj heq).1.symm
        have hE_in : E.card = ∑ j ∈ J, (J.filter (fun i => i ≠ j ∧ D i j)).card := by
          have hbij : E = J.biUnion (fun j =>
              (J.filter (fun i => i ≠ j ∧ D i j)).image (fun i => (i, j))) := by
            ext ⟨a, b⟩
            simp only [E, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
              Finset.mem_image]
            constructor
            · rintro ⟨⟨ha, hb⟩, hne, hd⟩
              exact ⟨b, hb, a, ⟨ha, hne, hd⟩, rfl⟩
            · rintro ⟨b', hb', a', ⟨ha', hne, hd⟩, hab⟩
              cases hab
              exact ⟨⟨ha', hb'⟩, hne, hd⟩
          rw [hbij, Finset.card_biUnion]
          · refine Finset.sum_congr rfl fun j _ => Finset.card_image_of_injective _ ?_
            intro x y hxy
            exact (Prod.mk.inj hxy).1
          · intro i _ j _ hij
            dsimp [Function.onFun]
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            obtain ⟨a1, _, rfl⟩ := Finset.mem_image.mp hp1
            obtain ⟨a2, _, heq⟩ := Finset.mem_image.mp hp2
            exact hij (Prod.mk.inj heq).2.symm
        have hE_le : E.card ≤ J.card * k := by
          rw [hE_out]
          calc ∑ i ∈ J, (J.filter (fun j => j ≠ i ∧ D i j)).card
              ≤ ∑ _i ∈ J, k := Finset.sum_le_sum houtJ
            _ = J.card * k := by simp
        have hsum_deg : (∑ x ∈ J, (J.filter (fun y => y ≠ x ∧ (D x y ∨ D y x))).card) ≤
            J.card * (2 * k) := by
          have hmul2 : J.card * (2 * k) = J.card * k + J.card * k := by ring
          calc ∑ x ∈ J, (J.filter (fun y => y ≠ x ∧ (D x y ∨ D y x))).card
              ≤ ∑ x ∈ J, ((J.filter (fun y => y ≠ x ∧ D x y)).card +
                  (J.filter (fun y => y ≠ x ∧ D y x)).card) := by
                refine Finset.sum_le_sum fun x _ => ?_
                have hsub : J.filter (fun y => y ≠ x ∧ (D x y ∨ D y x)) ⊆
                    J.filter (fun y => y ≠ x ∧ D x y) ∪
                      J.filter (fun y => y ≠ x ∧ D y x) := by
                  intro y hy
                  obtain ⟨hyJ, hne, hd⟩ := Finset.mem_filter.mp hy
                  rcases hd with h1 | h2
                  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyJ, hne, h1⟩)
                  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyJ, hne, h2⟩)
                exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
            _ = E.card + E.card := by rw [Finset.sum_add_distrib, ← hE_out, ← hE_in]
            _ ≤ J.card * (2 * k) := by omega
        have hex_min : ∃ x ∈ J,
            (J.filter (fun y => y ≠ x ∧ (D x y ∨ D y x))).card ≤ 2 * k := by
          by_contra hall
          have hgt : J.card * (2 * k + 1) ≤
              ∑ x ∈ J, (J.filter (fun y => y ≠ x ∧ (D x y ∨ D y x))).card := by
            calc J.card * (2 * k + 1)
                = ∑ _x ∈ J, (2 * k + 1) := by simp
              _ ≤ ∑ x ∈ J, (J.filter (fun y => y ≠ x ∧ (D x y ∨ D y x))).card := by
                  refine Finset.sum_le_sum fun x hx => ?_
                  by_contra hlt
                  exact hall ⟨x, hx, by omega⟩
          have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
          have hmul : J.card * (2 * k) < J.card * (2 * k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          omega
        obtain ⟨x, hxJ, hxdeg⟩ := hex_min
        let J' := J.erase x
        have hJ'card : J'.card ≤ m := by
          have her := Finset.card_erase_of_mem hxJ
          have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
          dsimp [J']
          omega
        have houtJ' : ∀ i ∈ J', (J'.filter (fun j => j ≠ i ∧ D i j)).card ≤ k := by
          intro i hi
          refine le_trans (Finset.card_le_card ?_) (houtJ i (Finset.mem_erase.mp hi).2)
          intro j hj
          obtain ⟨hjJ', hji⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hjJ').2, hji⟩
        obtain ⟨col', hcol'⟩ := ih J' hJ'card houtJ'
        let N_x := J'.filter (fun y => D x y ∨ D y x)
        have hNx_card : N_x.card ≤ 2 * k := by
          refine le_trans (Finset.card_le_card ?_) hxdeg
          intro y hy
          obtain ⟨hyJ', hd⟩ := Finset.mem_filter.mp hy
          obtain ⟨hyne, hyJ⟩ := Finset.mem_erase.mp hyJ'
          exact Finset.mem_filter.mpr ⟨hyJ, hyne, hd⟩
        let used : Finset (Fin (2 * k + 1)) := N_x.image col'
        have hused_lt : used.card < (Finset.univ : Finset (Fin (2 * k + 1))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact lt_of_le_of_lt Finset.card_image_le (by omega)
        have hex_c : ∃ c₀ : Fin (2 * k + 1), c₀ ∉ used := by
          by_contra hall
          have hsub : (Finset.univ : Finset (Fin (2 * k + 1))) ⊆ used := fun c _ => by
            by_contra hnc; exact hall ⟨c, hnc⟩
          exact absurd (Finset.card_le_card hsub) (not_le.mpr hused_lt)
        obtain ⟨c₀, hc₀⟩ := hex_c
        let colNew : α → Fin (2 * k + 1) := fun z => if z = x then c₀ else col' z
        refine ⟨colNew, ?_⟩
        intro i hi j hj hij hdij
        dsimp [colNew]
        by_cases hix : i = x
        · subst hix
          have hjx : j ≠ i := hij.symm
          have hjJ' : j ∈ J' := Finset.mem_erase.mpr ⟨hjx, hj⟩
          rw [if_pos rfl, if_neg hjx]
          intro heq
          exact hc₀ (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hjJ', Or.inl hdij⟩, heq.symm⟩)
        · by_cases hjx : j = x
          · subst hjx
            have hiJ' : i ∈ J' := Finset.mem_erase.mpr ⟨hix, hi⟩
            rw [if_neg hix, if_pos rfl]
            intro heq
            exact hc₀ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiJ', Or.inr hdij⟩, heq⟩)
          · rw [if_neg hix, if_neg hjx]
            exact hcol' i (Finset.mem_erase.mpr ⟨hix, hi⟩) j (Finset.mem_erase.mpr ⟨hjx, hj⟩)
              hij hdij
  exact hstrong I.card I le_rfl hout

private lemma exists_indep_of_digraph {α : Type*} [DecidableEq α] (I : Finset α)
    (D : α → α → Prop) [DecidableRel D] (k : ℕ)
    (hout : ∀ i ∈ I, (I.filter (fun j => j ≠ i ∧ D i j)).card ≤ k) :
    ∃ J ⊆ I, I.card ≤ (2 * k + 1) * J.card ∧ ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ D i j := by
  obtain ⟨col, hcol⟩ := digraph_coloring I D k hout
  have hsum : I.card = ∑ c : Fin (2 * k + 1), (I.filter (fun i => col i = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (col i))
  by_contra hall
  have hle_sum : ∑ c : Fin (2 * k + 1), (2 * k + 1) * (I.filter (fun i => col i = c)).card <
      ∑ _c : Fin (2 * k + 1), I.card := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ => ?_
    by_contra hge
    have hind : ∀ i ∈ I.filter (fun i => col i = c),
        ∀ j ∈ I.filter (fun i => col i = c), i ≠ j → ¬ D i j := by
      intro i hi j hj hij hd
      obtain ⟨hiI, hic⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjI, hjc⟩ := Finset.mem_filter.mp hj
      exact hcol i hiI j hjI hij hd (hic.trans hjc.symm)
    exact hall ⟨I.filter (fun i => col i = c), Finset.filter_subset _ _, by omega, hind⟩
  rw [← Finset.mul_sum, ← hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hle_sum
  exact lt_irrefl _ hle_sum

private lemma colorableOn_of_digraph_blocks {V α : Type*} [DecidableEq V] [DecidableEq α]
    {G : SimpleGraph V} (I : Finset α) (P : α → Finset V)
    (D : α → α → Prop) [DecidableRel D] (k M : ℕ)
    (hout : ∀ i ∈ I, (I.filter (fun j => j ≠ i ∧ D i j)).card ≤ k)
    (hind : ∀ J ⊆ I, (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ D i j) → ColorableOn G (J.biUnion P) M) :
    ColorableOn G (I.biUnion P) ((2 * k + 1) * M) := by
  obtain ⟨col, hcol⟩ := digraph_coloring I D k hout
  let F : Fin (2 * k + 1) → Finset V := fun c => (I.filter (fun i => col i = c)).biUnion P
  have hsub : I.biUnion P ⊆ Finset.univ.biUnion F := by
    intro v hv
    obtain ⟨i, hiI, hvPi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨col i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hiI, rfl⟩, hvPi⟩⟩
  have hcard : (Finset.univ : Finset (Fin (2 * k + 1))).card = 2 * k + 1 := by simp
  rw [← hcard]
  refine colorableOn_biUnion Finset.univ F hsub fun c _ => hind _ (Finset.filter_subset _ _) ?_
  intro i hi j hj hij hd
  obtain ⟨hiI, hic⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjI, hjc⟩ := Finset.mem_filter.mp hj
  exact hcol i hiI j hjI hij hd (hic.trans hjc.symm)

private lemma colorableOn_product_blocks {V α : Type*} [DecidableEq V] [DecidableEq α]
    {G : SimpleGraph V} [DecidableRel G.Adj] (I : Finset α) (P : α → Finset V) (M₁ M₂ : ℕ)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j))
    (hinner : ∀ i ∈ I, ColorableOn G (P i) M₁)
    (hcross : ∀ i ∈ I, ∀ v ∈ P i, ((I.biUnion P \ P i).filter (G.Adj v)).card ≤ M₂) :
    ColorableOn G (I.biUnion P) (M₁ * (M₂ + 1)) := by
  classical
  let U := I.biUnion P
  have hex1 : ∃ col₁ : V → ℕ, (∀ v ∈ U, col₁ v < M₁) ∧
      ∀ i ∈ I, ∀ u ∈ P i, ∀ v ∈ P i, G.Adj u v → col₁ u ≠ col₁ v := by
    choose f hf_lt hf_adj using fun i : {x // x ∈ I} => hinner i.1 i.2
    let idxOf : V → Option {x // x ∈ I} := fun v =>
      if hv : ∃ i ∈ I, v ∈ P i then some ⟨Classical.choose hv, (Classical.choose_spec hv).1⟩
      else none
    have hidx_eq : ∀ (i : α) (hi : i ∈ I) (v : V), v ∈ P i → idxOf v = some ⟨i, hi⟩ := by
      intro i hi v hv
      have hex : ∃ j ∈ I, v ∈ P j := ⟨i, hi, hv⟩
      dsimp [idxOf]
      rw [dif_pos hex]
      congr 1
      apply Subtype.ext
      by_contra hne
      have hj := Classical.choose_spec hex
      exact Finset.disjoint_left.mp (hdisj _ hj.1 i hi hne) hj.2 hv
    let col₁ : V → ℕ := fun v => match idxOf v with | some j => f j v | none => 0
    refine ⟨col₁, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, hiI, hvPi⟩ := Finset.mem_biUnion.mp hv
      dsimp [col₁]
      rw [hidx_eq i hiI v hvPi]
      exact hf_lt ⟨i, hiI⟩ v hvPi
    · intro i hiI u hu v hv huv
      dsimp [col₁]
      rw [hidx_eq i hiI u hu, hidx_eq i hiI v hv]
      exact hf_adj ⟨i, hiI⟩ u hu v hv huv
  obtain ⟨col₁, hlt₁, hadj₁⟩ := hex1
  let crossAdj : V → V → Prop := fun u v =>
    G.Adj u v ∧ ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ u ∈ P i ∧ v ∈ P j
  let G_cross : SimpleGraph V :=
    { Adj := crossAdj
      symm := ⟨fun _ _ ⟨huv, i, hi, j, hj, hij, hu, hv⟩ =>
        ⟨huv.symm, j, hj, i, hi, hij.symm, hv, hu⟩⟩
      loopless := ⟨fun v ⟨hvv, _⟩ => G.loopless.irrefl v hvv⟩ }
  have hcross_deg : ∀ v ∈ U, (U.filter (G_cross.Adj v)).card ≤ M₂ := by
    intro v hv
    obtain ⟨i, hiI, hvPi⟩ := Finset.mem_biUnion.mp hv
    refine le_trans (Finset.card_le_card ?_) (hcross i hiI v hvPi)
    intro w hw
    obtain ⟨hwU, hvw, i', hi'I, j', hj'I, hij', hvi', hwj'⟩ := Finset.mem_filter.mp hw
    have hii' : i = i' := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj i hiI i' hi'I hne) hvPi hvi'
    subst hii'
    have hw_not_Pi : w ∉ P i := fun hwPi =>
      Finset.disjoint_left.mp (hdisj i hiI j' hj'I hij') hwPi hwj'
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwU, hw_not_Pi⟩, hvw⟩
  obtain ⟨col₂, hlt₂, hadj₂⟩ := colorableOn_max_deg (G := G_cross) U M₂ hcross_deg
  let colProd : V → ℕ := fun x => (M₂ + 1) * col₁ x + col₂ x
  refine ⟨colProd, ?_, ?_⟩
  · intro v hv
    dsimp [colProd]
    have h1 := hlt₁ v hv
    have h2 := hlt₂ v hv
    calc (M₂ + 1) * col₁ v + col₂ v
        < (M₂ + 1) * col₁ v + (M₂ + 1) := by omega
      _ = (col₁ v + 1) * (M₂ + 1) := by ring
      _ ≤ M₁ * (M₂ + 1) := Nat.mul_le_mul_right (M₂ + 1) (by omega)
  · intro u hu v hv huv
    dsimp [colProd]
    obtain ⟨i, hiI, huPi⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨j, hjI, hvPj⟩ := Finset.mem_biUnion.mp hv
    by_cases hij : i = j
    · subst hij
      have hne1 := hadj₁ i hiI u huPi v hvPj huv
      have h2u := hlt₂ u hu
      have h2v := hlt₂ v hv
      intro heq
      have hdiv : ((M₂ + 1) * col₁ u + col₂ u) / (M₂ + 1) =
          ((M₂ + 1) * col₁ v + col₂ v) / (M₂ + 1) := congr_arg (· / (M₂ + 1)) heq
      rw [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
        Nat.div_eq_zero_iff.mpr (Or.inr h2u), Nat.div_eq_zero_iff.mpr (Or.inr h2v)] at hdiv
      omega
    · have hcr : G_cross.Adj u v := ⟨huv, i, hiI, j, hjI, hij, huPi, hvPj⟩
      have hne2 := hadj₂ u hu v hv hcr
      have h2u := hlt₂ u hu
      have h2v := hlt₂ v hv
      intro heq
      have hmod : ((M₂ + 1) * col₁ u + col₂ u) % (M₂ + 1) =
          ((M₂ + 1) * col₁ v + col₂ v) % (M₂ + 1) := congr_arg (· % (M₂ + 1)) heq
      rw [Nat.mul_add_mod, Nat.mul_add_mod,
        Nat.mod_eq_of_lt h2u, Nat.mod_eq_of_lt h2v] at hmod
      exact hne2 hmod

private lemma indep_of_colorableOn {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {C w : ℕ} (hC : 1 ≤ C) (hcol : ColorableOn G S C) (hcard : C * w ≤ S.card) :
    ∃ B ⊆ S, B.card = w ∧ ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v := by
  obtain ⟨col, hlt, hadj⟩ := hcol
  have hsum : S.card = ∑ c ∈ Finset.range C, (S.filter (fun v => col v = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_range.mpr (hlt v hv))
  have hex_c : ∃ c ∈ Finset.range C, w ≤ (S.filter (fun v => col v = c)).card := by
    by_contra hall
    have hlt_sum : ∑ c ∈ Finset.range C, (S.filter (fun v => col v = c)).card <
        ∑ _c ∈ Finset.range C, w := by
      refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) fun c hc => ?_
      by_contra hge
      exact hall ⟨c, hc, by omega⟩
    rw [← hsum, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt_sum
    omega
  obtain ⟨c, _, hwc⟩ := hex_c
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hwc
  refine ⟨B, hBsub.trans (Finset.filter_subset _ _), hBcard, ?_⟩
  intro u hu v hv huv
  obtain ⟨huS, huc⟩ := Finset.mem_filter.mp (hBsub hu)
  obtain ⟨hvS, hvc⟩ := Finset.mem_filter.mp (hBsub hv)
  exact hadj u huS v hvS huv (huc.trans hvc.symm)

private def ramseyNum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | p + 1, q + 1 => ramseyNum p (q + 1) + ramseyNum (p + 1) q + 1

private lemma ramsey_clique_or_indep {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℕ) (S : Finset V) (hcard : ramseyNum p q ≤ S.card) :
    (∃ K ⊆ S, K.card = p ∧ G.IsClique (K : Set V)) ∨
    (∃ I ⊆ S, I.card = q ∧ ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) := by
  induction p generalizing q S with
  | zero => exact Or.inl ⟨∅, Finset.empty_subset _, Finset.card_empty, by simp⟩
  | succ p ihp =>
    induction q generalizing S with
    | zero => exact Or.inr ⟨∅, Finset.empty_subset _, Finset.card_empty, by simp⟩
    | succ q ihq =>
      rw [ramseyNum] at hcard
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hvS⟩ := hne
      let S' := S.erase v
      let N := S'.filter (G.Adj v)
      let M := S'.filter (fun u => ¬ G.Adj v u)
      have hS'card : S'.card = S.card - 1 := Finset.card_erase_of_mem hvS
      have hNM : N.card + M.card = S'.card := by
        have hdisj : Disjoint N M := Finset.disjoint_left.mpr fun x hxN hxM =>
          (Finset.mem_filter.mp hxM).2 (Finset.mem_filter.mp hxN).2
        have hunion : N ∪ M = S' := by
          ext x
          simp only [N, M, Finset.mem_union, Finset.mem_filter]
          by_cases h : G.Adj v x <;> simp [h]
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      by_cases hN : ramseyNum p (q + 1) ≤ N.card
      · rcases ihp (q + 1) N hN with ⟨K, hKN, hKc, hKcl⟩ | ⟨I, hIN, hIc, hIi⟩
        · left
          have hvK : v ∉ K := fun hv =>
            (Finset.mem_erase.mp (Finset.filter_subset _ _ (hKN hv))).1 rfl
          refine ⟨insert v K, Finset.insert_subset_iff.mpr
            ⟨hvS, hKN.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))⟩,
            by rw [Finset.card_insert_of_notMem hvK, hKc], ?_⟩
          rw [Finset.coe_insert]
          exact hKcl.insert fun u hu _ => (Finset.mem_filter.mp (hKN hu)).2
        · exact Or.inr ⟨I, hIN.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)),
            hIc, hIi⟩
      · have hM : ramseyNum (p + 1) q ≤ M.card := by omega
        rcases ihq M hM with ⟨K, hKM, hKc, hKcl⟩ | ⟨I, hIM, hIc, hIi⟩
        · exact Or.inl ⟨K, hKM.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)),
            hKc, hKcl⟩
        · right
          have hvI : v ∉ I := fun hv =>
            (Finset.mem_erase.mp (Finset.filter_subset _ _ (hIM hv))).1 rfl
          refine ⟨insert v I, Finset.insert_subset_iff.mpr
            ⟨hvS, hIM.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))⟩,
            by rw [Finset.card_insert_of_notMem hvI, hIc], ?_⟩
          intro x hx y hy hxy
          rcases Finset.mem_insert.mp hx with rfl | hxI
          · rcases Finset.mem_insert.mp hy with rfl | hyI
            · exact G.loopless.irrefl _ hxy
            · exact (Finset.mem_filter.mp (hIM hyI)).2 hxy
          · rcases Finset.mem_insert.mp hy with rfl | hyI
            · exact (Finset.mem_filter.mp (hIM hxI)).2 hxy.symm
            · exact hIi x hxI y hyI hxy

private lemma indep_index_of_cliqueFreeOn {V α : Type*} [DecidableEq V] [DecidableEq α]
    {G : SimpleGraph V} [DecidableRel G.Adj] {V₀ : Finset V} {ω s : ℕ}
    (hcf : G.CliqueFreeOn (V₀ : Set V) (ω + 1))
    (J : Finset α) (g : α → V)
    (hmem : ∀ i ∈ J, g i ∈ V₀)
    (hinj : ∀ i ∈ J, ∀ j ∈ J, g i = g j → i = j)
    (hcard : ramseyNum (ω + 1) s ≤ J.card) :
    ∃ I' ⊆ J, I'.card = s ∧ ∀ i ∈ I', ∀ j ∈ I', ¬ G.Adj (g i) (g j) := by
  let S := J.image g
  have hScard : S.card = J.card := Finset.card_image_of_injOn hinj
  rcases ramsey_clique_or_indep G (ω + 1) s S (by omega) with
    ⟨K, hKS, hKc, hKcl⟩ | ⟨B, hBS, hBc, hBi⟩
  · exfalso
    have hKV₀ : (K : Set V) ⊆ (V₀ : Set V) := by
      intro x hx
      obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp (hKS (Finset.mem_coe.mp hx))
      exact Finset.mem_coe.mpr (hmem i hiJ)
    exact hcf hKV₀ ⟨hKcl, hKc⟩
  · let I' := J.filter (fun i => g i ∈ B)
    have hBij : B = I'.image g := by
      ext x
      simp only [I', Finset.mem_image, Finset.mem_filter]
      constructor
      · intro hxB
        obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp (hBS hxB)
        exact ⟨i, ⟨hiJ, hxB⟩, rfl⟩
      · rintro ⟨i, ⟨_, hgiB⟩, rfl⟩
        exact hgiB
    have hI'card : I'.card = s := by
      have hinj' : Set.InjOn g (I' : Set α) := fun i hi j hj hij =>
        hinj i (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
          j (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1 hij
      have hc := Finset.card_image_of_injOn hinj'
      rw [← hBij, hBc] at hc
      exact hc.symm
    refine ⟨I', Finset.filter_subset (fun i => g i ∈ B) J, hI'card, ?_⟩
    intro i hi j hj
    exact hBi (g i) (Finset.mem_filter.mp hi).2 (g j) (Finset.mem_filter.mp hj).2

/- ## Section 2: Universal Radius-Two Model Tree and Embedding -/

private abbrev RadTwoVert (s : ℕ) : Type := Unit ⊕ Fin s ⊕ (Fin s × Fin s)

private def modelTreeAdj (s : ℕ) : RadTwoVert s → RadTwoVert s → Prop
  | Sum.inl (), Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inl _), Sum.inl () => True
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr p) => i = p.1
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inl i) => i = p.1
  | _, _ => False

private def modelTree (s : ℕ) : SimpleGraph (RadTwoVert s) where
  Adj := modelTreeAdj s
  symm := ⟨by
    intro x y h
    rcases x with (_ | i | p) <;> rcases y with (_ | j | q) <;> simp_all [modelTreeAdj]⟩
  loopless := ⟨by intro x; rcases x with (_ | i | p) <;> simp [modelTreeAdj]⟩

private def HasModelTreeOn {V : Type*} (G : SimpleGraph V) (U : Finset V) (s : ℕ) : Prop :=
  ∃ (r₀ : V) (a : Fin s → V) (b : Fin s → Fin s → V),
    r₀ ∈ U ∧
    (∀ i, a i ∈ U) ∧
    (∀ i j, b i j ∈ U) ∧
    (∀ i j j', j ≠ j' → b i j ≠ b i j') ∧
    (∀ i, G.Adj r₀ (a i)) ∧
    (∀ i j, ¬ G.Adj r₀ (b i j)) ∧
    (∀ i j, i ≠ j → ¬ G.Adj (a i) (a j)) ∧
    (∀ i i' j, G.Adj (a i) (b i' j) ↔ i = i') ∧
    (∀ i j i' j', (i, j) ≠ (i', j') → ¬ G.Adj (b i j) (b i' j'))

private lemma hasModelTreeOn_mono {V : Type*} {G : SimpleGraph V} {U₁ U₂ : Finset V} {s : ℕ}
    (hsub : U₁ ⊆ U₂) (h : HasModelTreeOn G U₁ s) : HasModelTreeOn G U₂ s := by
  obtain ⟨r₀, a, b, hr, ha, hb, hdist, h1, h2, h3, h4, h5⟩ := h
  exact ⟨r₀, a, b, hsub hr, fun i => hsub (ha i), fun i j => hsub (hb i j),
    hdist, h1, h2, h3, h4, h5⟩

private def modelTreePhi {V : Type*} {s : ℕ} (r₀ : V) (a : Fin s → V) (b : Fin s → Fin s → V) :
    RadTwoVert s → V
  | Sum.inl () => r₀
  | Sum.inr (Sum.inl i) => a i
  | Sum.inr (Sum.inr p) => b p.1 p.2

private lemma isIndContained_of_hasModelTreeOn {V : Type*} {G : SimpleGraph V} {U : Finset V}
    {s : ℕ} (hs : 2 ≤ s) (h : HasModelTreeOn G U s) :
    SimpleGraph.IsIndContained (modelTree s) G := by
  obtain ⟨r₀, a, b, _, _, _, hb_ne, hr_a, hr_b, ha_a, ha_b, hb_b⟩ := h
  let φ := modelTreePhi r₀ a b
  have hinj : Function.Injective φ := by
    intro x y hxy
    rcases x with (_ | i | ⟨i, j⟩) <;> rcases y with (_ | i' | ⟨i', j'⟩) <;>
      dsimp [φ, modelTreePhi] at hxy
    · rfl
    · exfalso; have h1 := hr_a i'; rw [← hxy] at h1; exact G.loopless.irrefl r₀ h1
    · exfalso
      by_cases hi0 : i'.val = 0
      · have hk : (⟨1, hs⟩ : Fin s) ≠ i' := by
          intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
        have hadj : G.Adj (a ⟨1, hs⟩) r₀ := (hr_a ⟨1, hs⟩).symm
        rw [hxy] at hadj
        exact hk ((ha_b ⟨1, hs⟩ i' j').mp hadj)
      · have hk : (⟨0, by omega⟩ : Fin s) ≠ i' := by
          intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
        have hadj : G.Adj (a ⟨0, by omega⟩) r₀ := (hr_a ⟨0, by omega⟩).symm
        rw [hxy] at hadj
        exact hk ((ha_b ⟨0, by omega⟩ i' j').mp hadj)
    · exfalso; have h1 := hr_a i; rw [hxy] at h1; exact G.loopless.irrefl r₀ h1
    · congr 2
      by_contra hne
      have hadj : G.Adj (a i) (b i ⟨0, by omega⟩) := (ha_b i i ⟨0, by omega⟩).mpr rfl
      rw [hxy] at hadj
      exact hne ((ha_b i' i ⟨0, by omega⟩).mp hadj).symm
    · exfalso
      have hadj : G.Adj (a i') (b i' j') := (ha_b i' i' j').mpr rfl
      rw [← hxy] at hadj
      by_cases hii' : i = i'
      · subst hii'; exact G.loopless.irrefl (a i) hadj
      · exact ha_a i' i (Ne.symm hii') hadj
    · exfalso
      by_cases hi0 : i.val = 0
      · have hk : (⟨1, hs⟩ : Fin s) ≠ i := by
          intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
        have hadj : G.Adj (a ⟨1, hs⟩) r₀ := (hr_a ⟨1, hs⟩).symm
        rw [← hxy] at hadj
        exact hk ((ha_b ⟨1, hs⟩ i j).mp hadj)
      · have hk : (⟨0, by omega⟩ : Fin s) ≠ i := by
          intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
        have hadj : G.Adj (a ⟨0, by omega⟩) r₀ := (hr_a ⟨0, by omega⟩).symm
        rw [← hxy] at hadj
        exact hk ((ha_b ⟨0, by omega⟩ i j).mp hadj)
    · exfalso
      have hadj : G.Adj (a i) (b i j) := (ha_b i i j).mpr rfl
      rw [hxy] at hadj
      by_cases hii' : i = i'
      · subst hii'; exact G.loopless.irrefl (a i) hadj
      · exact ha_a i i' hii' hadj
    · congr 2
      have hii' : i = i' := by
        have hadj : G.Adj (a i) (b i j) := (ha_b i i j).mpr rfl
        rw [hxy] at hadj
        exact (ha_b i i' j').mp hadj
      subst hii'
      refine Prod.ext rfl ?_
      by_contra hjj'
      exact hb_ne i j j' hjj' hxy
  refine ⟨⟨⟨φ, hinj⟩, ?_⟩⟩
  intro x y
  rcases x with (_ | i | ⟨i, j⟩) <;> rcases y with (_ | i' | ⟨i', j'⟩) <;>
    dsimp [φ, modelTreePhi, modelTree, modelTreeAdj]
  · simp
  · simp [hr_a i']
  · simp [hr_b i' j']
  · simp [(hr_a i).symm]
  · constructor
    · intro h
      by_cases hii' : i = i'
      · subst hii'; exact G.loopless.irrefl (a i) h
      · exact ha_a i i' hii' h
    · exact False.elim
  · exact ha_b i i' j'
  · constructor
    · intro h; exact hr_b i j h.symm
    · exact False.elim
  · constructor
    · intro h; exact (ha_b i' i j).mp h.symm
    · rintro rfl; exact ((ha_b i' i' j).mpr rfl).symm
  · constructor
    · intro h
      by_cases heq : (i, j) = (i', j')
      · cases heq; exact G.loopless.irrefl (b i j) h
      · exact hb_b i j i' j' heq h
    · exact False.elim

private lemma tree_rad_two_indContained_modelTree
    {W : Type*} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    (hT : T.IsTree) (c : W) (hrad : ∀ w : W, T.dist c w ≤ 2) :
    SimpleGraph.IsIndContained T (modelTree (max (Fintype.card W) 2)) := by
  classical
  let s := max (Fintype.card W) 2
  have hle_s : Fintype.card W ≤ s := le_max_left _ _
  let eW : W ↪ Fin s := (Fintype.equivFin W).toEmbedding.trans (Fin.castLEEmb hle_s)
  have hconn : T.Connected := hT.connected
  have hdist0 : ∀ w : W, T.dist c w = 0 ↔ w = c := by
    intro w
    rw [hconn.dist_eq_zero_iff, eq_comm]
  have hdist1 : ∀ w : W, T.dist c w = 1 ↔ T.Adj c w := fun _ => T.dist_eq_one_iff_adj
  have hex_parent : ∀ w : W, w ≠ c → ¬ T.Adj c w → ∃ u : W, T.Adj c u ∧ T.Adj u w := by
    intro w hwc hncw
    have hd0 : T.dist c w ≠ 0 := fun h => hwc ((hdist0 w).mp h)
    have hd1 : T.dist c w ≠ 1 := fun h => hncw ((hdist1 w).mp h)
    have hd2 : T.dist c w = 2 := by have := hrad w; omega
    obtain ⟨p, _, hp_len⟩ := hconn.exists_path_of_dist c w
    rw [hd2] at hp_len
    rcases p with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    · simp at hp_len
    · simp at hp_len
    · exact ⟨_, h1, h2⟩
    · simp at hp_len
  have hno_adj_d1 : ∀ u₁ u₂ : W, T.Adj c u₁ → T.Adj c u₂ → ¬ T.Adj u₁ u₂ := by
    intro u₁ u₂ hu₁ hu₂ hu₁₂
    have hne12 : u₁ ≠ u₂ := T.ne_of_adj hu₁₂
    have hcu₁ : c ≠ u₁ := T.ne_of_adj hu₁
    have hcu₂ : c ≠ u₂ := T.ne_of_adj hu₂
    let p₁ : T.Walk c u₂ := Walk.cons hu₂ Walk.nil
    let p₂ : T.Walk c u₂ := Walk.cons hu₁ (Walk.cons hu₁₂ Walk.nil)
    have hp₁ : p₁.IsPath := by
      rw [Walk.isPath_def]; simp [p₁, hcu₂]
    have hp₂ : p₂.IsPath := by
      rw [Walk.isPath_def]; simp [p₂, hcu₁, hcu₂, hne12]
    have heq := (hT.existsUnique_path c u₂).unique hp₁ hp₂
    have hlen := congr_arg Walk.length heq
    simp [p₁, p₂] at hlen
  have huniq_parent : ∀ w u₁ u₂ : W, w ≠ c → ¬ T.Adj c w →
      T.Adj c u₁ → T.Adj u₁ w → T.Adj c u₂ → T.Adj u₂ w → u₁ = u₂ := by
    intro w u₁ u₂ hwc _ hcu₁ hu₁w hcu₂ hu₂w
    let p₁ : T.Walk c w := Walk.cons hcu₁ (Walk.cons hu₁w Walk.nil)
    let p₂ : T.Walk c w := Walk.cons hcu₂ (Walk.cons hu₂w Walk.nil)
    have hp₁ : p₁.IsPath := by
      rw [Walk.isPath_def]
      simp [p₁, T.ne_of_adj hcu₁, hwc.symm, T.ne_of_adj hu₁w]
    have hp₂ : p₂.IsPath := by
      rw [Walk.isPath_def]
      simp [p₂, T.ne_of_adj hcu₂, hwc.symm, T.ne_of_adj hu₂w]
    have heq := (hT.existsUnique_path c w).unique hp₁ hp₂
    have hget := congr_arg (fun q => q.getVert 1) heq
    simpa [p₁, p₂] using hget
  have hno_adj_d2 : ∀ w₁ w₂ : W, w₁ ≠ c → ¬ T.Adj c w₁ → w₂ ≠ c → ¬ T.Adj c w₂ →
      ¬ T.Adj w₁ w₂ := by
    intro w₁ w₂ hw₁c hncw₁ hw₂c hncw₂ hw₁₂
    obtain ⟨u₁, hcu₁, hu₁w₁⟩ := hex_parent w₁ hw₁c hncw₁
    obtain ⟨u₂, hcu₂, hu₂w₂⟩ := hex_parent w₂ hw₂c hncw₂
    let p₁ : T.Walk c w₂ := Walk.cons hcu₂ (Walk.cons hu₂w₂ Walk.nil)
    let p₂ : T.Walk c w₂ := Walk.cons hcu₁ (Walk.cons hu₁w₁ (Walk.cons hw₁₂ Walk.nil))
    have hp₁ : p₁.IsPath := by
      rw [Walk.isPath_def]
      simp [p₁, T.ne_of_adj hcu₂, hw₂c.symm, T.ne_of_adj hu₂w₂]
    have hp₂ : p₂.IsPath := by
      rw [Walk.isPath_def]
      have hu₁w₂ : u₁ ≠ w₂ := fun h => hncw₂ (h ▸ hcu₁)
      simp [p₂, T.ne_of_adj hcu₁, hw₁c.symm, hw₂c.symm, T.ne_of_adj hu₁w₁, hu₁w₂,
        T.ne_of_adj hw₁₂]
    have heq := (hT.existsUnique_path c w₂).unique hp₁ hp₂
    have hlen := congr_arg Walk.length heq
    simp [p₁, p₂] at hlen
  let ψ : W → RadTwoVert s := fun w =>
    if hwc : w = c then
      Sum.inl ()
    else if hcw : T.Adj c w then
      Sum.inr (Sum.inl (eW w))
    else
      Sum.inr (Sum.inr (eW (Classical.choose (hex_parent w hwc hcw)), eW w))
  have hψ_root : ψ c = Sum.inl () := by
    dsimp [ψ]; rw [dif_pos rfl]
  have hψ_d1 : ∀ w : W, T.Adj c w → ψ w = Sum.inr (Sum.inl (eW w)) := by
    intro w hcw
    have hwc : w ≠ c := (T.ne_of_adj hcw).symm
    dsimp [ψ]; rw [dif_neg hwc, dif_pos hcw]
  have hψ_d2 : ∀ (w : W) (hwc : w ≠ c) (hncw : ¬ T.Adj c w),
      ψ w = Sum.inr (Sum.inr (eW (Classical.choose (hex_parent w hwc hncw)), eW w)) := by
    intro w hwc hncw
    dsimp [ψ]; rw [dif_neg hwc, dif_neg hncw]
  have hinj : Function.Injective ψ := by
    intro x y hxy
    by_cases hxc : x = c
    · rw [hxc, hψ_root] at hxy
      by_cases hyc : y = c
      · exact hxc.trans hyc.symm
      · by_cases hcy : T.Adj c y
        · rw [hψ_d1 y hcy] at hxy; cases hxy
        · rw [hψ_d2 y hyc hcy] at hxy; cases hxy
    · by_cases hcx : T.Adj c x
      · rw [hψ_d1 x hcx] at hxy
        by_cases hyc : y = c
        · rw [hyc, hψ_root] at hxy; cases hxy
        · by_cases hcy : T.Adj c y
          · rw [hψ_d1 y hcy] at hxy
            exact eW.injective (Sum.inl.inj (Sum.inr.inj hxy))
          · rw [hψ_d2 y hyc hcy] at hxy; cases hxy
      · rw [hψ_d2 x hxc hcx] at hxy
        by_cases hyc : y = c
        · rw [hyc, hψ_root] at hxy; cases hxy
        · by_cases hcy : T.Adj c y
          · rw [hψ_d1 y hcy] at hxy; cases hxy
          · rw [hψ_d2 y hyc hcy] at hxy
            exact eW.injective (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hxy))).2
  refine ⟨⟨⟨ψ, hinj⟩, ?_⟩⟩
  intro x y
  change (modelTree s).Adj (ψ x) (ψ y) ↔ T.Adj x y
  by_cases hxc : x = c
  · rw [hxc, hψ_root]
    by_cases hyc : y = c
    · rw [hyc, hψ_root]; simp [modelTree]
    · by_cases hcy : T.Adj c y
      · rw [hψ_d1 y hcy]; simp [modelTree, modelTreeAdj, hcy]
      · rw [hψ_d2 y hyc hcy]; simp [modelTree, modelTreeAdj, hcy]
  · by_cases hcx : T.Adj c x
    · rw [hψ_d1 x hcx]
      by_cases hyc : y = c
      · rw [hyc, hψ_root]; simp [modelTree, modelTreeAdj, hcx.symm]
      · by_cases hcy : T.Adj c y
        · rw [hψ_d1 y hcy]; simp [modelTree, modelTreeAdj, hno_adj_d1 x y hcx hcy]
        · rw [hψ_d2 y hyc hcy]
          have hu_spec := Classical.choose_spec (hex_parent y hyc hcy)
          simp only [modelTree, modelTreeAdj, EmbeddingLike.apply_eq_iff_eq]
          constructor
          · rintro rfl; exact hu_spec.2
          · intro hxy; exact huniq_parent y x _ hyc hcy hcx hxy hu_spec.1 hu_spec.2
    · rw [hψ_d2 x hxc hcx]
      by_cases hyc : y = c
      · rw [hyc, hψ_root]
        have hncx : ¬ T.Adj x c := fun h => hcx h.symm
        simp [modelTree, modelTreeAdj, hncx]
      · by_cases hcy : T.Adj c y
        · rw [hψ_d1 y hcy]
          have hu_spec := Classical.choose_spec (hex_parent x hxc hcx)
          simp only [modelTree, modelTreeAdj, EmbeddingLike.apply_eq_iff_eq]
          constructor
          · rintro rfl; exact hu_spec.2.symm
          · intro hxy; exact huniq_parent x y _ hxc hcx hcy hxy.symm hu_spec.1 hu_spec.2
        · rw [hψ_d2 y hyc hcy]
          simp [modelTree, modelTreeAdj, hno_adj_d2 x y hxc hcx hyc hcy]

/- ## Section 3: Biclique-Free Base Case (Rodl Leaf-Peeling) -/

private def HasCore {V : Type*} (G : SimpleGraph V) (U : Finset V) (d w : ℕ) : Prop :=
  ∃ A : Fin d → Finset V,
    (∀ p, A p ⊆ U) ∧
    (∀ p, (A p).card = w) ∧
    (∀ p q, p ≠ q → Disjoint (A p) (A q)) ∧
    (∀ p q, p ≠ q → ∀ u ∈ A p, ∀ v ∈ A q, G.Adj u v)

private lemma hasCore_mono {V : Type*} {G : SimpleGraph V} {U₁ U₂ : Finset V} {d w : ℕ}
    (hsub : U₁ ⊆ U₂) (h : HasCore G U₁ d w) : HasCore G U₂ d w := by
  obtain ⟨A, hAU, hAc, hAd, hAadj⟩ := h
  exact ⟨A, fun p => (hAU p).trans hsub, hAc, hAd, hAadj⟩

private def enumVert (s : ℕ) (hs : 1 ≤ s) (k : Fin (1 + s + s * s)) : RadTwoVert s :=
  if h0 : k.val = 0 then
    Sum.inl ()
  else if h1 : k.val ≤ s then
    Sum.inr (Sum.inl ⟨k.val - 1, by omega⟩)
  else
    Sum.inr (Sum.inr (⟨(k.val - (1 + s)) / s,
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := k.isLt; omega)⟩,
      ⟨(k.val - (1 + s)) % s, Nat.mod_lt _ (by omega)⟩))

private lemma enumVert_zero {s : ℕ} (hs : 1 ≤ s) {k : Fin (1 + s + s * s)} (h0 : k.val = 0) :
    enumVert s hs k = Sum.inl () := by
  unfold enumVert
  rw [dif_pos h0]

private lemma enumVert_d1 {s : ℕ} (hs : 1 ≤ s) {k : Fin (1 + s + s * s)}
    (h0 : k.val ≠ 0) (h1 : k.val ≤ s) :
    enumVert s hs k = Sum.inr (Sum.inl ⟨k.val - 1, by omega⟩) := by
  unfold enumVert
  rw [dif_neg h0, dif_pos h1]

private lemma enumVert_d2 {s : ℕ} (hs : 1 ≤ s) {k : Fin (1 + s + s * s)} (h1 : ¬ k.val ≤ s) :
    enumVert s hs k = Sum.inr (Sum.inr (⟨(k.val - (1 + s)) / s,
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by have := k.isLt; omega)⟩,
      ⟨(k.val - (1 + s)) % s, Nat.mod_lt _ (by omega)⟩)) := by
  have h0 : k.val ≠ 0 := by omega
  unfold enumVert
  rw [dif_neg h0, dif_neg h1]

private def parentIdx (s : ℕ) (hs : 1 ≤ s) (m : ℕ) (hm : m + 1 < 1 + s + s * s) : Fin (m + 1) :=
  if _ : m + 1 ≤ s then
    ⟨0, by omega⟩
  else
    ⟨1 + ((m + 1) - (1 + s)) / s, by
      have hdiv : ((m + 1) - (1 + s)) / s < s := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega⟩

private lemma parentIdx_spec (s : ℕ) (hs : 1 ≤ s) (m : ℕ) (hm : m + 1 < 1 + s + s * s)
    (x : Fin (m + 1)) :
    (modelTree s).Adj (enumVert s hs ⟨x.val, by omega⟩) (enumVert s hs ⟨m + 1, hm⟩) ↔
      x = parentIdx s hs m hm := by
  have hm0 : (⟨m + 1, hm⟩ : Fin (1 + s + s * s)).val ≠ 0 := by dsimp; omega
  by_cases hms : m + 1 ≤ s
  · unfold parentIdx
    rw [dif_pos hms, enumVert_d1 hs hm0 hms]
    by_cases hx0 : x.val = 0
    · rw [enumVert_zero hs hx0]
      have hxeq : x = ⟨0, by omega⟩ := Fin.ext hx0
      simp [modelTree, modelTreeAdj, hxeq]
    · have hxs : x.val ≤ s := by omega
      rw [enumVert_d1 hs hx0 hxs]
      have hxne : x ≠ ⟨0, by omega⟩ := fun h => hx0 (congr_arg Fin.val h)
      exact ⟨False.elim, fun h => absurd h hxne⟩
  · unfold parentIdx
    have hm_d2 : enumVert s hs ⟨m + 1, hm⟩ = Sum.inr (Sum.inr (⟨((m + 1) - (1 + s)) / s,
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩,
        ⟨((m + 1) - (1 + s)) % s, Nat.mod_lt _ (by omega)⟩)) :=
      enumVert_d2 (k := ⟨m + 1, hm⟩) hs hms
    rw [dif_neg hms, hm_d2]
    have hdiv_lt : ((m + 1) - (1 + s)) / s < s :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    by_cases hx0 : x.val = 0
    · rw [enumVert_zero hs hx0]
      have hxne : x ≠ ⟨1 + ((m + 1) - (1 + s)) / s, by omega⟩ := by
        intro h
        have hval : x.val = 1 + ((m + 1) - (1 + s)) / s := congr_arg Fin.val h
        rw [hx0, Nat.add_comm] at hval
        exact Nat.succ_ne_zero _ hval.symm
      exact ⟨False.elim, fun h => absurd h hxne⟩
    · by_cases hxs : x.val ≤ s
      · rw [enumVert_d1 hs hx0 hxs]
        simp only [modelTree, modelTreeAdj, Fin.ext_iff]
        omega
      · rw [enumVert_d2 hs hxs]
        have hxne : x ≠ ⟨1 + ((m + 1) - (1 + s)) / s, by omega⟩ := by
          intro h; have := congr_arg Fin.val h; dsimp at this; omega
        exact ⟨False.elim, fun h => absurd h hxne⟩

private def HasPartialModel {V : Type*} (G : SimpleGraph V) (S : Finset V) (s : ℕ) (hs : 1 ≤ s)
    (k : ℕ) (hk : k ≤ 1 + s + s * s) : Prop :=
  ∃ f : Fin k → V,
    Function.Injective f ∧
    (∀ x : Fin k, f x ∈ S) ∧
    ∀ x y : Fin k, G.Adj (f x) (f y) ↔
      (modelTree s).Adj (enumVert s hs ⟨x.val, by omega⟩) (enumVert s hs ⟨y.val, by omega⟩)

private lemma hasPartialModel_mono {V : Type*} {G : SimpleGraph V} {S₁ S₂ : Finset V}
    {s : ℕ} {hs : 1 ≤ s} {k : ℕ} {hk : k ≤ 1 + s + s * s}
    (hsub : S₁ ⊆ S₂) (h : HasPartialModel G S₁ s hs k hk) :
    HasPartialModel G S₂ s hs k hk := by
  obtain ⟨f, hinj, hmem, hadj⟩ := h
  exact ⟨f, hinj, fun x => hsub (hmem x), hadj⟩

private lemma hasModelTreeOn_of_fullPartialModel {V : Type*} {G : SimpleGraph V} {S : Finset V}
    {s : ℕ} (hs : 1 ≤ s) (h : HasPartialModel G S s hs (1 + s + s * s) le_rfl) :
    HasModelTreeOn G S s := by
  obtain ⟨f, hinj, hmem, hadj⟩ := h
  let idxR : Fin (1 + s + s * s) := ⟨0, by omega⟩
  let idxA : Fin s → Fin (1 + s + s * s) := fun i => ⟨1 + i.val, by omega⟩
  let idxB : Fin s → Fin s → Fin (1 + s + s * s) := fun i j =>
    ⟨1 + s + i.val * s + j.val, by nlinarith [i.isLt, j.isLt]⟩
  have heR : enumVert s hs ⟨idxR.val, by omega⟩ = Sum.inl () :=
    enumVert_zero hs rfl
  have heA : ∀ i : Fin s, enumVert s hs ⟨(idxA i).val, by omega⟩ = Sum.inr (Sum.inl i) := by
    intro i
    rw [enumVert_d1 hs (by dsimp [idxA]; omega) (by dsimp [idxA]; omega)]
    congr 2; ext; dsimp [idxA]; omega
  have heB : ∀ i j : Fin s,
      enumVert s hs ⟨(idxB i j).val, by omega⟩ = Sum.inr (Sum.inr (i, j)) := by
    intro i j
    rw [enumVert_d2 hs (by dsimp [idxB]; omega)]
    have hsub : (idxB i j).val - (1 + s) = i.val * s + j.val := by dsimp [idxB]; omega
    have hdiv : ((idxB i j).val - (1 + s)) / s = i.val := by
      rw [hsub, mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_zero_iff.mpr (Or.inr j.isLt),
        add_zero]
    have hmod : ((idxB i j).val - (1 + s)) % s = j.val := by
      rw [hsub, mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
    congr 2
    exact Prod.ext (Fin.ext hdiv) (Fin.ext hmod)
  refine ⟨f idxR, fun i => f (idxA i), fun i j => f (idxB i j),
    hmem idxR, fun i => hmem (idxA i), fun i j => hmem (idxB i j), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j j' hjj' heq
    have hidx := congr_arg Fin.val (hinj heq)
    dsimp [idxB] at hidx
    exact hjj' (Fin.ext (by omega))
  · intro i
    rw [hadj idxR (idxA i), heR, heA i]
    trivial
  · intro i j
    rw [hadj idxR (idxB i j), heR, heB i j]
    simp [modelTree, modelTreeAdj]
  · intro i j _
    rw [hadj (idxA i) (idxA j), heA i, heA j]
    simp [modelTree, modelTreeAdj]
  · intro i i' j
    rw [hadj (idxA i) (idxB i' j), heA i, heB i' j]
    simp [modelTree, modelTreeAdj]
  · intro i j i' j' _
    rw [hadj (idxB i j) (idxB i' j'), heB i j, heB i' j']
    simp [modelTree, modelTreeAdj]

private lemma exists_max_disjoint_family {V : Type*} [DecidableEq V] (P : Finset V → Prop)
    (bound : ℕ)
    (hno : ¬ ∃ X : Fin (bound + 1) → Finset V,
      (∀ a b, a ≠ b → Disjoint (X a) (X b)) ∧ ∀ a, P (X a)) :
    ∃ r ≤ bound, ∃ X : Fin r → Finset V,
      (∀ a b, a ≠ b → Disjoint (X a) (X b)) ∧
      (∀ a, P (X a)) ∧
      ∀ Z : Finset V, P Z → ¬ Disjoint Z (Finset.univ.biUnion X) := by
  induction bound with
  | zero =>
    refine ⟨0, le_rfl, Fin.elim0, fun a => a.elim0, fun a => a.elim0, ?_⟩
    intro Z hPZ _
    exact hno ⟨fun _ => Z, fun a b hab => absurd (Fin.ext (by omega)) hab, fun _ => hPZ⟩
  | succ bound ih =>
    by_cases hex : ∃ X : Fin (bound + 1) → Finset V,
        (∀ a b, a ≠ b → Disjoint (X a) (X b)) ∧ ∀ a, P (X a)
    · obtain ⟨X, hdisj, hP⟩ := hex
      refine ⟨bound + 1, le_rfl, X, hdisj, hP, ?_⟩
      intro Z hPZ hZdisj
      apply hno
      let X' : Fin (bound + 2) → Finset V := Fin.snoc X Z
      refine ⟨X', ?_, ?_⟩
      · intro a b hab
        induction a using Fin.lastCases with
        | last =>
          induction b using Fin.lastCases with
          | last => exact absurd rfl hab
          | cast b₀ =>
            simp only [X', Fin.snoc_last, Fin.snoc_castSucc]
            exact Finset.disjoint_left.mpr fun x hxZ hxXb =>
              Finset.disjoint_left.mp hZdisj hxZ
                (Finset.mem_biUnion.mpr ⟨b₀, Finset.mem_univ _, hxXb⟩)
        | cast a₀ =>
          induction b using Fin.lastCases with
          | last =>
            simp only [X', Fin.snoc_last, Fin.snoc_castSucc]
            exact (Finset.disjoint_left.mpr fun x hxZ hxXa =>
              Finset.disjoint_left.mp hZdisj hxZ
                (Finset.mem_biUnion.mpr ⟨a₀, Finset.mem_univ _, hxXa⟩)).symm
          | cast b₀ =>
            simp only [X', Fin.snoc_castSucc]
            exact hdisj a₀ b₀ (fun h => hab (congr_arg Fin.castSucc h))
      · intro a
        induction a using Fin.lastCases with
        | last => simpa [X'] using hPZ
        | cast a₀ => simpa [X'] using hP a₀
    · obtain ⟨r, hr, X, hdisj, hP, hmax⟩ := ih hex
      exact ⟨r, by omega, X, hdisj, hP, hmax⟩

private def rodlStepBound (t k cPrev : ℕ) : ℕ :=
  max (t * k + t * k ^ (t - 1)) ((2 * ((t - 2) * k) + 1) * cPrev)

private def rodlPartialBound (t : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => rodlStepBound t (m + 1) (rodlPartialBound t m)

private lemma colorableOn_of_no_partialModel_bicliqueFree {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ} (hs : 1 ≤ s) {t : ℕ} (ht : 1 ≤ t)
    (m : ℕ) : ∀ (hm : m + 2 ≤ 1 + s + s * s) (S : Finset V),
      ¬ HasCore G S 2 t →
      ¬ HasPartialModel G S s hs (m + 2) hm →
      ColorableOn G S (rodlPartialBound t m) := by
  induction m with
  | zero =>
    intro hm S _ hno2
    refine colorableOn_edgeless fun u hu v hv huv => hno2 ?_
    have hne : u ≠ v := G.ne_of_adj huv
    let f : Fin 2 → V := ![u, v]
    have hf_inj : Function.Injective f := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab hne
      · exact absurd hab hne.symm
      · rfl
    refine ⟨f, hf_inj, ?_, ?_⟩
    · intro x; fin_cases x <;> simp [f, hu, hv]
    · intro x y
      fin_cases x <;> fin_cases y
      · simp
      · change G.Adj u v ↔
          (modelTree s).Adj (enumVert s hs ⟨0, by omega⟩) (enumVert s hs ⟨1, by omega⟩)
        rw [enumVert_zero (k := ⟨0, by omega⟩) hs rfl,
          enumVert_d1 (k := ⟨1, by omega⟩) hs (by simp) hs]
        simp [huv, modelTree, modelTreeAdj]
      · change G.Adj v u ↔
          (modelTree s).Adj (enumVert s hs ⟨1, by omega⟩) (enumVert s hs ⟨0, by omega⟩)
        rw [enumVert_d1 (k := ⟨1, by omega⟩) hs (by simp) hs,
          enumVert_zero (k := ⟨0, by omega⟩) hs rfl]
        simp [huv.symm, modelTree, modelTreeAdj]
      · simp
  | succ m ihm =>
    intro hm S hnoCore hnoNext
    let k := m + 1
    have hk_pos : 1 ≤ k := Nat.le_add_left 1 m
    let cPrev := rodlPartialBound t m
    let cNext := rodlStepBound t k cPrev
    change ColorableOn G S cNext
    by_cases ht1 : t = 1
    · subst ht1
      have hc1 : 1 ≤ cNext := by
        dsimp [cNext, rodlStepBound]
        omega
      refine colorableOn_mono_num hc1 (colorableOn_edgeless fun u hu v hv huv => hnoCore ?_)
      have hne : u ≠ v := G.ne_of_adj huv
      refine ⟨![{u}, {v}], ?_, ?_, ?_, ?_⟩
      · intro p; fin_cases p <;> simp [hu, hv]
      · intro p; fin_cases p <;> simp
      · intro p q hpq
        fin_cases p <;> fin_cases q
        · exact absurd rfl hpq
        · simp [hne]
        · simp [hne.symm]
        · exact absurd rfl hpq
      · intro p q hpq x hx y hy
        fin_cases p <;> fin_cases q
        · exact absurd rfl hpq
        · simp at hx hy; subst hx; subst hy; exact huv
        · simp at hx hy; subst hx; subst hy; exact huv.symm
        · exact absurd rfl hpq
    · have ht2 : 2 ≤ t := by omega
      have haux : ∀ n : ℕ, ∀ S' : Finset V, S'.card ≤ n → S' ⊆ S → ColorableOn G S' cNext := by
        intro n
        induction n with
        | zero =>
          intro S' hcard _
          rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]
          exact colorableOn_empty G cNext
        | succ n ih =>
          intro S' hcard hS'S
          by_cases hlow : ∃ v ∈ S', (S'.filter (G.Adj v)).card < cNext
          · obtain ⟨v, hvS', hvdeg⟩ := hlow
            have hcard_er : (S'.erase v).card ≤ n := by
              have := Finset.card_erase_of_mem hvS'
              have : 0 < S'.card := Finset.card_pos.mpr ⟨v, hvS'⟩
              omega
            have hcol_er := ih (S'.erase v) hcard_er ((Finset.erase_subset _ _).trans hS'S)
            have hvdeg_er : ((S'.erase v).filter (G.Adj v)).card < cNext := by
              refine lt_of_le_of_lt (Finset.card_le_card ?_) hvdeg
              intro z hz
              obtain ⟨hzE, hzv⟩ := Finset.mem_filter.mp hz
              exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hzE).2, hzv⟩
            have hins := colorableOn_insert_of_deg_lt hcol_er hvdeg_er
            rwa [Finset.insert_erase hvS'] at hins
          · simp only [not_exists, not_and, not_lt] at hlow
            let q : Fin (k + 1) := parentIdx s hs k (by omega)
            let IsBag : V → Finset V → Prop := fun v X =>
              X ⊆ S'.erase v ∧ X.card = k ∧
              ∃ f : Fin (k + 1) → V,
                Function.Injective f ∧
                (∀ x, f x ∈ S') ∧
                (∀ x y : Fin (k + 1), G.Adj (f x) (f y) ↔
                  (modelTree s).Adj (enumVert s hs ⟨x.val, by omega⟩)
                    (enumVert s hs ⟨y.val, by omega⟩)) ∧
                f q = v ∧
                (Finset.univ.erase q).image f = X
            have hbag_hit : ∀ v ∈ S', ∀ X : Finset V, IsBag v X →
                ∀ u ∈ S'.filter (G.Adj v), u ∉ X → ∃ z ∈ X, G.Adj z u := by
              intro v _ X ⟨_, _, f, hfinj, hfmem, hfadj, hfq, hfX⟩ u huN huX
              by_contra hno_z
              simp only [not_exists, not_and] at hno_z
              apply hnoNext
              refine hasPartialModel_mono hS'S ?_
              let f' : Fin (k + 2) → V := fun x =>
                if hx : x.val < k + 1 then f ⟨x.val, hx⟩ else u
              have huS' : u ∈ S' := (Finset.mem_filter.mp huN).1
              have hvu : G.Adj v u := (Finset.mem_filter.mp huN).2
              have hu_ne_v : u ≠ v := (G.ne_of_adj hvu).symm
              have hu_ne_f : ∀ x : Fin (k + 1), f x ≠ u := by
                intro x heq
                by_cases hxq : x = q
                · subst hxq; exact hu_ne_v (heq.symm.trans hfq)
                · exact huX (hfX ▸ Finset.mem_image.mpr
                    ⟨x, Finset.mem_erase.mpr ⟨hxq, Finset.mem_univ _⟩, heq⟩)
              refine ⟨f', ?_, ?_, ?_⟩
              · intro a b hab
                dsimp [f'] at hab
                split_ifs at hab with ha hb hb
                · have hval := congr_arg Fin.val (hfinj hab)
                  dsimp at hval
                  exact Fin.ext hval
                · exact absurd hab (hu_ne_f _)
                · exact absurd hab.symm (hu_ne_f _)
                · exact Fin.ext (by omega)
              · intro x
                dsimp [f']
                split_ifs with hx
                · exact hfmem ⟨x.val, hx⟩
                · exact huS'
              · intro a b
                dsimp [f']
                split_ifs with ha hb hb
                · exact hfadj ⟨a.val, ha⟩ ⟨b.val, hb⟩
                · have hb_eq : b.val = k + 1 := by omega
                  have he_b : (⟨b.val, by omega⟩ : Fin (1 + s + s * s)) = ⟨k + 1, hm⟩ :=
                    Fin.ext hb_eq
                  rw [he_b, parentIdx_spec s hs k (by omega) ⟨a.val, ha⟩]
                  constructor
                  · intro hadj_au
                    by_contra hneq
                    have haX : f ⟨a.val, ha⟩ ∈ X :=
                      hfX ▸ Finset.mem_image.mpr
                        ⟨⟨a.val, ha⟩, Finset.mem_erase.mpr ⟨hneq, Finset.mem_univ _⟩, rfl⟩
                    exact hno_z _ haX hadj_au
                  · intro heq_q
                    rw [heq_q, hfq]
                    exact hvu
                · have ha_eq : a.val = k + 1 := by omega
                  have he_a : (⟨a.val, by omega⟩ : Fin (1 + s + s * s)) = ⟨k + 1, hm⟩ :=
                    Fin.ext ha_eq
                  rw [he_a, adj_comm, (modelTree s).adj_comm,
                    parentIdx_spec s hs k (by omega) ⟨b.val, hb⟩]
                  constructor
                  · intro hadj_bu
                    by_contra hneq
                    have hbX : f ⟨b.val, hb⟩ ∈ X :=
                      hfX ▸ Finset.mem_image.mpr
                        ⟨⟨b.val, hb⟩, Finset.mem_erase.mpr ⟨hneq, Finset.mem_univ _⟩, rfl⟩
                    exact hno_z _ hbX hadj_bu
                  · intro heq_q
                    rw [heq_q, hfq]
                    exact hvu
                · have hab_eq : (⟨a.val, by omega⟩ : Fin (1 + s + s * s)) = ⟨b.val, by omega⟩ :=
                    Fin.ext (by dsimp; omega)
                  rw [hab_eq]
                  simp
            have hno_t_minus_1 : ∀ v ∈ S', ¬ ∃ X : Fin (t - 1) → Finset V,
                (∀ a b, a ≠ b → Disjoint (X a) (X b)) ∧ ∀ a, IsBag v (X a) := by
              intro v hvS' ⟨X, hXdisj, hXbag⟩
              let U_bags := Finset.univ.biUnion X
              have hU_card : U_bags.card ≤ (t - 1) * k := by
                calc U_bags.card
                    ≤ ∑ a : Fin (t - 1), (X a).card := Finset.card_biUnion_le
                  _ = ∑ _a : Fin (t - 1), k := Finset.sum_congr rfl fun a _ => (hXbag a).2.1
                  _ = (t - 1) * k := by simp
              let Nv := S'.filter (G.Adj v)
              let remN := Nv \ U_bags
              have hex_nb : ∀ u : {x // x ∈ remN}, ∀ a : Fin (t - 1),
                  ∃ z : {y // y ∈ X a}, G.Adj z.1 u.1 := by
                intro ⟨u, hu⟩ a
                obtain ⟨huNv, huNotU⟩ := Finset.mem_sdiff.mp hu
                have huNotXa : u ∉ X a := fun h =>
                  huNotU (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, h⟩)
                obtain ⟨z, hzXa, hzu⟩ := hbag_hit v hvS' (X a) (hXbag a) u huNv huNotXa
                exact ⟨⟨z, hzXa⟩, hzu⟩
              classical
              choose φ hφ using fun (u : {x // x ∈ remN}) (a : Fin (t - 1)) => hex_nb u a
              let Tup := ∀ a : Fin (t - 1), {y // y ∈ X a}
              have hTup_card : Fintype.card Tup = k ^ (t - 1) := by
                dsimp [Tup]
                rw [Fintype.card_pi]
                calc ∏ a : Fin (t - 1), Fintype.card {y // y ∈ X a}
                    = ∏ a : Fin (t - 1), (X a).card :=
                      Finset.prod_congr rfl fun a _ => Fintype.card_coe (X a)
                  _ = ∏ _a : Fin (t - 1), k := Finset.prod_congr rfl fun a _ => (hXbag a).2.1
                  _ = k ^ (t - 1) := by simp
              have hfiber_lt : ∀ g : Tup,
                  (Finset.univ.filter (fun u : {x // x ∈ remN} => φ u = g)).card ≤ t - 1 := by
                intro g
                by_contra hge
                have hgt : t ≤ (Finset.univ.filter (fun u : {x // x ∈ remN} => φ u = g)).card :=
                  by omega
                obtain ⟨Bsub, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hgt
                let B₀ : Finset V := Bsub.image Subtype.val
                have hB₀_card : B₀.card = t := by
                  rw [Finset.card_image_of_injective _ Subtype.val_injective, hBcard]
                let imgG : Finset V := Finset.univ.image (fun a : Fin (t - 1) => (g a).1)
                have himgG_card : imgG.card = t - 1 := by
                  rw [Finset.card_image_of_injective]
                  · simp
                  · intro a b hab
                    dsimp at hab
                    by_contra hne
                    have hga_in_b : (g a).1 ∈ X b := by rw [hab]; exact (g b).2
                    exact Finset.disjoint_left.mp (hXdisj a b hne) (g a).2 hga_in_b
                have hv_not_imgG : v ∉ imgG := by
                  intro hvi
                  obtain ⟨a, _, hva⟩ := Finset.mem_image.mp hvi
                  exact (Finset.mem_erase.mp ((hXbag a).1 (g a).2)).1 hva
                let A₀ : Finset V := insert v imgG
                have hA₀_card : A₀.card = t := by
                  rw [Finset.card_insert_of_notMem hv_not_imgG, himgG_card]
                  omega
                have hA₀S : A₀ ⊆ S := by
                  refine Finset.insert_subset_iff.mpr ⟨hS'S hvS', ?_⟩
                  intro x hx
                  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
                  exact hS'S ((Finset.mem_erase.mp ((hXbag a).1 (g a).2)).2)
                have hB₀S : B₀ ⊆ S := by
                  intro x hx
                  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
                  exact hS'S (Finset.mem_filter.mp (Finset.mem_sdiff.mp u.2).1).1
                have hAB_adj : ∀ x ∈ A₀, ∀ y ∈ B₀, G.Adj x y := by
                  intro x hx y hy
                  obtain ⟨u, huB, rfl⟩ := Finset.mem_image.mp hy
                  have hφu : φ u = g := (Finset.mem_filter.mp (hBsub huB)).2
                  rcases Finset.mem_insert.mp hx with rfl | hxI
                  · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp u.2).1).2
                  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxI
                    rw [← hφu]
                    exact hφ u a
                have hAB_disj : Disjoint A₀ B₀ :=
                  Finset.disjoint_left.mpr fun x hxA hxB =>
                    G.loopless.irrefl x (hAB_adj x hxA x hxB)
                apply hnoCore
                refine ⟨![A₀, B₀], ?_, ?_, ?_, ?_⟩
                · intro p; fin_cases p <;> simp [hA₀S, hB₀S]
                · intro p; fin_cases p <;> simp [hA₀_card, hB₀_card]
                · intro p q hpq
                  fin_cases p <;> fin_cases q
                  · exact absurd rfl hpq
                  · exact hAB_disj
                  · exact hAB_disj.symm
                  · exact absurd rfl hpq
                · intro p q hpq x hx y hy
                  fin_cases p <;> fin_cases q
                  · exact absurd rfl hpq
                  · exact hAB_adj x hx y hy
                  · exact (hAB_adj y hy x hx).symm
                  · exact absurd rfl hpq
              have hrem_card : remN.card ≤ k ^ (t - 1) * (t - 1) := by
                have h1 : remN.card = (Finset.univ : Finset {x // x ∈ remN}).card := by
                  rw [Finset.card_univ, Fintype.card_coe]
                have h2 : (Finset.univ : Finset {x // x ∈ remN}).card =
                    ∑ g : Tup, (Finset.univ.filter (fun u : {x // x ∈ remN} => φ u = g)).card :=
                  Finset.card_eq_sum_card_fiberwise (fun u _ => Finset.mem_univ (φ u))
                rw [h1, h2]
                calc ∑ g : Tup, (Finset.univ.filter (fun u : {x // x ∈ remN} => φ u = g)).card
                    ≤ ∑ _g : Tup, (t - 1) := Finset.sum_le_sum fun g _ => hfiber_lt g
                  _ = Fintype.card Tup * (t - 1) := by simp
                  _ = k ^ (t - 1) * (t - 1) := by rw [hTup_card]
              have hNv_le : Nv.card ≤ (t - 1) * k + (t - 1) * k ^ (t - 1) := by
                have hsub_u : Nv ⊆ U_bags ∪ remN := fun x hx => by
                  by_cases hxU : x ∈ U_bags
                  · exact Finset.mem_union_left _ hxU
                  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxU⟩)
                have hc := (Finset.card_le_card hsub_u).trans (Finset.card_union_le _ _)
                have hcomm : k ^ (t - 1) * (t - 1) = (t - 1) * k ^ (t - 1) := mul_comm _ _
                omega
              have hNv_ge : t * k + t * k ^ (t - 1) ≤ Nv.card :=
                le_trans (le_max_left _ _) (hlow v hvS')
              have hkpow_pos : 1 ≤ k ^ (t - 1) := Nat.one_le_pow _ _ hk_pos
              have hlt1 : (t - 1) * k < t * k := by
                have : t * k = (t - 1) * k + k := by
                  calc t * k = ((t - 1) + 1) * k := by congr 1; omega
                    _ = (t - 1) * k + k := by ring
                omega
              have hle2 : (t - 1) * k ^ (t - 1) ≤ t * k ^ (t - 1) :=
                Nat.mul_le_mul_right _ (by omega)
              omega
            have hex_Yv : ∀ v ∈ S', ∃ Yv : Finset V,
                Yv.card ≤ (t - 2) * k ∧ ∀ X : Finset V, IsBag v X → ¬ Disjoint X Yv := by
              intro v hvS'
              have hno_bound : ¬ ∃ X : Fin ((t - 2) + 1) → Finset V,
                  (∀ a b, a ≠ b → Disjoint (X a) (X b)) ∧ ∀ a, IsBag v (X a) := by
                have heq_t : (t - 2) + 1 = t - 1 := by omega
                rw [heq_t]
                exact hno_t_minus_1 v hvS'
              obtain ⟨r, hr, X, _, hXbag, hhit⟩ :=
                exists_max_disjoint_family (IsBag v) (t - 2) hno_bound
              refine ⟨Finset.univ.biUnion X, ?_, hhit⟩
              calc (Finset.univ.biUnion X).card
                  ≤ ∑ a : Fin r, (X a).card := Finset.card_biUnion_le
                _ = ∑ _a : Fin r, k := Finset.sum_congr rfl fun a _ => (hXbag a).2.1
                _ = r * k := by simp
                _ ≤ (t - 2) * k := Nat.mul_le_mul_right k hr
            classical
            let Yv : V → Finset V := fun v =>
              if hv : v ∈ S' then Classical.choose (hex_Yv v hv) else ∅
            let D : V → V → Prop := fun v y => y ∈ Yv v
            have hout_D : ∀ v ∈ S', (S'.filter (fun y => y ≠ v ∧ D v y)).card ≤ (t - 2) * k := by
              intro v hvS'
              have hspec := Classical.choose_spec (hex_Yv v hvS')
              refine le_trans (Finset.card_le_card ?_) hspec.1
              intro y hy
              obtain ⟨_, _, hyYv⟩ := Finset.mem_filter.mp hy
              simpa [D, Yv, hvS'] using hyYv
            have hind_D : ∀ Z ⊆ S', (∀ u ∈ Z, ∀ w ∈ Z, u ≠ w → ¬ D u w) →
                ColorableOn G (Z.biUnion (fun x => ({x} : Finset V))) cPrev := by
              intro Z hZS' hZind
              have hbi : Z.biUnion (fun x => ({x} : Finset V)) = Z := by
                ext x; simp
              rw [hbi]
              refine ihm (by omega) Z
                (fun hc => hnoCore (hasCore_mono (hZS'.trans hS'S) hc)) ?_
              rintro ⟨f, hfinj, hfZ, hfadj⟩
              let v := f q
              have hvZ : v ∈ Z := hfZ q
              have hvS' : v ∈ S' := hZS' hvZ
              let X := (Finset.univ.erase q).image f
              have hXbag_v : IsBag v X := by
                refine ⟨?_, ?_, f, hfinj, fun x => hZS' (hfZ x), hfadj, rfl, rfl⟩
                · intro y hy
                  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
                  have hxq : x ≠ q := (Finset.mem_erase.mp hx).1
                  exact Finset.mem_erase.mpr ⟨fun h => hxq (hfinj h), hZS' (hfZ x)⟩
                · rw [Finset.card_image_of_injective _ hfinj,
                    Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, Fintype.card_fin]
                  omega
              have hspec := Classical.choose_spec (hex_Yv v hvS')
              have hnot_disj := hspec.2 X hXbag_v
              rw [Finset.not_disjoint_iff] at hnot_disj
              obtain ⟨y, hyX, hyYv⟩ := hnot_disj
              obtain ⟨x, hx_er, rfl⟩ := Finset.mem_image.mp hyX
              have hxq : x ≠ q := (Finset.mem_erase.mp hx_er).1
              have hne_vx : v ≠ f x := fun h => hxq (hfinj h.symm)
              have hDvx : D v (f x) := by simpa [D, Yv, hvS'] using hyYv
              exact hZind v hvZ (f x) (hfZ x) hne_vx hDvx
            have hcol_bi := colorableOn_of_digraph_blocks S' (fun x => ({x} : Finset V)) D
              ((t - 2) * k) cPrev hout_D hind_D
            have hbiS' : S'.biUnion (fun x => ({x} : Finset V)) = S' := by ext x; simp
            rw [hbiS'] at hcol_bi
            exact colorableOn_mono_num (le_max_right _ _) hcol_bi
      exact haux S.card S le_rfl (Finset.Subset.refl S)

private def rodlBound (s t : ℕ) : ℕ :=
  rodlPartialBound t (s + s * s - 1)

private lemma colorableOn_bicliqueFree_no_modelTree {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ} (hs : 2 ≤ s) {t : ℕ} (ht : 1 ≤ t)
    (U : Finset V) (hnoTree : ¬ HasModelTreeOn G U s) (hnoBiclique : ¬ HasCore G U 2 t) :
    ColorableOn G U (rodlBound s t) := by
  have hs1 : 1 ≤ s := by omega
  have hspos : 1 ≤ s + s * s := by omega
  have hm : (s + s * s - 1) + 2 = 1 + s + s * s := by omega
  refine colorableOn_of_no_partialModel_bicliqueFree hs1 ht (s + s * s - 1) (by omega) U
    hnoBiclique ?_
  intro hp
  have hp' : HasPartialModel G U s hs1 (1 + s + s * s) le_rfl := by
    obtain ⟨f, hfinj, hfU, hfadj⟩ := hp
    refine ⟨f ∘ Fin.cast hm.symm, hfinj.comp (Fin.cast_injective _), fun x => hfU _, ?_⟩
    intro x y
    exact hfadj (Fin.cast hm.symm x) (Fin.cast hm.symm y)
  exact hnoTree (hasModelTreeOn_of_fullPartialModel hs1 hp')


/- ## Section 4: Cores, Templates, and Inductive Chi-Boundedness -/

private lemma exists_fin_emb_of_card {V : Type*} [DecidableEq V] (S : Finset V) {k : ℕ}
    (hk : k ≤ S.card) :
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, f i ∈ S := by
  classical
  have hle : k ≤ Fintype.card {x // x ∈ S} := by rwa [Fintype.card_coe]
  let e : Fin k ↪ {x // x ∈ S} :=
    (Fin.castLEEmb hle).trans (Fintype.equivFin {x // x ∈ S}).symm.toEmbedding
  exact ⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h), fun i => (e i).2⟩

private lemma hasCore_snoc {V : Type*} {G : SimpleGraph V} {U S K₀ : Finset V} {d t : ℕ}
    (hSU : S ⊆ U) (hKU : K₀ ⊆ U) (hKcard : K₀.card = t) (hdisjSK : Disjoint S K₀)
    (hcomp : ∀ u ∈ S, ∀ v ∈ K₀, G.Adj u v) (hcore : HasCore G S d t) :
    HasCore G U (d + 1) t := by
  obtain ⟨B, hBS, hBcard, hBdisj, hBadj⟩ := hcore
  refine ⟨Fin.snoc B K₀, ?_, ?_, ?_, ?_⟩
  · intro p
    induction p using Fin.lastCases with
    | last => simpa using hKU
    | cast p₀ => simpa using (hBS p₀).trans hSU
  · intro p
    induction p using Fin.lastCases with
    | last => simpa using hKcard
    | cast p₀ => simpa using hBcard p₀
  · intro p q hpq
    induction p using Fin.lastCases with
    | last =>
      induction q using Fin.lastCases with
      | last => exact absurd rfl hpq
      | cast q₀ =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact (Disjoint.mono_left (hBS q₀) hdisjSK).symm
    | cast p₀ =>
      induction q using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact Disjoint.mono_left (hBS p₀) hdisjSK
      | cast q₀ =>
        simp only [Fin.snoc_castSucc]
        exact hBdisj p₀ q₀ (fun h => hpq (congr_arg Fin.castSucc h))
  · intro p q hpq u hu v hv
    induction p using Fin.lastCases with
    | last =>
      induction q using Fin.lastCases with
      | last => exact absurd rfl hpq
      | cast q₀ =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hu hv
        exact (hcomp v (hBS q₀ hv) u hu).symm
    | cast p₀ =>
      induction q using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hu hv
        exact hcomp u (hBS p₀ hu) v hv
      | cast q₀ =>
        simp only [Fin.snoc_castSucc] at hu hv
        exact hBadj p₀ q₀ (fun h => hpq (congr_arg Fin.castSucc h)) u hu v hv

private lemma cliqueFreeOn_of_not_hasCore {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {U : Finset V} {d t : ℕ} (hno : ¬ HasCore G U d t) :
    G.CliqueFreeOn (U : Set V) (d * t) := by
  intro K hKU ⟨hKcl, hKcard⟩
  apply hno
  have hKU' : K ⊆ U := fun x hx => Finset.mem_coe.mp (hKU (Finset.mem_coe.mpr hx))
  obtain ⟨e, he_inj, he_mem⟩ := exists_fin_emb_of_card K (le_of_eq hKcard.symm)
  let A : Fin d → Finset V := fun p =>
    (Finset.univ : Finset (Fin t)).image (fun j => e ⟨p.val * t + j.val, by nlinarith [p.isLt, j.isLt]⟩)
  have hidx_ne : ∀ (p q : Fin d), p ≠ q → ∀ (j₁ j₂ : Fin t),
      (⟨p.val * t + j₁.val, by nlinarith [p.isLt, j₁.isLt]⟩ : Fin (d * t)) ≠
      ⟨q.val * t + j₂.val, by nlinarith [q.isLt, j₂.isLt]⟩ := by
    intro p q hpq j₁ j₂ heq
    have hval := congr_arg Fin.val heq
    dsimp at hval
    apply hpq
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (p.val + 1) * t ≤ q.val * t := Nat.mul_le_mul_right t hlt
      nlinarith [j₁.isLt, j₂.isLt]
    · have : (q.val + 1) * t ≤ p.val * t := Nat.mul_le_mul_right t hgt
      nlinarith [j₁.isLt, j₂.isLt]
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro p x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hKU' (he_mem _)
  · intro p
    dsimp [A]
    rw [Finset.card_image_of_injective]
    · simp
    · intro j₁ j₂ hj
      have hval := congr_arg Fin.val (he_inj hj)
      dsimp at hval
      exact Fin.ext (by omega)
  · intro p q hpq
    rw [Finset.disjoint_left]
    intro x hxp hxq
    obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hxp
    obtain ⟨j₂, _, heq⟩ := Finset.mem_image.mp hxq
    exact hidx_ne p q hpq j₁ j₂ (he_inj heq).symm
  · intro p q hpq u hu v hv
    obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hv
    exact hKcl (Finset.mem_coe.mpr (he_mem _)) (Finset.mem_coe.mpr (he_mem _))
      (fun heq => hidx_ne p q hpq j₁ j₂ (he_inj heq))

private structure StableCore {V : Type*} (G : SimpleGraph V) (U : Finset V) (d w : ℕ) where
  part : Fin d → Finset V
  part_sub : ∀ p, part p ⊆ U
  part_card : ∀ p, (part p).card = w
  part_disj : ∀ p q, p ≠ q → Disjoint (part p) (part q)
  part_adj : ∀ p q, p ≠ q → ∀ u ∈ part p, ∀ v ∈ part q, G.Adj u v
  part_indep : ∀ p, ∀ u ∈ part p, ∀ v ∈ part p, ¬ G.Adj u v

private def StableCore.verts {V : Type*} [DecidableEq V] {G : SimpleGraph V} {U : Finset V}
    {d w : ℕ} (C : StableCore G U d w) : Finset V :=
  Finset.univ.biUnion C.part

private lemma StableCore.verts_sub {V : Type*} [DecidableEq V] {G : SimpleGraph V} {U : Finset V}
    {d w : ℕ} (C : StableCore G U d w) : C.verts ⊆ U :=
  Finset.biUnion_subset.mpr fun p _ => C.part_sub p

private lemma StableCore.part_sub_verts {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {U : Finset V} {d w : ℕ} (C : StableCore G U d w) (p : Fin d) : C.part p ⊆ C.verts :=
  fun _ hx => Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, hx⟩

private lemma StableCore.verts_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {U : Finset V}
    {d w : ℕ} (C : StableCore G U d w) : C.verts.card = d * w := by
  unfold StableCore.verts
  rw [Finset.card_biUnion (fun p _ q _ hpq => C.part_disj p q hpq)]
  simp [C.part_card]

private def StableCore.mono {V : Type*} {G : SimpleGraph V} {U₁ U₂ : Finset V} {d w : ℕ}
    (hsub : U₁ ⊆ U₂) (C : StableCore G U₁ d w) : StableCore G U₂ d w where
  part := C.part
  part_sub := fun p => (C.part_sub p).trans hsub
  part_card := C.part_card
  part_disj := C.part_disj
  part_adj := C.part_adj
  part_indep := C.part_indep

private lemma colorableOn_of_isEmpty_stableCore {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U₀ U : Finset V}
    {s d t w M : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) (hw : 1 ≤ w)
    (hUU₀ : U ⊆ U₀)
    (hnoTree : ¬ HasModelTreeOn G U₀ s)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    (hemp : IsEmpty (StableCore G U d w))
    (hM : ¬ HasCore G U d (max (rodlBound s t) t * w) → ColorableOn G U M) :
    ColorableOn G U M := by
  apply hM
  intro ⟨A, hAU, hAcard, hAdisj, hAadj⟩
  let cB := max (rodlBound s t) t
  have hcB1 : 1 ≤ cB := le_trans ht (le_max_right _ _)
  have ht_le_A : ∀ p : Fin d, t ≤ (A p).card := by
    intro p
    rw [hAcard p]
    calc t = t * 1 := (Nat.mul_one t).symm
      _ ≤ cB * w := Nat.mul_le_mul (le_max_right _ _) hw
  have hnoBi : ∀ i : Fin d, ¬ HasCore G (A i) 2 t := by
    intro i ⟨D, hDA, hDcard, hDdisj, hDadj⟩
    apply hnoCore
    classical
    choose E hEA hEcard using fun p : Fin d => Finset.exists_subset_card_eq (ht_le_A p)
    let C' : Fin (d + 1) → Finset V :=
      Fin.snoc (fun p : Fin d => if p = i then D 0 else E p) (D 1)
    refine ⟨C', ?_, ?_, ?_, ?_⟩
    · intro p
      induction p using Fin.lastCases with
      | last => simpa [C'] using (hDA 1).trans ((hAU i).trans hUU₀)
      | cast p₀ =>
        simp only [C', Fin.snoc_castSucc]
        split_ifs with hp
        · exact (hDA 0).trans ((hAU i).trans hUU₀)
        · exact (hEA p₀).trans ((hAU p₀).trans hUU₀)
    · intro p
      induction p using Fin.lastCases with
      | last => simpa [C'] using hDcard 1
      | cast p₀ =>
        simp only [C', Fin.snoc_castSucc]
        split_ifs
        · exact hDcard 0
        · exact hEcard p₀
    · intro p q hpq
      induction p using Fin.lastCases with
      | last =>
        induction q using Fin.lastCases with
        | last => exact absurd rfl hpq
        | cast q₀ =>
          simp only [C', Fin.snoc_last, Fin.snoc_castSucc]
          split_ifs with hq
          · exact hDdisj 1 0 (by decide)
          · exact Disjoint.mono (hDA 1) (hEA q₀) (hAdisj i q₀ (Ne.symm hq))
      | cast p₀ =>
        induction q using Fin.lastCases with
        | last =>
          simp only [C', Fin.snoc_last, Fin.snoc_castSucc]
          split_ifs with hp
          · exact hDdisj 0 1 (by decide)
          · exact Disjoint.mono (hEA p₀) (hDA 1) (hAdisj p₀ i hp)
        | cast q₀ =>
          simp only [C', Fin.snoc_castSucc]
          have hpq₀ : p₀ ≠ q₀ := fun h => hpq (congr_arg Fin.castSucc h)
          split_ifs with hp hq hq
          · exact absurd (hp.trans hq.symm) hpq₀
          · subst hp; exact Disjoint.mono (hDA 0) (hEA q₀) (hAdisj p₀ q₀ hpq₀)
          · subst hq; exact Disjoint.mono (hEA p₀) (hDA 0) (hAdisj p₀ q₀ hpq₀)
          · exact Disjoint.mono (hEA p₀) (hEA q₀) (hAdisj p₀ q₀ hpq₀)
    · intro p q hpq u hu v hv
      induction p using Fin.lastCases with
      | last =>
        induction q using Fin.lastCases with
        | last => exact absurd rfl hpq
        | cast q₀ =>
          simp only [C', Fin.snoc_last, Fin.snoc_castSucc] at hu hv
          split_ifs at hv with hq
          · exact hDadj 1 0 (by decide) u hu v hv
          · exact hAadj i q₀ (Ne.symm hq) u (hDA 1 hu) v (hEA q₀ hv)
      | cast p₀ =>
        induction q using Fin.lastCases with
        | last =>
          simp only [C', Fin.snoc_last, Fin.snoc_castSucc] at hu hv
          split_ifs at hu with hp
          · exact hDadj 0 1 (by decide) u hu v hv
          · exact hAadj p₀ i hp u (hEA p₀ hu) v (hDA 1 hv)
        | cast q₀ =>
          simp only [C', Fin.snoc_castSucc] at hu hv
          have hpq₀ : p₀ ≠ q₀ := fun h => hpq (congr_arg Fin.castSucc h)
          split_ifs at hu hv with hp hq hq
          · exact absurd (hp.trans hq.symm) hpq₀
          · subst hp; exact hAadj p₀ q₀ hpq₀ u (hDA 0 hu) v (hEA q₀ hv)
          · subst hq; exact hAadj p₀ q₀ hpq₀ u (hEA p₀ hu) v (hDA 0 hv)
          · exact hAadj p₀ q₀ hpq₀ u (hEA p₀ hu) v (hEA q₀ hv)
  have hexB : ∀ i : Fin d, ∃ B ⊆ A i, B.card = w ∧ ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v := by
    intro i
    have hnoT_i : ¬ HasModelTreeOn G (A i) s :=
      fun h => hnoTree (hasModelTreeOn_mono ((hAU i).trans hUU₀) h)
    have hcol_i : ColorableOn G (A i) cB :=
      colorableOn_mono_num (le_max_left _ _)
        (colorableOn_bicliqueFree_no_modelTree hs ht (A i) hnoT_i (hnoBi i))
    exact indep_of_colorableOn hcB1 hcol_i (le_of_eq (hAcard i).symm)
  classical
  choose B hBA hBcard hBind using hexB
  exact hemp.false
    { part := B
      part_sub := fun p => (hBA p).trans (hAU p)
      part_card := hBcard
      part_disj := fun p q hpq => Disjoint.mono (hBA p) (hBA q) (hAdisj p q hpq)
      part_adj := fun p q hpq u hu v hv => hAadj p q hpq u (hBA p hu) v (hBA q hv)
      part_indep := hBind }

private structure Template {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U₀ : Finset V) (s d t wBase : ℕ) where
  core : StableCore G U₀ d (wBase * t)
  P : Finset V
  P_sub : P ⊆ U₀
  verts_sub_P : core.verts ⊆ P
  dense_part : ∀ v ∈ P \ core.verts,
    ∃ p : Fin d, s * t ^ (s - 1) ≤ ((core.part p).filter (G.Adj v)).card
  nonadj_part : ∀ v ∈ P \ core.verts,
    ∃ p : Fin d, wBase ≤ ((core.part p).filter (fun x => ¬ G.Adj v x)).card

private lemma colorableOn_template {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U₀ : Finset V}
    {s d t wBase Mf : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    (hf : ∀ S ⊆ U₀, ¬ HasCore G S d t → ColorableOn G S Mf)
    (T : Template G U₀ s d t wBase) :
    ColorableOn G T.P (d * (wBase * t) + 2 ^ (d * (wBase * t)) * Mf) := by
  have hPsub : T.P ⊆ T.core.verts ∪ (T.P \ T.core.verts) := fun x hx => by
    by_cases hxC : x ∈ T.core.verts
    · exact Finset.mem_union_left _ hxC
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxC⟩)
  have hcolC : ColorableOn G T.core.verts (d * (wBase * t)) :=
    colorableOn_of_card_le G T.core.verts (le_of_eq T.core.verts_card)
  let F : Finset V → Finset V := fun X =>
    (T.P \ T.core.verts).filter (fun v => T.core.verts.filter (G.Adj v) = X)
  have hsubF : T.P \ T.core.verts ⊆ T.core.verts.powerset.biUnion F := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨T.core.verts.filter (G.Adj v),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _),
      Finset.mem_filter.mpr ⟨hv, rfl⟩⟩
  have hpow_card : T.core.verts.powerset.card = 2 ^ (d * (wBase * t)) := by
    rw [Finset.card_powerset, T.core.verts_card]
  have hcolRem : ColorableOn G (T.P \ T.core.verts) (2 ^ (d * (wBase * t)) * Mf) := by
    rw [← hpow_card]
    refine colorableOn_biUnion T.core.verts.powerset F hsubF fun X hX => ?_
    rcases (F X).eq_empty_or_nonempty with hFemp | ⟨v₀, hv₀⟩
    · rw [hFemp]
      exact colorableOn_empty G Mf
    · obtain ⟨hv₀P, hXv₀⟩ := Finset.mem_filter.mp hv₀
      obtain ⟨p, hp_card⟩ := T.dense_part v₀ hv₀P
      have ht_le_st : t ≤ s * t ^ (s - 1) := by
        have hpow : t ≤ t ^ (s - 1) := by
          have hs1 : s - 1 = (s - 2) + 1 := by omega
          rw [hs1, pow_succ]
          exact Nat.le_mul_of_pos_left t (Nat.one_le_pow (s - 2) t ht)
        calc t = 1 * t := (Nat.one_mul t).symm
          _ ≤ s * t ^ (s - 1) := Nat.mul_le_mul (by omega) hpow
      have hsubX : (T.core.part p).filter (G.Adj v₀) ⊆ X := by
        rw [← hXv₀]
        intro x hx
        obtain ⟨hxp, hxv₀⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨T.core.part_sub_verts p hxp, hxv₀⟩
      have ht_le_X : t ≤ X.card :=
        le_trans ht_le_st (le_trans hp_card (Finset.card_le_card hsubX))
      obtain ⟨K₀, hK₀X, hK₀card⟩ := Finset.exists_subset_card_eq ht_le_X
      have hFX_U : F X ⊆ U₀ :=
        (Finset.filter_subset _ _).trans (Finset.sdiff_subset.trans T.P_sub)
      have hK₀_C : K₀ ⊆ T.core.verts := hK₀X.trans (Finset.mem_powerset.mp hX)
      have hdisj : Disjoint (F X) K₀ := Finset.disjoint_left.mpr fun u hu huk =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).2 (hK₀_C huk)
      have hcomp : ∀ u ∈ F X, ∀ x ∈ K₀, G.Adj u x := by
        intro u hu x hx
        have hXu : T.core.verts.filter (G.Adj u) = X := (Finset.mem_filter.mp hu).2
        have hx' : x ∈ T.core.verts.filter (G.Adj u) := hXu ▸ hK₀X hx
        exact (Finset.mem_filter.mp hx').2
      exact hf (F X) hFX_U fun hc =>
        hnoCore (hasCore_snoc hFX_U (hK₀_C.trans T.core.verts_sub) hK₀card hdisj hcomp hc)
  exact colorableOn_mono_set hPsub (colorableOn_union_add hcolC hcolRem)

private lemma few_nonadj_card_lt {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U₀ : Finset V}
    {d t wBase : ℕ} (hwBase : 1 ≤ wBase)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    (C : StableCore G U₀ d (wBase * t)) :
    ((U₀ \ C.verts).filter
      (fun v => ∀ p : Fin d, ((C.part p).filter (fun x => ¬ G.Adj v x)).card < wBase)).card < t := by
  by_contra hge
  have hle : t ≤ ((U₀ \ C.verts).filter
      (fun v => ∀ p : Fin d, ((C.part p).filter (fun x => ¬ G.Adj v x)).card < wBase)).card := by
    omega
  obtain ⟨K₀, hK₀Q, hK₀card⟩ := Finset.exists_subset_card_eq hle
  have hexB : ∀ p : Fin d, ∃ B ⊆ C.part p, B.card = t ∧ ∀ x ∈ B, ∀ v ∈ K₀, G.Adj x v := by
    intro p
    let Bad := K₀.biUnion (fun v => (C.part p).filter (fun x => ¬ G.Adj v x))
    have hBad_card : Bad.card ≤ t * (wBase - 1) := by
      calc Bad.card
          ≤ ∑ v ∈ K₀, ((C.part p).filter (fun x => ¬ G.Adj v x)).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ K₀, (wBase - 1) := by
            refine Finset.sum_le_sum fun v hv => ?_
            have hlt := (Finset.mem_filter.mp (hK₀Q hv)).2 p
            omega
        _ = t * (wBase - 1) := by simp [hK₀card]
    have hpart_sub : C.part p ⊆ (C.part p \ Bad) ∪ Bad := fun x hx => by
      by_cases hxB : x ∈ Bad
      · exact Finset.mem_union_right _ hxB
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
    have hsum_eq : t * (wBase - 1) + t = wBase * t := by
      cases wBase with
      | zero => omega
      | succ wb => simp; ring
    have hgood_card : t ≤ (C.part p \ Bad).card := by
      have hc := (Finset.card_le_card hpart_sub).trans (Finset.card_union_le _ _)
      have hp := C.part_card p
      omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hgood_card
    refine ⟨B, hBsub.trans Finset.sdiff_subset, hBcard, ?_⟩
    intro x hx v hv
    have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp (hBsub hx)).2
    have hxPart : x ∈ C.part p := (Finset.mem_sdiff.mp (hBsub hx)).1
    by_contra hnad
    exact hxNotBad (Finset.mem_biUnion.mpr ⟨v, hv,
      Finset.mem_filter.mpr ⟨hxPart, fun h => hnad h.symm⟩⟩)
  classical
  choose B hBpart hBcard hBadj using hexB
  have hK₀_sub : K₀ ⊆ U₀ :=
    hK₀Q.trans ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
  have hdisjCK : Disjoint C.verts K₀ := Finset.disjoint_left.mpr fun x hxC hxK =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hK₀Q hxK)).1).2 hxC
  have hCoreB : HasCore G (Finset.univ.biUnion B) d t :=
    ⟨B, fun p x hx => Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, hx⟩, hBcard,
      fun p q hpq => Disjoint.mono (hBpart p) (hBpart q) (C.part_disj p q hpq),
      fun p q hpq u hu v hv => C.part_adj p q hpq u (hBpart p hu) v (hBpart q hv)⟩
  have hbiB_sub : Finset.univ.biUnion B ⊆ U₀ :=
    (Finset.biUnion_subset.mpr fun p _ => (hBpart p).trans (C.part_sub_verts p)).trans C.verts_sub
  have hdisjBK : Disjoint (Finset.univ.biUnion B) K₀ :=
    Disjoint.mono_left
      (Finset.biUnion_subset.mpr fun p _ => (hBpart p).trans (C.part_sub_verts p)) hdisjCK
  have hcompBK : ∀ u ∈ Finset.univ.biUnion B, ∀ v ∈ K₀, G.Adj u v := by
    intro u hu v hv
    obtain ⟨p, _, hup⟩ := Finset.mem_biUnion.mp hu
    exact hBadj p u hup v hv
  exact hnoCore (hasCore_snoc hbiB_sub hK₀_sub hK₀card hdisjBK hcompBK hCoreB)

private def seqSupp {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Finset V :=
  I.biUnion (fun i => (Tseq i).P)

private def IsTemplateSeq {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Tseq i).P (Tseq j).P) ∧
  (∀ i ∈ I, ∀ j ∈ I, i < j → ∀ v ∈ (Tseq j).P,
    (∀ p : Fin d, (((Tseq i).core.part p).filter (G.Adj v)).card < s * t ^ (s - 1)) ∨
    (∀ p : Fin d, (((Tseq i).core.part p).filter (fun x => ¬ G.Adj v x)).card < wBase))

private lemma isTemplateSeq_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I₁ I₂ : Finset (Fin n)}
    (hsub : I₁ ⊆ I₂) (hseq : IsTemplateSeq Tseq I₂) : IsTemplateSeq Tseq I₁ :=
  ⟨fun i hi j hj => hseq.1 i (hsub hi) j (hsub hj),
   fun i hi j hj => hseq.2 i (hsub hi) j (hsub hj)⟩

private lemma seqSupp_sub {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) :
    seqSupp Tseq I ⊆ U₀ :=
  Finset.biUnion_subset.mpr fun i _ => (Tseq i).P_sub

private lemma exists_maximal_templateSeq {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U₀ : Finset V)
    {s d t wBase : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t) (hwBase : 1 ≤ wBase) :
    ∃ (n : ℕ) (Tseq : Fin n → Template G U₀ s d t wBase),
      IsTemplateSeq Tseq Finset.univ ∧
      IsEmpty (StableCore G (U₀ \ seqSupp Tseq Finset.univ) d (wBase * t)) := by
  have haux : ∀ (m : ℕ) (rem : Finset V), rem.card ≤ m → rem ⊆ U₀ →
      ∃ (n : ℕ) (Tseq : Fin n → Template G U₀ s d t wBase),
        (∀ i, (Tseq i).P ⊆ rem) ∧
        IsTemplateSeq Tseq Finset.univ ∧
        IsEmpty (StableCore G (rem \ seqSupp Tseq Finset.univ) d (wBase * t)) := by
    intro m
    induction m with
    | zero =>
      intro rem hcard _
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]
      refine ⟨0, Fin.elim0, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, ⟨fun C => ?_⟩⟩
      have h0 : (C.part ⟨0, hd⟩).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.subset_empty.mp (C.part_sub ⟨0, hd⟩))
      have hw : 1 ≤ wBase * t := Nat.mul_pos hwBase ht
      rw [C.part_card ⟨0, hd⟩] at h0
      omega
    | succ m ih =>
      intro rem hcard hremU
      by_cases hex : Nonempty (StableCore G rem d (wBase * t))
      · obtain ⟨C₀⟩ := hex
        let cand := (rem \ C₀.verts).filter (fun v =>
          (∃ p : Fin d, s * t ^ (s - 1) ≤ ((C₀.part p).filter (G.Adj v)).card) ∧
          (∃ p : Fin d, wBase ≤ ((C₀.part p).filter (fun x => ¬ G.Adj v x)).card))
        let P₀ : Finset V := C₀.verts ∪ cand
        have hP₀_rem : P₀ ⊆ rem :=
          Finset.union_subset C₀.verts_sub ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
        have hC₀_pos : 1 ≤ P₀.card := by
          have hw : 1 ≤ d * (wBase * t) := Nat.mul_pos hd (Nat.mul_pos hwBase ht)
          calc 1 ≤ C₀.verts.card := by rw [C₀.verts_card]; exact hw
            _ ≤ P₀.card := Finset.card_le_card Finset.subset_union_left
        have hrem'_card : (rem \ P₀).card ≤ m := by
          have hdisj : Disjoint (rem \ P₀) P₀ := Finset.sdiff_disjoint
          have hunion : (rem \ P₀) ∪ P₀ = rem := Finset.sdiff_union_of_subset hP₀_rem
          have hsum := Finset.card_union_of_disjoint hdisj
          rw [hunion] at hsum
          omega
        let T₀ : Template G U₀ s d t wBase :=
          { core := C₀.mono hremU
            P := P₀
            P_sub := hP₀_rem.trans hremU
            verts_sub_P := Finset.subset_union_left
            dense_part := fun v hv => by
              obtain ⟨hvP, hvNotC⟩ := Finset.mem_sdiff.mp hv
              have hvcand : v ∈ cand := (Finset.mem_union.mp hvP).resolve_left hvNotC
              exact (Finset.mem_filter.mp hvcand).2.1
            nonadj_part := fun v hv => by
              obtain ⟨hvP, hvNotC⟩ := Finset.mem_sdiff.mp hv
              have hvcand : v ∈ cand := (Finset.mem_union.mp hvP).resolve_left hvNotC
              exact (Finset.mem_filter.mp hvcand).2.2 }
        obtain ⟨n', Tseq', hPrem', hSeq', hEmp'⟩ :=
          ih (rem \ P₀) hrem'_card (Finset.sdiff_subset.trans hremU)
        let Tseq : Fin (n' + 1) → Template G U₀ s d t wBase := fun i =>
          if hi : i.val = 0 then T₀ else Tseq' ⟨i.val - 1, by omega⟩
        refine ⟨n' + 1, Tseq, ?_, ?_, ?_⟩
        · intro i
          dsimp [Tseq]
          split_ifs with hi
          · exact hP₀_rem
          · exact (hPrem' _).trans Finset.sdiff_subset
        · refine ⟨?_, ?_⟩
          · intro i _ j _ hij
            dsimp [Tseq]
            split_ifs with hi hj hj
            · exact absurd (Fin.ext (hi.trans hj.symm)) hij
            · exact (Disjoint.mono_left (hPrem' _) Finset.sdiff_disjoint).symm
            · exact Disjoint.mono_left (hPrem' _) Finset.sdiff_disjoint
            · refine hSeq'.1 _ (Finset.mem_univ _) _ (Finset.mem_univ _) ?_
              intro heq
              have hval := congr_arg Fin.val heq
              dsimp at hval
              exact hij (Fin.ext (by omega))
          · intro i _ j _ hij v hv
            dsimp [Tseq] at hv ⊢
            split_ifs at hv ⊢ with hi hj hj
            · exact absurd (Fin.ext (hi.trans hj.symm)) (ne_of_lt hij)
            · have hv_rem_sdiff : v ∈ rem \ P₀ := hPrem' ⟨j.val - 1, by omega⟩ hv
              obtain ⟨hv_rem, hv_not_P₀⟩ := Finset.mem_sdiff.mp hv_rem_sdiff
              have hv_not_C₀ : v ∉ C₀.verts :=
                fun h => hv_not_P₀ (Finset.mem_union_left _ h)
              have hv_not_cand : v ∉ cand :=
                fun h => hv_not_P₀ (Finset.mem_union_right _ h)
              have hnot_both : ¬ ((∃ p : Fin d, s * t ^ (s - 1) ≤ ((C₀.part p).filter (G.Adj v)).card) ∧
                  (∃ p : Fin d, wBase ≤ ((C₀.part p).filter (fun x => ¬ G.Adj v x)).card)) :=
                fun hb => hv_not_cand (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hv_rem, hv_not_C₀⟩, hb⟩)
              rw [not_and_or] at hnot_both
              rcases hnot_both with h1 | h2
              · left
                intro p
                exact lt_of_not_ge fun hp => h1 ⟨p, hp⟩
              · right
                intro p
                exact lt_of_not_ge fun hp => h2 ⟨p, hp⟩
            · exfalso; have : i.val < j.val := hij; omega
            · have hlt' : (⟨i.val - 1, by omega⟩ : Fin n') < ⟨j.val - 1, by omega⟩ := by
                change i.val - 1 < j.val - 1
                have : i.val < j.val := hij
                omega
              exact hSeq'.2 _ (Finset.mem_univ _) _ (Finset.mem_univ _) hlt' v hv
        · have hsupp_eq : rem \ seqSupp Tseq Finset.univ =
              (rem \ P₀) \ seqSupp Tseq' Finset.univ := by
            ext x
            simp only [Finset.mem_sdiff, seqSupp, Finset.mem_biUnion, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hx_rem, hnot⟩
              refine ⟨⟨hx_rem, fun hxP₀ => hnot ⟨⟨0, by omega⟩, by simpa [Tseq] using hxP₀⟩⟩, ?_⟩
              rintro ⟨k, hxk⟩
              exact hnot ⟨⟨k.val + 1, by omega⟩, by simp [Tseq, hxk]⟩
            · rintro ⟨⟨hx_rem, hxNotP₀⟩, hnot'⟩
              refine ⟨hx_rem, ?_⟩
              rintro ⟨i, hxi⟩
              dsimp [Tseq] at hxi
              split_ifs at hxi with hi
              · exact hxNotP₀ hxi
              · exact hnot' ⟨⟨i.val - 1, by omega⟩, hxi⟩
          rw [hsupp_eq]
          exact hEmp'
      · refine ⟨0, Fin.elim0, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, ?_⟩
        have hsupp_emp : rem \ seqSupp (Fin.elim0 : Fin 0 → Template G U₀ s d t wBase) Finset.univ = rem := by
          ext x; simp [seqSupp]
        rw [hsupp_emp]
        exact ⟨fun C => hex ⟨C⟩⟩
  obtain ⟨n, Tseq, _, hSeq, hEmp⟩ := haux U₀.card U₀ le_rfl (Finset.Subset.refl U₀)
  exact ⟨n, Tseq, hSeq, hEmp⟩

private def tplR (d t s : ℕ) : ℕ := ramseyNum ((d + 1) * t) s

private lemma tplR_pos {d t s : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s) : 1 ≤ tplR d t s := by
  unfold tplR
  have hdt : 1 ≤ (d + 1) * t := Nat.mul_pos (Nat.succ_pos d) ht
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : (d + 1) * t ≠ 0) with ⟨p, hp⟩
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0) with ⟨q, hq⟩
  rw [hp, hq, ramseyNum]
  omega

private def tplR4 (d t s : ℕ) : ℕ := tplR d t s + s
private def tplR6 (d t s : ℕ) : ℕ := (2 * tplR4 d t s + 1) * tplR d t s + tplR4 d t s
private def tplL4 (d t s : ℕ) : ℕ := (2 * (s * tplR6 d t s) + 1) * tplR d t s + tplR6 d t s
private def tplL2 (d t s w : ℕ) : ℕ := d * w * tplL4 d t s + d * w
private def tplR7 (d t s w : ℕ) : ℕ := (2 * tplR6 d t s + 1) * tplL2 d t s w

private def tplWBase (s t : ℕ) : ℕ :=
  1 + s + (s + 1) * (s + 1) * (s * t ^ (s - 1)) + s * (s ^ 3 * t ^ (s - 1))

private lemma tplWBase_pos (s t : ℕ) : 1 ≤ tplWBase s t := by
  unfold tplWBase; omega

private lemma card_sdiff_adj_ge {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (S X : Finset V) (k B : ℕ)
    (hdeg : ∀ u ∈ X, (S.filter (G.Adj u)).card ≤ B)
    (hS : k + X.card * B ≤ S.card) :
    k ≤ (S.filter (fun z => ∀ u ∈ X, ¬ G.Adj u z)).card := by
  let Bad := X.biUnion (fun u => S.filter (G.Adj u))
  have hBad : Bad.card ≤ X.card * B := by
    calc Bad.card
        ≤ ∑ u ∈ X, (S.filter (G.Adj u)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ X, B := Finset.sum_le_sum hdeg
      _ = X.card * B := by simp
  have hsub : S ⊆ S.filter (fun z => ∀ u ∈ X, ¬ G.Adj u z) ∪ Bad := by
    intro z hz
    by_cases hall : ∀ u ∈ X, ¬ G.Adj u z
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hall⟩)
    · have hex : ∃ u ∈ X, G.Adj u z := by
        by_contra hno
        exact hall fun u hu huz => hno ⟨u, hu, huz⟩
      obtain ⟨u, huX, huz⟩ := hex
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨u, huX, Finset.mem_filter.mpr ⟨hz, huz⟩⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

private def Nice1 {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  IsTemplateSeq Tseq I ∧
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ v ∈ (Tseq j).P,
    ∃ p : Fin d, wBase ≤ (((Tseq i).core.part p).filter (fun x => ¬ G.Adj v x)).card

private lemma nice1_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I₁ I₂ : Finset (Fin n)}
    (hsub : I₁ ⊆ I₂) (h : Nice1 Tseq I₂) : Nice1 Tseq I₁ :=
  ⟨isTemplateSeq_mono hsub h.1, fun i hi j hj => h.2 i (hsub hi) j (hsub hj)⟩

private lemma nice1_lt_adj {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (h1 : Nice1 Tseq I) {i j : Fin n} (hi : i ∈ I) (hj : j ∈ I) (hij : i < j)
    {v : V} (hv : v ∈ (Tseq j).P) (p : Fin d) :
    (((Tseq i).core.part p).filter (G.Adj v)).card < s * t ^ (s - 1) := by
  rcases h1.1.2 i hi j hj hij v hv with hlt | hnon
  · exact hlt p
  · obtain ⟨q, hq⟩ := h1.2 i hi j hj (ne_of_lt hij) v hv
    exact absurd (hnon q) (not_lt.mpr hq)

private lemma nice1_nonadj_of_notMem_core {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (h1 : Nice1 Tseq I) {v : V} (hv : v ∈ seqSupp Tseq I) {i : Fin n} (hi : i ∈ I)
    (hvC : v ∉ (Tseq i).core.verts) :
    ∃ p : Fin d, wBase ≤ (((Tseq i).core.part p).filter (fun x => ¬ G.Adj v x)).card := by
  obtain ⟨j, hjI, hvPj⟩ := Finset.mem_biUnion.mp hv
  by_cases hij : i = j
  · subst hij
    exact (Tseq i).nonadj_part v (Finset.mem_sdiff.mpr ⟨hvPj, hvC⟩)
  · exact h1.2 i hi j hjI hij v hvPj

private lemma mem_P_unique {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (hseq : IsTemplateSeq Tseq I) {i j : Fin n} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j)
    {v : V} (hv : v ∈ (Tseq i).P) : v ∉ (Tseq j).P :=
  Finset.disjoint_left.mp (hseq.1 i hi j hj hij) hv

private def Nice2 {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  Nice1 Tseq I ∧
  ∀ v ∈ seqSupp Tseq I,
    (I.filter (fun i => v ∉ (Tseq i).core.verts ∧
      ∃ p : Fin d, s ^ 3 * t ^ (s - 1) ≤ (((Tseq i).core.part p).filter (G.Adj v)).card)).card < s

private lemma nice2_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I₁ I₂ : Finset (Fin n)}
    (hsub : I₁ ⊆ I₂) (h : Nice2 Tseq I₂) : Nice2 Tseq I₁ := by
  refine ⟨nice1_mono hsub h.1, fun v hv => ?_⟩
  have hv₂ : v ∈ seqSupp Tseq I₂ := by
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨i, hsub hi, hvi⟩
  exact lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _ hsub)) (h.2 v hv₂)

private lemma nice1_imp_nice2 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t n : ℕ}
    (hs : 2 ≤ s) (hd : 2 ≤ d) (ht : 1 ≤ t)
    (hnoTree : ¬ HasModelTreeOn G U₀ s)
    {Tseq : Fin n → Template G U₀ s d t (tplWBase s t)} {I : Finset (Fin n)}
    (h1 : Nice1 Tseq I) : Nice2 Tseq I := by
  refine ⟨h1, fun v hv => ?_⟩
  by_contra hge
  let M₁ := s ^ 3 * t ^ (s - 1)
  let M₂ := s + (s - 1) * (s + 1) * (s * t ^ (s - 1))
  let Bad := I.filter (fun i => v ∉ (Tseq i).core.verts ∧
    ∃ p : Fin d, M₁ ≤ (((Tseq i).core.part p).filter (G.Adj v)).card)
  have hs_le : s ≤ Bad.card := le_of_not_gt hge
  obtain ⟨I', hI'sub, hI'card⟩ := Finset.exists_subset_card_eq hs_le
  let emb := I'.orderEmbOfFin hI'card
  let idx : Fin s → Fin n := fun r => emb ⟨s - 1 - r.val, by omega⟩
  have hidx_Bad : ∀ r : Fin s, idx r ∈ Bad :=
    fun r => hI'sub (Finset.orderEmbOfFin_mem I' hI'card _)
  have hidx_I : ∀ r : Fin s, idx r ∈ I :=
    fun r => (Finset.mem_filter.mp (hidx_Bad r)).1
  have hidx_anti : ∀ r₁ r₂ : Fin s, r₁ < r₂ → idx r₂ < idx r₁ := by
    intro r₁ r₂ hlt
    exact emb.strictMono (by
      change s - 1 - r₂.val < s - 1 - r₁.val
      have : r₁.val < r₂.val := hlt
      omega)
  have hM₂_le_wb : M₂ ≤ tplWBase s t := by
    dsimp [M₂, tplWBase]
    have hmul : (s - 1) * (s + 1) ≤ (s + 1) * (s + 1) :=
      Nat.mul_le_mul_right (s + 1) (by omega)
    have hmul2 := Nat.mul_le_mul_right (s * t ^ (s - 1)) hmul
    omega
  have hM₁₂_le_w : M₁ + M₂ ≤ tplWBase s t * t := by
    have hwb_le_w : tplWBase s t ≤ tplWBase s t * t := Nat.le_mul_of_pos_right _ ht
    have hM₁_le : M₁ ≤ s * (s ^ 3 * t ^ (s - 1)) := Nat.le_mul_of_pos_left _ (by omega)
    have hsum_le : M₁ + M₂ ≤ tplWBase s t := by
      dsimp [M₁, M₂, tplWBase]
      have hmul : (s - 1) * (s + 1) ≤ (s + 1) * (s + 1) :=
        Nat.mul_le_mul_right (s + 1) (by omega)
      have hmul2 := Nat.mul_le_mul_right (s * t ^ (s - 1)) hmul
      omega
    exact le_trans hsum_le hwb_le_w
  have hex_parts : ∀ r : Fin s, ∃ q₁ q₂ : Fin d, q₁ ≠ q₂ ∧
      M₁ ≤ (((Tseq (idx r)).core.part q₁).filter (G.Adj v)).card ∧
      M₂ ≤ (((Tseq (idx r)).core.part q₂).filter (fun x => ¬ G.Adj v x)).card := by
    intro r
    obtain ⟨hv_notC, p₁, hp₁⟩ := (Finset.mem_filter.mp (hidx_Bad r)).2
    obtain ⟨p₂, hp₂⟩ := nice1_nonadj_of_notMem_core h1 hv (hidx_I r) hv_notC
    by_cases hp12 : p₁ = p₂
    · let p' : Fin d := if p₁.val = 0 then ⟨1, hd⟩ else ⟨0, by omega⟩
      have hp'ne : p' ≠ p₁ := by
        by_cases hp0 : p₁.val = 0
        · dsimp [p']; rw [if_pos hp0]
          intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
        · dsimp [p']; rw [if_neg hp0]
          intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
      let P' := (Tseq (idx r)).core.part p'
      have hpart_sum : (P'.filter (G.Adj v)).card +
          (P'.filter (fun x => ¬ G.Adj v x)).card = P'.card := by
        have hdisj : Disjoint (P'.filter (G.Adj v)) (P'.filter (fun x => ¬ G.Adj v x)) :=
          Finset.disjoint_left.mpr fun _ hx1 hx2 =>
            (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
        have hunion : P'.filter (G.Adj v) ∪ P'.filter (fun x => ¬ G.Adj v x) = P' := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter]
          by_cases h : G.Adj v x <;> simp [h]
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hP'card : P'.card = tplWBase s t * t := (Tseq (idx r)).core.part_card p'
      by_cases hM₂_p' : M₂ ≤ (P'.filter (fun x => ¬ G.Adj v x)).card
      · exact ⟨p₁, p', hp'ne.symm, hp₁, hM₂_p'⟩
      · have hM₁_p' : M₁ ≤ (P'.filter (G.Adj v)).card := by omega
        exact ⟨p', p₂, hp12 ▸ hp'ne, hM₁_p', le_trans hM₂_le_wb hp₂⟩
    · exact ⟨p₁, p₂, hp12, hp₁, le_trans hM₂_le_wb hp₂⟩
  classical
  choose q₁ q₂ hq_ne hq₁ hq₂ using hex_parts
  have hM₁_bound : 1 + (s - 1) * (s + 1) * (s * t ^ (s - 1)) ≤ M₁ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    have hsub : 2 + k - 1 = k + 1 := by omega
    have ht_pos : 1 ≤ t ^ (k + 1) := Nat.one_le_pow _ _ ht
    have hid : (2 + k) ^ 3 * t ^ (k + 1) =
        (k + 1) * (2 + k + 1) * ((2 + k) * t ^ (k + 1)) + (2 + k) * t ^ (k + 1) := by
      ring
    dsimp [M₁]
    rw [hsub, hid]
    have hpos2 : 1 ≤ (2 + k) * t ^ (k + 1) := Nat.mul_pos (by omega) ht_pos
    omega
  have hstep : ∀ m : ℕ, ∀ (hm : m ≤ s),
      ∃ (a : Fin m → V) (b : Fin m → Fin s → V),
        (∀ r : Fin m, a r ∈
          (((Tseq (idx ⟨r.val, by omega⟩)).core.part (q₁ ⟨r.val, by omega⟩)).filter (G.Adj v))) ∧
        (∀ r : Fin m, ∀ j : Fin s, b r j ∈
          (((Tseq (idx ⟨r.val, by omega⟩)).core.part (q₂ ⟨r.val, by omega⟩)).filter
            (fun x => ¬ G.Adj v x))) ∧
        (∀ r : Fin m, Function.Injective (b r)) ∧
        (∀ r₁ r₂ : Fin m, r₁ < r₂ → ¬ G.Adj (a r₁) (a r₂)) ∧
        (∀ r₁ r₂ : Fin m, r₁ ≠ r₂ → ∀ j : Fin s, ¬ G.Adj (a r₁) (b r₂ j)) ∧
        (∀ r₁ r₂ : Fin m, r₁ < r₂ → ∀ j₁ j₂ : Fin s, ¬ G.Adj (b r₁ j₁) (b r₂ j₂)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨Fin.elim0, Fin.elim0, fun r => r.elim0, fun r => r.elim0,
        fun r => r.elim0, fun r => r.elim0, fun r => r.elim0, fun r => r.elim0⟩
    | succ m ih =>
      intro hm
      obtain ⟨a, b, ha_mem, hb_mem, hb_inj, ha_na, hab_na, hbb_na⟩ := ih (by omega)
      let rNew : Fin s := ⟨m, hm⟩
      let X : Finset V := (Finset.univ : Finset (Fin m)).image a ∪
        (Finset.univ : Finset (Fin m × Fin s)).image (fun p => b p.1 p.2)
      have hX_card : X.card ≤ (s - 1) * (s + 1) := by
        calc X.card
            ≤ ((Finset.univ : Finset (Fin m)).image a).card +
                ((Finset.univ : Finset (Fin m × Fin s)).image (fun p => b p.1 p.2)).card :=
              Finset.card_union_le _ _
          _ ≤ m + m * s := add_le_add
              (le_trans Finset.card_image_le (by simp))
              (le_trans Finset.card_image_le (by simp))
          _ = m * (s + 1) := by ring
          _ ≤ (s - 1) * (s + 1) := Nat.mul_le_mul_right (s + 1) (by omega)
      have hX_deg : ∀ u ∈ X, ∀ p : Fin d,
          (((Tseq (idx rNew)).core.part p).filter (G.Adj u)).card ≤ s * t ^ (s - 1) := by
        intro u hu p
        rcases Finset.mem_union.mp hu with hua | hub
        · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hua
          let r' : Fin s := ⟨r.val, by omega⟩
          have hr_lt : r' < rNew := r.isLt
          have huP : a r ∈ (Tseq (idx r')).P :=
            (Tseq (idx r')).verts_sub_P
              ((Tseq (idx r')).core.part_sub_verts _ (Finset.mem_filter.mp (ha_mem r)).1)
          exact le_of_lt (nice1_lt_adj h1 (hidx_I rNew) (hidx_I r') (hidx_anti r' rNew hr_lt) huP p)
        · obtain ⟨⟨r, j⟩, _, rfl⟩ := Finset.mem_image.mp hub
          let r' : Fin s := ⟨r.val, by omega⟩
          have hr_lt : r' < rNew := r.isLt
          have huP : b r j ∈ (Tseq (idx r')).P :=
            (Tseq (idx r')).verts_sub_P
              ((Tseq (idx r')).core.part_sub_verts _ (Finset.mem_filter.mp (hb_mem r j)).1)
          exact le_of_lt (nice1_lt_adj h1 (hidx_I rNew) (hidx_I r') (hidx_anti r' rNew hr_lt) huP p)
      let NA := ((Tseq (idx rNew)).core.part (q₁ rNew)).filter (G.Adj v)
      let NonB := ((Tseq (idx rNew)).core.part (q₂ rNew)).filter (fun x => ¬ G.Adj v x)
      have hNA_good : 1 ≤ (NA.filter (fun z => ∀ u ∈ X, ¬ G.Adj u z)).card := by
        refine card_sdiff_adj_ge NA X 1 (s * t ^ (s - 1)) (fun u hu => ?_) ?_
        · exact le_trans
            (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
            (hX_deg u hu (q₁ rNew))
        · calc 1 + X.card * (s * t ^ (s - 1))
              ≤ 1 + (s - 1) * (s + 1) * (s * t ^ (s - 1)) :=
                Nat.add_le_add_left (Nat.mul_le_mul_right _ hX_card) 1
            _ ≤ M₁ := hM₁_bound
            _ ≤ NA.card := hq₁ rNew
      obtain ⟨aNew, haNew_f⟩ := Finset.card_pos.mp hNA_good
      obtain ⟨haNew_NA, haNew_X⟩ := Finset.mem_filter.mp haNew_f
      have hNonB_good : s ≤ (NonB.filter (fun z => ∀ u ∈ X, ¬ G.Adj u z)).card := by
        refine card_sdiff_adj_ge NonB X s (s * t ^ (s - 1)) (fun u hu => ?_) ?_
        · exact le_trans
            (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
            (hX_deg u hu (q₂ rNew))
        · calc s + X.card * (s * t ^ (s - 1))
              ≤ s + (s - 1) * (s + 1) * (s * t ^ (s - 1)) :=
                Nat.add_le_add_left (Nat.mul_le_mul_right _ hX_card) s
            _ = M₂ := rfl
            _ ≤ NonB.card := hq₂ rNew
      obtain ⟨bNew, hbNew_inj, hbNew_f⟩ :=
        exists_fin_emb_of_card (NonB.filter (fun z => ∀ u ∈ X, ¬ G.Adj u z)) hNonB_good
      let a' : Fin (m + 1) → V := fun r => if hr : r.val < m then a ⟨r.val, hr⟩ else aNew
      let b' : Fin (m + 1) → Fin s → V := fun r => if hr : r.val < m then b ⟨r.val, hr⟩ else bNew
      refine ⟨a', b', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r
        dsimp [a']
        split_ifs with hr
        · exact ha_mem ⟨r.val, hr⟩
        · have hreq : (⟨r.val, by omega⟩ : Fin s) = rNew := Fin.ext (by dsimp [rNew]; omega)
          rwa [hreq]
      · intro r j
        dsimp [b']
        split_ifs with hr
        · exact hb_mem ⟨r.val, hr⟩ j
        · have hreq : (⟨r.val, by omega⟩ : Fin s) = rNew := Fin.ext (by dsimp [rNew]; omega)
          rw [hreq]
          exact (Finset.mem_filter.mp (hbNew_f j)).1
      · intro r
        dsimp [b']
        split_ifs with hr
        · exact hb_inj ⟨r.val, hr⟩
        · exact hbNew_inj
      · intro r₁ r₂ hr₁₂
        dsimp [a']
        split_ifs with h1r h2r h2r
        · exact ha_na ⟨r₁.val, h1r⟩ ⟨r₂.val, h2r⟩ hr₁₂
        · exact haNew_X (a ⟨r₁.val, h1r⟩)
            (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨r₁.val, h1r⟩, Finset.mem_univ _, rfl⟩))
        · exfalso; have : r₁.val < r₂.val := hr₁₂; omega
        · exfalso; have : r₁.val < r₂.val := hr₁₂; omega
      · intro r₁ r₂ hr₁₂ j
        dsimp [a', b']
        split_ifs with h1r h2r h2r
        · exact hab_na ⟨r₁.val, h1r⟩ ⟨r₂.val, h2r⟩
            (fun h => hr₁₂ (Fin.ext (Fin.mk.inj h))) j
        · exact (Finset.mem_filter.mp (hbNew_f j)).2 (a ⟨r₁.val, h1r⟩)
            (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨r₁.val, h1r⟩, Finset.mem_univ _, rfl⟩))
        · intro hadj
          exact haNew_X (b ⟨r₂.val, h2r⟩ j)
            (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨(⟨r₂.val, h2r⟩, j), Finset.mem_univ _, rfl⟩))
            hadj.symm
        · exact absurd (Fin.ext (by omega : r₁.val = r₂.val)) hr₁₂
      · intro r₁ r₂ hr₁₂ j₁ j₂
        dsimp [b']
        split_ifs with h1r h2r h2r
        · exact hbb_na ⟨r₁.val, h1r⟩ ⟨r₂.val, h2r⟩ hr₁₂ j₁ j₂
        · exact (Finset.mem_filter.mp (hbNew_f j₂)).2 (b ⟨r₁.val, h1r⟩ j₁)
            (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨(⟨r₁.val, h1r⟩, j₁), Finset.mem_univ _, rfl⟩))
        · exfalso; have : r₁.val < r₂.val := hr₁₂; omega
        · exfalso; have : r₁.val < r₂.val := hr₁₂; omega
  obtain ⟨a, b, ha_mem, hb_mem, hb_inj, ha_na, hab_na, hbb_na⟩ := hstep s le_rfl
  apply hnoTree
  refine ⟨v, a, b, seqSupp_sub Tseq I hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact (Tseq (idx r)).core.part_sub (q₁ r) (Finset.mem_filter.mp (ha_mem r)).1
  · intro r j
    exact (Tseq (idx r)).core.part_sub (q₂ r) (Finset.mem_filter.mp (hb_mem r j)).1
  · intro r j j' hjj' heq
    exact hjj' (hb_inj r heq)
  · intro r
    exact (Finset.mem_filter.mp (ha_mem r)).2
  · intro r j
    exact (Finset.mem_filter.mp (hb_mem r j)).2
  · intro r₁ r₂ hr₁₂
    rcases lt_or_gt_of_ne hr₁₂ with hlt | hgt
    · exact ha_na r₁ r₂ hlt
    · exact fun h => ha_na r₂ r₁ hgt h.symm
  · intro r₁ r₂ j
    constructor
    · intro hadj
      by_contra hne
      exact hab_na r₁ r₂ hne j hadj
    · rintro rfl
      exact (Tseq (idx r₁)).core.part_adj (q₁ r₁) (q₂ r₁) (hq_ne r₁)
        (a r₁) (Finset.mem_filter.mp (ha_mem r₁)).1
        (b r₁ j) (Finset.mem_filter.mp (hb_mem r₁ j)).1
  · intro r₁ j₁ r₂ j₂ hne
    by_cases hr : r₁ = r₂
    · subst hr
      exact (Tseq (idx r₁)).core.part_indep (q₂ r₁)
        (b r₁ j₁) (Finset.mem_filter.mp (hb_mem r₁ j₁)).1
        (b r₁ j₂) (Finset.mem_filter.mp (hb_mem r₁ j₂)).1
    · rcases lt_or_gt_of_ne hr with hlt | hgt
      · exact hbb_na r₁ r₂ hlt j₁ j₂
      · exact fun h => hbb_na r₂ r₁ hgt j₂ j₁ h.symm

private lemma indep_index_of_no_hasCore {V α : Type*} [DecidableEq V] [DecidableEq α]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U₀ : Finset V} {d t s : ℕ}
    (ht : 1 ≤ t) (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    (J : Finset α) (g : α → V)
    (hmem : ∀ i ∈ J, g i ∈ U₀)
    (hinj : ∀ i ∈ J, ∀ j ∈ J, g i = g j → i = j)
    (hcard : tplR d t s ≤ J.card) :
    ∃ I' ⊆ J, I'.card = s ∧ ∀ i ∈ I', ∀ j ∈ I', ¬ G.Adj (g i) (g j) := by
  have hpos : 1 ≤ (d + 1) * t := Nat.mul_pos (Nat.succ_pos d) ht
  have heq : ((d + 1) * t - 1) + 1 = (d + 1) * t := by omega
  have hcf : G.CliqueFreeOn (U₀ : Set V) (((d + 1) * t - 1) + 1) := by
    rw [heq]
    exact cliqueFreeOn_of_not_hasCore hnoCore
  have hcard' : ramseyNum (((d + 1) * t - 1) + 1) s ≤ J.card := by
    rw [heq]
    exact hcard
  exact indep_index_of_cliqueFreeOn hcf J g hmem hinj hcard'

private def Nice3 {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  Nice2 Tseq I ∧
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ v ∈ (Tseq i).core.verts, ∀ p : Fin d,
    (((Tseq j).core.part p).filter (G.Adj v)).card < s ^ 3 * t ^ (s - 1)

private lemma colorable_nice2_of_nice3 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t wBase n M : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (h2 : Nice2 Tseq I)
    (h3col : ∀ J ⊆ I, Nice3 Tseq J → ColorableOn G (seqSupp Tseq J) M) :
    ColorableOn G (seqSupp Tseq I) ((2 * (d * (wBase * t) * (s - 1)) + 1) * M) := by
  classical
  let D : Fin n → Fin n → Prop := fun i j =>
    ∃ v ∈ (Tseq i).core.verts, ∃ p : Fin d,
      s ^ 3 * t ^ (s - 1) ≤ (((Tseq j).core.part p).filter (G.Adj v)).card
  have hout : ∀ i ∈ I, (I.filter (fun j => j ≠ i ∧ D i j)).card ≤ d * (wBase * t) * (s - 1) := by
    intro i hi
    let F : V → Finset (Fin n) := fun v =>
      I.filter (fun j => v ∉ (Tseq j).core.verts ∧
        ∃ p : Fin d, s ^ 3 * t ^ (s - 1) ≤ (((Tseq j).core.part p).filter (G.Adj v)).card)
    have hsub : I.filter (fun j => j ≠ i ∧ D i j) ⊆ ((Tseq i).core.verts).biUnion F := by
      intro j hj
      obtain ⟨hjI, hji, v, hvCi, p, hp⟩ := Finset.mem_filter.mp hj
      have hvPi : v ∈ (Tseq i).P := (Tseq i).verts_sub_P hvCi
      have hvNotPj : v ∉ (Tseq j).P := mem_P_unique h2.1.1 hi hjI hji.symm hvPi
      have hvNotCj : v ∉ (Tseq j).core.verts := fun h => hvNotPj ((Tseq j).verts_sub_P h)
      exact Finset.mem_biUnion.mpr ⟨v, hvCi, Finset.mem_filter.mpr ⟨hjI, hvNotCj, p, hp⟩⟩
    calc (I.filter (fun j => j ≠ i ∧ D i j)).card
        ≤ (((Tseq i).core.verts).biUnion F).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ (Tseq i).core.verts, (F v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ (Tseq i).core.verts, (s - 1) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hvSupp : v ∈ seqSupp Tseq I :=
            Finset.mem_biUnion.mpr ⟨i, hi, (Tseq i).verts_sub_P hv⟩
          have hlt : (F v).card < s := h2.2 v hvSupp
          omega
      _ = ((Tseq i).core.verts).card * (s - 1) := by simp
      _ = d * (wBase * t) * (s - 1) := by rw [(Tseq i).core.verts_card]
  refine colorableOn_of_digraph_blocks I (fun i => (Tseq i).P) D
    (d * (wBase * t) * (s - 1)) M hout fun J hJI hind => h3col J hJI ⟨nice2_mono hJI h2, ?_⟩
  intro i hi j hj hij v hv p
  exact lt_of_not_ge fun hp => hind i hi j hj hij ⟨v, hv, p, hp⟩

private def Nice4 {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  Nice3 Tseq I ∧
  ∀ v ∈ seqSupp Tseq I,
    (I.filter (fun i => v ∉ (Tseq i).P ∧
      ∃ x ∈ (Tseq i).core.verts, G.Adj v x)).card < tplR4 d t s

private lemma nice4_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I₁ I₂ : Finset (Fin n)}
    (hsub : I₁ ⊆ I₂) (h : Nice4 Tseq I₂) : Nice4 Tseq I₁ := by
  refine ⟨⟨nice2_mono hsub h.1.1, fun i hi j hj => h.1.2 i (hsub hi) j (hsub hj)⟩, fun v hv => ?_⟩
  have hv₂ : v ∈ seqSupp Tseq I₂ := by
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨i, hsub hi, hvi⟩
  exact lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _ hsub)) (h.2 v hv₂)

private lemma nice3_imp_nice4 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t n : ℕ}
    (hs : 2 ≤ s) (hd : 2 ≤ d) (ht : 1 ≤ t)
    (hnoTree : ¬ HasModelTreeOn G U₀ s)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    {Tseq : Fin n → Template G U₀ s d t (tplWBase s t)} {I : Finset (Fin n)}
    (h3 : Nice3 Tseq I) : Nice4 Tseq I := by
  refine ⟨h3, fun v hv => ?_⟩
  by_contra hge
  let NC := I.filter (fun i => v ∉ (Tseq i).P ∧ ∃ x ∈ (Tseq i).core.verts, G.Adj v x)
  have hNC_ge : tplR d t s + s ≤ NC.card := le_of_not_gt hge
  let BadV := I.filter (fun i => v ∉ (Tseq i).core.verts ∧
    ∃ p : Fin d, s ^ 3 * t ^ (s - 1) ≤ (((Tseq i).core.part p).filter (G.Adj v)).card)
  have hBadV_lt : BadV.card < s := h3.1.2 v hv
  let I₁ := NC \ BadV
  have hI₁_card : tplR d t s ≤ I₁.card := by
    have hsub : NC ⊆ I₁ ∪ BadV := fun x hx => by
      by_cases hxB : x ∈ BadV
      · exact Finset.mem_union_right _ hxB
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  classical
  let a₀ : Fin n → V := fun i =>
    if hi : i ∈ I₁ then
      Classical.choose (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2.2
    else v
  have ha₀_spec : ∀ i ∈ I₁, a₀ i ∈ (Tseq i).core.verts ∧ G.Adj v (a₀ i) := by
    intro i hi
    dsimp [a₀]
    rw [dif_pos hi]
    exact Classical.choose_spec (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2.2
  have ha₀_U : ∀ i ∈ I₁, a₀ i ∈ U₀ :=
    fun i hi => (Tseq i).core.verts_sub (ha₀_spec i hi).1
  have ha₀_inj : ∀ i ∈ I₁, ∀ j ∈ I₁, a₀ i = a₀ j → i = j := by
    intro i hi j hj heq
    by_contra hij
    have hiI : i ∈ I := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1
    have hjI : j ∈ I := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).1
    have haiP : a₀ i ∈ (Tseq i).P := (Tseq i).verts_sub_P (ha₀_spec i hi).1
    have hajP : a₀ j ∈ (Tseq j).P := (Tseq j).verts_sub_P (ha₀_spec j hj).1
    rw [heq] at haiP
    exact mem_P_unique h3.1.1.1 hjI hiI (Ne.symm hij) hajP haiP
  obtain ⟨I₂, hI₂sub, hI₂card, ha₀_indep⟩ :=
    indep_index_of_no_hasCore ht hnoCore I₁ a₀ ha₀_U ha₀_inj hI₁_card
  let emb := I₂.orderEmbOfFin hI₂card
  let idx : Fin s → Fin n := fun r => emb ⟨s - 1 - r.val, by omega⟩
  have hidx_I₂ : ∀ r : Fin s, idx r ∈ I₂ :=
    fun r => Finset.orderEmbOfFin_mem I₂ hI₂card _
  have hidx_I₁ : ∀ r : Fin s, idx r ∈ I₁ :=
    fun r => hI₂sub (hidx_I₂ r)
  have hidx_I : ∀ r : Fin s, idx r ∈ I :=
    fun r => (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hidx_I₁ r)).1).1
  have hidx_anti : ∀ r₁ r₂ : Fin s, r₁ < r₂ → idx r₂ < idx r₁ := by
    intro r₁ r₂ hlt
    exact emb.strictMono (by
      change s - 1 - r₂.val < s - 1 - r₁.val
      have : r₁.val < r₂.val := hlt
      omega)
  have hidx_inj : Function.Injective idx := by
    intro r₁ r₂ heq
    have hval := congr_arg Fin.val (emb.injective heq)
    dsimp at hval
    exact Fin.ext (by omega)
  have hex_pA : ∀ r : Fin s, ∃ p : Fin d, a₀ (idx r) ∈ (Tseq (idx r)).core.part p := by
    intro r
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp (ha₀_spec (idx r) (hidx_I₁ r)).1
    exact ⟨p, hp⟩
  choose pA hpA using hex_pA
  let pB : Fin s → Fin d := fun r => if (pA r).val = 0 then ⟨1, hd⟩ else ⟨0, by omega⟩
  have hpB_ne : ∀ r : Fin s, pA r ≠ pB r := by
    intro r
    by_cases hp0 : (pA r).val = 0
    · dsimp [pB]; rw [if_pos hp0]
      intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
    · dsimp [pB]; rw [if_neg hp0]
      intro heq; have := congr_arg Fin.val heq; dsimp at this; omega
  have hw_bound :
      s + (s - 1) * s * (s * t ^ (s - 1)) + s * (s ^ 3 * t ^ (s - 1)) ≤ tplWBase s t * t := by
    have hwb_le_w : tplWBase s t ≤ tplWBase s t * t := Nat.le_mul_of_pos_right _ ht
    have h1_le : (s - 1) * s ≤ (s + 1) * (s + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2_le := Nat.mul_le_mul_right (s * t ^ (s - 1)) h1_le
    have hsum : s + (s - 1) * s * (s * t ^ (s - 1)) + s * (s ^ 3 * t ^ (s - 1)) ≤ tplWBase s t := by
      dsimp [tplWBase]
      omega
    exact le_trans hsum hwb_le_w
  have hstep : ∀ m : ℕ, ∀ (hm : m ≤ s),
      ∃ b : Fin m → Fin s → V,
        (∀ r : Fin m, ∀ j : Fin s,
          b r j ∈ (Tseq (idx ⟨r.val, by omega⟩)).core.part (pB ⟨r.val, by omega⟩)) ∧
        (∀ r : Fin m, Function.Injective (b r)) ∧
        (∀ r : Fin m, ∀ j : Fin s, ¬ G.Adj v (b r j)) ∧
        (∀ r : Fin m, ∀ r' : Fin s, r' ≠ ⟨r.val, by omega⟩ → ∀ j : Fin s,
          ¬ G.Adj (a₀ (idx r')) (b r j)) ∧
        (∀ r₁ r₂ : Fin m, r₁ < r₂ → ∀ j₁ j₂ : Fin s, ¬ G.Adj (b r₁ j₁) (b r₂ j₂)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨Fin.elim0, fun r => r.elim0, fun r => r.elim0,
        fun r => r.elim0, fun r => r.elim0, fun r => r.elim0⟩
    | succ m ih =>
      intro hm
      obtain ⟨b, hb_mem, hb_inj, hb_nv, hb_na, hbb_na⟩ := ih (by omega)
      let rNew : Fin s := ⟨m, hm⟩
      let Bcur := (Tseq (idx rNew)).core.part (pB rNew)
      let X₁ : Finset V :=
        insert v (((Finset.univ : Finset (Fin s)).erase rNew).image (fun r => a₀ (idx r)))
      have hX₁_card : X₁.card ≤ s := by
        calc X₁.card
            ≤ (((Finset.univ : Finset (Fin s)).erase rNew).image (fun r => a₀ (idx r))).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ ((Finset.univ : Finset (Fin s)).erase rNew).card + 1 :=
              Nat.add_le_add_right Finset.card_image_le 1
          _ = (s - 1) + 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          _ = s := by omega
      have hX₁_deg : ∀ u ∈ X₁, (Bcur.filter (G.Adj u)).card ≤ s ^ 3 * t ^ (s - 1) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with huv | huImg
        · rw [huv]
          have hi₁ := hidx_I₁ rNew
          obtain ⟨hiNC, hiNotBad⟩ := Finset.mem_sdiff.mp hi₁
          have hvNotP : v ∉ (Tseq (idx rNew)).P := (Finset.mem_filter.mp hiNC).2.1
          have hvNotC : v ∉ (Tseq (idx rNew)).core.verts :=
            fun h => hvNotP ((Tseq (idx rNew)).verts_sub_P h)
          by_contra hgt
          have hle_deg : s ^ 3 * t ^ (s - 1) ≤ (Bcur.filter (G.Adj v)).card := by omega
          exact hiNotBad (Finset.mem_filter.mpr ⟨hidx_I rNew, hvNotC, pB rNew, hle_deg⟩)
        · obtain ⟨r', hr'er, rfl⟩ := Finset.mem_image.mp huImg
          have hr'ne : r' ≠ rNew := (Finset.mem_erase.mp hr'er).1
          have hidx_ne : idx r' ≠ idx rNew := fun h => hr'ne (hidx_inj h)
          exact le_of_lt (h3.2 (idx r') (hidx_I r') (idx rNew) (hidx_I rNew) hidx_ne
            (a₀ (idx r')) (ha₀_spec (idx r') (hidx_I₁ r')).1 (pB rNew))
      let k₁ := s + (s - 1) * s * (s * t ^ (s - 1))
      let S₁ := Bcur.filter (fun z => ∀ u ∈ X₁, ¬ G.Adj u z)
      have hS₁_card : k₁ ≤ S₁.card := by
        refine card_sdiff_adj_ge Bcur X₁ k₁ (s ^ 3 * t ^ (s - 1)) hX₁_deg ?_
        have hBcard : Bcur.card = tplWBase s t * t := (Tseq (idx rNew)).core.part_card (pB rNew)
        have hmul := Nat.mul_le_mul_right (s ^ 3 * t ^ (s - 1)) hX₁_card
        dsimp [k₁]
        omega
      let X₂ : Finset V := (Finset.univ : Finset (Fin m × Fin s)).image (fun p => b p.1 p.2)
      have hX₂_card : X₂.card ≤ (s - 1) * s := by
        have hc : X₂.card ≤ m * s := le_trans Finset.card_image_le (by simp)
        exact le_trans hc (Nat.mul_le_mul_right s (by omega))
      have hX₂_deg : ∀ u ∈ X₂, (S₁.filter (G.Adj u)).card ≤ s * t ^ (s - 1) := by
        intro u hu
        obtain ⟨⟨r, j⟩, _, rfl⟩ := Finset.mem_image.mp hu
        let r' : Fin s := ⟨r.val, by omega⟩
        have hr_lt : r' < rNew := r.isLt
        have huP : b r j ∈ (Tseq (idx r')).P :=
          (Tseq (idx r')).verts_sub_P ((Tseq (idx r')).core.part_sub_verts _ (hb_mem r j))
        have hlt := nice1_lt_adj h3.1.1 (hidx_I rNew) (hidx_I r') (hidx_anti r' rNew hr_lt)
          huP (pB rNew)
        exact le_trans
          (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
          (le_of_lt hlt)
      have hS₂_card : s ≤ (S₁.filter (fun z => ∀ u ∈ X₂, ¬ G.Adj u z)).card := by
        refine card_sdiff_adj_ge S₁ X₂ s (s * t ^ (s - 1)) hX₂_deg ?_
        calc s + X₂.card * (s * t ^ (s - 1))
            ≤ s + ((s - 1) * s) * (s * t ^ (s - 1)) :=
              Nat.add_le_add_left (Nat.mul_le_mul_right _ hX₂_card) s
          _ = k₁ := rfl
          _ ≤ S₁.card := hS₁_card
      obtain ⟨bNew, hbNew_inj, hbNew_f⟩ :=
        exists_fin_emb_of_card (S₁.filter (fun z => ∀ u ∈ X₂, ¬ G.Adj u z)) hS₂_card
      let b' : Fin (m + 1) → Fin s → V := fun r => if hr : r.val < m then b ⟨r.val, hr⟩ else bNew
      refine ⟨b', ?_, ?_, ?_, ?_, ?_⟩
      · intro r j
        dsimp [b']
        split_ifs with hr
        · exact hb_mem ⟨r.val, hr⟩ j
        · have hreq : (⟨r.val, by omega⟩ : Fin s) = rNew := Fin.ext (by dsimp [rNew]; omega)
          rw [hreq]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hbNew_f j)).1).1
      · intro r
        dsimp [b']
        split_ifs with hr
        · exact hb_inj ⟨r.val, hr⟩
        · exact hbNew_inj
      · intro r j
        dsimp [b']
        split_ifs with hr
        · exact hb_nv ⟨r.val, hr⟩ j
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hbNew_f j)).1).2 v
            (Finset.mem_insert_self _ _)
      · intro r r' hr'ne j
        dsimp [b']
        split_ifs with hr
        · exact hb_na ⟨r.val, hr⟩ r' hr'ne j
        · have hreq : (⟨r.val, by omega⟩ : Fin s) = rNew := Fin.ext (by dsimp [rNew]; omega)
          rw [hreq] at hr'ne
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hbNew_f j)).1).2 (a₀ (idx r'))
            (Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨r', Finset.mem_erase.mpr ⟨hr'ne, Finset.mem_univ _⟩, rfl⟩))
      · intro r₁ r₂ hr₁₂ j₁ j₂
        dsimp [b']
        split_ifs with h1r h2r h2r
        · exact hbb_na ⟨r₁.val, h1r⟩ ⟨r₂.val, h2r⟩ hr₁₂ j₁ j₂
        · exact (Finset.mem_filter.mp (hbNew_f j₂)).2 (b ⟨r₁.val, h1r⟩ j₁)
            (Finset.mem_image.mpr ⟨(⟨r₁.val, h1r⟩, j₁), Finset.mem_univ _, rfl⟩)
        · exfalso; have : r₁.val < r₂.val := hr₁₂; omega
        · exfalso; have : r₁.val < r₂.val := hr₁₂; omega
  obtain ⟨b, hb_mem, hb_inj, hb_nv, hb_na, hbb_na⟩ := hstep s le_rfl
  apply hnoTree
  refine ⟨v, fun r => a₀ (idx r), b, seqSupp_sub Tseq I hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ha₀_U (idx r) (hidx_I₁ r)
  · intro r j
    exact (Tseq (idx r)).core.part_sub (pB r) (hb_mem r j)
  · intro r j j' hjj' heq
    exact hjj' (hb_inj r heq)
  · intro r
    exact (ha₀_spec (idx r) (hidx_I₁ r)).2
  · intro r j
    exact hb_nv r j
  · intro r₁ r₂ _
    exact ha₀_indep (idx r₁) (hidx_I₂ r₁) (idx r₂) (hidx_I₂ r₂)
  · intro r₁ r₂ j
    constructor
    · intro hadj
      by_contra hne
      exact hb_na r₂ r₁ hne j hadj
    · rintro rfl
      exact (Tseq (idx r₁)).core.part_adj (pA r₁) (pB r₁) (hpB_ne r₁)
        (a₀ (idx r₁)) (hpA r₁) (b r₁ j) (hb_mem r₁ j)
  · intro r₁ j₁ r₂ j₂ _
    by_cases hr : r₁ = r₂
    · subst hr
      exact (Tseq (idx r₁)).core.part_indep (pB r₁) (b r₁ j₁) (hb_mem r₁ j₁) (b r₁ j₂) (hb_mem r₁ j₂)
    · rcases lt_or_gt_of_ne hr with hlt | hgt
      · exact hbb_na r₁ r₂ hlt j₁ j₂
      · exact fun h => hbb_na r₂ r₁ hgt j₂ j₁ h.symm

private def Nice5 {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  Nice4 Tseq I ∧
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ u ∈ (Tseq i).core.verts, ∀ v ∈ (Tseq j).core.verts, ¬ G.Adj u v

private lemma colorable_nice4_of_nice5 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t wBase n M : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (h4 : Nice4 Tseq I)
    (h5col : ∀ J ⊆ I, Nice5 Tseq J → ColorableOn G (seqSupp Tseq J) M) :
    ColorableOn G (seqSupp Tseq I) ((2 * (d * (wBase * t) * tplR4 d t s) + 1) * M) := by
  classical
  let D : Fin n → Fin n → Prop := fun i j =>
    ∃ u ∈ (Tseq i).core.verts, ∃ v ∈ (Tseq j).core.verts, G.Adj u v
  have hout : ∀ i ∈ I, (I.filter (fun j => j ≠ i ∧ D i j)).card ≤ d * (wBase * t) * tplR4 d t s := by
    intro i hi
    let F : V → Finset (Fin n) := fun u =>
      I.filter (fun j => u ∉ (Tseq j).P ∧ ∃ v ∈ (Tseq j).core.verts, G.Adj u v)
    have hsub : I.filter (fun j => j ≠ i ∧ D i j) ⊆ ((Tseq i).core.verts).biUnion F := by
      intro j hj
      obtain ⟨hjI, hji, u, huCi, v, hvCj, huv⟩ := Finset.mem_filter.mp hj
      have huPi : u ∈ (Tseq i).P := (Tseq i).verts_sub_P huCi
      have huNotPj : u ∉ (Tseq j).P := mem_P_unique h4.1.1.1.1 hi hjI hji.symm huPi
      exact Finset.mem_biUnion.mpr ⟨u, huCi, Finset.mem_filter.mpr ⟨hjI, huNotPj, v, hvCj, huv⟩⟩
    calc (I.filter (fun j => j ≠ i ∧ D i j)).card
        ≤ (((Tseq i).core.verts).biUnion F).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ (Tseq i).core.verts, (F u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ (Tseq i).core.verts, tplR4 d t s := by
          refine Finset.sum_le_sum fun u hu => ?_
          have huSupp : u ∈ seqSupp Tseq I :=
            Finset.mem_biUnion.mpr ⟨i, hi, (Tseq i).verts_sub_P hu⟩
          exact le_of_lt (h4.2 u huSupp)
      _ = ((Tseq i).core.verts).card * tplR4 d t s := by simp
      _ = d * (wBase * t) * tplR4 d t s := by rw [(Tseq i).core.verts_card]
  refine colorableOn_of_digraph_blocks I (fun i => (Tseq i).P) D
    (d * (wBase * t) * tplR4 d t s) M hout fun J hJI hind => h5col J hJI ⟨nice4_mono hJI h4, ?_⟩
  intro i hi j hj hij u hu v hv huv
  exact hind i hi j hj hij ⟨u, hu, v, hv, huv⟩

private def Nice6 {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  Nice5 Tseq I ∧
  ∀ v ∈ seqSupp Tseq I,
    (I.filter (fun i => v ∉ (Tseq i).P ∧ ∃ u ∈ (Tseq i).P, G.Adj v u)).card < tplR6 d t s

private lemma nice6_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    {Tseq : Fin n → Template G U₀ s d t wBase} {I₁ I₂ : Finset (Fin n)}
    (hsub : I₁ ⊆ I₂) (h : Nice6 Tseq I₂) : Nice6 Tseq I₁ := by
  refine ⟨⟨nice4_mono hsub h.1.1, fun i hi j hj => h.1.2 i (hsub hi) j (hsub hj)⟩, fun v hv => ?_⟩
  have hv₂ : v ∈ seqSupp Tseq I₂ := by
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨i, hsub hi, hvi⟩
  exact lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _ hsub)) (h.2 v hv₂)

private lemma nice5_imp_nice6 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t wBase n : ℕ}
    (ht : 1 ≤ t)
    (hnoTree : ¬ HasModelTreeOn G U₀ s)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (h5 : Nice5 Tseq I) : Nice6 Tseq I := by
  refine ⟨h5, fun v hv => ?_⟩
  by_contra hge
  let NP := I.filter (fun i => v ∉ (Tseq i).P ∧ ∃ u ∈ (Tseq i).P, G.Adj v u)
  let NC := I.filter (fun i => v ∉ (Tseq i).P ∧ ∃ x ∈ (Tseq i).core.verts, G.Adj v x)
  have hNC_lt : NC.card < tplR4 d t s := h5.1.2 v hv
  let I₁ := NP \ NC
  have hI₁_card : (2 * tplR4 d t s + 1) * tplR d t s ≤ I₁.card := by
    have hsub : NP ⊆ I₁ ∪ NC := fun x hx => by
      by_cases hxC : x ∈ NC
      · exact Finset.mem_union_right _ hxC
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxC⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    change ¬ NP.card < (2 * tplR4 d t s + 1) * tplR d t s + tplR4 d t s at hge
    omega
  classical
  let a₀ : Fin n → V := fun i =>
    if hi : i ∈ I₁ then
      Classical.choose (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2.2
    else v
  have ha₀_spec : ∀ i ∈ I₁, a₀ i ∈ (Tseq i).P ∧ G.Adj v (a₀ i) := by
    intro i hi
    dsimp [a₀]
    rw [dif_pos hi]
    exact Classical.choose_spec (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2.2
  have ha₀_notC : ∀ i ∈ I₁, a₀ i ∉ (Tseq i).core.verts := by
    intro i hi hmemC
    obtain ⟨hiNP, hiNotNC⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hiI, hvNotPi, _⟩ := Finset.mem_filter.mp hiNP
    exact hiNotNC (Finset.mem_filter.mpr ⟨hiI, hvNotPi, a₀ i, hmemC, (ha₀_spec i hi).2⟩)
  let D : Fin n → Fin n → Prop := fun i j =>
    ∃ x ∈ (Tseq j).core.verts, G.Adj (a₀ i) x
  have houtD : ∀ i ∈ I₁, (I₁.filter (fun j => j ≠ i ∧ D i j)).card ≤ tplR4 d t s := by
    intro i hi
    have hiI : i ∈ I := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1
    have hai_supp : a₀ i ∈ seqSupp Tseq I :=
      Finset.mem_biUnion.mpr ⟨i, hiI, (ha₀_spec i hi).1⟩
    have hsub : I₁.filter (fun j => j ≠ i ∧ D i j) ⊆
        I.filter (fun j => a₀ i ∉ (Tseq j).P ∧ ∃ x ∈ (Tseq j).core.verts, G.Adj (a₀ i) x) := by
      intro j hj
      obtain ⟨hjI₁, hji, hD⟩ := Finset.mem_filter.mp hj
      have hjI : j ∈ I := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hjI₁).1).1
      have hai_notPj : a₀ i ∉ (Tseq j).P :=
        mem_P_unique h5.1.1.1.1.1 hiI hjI hji.symm (ha₀_spec i hi).1
      exact Finset.mem_filter.mpr ⟨hjI, hai_notPj, hD⟩
    exact le_trans (Finset.card_le_card hsub) (le_of_lt (h5.1.2 (a₀ i) hai_supp))
  obtain ⟨I₂, hI₂sub, hI₂_mul, hind₂⟩ := exists_indep_of_digraph I₁ D (tplR4 d t s) houtD
  have hI₂_card : tplR d t s ≤ I₂.card :=
    Nat.le_of_mul_le_mul_left (le_trans hI₁_card hI₂_mul) (by omega)
  have ha₀_U : ∀ i ∈ I₂, a₀ i ∈ U₀ :=
    fun i hi => (Tseq i).P_sub (ha₀_spec i (hI₂sub hi)).1
  have ha₀_inj : ∀ i ∈ I₂, ∀ j ∈ I₂, a₀ i = a₀ j → i = j := by
    intro i hi j hj heq
    by_contra hij
    have hiI : i ∈ I := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hI₂sub hi)).1).1
    have hjI : j ∈ I := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hI₂sub hj)).1).1
    have haiP : a₀ i ∈ (Tseq i).P := (ha₀_spec i (hI₂sub hi)).1
    have hajP : a₀ j ∈ (Tseq j).P := (ha₀_spec j (hI₂sub hj)).1
    rw [heq] at haiP
    exact mem_P_unique h5.1.1.1.1.1 hjI hiI (Ne.symm hij) hajP haiP
  obtain ⟨I₃, hI₃sub, hI₃card, ha₀_indep⟩ :=
    indep_index_of_no_hasCore ht hnoCore I₂ a₀ ha₀_U ha₀_inj hI₂_card
  let idx := I₃.orderEmbOfFin hI₃card
  have hidx_I₃ : ∀ r : Fin s, idx r ∈ I₃ := fun _ => Finset.orderEmbOfFin_mem I₃ hI₃card _
  have hidx_I₂ : ∀ r : Fin s, idx r ∈ I₂ := fun r => hI₃sub (hidx_I₃ r)
  have hidx_I₁ : ∀ r : Fin s, idx r ∈ I₁ := fun r => hI₂sub (hidx_I₂ r)
  have hidx_I : ∀ r : Fin s, idx r ∈ I :=
    fun r => (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hidx_I₁ r)).1).1
  have hex_b : ∀ r : Fin s, ∃ (p : Fin d) (br : Fin s → V),
      Function.Injective br ∧
      ∀ j : Fin s, br j ∈ ((Tseq (idx r)).core.part p).filter (G.Adj (a₀ (idx r))) := by
    intro r
    have hi₁ := hidx_I₁ r
    obtain ⟨p, hp_card⟩ := (Tseq (idx r)).dense_part (a₀ (idx r))
      (Finset.mem_sdiff.mpr ⟨(ha₀_spec (idx r) hi₁).1, ha₀_notC (idx r) hi₁⟩)
    have hs_le : s ≤ (((Tseq (idx r)).core.part p).filter (G.Adj (a₀ (idx r)))).card :=
      le_trans (Nat.le_mul_of_pos_right s (Nat.one_le_pow _ _ ht)) hp_card
    obtain ⟨br, hbr_inj, hbr_mem⟩ :=
      exists_fin_emb_of_card (((Tseq (idx r)).core.part p).filter (G.Adj (a₀ (idx r)))) hs_le
    exact ⟨p, br, hbr_inj, hbr_mem⟩
  choose p_of b_of hb_inj hb_mem using hex_b
  apply hnoTree
  refine ⟨v, fun r => a₀ (idx r), b_of, seqSupp_sub Tseq I hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ha₀_U (idx r) (hidx_I₂ r)
  · intro r j
    exact (Tseq (idx r)).core.part_sub (p_of r) (Finset.mem_filter.mp (hb_mem r j)).1
  · intro r j j' hjj' heq
    exact hjj' (hb_inj r heq)
  · intro r
    exact (ha₀_spec (idx r) (hidx_I₁ r)).2
  · intro r j hadj
    obtain ⟨hiNP, hiNotNC⟩ := Finset.mem_sdiff.mp (hidx_I₁ r)
    obtain ⟨hiI, hvNotP, _⟩ := Finset.mem_filter.mp hiNP
    have hbC : b_of r j ∈ (Tseq (idx r)).core.verts :=
      (Tseq (idx r)).core.part_sub_verts (p_of r) (Finset.mem_filter.mp (hb_mem r j)).1
    exact hiNotNC (Finset.mem_filter.mpr ⟨hiI, hvNotP, b_of r j, hbC, hadj⟩)
  · intro r₁ r₂ _
    exact ha₀_indep (idx r₁) (hidx_I₃ r₁) (idx r₂) (hidx_I₃ r₂)
  · intro r₁ r₂ j
    constructor
    · intro hadj
      by_contra hne
      have hidx_ne : idx r₁ ≠ idx r₂ := fun h => hne (idx.injective h)
      have hbC : b_of r₂ j ∈ (Tseq (idx r₂)).core.verts :=
        (Tseq (idx r₂)).core.part_sub_verts (p_of r₂) (Finset.mem_filter.mp (hb_mem r₂ j)).1
      exact hind₂ (idx r₁) (hidx_I₂ r₁) (idx r₂) (hidx_I₂ r₂) hidx_ne ⟨b_of r₂ j, hbC, hadj⟩
    · rintro rfl
      exact (Finset.mem_filter.mp (hb_mem r₁ j)).2
  · intro r₁ j₁ r₂ j₂ _
    by_cases hr : r₁ = r₂
    · subst hr
      exact (Tseq (idx r₁)).core.part_indep (p_of r₁)
        (b_of r₁ j₁) (Finset.mem_filter.mp (hb_mem r₁ j₁)).1
        (b_of r₁ j₂) (Finset.mem_filter.mp (hb_mem r₁ j₂)).1
    · have hidx_ne : idx r₁ ≠ idx r₂ := fun h => hr (idx.injective h)
      exact h5.2 (idx r₁) (hidx_I r₁) (idx r₂) (hidx_I r₂) hidx_ne
        (b_of r₁ j₁) ((Tseq (idx r₁)).core.part_sub_verts _ (Finset.mem_filter.mp (hb_mem r₁ j₁)).1)
        (b_of r₂ j₂) ((Tseq (idx r₂)).core.part_sub_verts _ (Finset.mem_filter.mp (hb_mem r₂ j₂)).1)

private def Nice7 {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U₀ : Finset V} {s d t wBase n : ℕ}
    (Tseq : Fin n → Template G U₀ s d t wBase) (I : Finset (Fin n)) : Prop :=
  Nice6 Tseq I ∧
  ∀ i ∈ I,
    ((I.erase i).filter (fun j =>
      ∃ v ∈ (Tseq i).P, tplR d t s ≤ (((Tseq j).P).filter (G.Adj v)).card)).card <
        tplR7 d t s (wBase * t)

private lemma nice6_imp_nice7 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t wBase n : ℕ}
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ht : 1 ≤ t) (hwBase : 1 ≤ wBase)
    (hnoTree : ¬ HasModelTreeOn G U₀ s)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (h6 : Nice6 Tseq I) : Nice7 Tseq I := by
  refine ⟨h6, fun h hhI => ?_⟩
  by_contra hge
  let w := wBase * t
  let I₁ := (I.erase h).filter (fun j =>
    ∃ v ∈ (Tseq h).P, tplR d t s ≤ (((Tseq j).P).filter (G.Adj v)).card)
  have hI₁_card : (2 * tplR6 d t s + 1) * tplL2 d t s w ≤ I₁.card := by
    change ¬ I₁.card < (2 * tplR6 d t s + 1) * tplL2 d t s w at hge
    omega
  have hI₁_ne_h : ∀ j ∈ I₁, j ≠ h ∧ j ∈ I :=
    fun j hj => Finset.mem_erase.mp (Finset.mem_filter.mp hj).1
  classical
  obtain ⟨v_dummy, _⟩ : (Tseq h).P.Nonempty := by
    have hc : 1 ≤ (Tseq h).core.verts.card := by
      rw [(Tseq h).core.verts_card]
      exact Nat.mul_pos hd (Nat.mul_pos hwBase ht)
    exact Finset.Nonempty.mono (Tseq h).verts_sub_P (Finset.card_pos.mp hc)
  let a₀ : Fin n → V := fun j =>
    if hj : j ∈ I₁ then Classical.choose (Finset.mem_filter.mp hj).2 else v_dummy
  have ha₀_spec : ∀ j ∈ I₁, a₀ j ∈ (Tseq h).P ∧
      tplR d t s ≤ (((Tseq j).P).filter (G.Adj (a₀ j))).card := by
    intro j hj
    simp only [a₀, dif_pos hj]
    exact Classical.choose_spec (Finset.mem_filter.mp hj).2
  let D : Fin n → Fin n → Prop := fun i j => ∃ z ∈ (Tseq j).P, G.Adj (a₀ i) z
  have houtD : ∀ i ∈ I₁, (I₁.filter (fun j => j ≠ i ∧ D i j)).card ≤ tplR6 d t s := by
    intro i hi
    have hai_Ph : a₀ i ∈ (Tseq h).P := (ha₀_spec i hi).1
    have hai_supp : a₀ i ∈ seqSupp Tseq I := Finset.mem_biUnion.mpr ⟨h, hhI, hai_Ph⟩
    have hsub : I₁.filter (fun j => j ≠ i ∧ D i j) ⊆
        I.filter (fun j => a₀ i ∉ (Tseq j).P ∧ ∃ z ∈ (Tseq j).P, G.Adj (a₀ i) z) := by
      intro j hj
      obtain ⟨hjI₁, _, hD⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjh, hjI⟩ := hI₁_ne_h j hjI₁
      have hai_notPj : a₀ i ∉ (Tseq j).P :=
        mem_P_unique h6.1.1.1.1.1.1 hhI hjI hjh.symm hai_Ph
      exact Finset.mem_filter.mpr ⟨hjI, hai_notPj, hD⟩
    exact le_trans (Finset.card_le_card hsub) (le_of_lt (h6.2 (a₀ i) hai_supp))
  obtain ⟨I₂, hI₂sub, hI₂_mul, hind₂⟩ := exists_indep_of_digraph I₁ D (tplR6 d t s) houtD
  have hI₂_card : d * w * tplL4 d t s + d * w ≤ I₂.card := by
    have hle := Nat.le_of_mul_le_mul_left (le_trans hI₁_card hI₂_mul) (by omega)
    simpa [tplL2] using hle
  have ha₀_inj_I₂ : ∀ i ∈ I₂, ∀ j ∈ I₂, a₀ i = a₀ j → i = j := by
    intro i hi j hj heq
    by_contra hij
    have hRpos : 1 ≤ (((Tseq i).P).filter (G.Adj (a₀ i))).card :=
      le_trans (tplR_pos ht (by omega)) (ha₀_spec i (hI₂sub hi)).2
    obtain ⟨z, hz_f⟩ := Finset.card_pos.mp hRpos
    obtain ⟨hzPi, haz⟩ := Finset.mem_filter.mp hz_f
    rw [heq] at haz
    exact hind₂ j hj i hi (Ne.symm hij) ⟨z, hzPi, haz⟩
  let I₂C := I₂.filter (fun i => a₀ i ∈ (Tseq h).core.verts)
  have hI₂C_card : I₂C.card ≤ d * w := by
    have hinj_on : Set.InjOn a₀ (I₂C : Set (Fin n)) := fun i hi j hj hij =>
      ha₀_inj_I₂ i (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
        j (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1 hij
    have himg_sub : I₂C.image a₀ ⊆ (Tseq h).core.verts := by
      intro x hx
      obtain ⟨i, hiC, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hiC).2
    calc I₂C.card
        = (I₂C.image a₀).card := (Finset.card_image_of_injOn hinj_on).symm
      _ ≤ (Tseq h).core.verts.card := Finset.card_le_card himg_sub
      _ = d * w := (Tseq h).core.verts_card
  let I₃ := I₂.filter (fun i => a₀ i ∉ (Tseq h).core.verts)
  have hI₃_card : d * w * tplL4 d t s ≤ I₃.card := by
    have hsub : I₂ ⊆ I₃ ∪ I₂C := fun i hi => by
      by_cases hiC : a₀ i ∈ (Tseq h).core.verts
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hiC⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hiC⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hex_c : ∀ i ∈ I₃, ∃ x ∈ (Tseq h).core.verts, G.Adj (a₀ i) x := by
    intro i hi
    obtain ⟨hiI₂, hai_notC⟩ := Finset.mem_filter.mp hi
    obtain ⟨p, hp_card⟩ := (Tseq h).dense_part (a₀ i)
      (Finset.mem_sdiff.mpr ⟨(ha₀_spec i (hI₂sub hiI₂)).1, hai_notC⟩)
    have hpos : 1 ≤ (((Tseq h).core.part p).filter (G.Adj (a₀ i))).card :=
      le_trans (Nat.mul_pos (by omega) (Nat.one_le_pow _ _ ht)) hp_card
    obtain ⟨x, hx_f⟩ := Finset.card_pos.mp hpos
    obtain ⟨hxp, hax⟩ := Finset.mem_filter.mp hx_f
    exact ⟨x, (Tseq h).core.part_sub_verts p hxp, hax⟩
  let c_of : Fin n → V := fun i =>
    if hi : i ∈ I₃ then Classical.choose (hex_c i hi) else v_dummy
  have hc_of_spec : ∀ i ∈ I₃, c_of i ∈ (Tseq h).core.verts ∧ G.Adj (a₀ i) (c_of i) := by
    intro i hi
    dsimp [c_of]
    rw [dif_pos hi]
    exact Classical.choose_spec (hex_c i hi)
  have hex_c₀ : ∃ c₀ ∈ (Tseq h).core.verts,
      tplL4 d t s ≤ (I₃.filter (fun i => c_of i = c₀)).card := by
    by_contra hall
    have hsum : I₃.card = ∑ c₀ ∈ (Tseq h).core.verts, (I₃.filter (fun i => c_of i = c₀)).card :=
      Finset.card_eq_sum_card_fiberwise fun i hi => (hc_of_spec i hi).1
    have hC_ne : (Tseq h).core.verts.Nonempty := by
      rw [← Finset.card_pos, (Tseq h).core.verts_card]
      exact Nat.mul_pos hd (Nat.mul_pos hwBase ht)
    have hlt_sum : ∑ c₀ ∈ (Tseq h).core.verts, (I₃.filter (fun i => c_of i = c₀)).card <
        ∑ _c₀ ∈ (Tseq h).core.verts, tplL4 d t s := by
      refine Finset.sum_lt_sum_of_nonempty hC_ne fun c₀ hc₀ => ?_
      exact lt_of_not_ge fun hge_c => hall ⟨c₀, hc₀, hge_c⟩
    rw [← hsum, Finset.sum_const, (Tseq h).core.verts_card, smul_eq_mul] at hlt_sum
    change d * (wBase * t) * tplL4 d t s ≤ I₃.card at hI₃_card
    omega
  obtain ⟨c₀, hc₀C, hI₄_card⟩ := hex_c₀
  let I₄ := I₃.filter (fun i => c_of i = c₀)
  let BadC := I₄.filter (fun i => ∃ z ∈ (Tseq i).P, G.Adj c₀ z)
  have hBadC_lt : BadC.card < tplR6 d t s := by
    have hc₀_supp : c₀ ∈ seqSupp Tseq I :=
      Finset.mem_biUnion.mpr ⟨h, hhI, (Tseq h).verts_sub_P hc₀C⟩
    have hsub : BadC ⊆ I.filter (fun i => c₀ ∉ (Tseq i).P ∧ ∃ z ∈ (Tseq i).P, G.Adj c₀ z) := by
      intro i hi
      obtain ⟨hiI₄, hcz⟩ := Finset.mem_filter.mp hi
      have hiI₁ : i ∈ I₁ := hI₂sub (Finset.mem_filter.mp (Finset.mem_filter.mp hiI₄).1).1
      obtain ⟨hih, hiI⟩ := hI₁_ne_h i hiI₁
      have hc₀_notPi : c₀ ∉ (Tseq i).P :=
        mem_P_unique h6.1.1.1.1.1.1 hhI hiI hih.symm ((Tseq h).verts_sub_P hc₀C)
      exact Finset.mem_filter.mpr ⟨hiI, hc₀_notPi, hcz⟩
    exact lt_of_le_of_lt (Finset.card_le_card hsub) (h6.2 c₀ hc₀_supp)
  let I₅ := I₄ \ BadC
  have hI₅_card : (2 * (s * tplR6 d t s) + 1) * tplR d t s ≤ I₅.card := by
    have hsub : I₄ ⊆ I₅ ∪ BadC := fun i hi => by
      by_cases hiB : i ∈ BadC
      · exact Finset.mem_union_right _ hiB
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hiB⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    change (2 * (s * tplR6 d t s) + 1) * tplR d t s + tplR6 d t s ≤ I₄.card at hI₄_card
    omega
  have hI₅_sub_I₁ : I₅ ⊆ I₁ :=
    Finset.sdiff_subset.trans
      ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans hI₂sub))
  have hex_Y : ∀ i ∈ I₅, ∃ br : Fin s → V,
      Function.Injective br ∧
      (∀ m : Fin s, br m ∈ ((Tseq i).P).filter (G.Adj (a₀ i))) ∧
      (∀ m₁ m₂ : Fin s, ¬ G.Adj (br m₁) (br m₂)) := by
    intro i hi
    let Ni := ((Tseq i).P).filter (G.Adj (a₀ i))
    have hNi_card : ramseyNum ((d + 1) * t) s ≤ Ni.card := (ha₀_spec i (hI₅_sub_I₁ hi)).2
    rcases ramsey_clique_or_indep G ((d + 1) * t) s Ni hNi_card with
      ⟨K, hKNi, hKc, hKcl⟩ | ⟨Y, hYNi, hYc, hYi⟩
    · exfalso
      have hKU₀ : (K : Set V) ⊆ (U₀ : Set V) := by
        intro x hx
        exact Finset.mem_coe.mpr
          ((Tseq i).P_sub (Finset.mem_filter.mp (hKNi (Finset.mem_coe.mp hx))).1)
      exact cliqueFreeOn_of_not_hasCore hnoCore hKU₀ ⟨hKcl, hKc⟩
    · obtain ⟨br, hbr_inj, hbr_Y⟩ := exists_fin_emb_of_card Y (le_of_eq hYc.symm)
      exact ⟨br, hbr_inj, fun m => hYNi (hbr_Y m), fun m₁ m₂ => hYi _ (hbr_Y m₁) _ (hbr_Y m₂)⟩
  let b₀ : Fin n → Fin s → V := fun i =>
    if hi : i ∈ I₅ then Classical.choose (hex_Y i hi) else fun _ => v_dummy
  have hb₀_spec : ∀ i ∈ I₅,
      Function.Injective (b₀ i) ∧
      (∀ m : Fin s, b₀ i m ∈ ((Tseq i).P).filter (G.Adj (a₀ i))) ∧
      (∀ m₁ m₂ : Fin s, ¬ G.Adj (b₀ i m₁) (b₀ i m₂)) := by
    intro i hi
    dsimp [b₀]
    rw [dif_pos hi]
    exact Classical.choose_spec (hex_Y i hi)
  let D' : Fin n → Fin n → Prop := fun i j => ∃ m₁ m₂ : Fin s, G.Adj (b₀ i m₁) (b₀ j m₂)
  have houtD' : ∀ i ∈ I₅, (I₅.filter (fun j => j ≠ i ∧ D' i j)).card ≤ s * tplR6 d t s := by
    intro i hi
    have hiI : i ∈ I := (hI₁_ne_h i (hI₅_sub_I₁ hi)).2
    let F : Fin s → Finset (Fin n) := fun m₁ =>
      I.filter (fun j => b₀ i m₁ ∉ (Tseq j).P ∧ ∃ z ∈ (Tseq j).P, G.Adj (b₀ i m₁) z)
    have hsub : I₅.filter (fun j => j ≠ i ∧ D' i j) ⊆ (Finset.univ : Finset (Fin s)).biUnion F := by
      intro j hj
      obtain ⟨hjI₅, hji, m₁, m₂, hadj⟩ := Finset.mem_filter.mp hj
      have hjI : j ∈ I := (hI₁_ne_h j (hI₅_sub_I₁ hjI₅)).2
      have hbiPi : b₀ i m₁ ∈ (Tseq i).P := (Finset.mem_filter.mp ((hb₀_spec i hi).2.1 m₁)).1
      have hbjPj : b₀ j m₂ ∈ (Tseq j).P := (Finset.mem_filter.mp ((hb₀_spec j hjI₅).2.1 m₂)).1
      have hbi_notPj : b₀ i m₁ ∉ (Tseq j).P :=
        mem_P_unique h6.1.1.1.1.1.1 hiI hjI hji.symm hbiPi
      exact Finset.mem_biUnion.mpr ⟨m₁, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hjI, hbi_notPj, b₀ j m₂, hbjPj, hadj⟩⟩
    calc (I₅.filter (fun j => j ≠ i ∧ D' i j)).card
        ≤ ((Finset.univ : Finset (Fin s)).biUnion F).card := Finset.card_le_card hsub
      _ ≤ ∑ m₁ : Fin s, (F m₁).card := Finset.card_biUnion_le
      _ ≤ ∑ _m₁ : Fin s, tplR6 d t s := by
          refine Finset.sum_le_sum fun m₁ _ => ?_
          have hbi_supp : b₀ i m₁ ∈ seqSupp Tseq I :=
            Finset.mem_biUnion.mpr ⟨i, hiI, (Finset.mem_filter.mp ((hb₀_spec i hi).2.1 m₁)).1⟩
          exact le_of_lt (h6.2 (b₀ i m₁) hbi_supp)
      _ = s * tplR6 d t s := by simp
  obtain ⟨I₆, hI₆sub, hI₆_mul, hind₆⟩ := exists_indep_of_digraph I₅ D' (s * tplR6 d t s) houtD'
  have hI₆_card : tplR d t s ≤ I₆.card :=
    Nat.le_of_mul_le_mul_left (le_trans hI₅_card hI₆_mul) (by omega)
  have hI₆_sub_I₂ : I₆ ⊆ I₂ :=
    hI₆sub.trans (Finset.sdiff_subset.trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))
  have ha₀_U : ∀ i ∈ I₆, a₀ i ∈ U₀ :=
    fun i hi => (Tseq h).P_sub (ha₀_spec i (hI₂sub (hI₆_sub_I₂ hi))).1
  have ha₀_inj_I₆ : ∀ i ∈ I₆, ∀ j ∈ I₆, a₀ i = a₀ j → i = j :=
    fun i hi j hj => ha₀_inj_I₂ i (hI₆_sub_I₂ hi) j (hI₆_sub_I₂ hj)
  obtain ⟨I₇, hI₇sub, hI₇card, ha₀_indep⟩ :=
    indep_index_of_no_hasCore ht hnoCore I₆ a₀ ha₀_U ha₀_inj_I₆ hI₆_card
  let idx := I₇.orderEmbOfFin hI₇card
  have hidx_I₇ : ∀ r : Fin s, idx r ∈ I₇ := fun _ => Finset.orderEmbOfFin_mem I₇ hI₇card _
  have hidx_I₆ : ∀ r : Fin s, idx r ∈ I₆ := fun r => hI₇sub (hidx_I₇ r)
  have hidx_I₅ : ∀ r : Fin s, idx r ∈ I₅ := fun r => hI₆sub (hidx_I₆ r)
  have hidx_I₂ : ∀ r : Fin s, idx r ∈ I₂ := fun r => hI₆_sub_I₂ (hidx_I₆ r)
  apply hnoTree
  refine ⟨c₀, fun r => a₀ (idx r), fun r => b₀ (idx r),
    (Tseq h).core.verts_sub hc₀C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ha₀_U (idx r) (hidx_I₆ r)
  · intro r m
    exact (Tseq (idx r)).P_sub
      (Finset.mem_filter.mp ((hb₀_spec (idx r) (hidx_I₅ r)).2.1 m)).1
  · intro r m m' hmm' heq
    exact hmm' ((hb₀_spec (idx r) (hidx_I₅ r)).1 heq)
  · intro r
    have hi₄ : idx r ∈ I₄ := (Finset.mem_sdiff.mp (hidx_I₅ r)).1
    obtain ⟨hi₃, hc_eq⟩ := Finset.mem_filter.mp hi₄
    rw [← hc_eq]
    exact ((hc_of_spec (idx r) hi₃).2).symm
  · intro r m hadj
    obtain ⟨hi₄, hiNotBad⟩ := Finset.mem_sdiff.mp (hidx_I₅ r)
    have hbP : b₀ (idx r) m ∈ (Tseq (idx r)).P :=
      (Finset.mem_filter.mp ((hb₀_spec (idx r) (hidx_I₅ r)).2.1 m)).1
    exact hiNotBad (Finset.mem_filter.mpr ⟨hi₄, b₀ (idx r) m, hbP, hadj⟩)
  · intro r₁ r₂ _
    exact ha₀_indep (idx r₁) (hidx_I₇ r₁) (idx r₂) (hidx_I₇ r₂)
  · intro r₁ r₂ m
    constructor
    · intro hadj
      by_contra hne
      have hidx_ne : idx r₁ ≠ idx r₂ := fun heq => hne (idx.injective heq)
      have hbP : b₀ (idx r₂) m ∈ (Tseq (idx r₂)).P :=
        (Finset.mem_filter.mp ((hb₀_spec (idx r₂) (hidx_I₅ r₂)).2.1 m)).1
      exact hind₂ (idx r₁) (hidx_I₂ r₁) (idx r₂) (hidx_I₂ r₂) hidx_ne ⟨b₀ (idx r₂) m, hbP, hadj⟩
    · rintro rfl
      exact (Finset.mem_filter.mp ((hb₀_spec (idx r₁) (hidx_I₅ r₁)).2.1 m)).2
  · intro r₁ m₁ r₂ m₂ _
    by_cases hr : r₁ = r₂
    · subst hr
      exact (hb₀_spec (idx r₁) (hidx_I₅ r₁)).2.2 m₁ m₂
    · have hidx_ne : idx r₁ ≠ idx r₂ := fun heq => hr (idx.injective heq)
      intro hadj
      exact hind₆ (idx r₁) (hidx_I₆ r₁) (idx r₂) (hidx_I₆ r₂) hidx_ne ⟨m₁, m₂, hadj⟩

private lemma colorable_nice7 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t wBase n Mf : ℕ}
    (hs : 2 ≤ s) (ht : 1 ≤ t)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    (hf : ∀ S ⊆ U₀, ¬ HasCore G S d t → ColorableOn G S Mf)
    {Tseq : Fin n → Template G U₀ s d t wBase} {I : Finset (Fin n)}
    (h7 : Nice7 Tseq I) :
    ColorableOn G (seqSupp Tseq I)
      ((2 * tplR7 d t s (wBase * t) + 1) *
        ((d * (wBase * t) + 2 ^ (d * (wBase * t)) * Mf) *
          (tplR6 d t s * tplR d t s + 1))) := by
  classical
  let w := wBase * t
  let D : Fin n → Fin n → Prop := fun i j =>
    ∃ v ∈ (Tseq i).P, tplR d t s ≤ (((Tseq j).P).filter (G.Adj v)).card
  have hout : ∀ i ∈ I, (I.filter (fun j => j ≠ i ∧ D i j)).card ≤ tplR7 d t s w := by
    intro i hi
    have hsub : I.filter (fun j => j ≠ i ∧ D i j) ⊆ (I.erase i).filter (fun j => D i j) := by
      intro j hj
      obtain ⟨hjI, hji, hD⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hji, hjI⟩, hD⟩
    exact le_trans (Finset.card_le_card hsub) (le_of_lt (h7.2 i hi))
  refine colorableOn_of_digraph_blocks I (fun i => (Tseq i).P) D (tplR7 d t s w)
    ((d * w + 2 ^ (d * w) * Mf) * (tplR6 d t s * tplR d t s + 1)) hout fun J hJI hind => ?_
  refine colorableOn_product_blocks J (fun i => (Tseq i).P)
    (d * w + 2 ^ (d * w) * Mf) (tplR6 d t s * tplR d t s)
    (fun i hi j hj hij => h7.1.1.1.1.1.1.1.1 i (hJI hi) j (hJI hj) hij)
    (fun i _ => colorableOn_template hs ht hnoCore hf (Tseq i)) ?_
  intro i hi v hv
  let NJ := J.filter (fun j => v ∉ (Tseq j).P ∧ ∃ u ∈ (Tseq j).P, G.Adj v u)
  have hNJ_card : NJ.card ≤ tplR6 d t s := by
    have hvSupp : v ∈ seqSupp Tseq I := Finset.mem_biUnion.mpr ⟨i, hJI hi, hv⟩
    exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hJI))
      (le_of_lt (h7.1.2 v hvSupp))
  have hsub : (J.biUnion (fun j => (Tseq j).P) \ (Tseq i).P).filter (G.Adj v) ⊆
      NJ.biUnion (fun j => ((Tseq j).P).filter (G.Adj v)) := by
    intro z hz
    obtain ⟨hzSdiff, hzv⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzBi, hzNotPi⟩ := Finset.mem_sdiff.mp hzSdiff
    obtain ⟨j, hjJ, hzPj⟩ := Finset.mem_biUnion.mp hzBi
    have hji : j ≠ i := fun heq => hzNotPi (heq ▸ hzPj)
    have hvNotPj : v ∉ (Tseq j).P :=
      mem_P_unique h7.1.1.1.1.1.1.1 (hJI hi) (hJI hjJ) hji.symm hv
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjJ, hvNotPj, z, hzPj, hzv⟩,
      Finset.mem_filter.mpr ⟨hzPj, hzv⟩⟩
  calc ((J.biUnion (fun j => (Tseq j).P) \ (Tseq i).P).filter (G.Adj v)).card
      ≤ (NJ.biUnion (fun j => ((Tseq j).P).filter (G.Adj v))).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ NJ, (((Tseq j).P).filter (G.Adj v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ NJ, tplR d t s := by
        refine Finset.sum_le_sum fun j hj => ?_
        obtain ⟨hjJ, hvNotPj, _⟩ := Finset.mem_filter.mp hj
        have hji : i ≠ j := fun heq => hvNotPj (heq ▸ hv)
        exact le_of_lt (lt_of_not_ge fun hge_R => hind i hi j hjJ hji ⟨v, hv, hge_R⟩)
    _ = NJ.card * tplR d t s := by simp
    _ ≤ tplR6 d t s * tplR d t s := Nat.mul_le_mul_right _ hNJ_card

private def stepChiBound (s d : ℕ) (f : ℕ → ℕ) (t : ℕ) : ℕ :=
  let wBase := tplWBase s t
  let w := wBase * t
  let M_tpl := d * w + 2 ^ (d * w) * f t
  let M_cross := tplR6 d t s * tplR d t s
  let B7 := (2 * tplR7 d t s w + 1) * (M_tpl * (M_cross + 1))
  let B4 := (2 * (d * w * tplR4 d t s) + 1) * B7
  let B2 := (2 * (d * w * (s - 1)) + 1) * B4
  f (max (rodlBound s t) t * w) + (2 * t + 1) * B2

private lemma colorableOn_step {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {U₀ : Finset V} {s d t : ℕ} {f : ℕ → ℕ}
    (hs : 2 ≤ s) (hd : 2 ≤ d) (ht : 1 ≤ t)
    (hnoTree : ¬ HasModelTreeOn G U₀ s)
    (hnoCore : ¬ HasCore G U₀ (d + 1) t)
    (hf : ∀ t' : ℕ, 1 ≤ t' → ∀ S ⊆ U₀, ¬ HasCore G S d t' → ColorableOn G S (f t')) :
    ColorableOn G U₀ (stepChiBound s d f t) := by
  classical
  let wBase := tplWBase s t
  let w := wBase * t
  have hwBase_pos : 1 ≤ wBase := tplWBase_pos s t
  have hw_pos : 1 ≤ w := Nat.mul_pos hwBase_pos ht
  obtain ⟨n, Tseq, hSeqUniv, hEmp⟩ :=
    exists_maximal_templateSeq (s := s) G U₀ (by omega : 1 ≤ d) ht hwBase_pos
  have ht'_pos : 1 ≤ max (rodlBound s t) t * w :=
    Nat.mul_pos (le_trans ht (le_max_right _ _)) hw_pos
  have hrem_sub : U₀ \ seqSupp Tseq Finset.univ ⊆ U₀ := Finset.sdiff_subset
  have hcolRem : ColorableOn G (U₀ \ seqSupp Tseq Finset.univ) (f (max (rodlBound s t) t * w)) :=
    colorableOn_of_isEmpty_stableCore hs ht hw_pos hrem_sub hnoTree hnoCore hEmp
      (hf _ ht'_pos _ hrem_sub)
  let D₀ : Fin n → Fin n → Prop := fun i j =>
    ∃ v ∈ (Tseq j).P,
      ∀ p : Fin d, (((Tseq i).core.part p).filter (fun x => ¬ G.Adj v x)).card < wBase
  have hout₀ : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ((Finset.univ : Finset (Fin n)).filter (fun j => j ≠ i ∧ D₀ i j)).card ≤ t := by
    intro i _
    let Bidx := (Finset.univ : Finset (Fin n)).filter (fun j => j ≠ i ∧ D₀ i j)
    rcases Bidx.eq_empty_or_nonempty with hemp | ⟨j₀, hj₀⟩
    · change Bidx.card ≤ t; rw [hemp]; simp
    · obtain ⟨v_dummy, _⟩ := (Finset.mem_filter.mp hj₀).2.2
      let v_of : Fin n → V := fun j =>
        if hj : j ∈ Bidx then Classical.choose (Finset.mem_filter.mp hj).2.2 else v_dummy
      have hv_spec : ∀ j ∈ Bidx, v_of j ∈ (Tseq j).P ∧
          ∀ p : Fin d, (((Tseq i).core.part p).filter (fun x => ¬ G.Adj (v_of j) x)).card < wBase := by
        intro j hj
        simp only [v_of, dif_pos hj]
        exact Classical.choose_spec (Finset.mem_filter.mp hj).2.2
      have hinj_on : Set.InjOn v_of (Bidx : Set (Fin n)) := by
        intro j₁ hj₁ j₂ hj₂ heq
        by_contra hne
        have hv1 : v_of j₁ ∈ (Tseq j₁).P :=
          (hv_spec j₁ (Finset.mem_coe.mp hj₁)).1
        have hv2 : v_of j₂ ∈ (Tseq j₂).P :=
          (hv_spec j₂ (Finset.mem_coe.mp hj₂)).1
        rw [heq] at hv1
        exact mem_P_unique hSeqUniv (Finset.mem_univ _) (Finset.mem_univ _) (Ne.symm hne) hv2 hv1
      have himg_sub : Bidx.image v_of ⊆ (U₀ \ (Tseq i).core.verts).filter
          (fun v => ∀ p : Fin d, (((Tseq i).core.part p).filter (fun x => ¬ G.Adj v x)).card < wBase) := by
        intro v hv
        obtain ⟨j, hjB, rfl⟩ := Finset.mem_image.mp hv
        have hji : j ≠ i := (Finset.mem_filter.mp hjB).2.1
        have hvPj : v_of j ∈ (Tseq j).P := (hv_spec j hjB).1
        have hvNotPi : v_of j ∉ (Tseq i).P :=
          mem_P_unique hSeqUniv (Finset.mem_univ _) (Finset.mem_univ _) hji hvPj
        have hvNotCi : v_of j ∉ (Tseq i).core.verts :=
          fun h => hvNotPi ((Tseq i).verts_sub_P h)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨(Tseq j).P_sub hvPj, hvNotCi⟩, (hv_spec j hjB).2⟩
      have hQ_lt := few_nonadj_card_lt hwBase_pos hnoCore (Tseq i).core
      calc Bidx.card
          = (Bidx.image v_of).card := (Finset.card_image_of_injOn hinj_on).symm
        _ ≤ ((U₀ \ (Tseq i).core.verts).filter _).card := Finset.card_le_card himg_sub
        _ ≤ t := le_of_lt hQ_lt
  let M_tpl := d * w + 2 ^ (d * w) * f t
  let M_cross := tplR6 d t s * tplR d t s
  let B7 := (2 * tplR7 d t s w + 1) * (M_tpl * (M_cross + 1))
  let B4 := (2 * (d * w * tplR4 d t s) + 1) * B7
  let B2 := (2 * (d * w * (s - 1)) + 1) * B4
  have hcolSupp : ColorableOn G (seqSupp Tseq Finset.univ) ((2 * t + 1) * B2) := by
    refine colorableOn_of_digraph_blocks Finset.univ (fun i => (Tseq i).P) D₀ t B2 hout₀ ?_
    intro I hI hind₀
    have h1 : Nice1 Tseq I := by
      refine ⟨isTemplateSeq_mono hI hSeqUniv, fun i hi j hj hij v hv => ?_⟩
      by_contra hno_p
      exact hind₀ i hi j hj hij ⟨v, hv, fun p => lt_of_not_ge fun hp => hno_p ⟨p, hp⟩⟩
    have h2 : Nice2 Tseq I := nice1_imp_nice2 hs hd ht hnoTree h1
    refine colorable_nice2_of_nice3 h2 fun J₃ _ h3 => ?_
    have h4 : Nice4 Tseq J₃ := nice3_imp_nice4 hs hd ht hnoTree hnoCore h3
    refine colorable_nice4_of_nice5 h4 fun J₅ _ h5 => ?_
    have h6 : Nice6 Tseq J₅ := nice5_imp_nice6 ht hnoTree hnoCore h5
    have h7 : Nice7 Tseq J₅ := nice6_imp_nice7 hs (by omega) ht hwBase_pos hnoTree hnoCore h6
    exact colorable_nice7 hs ht hnoCore (hf t ht) h7
  have hU_sub : U₀ ⊆ (U₀ \ seqSupp Tseq Finset.univ) ∪ seqSupp Tseq Finset.univ := fun x hx => by
    by_cases hxS : x ∈ seqSupp Tseq Finset.univ
    · exact Finset.mem_union_right _ hxS
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
  exact colorableOn_mono_set hU_sub (colorableOn_union_add hcolRem hcolSupp)

private def coreChiBound (s : ℕ) : ℕ → ℕ → ℕ
  | 0, t => rodlBound s t
  | m + 1, t => stepChiBound s (m + 2) (coreChiBound s m) t

private lemma colorableOn_of_no_core {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : ℕ} (hs : 2 ≤ s) (m : ℕ) :
    ∀ {t : ℕ} (_ht : 1 ≤ t) (U : Finset V),
      ¬ HasModelTreeOn G U s →
      ¬ HasCore G U (m + 2) t →
      ColorableOn G U (coreChiBound s m t) := by
  induction m with
  | zero =>
    intro t ht U hnoTree hnoCore
    exact colorableOn_bicliqueFree_no_modelTree hs ht U hnoTree hnoCore
  | succ m ih =>
    intro t ht U hnoTree hnoCore
    exact colorableOn_step hs (by omega : 2 ≤ m + 2) ht hnoTree hnoCore
      fun t' ht' S hSU hnoS => ih ht' S (fun h => hnoTree (hasModelTreeOn_mono hSU h)) hnoS

/- ## Section 5: Main Theorem -/

theorem OMA.solution : type_of% @GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.radius_two := by
  intro W _ _ T _ hT ⟨c, hrad⟩
  let s := max (Fintype.card W) 2
  have hs : 2 ≤ s := le_max_right _ _
  have hemb : SimpleGraph.IsIndContained T (modelTree s) :=
    tree_rad_two_indContained_modelTree T hT c hrad
  refine ⟨fun ω => coreChiBound s (ω - 1) 1, ?_⟩
  intro V _ _ G _ hTfree
  have hnoTree : ¬ HasModelTreeOn G Finset.univ s :=
    fun hm => hTfree (hemb.trans (isIndContained_of_hasModelTreeOn hs hm))
  let d := (G.cliqueNum - 1) + 2
  have hd_gt : G.cliqueNum < d := by dsimp [d]; omega
  have hnoCore : ¬ HasCore G Finset.univ d 1 := by
    rintro ⟨A, _, hAcard, hAdisj, hAadj⟩
    have hex_v : ∀ p : Fin d, ∃ v : V, A p = {v} :=
      fun p => Finset.card_eq_one.mp (hAcard p)
    choose v hv using hex_v
    have hv_inj : Function.Injective v := by
      intro p q heq
      by_contra hpq
      have hvp : v p ∈ A p := by rw [hv p]; exact Finset.mem_singleton_self _
      have hvq : v p ∈ A q := by rw [heq, hv q]; exact Finset.mem_singleton_self _
      exact Finset.disjoint_left.mp (hAdisj p q hpq) hvp hvq
    let K : Finset V := Finset.univ.image v
    have hKcard : K.card = d := by
      rw [Finset.card_image_of_injective _ hv_inj, Finset.card_univ, Fintype.card_fin]
    have hKcl : G.IsClique (K : Set V) := by
      intro x hx y hy hxy
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      have hpq : p ≠ q := fun heq => hxy (congr_arg v heq)
      exact hAadj p q hpq (v p) (by rw [hv p]; exact Finset.mem_singleton_self _)
        (v q) (by rw [hv q]; exact Finset.mem_singleton_self _)
    have hle := hKcl.card_le_cliqueNum
    rw [hKcard] at hle
    omega
  obtain ⟨col, hlt, hadj⟩ :=
    colorableOn_of_no_core hs (G.cliqueNum - 1) le_rfl Finset.univ hnoTree hnoCore
  have hcol : G.Colorable (coreChiBound s (G.cliqueNum - 1) 1) :=
    ⟨SimpleGraph.Coloring.mk
      (fun x => ⟨col x, hlt x (Finset.mem_univ x)⟩)
      (fun {x y} hxy heq =>
        hadj x (Finset.mem_univ x) y (Finset.mem_univ y) hxy (congr_arg Fin.val heq))⟩
  exact hcol.chromaticNumber_le
