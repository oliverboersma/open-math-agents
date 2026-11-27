import FormalConjectures.ErdosProblems.«601»

/-!
# Erdős–Hajnal–Milner (1970)

Proof of `Erdos601.erdos_601.variants.erdos_hajnal_milner_1970`:
for every limit ordinal `α < ω₁ ^ (ω + 2)`, every simple graph on `α.ToType` contains either
an infinite simple path or an independent set of order type `α`.
-/

-- Problem: Erdős–Hajnal–Milner (1970)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/601.lean:88 (declaration Erdos601.erdos_601.variants.erdos_hajnal_milner_1970)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Erdos601 Cardinal Ordinal SimpleGraph Set Filter MeasureTheory ProbabilityTheory MeasurableSpace
open scoped Cardinal Ordinal ENNReal

namespace OMA.Erdos601EHM

noncomputable section

/- ## Section 1: Ordinal and `typeLT` Toolkit -/

section OrdinalToolkit

lemma typeLT_le_of_strictMono {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] {f : α → β} (hf : StrictMono f) :
    typeLT α ≤ typeLT β :=
  (RelEmbedding.ofMonotone f fun _ _ h => hf h).ordinal_type_le

lemma typeLT_eq_of_orderIso {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (e : α ≃o β) :
    typeLT α = typeLT β :=
  le_antisymm (typeLT_le_of_strictMono e.strictMono)
    (typeLT_le_of_strictMono e.symm.strictMono)

lemma typeLT_mono_subset {α : Type} [LinearOrder α] [WellFoundedLT α]
    {s t : Set α} (h : s ⊆ t) :
    typeLT s ≤ typeLT t :=
  typeLT_le_of_strictMono (f := fun x : s => (⟨x.1, h x.2⟩ : t)) fun _ _ hxy => hxy

lemma typeLT_image_strictMono {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] {f : α → β} (hf : StrictMono f) (s : Set α) :
    typeLT (f '' s) = typeLT s := by
  refine typeLT_eq_of_orderIso
    { toFun := fun x => ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
      invFun := fun x => ⟨f x.1, x.1, x.2, rfl⟩
      left_inv := fun x => by
        ext
        exact (Classical.choose_spec x.2).2
      right_inv := fun x => by
        ext
        exact hf.injective (Classical.choose_spec (⟨x.1, x.2, rfl⟩ : f x.1 ∈ f '' s)).2
      map_rel_iff' := fun {a b} => by
        change Classical.choose a.2 ≤ Classical.choose b.2 ↔ a.1 ≤ b.1
        rw [← hf.le_iff_le, (Classical.choose_spec a.2).2, (Classical.choose_spec b.2).2] }

lemma typeLT_image_val {α : Type} [LinearOrder α] [WellFoundedLT α]
    {s : Set α} (t : Set s) :
    typeLT (Subtype.val '' t : Set α) = typeLT t :=
  typeLT_image_strictMono (f := (Subtype.val : s → α)) (fun _ _ h => h) t

lemma typeLT_subtype_set {α : Type} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) (p : s → Prop) :
    typeLT {x : s | p x} = typeLT {x : α | ∃ hx : x ∈ s, p ⟨x, hx⟩} := by
  refine typeLT_eq_of_orderIso
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

lemma typeLT_univ {α : Type} [LinearOrder α] [WellFoundedLT α] :
    typeLT (Set.univ : Set α) = typeLT α :=
  typeLT_eq_of_orderIso
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Set.mem_univ x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

lemma typeLT_set_le_self {α : Type} [LinearOrder α] [WellFoundedLT α] (s : Set α) :
    typeLT s ≤ typeLT α :=
  Ordinal.type_set_le s

lemma exists_orderIso_toType {α : Type} [LinearOrder α] [WellFoundedLT α]
    {γ : Ordinal.{0}} (h : typeLT α = γ) : Nonempty (α ≃o γ.ToType) := by
  have h1 : typeLT α = typeLT γ.ToType := by rw [h, Ordinal.type_toType]
  obtain ⟨e⟩ := Ordinal.type_eq.1 h1
  exact ⟨OrderIso.ofRelIsoLT e⟩

lemma typeLT_le_of_forall_typein_lt {α : Type} [LinearOrder α] [WellFoundedLT α]
    {γ : Ordinal.{0}} (h : ∀ x : α, Ordinal.typein LT.lt x < γ) :
    typeLT α ≤ γ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hx⟩ := Ordinal.typein_surj LT.lt hlt
  exact (h x).ne hx

lemma typeLT_Iio_subtype {α : Type} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) (x : s) :
    typeLT {y : α | y ∈ s ∧ y < x.1} = Ordinal.typein LT.lt x := by
  rw [← Ordinal.type_Iio_lt x]
  refine typeLT_eq_of_orderIso
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

lemma le_typeLT_of_succ {α : Type} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) (η : Ordinal.{0}) :
    Order.succ η ≤ typeLT s ↔ ∃ x ∈ s, η ≤ typeLT {y : α | y ∈ s ∧ y < x} := by
  rw [Order.succ_le_iff]
  constructor
  · intro hlt
    obtain ⟨x, hx⟩ := Ordinal.typein_surj LT.lt hlt
    refine ⟨x.1, x.2, ?_⟩
    rw [typeLT_Iio_subtype s x, hx]
  · rintro ⟨x, hx, hle⟩
    have hlt := Ordinal.typein_lt_type LT.lt (⟨x, hx⟩ : s)
    rw [← typeLT_Iio_subtype s ⟨x, hx⟩] at hlt
    exact hle.trans_lt hlt

lemma countable_of_typeLT_lt_omega1 {α : Type} [LinearOrder α] [WellFoundedLT α]
    (h : typeLT α < ω₁) : Countable α := by
  rw [← Cardinal.mk_le_aleph0_iff, ← Cardinal.lt_aleph_one_iff]
  rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_type] at h
  exact h

lemma typeLT_lt_omega1_of_countable {α : Type} [LinearOrder α] [WellFoundedLT α]
    [Countable α] : typeLT α < ω₁ := by
  rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_type, Cardinal.lt_aleph_one_iff,
    Cardinal.mk_le_aleph0_iff]
  infer_instance

lemma countable_toType_of_lt_omega1 {γ : Ordinal.{0}} (h : γ < ω₁) : Countable γ.ToType :=
  countable_of_typeLT_lt_omega1 (by simpa [Ordinal.type_toType] using h)

lemma countable_Iio_omega1 (ξ : (ω₁ : Ordinal.{0}).ToType) : (Set.Iio ξ).Countable := by
  have hlt : typeLT (Set.Iio ξ) < ω₁ := by
    change Ordinal.type (α := Set.Iio ξ) (· < ·) < ω₁
    rw [Ordinal.type_Iio_lt]
    exact (Ordinal.typein_lt_type LT.lt ξ).trans_eq (Ordinal.type_toType ω₁)
  exact Set.countable_coe_iff.1 (countable_of_typeLT_lt_omega1 hlt)

lemma countable_Iic_omega1 (ξ : (ω₁ : Ordinal.{0}).ToType) : (Set.Iic ξ).Countable := by
  have h : Set.Iic ξ = Set.Iio ξ ∪ {ξ} := by ext x; simp [le_iff_lt_or_eq]
  rw [h]
  exact (countable_Iio_omega1 ξ).union (Set.countable_singleton ξ)

lemma exists_gt_of_countable_omega1 {s : Set (ω₁ : Ordinal.{0}).ToType} (hs : s.Countable) :
    ∃ ξ : (ω₁ : Ordinal.{0}).ToType, ∀ x ∈ s, x < ξ := by
  by_contra h
  push Not at h
  have huniv : (Set.univ : Set (ω₁ : Ordinal.{0}).ToType) ⊆ ⋃ x ∈ s, Set.Iic x := by
    intro ξ _
    obtain ⟨x, hxs, hle⟩ := h ξ
    exact Set.mem_biUnion hxs hle
  have hc : (Set.univ : Set (ω₁ : Ordinal.{0}).ToType).Countable :=
    (hs.biUnion fun x _ => countable_Iic_omega1 x).mono huniv
  have : Countable (ω₁ : Ordinal.{0}).ToType := Set.countable_univ_iff.1 hc
  have hlt : typeLT (ω₁ : Ordinal.{0}).ToType < ω₁ := typeLT_lt_omega1_of_countable
  rw [Ordinal.type_toType] at hlt
  exact lt_irrefl _ hlt

instance prodLexWellFoundedLT {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] : WellFoundedLT (α ×ₗ β) :=
  ⟨WellFounded.prod_lex wellFounded_lt wellFounded_lt⟩

instance sumLexWellFoundedLT {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] : WellFoundedLT (α ⊕ₗ β) :=
  ⟨Sum.lex_wf wellFounded_lt wellFounded_lt⟩

lemma typeLT_prodLex {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] :
    typeLT (α ×ₗ β) = (typeLT β) * (typeLT α) := by
  change Ordinal.type (Prod.Lex (· < ·) (· < ·)) = _
  exact Ordinal.type_prod_lex (· < ·) (· < ·)

lemma typeLT_sumLex {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] :
    typeLT (α ⊕ₗ β) = (typeLT α) + (typeLT β) := by
  change Ordinal.type (Sum.Lex (· < ·) (· < ·)) = _
  exact Ordinal.type_sum_lex (· < ·) (· < ·)

lemma typeLT_union_le_add {α : Type} [LinearOrder α] [WellFoundedLT α]
    {s t : Set α} (hst : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    typeLT (s ∪ t : Set α) = (typeLT s) + (typeLT t) := by
  classical
  rw [← typeLT_sumLex]
  refine typeLT_eq_of_orderIso
    { toFun := fun x : (s ∪ t : Set α) =>
        if hx : x.1 ∈ s then toLex (Sum.inl ⟨x.1, hx⟩)
        else toLex (Sum.inr ⟨x.1, Or.resolve_left ((Set.mem_union x.1 s t).1 x.2) hx⟩)
      invFun := fun x : (s ⊕ₗ t) =>
        match ofLex x with
        | Sum.inl a => ⟨a.1, Or.inl a.2⟩
        | Sum.inr b => ⟨b.1, Or.inr b.2⟩
      left_inv := fun x => by
        by_cases hx : x.1 ∈ s <;> simp [hx]
      right_inv := fun x => by
        cases x with | _ x' =>
        cases x' with
        | inl a => simp [a.2]
        | inr b =>
          have hb : b.1 ∉ s := fun h' => (hst b.1 h' b.1 b.2).false
          simp [hb]
      map_rel_iff' := fun {a b} => by
        by_cases ha : a.1 ∈ s <;> by_cases hb : b.1 ∈ s
        · simp only [Equiv.coe_fn_mk, dif_pos ha, dif_pos hb]
          change Sum.Lex (· ≤ ·) (· ≤ ·) (Sum.inl (⟨a.1, ha⟩ : s)) (Sum.inl (⟨b.1, hb⟩ : s)) ↔ a ≤ b
          constructor
          · intro h; cases h with | inl h1 => exact h1
          · intro h; exact Sum.Lex.inl h
        · have hab : a.1 < b.1 := hst a.1 ha b.1 (Or.resolve_left ((Set.mem_union b.1 s t).1 b.2) hb)
          simp only [Equiv.coe_fn_mk, dif_pos ha, dif_neg hb]
          constructor
          · intro _; exact hab.le
          · intro _; exact Sum.Lex.sep _ _
        · have hba : b.1 < a.1 := hst b.1 hb a.1 (Or.resolve_left ((Set.mem_union a.1 s t).1 a.2) ha)
          simp only [Equiv.coe_fn_mk, dif_neg ha, dif_pos hb]
          constructor
          · intro h; cases h
          · intro h; exact (not_le.2 hba h).elim
        · simp only [Equiv.coe_fn_mk, dif_neg ha, dif_neg hb]
          change Sum.Lex (· ≤ ·) (· ≤ ·)
            (Sum.inr (⟨a.1, Or.resolve_left ((Set.mem_union a.1 s t).1 a.2) ha⟩ : t))
            (Sum.inr (⟨b.1, Or.resolve_left ((Set.mem_union b.1 s t).1 b.2) hb⟩ : t)) ↔ a ≤ b
          constructor
          · intro h; cases h with | inr h1 => exact h1
          · intro h; exact Sum.Lex.inr h }

lemma omega0_opow_lt_omega1 {δ : Ordinal.{0}} (hδ : δ < ω₁) : ω ^ δ < ω₁ := by
  induction δ using WellFoundedLT.induction with
  | ind δ ih =>
    rcases Ordinal.zero_or_succ_or_isSuccLimit δ with rfl | ⟨γ, rfl⟩ | hlim
    · simpa using (Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one)
    · rw [Ordinal.opow_succ]
      have hγ : γ < ω₁ := (Order.lt_succ γ).trans hδ
      have h1 : ω ^ γ < ω₁ := ih γ (Order.lt_succ γ) hγ
      rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_mul, Cardinal.lt_aleph_one_iff]
      rw [Cardinal.lt_omega_iff_card_lt, Cardinal.lt_aleph_one_iff] at h1
      rw [Ordinal.card_omega0]
      exact (mul_le_mul' h1 le_rfl).trans_eq (Cardinal.mul_eq_self le_rfl)
    · have : Countable δ.ToType := countable_toType_of_lt_omega1 hδ
      have hsub : ∀ a : δ.ToType, ω ^ (Ordinal.typein LT.lt a) < ω₁ := by
        intro a
        have ha : Ordinal.typein LT.lt a < δ :=
          (Ordinal.typein_lt_type LT.lt a).trans_eq (Ordinal.type_toType δ)
        exact ih _ ha (ha.trans hδ)
      have hbd : ∃ ξ : (ω₁ : Ordinal.{0}).ToType, ∀ a : δ.ToType,
          ω ^ (Ordinal.typein LT.lt a) < Ordinal.typein LT.lt ξ := by
        have hf : ∀ a : δ.ToType, ∃ x : (ω₁ : Ordinal.{0}).ToType,
            Ordinal.typein LT.lt x = ω ^ (Ordinal.typein LT.lt a) := fun a =>
          Ordinal.typein_surj LT.lt (by rw [Ordinal.type_toType]; exact hsub a)
        choose g hg using hf
        obtain ⟨ξ, hξ⟩ := exists_gt_of_countable_omega1 (Set.countable_range g)
        refine ⟨ξ, fun a => ?_⟩
        rw [← hg a, Ordinal.typein_lt_typein]
        exact hξ (g a) ⟨a, rfl⟩
      obtain ⟨ξ, hξ⟩ := hbd
      have hle : ω ^ δ ≤ Ordinal.typein LT.lt ξ := by
        rw [Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero hlim]
        intro γ hγ
        obtain ⟨a, rfl⟩ := Ordinal.typein_surj LT.lt (by rwa [Ordinal.type_toType])
        exact (hξ a).le
      exact hle.trans_lt ((Ordinal.typein_lt_type LT.lt ξ).trans_eq (Ordinal.type_toType ω₁))

/-- Indissectability of `ω ^ δ` for every ordinal `δ`: if two subsets of a well-order each
have order type `< ω ^ δ`, then their union also has order type `< ω ^ δ`. -/
lemma omega0_opow_union_lt (δ : Ordinal.{0}) :
    ∀ {α : Type} [LinearOrder α] [WellFoundedLT α] {A B : Set α},
      typeLT A < ω ^ δ → typeLT B < ω ^ δ → typeLT (A ∪ B : Set α) < ω ^ δ := by
  induction δ using WellFoundedLT.induction with
  | ind δ ih =>
    intro α _ _ A B hA hB
    rcases Ordinal.zero_or_succ_or_isSuccLimit δ with rfl | ⟨γ, rfl⟩ | hlim
    · simp only [Ordinal.opow_zero] at hA hB ⊢
      have hA0 : typeLT A = 0 := Order.lt_one_iff.1 hA
      have hB0 : typeLT B = 0 := Order.lt_one_iff.1 hB
      have hAe : A = ∅ := by
        ext x; simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have := (Ordinal.type_eq_zero_iff_isEmpty).1 hA0
        exact IsEmpty.false (⟨x, hx⟩ : A)
      have hBe : B = ∅ := by
        ext x; simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have := (Ordinal.type_eq_zero_iff_isEmpty).1 hB0
        exact IsEmpty.false (⟨x, hx⟩ : B)
      simp [hAe, hBe]
    · by_contra hge
      push Not at hge
      let U : Set α := A ∪ B
      have hge' : ω ^ γ * ω ≤ typeLT U := by rwa [← Ordinal.opow_succ]
      let U₀ : Set α := {x : α | ∃ hx : x ∈ U, Ordinal.typein LT.lt (⟨x, hx⟩ : U) < ω ^ γ * ω}
      have hU₀_type : typeLT U₀ = ω ^ γ * ω := by
        have heq : typeLT {x : U | Ordinal.typein LT.lt x < ω ^ γ * ω} = ω ^ γ * ω := by
          by_cases hlt : ω ^ γ * ω < typeLT U
          · obtain ⟨c, hc⟩ := Ordinal.typein_surj LT.lt hlt
            have hset : {x : U | Ordinal.typein LT.lt x < ω ^ γ * ω} = Set.Iio c := by
              ext x; simp [← hc]
            rw [hset]
            change Ordinal.type (α := Set.Iio c) (· < ·) = _
            rw [Ordinal.type_Iio_lt, hc]
          · have heqU : typeLT U = ω ^ γ * ω := le_antisymm (not_lt.1 hlt) hge'
            have hset : {x : U | Ordinal.typein LT.lt x < ω ^ γ * ω} = Set.univ := by
              ext x; simp [← heqU, Ordinal.typein_lt_type]
            rw [hset, typeLT_univ, heqU]
        exact (typeLT_subtype_set U _).symm.trans heq
      have hprod : typeLT (ℕ ×ₗ (ω ^ γ).ToType) = ω ^ γ * ω := by
        rw [typeLT_prodLex, Ordinal.type_toType, Ordinal.type_nat_lt]
      obtain ⟨e⟩ := exists_orderIso_toType hU₀_type
      obtain ⟨e2⟩ := exists_orderIso_toType hprod
      let φ : ℕ ×ₗ (ω ^ γ).ToType ≃o U₀ := e2.trans e.symm
      let K : ℕ → Set α := fun n => Set.range (fun y : (ω ^ γ).ToType => (φ (toLex (n, y))).1)
      have hK_type : ∀ n, typeLT (K n) = ω ^ γ := fun n => by
        have hsm : StrictMono (fun y : (ω ^ γ).ToType => (φ (toLex (n, y))).1) := fun a b hab =>
          φ.strictMono (Prod.Lex.right n hab)
        have h1 := typeLT_image_strictMono hsm Set.univ
        rw [Set.image_univ, typeLT_univ, Ordinal.type_toType] at h1
        exact h1
      have hK_sub : ∀ n, K n ⊆ A ∪ B := fun n x ⟨y, hy⟩ => by
        rw [← hy]; exact (φ (toLex (n, y))).2.1
      have hK_split : ∀ n, typeLT (A ∩ K n : Set α) = ω ^ γ ∨ typeLT (B ∩ K n : Set α) = ω ^ γ := fun n => by
        by_contra hboth
        push Not at hboth
        have hA' : typeLT (A ∩ K n : Set α) < ω ^ γ :=
          lt_of_le_of_ne ((typeLT_mono_subset Set.inter_subset_right).trans_eq (hK_type n)) hboth.1
        have hB' : typeLT (B ∩ K n : Set α) < ω ^ γ :=
          lt_of_le_of_ne ((typeLT_mono_subset Set.inter_subset_right).trans_eq (hK_type n)) hboth.2
        have hun : (A ∩ K n) ∪ (B ∩ K n) = K n := by
          rw [← Set.union_inter_distrib_right, Set.inter_eq_right.2 (hK_sub n)]
        have hlt := ih γ (Order.lt_succ γ) hA' hB'
        rw [hun, hK_type n] at hlt
        exact lt_irrefl _ hlt
      have hinf : {n : ℕ | typeLT (A ∩ K n : Set α) = ω ^ γ}.Infinite ∨
          {n : ℕ | typeLT (B ∩ K n : Set α) = ω ^ γ}.Infinite := by
        by_contra hfin
        push Not at hfin
        have hun : ({n : ℕ | typeLT (A ∩ K n : Set α) = ω ^ γ} ∪
            {n : ℕ | typeLT (B ∩ K n : Set α) = ω ^ γ}) = Set.univ := by
          ext n; simp [hK_split n]
        exact Set.infinite_univ (hun ▸ hfin.1.union hfin.2)
      have hcontra_of_inf : ∀ {S : Set α},
          {n : ℕ | typeLT (S ∩ K n : Set α) = ω ^ γ}.Infinite → ¬ typeLT S < ω ^ Order.succ γ := by
        intro S hS hSlt
        let g : ℕ → ℕ := Nat.nth (· ∈ {n : ℕ | typeLT (S ∩ K n : Set α) = ω ^ γ})
        have hg_mono : StrictMono g := Nat.nth_strictMono hS
        have hg_mem : ∀ k, typeLT (S ∩ K (g k) : Set α) = ω ^ γ := fun k =>
          Nat.nth_mem_of_infinite hS k
        have heIso : ∀ k : ℕ, Nonempty ((ω ^ γ).ToType ≃o (S ∩ K (g k) : Set α)) := fun k => by
          obtain ⟨eS⟩ := exists_orderIso_toType (hg_mem k)
          exact ⟨eS.symm⟩
        let ψ := fun k => Classical.choice (heIso k)
        let emb : ℕ ×ₗ (ω ^ γ).ToType → S := fun p =>
          ⟨(ψ (ofLex p).1 (ofLex p).2).1, (ψ (ofLex p).1 (ofLex p).2).2.1⟩
        have hemb : StrictMono emb := by
          intro p q hpq
          cases p with | _ p' => cases q with | _ q' =>
          cases p' with | mk p1 p2 => cases q' with | mk q1 q2 =>
          rcases Prod.lex_iff.1 hpq with h1 | ⟨h1, h2⟩
          · have hlt_g : g p1 < g q1 := hg_mono h1
            obtain ⟨yp, hyp⟩ := (ψ p1 p2).2.2
            obtain ⟨yq, hyq⟩ := (ψ q1 q2).2.2
            change (ψ p1 p2).1 < (ψ q1 q2).1
            rw [← hyp, ← hyq]
            exact φ.strictMono (Prod.Lex.left yp yq hlt_g)
          · subst h1
            exact (ψ p1).strictMono h2
        have hle := typeLT_le_of_strictMono hemb
        rw [hprod, ← Ordinal.opow_succ] at hle
        exact not_lt.2 hle hSlt
      rcases hinf with hinfA | hinfB
      · exact hcontra_of_inf hinfA hA
      · exact hcontra_of_inf hinfB hB
    · rw [Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim] at hA hB ⊢
      obtain ⟨γ₁, hγ₁, hA'⟩ := hA
      obtain ⟨γ₂, hγ₂, hB'⟩ := hB
      let γ := max γ₁ γ₂
      have hγ : γ < δ := max_lt hγ₁ hγ₂
      have hA'' : typeLT A < ω ^ γ :=
        hA'.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_left _ _))
      have hB'' : typeLT B < ω ^ γ :=
        hB'.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_right _ _))
      exact ⟨γ, hγ, ih γ hγ hA'' hB''⟩

lemma omega0_opow_biUnion_finset_lt {α ι : Type} [LinearOrder α] [WellFoundedLT α]
    {δ : Ordinal.{0}} {F : Finset ι} {A : ι → Set α}
    (hA : ∀ i ∈ F, typeLT (A i) < ω ^ δ) :
    typeLT (⋃ i ∈ F, A i : Set α) < ω ^ δ := by
  classical
  induction F using Finset.induction with
  | empty =>
    have he : (⋃ i ∈ (∅ : Finset ι), A i) = ∅ := by simp
    rw [he]
    have h0 : typeLT (∅ : Set α) = 0 := Ordinal.type_eq_zero_iff_isEmpty.2 inferInstance
    rw [h0]
    exact Ordinal.opow_pos δ Ordinal.omega0_pos
  | @insert a s ha ih =>
    have hins : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
      ext x; simp
    rw [hins]
    exact omega0_opow_union_lt δ (hA a (Finset.mem_insert_self a s))
      (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

lemma typeLT_sdiff_of_lt_omega0_opow {α : Type} [LinearOrder α] [WellFoundedLT α]
    {δ : Ordinal.{0}} {A B : Set α} (hA : typeLT A = ω ^ δ) (hB : typeLT B < ω ^ δ) :
    typeLT (A \ B : Set α) = ω ^ δ := by
  refine le_antisymm ((typeLT_mono_subset Set.sdiff_subset).trans_eq hA) ?_
  by_contra hlt
  push Not at hlt
  have h1 := omega0_opow_union_lt δ hlt hB
  have hsub : A ⊆ (A \ B) ∪ B := fun x hx => by
    by_cases h : x ∈ B
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  have h2 := (typeLT_mono_subset hsub).trans_lt h1
  rw [hA] at h2
  exact lt_irrefl _ h2

lemma typeLT_finite_lt_omega0 {α : Type} [LinearOrder α] [WellFoundedLT α]
    {F : Set α} (hF : F.Finite) : typeLT F < ω := by
  rw [Ordinal.lt_omega0]
  have : Finite F := hF.to_subtype
  have : Fintype F := Fintype.ofFinite F
  exact ⟨Fintype.card F, by simp [Ordinal.type_fintype]⟩

lemma typeLT_sdiff_finset_omega0_opow {α : Type} [LinearOrder α] [WellFoundedLT α]
    {δ : Ordinal.{0}} (hδ : 1 ≤ δ) {A : Set α} (hA : typeLT A = ω ^ δ) (F : Finset α) :
    typeLT (A \ (F : Set α) : Set α) = ω ^ δ := by
  refine typeLT_sdiff_of_lt_omega0_opow hA ?_
  have h1 : typeLT (F : Set α) < ω := typeLT_finite_lt_omega0 F.finite_toSet
  have h2 : ω ≤ ω ^ δ := by simpa using Ordinal.opow_le_opow_right Ordinal.omega0_pos hδ
  exact h1.trans_le h2

lemma isSuccLimit_of_add_right {a b : Ordinal.{0}}
    (hab : Order.IsSuccLimit (a + b)) (hb : b ≠ 0) : Order.IsSuccLimit b := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit b with h0 | ⟨c, rfl⟩ | hlim
  · exact (hb h0).elim
  · exfalso
    rw [Order.succ_eq_add_one, ← add_assoc, ← Order.succ_eq_add_one] at hab
    exact Order.not_isSuccLimit_succ (a + c) hab
  · exact hlim

/-- Cantor Normal Form for limit ordinals: every limit ordinal is a finite sum of
`ω ^ η` with `1 ≤ η`. -/
lemma cnf_limit (α : Ordinal.{0}) (hα : Order.IsSuccLimit α) :
    ∃ L : List Ordinal.{0}, (∀ η ∈ L, 1 ≤ η) ∧ α = (L.map (fun η => ω ^ η)).sum := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    have hα0 : α ≠ 0 := hα.ne_bot
    have hωα : ω ≤ α := Ordinal.omega0_le_of_isSuccLimit hα
    let e := Ordinal.log ω α
    have he1 : 1 ≤ e := by
      have h0 : Order.succ (0 : Ordinal.{0}) ≤ e :=
        Order.succ_le_iff.2 (Ordinal.log_pos Ordinal.one_lt_omega0 hα0 hωα)
      rwa [Order.succ_eq_add_one, zero_add] at h0
    have hle : ω ^ e ≤ α := Ordinal.opow_log_le_self ω hα0
    let r := α - ω ^ e
    have hadd : ω ^ e + r = α := Ordinal.add_sub_cancel_of_le hle
    have hr_lt : r < α := Ordinal.sub_omega0_opow_log_lt hα0
    by_cases hr0 : r = 0
    · refine ⟨[e], by simp [he1], ?_⟩
      simpa [hr0] using hadd.symm
    · have hr_lim : Order.IsSuccLimit r := by
        rw [← hadd] at hα
        exact isSuccLimit_of_add_right hα hr0
      obtain ⟨L, hL1, hLsum⟩ := ih r hr_lt hr_lim
      refine ⟨e :: L, ?_, ?_⟩
      · intro η hη
        rcases List.mem_cons.1 hη with rfl | hmem
        · exact he1
        · exact hL1 η hmem
      · simp only [List.map_cons, List.sum_cons, ← hLsum, hadd]

/-- Splitting a well-order of type `L.sum` into `L.length` contiguous disjoint blocks. -/
lemma partition_of_list_sum (L : List Ordinal.{0}) :
    ∀ {α : Type} [LinearOrder α] [WellFoundedLT α],
      typeLT α = L.sum →
      ∃ B : Fin L.length → Set α,
        (∀ i, typeLT (B i) = L.get i) ∧
        (∀ i j : Fin L.length, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) := by
  induction L with
  | nil =>
    intro α _ _ _
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | cons a t ih =>
    intro α _ _ hα
    simp only [List.sum_cons] at hα
    have hsum : typeLT (a.ToType ⊕ₗ t.sum.ToType) = a + t.sum := by
      rw [typeLT_sumLex, Ordinal.type_toType, Ordinal.type_toType]
    obtain ⟨e1⟩ := exists_orderIso_toType hα
    obtain ⟨e2⟩ := exists_orderIso_toType hsum
    let φ : a.ToType ⊕ₗ t.sum.ToType ≃o α := e2.trans e1.symm
    let A0 : Set α := Set.range (fun x : a.ToType => φ (toLex (Sum.inl x)))
    let R : Set α := Set.range (fun y : t.sum.ToType => φ (toLex (Sum.inr y)))
    have hA0 : typeLT A0 = a := by
      have hsm : StrictMono (fun x : a.ToType => φ (toLex (Sum.inl x))) := fun x y hxy =>
        φ.strictMono (Sum.Lex.inl hxy)
      have h1 := typeLT_image_strictMono hsm Set.univ
      rw [Set.image_univ, typeLT_univ, Ordinal.type_toType] at h1
      exact h1
    have hR : typeLT R = t.sum := by
      have hsm : StrictMono (fun x : t.sum.ToType => φ (toLex (Sum.inr x))) := fun x y hxy =>
        φ.strictMono (Sum.Lex.inr hxy)
      have h1 := typeLT_image_strictMono hsm Set.univ
      rw [Set.image_univ, typeLT_univ, Ordinal.type_toType] at h1
      exact h1
    obtain ⟨BR, hBR_type, hBR_ord⟩ := ih hR
    let B : Fin (t.length + 1) → Set α := Fin.cases A0 (fun i => Subtype.val '' BR i)
    refine ⟨B, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact hA0
      · intro j
        change typeLT (Subtype.val '' BR j : Set α) = t.get j
        rw [typeLT_image_val, hBR_type j]
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun h => (lt_irrefl _ h).elim) (fun j' _ => ?_) j
        rintro x ⟨ax, rfl⟩ y ⟨⟨yr, ⟨ty, rfl⟩⟩, _, rfl⟩
        exact φ.strictMono (Sum.Lex.sep ax ty)
      · refine Fin.cases (fun h => (Nat.not_lt_zero _ h).elim) (fun j' h => ?_) j
        rintro x ⟨xr, hxr, rfl⟩ y ⟨yr, hyr, rfl⟩
        exact hBR_ord i' j' (Fin.succ_lt_succ_iff.1 h) xr hxr yr hyr

lemma typeLT_of_ordered_blocks {L : List Ordinal.{0}} {α : Type} [LinearOrder α] [WellFoundedLT α]
    {B : Fin L.length → Set α}
    (hB : ∀ i, typeLT (B i) = L.get i)
    (hord : ∀ i j : Fin L.length, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) :
    typeLT (⋃ i : Fin L.length, B i : Set α) = L.sum := by
  induction L with
  | nil =>
    simp only [List.length_nil, List.sum_nil]
    have : IsEmpty (⋃ i : Fin 0, B i : Set α) :=
      ⟨fun ⟨_, hx⟩ => by obtain ⟨i, _⟩ := Set.mem_iUnion.1 hx; exact Fin.elim0 i⟩
    exact Ordinal.type_eq_zero_iff_isEmpty.2 inferInstance
  | cons a t ih =>
    have hun : (⋃ i : Fin (a :: t).length, B i) =
        B 0 ∪ ⋃ j : Fin t.length, B j.succ := by
      ext x; simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        refine Fin.cases (fun h => Or.inl h) (fun j h => Or.inr ⟨j, h⟩) i hi
      · rintro (h | ⟨j, hj⟩)
        · exact ⟨0, h⟩
        · exact ⟨j.succ, hj⟩
    rw [hun, typeLT_union_le_add]
    · rw [hB 0, List.sum_cons]
      congr 1
      exact ih (fun j => hB j.succ) (fun i j hij => hord i.succ j.succ (Fin.succ_lt_succ_iff.2 hij))
    · intro x hx y hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
      exact hord 0 j.succ (Fin.succ_pos j) x hx y hj

lemma hasPathOrIndep_of_orderIso {α : Ordinal.{0}} {V : Type} [LinearOrder V] [WellFoundedLT V]
    (hV : typeLT V = α) (h : HasPathOrIndepSetOfType α) :
    ∀ G : SimpleGraph V,
      (∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))) ∨
      (∃ s : Set V, G.IsIndepSet s ∧ typeLT s = α) := by
  intro G
  obtain ⟨e⟩ := exists_orderIso_toType hV
  let G' : SimpleGraph α.ToType := G.comap e.symm
  rcases h G' with ⟨f, hf_inj, hf_adj⟩ | ⟨s, hs_indep, hs_type⟩
  · exact Or.inl ⟨fun n => e.symm (f n), e.symm.injective.comp hf_inj, hf_adj⟩
  · refine Or.inr ⟨e.symm '' s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy hadj
      exact hs_indep hx hy (fun h => hxy (congrArg e.symm h)) hadj
    · rw [typeLT_image_strictMono e.symm.strictMono, hs_type]

lemma hasPathOrIndep_iff_of_orderIso {α : Ordinal.{0}} {V : Type} [LinearOrder V] [WellFoundedLT V]
    (hV : typeLT V = α) :
    HasPathOrIndepSetOfType α ↔
      ∀ G : SimpleGraph V,
        (∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))) ∨
        (∃ s : Set V, G.IsIndepSet s ∧ typeLT s = α) := by
  constructor
  · exact hasPathOrIndep_of_orderIso hV
  · intro h G
    obtain ⟨e⟩ := exists_orderIso_toType hV
    let G' : SimpleGraph V := G.comap e
    rcases h G' with ⟨f, hf_inj, hf_adj⟩ | ⟨s, hs_indep, hs_type⟩
    · exact Or.inl ⟨fun n => e (f n), e.injective.comp hf_inj, hf_adj⟩
    · refine Or.inr ⟨e '' s, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy hadj
        exact hs_indep hx hy (fun h => hxy (congrArg e h)) hadj
      · rw [typeLT_image_strictMono e.strictMono, hs_type]

end OrdinalToolkit

/- ## Section 2: Finite Orientation and `ℕ`-Coloring for Finite Set Mappings -/

section FiniteSetMappings

/-- If `G` has no infinite simple path, every nonempty subset `s` contains a vertex with
finitely many neighbors inside `s`. -/
lemma exists_finite_deg_in_subset {V : Type*} {G : SimpleGraph V}
    (hno : ¬ ∃ p : ℕ → V, Function.Injective p ∧ ∀ n, G.Adj (p n) (p (n + 1)))
    {s : Set V} (hs : s.Nonempty) :
    ∃ x ∈ s, {y ∈ s | G.Adj x y}.Finite := by
  classical
  by_contra hall
  push Not at hall
  have hnext : ∀ (x : V) (hx : x ∈ s) (L : Finset V),
      ∃ y ∈ s, G.Adj x y ∧ y ∉ L := fun x hx L => by
    have hinf := hall x hx
    have hne : ({y ∈ s | G.Adj x y} \ (L : Set V)).Nonempty :=
      (hinf.sdiff L.finite_toSet).nonempty
    obtain ⟨y, ⟨hys, hadj⟩, hyL⟩ := hne
    exact ⟨y, hys, hadj, hyL⟩
  let stepFn : {p : V × Finset V // p.1 ∈ s ∧ p.1 ∈ p.2} →
      {p : V × Finset V // p.1 ∈ s ∧ p.1 ∈ p.2} := fun prev =>
    let h := hnext prev.1.1 prev.2.1 prev.1.2
    let y := Classical.choose h
    have hy := Classical.choose_spec h
    ⟨(y, insert y prev.1.2), hy.1, Finset.mem_insert_self y _⟩
  let initSt : {p : V × Finset V // p.1 ∈ s ∧ p.1 ∈ p.2} :=
    let x0 := Classical.choose hs
    ⟨(x0, {x0}), Classical.choose_spec hs, Finset.mem_singleton_self x0⟩
  let build : ℕ → {p : V × Finset V // p.1 ∈ s ∧ p.1 ∈ p.2} := fun n => stepFn^[n] initSt
  have hbuild_succ : ∀ n, build (n + 1) = stepFn (build n) := fun n =>
    Function.iterate_succ_apply' stepFn n initSt
  have hsub : ∀ m n, m ≤ n → (build m).1.2 ⊆ (build n).1.2 := by
    intro m n hmn
    induction hmn with
    | refl => exact Finset.Subset.refl _
    | step _ ih =>
      rw [hbuild_succ]
      exact ih.trans (Finset.subset_insert _ _)
  have hnotmem : ∀ n, (build (n + 1)).1.1 ∉ (build n).1.2 := fun n => by
    rw [hbuild_succ]
    exact (Classical.choose_spec (hnext (build n).1.1 (build n).2.1 (build n).1.2)).2.2
  have hadj : ∀ n, G.Adj (build n).1.1 (build (n + 1)).1.1 := fun n => by
    rw [hbuild_succ]
    exact (Classical.choose_spec (hnext (build n).1.1 (build n).2.1 (build n).1.2)).2.1
  have hinj : Function.Injective (fun n => (build n).1.1) := by
    intro m n hmn
    dsimp only at hmn
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (build m).1.1 ∈ (build (n - 1)).1.2 :=
        hsub m (n - 1) (Nat.le_sub_one_of_lt hlt) (build m).2.2
      have h2 : (build ((n - 1) + 1)).1.1 ∉ (build (n - 1)).1.2 := hnotmem (n - 1)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero (by omega)), ← hmn] at h2
      exact h2 h1
    · have h1 : (build n).1.1 ∈ (build (m - 1)).1.2 :=
        hsub n (m - 1) (Nat.le_sub_one_of_lt hgt) (build n).2.2
      have h2 : (build ((m - 1) + 1)).1.1 ∉ (build (m - 1)).1.2 := hnotmem (m - 1)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero (by omega)), hmn] at h2
      exact h2 h1
  exact hno ⟨fun n => (build n).1.1, hinj, hadj⟩

private structure PartialOrient {V : Type*} (G : SimpleGraph V) where
  dom : Set V
  f : V → Finset V
  irr : ∀ x, x ∉ f x
  cov : ∀ x ∈ dom, ∀ y, G.Adj x y → y ∈ f x ∨ (y ∈ dom ∧ x ∈ f y)
  out : ∀ x ∉ dom, f x = ∅

private instance partialOrientOrder {V : Type*} (G : SimpleGraph V) :
    PartialOrder (PartialOrient G) where
  le p q := p.dom ⊆ q.dom ∧ ∀ x ∈ p.dom, p.f x = q.f x
  le_refl p := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1, fun x hx => (hpq.2 x hx).trans (hqr.2 x (hpq.1 hx))⟩
  le_antisymm p q hpq hqp := by
    cases p with | mk dp fp ip cp op =>
    cases q with | mk dq fq iq cq oq =>
    dsimp at hpq hqp
    have hd : dp = dq := Subset.antisymm hpq.1 hqp.1
    subst hd
    have hf : fp = fq := by
      funext x
      by_cases hx : x ∈ dp
      · exact hpq.2 x hx
      · rw [op x hx, oq x hx]
    subst hf
    rfl

/-- Every graph without an infinite simple path admits a finite orientation `F : V → Finset V`. -/
lemma finiteOrientation {V : Type*} (G : SimpleGraph V)
    (hno : ¬ ∃ p : ℕ → V, Function.Injective p ∧ ∀ n, G.Adj (p n) (p (n + 1))) :
    ∃ F : V → Finset V, (∀ x, x ∉ F x) ∧ (∀ x y, G.Adj x y → y ∈ F x ∨ x ∈ F y) := by
  classical
  have hchain : ∀ c : Set (PartialOrient G), IsChain (· ≤ ·) c → BddAbove c := by
    intro c hch
    let S := ⋃ p ∈ c, p.dom
    let f : V → Finset V := fun x =>
      if hx : ∃ p ∈ c, x ∈ p.dom then (Classical.choose hx).f x else ∅
    have hf_eq : ∀ p ∈ c, ∀ x ∈ p.dom, f x = p.f x := fun p hp x hx => by
      have hex : ∃ q ∈ c, x ∈ q.dom := ⟨p, hp, hx⟩
      simp only [f, dif_pos hex]
      let q := Classical.choose hex
      have hq := Classical.choose_spec hex
      rcases hch.total hq.1 hp with ⟨_, hqp⟩ | ⟨_, hpq⟩
      · exact hqp x hq.2
      · exact (hpq x hx).symm
    let ub : PartialOrient G :=
      { dom := S
        f := f
        irr := fun x => by
          by_cases hex : ∃ p ∈ c, x ∈ p.dom
          · obtain ⟨p, hp, hxp⟩ := hex
            rw [hf_eq p hp x hxp]
            exact p.irr x
          · simp [f, hex]
        cov := fun x hx y hadj => by
          obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 hx
          rcases p.cov x hxp y hadj with h1 | ⟨hy, h2⟩
          · left; rwa [hf_eq p hp x hxp]
          · right; refine ⟨Set.mem_biUnion hp hy, ?_⟩; rwa [hf_eq p hp y hy]
        out := fun x hx => by
          have hne : ¬ ∃ p ∈ c, x ∈ p.dom := fun ⟨p, hp, hxp⟩ => hx (Set.mem_biUnion hp hxp)
          simp [f, hne] }
    exact ⟨ub, fun p hp => ⟨Set.subset_biUnion_of_mem hp, fun x hx => (hf_eq p hp x hx).symm⟩⟩
  obtain ⟨m, hm_max⟩ := zorn_le hchain
  have huniv : m.dom = Set.univ := by
    by_contra hne
    have hcomp : m.domᶜ.Nonempty := Set.nonempty_compl.2 hne
    obtain ⟨x, hx, hfin⟩ := exists_finite_deg_in_subset hno hcomp
    let m' : PartialOrient G :=
      { dom := insert x m.dom
        f := Function.update m.f x hfin.toFinset
        irr := fun z => by
          by_cases hzx : z = x
          · subst hzx; simp
          · simp [hzx, m.irr z]
        cov := fun z hz y hadj => by
          rcases Set.mem_insert_iff.1 hz with rfl | hzm
          · by_cases hym : y ∈ m.dom
            · rcases m.cov y hym z hadj.symm with h1 | ⟨hz', _⟩
              · right; refine ⟨Set.mem_insert_of_mem z hym, ?_⟩
                have hyx : y ≠ z := hadj.ne'
                simp [hyx, h1]
              · exact (hx hz').elim
            · left; simp [hfin.mem_toFinset, hym, hadj]
          · have hzx : z ≠ x := fun h => hx (h ▸ hzm)
            rcases m.cov z hzm y hadj with h1 | ⟨hym, h2⟩
            · left; simp [hzx, h1]
            · right
              have hyx : y ≠ x := fun h => hx (h ▸ hym)
              exact ⟨Set.mem_insert_of_mem x hym, by simp [hyx, h2]⟩
        out := fun z hz => by
          have hzx : z ≠ x := fun h => hz (h ▸ Set.mem_insert x m.dom)
          have hzm : z ∉ m.dom := fun h => hz (Set.mem_insert_of_mem x h)
          simp [hzx, m.out z hzm] }
    have hle : m ≤ m' :=
      ⟨Set.subset_insert x m.dom, fun z hz => by
        have hzx : z ≠ x := fun h => hx (h ▸ hz)
        simp [m', hzx]⟩
    have hge : m' ≤ m := hm_max hle
    exact hx (hge.1 (Set.mem_insert x m.dom))
  refine ⟨m.f, m.irr, fun x y hadj => ?_⟩
  have hx : x ∈ m.dom := huniv ▸ Set.mem_univ x
  rcases m.cov x hx y hadj with h | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Every finite set mapping on a set of cardinality `≤ ℵ₁` is `ℕ`-colorable. -/
lemma natColoring_of_finsetMapping {V : Type} (hcard : #V ≤ ℵ₁)
    (F : V → Finset V) (hirr : ∀ x, x ∉ F x) :
    ∃ c : V → ℕ, ∀ x y, y ∈ F x → c x ≠ c y := by
  classical
  have hmk : #V ≤ #(ω₁ : Ordinal.{0}).ToType := by
    simpa [Cardinal.mk_toType, Ordinal.card_omega] using hcard
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hmk
  -- One-step F-closure
  let step : Set V → Set V := fun s => s ∪ ⋃ x ∈ s, (F x : Set V)
  have hstep_cnt : ∀ s : Set V, s.Countable → (step s).Countable := fun s hs =>
    hs.union (hs.biUnion fun x _ => (F x).countable_toSet)
  let cl : Set V → Set V := fun s => ⋃ n : ℕ, step^[n] s
  have hcl_cnt : ∀ s : Set V, s.Countable → (cl s).Countable := fun s hs =>
    Set.countable_iUnion fun n => by
      induction n with
      | zero => exact hs
      | succ n ih => simpa [Function.iterate_succ_apply'] using hstep_cnt _ ih
  have hcl_sub : ∀ s : Set V, s ⊆ cl s := fun s =>
    Set.subset_iUnion (fun n => step^[n] s) 0
  have hcl_mono : Monotone cl := fun s t hst =>
    Set.iUnion_mono fun n => by
      induction n with
      | zero => exact hst
      | succ n ih =>
        intro x hx
        simp only [Function.iterate_succ_apply', step, Set.mem_union, Set.mem_iUnion] at hx ⊢
        rcases hx with hx | ⟨y, hy, hxy⟩
        · exact Or.inl (ih hx)
        · exact Or.inr ⟨y, ih hy, hxy⟩
  have hcl_closed : ∀ s : Set V, ∀ x ∈ cl s, ∀ y ∈ F x, y ∈ cl s := by
    intro s x hx y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    refine Set.mem_iUnion.2 ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact Or.inr (Set.mem_biUnion hn hy)
  have : NoMaxOrder (ω₁ : Ordinal.{0}).ToType :=
    ⟨fun x => by
      obtain ⟨y, hy⟩ := exists_gt_of_countable_omega1 (Set.countable_singleton x)
      exact ⟨y, hy x rfl⟩⟩
  -- M ξ = F-closure of {v | e v < ξ}
  let M : (ω₁ : Ordinal.{0}).ToType → Set V := fun ξ => cl {v : V | e v < ξ}
  have hM_cnt : ∀ ξ : (ω₁ : Ordinal.{0}).ToType, (M ξ).Countable := fun ξ => by
    refine hcl_cnt _ ?_
    have hpre : {v : V | e v < ξ} = e ⁻¹' Set.Iio ξ := rfl
    rw [hpre]
    exact (countable_Iio_omega1 ξ).preimage e.injective
  have hM_mono : Monotone M := fun ξ₁ ξ₂ hle =>
    hcl_mono fun v hv => lt_of_lt_of_le hv hle
  -- Every v lies in M (Order.succ (e v))
  have hv_mem : ∀ v : V, ∃ ξ : (ω₁ : Ordinal.{0}).ToType, v ∈ M (Order.succ ξ) := fun v =>
    ⟨e v, hcl_sub _ (Order.lt_succ (e v))⟩
  -- rank v = least ξ with v ∈ M (Order.succ ξ)
  let rank : V → (ω₁ : Ordinal.{0}).ToType := fun v =>
    WellFounded.min wellFounded_lt {ξ : (ω₁ : Ordinal.{0}).ToType | v ∈ M (Order.succ ξ)} (hv_mem v)
  have hrank_mem : ∀ v : V, v ∈ M (Order.succ (rank v)) := fun v =>
    WellFounded.min_mem wellFounded_lt {ξ : (ω₁ : Ordinal.{0}).ToType | v ∈ M (Order.succ ξ)} (hv_mem v)
  have hrank_min : ∀ v ξ, v ∈ M (Order.succ ξ) → rank v ≤ ξ := fun v ξ h =>
    le_of_not_gt (WellFounded.not_lt_min wellFounded_lt
      {η : (ω₁ : Ordinal.{0}).ToType | v ∈ M (Order.succ η)} h)
  have hM_not_mem : ∀ v : V, v ∉ M (rank v) := by
    intro v hv
    have hsub_union : ∀ n : ℕ, step^[n] {u : V | e u < rank v} ⊆
        ⋃ (η : (ω₁ : Ordinal.{0}).ToType) (_ : η < rank v), M (Order.succ η) := by
      intro n
      induction n with
      | zero =>
        intro u hu
        refine Set.mem_iUnion₂.2 ⟨e u, hu, hcl_sub _ (Order.lt_succ (e u))⟩
      | succ n ih =>
        intro u hu
        rw [Function.iterate_succ_apply'] at hu
        rcases hu with hu | hu
        · exact ih hu
        · obtain ⟨w, hw, huw⟩ := Set.mem_iUnion₂.1 hu
          obtain ⟨η, hη, hwη⟩ := Set.mem_iUnion₂.1 (ih hw)
          exact Set.mem_iUnion₂.2 ⟨η, hη, hcl_closed _ w hwη u huw⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hv
    obtain ⟨η, hη, hvη⟩ := Set.mem_iUnion₂.1 (hsub_union n hn)
    exact not_le.2 hη (hrank_min v η hvη)
  -- Each layer D ξ = {v | rank v = ξ} ⊆ M (Order.succ ξ) is countable; pick non-dependent idx ξ : V → ℕ
  have hidx_ex : ∀ ξ : (ω₁ : Ordinal.{0}).ToType,
      ∃ f : V → ℕ, ∀ u w : V, rank u = ξ → rank w = ξ → f u = f w → u = w := fun ξ => by
    have hsub : {v : V | rank v = ξ} ⊆ M (Order.succ ξ) := fun v hv => hv ▸ hrank_mem v
    have hcnt : Countable {v : V // rank v = ξ} :=
      Set.countable_coe_iff.1 ((hM_cnt (Order.succ ξ)).mono hsub)
    obtain ⟨g, hg⟩ := @Countable.exists_injective_nat _ hcnt
    refine ⟨fun v => if h : rank v = ξ then g ⟨v, h⟩ else 0, fun u w hu hw heq => ?_⟩
    simp only [dif_pos hu, dif_pos hw] at heq
    exact congrArg Subtype.val (hg heq)
  choose idx hidx_inj using hidx_ex
  let key : V → (ω₁ : Ordinal.{0}).ToType ×ₗ ℕ := fun v => toLex (rank v, idx (rank v) v)
  let prec : V → V → Prop := fun u v => key u < key v
  have hwf : WellFounded prec := InvImage.wf key wellFounded_lt
  have hfin_nbrs : ∀ v : V,
      {u : V | prec u v ∧ (u ∈ F v ∨ v ∈ F u)}.Finite := fun v => by
    have hsub : {u : V | prec u v ∧ (u ∈ F v ∨ v ∈ F u)} ⊆
        (F v : Set V) ∪ {u : V | rank u = rank v ∧ idx (rank v) u < idx (rank v) v} := by
      intro u ⟨huv, hedge⟩
      rcases Prod.lex_iff.1 huv with hlt | ⟨heq, hlt_idx⟩
      · left
        rcases hedge with h1 | h2
        · exact h1
        · exfalso
          have huM : u ∈ M (rank v) :=
            hM_mono (Order.succ_le_of_lt hlt) (hrank_mem u)
          exact hM_not_mem v (hcl_closed _ u huM v h2)
      · right
        have heq' : rank u = rank v := heq
        have hlt_idx' : idx (rank u) u < idx (rank v) v := hlt_idx
        rw [heq'] at hlt_idx'
        exact ⟨heq', hlt_idx'⟩
    refine ((F v).finite_toSet.union ?_).subset hsub
    let S := {u : V | rank u = rank v ∧ idx (rank v) u < idx (rank v) v}
    let g : S → Fin (idx (rank v) v) := fun u => ⟨idx (rank v) u.1, u.2.2⟩
    have hg_inj : Function.Injective g := fun a b hab =>
      Subtype.ext (hidx_inj (rank v) a.1 b.1 a.2.1 b.2.1 (congrArg Fin.val hab))
    exact Set.finite_coe_iff.1 (Finite.of_injective g hg_inj)
  -- Greedy coloring along prec by well-founded recursion
  let c : V → ℕ := hwf.fix fun v rec =>
    let N := (hfin_nbrs v).toFinset
    (N.attach.image fun u => rec u.1 ((hfin_nbrs v).mem_toFinset.1 u.2).1).sup id + 1
  refine ⟨c, fun x y hyx => ?_⟩
  have hxy_ne : x ≠ y := fun h => hirr x (h ▸ hyx)
  have hkey_ne : key x ≠ key y := by
    intro hk
    have hr : rank x = rank y := congrArg (fun p => (ofLex p).1) hk
    have hi : idx (rank x) x = idx (rank y) y := congrArg (fun p => (ofLex p).2) hk
    rw [hr] at hi
    exact hxy_ne (hidx_inj (rank y) x y hr rfl hi)
  rcases lt_or_gt_of_ne hkey_ne with hlt | hgt
  · -- key x < key y, so x is a prec-smaller neighbor of y
    have hmem : x ∈ (hfin_nbrs y).toFinset :=
      (hfin_nbrs y).mem_toFinset.2 ⟨hlt, Or.inr hyx⟩
    have hcy : c y = ((hfin_nbrs y).toFinset.attach.image
        fun u => c u.1).sup id + 1 := WellFounded.fix_eq hwf _ y
    have hle : c x ≤ ((hfin_nbrs y).toFinset.attach.image fun u => c u.1).sup id :=
      Finset.le_sup (f := id)
        (Finset.mem_image.2 ⟨⟨x, hmem⟩, Finset.mem_attach _ _, rfl⟩)
    omega
  · -- key y < key x, so y is a prec-smaller neighbor of x
    have hmem : y ∈ (hfin_nbrs x).toFinset :=
      (hfin_nbrs x).mem_toFinset.2 ⟨hgt, Or.inl hyx⟩
    have hcx : c x = ((hfin_nbrs x).toFinset.attach.image
        fun u => c u.1).sup id + 1 := WellFounded.fix_eq hwf _ x
    have hle : c y ≤ ((hfin_nbrs x).toFinset.attach.image fun u => c u.1).sup id :=
      Finset.le_sup (f := id)
        (Finset.mem_image.2 ⟨⟨y, hmem⟩, Finset.mem_attach _ _, rfl⟩)
    omega

end FiniteSetMappings

/- ## Section 3: Part A (`H1`) — Free Sets for `ω₁ * γ < ω₁ ^ (ω + 2)` -/

section PartH1

/-- Every `ℕ`-coloring of a well-order of type `ω₁ ^ n` (`n ≥ 1`) has a monochromatic subset
of full order type `ω₁ ^ n`. -/
lemma indivisible_omega1_pow :
    ∀ n : ℕ, 1 ≤ n →
      ∀ {X : Type} [LinearOrder X] [WellFoundedLT X],
        typeLT X = ω₁ ^ (n : Ordinal.{0}) →
        ∀ c : X → ℕ, ∃ k : ℕ, typeLT (c ⁻¹' {k} : Set X) = ω₁ ^ (n : Ordinal.{0}) := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction m with
  | zero =>
    intro X _ _ hX c
    simp only [zero_add, Nat.cast_one, Ordinal.opow_one] at hX ⊢
    by_contra hall
    push Not at hall
    have hcnt : ∀ k : ℕ, (c ⁻¹' {k}).Countable := fun k => by
      have hlt : typeLT (c ⁻¹' {k} : Set X) < ω₁ :=
        lt_of_le_of_ne ((typeLT_set_le_self _).trans_eq hX) (hall k)
      exact Set.countable_coe_iff.1 (countable_of_typeLT_lt_omega1 hlt)
    have huniv : (Set.univ : Set X) = ⋃ k : ℕ, c ⁻¹' {k} := by ext x; simp
    have : Countable X := Set.countable_univ_iff.1 (huniv ▸ Set.countable_iUnion hcnt)
    have hlt := typeLT_lt_omega1_of_countable (α := X)
    rw [hX] at hlt
    exact lt_irrefl _ hlt
  | succ m ih =>
    intro X _ _ hX c
    have hexp : ω₁ ^ ((m + 1 + 1 : ℕ) : Ordinal.{0}) =
        ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0}) * ω₁ := by
      rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
    have hprod : typeLT ((ω₁ : Ordinal.{0}).ToType ×ₗ (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType) =
        ω₁ ^ ((m + 1 + 1 : ℕ) : Ordinal.{0}) := by
      rw [typeLT_prodLex, Ordinal.type_toType, Ordinal.type_toType, hexp]
    obtain ⟨e1⟩ := exists_orderIso_toType hX
    obtain ⟨e2⟩ := exists_orderIso_toType hprod
    let φ : (ω₁ : Ordinal.{0}).ToType ×ₗ (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType ≃o X := e2.trans e1.symm
    have hslice : ∀ ξ : (ω₁ : Ordinal.{0}).ToType, ∃ k : ℕ,
        typeLT ((fun y : (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType =>
          c (φ (toLex (ξ, y)))) ⁻¹' {k} : Set _) = ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0}) := fun ξ =>
      ih (by omega) (X := (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType)
        (Ordinal.type_toType _) (fun y => c (φ (toLex (ξ, y))))
    choose g hg using hslice
    have hbase : ∃ k : ℕ, typeLT (g ⁻¹' {k} : Set (ω₁ : Ordinal.{0}).ToType) = ω₁ := by
      by_contra hall
      push Not at hall
      have hcnt : ∀ k : ℕ, (g ⁻¹' {k}).Countable := fun k =>
        Set.countable_coe_iff.1 (countable_of_typeLT_lt_omega1
          (lt_of_le_of_ne ((typeLT_set_le_self _).trans_eq (Ordinal.type_toType ω₁)) (hall k)))
      have : Countable (ω₁ : Ordinal.{0}).ToType :=
        Set.countable_univ_iff.1 (by
          have : (Set.univ : Set (ω₁ : Ordinal.{0}).ToType) = ⋃ k : ℕ, g ⁻¹' {k} := by ext x; simp
          rw [this]; exact Set.countable_iUnion hcnt)
      have hlt := typeLT_lt_omega1_of_countable (α := (ω₁ : Ordinal.{0}).ToType)
      rw [Ordinal.type_toType] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨k, hk⟩ := hbase
    refine ⟨k, le_antisymm ((typeLT_set_le_self _).trans_eq hX) ?_⟩
    obtain ⟨eξ⟩ := exists_orderIso_toType hk
    have hey : ∀ ξ : (g ⁻¹' {k} : Set (ω₁ : Ordinal.{0}).ToType),
        Nonempty ((ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType ≃o
          ((fun y : (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType =>
            c (φ (toLex (ξ.1, y)))) ⁻¹' {k} : Set _)) := fun ξ => by
      have h1 : typeLT ((fun y : (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType =>
          c (φ (toLex (ξ.1, y)))) ⁻¹' {k} : Set _) = ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0}) := by
        have hset : ((fun y : (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType =>
            c (φ (toLex (ξ.1, y)))) ⁻¹' {k}) =
            ((fun y : (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType =>
            c (φ (toLex (ξ.1, y)))) ⁻¹' {g ξ.1}) := by
          have hgk : g ξ.1 = k := ξ.2
          rw [hgk]
        rw [hset]
        exact hg ξ.1
      obtain ⟨e'⟩ := exists_orderIso_toType h1
      exact ⟨e'.symm⟩
    let ψ := fun ξ => Classical.choice (hey ξ)
    let emb : (ω₁ : Ordinal.{0}).ToType ×ₗ (ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0})).ToType →
        (c ⁻¹' {k} : Set X) := fun p =>
      let ξ := eξ.symm (ofLex p).1
      let y := ψ ξ (ofLex p).2
      ⟨φ (toLex (ξ.1, y.1)), y.2⟩
    have hemb : StrictMono emb := by
      intro p q hpq
      cases p with | _ p' => cases q with | _ q' =>
      cases p' with | mk p1 p2 => cases q' with | mk q1 q2 =>
      rcases Prod.lex_iff.1 hpq with h1 | ⟨h1, h2⟩
      · exact φ.strictMono (Prod.Lex.left _ _ (eξ.symm.strictMono h1))
      · subst h1
        exact φ.strictMono (Prod.Lex.right _ ((ψ (eξ.symm p1)).strictMono h2))
    exact hprod ▸ typeLT_le_of_strictMono hemb

/-- Any well-order of type `ω₁ ^ n` (`n ≥ 1`) splits into `ω₁` pairwise disjoint subsets,
each of full order type `ω₁ ^ n`. -/
lemma omega1_split_omega1_pow {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [LinearOrder X] [WellFoundedLT X]
    (hX : typeLT X = ω₁ ^ (n : Ordinal.{0})) :
    ∃ P : (ω₁ : Ordinal.{0}).ToType → Set X,
      Pairwise (Function.onFun Disjoint P) ∧
      ∀ ξ : (ω₁ : Ordinal.{0}).ToType, typeLT (P ξ) = ω₁ ^ (n : Ordinal.{0}) := by
  have hmk : #((ω₁ : Ordinal.{0}).ToType × (ω₁ : Ordinal.{0}).ToType) = #(ω₁ : Ordinal.{0}).ToType := by
    simp only [Cardinal.mk_prod, Cardinal.mk_toType, Ordinal.card_omega, Cardinal.lift_id]
    exact Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)
  obtain ⟨bi⟩ := Cardinal.eq.1 hmk
  let Q : (ω₁ : Ordinal.{0}).ToType → Set (ω₁ : Ordinal.{0}).ToType :=
    fun ξ => Set.range (fun η : (ω₁ : Ordinal.{0}).ToType => bi (ξ, η))
  have hQ_disj : Pairwise (Function.onFun Disjoint Q) := by
    intro ξ₁ ξ₂ hne
    change Disjoint (Q ξ₁) (Q ξ₂)
    rw [Set.disjoint_left]
    rintro x ⟨η₁, rfl⟩ ⟨η₂, h2⟩
    exact hne (congrArg Prod.fst (bi.injective h2.symm))
  have hQ_type : ∀ ξ : (ω₁ : Ordinal.{0}).ToType, typeLT (Q ξ) = ω₁ := fun ξ => by
    refine le_antisymm ((typeLT_set_le_self _).trans_eq (Ordinal.type_toType ω₁)) ?_
    by_contra hlt
    push Not at hlt
    have : Countable (Q ξ) := countable_of_typeLT_lt_omega1 hlt
    have hinj : Function.Injective (fun η : (ω₁ : Ordinal.{0}).ToType => (⟨bi (ξ, η), ⟨η, rfl⟩⟩ : Q ξ)) :=
      fun a b h => congrArg Prod.snd (bi.injective (congrArg Subtype.val h))
    have : Countable (ω₁ : Ordinal.{0}).ToType := Function.Injective.countable hinj
    have hlt2 := typeLT_lt_omega1_of_countable (α := (ω₁ : Ordinal.{0}).ToType)
    rw [Ordinal.type_toType] at hlt2
    exact lt_irrefl _ hlt2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hexp : ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0}) = ω₁ ^ (m : Ordinal.{0}) * ω₁ := by
    rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
  have hprod : typeLT ((ω₁ : Ordinal.{0}).ToType ×ₗ (ω₁ ^ (m : Ordinal.{0})).ToType) =
      ω₁ ^ ((m + 1 : ℕ) : Ordinal.{0}) := by
    rw [typeLT_prodLex, Ordinal.type_toType, Ordinal.type_toType, hexp]
  obtain ⟨e1⟩ := exists_orderIso_toType hX
  obtain ⟨e2⟩ := exists_orderIso_toType hprod
  let φ : (ω₁ : Ordinal.{0}).ToType ×ₗ (ω₁ ^ (m : Ordinal.{0})).ToType ≃o X := e2.trans e1.symm
  let P : (ω₁ : Ordinal.{0}).ToType → Set X := fun ξ =>
    {x : X | (ofLex (φ.symm x)).1 ∈ Q ξ}
  refine ⟨P, ?_, ?_⟩
  · intro ξ₁ ξ₂ hne
    change Disjoint (P ξ₁) (P ξ₂)
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact Set.disjoint_left.1 (hQ_disj hne) hx1 hx2
  · intro ξ
    refine le_antisymm ((typeLT_set_le_self _).trans_eq hX) ?_
    obtain ⟨eQ⟩ := exists_orderIso_toType (hQ_type ξ)
    let emb : (ω₁ : Ordinal.{0}).ToType ×ₗ (ω₁ ^ (m : Ordinal.{0})).ToType → P ξ := fun p =>
      ⟨φ (toLex ((eQ.symm (ofLex p).1).1, (ofLex p).2)), by simp [P, (eQ.symm (ofLex p).1).2]⟩
    have hemb : StrictMono emb := by
      intro p q hpq
      cases p with | _ p' => cases q with | _ q' =>
      cases p' with | mk p1 p2 => cases q' with | mk q1 q2 =>
      rcases Prod.lex_iff.1 hpq with h1 | ⟨h1, h2⟩
      · exact φ.strictMono (Prod.Lex.left _ _ (eQ.symm.strictMono h1))
      · subst h1
        exact φ.strictMono (Prod.Lex.right _ h2)
    exact hprod ▸ typeLT_le_of_strictMono hemb

lemma nat_split_omega1_pow {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [LinearOrder X] [WellFoundedLT X]
    (hX : typeLT X = ω₁ ^ (n : Ordinal.{0})) :
    ∃ P : ℕ → Set X,
      Pairwise (Function.onFun Disjoint P) ∧
      ∀ k : ℕ, typeLT (P k) = ω₁ ^ (n : Ordinal.{0}) := by
  obtain ⟨P, hP_disj, hP_type⟩ := omega1_split_omega1_pow hn hX
  have hinf : Infinite (ω₁ : Ordinal.{0}).ToType := by
    rw [← Cardinal.aleph0_le_mk_iff, Cardinal.mk_toType, Ordinal.card_omega]
    exact Cardinal.aleph0_le_aleph 1
  let e := Infinite.natEmbedding (ω₁ : Ordinal.{0}).ToType
  exact ⟨fun k => P (e k), fun i j hij => hP_disj (e.injective.ne hij), fun k => hP_type (e k)⟩

/-- Helper: given subsets `A` of type `ω₁^mA` and `B` of type `ω₁^mB` (`mA, mB ≥ 1`),
shrink both preserving order type so that `F` sends no point of `A'` into `B'`. -/
lemma shrink_avoid_forward {V : Type} [LinearOrder V] [WellFoundedLT V]
    (F : V → Finset V) {mA mB : ℕ} (hmA : 1 ≤ mA) (hmB : 1 ≤ mB)
    {A B : Set V} (hA : typeLT A = ω₁ ^ (mA : Ordinal.{0}))
    (hB : typeLT B = ω₁ ^ (mB : Ordinal.{0})) :
    ∃ A' B' : Set V, A' ⊆ A ∧ B' ⊆ B ∧
      typeLT A' = ω₁ ^ (mA : Ordinal.{0}) ∧
      typeLT B' = ω₁ ^ (mB : Ordinal.{0}) ∧
      ∀ x ∈ A', ∀ y ∈ B', y ∉ F x := by
  classical
  obtain ⟨Q, hQ_disj, hQ_type⟩ := nat_split_omega1_pow hmB hB
  let Qv : ℕ → Set V := fun r => Subtype.val '' Q r
  have hQv_sub : ∀ r, Qv r ⊆ B := fun r x ⟨y, _, hy⟩ => hy ▸ y.2
  have hQv_type : ∀ r, typeLT (Qv r) = ω₁ ^ (mB : Ordinal.{0}) := fun r => by
    exact (typeLT_image_val (Q r)).trans (hQ_type r)
  have hQv_disj : Pairwise (Function.onFun Disjoint Qv) := fun i j hij => by
    change Disjoint (Qv i) (Qv j)
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have : a = b := Subtype.ext hba.symm
    subst this
    exact Set.disjoint_left.1 (hQ_disj hij) ha hb
  have hpick : ∀ x : A, ∃ r : ℕ, ∀ y ∈ Qv r, y ∉ F x.1 := fun x => by
    let owner : V → ℕ := fun y =>
      if h : ∃ r, y ∈ Qv r then Classical.choose h else 0
    refine ⟨(F x.1).sup owner + 1, fun y hy hmem => ?_⟩
    have hex : ∃ r, y ∈ Qv r := ⟨(F x.1).sup owner + 1, hy⟩
    have hown : owner y = (F x.1).sup owner + 1 := by
      simp only [owner, dif_pos hex]
      by_contra hne
      exact Set.disjoint_left.1 (hQv_disj hne) (Classical.choose_spec hex) hy
    have hle : owner y ≤ (F x.1).sup owner := Finset.le_sup hmem
    omega
  choose rfun hrfun using hpick
  obtain ⟨r0, hr0⟩ := indivisible_omega1_pow mA hmA hA rfun
  let A' : Set V := Subtype.val '' (rfun ⁻¹' {r0})
  refine ⟨A', Qv r0, fun x ⟨a, _, ha⟩ => ha ▸ a.2, hQv_sub r0, ?_, hQv_type r0, ?_⟩
  · exact (typeLT_image_val _).trans hr0
  · rintro x ⟨a, ha, rfl⟩ y hy
    have h1 : rfun a = r0 := ha
    rw [← h1] at hy
    exact hrfun a y hy

/-- Simultaneous free sets inside a countable pairwise-disjoint family of blocks of order types
`ω₁ ^ (m k)` (`m k ≥ 1` whenever `B k` is nonempty). -/
lemma countable_family_free {V : Type} [LinearOrder V] [WellFoundedLT V]
    (hcard : #V ≤ ℵ₁) (F : V → Finset V) (hirr : ∀ x, x ∉ F x)
    (B : ℕ → Set V) (hdisj : Pairwise (Function.onFun Disjoint B))
    (m : ℕ → ℕ)
    (hB : ∀ k, B k = ∅ ∨ (1 ≤ m k ∧ typeLT (B k) = ω₁ ^ (m k : Ordinal.{0}))) :
    ∃ S : ℕ → Set V,
      (∀ k, S k ⊆ B k ∧ typeLT (S k) = typeLT (B k)) ∧
      (∀ x ∈ ⋃ k, S k, ∀ y ∈ ⋃ k, S k, y ∉ F x) := by
  classical
  obtain ⟨col, hcol⟩ := natColoring_of_finsetMapping hcard F hirr
  -- State after k steps: chosen S_0,...,S_{k-1} (stored as a function ℕ → Set V) and reservoirs R_l (l ≥ k)
  let Inv (k : ℕ) (S R : ℕ → Set V) : Prop :=
    (∀ i < k, S i ⊆ B i ∧ typeLT (S i) = typeLT (B i)) ∧
    (∀ l ≥ k, R l ⊆ B l ∧ typeLT (R l) = typeLT (B l)) ∧
    (∀ i < k, ∀ j < k, ∀ x ∈ S i, ∀ y ∈ S j, y ∉ F x) ∧
    (∀ i < k, ∀ l ≥ k, ∀ x ∈ S i, ∀ y ∈ R l, y ∉ F x ∧ x ∉ F y)
  have hstep : ∀ (k : ℕ) (S R : ℕ → Set V), Inv k S R →
      ∃ S' R' : ℕ → Set V,
        (∀ i < k, S' i = S i) ∧ Inv (k + 1) S' R' := by
    intro k S R ⟨hS_sub, hR_sub, hSS, hSR⟩
    rcases hB k with hBk_empty | ⟨hmk, hBk_type⟩
    · -- B k = ∅: trivial step
      let S' := Function.update S k (∅ : Set V)
      refine ⟨S', R, fun i hi => by simp [S', hi.ne], ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · subst hik
          have hupd : S' i = ∅ := Function.update_self i ∅ S
          rw [hupd, hBk_empty]
          exact ⟨Subset.refl _, rfl⟩
        · have hlt : i < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hik
          have hupd : S' i = S i := Function.update_of_ne hik ∅ S
          rw [hupd]
          exact hS_sub i hlt
      · intro l hl; exact hR_sub l (Nat.le_of_succ_le hl)
      · intro i hi j hj x hx y hy
        by_cases hik : i = k
        · subst hik; simp [S'] at hx
        · by_cases hjk : j = k
          · subst hjk; simp [S'] at hy
          · simp [S', hik] at hx; simp [S', hjk] at hy
            exact hSS i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hik)
              j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hj) hjk) x hx y hy
      · intro i hi l hl x hx y hy
        by_cases hik : i = k
        · subst hik; simp [S'] at hx
        · simp [S', hik] at hx
          exact hSR i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hik)
            l (Nat.le_of_succ_le hl) x hx y hy
    · -- B k has type ω₁ ^ (m k), 1 ≤ m k
      have hRk_type : typeLT (R k) = ω₁ ^ (m k : Ordinal.{0}) :=
        (hR_sub k le_rfl).2.trans hBk_type
      -- Step 1: make A0 ⊆ R k F-free via col
      obtain ⟨c0, hc0⟩ := indivisible_omega1_pow (m k) hmk hRk_type (fun x : R k => col x.1)
      let A0 : Set V := Subtype.val '' ((fun x : R k => col x.1) ⁻¹' {c0})
      have hA0_sub : A0 ⊆ R k := fun x ⟨a, _, ha⟩ => ha ▸ a.2
      have hA0_type : typeLT A0 = ω₁ ^ (m k : Ordinal.{0}) :=
        (typeLT_image_val _).trans hc0
      have hA0_free : ∀ x ∈ A0, ∀ y ∈ A0, y ∉ F x := by
        rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hmem
        have h1 : col a.1 = c0 := ha
        have h2 : col b.1 = c0 := hb
        exact hcol a.1 b.1 hmem (h1.trans h2.symm)
      -- Step 2: bound max block index hit by F x for x ∈ A0
      let owner : V → ℕ := fun y =>
        if h : ∃ l, y ∈ B l then Classical.choose h else 0
      have howner : ∀ l y, y ∈ B l → owner y = l := fun l y hy => by
        have hex : ∃ l', y ∈ B l' := ⟨l, hy⟩
        simp only [owner, dif_pos hex]
        by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) (Classical.choose_spec hex) hy
      let Mfn : A0 → ℕ := fun x => (F x.1).sup owner
      obtain ⟨M0, hM0⟩ := indivisible_omega1_pow (m k) hmk hA0_type Mfn
      let A1 : Set V := Subtype.val '' (Mfn ⁻¹' {M0})
      have hA1_sub : A1 ⊆ A0 := fun x ⟨a, _, ha⟩ => ha ▸ a.2
      have hA1_type : typeLT A1 = ω₁ ^ (m k : Ordinal.{0}) :=
        (typeLT_image_val _).trans hM0
      have hA1_far : ∀ l > M0, ∀ x ∈ A1, ∀ y ∈ B l, y ∉ F x := by
        rintro l hl x ⟨a, ha, rfl⟩ y hy hmem
        have h1 : owner y ≤ (F a.1).sup owner := Finset.le_sup hmem
        have h2 : (F a.1).sup owner = M0 := ha
        rw [howner l y hy, h2] at h1
        omega
      -- Step 3: eliminate forward edges from A1 to R l for k < l ≤ k + t by induction on t
      have hclean_fwd : ∀ t : ℕ, ∃ (A' : Set V) (R' : ℕ → Set V),
          A' ⊆ A1 ∧ typeLT A' = ω₁ ^ (m k : Ordinal.{0}) ∧
          (∀ l ≥ k + 1, R' l ⊆ R l ∧ typeLT (R' l) = typeLT (R l)) ∧
          (∀ l, k < l → l ≤ k + t → ∀ x ∈ A', ∀ y ∈ R' l, y ∉ F x) := by
        intro t
        induction t with
        | zero =>
          exact ⟨A1, R, Subset.refl _, hA1_type, fun l _ => ⟨Subset.refl _, rfl⟩,
            fun l h1 h2 => by omega⟩
        | succ t iht =>
          obtain ⟨At, Rt, hAt_sub, hAt_type, hRt_sub, hRt_clean⟩ := iht
          let l0 := k + (t + 1)
          rcases hB l0 with hBl0_e | ⟨hml0, hBl0_type⟩
          · refine ⟨At, Rt, hAt_sub, hAt_type, hRt_sub, fun l hl1 hl2 x hx y hy => ?_⟩
            by_cases hll0 : l = l0
            · subst hll0
              have hyB : y ∈ B l0 := (hR_sub l0 (by omega)).1 ((hRt_sub l0 (by omega)).1 hy)
              rw [hBl0_e] at hyB; exact hyB.elim
            · exact hRt_clean l hl1 (by omega) x hx y hy
          · have hRtl0_type : typeLT (Rt l0) = ω₁ ^ (m l0 : Ordinal.{0}) :=
              (hRt_sub l0 (by omega)).2.trans ((hR_sub l0 (by omega)).2.trans hBl0_type)
            obtain ⟨At', B', hAt'_sub, hB'_sub, hAt'_type, hB'_type, hno_edge⟩ :=
              shrink_avoid_forward F hmk hml0 hAt_type hRtl0_type
            let Rt' := Function.update Rt l0 B'
            refine ⟨At', Rt', hAt'_sub.trans hAt_sub, hAt'_type, ?_, ?_⟩
            · intro l hl
              by_cases hll0 : l = l0
              · have hupd : Rt' l = B' := by simp [Rt', hll0]
                rw [hupd]
                subst hll0
                refine ⟨hB'_sub.trans (hRt_sub l0 hl).1, ?_⟩
                rw [hB'_type, ← hRtl0_type, (hRt_sub l0 hl).2]
              · have hupd : Rt' l = Rt l := Function.update_of_ne hll0 B' Rt
                rw [hupd]
                exact hRt_sub l hl
            · intro l hl1 hl2 x hx y hy
              by_cases hll0 : l = l0
              · subst hll0
                simp only [Rt', Function.update_self] at hy
                exact hno_edge x hx y hy
              · simp only [Rt', Function.update_of_ne hll0] at hy
                exact hRt_clean l hl1 (by omega) x (hAt'_sub hx) y hy
      obtain ⟨A2, R1, hA2_sub, hA2_type, hR1_sub, hR1_clean⟩ := hclean_fwd M0
      have hA2_all_fwd : ∀ l ≥ k + 1, ∀ x ∈ A2, ∀ y ∈ R1 l, y ∉ F x := by
        intro l hl x hx y hy
        by_cases hlM : l ≤ k + M0
        · exact hR1_clean l (by omega) hlM x hx y hy
        · exact hA1_far l (by omega) x (hA2_sub hx) y
            ((hR_sub l (by omega)).1 ((hR1_sub l hl).1 hy))
      -- Step 4: split A2 into ω₁ disjoint copies P ξ and kill backward edges from all l ≥ k + 1
      obtain ⟨P, hP_disj, hP_type⟩ := omega1_split_omega1_pow hmk hA2_type
      let Pv : (ω₁ : Ordinal.{0}).ToType → Set V := fun ξ => Subtype.val '' P ξ
      have hPv_sub : ∀ ξ, Pv ξ ⊆ A2 := fun ξ x ⟨a, _, ha⟩ => ha ▸ a.2
      have hPv_type : ∀ ξ, typeLT (Pv ξ) = ω₁ ^ (m k : Ordinal.{0}) := fun ξ =>
        (typeLT_image_val _).trans (hP_type ξ)
      have hPv_disj : Pairwise (Function.onFun Disjoint Pv) := fun ξ₁ ξ₂ hne => by
        change Disjoint (Pv ξ₁) (Pv ξ₂)
        rw [Set.disjoint_left]
        rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
        have : a = b := Subtype.ext hba.symm
        subst this
        exact Set.disjoint_left.1 (hP_disj hne) ha hb
      let Good : ℕ → (ω₁ : Ordinal.{0}).ToType → Set V := fun l ξ =>
        {y ∈ R1 l | ∀ x ∈ Pv ξ, x ∉ F y}
      let Bad : ℕ → Set (ω₁ : Ordinal.{0}).ToType := fun l =>
        {ξ : (ω₁ : Ordinal.{0}).ToType | k + 1 ≤ l ∧ typeLT (Good l ξ) < typeLT (R1 l)}
      have hBad_fin : ∀ l, (Bad l).Finite := fun l => by
        by_contra hinf
        by_cases hlk : k + 1 ≤ l
        · rcases hB l with hBl_e | ⟨hml, hBl_type⟩
          · have hR1l_e : R1 l = ∅ := Set.subset_eq_empty
              ((hR1_sub l hlk).1.trans (hR_sub l (by omega)).1) hBl_e
            have hBe : Bad l = ∅ := by
              ext ξ; simp only [Bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
              rintro ⟨_, hlt⟩
              have h0 : typeLT (R1 l) = 0 := by
                rw [hR1l_e]; exact Ordinal.type_eq_zero_iff_isEmpty.2 inferInstance
              rw [h0] at hlt
              exact not_lt_zero hlt
            exact hinf (hBe ▸ Set.finite_empty)
          · have hR1l_type : typeLT (R1 l) = ω₁ ^ (m l : Ordinal.{0}) :=
              (hR1_sub l hlk).2.trans ((hR_sub l (by omega)).2.trans hBl_type)
            have : Infinite (Bad l) := Set.infinite_coe_iff.2 hinf
            let emb := Infinite.natEmbedding (Bad l)
            let ξseq : ℕ → (ω₁ : Ordinal.{0}).ToType := fun t => (emb t).1
            have hξ_inj : Function.Injective ξseq := Subtype.val_injective.comp emb.injective
            have hpick : ∀ y : R1 l, ∃ t : ℕ, ∀ x ∈ Pv (ξseq t), x ∉ F y.1 := fun y => by
              let own : V → ℕ := fun x =>
                if h : ∃ t, x ∈ Pv (ξseq t) then Classical.choose h else 0
              refine ⟨(F y.1).sup own + 1, fun x hx hmem => ?_⟩
              have hex : ∃ t, x ∈ Pv (ξseq t) := ⟨(F y.1).sup own + 1, hx⟩
              have hown : own x = (F y.1).sup own + 1 := by
                simp only [own, dif_pos hex]
                by_contra hne
                exact Set.disjoint_left.1 (hPv_disj (hξ_inj.ne hne))
                  (Classical.choose_spec hex) hx
              have hle : own x ≤ (F y.1).sup own := Finset.le_sup hmem
              omega
            choose tfun htfun using hpick
            obtain ⟨t0, ht0⟩ := indivisible_omega1_pow (m l) hml hR1l_type tfun
            have hsub : Subtype.val '' (tfun ⁻¹' {t0}) ⊆ Good l (ξseq t0) := by
              rintro y ⟨a, ha, rfl⟩
              have h1 : tfun a = t0 := ha
              refine ⟨a.2, fun x hx => ?_⟩
              rw [← h1] at hx
              exact htfun a x hx
            have hge : ω₁ ^ (m l : Ordinal.{0}) ≤ typeLT (Good l (ξseq t0)) := by
              have h1 := typeLT_mono_subset hsub
              rw [typeLT_image_val, ht0] at h1
              exact h1
            have hlt : typeLT (Good l (ξseq t0)) < ω₁ ^ (m l : Ordinal.{0}) :=
              hR1l_type ▸ (emb t0).2.2
            exact not_lt.2 hge hlt
        · have hBe : Bad l = ∅ := by
            ext ξ; simp only [Bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨h1, _⟩; exact hlk h1
          exact hinf (hBe ▸ Set.finite_empty)
      have hunion_cnt : (⋃ l : ℕ, Bad l).Countable :=
        Set.countable_iUnion fun l => (hBad_fin l).countable
      have hex_good : ∃ ξ : (ω₁ : Ordinal.{0}).ToType, ξ ∉ ⋃ l : ℕ, Bad l := by
        by_contra hall
        push Not at hall
        have huniv : (Set.univ : Set (ω₁ : Ordinal.{0}).ToType) ⊆ ⋃ l : ℕ, Bad l := fun ξ _ => hall ξ
        have : Countable (ω₁ : Ordinal.{0}).ToType := Set.countable_univ_iff.1 (hunion_cnt.mono huniv)
        have hlt2 := typeLT_lt_omega1_of_countable (α := (ω₁ : Ordinal.{0}).ToType)
        rw [Ordinal.type_toType] at hlt2
        exact lt_irrefl _ hlt2
      obtain ⟨ξ0, hξ0⟩ := hex_good
      let S' := Function.update S k (Pv ξ0)
      let R' : ℕ → Set V := fun l => Good l ξ0
      have hPv0_sub_Rk : Pv ξ0 ⊆ R k := (hPv_sub ξ0).trans (hA2_sub.trans (hA1_sub.trans hA0_sub))
      have hPv0_sub_A0 : Pv ξ0 ⊆ A0 := (hPv_sub ξ0).trans (hA2_sub.trans hA1_sub)
      refine ⟨S', R', fun i hi => by simp [S', hi.ne], ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · subst hik
          have hupd : S' i = Pv ξ0 := Function.update_self i (Pv ξ0) S
          rw [hupd]
          exact ⟨hPv0_sub_Rk.trans (hR_sub i le_rfl).1, (hPv_type ξ0).trans hBk_type.symm⟩
        · have hlt : i < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hik
          have hupd : S' i = S i := Function.update_of_ne hik (Pv ξ0) S
          rw [hupd]
          exact hS_sub i hlt
      · intro l hl
        have hnotbad : ξ0 ∉ Bad l := fun h => hξ0 (Set.mem_iUnion.2 ⟨l, h⟩)
        have hge : typeLT (R1 l) ≤ typeLT (Good l ξ0) := by
          by_contra hlt; exact hnotbad ⟨hl, not_le.1 hlt⟩
        have hsub_R1 : Good l ξ0 ⊆ R1 l := fun y hy => hy.1
        have heq_type : typeLT (Good l ξ0) = typeLT (R1 l) :=
          le_antisymm (typeLT_mono_subset hsub_R1) hge
        exact ⟨hsub_R1.trans ((hR1_sub l hl).1.trans (hR_sub l (by omega)).1),
          heq_type.trans ((hR1_sub l hl).2.trans (hR_sub l (by omega)).2)⟩
      · intro i hi j hj x hx y hy
        by_cases hik : i = k <;> by_cases hjk : j = k
        · subst hik; subst hjk
          simp only [S', Function.update_self] at hx hy
          exact hA0_free x (hPv0_sub_A0 hx) y (hPv0_sub_A0 hy)
        · subst hik
          simp only [S', Function.update_self] at hx
          simp only [S', Function.update_of_ne hjk] at hy
          exact (hSR j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hj) hjk) i le_rfl
            y hy x (hPv0_sub_Rk hx)).2
        · subst hjk
          simp only [S', Function.update_of_ne hik] at hx
          simp only [S', Function.update_self] at hy
          exact (hSR i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hik) j le_rfl
            x hx y (hPv0_sub_Rk hy)).1
        · simp only [S', Function.update_of_ne hik] at hx
          simp only [S', Function.update_of_ne hjk] at hy
          exact hSS i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hik)
            j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hj) hjk) x hx y hy
      · intro i hi l hl x hx y hy
        by_cases hik : i = k
        · subst hik
          simp only [S', Function.update_self] at hx
          exact ⟨hA2_all_fwd l hl x (hPv_sub ξ0 hx) y hy.1, hy.2 x hx⟩
        · simp only [S', Function.update_of_ne hik] at hx
          exact hSR i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hik) l (by omega)
            x hx y ((hR1_sub l hl).1 hy.1)
  -- Run the recursion for all k : ℕ
  let State (k : ℕ) := {p : (ℕ → Set V) × (ℕ → Set V) // Inv k p.1 p.2}
  let initSt : State 0 := ⟨(fun _ => ∅, B),
    ⟨fun _ h => (Nat.not_lt_zero _ h).elim,
     fun l _ => ⟨Subset.refl _, rfl⟩,
     fun _ h => (Nat.not_lt_zero _ h).elim,
     fun _ h => (Nat.not_lt_zero _ h).elim⟩⟩
  let nextSt : ∀ k, State k → State (k + 1) := fun k prev =>
    let h := hstep k prev.1.1 prev.1.2 prev.2
    ⟨(Classical.choose h, Classical.choose (Classical.choose_spec h)),
      (Classical.choose_spec (Classical.choose_spec h)).2⟩
  let run : (k : ℕ) → State k := Nat.rec initSt nextSt
  have hstable : ∀ k m, k < m → (run m).1.1 k = (run (k + 1)).1.1 k := by
    intro k m hkm
    induction m with
    | zero => exact (Nat.not_lt_zero _ hkm).elim
    | succ m ih =>
      by_cases h : k = m
      · subst h; rfl
      · have hlt : k < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.1 hkm) h
        have hstep_eq : (run (m + 1)).1.1 k = (run m).1.1 k :=
          (Classical.choose_spec (Classical.choose_spec
            (hstep m (run m).1.1 (run m).1.2 (run m).2))).1 k hlt
        exact hstep_eq.trans (ih hlt)
  let Sfinal : ℕ → Set V := fun k => (run (k + 1)).1.1 k
  refine ⟨Sfinal, ?_, ?_⟩
  · intro k
    exact (run (k + 1)).2.1 k (Nat.lt_succ_self k)
  · intro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    let N := max i j + 1
    have hiN : i < N := by omega
    have hjN : j < N := by omega
    have hxi : x ∈ (run N).1.1 i := by rwa [hstable i N hiN]
    have hyj : y ∈ (run N).1.1 j := by rwa [hstable j N hjN]
    exact (run N).2.2.2.1 i hiN j hjN x hxi y hyj

/-- Custom well-ordered sigma type `LexSigma I F` with lexicographic order. -/
structure LexSigma (I : Type) (F : I → Type) where
  fst : I
  snd : F fst

instance lexSigmaLinearOrder {I : Type} {F : I → Type}
    [LinearOrder I] [∀ i, LinearOrder (F i)] : LinearOrder (LexSigma I F) where
  le a b := a.fst < b.fst ∨ ∃ h : a.fst = b.fst, h ▸ a.snd ≤ b.snd
  lt a b := a.fst < b.fst ∨ ∃ h : a.fst = b.fst, h ▸ a.snd < b.snd
  le_refl a := Or.inr ⟨rfl, le_rfl⟩
  le_trans a b c hab hbc := by
    cases a with | mk ia xa =>
    cases b with | mk ib xb =>
    cases c with | mk ic xc =>
    rcases hab with h1 | ⟨h1, h2⟩
    · rcases hbc with h3 | ⟨h3, _⟩
      · exact Or.inl (h1.trans h3)
      · dsimp at h3; subst h3; exact Or.inl h1
    · dsimp at h1; subst h1
      rcases hbc with h3 | ⟨h3, h4⟩
      · exact Or.inl h3
      · dsimp at h3; subst h3; exact Or.inr ⟨rfl, h2.trans h4⟩
  lt_iff_le_not_ge a b := by
    cases a with | mk ia xa =>
    cases b with | mk ib xb =>
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, by rintro (h2 | ⟨heq, _⟩); exact h1.asymm h2; exact h1.ne heq.symm⟩
      · dsimp at h1; subst h1
        refine ⟨Or.inr ⟨rfl, h2.le⟩, ?_⟩
        rintro (h3 | ⟨_, h3⟩)
        · exact lt_irrefl _ h3
        · exact not_le.2 h2 h3
    · rintro ⟨h1 | ⟨h1, h2⟩, hnot⟩
      · exact Or.inl h1
      · dsimp at h1; subst h1
        refine Or.inr ⟨rfl, lt_of_le_of_ne h2 fun heq => hnot ?_⟩
        exact Or.inr ⟨rfl, heq.ge⟩
  le_antisymm a b hab hba := by
    cases a with | mk i x =>
    cases b with | mk j y =>
    rcases hab with h1 | ⟨h1, h2⟩
    · rcases hba with h3 | ⟨h3, _⟩
      · exact (h1.asymm h3).elim
      · exact (h1.ne h3.symm).elim
    · dsimp at h1; subst h1
      rcases hba with h3 | ⟨_, h3⟩
      · exact (lt_irrefl _ h3).elim
      · congr; exact le_antisymm h2 h3
  le_total a b := by
    cases a with | mk i x =>
    cases b with | mk j y =>
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (Or.inl h)
    · subst h
      rcases le_total x y with hxy | hyx
      · exact Or.inl (Or.inr ⟨rfl, hxy⟩)
      · exact Or.inr (Or.inr ⟨rfl, hyx⟩)
    · exact Or.inr (Or.inl h)
  toDecidableLE := Classical.decRel _

instance lexSigmaWellFoundedLT {I : Type} {F : I → Type}
    [LinearOrder I] [WellFoundedLT I] [∀ i, LinearOrder (F i)] [∀ i, WellFoundedLT (F i)] :
    WellFoundedLT (LexSigma I F) := by
  refine ⟨⟨fun a => ?_⟩⟩
  cases a with | mk i x =>
  induction i using WellFoundedLT.induction with
  | ind i ih_i =>
    induction x using WellFoundedLT.induction with
    | ind x ih_x =>
      refine Acc.intro (⟨i, x⟩ : LexSigma I F) fun b hb => ?_
      cases b with | mk j y =>
      rcases hb with hlt | ⟨heq, hlt⟩
      · exact ih_i j hlt y
      · dsimp at heq; subst heq
        exact ih_x y hlt

/-- The well-ordered sum `Σ_{n : ℕ} ω₁ ^ (n + 1)` has order type `ω₁ ^ ω`. -/
lemma typeLT_omega1_opow_omega0 :
    typeLT (LexSigma ℕ (fun n => (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType)) = ω₁ ^ ω := by
  refine le_antisymm ?_ ?_
  · refine typeLT_le_of_forall_typein_lt fun p => ?_
    -- Initial segment of p = ⟨n, x⟩ embeds into Fin (n + 1) ×ₗ (ω₁ ^ (n + 1)).ToType
    let n := p.fst
    have hsub : Set.Iio p ⊆ {q | q.fst ≤ n} := fun q hq => by
      rcases hq with h1 | ⟨h1, _⟩
      · exact h1.le
      · exact h1.le
    have hle1 : Ordinal.typein LT.lt p ≤ typeLT {q : LexSigma ℕ (fun k => (ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0})).ToType) | q.fst ≤ n} := by
      rw [← Ordinal.type_Iio_lt]
      exact typeLT_mono_subset hsub
    -- Embed {q | q.fst ≤ n} into (Fin (n + 1)) ×ₗ (ω₁ ^ (n + 1)).ToType
    have hmono : ∀ k ≤ n, Nonempty ((ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0})).ToType ↪o
        (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType) := fun k hk => by
      have hle : ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0}) ≤ ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) :=
        Ordinal.opow_le_opow_right (Ordinal.omega_pos 1) (Nat.cast_le.2 (Nat.add_le_add_right hk 1))
      rw [← Ordinal.type_toType (ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0})),
        ← Ordinal.type_toType (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}))] at hle
      obtain ⟨f⟩ := Ordinal.type_le_iff.1 hle
      exact ⟨OrderEmbedding.ofStrictMono f fun _ _ h => f.map_rel_iff.2 h⟩
    let emb := fun (k : Fin (n + 1)) => Classical.choice (hmono k.1 (Nat.le_of_lt_succ k.2))
    let g : {q : LexSigma ℕ (fun k => (ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0})).ToType) | q.fst ≤ n} →
        Fin (n + 1) ×ₗ (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType := fun q =>
      let k : Fin (n + 1) := ⟨q.1.fst, Nat.lt_succ_of_le q.2⟩
      toLex (k, emb k q.1.snd)
    have hg : StrictMono g := by
      intro a b hab
      rcases hab with h1 | ⟨heq, h2⟩
      · exact Prod.Lex.left _ _ h1
      · cases a with | mk a' ha =>
        cases b with | mk b' hb =>
        cases a' with | mk ia xa =>
        cases b' with | mk ib xb =>
        dsimp at heq h2 ⊢
        subst heq
        exact Prod.Lex.right _ ((emb ⟨ia, Nat.lt_succ_of_le ha⟩).strictMono h2)
    have hle2 := hle1.trans (typeLT_le_of_strictMono hg)
    rw [typeLT_prodLex, Ordinal.type_toType, Ordinal.type_fin] at hle2
    have hlt3 : ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) * ((n + 1 : ℕ) : Ordinal.{0}) < ω₁ ^ ω := by
      have h1 : ((n + 1 : ℕ) : Ordinal.{0}) < ω₁ :=
        (Ordinal.natCast_lt_omega0 (n + 1)).trans Ordinal.omega0_lt_omega_one
      have h2 : ((n + 1 : ℕ) : Ordinal.{0}) < ω := Ordinal.natCast_lt_omega0 (n + 1)
      exact Ordinal.opow_mul_lt_opow h1 h2
    exact hle2.trans_lt hlt3
  · rw [Ordinal.opow_le_of_isSuccLimit (Ordinal.omega_pos 1).ne' Ordinal.isSuccLimit_omega0]
    intro c hc
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hc
    have hle : ω₁ ^ (n : Ordinal.{0}) ≤ ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) :=
      Ordinal.opow_le_opow_right (Ordinal.omega_pos 1) (Nat.cast_le.2 (Nat.le_succ n))
    refine hle.trans ?_
    rw [← Ordinal.type_toType (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}))]
    exact typeLT_le_of_strictMono
      (f := fun x : (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType =>
        (⟨n, x⟩ : LexSigma ℕ (fun k => (ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0})).ToType)))
      fun _ _ h => Or.inr ⟨rfl, h⟩

/-- Layer-reconstitution lemma for `Y = ω₁ ×ₗ Σ_{n : ℕ} ω₁ ^ (n + 1)` (order type `ω₁ ^ (ω + 1)`):
if `T ⊆ Y` meets each layer `L n` in order type `ω₁ ^ (n + 2)`, then `typeLT T = ω₁ ^ (ω + 1)`. -/
lemma typeLT_of_layers
    (T : Set ((ω₁).ToType ×ₗ LexSigma ℕ (fun n => (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType)))
    (hT : ∀ n : ℕ,
      typeLT {p : (ω₁).ToType ×ₗ LexSigma ℕ (fun k => (ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0})).ToType) |
        p ∈ T ∧ (ofLex p).2.fst = n} = ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0})) :
    typeLT T = ω₁ ^ (ω + 1) := by
  let Y := (ω₁).ToType ×ₗ LexSigma ℕ (fun k => (ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0})).ToType)
  have hY : typeLT Y = ω₁ ^ (ω + 1) := by
    rw [typeLT_prodLex, typeLT_omega1_opow_omega0, Ordinal.type_toType, Ordinal.opow_add_one]
  refine le_antisymm ((typeLT_set_le_self T).trans_eq hY) ?_
  -- For each n, the set E n of ξ where slice (ξ, n) has full type ω₁ ^ (n + 1) is unbounded in ω₁
  let Slice (ξ : (ω₁).ToType) (n : ℕ) : Set Y :=
    {p : Y | p ∈ T ∧ (ofLex p).1 = ξ ∧ (ofLex p).2.fst = n}
  let E (n : ℕ) : Set (ω₁).ToType :=
    {ξ : (ω₁).ToType | typeLT (Slice ξ n) = ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})}
  have hE_unbdd : ∀ n : ℕ, ∀ α0 : (ω₁).ToType, ∃ ξ : (ω₁).ToType, α0 < ξ ∧ ξ ∈ E n := by
    intro n α0
    by_contra hbdd
    push Not at hbdd
    let Ln : Set Y := {p : Y | p ∈ T ∧ (ofLex p).2.fst = n}
    let P1 : Set Y := {p : Y | p ∈ Ln ∧ (ofLex p).1 ≤ α0}
    let P2 : Set Y := {p : Y | p ∈ Ln ∧ α0 < (ofLex p).1}
    have hun : Ln = P1 ∪ P2 := by
      ext p; simp only [P1, P2, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · intro hp; rcases le_or_gt (ofLex p).1 α0 with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    -- Bound P1 < ω₁ ^ (n + 2)
    have hP1_lt : typeLT P1 < ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
      let emb1 : P1 → Set.Iic α0 ×ₗ (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType := fun p =>
        toLex (⟨(ofLex p.1).1, p.2.2⟩, p.2.1.2 ▸ (ofLex p.1).2.snd)
      have hemb1 : StrictMono emb1 := by
        intro a b hab
        cases a with | mk a' ha' =>
        cases b with | mk b' hb' =>
        cases a' with | mk ia sa =>
        cases b' with | mk ib sb =>
        cases sa with | mk na xa =>
        cases sb with | mk nb xb =>
        rcases Prod.lex_iff.1 hab with h1 | ⟨h1, h2⟩
        · exact Prod.Lex.left _ _ h1
        · dsimp at h1; subst h1
          have ha : na = n := ha'.1.2
          have hb : nb = n := hb'.1.2
          subst ha; subst hb
          rcases h2 with h2a | ⟨_, h2c⟩
          · exact (lt_irrefl _ h2a).elim
          · exact Prod.Lex.right _ h2c
      have hle := typeLT_le_of_strictMono hemb1
      rw [typeLT_prodLex, Ordinal.type_toType] at hle
      have hIic : typeLT (Set.Iic α0) < ω₁ := by
        have : Countable (Set.Iic α0) := Set.countable_coe_iff.1 (countable_Iic_omega1 α0)
        exact typeLT_lt_omega1_of_countable
      have hexp : ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0}) = ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) * ω₁ := by
        rw [show (n + 2 : ℕ) = (n + 1) + 1 by omega, Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
      rw [hexp]
      have hpos : 0 < ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) := Ordinal.opow_pos _ (Ordinal.omega_pos 1)
      exact hle.trans_lt ((mul_lt_mul_iff_right₀ hpos).2 hIic)
    -- Bound P2 ≤ ω₁ ^ (n + 1) < ω₁ ^ (n + 2)
    have hP2_lt : typeLT P2 < ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
      have hslice_lt : ∀ ξ : (ω₁ : Ordinal.{0}).ToType, α0 < ξ →
          ∃ q : Ordinal.{0}, q < ω₁ ∧
            typeLT (Slice ξ n) ≤ ω₁ ^ (n : Ordinal.{0}) * q := fun ξ hξ => by
        have hlt_sl : typeLT (Slice ξ n) < ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) := by
          have hle_sl : typeLT (Slice ξ n) ≤ ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) := by
            let f : Slice ξ n → (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType := fun p =>
              p.2.2.2 ▸ (ofLex p.1).2.snd
            have hf : StrictMono f := by
              intro a b hab
              cases a with | mk a' ha' =>
              cases b with | mk b' hb' =>
              cases a' with | mk ia sa =>
              cases b' with | mk ib sb =>
              cases sa with | mk na xa =>
              cases sb with | mk nb xb =>
              have hia : ia = ξ := ha'.2.1
              have hib : ib = ξ := hb'.2.1
              have hna : na = n := ha'.2.2
              have hnb : nb = n := hb'.2.2
              subst hia; subst hib; subst hna; subst hnb
              rcases Prod.lex_iff.1 hab with h1 | ⟨_, h2⟩
              · exact (lt_irrefl _ h1).elim
              · rcases h2 with h2a | ⟨_, h2c⟩
                · exact (lt_irrefl _ h2a).elim
                · exact h2c
            exact (typeLT_le_of_strictMono hf).trans_eq (Ordinal.type_toType _)
          exact lt_of_le_of_ne hle_sl (hbdd ξ hξ)
        let d := ω₁ ^ (n : Ordinal.{0})
        have hd_pos : 0 < d := Ordinal.opow_pos _ (Ordinal.omega_pos 1)
        have hmul : ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) = d * ω₁ := by
          rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
        let q0 := (typeLT (Slice ξ n)) / d
        have hq0_lt : q0 < ω₁ := by
          by_contra hge; push Not at hge
          have h1 : d * ω₁ ≤ d * q0 := by gcongr
          have h2 : d * q0 ≤ typeLT (Slice ξ n) := Ordinal.mul_div_le (typeLT (Slice ξ n)) d
          exact not_le.2 hlt_sl (hmul ▸ h1.trans h2)
        have hsucc_lt : Order.succ q0 < ω₁ :=
          (Cardinal.isSuccLimit_omega 1).succ_lt hq0_lt
        refine ⟨Order.succ q0, hsucc_lt, ?_⟩
        have hdiv := Ordinal.div_add_mod (typeLT (Slice ξ n)) d
        have hmod : (typeLT (Slice ξ n)) % d < d := Ordinal.mod_lt _ hd_pos.ne'
        calc typeLT (Slice ξ n)
            = d * q0 + (typeLT (Slice ξ n)) % d := hdiv.symm
          _ ≤ d * q0 + d := by gcongr
          _ = d * Order.succ q0 := by rw [Ordinal.mul_succ]
      let qf : (ω₁ : Ordinal.{0}).ToType → Ordinal.{0} := fun ξ =>
        if h : α0 < ξ then Classical.choose (hslice_lt ξ h) else 0
      have hqf_lt : ∀ ξ, qf ξ < ω₁ := fun ξ => by
        by_cases h : α0 < ξ
        · simp only [qf, dif_pos h]; exact (Classical.choose_spec (hslice_lt ξ h)).1
        · simp only [qf, dif_neg h]; exact Ordinal.omega_pos 1
      have hqf_emb : ∀ ξ, α0 < ξ →
          Nonempty (Slice ξ n ↪o ((qf ξ).ToType ×ₗ (ω₁ ^ (n : Ordinal.{0})).ToType)) := fun ξ h => by
        have hle : typeLT (Slice ξ n) ≤ typeLT ((qf ξ).ToType ×ₗ (ω₁ ^ (n : Ordinal.{0})).ToType) := by
          rw [typeLT_prodLex, Ordinal.type_toType, Ordinal.type_toType]
          simpa [qf, dif_pos h] using (Classical.choose_spec (hslice_lt ξ h)).2
        obtain ⟨f⟩ := Ordinal.type_le_iff.1 hle
        exact ⟨OrderEmbedding.ofStrictMono f fun _ _ hlt => f.map_rel_iff.2 hlt⟩
      let Z := LexSigma (ω₁ : Ordinal.{0}).ToType (fun ξ => (qf ξ).ToType)
      have hZ_le : typeLT Z ≤ ω₁ := by
        refine typeLT_le_of_forall_typein_lt fun z => ?_
        have hsub : Set.Iio z ⊆ {w : Z | w.fst ≤ z.fst} := fun w hw => by
          rcases hw with h1 | ⟨h1, _⟩ <;> exact h1.le
        have hcnt : ({w : Z | w.fst ≤ z.fst}).Countable := by
          have h1 : {w : Z | w.fst ≤ z.fst} =
              ⋃ ξ ∈ Set.Iic z.fst, Set.range (fun y : (qf ξ).ToType => (⟨ξ, y⟩ : Z)) := by
            ext w; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Iic, Set.mem_range]
            constructor
            · intro hw; exact ⟨w.fst, hw, w.snd, rfl⟩
            · rintro ⟨ξ, hle, y, heq⟩; cases heq; exact hle
          rw [h1]
          refine (countable_Iic_omega1 z.fst).biUnion fun ξ _ => ?_
          have := countable_toType_of_lt_omega1 (hqf_lt ξ)
          exact Set.countable_range _
        have : Countable (Set.Iio z) := Set.countable_coe_iff.1 (hcnt.mono hsub)
        rw [← Ordinal.type_Iio_lt]
        exact typeLT_lt_omega1_of_countable
      let emb2 : P2 → Z ×ₗ (ω₁ ^ (n : Ordinal.{0})).ToType := fun p =>
        let ξ := (ofLex p.1).1
        have hξ : α0 < ξ := p.2.2
        let f := Classical.choice (hqf_emb ξ hξ)
        let img := f ⟨p.1, p.2.1.1, rfl, p.2.1.2⟩
        toLex (⟨ξ, (ofLex img).1⟩, (ofLex img).2)
      have hemb2 : StrictMono emb2 := by
        intro a b hab
        cases a with | mk a' ha =>
        cases b with | mk b' hb =>
        cases a' with | mk ia sa =>
        cases b' with | mk ib sb =>
        rcases Prod.lex_iff.1 hab with h1 | ⟨h1, h2⟩
        · exact Prod.Lex.left _ _ (Or.inl h1)
        · dsimp at h1; subst h1
          let f := Classical.choice (hqf_emb ia ha.2)
          have hlt_img : f ⟨toLex (ia, sa), ha.1.1, rfl, ha.1.2⟩ <
              f ⟨toLex (ia, sb), hb.1.1, rfl, hb.1.2⟩ :=
            f.strictMono (Prod.Lex.right ia h2)
          rcases Prod.lex_iff.1 hlt_img with h3 | ⟨h3, h4⟩
          · exact Prod.Lex.left _ _ (Or.inr ⟨rfl, h3⟩)
          · refine Prod.lex_iff.2 (Or.inr ⟨?_, h4⟩)
            change (⟨ia, (ofLex (f ⟨toLex (ia, sa), ha.1.1, rfl, ha.1.2⟩)).1⟩ : Z) =
              ⟨ia, (ofLex (f ⟨toLex (ia, sb), hb.1.1, rfl, hb.1.2⟩)).1⟩
            congr 1
      have hle2 := typeLT_le_of_strictMono hemb2
      rw [typeLT_prodLex, Ordinal.type_toType] at hle2
      have hle3 : typeLT P2 ≤ ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
        exact hle2.trans (by gcongr)
      exact hle3.trans_lt ((Ordinal.opow_lt_opow_iff_right (Ordinal.one_lt_omega0.trans
        Ordinal.omega0_lt_omega_one)).2 (Nat.cast_lt.2 (by omega)))
    have hord : ∀ x ∈ P1, ∀ y ∈ P2, x < y := fun x hx y hy =>
      Prod.Lex.left _ _ (lt_of_le_of_lt hx.2 hy.2)
    have hsum : typeLT Ln = (typeLT P1) + (typeLT P2) := hun ▸ typeLT_union_le_add hord
    have hprinc : Ordinal.IsPrincipal (· + ·) (ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0})) := by
      refine Ordinal.isPrincipal_add_opow_of_isPrincipal_add ?_ _
      have h1 : Ordinal.IsPrincipal (· + ·) ω₁ := by
        rw [Ordinal.isPrincipal_add_iff_add_left_eq_self]
        intro a ha
        refine le_antisymm ?_ (by simp)
        by_contra hlt; push Not at hlt
        have hsum_type : typeLT (a.ToType ⊕ₗ (ω₁ : Ordinal.{0}).ToType) = a + ω₁ := by
          rw [typeLT_sumLex, Ordinal.type_toType, Ordinal.type_toType]
        have hle_w1 : typeLT (a.ToType ⊕ₗ (ω₁ : Ordinal.{0}).ToType) ≤ ω₁ := by
          refine typeLT_le_of_forall_typein_lt fun z => ?_
          rw [← Ordinal.type_Iio_lt]
          have hcnt_a : Countable a.ToType := countable_toType_of_lt_omega1 ha
          have hcnt_z : Countable (Set.Iio z) := by
            cases z with | _ z' =>
            cases z' with
            | inl xa =>
              have hsub : Set.Iio (toLex (Sum.inl xa) : a.ToType ⊕ₗ (ω₁ : Ordinal.{0}).ToType) ⊆
                  Set.range (fun x : a.ToType => toLex (Sum.inl x)) := by
                intro w hw
                cases w with | _ w' =>
                cases w' with
                | inl xw => exact ⟨xw, rfl⟩
                | inr xw => cases hw
              exact Set.countable_coe_iff.1 ((Set.countable_range _).mono hsub)
            | inr xw =>
              have hsub : Set.Iio (toLex (Sum.inr xw) : a.ToType ⊕ₗ (ω₁ : Ordinal.{0}).ToType) ⊆
                  Set.range (fun x : a.ToType => toLex (Sum.inl x)) ∪
                  (fun y : (ω₁ : Ordinal.{0}).ToType => toLex (Sum.inr y)) '' Set.Iio xw := by
                intro w hw
                cases w with | _ w' =>
                cases w' with
                | inl xa => exact Or.inl ⟨xa, rfl⟩
                | inr yb =>
                  cases hw with | inr h => exact Or.inr ⟨yb, h, rfl⟩
              exact Set.countable_coe_iff.1
                (((Set.countable_range _).union ((countable_Iio_omega1 xw).image _)).mono hsub)
          exact typeLT_lt_omega1_of_countable
        exact not_le.2 hlt (hsum_type ▸ hle_w1)
      exact h1
    have hlt_tot : (typeLT P1) + (typeLT P2) < ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0}) :=
      hprinc hP1_lt hP2_lt
    rw [← hsum, hT n] at hlt_tot
    exact lt_irrefl _ hlt_tot
  let Block := (ℕ → (ω₁ : Ordinal.{0}).ToType) × (ω₁ : Ordinal.{0}).ToType
  let seqFn (b : (ω₁ : Ordinal.{0}).ToType) : ℕ → (ω₁ : Ordinal.{0}).ToType :=
    Nat.rec (Classical.choose (hE_unbdd 0 b)) (fun n prev => Classical.choose (hE_unbdd (n + 1) prev))
  let buildStep (b : (ω₁ : Ordinal.{0}).ToType) : Block :=
    (seqFn b, Classical.choose (exists_gt_of_countable_omega1 (Set.countable_range (seqFn b))))
  have hbuild_gt : ∀ b n, b < (buildStep b).1 n := by
    intro b n
    induction n with
    | zero => exact (Classical.choose_spec (hE_unbdd 0 b)).1
    | succ n ih => exact ih.trans (Classical.choose_spec (hE_unbdd (n + 1) (seqFn b n))).1
  have hbuild_mono : ∀ b, StrictMono (buildStep b).1 := fun b =>
    strictMono_nat_of_lt_succ fun n => (Classical.choose_spec (hE_unbdd (n + 1) (seqFn b n))).1
  have hbuild_mem : ∀ b n, (buildStep b).1 n ∈ E n := fun b n => by
    cases n with
    | zero => exact (Classical.choose_spec (hE_unbdd 0 b)).2
    | succ n => exact (Classical.choose_spec (hE_unbdd (n + 1) (seqFn b n))).2
  have hbuild_ub : ∀ b n, (buildStep b).1 n < (buildStep b).2 := fun b n =>
    Classical.choose_spec (exists_gt_of_countable_omega1 (Set.countable_range (seqFn b))) _ ⟨n, rfl⟩
  let run : (ω₁ : Ordinal.{0}).ToType → Block := wellFounded_lt.fix fun ξ rec =>
    let prev : Set (ω₁ : Ordinal.{0}).ToType := Set.range (fun η : Set.Iio ξ => (rec η.1 η.2).2)
    have : Countable (Set.Iio ξ) := (countable_Iio_omega1 ξ).to_subtype
    have hprev_cnt : prev.Countable := Set.countable_range _
    let b := Classical.choose (exists_gt_of_countable_omega1 hprev_cnt)
    buildStep b
  have hrun_eq : ∀ ξ, ∃ b : (ω₁ : Ordinal.{0}).ToType,
      (∀ η < ξ, (run η).2 < b) ∧ run ξ = buildStep b := fun ξ => by
    let prev : Set (ω₁ : Ordinal.{0}).ToType := Set.range (fun η : Set.Iio ξ => (run η.1).2)
    have : Countable (Set.Iio ξ) := (countable_Iio_omega1 ξ).to_subtype
    have hprev_cnt : prev.Countable := Set.countable_range _
    let b := Classical.choose (exists_gt_of_countable_omega1 hprev_cnt)
    refine ⟨b, fun η hη => ?_, ?_⟩
    · exact Classical.choose_spec (exists_gt_of_countable_omega1 hprev_cnt) _ ⟨⟨η, hη⟩, rfl⟩
    · exact WellFounded.fix_eq wellFounded_lt _ ξ
  have hrun_mem : ∀ ξ n, (run ξ).1 n ∈ E n := fun ξ n => by
    obtain ⟨b, _, heq⟩ := hrun_eq ξ; rw [heq]; exact hbuild_mem b n
  have hrun_mono_n : ∀ ξ, StrictMono (run ξ).1 := fun ξ => by
    obtain ⟨b, _, heq⟩ := hrun_eq ξ; rw [heq]; exact hbuild_mono b
  have hrun_lt_ξ : ∀ {ξ₁ ξ₂ : (ω₁ : Ordinal.{0}).ToType}, ξ₁ < ξ₂ → ∀ n₁ n₂,
      (run ξ₁).1 n₁ < (run ξ₂).1 n₂ := fun {ξ₁ ξ₂} hlt n₁ n₂ => by
    obtain ⟨b₁, _, heq₁⟩ := hrun_eq ξ₁
    obtain ⟨b₂, hb₂, heq₂⟩ := hrun_eq ξ₂
    have h1 : (run ξ₁).1 n₁ < (run ξ₁).2 := by rw [heq₁]; exact hbuild_ub b₁ n₁
    have h2 : (run ξ₁).2 < b₂ := hb₂ ξ₁ hlt
    have h3 : b₂ < (run ξ₂).1 n₂ := by rw [heq₂]; exact hbuild_gt b₂ n₂
    exact h1.trans (h2.trans h3)
  have hiso : ∀ ξ n, Nonempty ((ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType ≃o Slice ((run ξ).1 n) n) :=
    fun ξ n => by
      obtain ⟨e⟩ := exists_orderIso_toType (hrun_mem ξ n)
      exact ⟨e.symm⟩
  let ψ := fun ξ n => Classical.choice (hiso ξ n)
  let emb : Y → T := fun p =>
    let ξ := (ofLex p).1
    let n := (ofLex p).2.fst
    let x := (ofLex p).2.snd
    ⟨(ψ ξ n x).1, (ψ ξ n x).2.1⟩
  have hemb : StrictMono emb := by
    intro a b hab
    cases a with | mk ξa sa =>
    cases b with | mk ξb sb =>
    cases sa with | mk na xa =>
    cases sb with | mk nb xb =>
    rcases Prod.lex_iff.1 hab with h1 | ⟨h1, h2⟩
    · change (ψ ξa na xa).1 < (ψ ξb nb xb).1
      have hfa : (ofLex (ψ ξa na xa).1).1 = (run ξa).1 na := (ψ ξa na xa).2.2.1
      have hfb : (ofLex (ψ ξb nb xb).1).1 = (run ξb).1 nb := (ψ ξb nb xb).2.2.1
      exact Prod.Lex.left _ _
        (show (ofLex (ψ ξa na xa).1).1 < (ofLex (ψ ξb nb xb).1).1 by rw [hfa, hfb]; exact hrun_lt_ξ h1 na nb)
    · dsimp at h1; subst h1
      rcases h2 with h2a | ⟨h2b, h2c⟩
      · change (ψ ξa na xa).1 < (ψ ξa nb xb).1
        have hfa : (ofLex (ψ ξa na xa).1).1 = (run ξa).1 na := (ψ ξa na xa).2.2.1
        have hfb : (ofLex (ψ ξa nb xb).1).1 = (run ξa).1 nb := (ψ ξa nb xb).2.2.1
        exact Prod.Lex.left _ _
          (show (ofLex (ψ ξa na xa).1).1 < (ofLex (ψ ξa nb xb).1).1 by rw [hfa, hfb]; exact hrun_mono_n ξa h2a)
      · dsimp at h2b; subst h2b
        exact (ψ ξa na).strictMono h2c
  exact hY ▸ typeLT_le_of_strictMono hemb

/-- Any `ω₁ * r` with `r < ω₁ ^ N` (`N : ℕ`) is the order type of a countable well-ordered
sigma sum of `ω₁ ^ (m i)` (`1 ≤ m i`). -/
lemma decomp_omega1_mul_lt_pow_nat :
    ∀ N : ℕ, ∀ r : Ordinal.{0}, r < ω₁ ^ (N : Ordinal.{0}) →
      ∃ (I : Type) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Countable I)
        (m : I → ℕ), (∀ i, 1 ≤ m i) ∧
        typeLT (LexSigma I (fun i => (ω₁ ^ (m i : Ordinal.{0})).ToType)) = ω₁ * r := by
  intro N
  induction N with
  | zero =>
    intro r hr
    simp only [Nat.cast_zero, Ordinal.opow_zero, Order.lt_one_iff] at hr
    subst hr
    refine ⟨PEmpty, inferInstance, inferInstance, inferInstance, fun i => PEmpty.elim i,
      fun i => PEmpty.elim i, ?_⟩
    rw [mul_zero]
    exact Ordinal.type_eq_zero_iff_isEmpty.2 ⟨fun p => PEmpty.elim p.fst⟩
  | succ N ih =>
    intro r hr
    let d := ω₁ ^ (N : Ordinal.{0})
    have hd_pos : 0 < d := Ordinal.opow_pos _ (Ordinal.omega_pos 1)
    let a := r / d
    let b := r % d
    have hr_eq : d * a + b = r := Ordinal.div_add_mod r d
    have hb_lt : b < d := Ordinal.mod_lt r hd_pos.ne'
    have ha_lt : a < ω₁ := by
      by_contra hge; push Not at hge
      have h1 : ω₁ ^ ((N + 1 : ℕ) : Ordinal.{0}) = d * ω₁ := by
        rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
      have h2 : d * ω₁ ≤ d * a := by gcongr
      exact not_le.2 hr (h1 ▸ h2.trans (Ordinal.mul_div_le r d))
    obtain ⟨I₂, hlo₂, hwf₂, hcnt₂, m₂, hm₂, htype₂⟩ := ih b hb_lt
    let _ := hlo₂; let _ := hwf₂; have _ := hcnt₂
    have : Countable a.ToType := countable_toType_of_lt_omega1 ha_lt
    let I := a.ToType ⊕ₗ I₂
    have hcntI : Countable I := (inferInstance : Countable (a.ToType ⊕ I₂))
    let m : I → ℕ := fun i => match ofLex i with | Sum.inl _ => N + 1 | Sum.inr j => m₂ j
    refine ⟨I, inferInstance, inferInstance, hcntI, m, ?_, ?_⟩
    · intro i
      cases h : ofLex i with
      | inl _ => simp [m, h]
      | inr j => simp [m, h, hm₂ j]
    · have hmul_eq : ω₁ * r = ω₁ ^ ((N + 1 : ℕ) : Ordinal.{0}) * a + ω₁ * b := by
        rw [← hr_eq, mul_add, ← mul_assoc]
        congr 2
        rw [show ((N + 1 : ℕ) : Ordinal.{0}) = 1 + (N : Ordinal.{0}) by
          rw [show N + 1 = 1 + N by omega, Nat.cast_add, Nat.cast_one],
          Ordinal.opow_one_add]
      rw [hmul_eq, ← htype₂]
      let L : Type := a.ToType ×ₗ (ω₁ ^ ((N + 1 : ℕ) : Ordinal.{0})).ToType
      let R : Type := LexSigma I₂ (fun j => (ω₁ ^ (m₂ j : Ordinal.{0})).ToType)
      have hLR : typeLT (L ⊕ₗ R) = ω₁ ^ ((N + 1 : ℕ) : Ordinal.{0}) * a + typeLT R := by
        rw [typeLT_sumLex, typeLT_prodLex, Ordinal.type_toType, Ordinal.type_toType]
      rw [← hLR]
      refine typeLT_eq_of_orderIso
        { toFun := fun p =>
            match h : ofLex p.fst with
            | Sum.inl x => toLex (Sum.inl (toLex (x, cast (by simp [m, h]) p.snd)))
            | Sum.inr j => toLex (Sum.inr ⟨j, cast (by simp [m, h]) p.snd⟩)
          invFun := fun q =>
            match ofLex q with
            | Sum.inl p => ⟨toLex (Sum.inl (ofLex p).1), (ofLex p).2⟩
            | Sum.inr p => ⟨toLex (Sum.inr p.fst), p.snd⟩
          left_inv := fun p => by
            cases p with | mk i x =>
            cases i with
            | inl a' => rfl
            | inr j' => rfl
          right_inv := fun q => by
            cases q with | _ q' =>
            cases q' with
            | inl p => cases p with | mk x y => rfl
            | inr p => cases p with | mk j y => rfl
          map_rel_iff' := fun {p₁ p₂} => by
            cases p₁ with | mk i₁ x₁ =>
            cases p₂ with | mk i₂ x₂ =>
            cases i₁ with
            | inl a₁ =>
              cases i₂ with
              | inl a₂ =>
                change Sum.Lex (· ≤ ·) (· ≤ ·) (Sum.inl (toLex (a₁, x₁))) (Sum.inl (toLex (a₂, x₂))) ↔ _
                constructor
                · intro h
                  cases h with | inl h1 =>
                  rcases Prod.Lex.le_iff.1 h1 with hlt | ⟨rfl, hle⟩
                  · exact Or.inl (Sum.Lex.inl hlt)
                  · exact Or.inr ⟨rfl, hle⟩
                · rintro (h1 | ⟨h1, h2⟩)
                  · cases h1 with | inl hlt => exact Sum.Lex.inl (Prod.Lex.le_iff.2 (Or.inl hlt))
                  · have ha : a₁ = a₂ := Sum.inl.inj h1
                    subst ha
                    exact Sum.Lex.inl (Prod.Lex.le_iff.2 (Or.inr ⟨rfl, h2⟩))
              | inr j₂ =>
                constructor
                · intro _; exact Or.inl (Sum.Lex.sep _ _)
                · intro _; exact Sum.Lex.sep _ _
            | inr j₁ =>
              cases i₂ with
              | inl a₂ =>
                constructor
                · intro h; cases h
                · rintro (h1 | ⟨h1, _⟩)
                  · cases h1
                  · cases h1
              | inr j₂ =>
                change Sum.Lex (· ≤ ·) (· ≤ ·) (Sum.inr (⟨j₁, x₁⟩ : R)) (Sum.inr (⟨j₂, x₂⟩ : R)) ↔ _
                constructor
                · intro h
                  cases h with | inr h1 =>
                  rcases h1 with hlt | ⟨heq, hle⟩
                  · exact Or.inl (Sum.Lex.inr hlt)
                  · dsimp at heq hle; subst heq; exact Or.inr ⟨rfl, hle⟩
                · rintro (h1 | ⟨h1, h2⟩)
                  · cases h1 with | inr hlt => exact Sum.Lex.inr (Or.inl hlt)
                  · have hj : j₁ = j₂ := Sum.inr.inj h1
                    subst hj
                    exact Sum.Lex.inr (Or.inr ⟨rfl, h2⟩) }

/-- **Part A (`H1`)**: For every `γ` with `ω₁ * γ < ω₁ ^ (ω + 2)`, any finite set mapping
on `(ω₁ * γ).ToType` has a free set of order type `ω₁ * γ`. -/
lemma freeSet_of_omega1_mul {γ : Ordinal.{0}} (hγ : ω₁ * γ < ω₁ ^ (ω + 2))
    (F : (ω₁ * γ).ToType → Finset (ω₁ * γ).ToType) (hirr : ∀ x, x ∉ F x) :
    ∃ S : Set (ω₁ * γ).ToType,
      (∀ x ∈ S, ∀ y ∈ S, y ∉ F x) ∧ typeLT S = ω₁ * γ := by
  classical
  have h1ω : (1 : Ordinal.{0}) + ω = ω := by
    rw [← Nat.cast_one]
    exact Ordinal.natCast_add_omega0 1
  have hmul_w1_ow : ω₁ * ω₁ ^ ω = ω₁ ^ ω := by
    rw [← Ordinal.opow_one_add, h1ω]
  have hmul_w1_ow1 : ω₁ * ω₁ ^ (ω + 1) = ω₁ ^ (ω + 1) := by
    rw [← Ordinal.opow_one_add, ← add_assoc, h1ω]
  have hmul_w1_ow2 : ω₁ * ω₁ ^ (ω + 2) = ω₁ ^ (ω + 2) := by
    rw [← Ordinal.opow_one_add, ← add_assoc, h1ω]
  have hγ_lt : γ < ω₁ ^ (ω + 2) := by
    by_contra hge; push Not at hge
    exact not_le.2 hγ (hmul_w1_ow2 ▸ (by gcongr : ω₁ * ω₁ ^ (ω + 2) ≤ ω₁ * γ))
  -- Divide γ by ω₁ ^ (ω + 1): γ = ω₁ ^ (ω + 1) * q + s
  let D1 := ω₁ ^ (ω + 1)
  have hD1_pos : 0 < D1 := Ordinal.opow_pos _ (Ordinal.omega_pos 1)
  let q := γ / D1
  let s := γ % D1
  have hγ_eq : D1 * q + s = γ := Ordinal.div_add_mod γ D1
  have hs_lt : s < D1 := Ordinal.mod_lt γ hD1_pos.ne'
  have hq_lt : q < ω₁ := by
    by_contra hge; push Not at hge
    have h1 : ω₁ ^ (ω + 2) = D1 * ω₁ := by
      rw [show (ω + 2 : Ordinal.{0}) = (ω + 1) + 1 by rw [add_assoc]; norm_num,
        Ordinal.opow_add_one]
    exact not_le.2 hγ_lt (h1 ▸ (by gcongr : D1 * ω₁ ≤ D1 * q).trans (Ordinal.mul_div_le γ D1))
  -- Divide s by ω₁ ^ ω: s = ω₁ ^ ω * q' + r
  let D0 := ω₁ ^ ω
  have hD0_pos : 0 < D0 := Ordinal.opow_pos _ (Ordinal.omega_pos 1)
  let q' := s / D0
  let r := s % D0
  have hs_eq : D0 * q' + r = s := Ordinal.div_add_mod s D0
  have hr_lt : r < D0 := Ordinal.mod_lt s hD0_pos.ne'
  have hq'_lt : q' < ω₁ := by
    by_contra hge; push Not at hge
    have h1 : D1 = D0 * ω₁ := Ordinal.opow_add_one ω₁ ω
    exact not_le.2 hs_lt (h1 ▸ (by gcongr : D0 * ω₁ ≤ D0 * q').trans (Ordinal.mul_div_le s D0))
  -- r < ω₁ ^ ω → ∃ N : ℕ, r < ω₁ ^ N
  have hr_nat : ∃ N : ℕ, r < ω₁ ^ (N : Ordinal.{0}) := by
    rw [Ordinal.lt_opow_of_isSuccLimit (Ordinal.omega_pos 1).ne' Ordinal.isSuccLimit_omega0] at hr_lt
    obtain ⟨c, hc, hrc⟩ := hr_lt
    obtain ⟨N, rfl⟩ := Ordinal.lt_omega0.1 hc
    exact ⟨N, hrc⟩
  obtain ⟨N, hrN⟩ := hr_nat
  obtain ⟨Ir, hlo_r, hwf_r, hcnt_r, mr, hmr, htype_r⟩ := decomp_omega1_mul_lt_pow_nat N r hrN
  let _ := hlo_r; let _ := hwf_r; have _ := hcnt_r
  -- Explicit well-order W of order type ω₁ * γ
  let Y := (ω₁).ToType ×ₗ LexSigma ℕ (fun n => (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType)
  have hY : typeLT Y = D1 := by
    rw [typeLT_prodLex, typeLT_omega1_opow_omega0, Ordinal.type_toType]
    exact (Ordinal.opow_add_one ω₁ ω).symm
  let Z0 := LexSigma ℕ (fun n => (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType)
  let W1 := q.ToType ×ₗ Y
  let W2 := q'.ToType ×ₗ Z0
  let W3 := LexSigma Ir (fun i => (ω₁ ^ (mr i : Ordinal.{0})).ToType)
  let W := W1 ⊕ₗ (W2 ⊕ₗ W3)
  have hW_type : typeLT W = ω₁ * γ := by
    rw [typeLT_sumLex, typeLT_sumLex, typeLT_prodLex (α := q.ToType),
      typeLT_prodLex (α := q'.ToType), hY, typeLT_omega1_opow_omega0, htype_r,
      Ordinal.type_toType, Ordinal.type_toType]
    calc D1 * q + (D0 * q' + ω₁ * r)
        = (ω₁ * D1) * q + ((ω₁ * D0) * q' + ω₁ * r) := by rw [hmul_w1_ow1, hmul_w1_ow]
      _ = ω₁ * (D1 * q) + (ω₁ * (D0 * q') + ω₁ * r) := by simp only [mul_assoc]
      _ = ω₁ * (D1 * q + (D0 * q' + r)) := by simp only [mul_add]
      _ = ω₁ * γ := by rw [hs_eq, hγ_eq]
  -- Transfer F to W along OrderIso W ≃o (ω₁ * γ).ToType
  obtain ⟨eW⟩ := exists_orderIso_toType hW_type
  let FW : W → Finset W := fun x => (F (eW x)).map eW.symm.toEquiv.toEmbedding
  have hFW_irr : ∀ x, x ∉ FW x := fun x hx => by
    simp only [FW, Finset.mem_map, Equiv.toEmbedding_apply] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = eW x := by simpa using congrArg eW hyx
    exact hirr (eW x) (this ▸ hy)
  -- Bound #W ≤ ℵ₁
  have : Countable q.ToType := countable_toType_of_lt_omega1 hq_lt
  have : Countable q'.ToType := countable_toType_of_lt_omega1 hq'_lt
  have hcard_pow : ∀ k : ℕ, #(ω₁ ^ (k : Ordinal.{0})).ToType ≤ ℵ₁ := fun k => by
    induction k with
    | zero =>
      simp only [Nat.cast_zero, Ordinal.opow_zero, Cardinal.mk_toType, Ordinal.card_one]
      exact (Cardinal.one_lt_aleph0.le).trans (Cardinal.aleph0_le_aleph 1)
    | succ k ih =>
      have h1 : typeLT ((ω₁).ToType ×ₗ (ω₁ ^ (k : Ordinal.{0})).ToType) =
          ω₁ ^ ((k + 1 : ℕ) : Ordinal.{0}) := by
        rw [typeLT_prodLex, Ordinal.type_toType, Ordinal.type_toType,
          Nat.cast_add, Nat.cast_one, Ordinal.opow_add_one]
      obtain ⟨e⟩ := exists_orderIso_toType h1
      rw [← Cardinal.mk_congr e.toEquiv, Cardinal.mk_congr (Equiv.refl _)]
      change #((ω₁).ToType × (ω₁ ^ (k : Ordinal.{0})).ToType) ≤ ℵ₁
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_toType, Ordinal.card_omega]
      have hmul : ℵ₁ * #(ω₁ ^ (k : Ordinal.{0})).ToType ≤ ℵ₁ * ℵ₁ := by gcongr
      exact hmul.trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))
  have hcard_Z0 : #Z0 ≤ ℵ₁ := by
    have h1 : #Z0 = #(Σ n : ℕ, (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType) :=
      Cardinal.mk_congr ⟨fun p => ⟨p.fst, p.snd⟩, fun p => ⟨p.1, p.2⟩,
        fun _ => rfl, fun _ => rfl⟩
    rw [h1, Cardinal.mk_sigma]
    calc Cardinal.sum (fun n : ℕ => #(ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType)
        ≤ Cardinal.sum (fun _ : ℕ => ℵ₁) := Cardinal.sum_le_sum _ _ fun n => hcard_pow (n + 1)
      _ = #ℕ * ℵ₁ := by rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]
      _ ≤ ℵ₁ * ℵ₁ := by
        have h0 : #ℕ ≤ ℵ₁ := by rw [Cardinal.mk_nat]; exact Cardinal.aleph0_le_aleph 1
        gcongr
      _ = ℵ₁ := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)
  have hcard_Y : #Y ≤ ℵ₁ := by
    change #((ω₁).ToType × Z0) ≤ ℵ₁
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_toType, Ordinal.card_omega]
    have hmul : ℵ₁ * #Z0 ≤ ℵ₁ * ℵ₁ := by gcongr
    exact hmul.trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))
  have hcard_W1 : #W1 ≤ ℵ₁ := by
    change #(q.ToType × Y) ≤ ℵ₁
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    have hq_c : #q.ToType ≤ ℵ₁ :=
      (Cardinal.mk_le_aleph0_iff.2 inferInstance).trans (Cardinal.aleph0_le_aleph 1)
    have hmul : #q.ToType * #Y ≤ ℵ₁ * ℵ₁ := by gcongr
    exact hmul.trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))
  have hcard_W2 : #W2 ≤ ℵ₁ := by
    change #(q'.ToType × Z0) ≤ ℵ₁
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    have hq'_c : #q'.ToType ≤ ℵ₁ :=
      (Cardinal.mk_le_aleph0_iff.2 inferInstance).trans (Cardinal.aleph0_le_aleph 1)
    have hmul : #q'.ToType * #Z0 ≤ ℵ₁ * ℵ₁ := by gcongr
    exact hmul.trans_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1))
  have hcard_W3 : #W3 ≤ ℵ₁ := by
    have h1 : #W3 = #(Σ i : Ir, (ω₁ ^ (mr i : Ordinal.{0})).ToType) :=
      Cardinal.mk_congr ⟨fun p => ⟨p.fst, p.snd⟩, fun p => ⟨p.1, p.2⟩,
        fun _ => rfl, fun _ => rfl⟩
    rw [h1, Cardinal.mk_sigma]
    calc Cardinal.sum (fun i : Ir => #(ω₁ ^ (mr i : Ordinal.{0})).ToType)
        ≤ Cardinal.sum (fun _ : Ir => ℵ₁) := Cardinal.sum_le_sum _ _ fun i => hcard_pow (mr i)
      _ = #Ir * ℵ₁ := by rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]
      _ ≤ ℵ₁ * ℵ₁ := by
        have h0 : #Ir ≤ ℵ₁ :=
          (Cardinal.mk_le_aleph0_iff.2 inferInstance).trans (Cardinal.aleph0_le_aleph 1)
        gcongr
      _ = ℵ₁ := Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)
  have hcard_W : #W ≤ ℵ₁ := by
    change #(W1 ⊕ (W2 ⊕ W3)) ≤ ℵ₁
    rw [Cardinal.mk_sum, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.lift_id, Cardinal.lift_id]
    have h23 : #W2 + #W3 ≤ ℵ₁ :=
      (add_le_add hcard_W2 hcard_W3).trans_eq (Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1))
    exact (add_le_add hcard_W1 h23).trans_eq (Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1))
  -- Index all blocks/layers by countable type Idx = (q × ℕ) ⊕ ((q' × ℕ) ⊕ Ir)
  let Idx := (q.ToType × ℕ) ⊕ ((q'.ToType × ℕ) ⊕ Ir)
  have : Countable Idx := inferInstance
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat Idx
  let blk : Idx → Set W := fun idx =>
    match idx with
    | Sum.inl (η, n) =>
        {w : W | ∃ (y : Y), w = toLex (Sum.inl (toLex (η, y))) ∧ (ofLex y).2.fst = n}
    | Sum.inr (Sum.inl (η', n)) =>
        {w : W | ∃ (z : Z0), w = toLex (Sum.inr (toLex (Sum.inl (toLex (η', z))))) ∧ z.fst = n}
    | Sum.inr (Sum.inr i) =>
        {w : W | ∃ (x : (ω₁ ^ (mr i : Ordinal.{0})).ToType),
          w = toLex (Sum.inr (toLex (Sum.inr ⟨i, x⟩)))}
  let mIdx : Idx → ℕ := fun idx =>
    match idx with
    | Sum.inl (_, n) => n + 2
    | Sum.inr (Sum.inl (_, n)) => n + 1
    | Sum.inr (Sum.inr i) => mr i
  have hblk_disj : Pairwise (Function.onFun Disjoint blk) := by
    intro a b hab
    change Disjoint (blk a) (blk b)
    rw [Set.disjoint_left]
    intro w ha hb
    rcases a with ⟨η₁, n₁⟩ | (⟨η₁', n₁⟩ | i₁) <;> rcases b with ⟨η₂, n₂⟩ | (⟨η₂', n₂⟩ | i₂)
    · rcases ha with ⟨y₁, rfl, hn₁⟩; rcases hb with ⟨y₂, h2, hn₂⟩
      have h3 : (η₁, y₁) = (η₂, y₂) := by simpa using h2
      cases h3; exact hab (by rw [← hn₁, ← hn₂])
    · rcases ha with ⟨_, rfl, _⟩; rcases hb with ⟨_, h2, _⟩; cases h2
    · rcases ha with ⟨_, rfl, _⟩; rcases hb with ⟨_, h2⟩; cases h2
    · rcases ha with ⟨_, rfl, _⟩; rcases hb with ⟨_, h2, _⟩; cases h2
    · rcases ha with ⟨z₁, rfl, hn₁⟩; rcases hb with ⟨z₂, h2, hn₂⟩
      have h3 : (η₁', z₁) = (η₂', z₂) := by simpa using h2
      cases h3; exact hab (by rw [← hn₁, ← hn₂])
    · rcases ha with ⟨_, rfl, _⟩; rcases hb with ⟨_, h2⟩; cases h2
    · rcases ha with ⟨_, rfl⟩; rcases hb with ⟨_, h2, _⟩; cases h2
    · rcases ha with ⟨_, rfl⟩; rcases hb with ⟨_, h2, _⟩; cases h2
    · rcases ha with ⟨x₁, rfl⟩; rcases hb with ⟨x₂, h2⟩
      have h3 : (⟨i₁, x₁⟩ : W3) = ⟨i₂, x₂⟩ := Sum.inr.inj (Sum.inr.inj h2)
      exact hab (congrArg (fun p => Sum.inr (Sum.inr p.fst)) h3)
  have hblk_type : ∀ idx : Idx, 1 ≤ mIdx idx ∧ typeLT (blk idx) = ω₁ ^ (mIdx idx : Ordinal.{0}) := by
    intro idx
    rcases idx with ⟨η, n⟩ | (⟨η', n⟩ | i)
    · refine ⟨by dsimp [mIdx]; omega, ?_⟩
      have hsm : StrictMono (fun p : (ω₁).ToType ×ₗ (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType =>
          (toLex (Sum.inl (toLex (η, toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩)))) : W)) := by
        intro a b hab
        cases a with | _ a' => cases b with | _ b' =>
        cases a' with | mk a1 a2 => cases b' with | mk b1 b2 =>
        rcases Prod.lex_iff.1 hab with h1 | ⟨h1, h2⟩
        · exact Sum.Lex.inl (Prod.Lex.right η (Prod.Lex.left _ _ h1))
        · dsimp at h1 h2 ⊢; subst h1
          exact Sum.Lex.inl (Prod.Lex.right η (Prod.Lex.right _ (Or.inr ⟨rfl, h2⟩)))
      have hrg : Set.range (fun p : (ω₁).ToType ×ₗ (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType =>
          (toLex (Sum.inl (toLex (η, toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩)))) : W)) =
          blk (Sum.inl (η, n)) := by
        ext w; simp only [Set.mem_range, blk]
        constructor
        · rintro ⟨p, rfl⟩; exact ⟨toLex ((ofLex p).1, ⟨n, (ofLex p).2⟩), rfl, rfl⟩
        · rintro ⟨y, rfl, hn⟩
          refine ⟨toLex ((ofLex y).1, cast (by rw [hn]) (ofLex y).2.snd), ?_⟩
          have hz : (⟨n, cast (by rw [hn]) (ofLex y).2.snd⟩ : Z0) = (ofLex y).2 := by
            generalize (ofLex y).2 = z0 at hn ⊢
            cases z0 with | mk k x =>
            dsimp at hn; subst hn; rfl
          change toLex (Sum.inl (toLex (η, toLex ((ofLex y).1, ⟨n, cast (by rw [hn]) (ofLex y).2.snd⟩)))) =
            toLex (Sum.inl (toLex (η, y)))
          rw [hz]; rfl
      have h1 := typeLT_image_strictMono hsm Set.univ
      rw [Set.image_univ, hrg, typeLT_univ, typeLT_prodLex, Ordinal.type_toType,
        Ordinal.type_toType] at h1
      dsimp only [mIdx]
      rw [h1, show ((n + 2 : ℕ) : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0}) + 1 by
        rw [show n + 2 = (n + 1) + 1 by omega, Nat.cast_add, Nat.cast_one],
        Ordinal.opow_add_one]
    · refine ⟨by dsimp [mIdx]; omega, ?_⟩
      have hsm : StrictMono (fun x : (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType =>
          (toLex (Sum.inr (toLex (Sum.inl (toLex (η', ⟨n, x⟩))))) : W)) := fun a b hab =>
        Sum.Lex.inr (Sum.Lex.inl (Prod.Lex.right η' (Or.inr ⟨rfl, hab⟩)))
      have hrg : Set.range (fun x : (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType =>
          (toLex (Sum.inr (toLex (Sum.inl (toLex (η', ⟨n, x⟩))))) : W)) =
          blk (Sum.inr (Sum.inl (η', n))) := by
        ext w; simp only [Set.mem_range, blk]
        constructor
        · rintro ⟨x, rfl⟩; exact ⟨⟨n, x⟩, rfl, rfl⟩
        · rintro ⟨z, rfl, hn⟩
          cases z with | mk k x => dsimp at hn; subst hn; exact ⟨x, rfl⟩
      have h1 := typeLT_image_strictMono hsm Set.univ
      rw [Set.image_univ, hrg, typeLT_univ, Ordinal.type_toType] at h1
      exact h1
    · refine ⟨hmr i, ?_⟩
      have hsm : StrictMono (fun x : (ω₁ ^ (mr i : Ordinal.{0})).ToType =>
          (toLex (Sum.inr (toLex (Sum.inr ⟨i, x⟩))) : W)) := fun a b hab =>
        Sum.Lex.inr (Sum.Lex.inr (Or.inr ⟨rfl, hab⟩))
      have hrg : Set.range (fun x : (ω₁ ^ (mr i : Ordinal.{0})).ToType =>
          (toLex (Sum.inr (toLex (Sum.inr ⟨i, x⟩))) : W)) = blk (Sum.inr (Sum.inr i)) := by
        ext w; simp only [Set.mem_range, blk]
        exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩
      have h1 := typeLT_image_strictMono hsm Set.univ
      rw [Set.image_univ, hrg, typeLT_univ, Ordinal.type_toType] at h1
      exact h1
  -- Lift blk to ℕ
  let Bnat : ℕ → Set W := fun k =>
    if h : ∃ idx : Idx, enc idx = k then blk (Classical.choose h) else ∅
  let mnat : ℕ → ℕ := fun k =>
    if h : ∃ idx : Idx, enc idx = k then mIdx (Classical.choose h) else 0
  have hBnat_eq : ∀ idx : Idx, Bnat (enc idx) = blk idx := fun idx => by
    have hex : ∃ idx', enc idx' = enc idx := ⟨idx, rfl⟩
    simp only [Bnat, dif_pos hex]
    rw [henc (Classical.choose_spec hex)]
  have hmnat_eq : ∀ idx : Idx, mnat (enc idx) = mIdx idx := fun idx => by
    have hex : ∃ idx', enc idx' = enc idx := ⟨idx, rfl⟩
    simp only [mnat, dif_pos hex]
    rw [henc (Classical.choose_spec hex)]
  have hBnat_disj : Pairwise (Function.onFun Disjoint Bnat) := fun k₁ k₂ hne => by
    change Disjoint (Bnat k₁) (Bnat k₂)
    by_cases h1 : ∃ idx, enc idx = k₁
    · by_cases h2 : ∃ idx, enc idx = k₂
      · dsimp only [Bnat]; rw [dif_pos h1, dif_pos h2]
        exact hblk_disj fun heq => hne ((Classical.choose_spec h1).symm.trans
          ((congrArg enc heq).trans (Classical.choose_spec h2)))
      · dsimp only [Bnat]; rw [dif_neg h2]; exact disjoint_bot_right
    · dsimp only [Bnat]; rw [dif_neg h1]; exact disjoint_bot_left
  have hBnat_prop : ∀ k, Bnat k = ∅ ∨ (1 ≤ mnat k ∧ typeLT (Bnat k) = ω₁ ^ (mnat k : Ordinal.{0})) := by
    intro k
    by_cases h : ∃ idx, enc idx = k
    · right
      have hB : Bnat k = blk (Classical.choose h) := dif_pos h
      have hm : mnat k = mIdx (Classical.choose h) := dif_pos h
      rw [hB, hm]
      exact hblk_type (Classical.choose h)
    · left; exact dif_neg h
  obtain ⟨Snat, hSnat_prop, hSnat_free⟩ :=
    countable_family_free hcard_W FW hFW_irr Bnat hBnat_disj mnat hBnat_prop
  let SW : Set W := ⋃ k : ℕ, Snat k
  -- Reconstitute order type of SW: embed W into SW!
  have hSW_type : typeLT SW = ω₁ * γ := by
    refine le_antisymm ((typeLT_set_le_self SW).trans_eq hW_type) ?_
    -- 1. For each η : q.ToType, SW ∩ {η-slice} has type D1 via typeLT_of_layers
    have hW1_iso : ∀ η : q.ToType, Nonempty (Y ≃o
        ({y : Y | toLex (Sum.inl (toLex (η, y))) ∈ SW} : Set Y)) := fun η => by
      let Tη : Set Y := {y : Y | toLex (Sum.inl (toLex (η, y))) ∈ SW}
      have hTη : typeLT Tη = D1 := by
        refine typeLT_of_layers Tη fun n => ?_
        let k := enc (Sum.inl (η, n))
        have hSk_sub : Snat k ⊆ blk (Sum.inl (η, n)) :=
          (hSnat_prop k).1.trans (le_of_eq (hBnat_eq (Sum.inl (η, n))))
        have hSk_type : typeLT (Snat k) = ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
          rw [(hSnat_prop k).2, hBnat_eq]; exact (hblk_type (Sum.inl (η, n))).2
        let f : Y → W := fun y => toLex (Sum.inl (toLex (η, y)))
        have hf : StrictMono f := fun _ _ h => Sum.Lex.inl (Prod.Lex.right η h)
        have hsub : Snat k ⊆ f '' {y : Y | y ∈ Tη ∧ (ofLex y).2.fst = n} := by
          intro w hw
          obtain ⟨y, rfl, hn⟩ := hSk_sub hw
          exact ⟨y, ⟨Set.mem_iUnion.2 ⟨k, hw⟩, hn⟩, rfl⟩
        have hle1 := typeLT_mono_subset hsub
        rw [hSk_type, typeLT_image_strictMono hf] at hle1
        have hle2 : typeLT {y : Y | y ∈ Tη ∧ (ofLex y).2.fst = n} ≤
            ω₁ ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
          rw [← (hblk_type (Sum.inl (η, n))).2, ← typeLT_image_strictMono hf]
          refine typeLT_mono_subset ?_
          rintro _ ⟨y, ⟨_, hn⟩, rfl⟩
          exact ⟨y, rfl, hn⟩
        exact le_antisymm hle2 hle1
      obtain ⟨e1⟩ := exists_orderIso_toType hY
      obtain ⟨e2⟩ := exists_orderIso_toType hTη
      exact ⟨e1.trans e2.symm⟩
    -- 2. For each η' : q'.ToType and n : ℕ, SW contains a full copy of ω₁ ^ (n + 1)
    have hW2_iso : ∀ η' : q'.ToType, ∀ n : ℕ, Nonempty ((ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType ≃o
        ({x : (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType |
          toLex (Sum.inr (toLex (Sum.inl (toLex (η', ⟨n, x⟩))))) ∈ SW} : Set _)) := fun η' n => by
      let k := enc (Sum.inr (Sum.inl (η', n)))
      let f : (ω₁ ^ ((n + 1 : ℕ) : Ordinal.{0})).ToType → W := fun x =>
        toLex (Sum.inr (toLex (Sum.inl (toLex (η', ⟨n, x⟩)))))
      have hf : StrictMono f := fun _ _ h =>
        Sum.Lex.inr (Sum.Lex.inl (Prod.Lex.right η' (Or.inr ⟨rfl, h⟩)))
      have hsub : Snat k ⊆ f '' {x | f x ∈ SW} := by
        intro w hw
        have hmem := hBnat_eq (Sum.inr (Sum.inl (η', n))) ▸ (hSnat_prop k).1 hw
        obtain ⟨z, rfl, hn⟩ := hmem
        cases z with | mk k' x =>
        dsimp at hn; subst hn
        exact ⟨x, Set.mem_iUnion.2 ⟨k, hw⟩, rfl⟩
      have hge := typeLT_mono_subset hsub
      rw [(hSnat_prop k).2, hBnat_eq, (hblk_type (Sum.inr (Sum.inl (η', n)))).2,
        typeLT_image_strictMono hf] at hge
      have heq := le_antisymm ((typeLT_set_le_self _).trans_eq (Ordinal.type_toType _)) hge
      obtain ⟨e⟩ := exists_orderIso_toType heq
      exact ⟨e.symm⟩
    -- 3. For each i : Ir, SW contains a full copy of ω₁ ^ (mr i)
    have hW3_iso : ∀ i : Ir, Nonempty ((ω₁ ^ (mr i : Ordinal.{0})).ToType ≃o
        ({x : (ω₁ ^ (mr i : Ordinal.{0})).ToType |
          toLex (Sum.inr (toLex (Sum.inr ⟨i, x⟩))) ∈ SW} : Set _)) := fun i => by
      let k := enc (Sum.inr (Sum.inr i))
      let f : (ω₁ ^ (mr i : Ordinal.{0})).ToType → W := fun x =>
        toLex (Sum.inr (toLex (Sum.inr ⟨i, x⟩)))
      have hf : StrictMono f := fun _ _ h => Sum.Lex.inr (Sum.Lex.inr (Or.inr ⟨rfl, h⟩))
      have hsub : Snat k ⊆ f '' {x | f x ∈ SW} := by
        intro w hw
        have hmem := hBnat_eq (Sum.inr (Sum.inr i)) ▸ (hSnat_prop k).1 hw
        obtain ⟨x, rfl⟩ := hmem
        exact ⟨x, Set.mem_iUnion.2 ⟨k, hw⟩, rfl⟩
      have hge := typeLT_mono_subset hsub
      rw [(hSnat_prop k).2, hBnat_eq, (hblk_type (Sum.inr (Sum.inr i))).2,
        typeLT_image_strictMono hf] at hge
      have heq := le_antisymm ((typeLT_set_le_self _).trans_eq (Ordinal.type_toType _)) hge
      obtain ⟨e⟩ := exists_orderIso_toType heq
      exact ⟨e.symm⟩
    let ψ1 := fun η => Classical.choice (hW1_iso η)
    let ψ2 := fun η' n => Classical.choice (hW2_iso η' n)
    let ψ3 := fun i => Classical.choice (hW3_iso i)
    let emb : W → SW := fun w =>
      match ofLex w with
      | Sum.inl p =>
          let y := ψ1 (ofLex p).1 (ofLex p).2
          ⟨toLex (Sum.inl (toLex ((ofLex p).1, y.1))), y.2⟩
      | Sum.inr q =>
          match ofLex q with
          | Sum.inl p =>
              let x := ψ2 (ofLex p).1 (ofLex p).2.fst (ofLex p).2.snd
              ⟨toLex (Sum.inr (toLex (Sum.inl (toLex ((ofLex p).1, ⟨(ofLex p).2.fst, x.1⟩))))), x.2⟩
          | Sum.inr p =>
              let x := ψ3 p.fst p.snd
              ⟨toLex (Sum.inr (toLex (Sum.inr ⟨p.fst, x.1⟩))), x.2⟩
    have hemb : StrictMono emb := by
      intro a b hab
      have ha : a = toLex (ofLex a) := rfl
      have hb : b = toLex (ofLex b) := rfl
      rw [ha, hb] at hab ⊢
      generalize ofLex a = a' at hab ⊢
      generalize ofLex b = b' at hab ⊢
      cases a' with
      | inl pa =>
        cases b' with
        | inl pb =>
          cases hab with | inl h2 =>
          change Sum.Lex (· < ·) (· < ·)
            (Sum.inl (toLex ((ofLex pa).1, (ψ1 (ofLex pa).1 (ofLex pa).2).1)))
            (Sum.inl (toLex ((ofLex pb).1, (ψ1 (ofLex pb).1 (ofLex pb).2).1)))
          rcases Prod.lex_iff.1 h2 with h3 | ⟨h3, h4⟩
          · exact Sum.Lex.inl (Prod.Lex.left _ _ h3)
          · have h3' : (ofLex pa).1 = (ofLex pb).1 := h3
            rw [← h3']
            exact Sum.Lex.inl (Prod.Lex.right _ ((ψ1 _).strictMono h4))
        | inr qb =>
          have hqb : qb = toLex (ofLex qb) := rfl
          rw [hqb]
          generalize ofLex qb = qb'
          cases qb' with
          | inl _ => exact Sum.Lex.sep _ _
          | inr _ => exact Sum.Lex.sep _ _
      | inr qa =>
        cases b' with
        | inl pb => cases hab
        | inr qb =>
          cases hab with | inr h1 =>
          have hqa : qa = toLex (ofLex qa) := rfl
          have hqb : qb = toLex (ofLex qb) := rfl
          rw [hqa, hqb] at h1 ⊢
          generalize ofLex qa = qa' at h1 ⊢
          generalize ofLex qb = qb' at h1 ⊢
          cases qa' with
          | inl pa =>
            cases qb' with
            | inl pb =>
              cases h1 with | inl h2 =>
              change Sum.Lex (· < ·) (· < ·)
                (Sum.inr (toLex (Sum.inl (toLex ((ofLex pa).1,
                  (⟨(ofLex pa).2.fst, (ψ2 (ofLex pa).1 (ofLex pa).2.fst (ofLex pa).2.snd).1⟩ : Z0))))))
                (Sum.inr (toLex (Sum.inl (toLex ((ofLex pb).1,
                  (⟨(ofLex pb).2.fst, (ψ2 (ofLex pb).1 (ofLex pb).2.fst (ofLex pb).2.snd).1⟩ : Z0))))))
              rcases Prod.lex_iff.1 h2 with h3 | ⟨h3, h4⟩
              · exact Sum.Lex.inr (Sum.Lex.inl (Prod.Lex.left _ _ h3))
              · have h3' : (ofLex pa).1 = (ofLex pb).1 := h3
                rw [← h3']
                have h4' : (ofLex pa).2 < (ofLex pb).2 := h4
                rcases h4' with h5 | ⟨h5, h6⟩
                · exact Sum.Lex.inr (Sum.Lex.inl (Prod.Lex.right _ (Or.inl h5)))
                · generalize (ofLex pa).2 = za at h5 h6 ⊢
                  generalize (ofLex pb).2 = zb at h5 h6 ⊢
                  cases za with | mk na xa =>
                  cases zb with | mk nb xb =>
                  dsimp at h5 h6 ⊢; subst h5
                  exact Sum.Lex.inr (Sum.Lex.inl (Prod.Lex.right _
                    (Or.inr ⟨rfl, (ψ2 _ na).strictMono h6⟩)))
            | inr _ => exact Sum.Lex.inr (Sum.Lex.sep _ _)
          | inr pa =>
            cases qb' with
            | inl _ => cases h1
            | inr pb =>
              cases h1 with | inr h2 =>
              change Sum.Lex (· < ·) (· < ·)
                (Sum.inr (toLex (Sum.inr (⟨pa.fst, (ψ3 pa.fst pa.snd).1⟩ : W3))))
                (Sum.inr (toLex (Sum.inr (⟨pb.fst, (ψ3 pb.fst pb.snd).1⟩ : W3))))
              rcases h2 with h3 | ⟨h3, h4⟩
              · exact Sum.Lex.inr (Sum.Lex.inr (Or.inl h3))
              · cases pa with | mk ia xa => cases pb with | mk ib xb =>
                dsimp at h3 h4 ⊢; subst h3
                exact Sum.Lex.inr (Sum.Lex.inr (Or.inr ⟨rfl, (ψ3 ia).strictMono h4⟩))
    exact hW_type ▸ typeLT_le_of_strictMono hemb
  -- Pull SW back to (ω₁ * γ).ToType along eW
  refine ⟨eW '' SW, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hmem
    refine hSnat_free x hx y hy ?_
    simp only [FW, Finset.mem_map, Equiv.toEmbedding_apply]
    exact ⟨eW y, hmem, by simp⟩
  · rw [typeLT_image_strictMono eW.strictMono, hSW_type]

/-- Part A (`H1`) for graphs: every `ω₁ * γ < ω₁ ^ (ω + 2)` has `HasPathOrIndepSetOfType`. -/
lemma hasPathOrIndep_of_omega1_mul {γ : Ordinal.{0}} (hγ : ω₁ * γ < ω₁ ^ (ω + 2)) :
    HasPathOrIndepSetOfType (ω₁ * γ) := by
  intro G
  by_cases hpath : ∃ f : ℕ → (ω₁ * γ).ToType, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))
  · exact Or.inl hpath
  · right
    obtain ⟨F, hirr, hcov⟩ := finiteOrientation G hpath
    obtain ⟨S, hfree, htype⟩ := freeSet_of_omega1_mul hγ F hirr
    refine ⟨S, ?_, htype⟩
    intro x hx y hy _ hadj
    rcases hcov x y hadj with h1 | h2
    · exact hfree x hx y hy h1
    · exact hfree y hy x hx h2

end PartH1

/- ## Section 4: Kolmogorov 0-1 Splitting for Countable Indecomposable Ordinals -/

section KolmogorovSplit

noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

lemma fairCoin_isProb : IsProbabilityMeasure fairCoin := by
  refine ⟨?_⟩
  simp only [fairCoin, Measure.add_apply, Measure.smul_apply, _root_.smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, mul_one]
  exact ENNReal.add_halves 1

lemma fairCoin_map_not : fairCoin.map Bool.not = fairCoin := by
  have hm : Measurable Bool.not := measurable_of_countable _
  ext s _
  rw [Measure.map_apply hm MeasurableSpace.measurableSet_top]
  simp only [fairCoin, Measure.add_apply, Measure.smul_apply, _root_.smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSpace.measurableSet_top]
  exact add_comm _ _

/-- **2-Way Countable Splitting via Kolmogorov's 0-1 Law**:
If `U` has countable additively indecomposable order type `ω ^ δ` (`1 ≤ δ < ω₁`) and
`f : U → ℕ` has all fibers of order type `< ω ^ δ`, then there exists `P : Set ℕ` such that
both `f ⁻¹' P` and `f ⁻¹' Pᶜ` have full order type `ω ^ δ`. -/
lemma countable_split_two {U : Type} [LinearOrder U] [WellFoundedLT U]
    {δ : Ordinal.{0}} (_ : 1 ≤ δ) (hδc : δ < ω₁)
    (hU : typeLT U = ω ^ δ) (f : U → ℕ)
    (hf : ∀ c : ℕ, typeLT (f ⁻¹' {c}) < ω ^ δ) :
    ∃ P : Set ℕ, typeLT (f ⁻¹' P) = ω ^ δ ∧ typeLT (f ⁻¹' Pᶜ) = ω ^ δ := by
  have : IsProbabilityMeasure fairCoin := fairCoin_isProb
  let μ : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => fairCoin)
  have : IsProbabilityMeasure μ := inferInstance
  have hU_cnt : Countable U :=
    countable_of_typeLT_lt_omega1 (hU ▸ omega0_opow_lt_omega1 hδc)
  let s : ℕ → MeasurableSpace (ℕ → Bool) :=
    fun n => MeasurableSpace.comap (fun g : ℕ → Bool => g n) (inferInstance : MeasurableSpace Bool)
  have hs_le : ∀ n : ℕ, s n ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) := fun n => by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    exact (measurable_pi_apply n) hB
  have hindep : iIndep s μ := by
    have h1 : iIndepFun (fun (n : ℕ) (g : ℕ → Bool) => g n) μ :=
      iIndepFun_infinitePi (P := fun _ : ℕ => fairCoin) (X := fun _ b => b) (fun _ => measurable_id)
    exact (iIndepFun_iff_iIndep _ _ _).1 h1
  let T (W : Set U) (η : Ordinal.{0}) : Set (ℕ → Bool) :=
    {g : ℕ → Bool | η ≤ typeLT {u : U | u ∈ W ∧ g (f u) = true}}
  have hT_meas : ∀ (N : ℕ) (η : Ordinal.{0}), η < ω₁ →
      ∀ W : Set U, (∀ u ∈ W, N ≤ f u) →
        MeasurableSet[⨆ k ≥ N, s k] (T W η) := by
    intro N η
    induction η using WellFoundedLT.induction with
    | ind η ih =>
      intro hη W hWN
      let mN : MeasurableSpace (ℕ → Bool) := ⨆ k ≥ N, s k
      rcases Ordinal.zero_or_succ_or_isSuccLimit η with rfl | ⟨η', rfl⟩ | hlim
      · have heq : T W 0 = Set.univ := by ext g; simp [T]
        rw [heq]
        exact MeasurableSet.univ
      · have heq : T W (Order.succ η') =
            ⋃ u : W, ({g : ℕ → Bool | g (f u.1) = true} ∩ T (W ∩ Set.Iio u.1) η') := by
          ext g
          simp only [T, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
          rw [le_typeLT_of_succ]
          constructor
          · rintro ⟨x, ⟨hxW, hgx⟩, hle⟩
            refine ⟨⟨x, hxW⟩, hgx, ?_⟩
            refine hle.trans (typeLT_mono_subset ?_)
            intro y ⟨⟨hyW, hgy⟩, hyx⟩
            exact ⟨⟨hyW, hyx⟩, hgy⟩
          · rintro ⟨⟨x, hxW⟩, hgx, hle⟩
            refine ⟨x, ⟨hxW, hgx⟩, ?_⟩
            refine hle.trans (typeLT_mono_subset ?_)
            intro y ⟨⟨hyW, hyx⟩, hgy⟩
            exact ⟨⟨hyW, hgy⟩, hyx⟩
        rw [heq]
        refine MeasurableSet.iUnion fun u => ?_
        refine MeasurableSet.inter ?_ ?_
        · have hle_s : s (f u.1) ≤ mN := le_iSup₂_of_le (f u.1) (hWN u.1 u.2) le_rfl
          apply hle_s
          exact ⟨{true}, MeasurableSpace.measurableSet_top, rfl⟩
        · exact ih η' (Order.lt_succ η') ((Order.lt_succ η').trans hη)
            (W ∩ Set.Iio u.1) (fun v hv => hWN v hv.1)
      · have : Countable η.ToType := countable_toType_of_lt_omega1 hη
        have heq : T W η = ⋂ a : η.ToType, T W (Ordinal.typein LT.lt a) := by
          ext g
          simp only [T, Set.mem_ofPred_eq, Set.mem_iInter]
          constructor
          · intro h a
            exact ((Ordinal.typein_lt_type LT.lt a).trans_eq (Ordinal.type_toType η)).le.trans h
          · intro hall
            by_contra hlt; push Not at hlt
            have hsucc : Order.succ (typeLT {u : U | u ∈ W ∧ g (f u) = true}) < η :=
              hlim.succ_lt hlt
            obtain ⟨a, ha⟩ := Ordinal.typein_surj LT.lt (by rwa [Ordinal.type_toType])
            have := hall a
            rw [ha] at this
            exact not_lt.2 this (Order.lt_succ _)
        rw [heq]
        refine MeasurableSet.iInter fun a => ?_
        have ha : Ordinal.typein LT.lt a < η :=
          (Ordinal.typein_lt_type LT.lt a).trans_eq (Ordinal.type_toType η)
        exact ih _ ha (ha.trans hη) W hWN
  let E : Set (ℕ → Bool) := T Set.univ (ω ^ δ)
  have hE_eq_tail : ∀ N : ℕ, E = T {u : U | N ≤ f u} (ω ^ δ) := fun N => by
    ext g
    change ω ^ δ ≤ typeLT {u : U | u ∈ Set.univ ∧ g (f u) = true} ↔
      ω ^ δ ≤ typeLT {u : U | N ≤ f u ∧ g (f u) = true}
    constructor
    · intro hle
      let A : Set U := {u : U | u ∈ Set.univ ∧ g (f u) = true}
      let B : Set U := {u : U | N ≤ f u ∧ g (f u) = true}
      let C : Set U := ⋃ c ∈ Finset.range N, f ⁻¹' {c}
      have hsub : A ⊆ B ∪ C := by
        intro u hu
        by_cases hN : N ≤ f u
        · exact Or.inl ⟨hN, hu.2⟩
        · exact Or.inr (Set.mem_biUnion (Finset.mem_range.2 (not_le.1 hN)) rfl)
      have hC_lt : typeLT C < ω ^ δ := omega0_opow_biUnion_finset_lt fun c _ => hf c
      by_contra hBlt; push Not at hBlt
      have hun_lt := omega0_opow_union_lt δ hBlt hC_lt
      exact not_lt.2 (hle.trans (typeLT_mono_subset hsub)) hun_lt
    · intro hle
      exact hle.trans (typeLT_mono_subset fun u hu => ⟨Set.mem_univ u, hu.2⟩)
  have hE_tail : MeasurableSet[Filter.limsup s atTop] E := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    rw [hE_eq_tail N]
    exact hT_meas N (ω ^ δ) (omega0_opow_lt_omega1 hδc) {u : U | N ≤ f u} (fun _ hu => hu)
  have hE_meas : MeasurableSet E :=
    (limsup_le_iSup.trans (iSup_le hs_le)) E hE_tail
  have h01 : μ E = 0 ∨ μ E = 1 :=
    ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop hs_le hindep hE_tail
  let flip : (ℕ → Bool) → (ℕ → Bool) := fun g n => !(g n)
  have hflip_meas : Measurable flip :=
    measurable_pi_lambda _ fun n => (measurable_of_countable Bool.not).comp (measurable_pi_apply n)
  have hflip_pres : μ.map flip = μ := by
    have h1 := Measure.infinitePi_map_pi (μ := fun _ : ℕ => fairCoin)
      (f := fun (_ : ℕ) => Bool.not) (fun _ => measurable_of_countable Bool.not)
    simpa only [μ, flip, fairCoin_map_not] using h1
  have hflip_E : μ (flip ⁻¹' E) = μ E := by
    rw [← Measure.map_apply hflip_meas hE_meas, hflip_pres]
  have hcover : E ∪ flip ⁻¹' E = Set.univ := by
    ext g
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
    by_contra hneither
    push Not at hneither
    have h1 : typeLT {u : U | u ∈ Set.univ ∧ g (f u) = true} < ω ^ δ := not_le.1 hneither.1
    have h2 : typeLT {u : U | u ∈ Set.univ ∧ flip g (f u) = true} < ω ^ δ := not_le.1 hneither.2
    have hun : {u : U | u ∈ Set.univ ∧ g (f u) = true} ∪
        {u : U | u ∈ Set.univ ∧ flip g (f u) = true} = Set.univ := by
      ext u; cases g (f u) <;> simp [flip]
    have hlt := omega0_opow_union_lt δ h1 h2
    rw [hun, typeLT_univ, hU] at hlt
    exact lt_irrefl _ hlt
  have hE_one : μ E = 1 := by
    rcases h01 with h0 | h1
    · exfalso
      have h1 : (1 : ℝ≥0∞) = μ Set.univ := (measure_univ (μ := μ)).symm
      rw [← hcover] at h1
      have h2 := measure_union_le (μ := μ) E (flip ⁻¹' E)
      rw [hflip_E, h0, add_zero] at h2
      have h3 : (1 : ℝ≥0∞) ≤ 0 := h1.le.trans h2
      simp at h3
    · exact h1
  have hinter_ne : (E ∩ flip ⁻¹' E).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have h1 : μ E + μ (flip ⁻¹' E) = μ (E ∪ flip ⁻¹' E) :=
      (measure_union (Set.disjoint_iff_inter_eq_empty.2 hempty) (hflip_meas hE_meas)).symm
    rw [hcover, measure_univ, hflip_E, hE_one] at h1
    have h2 : (2 : ℝ≥0∞) = 1 := by rw [one_add_one_eq_two] at h1; exact h1
    norm_num at h2
  obtain ⟨g, hg1, hg2⟩ := hinter_ne
  let P : Set ℕ := {c : ℕ | g c = true}
  refine ⟨P, le_antisymm ((typeLT_set_le_self _).trans_eq hU) ?_,
    le_antisymm ((typeLT_set_le_self _).trans_eq hU) ?_⟩
  · have heqP : f ⁻¹' P = {u : U | u ∈ Set.univ ∧ g (f u) = true} := by
      ext u; simp [P]
    rw [heqP]
    exact hg1
  · have heqPc : f ⁻¹' Pᶜ = {u : U | u ∈ Set.univ ∧ flip g (f u) = true} := by
      ext u; simp [P, flip]
    rw [heqPc]
    exact hg2

/-- Finite `k`-way pairwise disjoint splitting of `f : U → ℕ`. -/
lemma countable_split_fin :
    ∀ k : ℕ, ∀ {U : Type} [LinearOrder U] [WellFoundedLT U]
      {δ : Ordinal.{0}} (_ : 1 ≤ δ) (_ : δ < ω₁)
      (_ : typeLT U = ω ^ δ) (f : U → ℕ)
      (_ : ∀ c : ℕ, typeLT (f ⁻¹' {c}) < ω ^ δ),
      ∃ P : Fin k → Set ℕ,
        Pairwise (Function.onFun Disjoint P) ∧
        ∀ i : Fin k, typeLT (f ⁻¹' (P i)) = ω ^ δ := by
  intro k
  induction k with
  | zero =>
    intro U _ _ δ _ _ _ _ _
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro U _ _ δ hδ1 hδc hU f hf
    obtain ⟨Q, hQ1, hQ2⟩ := countable_split_two hδ1 hδc hU f hf
    -- Apply IH on f ⁻¹' Qᶜ
    let f' : (f ⁻¹' Qᶜ : Set U) → ℕ := fun u => f u.1
    have hf' : ∀ c : ℕ, typeLT (f' ⁻¹' {c}) < ω ^ δ := fun c => by
      have hle : typeLT (f' ⁻¹' {c}) ≤ typeLT (f ⁻¹' {c}) :=
        typeLT_le_of_strictMono (f := fun u : f' ⁻¹' {c} => (⟨u.1.1, u.2⟩ : f ⁻¹' {c}))
          fun _ _ h => h
      exact hle.trans_lt (hf c)
    obtain ⟨P', hP'_disj, hP'_type⟩ := ih hδ1 hδc hQ2 f' hf'
    let P : Fin (k + 1) → Set ℕ := Fin.cases Q (fun i => Qᶜ ∩ P' i)
    refine ⟨P, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun h => (h rfl).elim) (fun j' _ => ?_) j
        change Disjoint Q (Qᶜ ∩ P' j')
        exact Set.disjoint_left.2 fun c hc1 hc2 => hc2.1 hc1
      · refine Fin.cases (fun _ => ?_) (fun j' h => ?_) j
        · change Disjoint (Qᶜ ∩ P' i') Q
          exact Set.disjoint_left.2 fun c hc1 hc2 => hc1.1 hc2
        · change Disjoint (Qᶜ ∩ P' i') (Qᶜ ∩ P' j')
          have hne : i' ≠ j' := fun heq => h (congrArg Fin.succ heq)
          exact (hP'_disj hne).mono Set.inter_subset_right Set.inter_subset_right
    · intro i
      refine Fin.cases hQ1 (fun j => ?_) i
      change typeLT (f ⁻¹' (Qᶜ ∩ P' j)) = ω ^ δ
      have heq : typeLT (f ⁻¹' (Qᶜ ∩ P' j)) = typeLT (f' ⁻¹' (P' j)) := by
        refine typeLT_eq_of_orderIso
          { toFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
            invFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_rel_iff' := Iff.rfl }
      rw [heq, hP'_type j]

/-- Countably infinite (`ω`-way) pairwise disjoint splitting of `f : U → ℕ`. -/
lemma countable_split_nat {U : Type} [LinearOrder U] [WellFoundedLT U]
    {δ : Ordinal.{0}} (hδ1 : 1 ≤ δ) (hδc : δ < ω₁)
    (hU : typeLT U = ω ^ δ) (f : U → ℕ)
    (hf : ∀ c : ℕ, typeLT (f ⁻¹' {c}) < ω ^ δ) :
    ∃ P : ℕ → Set ℕ,
      Pairwise (Function.onFun Disjoint P) ∧
      ∀ n : ℕ, typeLT (f ⁻¹' (P n)) = ω ^ δ := by
  -- Step function: given R ⊆ ℕ with typeLT (f ⁻¹' R) = ω ^ δ, split R = P ⊔ R'
  have hstep : ∀ R : Set ℕ, typeLT (f ⁻¹' R) = ω ^ δ →
      ∃ P R' : Set ℕ, P ⊆ R ∧ R' ⊆ R ∧ Disjoint P R' ∧
        typeLT (f ⁻¹' P) = ω ^ δ ∧ typeLT (f ⁻¹' R') = ω ^ δ := fun R hR => by
    let fR : (f ⁻¹' R : Set U) → ℕ := fun u => f u.1
    have hfR : ∀ c : ℕ, typeLT (fR ⁻¹' {c}) < ω ^ δ := fun c =>
      (typeLT_le_of_strictMono (f := fun u : fR ⁻¹' {c} => (⟨u.1.1, u.2⟩ : f ⁻¹' {c}))
        fun _ _ h => h).trans_lt (hf c)
    obtain ⟨Q, hQ1, hQ2⟩ := countable_split_two hδ1 hδc hR fR hfR
    refine ⟨R ∩ Q, R ∩ Qᶜ, Set.inter_subset_left, Set.inter_subset_left,
      Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1.2, ?_, ?_⟩
    · rw [← hQ1]
      refine typeLT_eq_of_orderIso
        { toFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
          invFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := Iff.rfl }
    · rw [← hQ2]
      refine typeLT_eq_of_orderIso
        { toFun := fun u => ⟨⟨u.1, u.2.1⟩, u.2.2⟩
          invFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := Iff.rfl }
  let Rem := {R : Set ℕ // typeLT (f ⁻¹' R) = ω ^ δ}
  let initRem : Rem := ⟨Set.univ, by rw [Set.preimage_univ, typeLT_univ, hU]⟩
  let nextRem : Rem → Rem := fun prev =>
    let h := hstep prev.1 prev.2
    ⟨Classical.choose (Classical.choose_spec h),
      (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2⟩
  let rem : ℕ → Rem := fun n => nextRem^[n] initRem
  have hrem_succ : ∀ n, rem (n + 1) = nextRem (rem n) := fun n =>
    Function.iterate_succ_apply' nextRem n initRem
  let P : ℕ → Set ℕ := fun n => Classical.choose (hstep (rem n).1 (rem n).2)
  have hP_sub : ∀ n, P n ⊆ (rem n).1 := fun n =>
    (Classical.choose_spec (Classical.choose_spec (hstep (rem n).1 (rem n).2))).1
  have hrem_sub : ∀ n, (rem (n + 1)).1 ⊆ (rem n).1 := fun n => by
    rw [hrem_succ]
    exact (Classical.choose_spec (Classical.choose_spec (hstep (rem n).1 (rem n).2))).2.1
  have hP_disj_next : ∀ n, Disjoint (P n) (rem (n + 1)).1 := fun n => by
    rw [hrem_succ]
    exact (Classical.choose_spec (Classical.choose_spec (hstep (rem n).1 (rem n).2))).2.2.1
  have hrem_anti : ∀ m n, m ≤ n → (rem n).1 ⊆ (rem m).1 := by
    intro m n hmn
    induction hmn with
    | refl => exact Subset.refl _
    | step _ ih => exact (hrem_sub _).trans ih
  refine ⟨P, ?_, fun n =>
    (Classical.choose_spec (Classical.choose_spec (hstep (rem n).1 (rem n).2))).2.2.2.1⟩
  intro m n hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hP_disj_next m).mono_right ((hP_sub n).trans (hrem_anti (m + 1) n hlt))
  · exact ((hP_disj_next n).mono_right ((hP_sub m).trans (hrem_anti (n + 1) m hgt))).symm

end KolmogorovSplit

/- ## Section 5: Component Peeling, Master Gluing (`H3`), and Countable Limits (`H2`) -/

section PeelingAndGluing

/-- Connected component of `u` in `G.induce U`, viewed as a subset of `V`. -/
def inducedComp {V : Type*} (G : SimpleGraph V) (U : Set V) (u : U) : Set V :=
  {v : V | ∃ hv : v ∈ U, (G.induce U).Reachable u ⟨v, hv⟩}

lemma inducedComp_sub {V : Type*} (G : SimpleGraph V) (U : Set V) (u : U) :
    inducedComp G U u ⊆ U := fun _ ⟨hv, _⟩ => hv

/-- **Component-Peeling Lemma**: If `G` has no infinite simple path and `B ⊆ V` has
additively indecomposable order type `ω ^ δ` (`1 ≤ δ`), then there is a finite cut `F` and a
component-union `U ⊆ V \ F` with `typeLT (U ∩ B) = ω ^ δ` whose every connected component
intersects `B` in order type `< ω ^ δ`. -/
lemma exists_finite_cut_small_components {V : Type} [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V)
    (hno : ¬ ∃ p : ℕ → V, Function.Injective p ∧ ∀ n, G.Adj (p n) (p (n + 1)))
    (B : Set V) {δ : Ordinal.{0}} (hδ : 1 ≤ δ) (hB : typeLT B = ω ^ δ) :
    ∃ (F : Finset V) (U : Set V),
      Disjoint (F : Set V) U ∧
      (∀ u ∈ U, ∀ v : V, v ∉ F → G.Adj u v → v ∈ U) ∧
      typeLT (U ∩ B : Set V) = ω ^ δ ∧
      ∀ u : U, typeLT (inducedComp G U u ∩ B : Set V) < ω ^ δ := by
  classical
  by_contra hnone
  push Not at hnone
  have hex_adj : ∀ (C : Set V) (v : V) (hv : v ∈ C)
      (_hconn : ∀ a b : C, (G.induce C).Reachable a b)
      (C' : Set V) (u0 : (C \ {v} : Set V)),
      C' = inducedComp G (C \ {v}) u0 →
      ∃ w ∈ C', G.Adj v w := by
    intro C v hv hconn C' u0 hC'
    have hreach := hconn ⟨v, hv⟩ ⟨u0.1, u0.2.1⟩
    obtain ⟨W⟩ := hreach
    suffices ∀ n : ℕ, ∀ (a b : C) (p : (G.induce C).Walk a b),
        p.length = n → a.1 = v → b.1 ∈ C' → ∃ w ∈ C', G.Adj v w by
      exact this W.length ⟨v, hv⟩ ⟨u0.1, u0.2.1⟩ W rfl rfl
        (hC' ▸ ⟨u0.2, SimpleGraph.Reachable.refl u0⟩)
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b p hlen ha hb
      cases p with
      | nil =>
        rw [hC'] at hb
        exact (hb.1.2 (Set.mem_singleton_iff.2 ha)).elim
      | @cons _ c _ hadj p' =>
        by_cases hmem : (⟨v, hv⟩ : C) ∈ p'.support
        · let p'' := p'.dropUntil ⟨v, hv⟩ hmem
          have hlen_lt : p''.length < n := by
            have h1 : p''.length ≤ p'.length := SimpleGraph.Walk.length_dropUntil_le_length p' hmem
            have h2 : p'.length + 1 = n := hlen
            omega
          exact ih p''.length hlen_lt ⟨v, hv⟩ b p'' rfl rfl hb
        · have hlift : ∀ {x y : C} (q : (G.induce C).Walk x y),
              (⟨v, hv⟩ : C) ∉ q.support →
              ∀ (hx : x.1 ∈ C \ {v}) (hy : y.1 ∈ C \ {v}),
                (G.induce (C \ {v})).Reachable ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
            intro x y q
            induction q with
            | nil =>
              intro _ hx hy
              exact SimpleGraph.Reachable.refl _
            | @cons x1 x2 y1 h12 q' ihq =>
              intro hnot hx1 hy1
              have hx2_ne : x2.1 ≠ v := fun heq => by
                have hxeq : x2 = ⟨v, hv⟩ := Subtype.ext heq
                exact hnot (List.mem_cons_of_mem x1 (hxeq ▸ SimpleGraph.Walk.start_mem_support q'))
              have hx2 : x2.1 ∈ C \ {v} := ⟨x2.2, hx2_ne⟩
              have hnot' : (⟨v, hv⟩ : C) ∉ q'.support := fun hm =>
                hnot (List.mem_cons_of_mem x1 hm)
              have hadj' : (G.induce (C \ {v})).Adj ⟨x1.1, hx1⟩ ⟨x2.1, hx2⟩ := h12
              exact hadj'.reachable.trans (ihq hnot' hx2 hy1)
          have hc_ne : c.1 ≠ v := fun heq => by
            have hceq : c = ⟨v, hv⟩ := Subtype.ext heq
            exact hmem (hceq ▸ SimpleGraph.Walk.start_mem_support p')
          have hc_mem : c.1 ∈ C \ {v} := ⟨c.2, hc_ne⟩
          rw [hC'] at hb
          obtain ⟨hb_mem, hb_reach⟩ := hb
          have hcb : (G.induce (C \ {v})).Reachable ⟨c.1, hc_mem⟩ ⟨b.1, hb_mem⟩ :=
            hlift p' hmem hc_mem hb_mem
          refine ⟨c.1, ?_, ha ▸ hadj⟩
          rw [hC']
          exact ⟨hc_mem, hb_reach.trans hcb.symm⟩
  let GoodState (F : Finset V) (C : Set V) (v : V) : Prop :=
    Disjoint (F : Set V) C ∧
    (∀ u ∈ C, ∀ w : V, w ∉ F → G.Adj u w → w ∈ C) ∧
    typeLT (C ∩ B : Set V) = ω ^ δ ∧
    (∀ a b : C, (G.induce C).Reachable a b) ∧
    v ∈ C
  have hinit : ∃ C : Set V, ∃ v : V, GoodState ∅ C v := by
    have h0 := hnone ∅ Set.univ (by simp) (fun _ _ _ _ _ => Set.mem_univ _)
      (by rw [Set.univ_inter]; exact hB)
    obtain ⟨u0, hu0_ge⟩ := h0
    let C0 := inducedComp G Set.univ u0
    have hC0_type : typeLT (C0 ∩ B : Set V) = ω ^ δ :=
      le_antisymm ((typeLT_mono_subset Set.inter_subset_right).trans_eq hB) hu0_ge
    refine ⟨C0, u0.1, by simp, ?_, hC0_type, ?_, ⟨Set.mem_univ _, SimpleGraph.Reachable.refl u0⟩⟩
    · intro u hu w _ hadj
      obtain ⟨_, hru⟩ := hu
      exact ⟨Set.mem_univ w, hru.trans (SimpleGraph.Adj.reachable hadj)⟩
    · intro a b
      have hlift : ∀ {x y : (Set.univ : Set V)} (q : (G.induce Set.univ).Walk x y),
          (G.induce Set.univ).Reachable u0 x →
          ∀ (hx : x.1 ∈ C0) (hy : y.1 ∈ C0),
            (G.induce C0).Reachable ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
        intro x y q
        induction q with
        | nil => intro _ _ _; exact SimpleGraph.Reachable.refl _
        | @cons x1 x2 y1 h12 q' ihq =>
          intro hr1 hx1 hy1
          have hr2 : (G.induce Set.univ).Reachable u0 x2 := hr1.trans (SimpleGraph.Adj.reachable h12)
          have hx2 : x2.1 ∈ C0 := ⟨x2.2, hr2⟩
          have hadj' : (G.induce C0).Adj ⟨x1.1, hx1⟩ ⟨x2.1, hx2⟩ := h12
          exact hadj'.reachable.trans (ihq hr2 hx2 hy1)
      obtain ⟨_, hra⟩ := a.2
      obtain ⟨_, hrb⟩ := b.2
      obtain ⟨W⟩ := hra.symm.trans hrb
      exact hlift W hra a.2 b.2
  have htrans : ∀ (F : Finset V) (C : Set V) (v : V), GoodState F C v →
      ∃ C' : Set V, ∃ w : V, GoodState (insert v F) C' w ∧ G.Adj v w := by
    intro F C v ⟨hdisj, hclosed, hCB, hconn, hvC⟩
    let F' := insert v F
    let U' := C \ {v}
    have hdisj' : Disjoint (F' : Set V) U' := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_insert.1 hx1 with rfl | hxF
      · exact hx2.2 rfl
      · exact Set.disjoint_left.1 hdisj hxF hx2.1
    have hclosed' : ∀ u ∈ U', ∀ w : V, w ∉ F' → G.Adj u w → w ∈ U' := by
      intro u hu w hw hadj
      have hwF : w ∉ F := fun h => hw (Finset.mem_insert_of_mem h)
      have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self v F)
      exact ⟨hclosed u hu.1 w hwF hadj, hwv⟩
    have hU'B : typeLT (U' ∩ B : Set V) = ω ^ δ := by
      have heq : U' ∩ B = (C ∩ B) \ (({v} : Finset V) : Set V) := by
        ext x
        simp only [U', Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe, Finset.mem_singleton]
        tauto
      rw [heq]
      exact typeLT_sdiff_finset_omega0_opow hδ hCB {v}
    obtain ⟨u0, hu0_ge⟩ := hnone F' U' hdisj' hclosed' hU'B
    let C' := inducedComp G U' u0
    have hC'_sub : C' ⊆ U' := inducedComp_sub G U' u0
    have hC'_type : typeLT (C' ∩ B : Set V) = ω ^ δ :=
      le_antisymm ((typeLT_mono_subset (Set.inter_subset_inter_left B (hC'_sub.trans Set.sdiff_subset))).trans_eq hCB) hu0_ge
    obtain ⟨w, hwC', hadj⟩ := hex_adj C v hvC hconn C' u0 rfl
    refine ⟨C', w, ⟨hdisj'.mono_right hC'_sub, ?_, hC'_type, ?_, hwC'⟩, hadj⟩
    · intro u hu x hx hadj_ux
      obtain ⟨huU', hru⟩ := hu
      have hxU' : x ∈ U' := hclosed' u huU' x hx hadj_ux
      have hadj' : (G.induce U').Adj ⟨u, huU'⟩ ⟨x, hxU'⟩ := hadj_ux
      exact ⟨hxU', hru.trans hadj'.reachable⟩
    · intro a b
      have hlift : ∀ {x y : U'} (q : (G.induce U').Walk x y),
          (G.induce U').Reachable u0 x →
          ∀ (hx : x.1 ∈ C') (hy : y.1 ∈ C'),
            (G.induce C').Reachable ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
        intro x y q
        induction q with
        | nil => intro _ _ _; exact SimpleGraph.Reachable.refl _
        | @cons x1 x2 y1 h12 q' ihq =>
          intro hr1 hx1 hy1
          have hr2 : (G.induce U').Reachable u0 x2 := hr1.trans (SimpleGraph.Adj.reachable h12)
          have hx2 : x2.1 ∈ C' := ⟨x2.2, hr2⟩
          have hadj' : (G.induce C').Adj ⟨x1.1, hx1⟩ ⟨x2.1, hx2⟩ := h12
          exact hadj'.reachable.trans (ihq hr2 hx2 hy1)
      obtain ⟨haU', hra⟩ := a.2
      obtain ⟨hbU', hrb⟩ := b.2
      obtain ⟨W⟩ := hra.symm.trans hrb
      exact hlift W hra a.2 b.2
  let St := {t : Finset V × Set V × V // GoodState t.1 t.2.1 t.2.2}
  let initSt : St :=
    ⟨(∅, Classical.choose hinit, Classical.choose (Classical.choose_spec hinit)),
      Classical.choose_spec (Classical.choose_spec hinit)⟩
  let nextSt : St → St := fun prev =>
    let h := htrans prev.1.1 prev.1.2.1 prev.1.2.2 prev.2
    ⟨(insert prev.1.2.2 prev.1.1,
      Classical.choose h,
      Classical.choose (Classical.choose_spec h)),
      (Classical.choose_spec (Classical.choose_spec h)).1⟩
  let run : ℕ → St := fun n => nextSt^[n] initSt
  have hrun_succ : ∀ n, run (n + 1) = nextSt (run n) := fun n =>
    Function.iterate_succ_apply' nextSt n initSt
  have hF_sub : ∀ m n, m ≤ n → (run m).1.1 ⊆ (run n).1.1 := by
    intro m n hmn
    induction hmn with
    | refl => exact Finset.Subset.refl _
    | step _ ih =>
      rw [hrun_succ]
      exact ih.trans (Finset.subset_insert _ _)
  have hv_in_nextF : ∀ n, (run n).1.2.2 ∈ (run (n + 1)).1.1 := fun n => by
    rw [hrun_succ]
    exact Finset.mem_insert_self _ _
  have hv_not_in_F : ∀ n, (run n).1.2.2 ∉ (run n).1.1 := fun n hv =>
    Set.disjoint_left.1 (run n).2.1 hv (run n).2.2.2.2.2
  have hadj_seq : ∀ n, G.Adj (run n).1.2.2 (run (n + 1)).1.2.2 := fun n => by
    rw [hrun_succ]
    exact (Classical.choose_spec (Classical.choose_spec
      (htrans (run n).1.1 (run n).1.2.1 (run n).1.2.2 (run n).2))).2
  have hinj : Function.Injective (fun n => (run n).1.2.2) := by
    intro m n hmn
    dsimp only at hmn
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (run m).1.2.2 ∈ (run n).1.1 := hF_sub (m + 1) n hlt (hv_in_nextF m)
      exact hv_not_in_F n (hmn ▸ h1)
    · have h1 : (run n).1.2.2 ∈ (run m).1.1 := hF_sub (n + 1) m hgt (hv_in_nextF n)
      exact hv_not_in_F m (hmn.symm ▸ h1)
  exact hno ⟨fun n => (run n).1.2.2, hinj, hadj_seq⟩

/-- **Master Gluing Lemma (`attach_indecomposable`)**:
For ANY limit ordinal `α` and ANY countable `1 ≤ δ < ω₁`:
`HasPathOrIndepSetOfType α → HasPathOrIndepSetOfType (ω ^ δ) → HasPathOrIndepSetOfType (α + ω ^ δ)`. -/
lemma attach_indecomposable {α δ : Ordinal.{0}}
    (hα : Order.IsSuccLimit α) (hδ1 : 1 ≤ δ) (hδc : δ < ω₁)
    (IHα : HasPathOrIndepSetOfType α)
    (IHδ : HasPathOrIndepSetOfType (ω ^ δ)) :
    HasPathOrIndepSetOfType (α + ω ^ δ) := by
  classical
  let V := α.ToType ⊕ₗ (ω ^ δ).ToType
  have hV : typeLT V = α + ω ^ δ := by
    rw [typeLT_sumLex, Ordinal.type_toType, Ordinal.type_toType]
  rw [hasPathOrIndep_iff_of_orderIso hV]
  intro G
  by_cases hpath : ∃ p : ℕ → V, Function.Injective p ∧ ∀ n, G.Adj (p n) (p (n + 1))
  · exact Or.inl hpath
  · right
    let Aset : Set V := Set.range (fun a : α.ToType => toLex (Sum.inl a))
    let Bset : Set V := Set.range (fun b : (ω ^ δ).ToType => toLex (Sum.inr b))
    have hA_type : typeLT Aset = α := by
      have hsm : StrictMono (fun a : α.ToType => (toLex (Sum.inl a) : V)) := fun _ _ h => Sum.Lex.inl h
      have h1 := typeLT_image_strictMono hsm Set.univ
      rw [Set.image_univ, typeLT_univ, Ordinal.type_toType] at h1
      exact h1
    have hB_type : typeLT Bset = ω ^ δ := by
      have hsm : StrictMono (fun b : (ω ^ δ).ToType => (toLex (Sum.inr b) : V)) := fun _ _ h => Sum.Lex.inr h
      have h1 := typeLT_image_strictMono hsm Set.univ
      rw [Set.image_univ, typeLT_univ, Ordinal.type_toType] at h1
      exact h1
    -- CNF decomposition of α = ω ^ η_0 + ... + ω ^ η_{m-1}
    obtain ⟨L, hL1, hLsum⟩ := cnf_limit α hα
    let m := L.length
    have hA_L : typeLT Aset = (L.map (fun η => ω ^ η)).sum := hA_type.trans hLsum
    obtain ⟨Bblk, hBblk_type, hBblk_ord⟩ := partition_of_list_sum (L.map (fun η => ω ^ η)) hA_L
    -- Peel components of Bset
    obtain ⟨F, U, hFU_disj, hU_closed, hUB_type, hU_small⟩ :=
      exists_finite_cut_small_components G hpath Bset hδ1 hB_type
    -- Countably many components of G.induce U meet Bset; label U ∩ Bset by component index in ℕ
    have hUB_cnt : Countable (U ∩ Bset : Set V) :=
      countable_of_typeLT_lt_omega1 (by rw [hUB_type]; exact omega0_opow_lt_omega1 hδc)
    let rel : (U ∩ Bset : Set V) → (U ∩ Bset : Set V) → Prop :=
      fun x y => (G.induce U).Reachable ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩
    let setoid : Setoid (U ∩ Bset : Set V) :=
      ⟨rel, ⟨fun _ => SimpleGraph.Reachable.refl _,
             fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
    have : Countable (Quotient setoid) := Quotient.countable
    obtain ⟨code, hcode_inj⟩ := Countable.exists_injective_nat (Quotient setoid)
    let f : (U ∩ Bset : Set V) → ℕ := fun x => code (Quotient.mk setoid x)
    have hf_small : ∀ c : ℕ, typeLT (f ⁻¹' {c}) < ω ^ δ := fun c => by
      by_cases hne : (f ⁻¹' {c}).Nonempty
      · obtain ⟨x0, hx0⟩ := hne
        have hsub : Subtype.val '' (f ⁻¹' {c}) ⊆ inducedComp G U ⟨x0.1, x0.2.1⟩ ∩ Bset := by
          rintro v ⟨y, hy, rfl⟩
          have hq : Quotient.mk setoid y = Quotient.mk setoid x0 :=
            hcode_inj ((hy : f y = c).trans hx0.symm)
          have hr : (G.induce U).Reachable ⟨y.1, y.2.1⟩ ⟨x0.1, x0.2.1⟩ := Quotient.exact hq
          exact ⟨⟨y.2.1, hr.symm⟩, y.2.2⟩
        have h1 := typeLT_mono_subset hsub
        rw [typeLT_image_val] at h1
        exact h1.trans_lt (hU_small ⟨x0.1, x0.2.1⟩)
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        have h0 : typeLT (∅ : Set (U ∩ Bset : Set V)) = 0 :=
          Ordinal.type_eq_zero_iff_isEmpty.2 inferInstance
        rw [h0]
        exact Ordinal.opow_pos δ Ordinal.omega0_pos
    obtain ⟨P, hP_disj, hP_type⟩ := countable_split_fin (m + 1) hδ1 hδc hUB_type f hf_small
    let Uj : Fin (m + 1) → Set V := fun j =>
      {v : V | ∃ hv : v ∈ U, ∃ b : (U ∩ Bset : Set V),
        (G.induce U).Reachable ⟨v, hv⟩ ⟨b.1, b.2.1⟩ ∧ f b ∈ P j}
    have hUj_disj : Pairwise (Function.onFun Disjoint Uj) := fun j₁ j₂ hne => by
      change Disjoint (Uj j₁) (Uj j₂)
      rw [Set.disjoint_left]
      rintro v ⟨hv, b₁, hr₁, hp₁⟩ ⟨_, b₂, hr₂, hp₂⟩
      have hreach : (G.induce U).Reachable ⟨b₁.1, b₁.2.1⟩ ⟨b₂.1, b₂.2.1⟩ := hr₁.symm.trans hr₂
      have hf_eq : f b₁ = f b₂ := congrArg code (Quotient.sound hreach)
      exact Set.disjoint_left.1 (hP_disj hne) hp₁ (hf_eq ▸ hp₂)
    have hUj_closed : ∀ j, ∀ u ∈ Uj j, ∀ v : V, v ∉ F → G.Adj u v → v ∈ Uj j := by
      rintro j u ⟨huU, b, hr, hpb⟩ v hvF hadj
      have hvU : v ∈ U := hU_closed u huU v hvF hadj
      have hadj' : (G.induce U).Adj ⟨v, hvU⟩ ⟨u, huU⟩ := hadj.symm
      exact ⟨hvU, b, hadj'.reachable.trans hr, hpb⟩
    have hUj_Btype : ∀ j, typeLT (Uj j ∩ Bset : Set V) = ω ^ δ := fun j => by
      refine le_antisymm ((typeLT_mono_subset Set.inter_subset_right).trans_eq hB_type) ?_
      have hsub : Subtype.val '' (f ⁻¹' (P j)) ⊆ Uj j ∩ Bset := by
        rintro v ⟨b, hb, rfl⟩
        exact ⟨⟨b.2.1, b, SimpleGraph.Reachable.refl _, hb⟩, b.2.2⟩
      have h1 := typeLT_mono_subset hsub
      rw [typeLT_image_val, hP_type j] at h1
      exact h1
    let Asub (i : Fin (L.map (fun η => ω ^ η)).length) : Set V := Subtype.val '' Bblk i
    have hAsub_type : ∀ i, typeLT (Asub i) = ω ^ (L.get (i.cast (by simp))) := fun i => by
      rw [typeLT_image_val, hBblk_type i]
      simp
    let Fsub (i : Fin (L.map (fun η => ω ^ η)).length) : Set V := Asub i \ (F : Set V)
    have hFsub_type : ∀ i, typeLT (Fsub i) = ω ^ (L.get (i.cast (by simp))) := fun i =>
      typeLT_sdiff_finset_omega0_opow (hL1 _ (List.get_mem L _)) (hAsub_type i) F
    have hat_most_one : ∀ i, ∀ j₁ j₂ : Fin (m + 1),
        typeLT (Fsub i \ Uj j₁ : Set V) < ω ^ (L.get (i.cast (by simp))) →
        typeLT (Fsub i \ Uj j₂ : Set V) < ω ^ (L.get (i.cast (by simp))) →
        j₁ = j₂ := fun i j₁ j₂ h1 h2 => by
      by_contra hne
      have hun : (Fsub i \ Uj j₁) ∪ (Fsub i \ Uj j₂) = Fsub i := by
        ext v; simp only [Set.mem_union, Set.mem_sdiff]
        constructor
        · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
        · intro hv
          by_cases h : v ∈ Uj j₁
          · exact Or.inr ⟨hv, fun h' => Set.disjoint_left.1 (hUj_disj hne) h h'⟩
          · exact Or.inl ⟨hv, h⟩
      have hlt := omega0_opow_union_lt (L.get (i.cast (by simp))) h1 h2
      rw [hun, hFsub_type i] at hlt
      exact lt_irrefl _ hlt
    have hex_j : ∃ j : Fin (m + 1), ∀ i : Fin (L.map (fun η => ω ^ η)).length,
        typeLT (Fsub i \ Uj j : Set V) = ω ^ (L.get (i.cast (by simp))) := by
      let badJ : Fin (L.map (fun η => ω ^ η)).length → Fin (m + 1) := fun i =>
        if h : ∃ j, typeLT (Fsub i \ Uj j : Set V) < ω ^ (L.get (i.cast (by simp))) then
          Classical.choose h
        else 0
      have hcard_img : (Finset.univ.image badJ).card < (Finset.univ : Finset (Fin (m + 1))).card := by
        calc (Finset.univ.image badJ).card
            ≤ (Finset.univ : Finset (Fin (L.map (fun η => ω ^ η)).length)).card := Finset.card_image_le
          _ = m := by simp [m]
          _ < m + 1 := Nat.lt_succ_self m
          _ = (Finset.univ : Finset (Fin (m + 1))).card := by simp
      have hne_sub : ((Finset.univ : Finset (Fin (m + 1))) \ Finset.univ.image badJ).Nonempty :=
        Finset.card_pos.1 (by
          rw [Finset.card_sdiff, Finset.inter_univ]
          omega)
      obtain ⟨j0, hj0⟩ := hne_sub
      have hj0_not : j0 ∉ Finset.univ.image badJ := (Finset.mem_sdiff.1 hj0).2
      refine ⟨j0, fun i => ?_⟩
      refine le_antisymm ((typeLT_mono_subset Set.sdiff_subset).trans_eq (hFsub_type i)) ?_
      by_contra hlt; push Not at hlt
      have hex : ∃ j, typeLT (Fsub i \ Uj j : Set V) < ω ^ (L.get (i.cast (by simp))) := ⟨j0, hlt⟩
      have heq : badJ i = j0 := by
        simp only [badJ, dif_pos hex]
        exact hat_most_one i (Classical.choose hex) j0 (Classical.choose_spec hex) hlt
      exact hj0_not (Finset.mem_image.2 ⟨i, Finset.mem_univ i, heq⟩)
    obtain ⟨j0, hj0⟩ := hex_j
    -- Combine surviving pieces of A and Uj j0 ∩ Bset
    let A' : Set V := ⋃ i : Fin (L.map (fun η => ω ^ η)).length, (Fsub i \ Uj j0)
    let B' : Set V := Uj j0 ∩ Bset
    have hA'_type : typeLT A' = α := by
      have hord' : ∀ i₁ i₂ : Fin (L.map (fun η => ω ^ η)).length, i₁ < i₂ →
          ∀ x ∈ Fsub i₁ \ Uj j0, ∀ y ∈ Fsub i₂ \ Uj j0, x < y := by
        intro i₁ i₂ hlt x hx y hy
        obtain ⟨ax, hax, rfl⟩ := hx.1.1
        obtain ⟨ay, hay, rfl⟩ := hy.1.1
        exact hBblk_ord i₁ i₂ hlt ax hax ay hay
      rw [typeLT_of_ordered_blocks (L := L.map (fun η => ω ^ η)) (fun i => by simpa using hj0 i) hord',
        ← hLsum]
    have hB'_type : typeLT B' = ω ^ δ := hUj_Btype j0
    have hA'_sub_A : A' ⊆ Aset := by
      intro v hv
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hv
      obtain ⟨a, _, rfl⟩ := hi.1.1
      exact a.2
    have hA'_disj_F : ∀ v ∈ A', v ∉ F := fun v hv => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hv
      exact hi.1.2
    have hA'_disj_Uj : ∀ v ∈ A', v ∉ Uj j0 := fun v hv => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hv
      exact hi.2
    -- ZERO edges between A' and B'!
    have hno_cross : ∀ x ∈ A', ∀ y ∈ B', ¬ G.Adj x y := fun x hx y hy hadj =>
      hA'_disj_Uj x hx (hUj_closed j0 y hy.1 x (hA'_disj_F x hx) hadj.symm)
    -- Apply IHα to G.induce A' and IHδ to G.induce B'
    have hnoA : ¬ ∃ p : ℕ → A', Function.Injective p ∧ ∀ n, (G.induce A').Adj (p n) (p (n + 1)) := by
      rintro ⟨p, hinj, hadj⟩
      exact hpath ⟨fun n => (p n).1, Subtype.val_injective.comp hinj, hadj⟩
    have hnoB : ¬ ∃ p : ℕ → B', Function.Injective p ∧ ∀ n, (G.induce B').Adj (p n) (p (n + 1)) := by
      rintro ⟨p, hinj, hadj⟩
      exact hpath ⟨fun n => (p n).1, Subtype.val_injective.comp hinj, hadj⟩
    obtain ⟨IA, hIA_indep, hIA_type⟩ :=
      (hasPathOrIndep_of_orderIso hA'_type IHα (G.induce A')).resolve_left hnoA
    obtain ⟨IB, hIB_indep, hIB_type⟩ :=
      (hasPathOrIndep_of_orderIso hB'_type IHδ (G.induce B')).resolve_left hnoB
    let IAv : Set V := Subtype.val '' IA
    let IBv : Set V := Subtype.val '' IB
    refine ⟨IAv ∪ IBv, ?_, ?_⟩
    · intro x hx y hy hne hadj
      rcases hx with ⟨ax, hax, rfl⟩ | ⟨bx, hbx, rfl⟩ <;>
      rcases hy with ⟨ay, hay, rfl⟩ | ⟨by_, hby, rfl⟩
      · exact hIA_indep hax hay (fun h => hne (congrArg Subtype.val h)) hadj
      · exact hno_cross ax.1 ax.2 by_.1 by_.2 hadj
      · exact hno_cross ay.1 ay.2 bx.1 bx.2 hadj.symm
      · exact hIB_indep hbx hby (fun h => hne (congrArg Subtype.val h)) hadj
    · have hord_AB : ∀ x ∈ IAv, ∀ y ∈ IBv, x < y := by
        rintro x ⟨ax, _, rfl⟩ y ⟨by_, _, rfl⟩
        obtain ⟨a, ha⟩ := hA'_sub_A ax.2
        obtain ⟨b, hb⟩ := by_.2.2
        rw [← ha, ← hb]
        exact Sum.Lex.sep a b
      rw [typeLT_union_le_add hord_AB,
        typeLT_image_val,
        typeLT_image_val,
        hIA_type, hIB_type]

/-- **Attaching any countable limit tail (`H3` + CNF step for `H2`)**:
Given any limit ordinal `α`, any countable limit ordinal `β < ω₁`, if `α` and every
indecomposable `ω ^ δ ≤ β` (`1 ≤ δ < ω₁`) satisfy `HasPathOrIndepSetOfType`, then so does `α + β`. -/
lemma attach_countable_limit {α β : Ordinal.{0}}
    (hα : Order.IsSuccLimit α) (hβ : Order.IsSuccLimit β) (hβc : β < ω₁)
    (IHα : HasPathOrIndepSetOfType α)
    (IHind : ∀ δ : Ordinal.{0}, 1 ≤ δ → δ < ω₁ → ω ^ δ ≤ β → HasPathOrIndepSetOfType (ω ^ δ)) :
    HasPathOrIndepSetOfType (α + β) := by
  obtain ⟨L, hL1, hLsum⟩ := cnf_limit β hβ
  rw [hLsum] at hβc IHind ⊢
  -- Induct on L (in reverse via list append or directly with generalized α!)
  have hmain : ∀ (M : List Ordinal.{0}) (α₀ : Ordinal.{0}),
      Order.IsSuccLimit α₀ →
      HasPathOrIndepSetOfType α₀ →
      (∀ η ∈ M, 1 ≤ η) →
      (M.map (fun η => ω ^ η)).sum < ω₁ →
      (∀ δ : Ordinal.{0}, 1 ≤ δ → δ < ω₁ → ω ^ δ ≤ (M.map (fun η => ω ^ η)).sum →
        HasPathOrIndepSetOfType (ω ^ δ)) →
      HasPathOrIndepSetOfType (α₀ + (M.map (fun η => ω ^ η)).sum) := by
    intro M
    induction M with
    | nil =>
      intro α₀ _ hIH _ _ _
      simpa using hIH
    | cons η t ih =>
      intro α₀ hα₀ hIH hM1 hMc hMind
      simp only [List.map_cons, List.sum_cons] at hMc hMind ⊢
      rw [← add_assoc]
      have hη1 : 1 ≤ η := hM1 η List.mem_cons_self
      have hωη_le : ω ^ η ≤ ω ^ η + (t.map (fun x => ω ^ x)).sum := by simp
      have hωη_lt : ω ^ η < ω₁ := hωη_le.trans_lt hMc
      have hηc : η < ω₁ := (Ordinal.right_le_opow η Ordinal.one_lt_omega0).trans_lt hωη_lt
      have hIH_next : HasPathOrIndepSetOfType (α₀ + ω ^ η) :=
        attach_indecomposable hα₀ hη1 hηc hIH (hMind η hη1 hηc hωη_le)
      have hlim_next : Order.IsSuccLimit (α₀ + ω ^ η) := by
        have hlimη : Order.IsSuccLimit (ω ^ η) :=
          Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (Order.one_le_iff_ne_zero.1 hη1)
        exact Ordinal.isSuccLimit_add α₀ hlimη
      have ht_le : (t.map (fun x => ω ^ x)).sum ≤ ω ^ η + (t.map (fun x => ω ^ x)).sum := by simp
      exact ih (α₀ + ω ^ η) hlim_next hIH_next
        (fun x hx => hM1 x (List.mem_cons_of_mem η hx))
        (ht_le.trans_lt hMc)
        (fun δ hδ1 hδc hδle => hMind δ hδ1 hδc (hδle.trans ht_le))
  exact hmain L α hα IHα hL1 hβc IHind

/-- **Part B (`H2`)**: Every countable limit ordinal `α < ω₁` satisfies `HasPathOrIndepSetOfType α`. -/
lemma hasPathOrIndep_of_countable_limit :
    ∀ α : Ordinal.{0}, α < ω₁ → Order.IsSuccLimit α → HasPathOrIndepSetOfType α := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro hαc hαlim
    have hα0 : α ≠ 0 := hαlim.ne_bot
    have hωα : ω ≤ α := Ordinal.omega0_le_of_isSuccLimit hαlim
    let δ := Ordinal.log ω α
    have hδ1 : 1 ≤ δ := by
      have h0 : Order.succ (0 : Ordinal.{0}) ≤ δ :=
        Order.succ_le_iff.2 (Ordinal.log_pos Ordinal.one_lt_omega0 hα0 hωα)
      rwa [Order.succ_eq_add_one, zero_add] at h0
    have hωδ_le : ω ^ δ ≤ α := Ordinal.opow_log_le_self ω hα0
    have hδc : δ < ω₁ := (Ordinal.right_le_opow δ Ordinal.one_lt_omega0).trans_lt (hωδ_le.trans_lt hαc)
    by_cases heq : α = ω ^ δ
    · rw [heq] at hαc ⊢
      by_cases hδ_one : δ = 1
      · rw [hδ_one]
        simpa using Erdos601.erdos_601.variants.at_omega
      · have h1lt : 1 < δ := lt_of_le_of_ne hδ1 (Ne.symm hδ_one)
        have hseq_ex : ∃ αseq : ℕ → Ordinal.{0},
            (∀ n, Order.IsSuccLimit (αseq n) ∧ αseq n < ω ^ δ) ∧
            ω ^ δ ≤ typeLT (LexSigma ℕ (fun n => (αseq n).ToType)) := by
          rcases Ordinal.zero_or_succ_or_isSuccLimit δ with h0 | ⟨γ, hγ⟩ | hlim
          · exact (not_lt.2 zero_le (h0 ▸ h1lt)).elim
          · rw [← hγ] at h1lt ⊢
            have hγ1 : 1 ≤ γ := by
              by_contra hlt; push Not at hlt
              have hγ0 : γ = 0 := Order.lt_one_iff.1 hlt
              subst hγ0; simp at h1lt
            refine ⟨fun _ => ω ^ γ, fun _ => ⟨Ordinal.isSuccLimit_opow_left
                Ordinal.isSuccLimit_omega0 (Order.one_le_iff_ne_zero.1 hγ1),
              (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (Order.lt_succ γ)⟩, ?_⟩
            rw [Ordinal.opow_succ]
            have hprod : typeLT (ℕ ×ₗ (ω ^ γ).ToType) = ω ^ γ * ω := by
              rw [typeLT_prodLex, Ordinal.type_toType, Ordinal.type_nat_lt]
            rw [← hprod]
            refine typeLT_le_of_strictMono
              (f := fun p : ℕ ×ₗ (ω ^ γ).ToType =>
                (⟨(ofLex p).1, (ofLex p).2⟩ : LexSigma ℕ (fun _ => (ω ^ γ).ToType))) ?_
            intro a b hab
            cases a with | _ a' => cases b with | _ b' =>
            cases a' with | mk a1 a2 => cases b' with | mk b1 b2 =>
            rcases Prod.lex_iff.1 hab with h1 | ⟨h1, h2⟩
            · exact Or.inl h1
            · subst h1; exact Or.inr ⟨rfl, h2⟩
          · have : Countable δ.ToType := countable_toType_of_lt_omega1 hδc
            have : Nonempty δ.ToType := by
              have hpos : 0 < typeLT δ.ToType := by
                rw [Ordinal.type_toType]; exact (zero_lt_one (α := Ordinal.{0})).trans h1lt
              obtain ⟨x, _⟩ := Ordinal.typein_surj LT.lt hpos
              exact ⟨x⟩
            obtain ⟨e, he_surj⟩ := exists_surjective_nat δ.ToType
            let αseq : ℕ → Ordinal.{0} := fun n => ω ^ (Order.succ (Ordinal.typein LT.lt (e n)))
            refine ⟨αseq, fun n => ?_, ?_⟩
            · have hsucc_lt : Order.succ (Ordinal.typein LT.lt (e n)) < δ :=
                hlim.succ_lt ((Ordinal.typein_lt_type LT.lt (e n)).trans_eq (Ordinal.type_toType δ))
              refine ⟨Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
                (Order.succ_ne_bot _), (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 hsucc_lt⟩
            · rw [Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero hlim]
              intro γ hγ
              obtain ⟨x, hx⟩ := Ordinal.typein_surj LT.lt (by rwa [Ordinal.type_toType])
              obtain ⟨n, hn⟩ := he_surj x
              have hle1 : ω ^ γ ≤ αseq n := by
                dsimp [αseq]; rw [hn, hx]
                exact Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.le_succ γ)
              refine hle1.trans ?_
              rw [← Ordinal.type_toType (αseq n)]
              exact typeLT_le_of_strictMono
                (f := fun y : (αseq n).ToType =>
                  (⟨n, y⟩ : LexSigma ℕ (fun k => (αseq k).ToType)))
                fun _ _ h => Or.inr ⟨rfl, h⟩
        obtain ⟨αseq, hαseq, hsum_ge⟩ := hseq_ex
        intro G
        by_cases hpath : ∃ p : ℕ → (ω ^ δ).ToType,
            Function.Injective p ∧ ∀ n, G.Adj (p n) (p (n + 1))
        · exact Or.inl hpath
        · right
          obtain ⟨F, U, _, hU_closed, hU_type, hU_small⟩ :=
            exists_finite_cut_small_components G hpath Set.univ hδ1
              (by rw [typeLT_univ, Ordinal.type_toType])
          rw [Set.inter_univ] at hU_type
          have : Countable U := countable_of_typeLT_lt_omega1 (by rw [hU_type]; exact hαc)
          let setoid : Setoid U :=
            ⟨fun x y => (G.induce U).Reachable x y,
             ⟨fun _ => SimpleGraph.Reachable.refl _,
              fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
          have : Countable (Quotient setoid) := Quotient.countable
          obtain ⟨code, hcode_inj⟩ := Countable.exists_injective_nat (Quotient setoid)
          let f : U → ℕ := fun x => code (Quotient.mk setoid x)
          have hf_small : ∀ c : ℕ, typeLT (f ⁻¹' {c}) < ω ^ δ := fun c => by
            by_cases hne : (f ⁻¹' {c}).Nonempty
            · obtain ⟨x0, hx0⟩ := hne
              have hsub : Subtype.val '' (f ⁻¹' {c}) ⊆ inducedComp G U x0 ∩ Set.univ := by
                rintro v ⟨y, hy, rfl⟩
                have hq : Quotient.mk setoid y = Quotient.mk setoid x0 :=
                  hcode_inj ((hy : f y = c).trans hx0.symm)
                exact ⟨⟨y.2, (Quotient.exact hq).symm⟩, Set.mem_univ _⟩
              have h1 := typeLT_mono_subset hsub
              rw [typeLT_image_val] at h1
              exact h1.trans_lt (hU_small x0)
            · rw [Set.not_nonempty_iff_eq_empty] at hne
              rw [hne]
              have h0 : typeLT (∅ : Set U) = 0 := Ordinal.type_eq_zero_iff_isEmpty.2 inferInstance
              rw [h0]
              exact Ordinal.opow_pos δ Ordinal.omega0_pos
          obtain ⟨P, hP_disj, hP_type⟩ := countable_split_nat hδ1 hδc hU_type f hf_small
          let Un : ℕ → Set (ω ^ δ).ToType := fun n => Subtype.val '' (f ⁻¹' (P n))
          have hUn_type : ∀ n, typeLT (Un n) = ω ^ δ := fun n => by
            rw [typeLT_image_val, hP_type n]
          have hUn_no_edge : ∀ m n, m ≠ n → ∀ x ∈ Un m, ∀ y ∈ Un n, ¬ G.Adj x y := by
            rintro m n hne _ ⟨xm, hxm, rfl⟩ _ ⟨yn, hyn, rfl⟩ hadj
            have hreach : (G.induce U).Reachable xm yn := SimpleGraph.Adj.reachable hadj
            have hf_eq : f xm = f yn := congrArg code (Quotient.sound hreach)
            exact Set.disjoint_left.1 (hP_disj hne) hxm (hf_eq ▸ hyn)
          have hpick_block : ∀ (n : ℕ) (lb : Option (ω ^ δ).ToType),
              ∃ (A : Set (ω ^ δ).ToType) (b : (ω ^ δ).ToType),
                A ⊆ Un n ∧ typeLT A = αseq n ∧
                (∀ x ∈ A, x < b) ∧
                (∀ x ∈ A, ∀ l, lb = some l → l < x) := fun n lb => by
            let tail : Set (ω ^ δ).ToType :=
              match lb with
              | none => Un n
              | some l => {x ∈ Un n | l < x}
            have htail_type : typeLT tail = ω ^ δ := by
              cases lb with
              | none => exact hUn_type n
              | some l =>
                have hdiff : tail = Un n \ Set.Iic l := by
                  ext x; simp [tail, Set.mem_sdiff, not_le]
                rw [hdiff]
                refine typeLT_sdiff_of_lt_omega0_opow (hUn_type n) ?_
                have hIic : Set.Iic l = Set.Iio l ∪ {l} := by ext x; simp [le_iff_lt_or_eq]
                rw [hIic]
                have hlt1 : typeLT (Set.Iio l) < ω ^ δ := by
                  change Ordinal.type (α := Set.Iio l) (· < ·) < ω ^ δ
                  rw [Ordinal.type_Iio_lt]
                  exact (Ordinal.typein_lt_type LT.lt l).trans_eq (Ordinal.type_toType (ω ^ δ))
                have hlt2 : typeLT ({l} : Set (ω ^ δ).ToType) < ω ^ δ :=
                  (typeLT_finite_lt_omega0 (Set.finite_singleton l)).trans_le
                    (by simpa using Ordinal.opow_le_opow_right Ordinal.omega0_pos hδ1)
                exact omega0_opow_union_lt δ hlt1 hlt2
            have hlt_a : αseq n < typeLT tail := htail_type.symm ▸ (hαseq n).2
            obtain ⟨c, hc⟩ := Ordinal.typein_surj LT.lt hlt_a
            let A : Set (ω ^ δ).ToType := {x | x ∈ tail ∧ x < c.1}
            refine ⟨A, c.1, fun x hx => ?_, ?_, fun x hx => hx.2, fun x hx l hl => ?_⟩
            · cases lb with
              | none => exact hx.1
              | some _ => exact hx.1.1
            · rw [typeLT_Iio_subtype tail c, hc]
            · subst hl; exact hx.1.2
          let chooseBlk : ℕ → Set (ω ^ δ).ToType × (ω ^ δ).ToType :=
            Nat.rec
              (let h := hpick_block 0 none
               (Classical.choose h, Classical.choose (Classical.choose_spec h)))
              (fun n prev =>
                let h := hpick_block (n + 1) (some prev.2)
                (Classical.choose h, Classical.choose (Classical.choose_spec h)))
          let A : ℕ → Set (ω ^ δ).ToType := fun n => (chooseBlk n).1
          let b : ℕ → (ω ^ δ).ToType := fun n => (chooseBlk n).2
          have hA_sub : ∀ n, A n ⊆ Un n := fun n => by
            cases n with
            | zero => exact (Classical.choose_spec (Classical.choose_spec (hpick_block 0 none))).1
            | succ n => exact (Classical.choose_spec (Classical.choose_spec (hpick_block (n + 1) (some (chooseBlk n).2)))).1
          have hA_type : ∀ n, typeLT (A n) = αseq n := fun n => by
            cases n with
            | zero => exact (Classical.choose_spec (Classical.choose_spec (hpick_block 0 none))).2.1
            | succ n => exact (Classical.choose_spec (Classical.choose_spec (hpick_block (n + 1) (some (chooseBlk n).2)))).2.1
          have hA_lt_b : ∀ n, ∀ x ∈ A n, x < b n := fun n => by
            cases n with
            | zero => exact (Classical.choose_spec (Classical.choose_spec (hpick_block 0 none))).2.2.1
            | succ n => exact (Classical.choose_spec (Classical.choose_spec (hpick_block (n + 1) (some (chooseBlk n).2)))).2.2.1
          have hb_lt_A : ∀ n, ∀ x ∈ A (n + 1), b n < x := fun n x hx =>
            (Classical.choose_spec (Classical.choose_spec (hpick_block (n + 1) (some (chooseBlk n).2)))).2.2.2 x hx (b n) rfl
          have hb_mono : StrictMono b := strictMono_nat_of_lt_succ fun n => by
            have hne : (A (n + 1)).Nonempty := by
              by_contra he
              rw [Set.not_nonempty_iff_eq_empty] at he
              have h0 : typeLT (A (n + 1)) = 0 := by
                rw [he]; exact Ordinal.type_eq_zero_iff_isEmpty.2 inferInstance
              rw [hA_type (n + 1)] at h0
              exact (hαseq (n + 1)).1.ne_bot h0
            obtain ⟨x, hx⟩ := hne
            exact (hb_lt_A n x hx).trans (hA_lt_b (n + 1) x hx)
          have hA_ord : ∀ m n, m < n → ∀ x ∈ A m, ∀ y ∈ A n, x < y := by
            intro m n hmn x hx y hy
            obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
            have hmk : m ≤ k := Nat.le_of_lt_succ hmn
            exact (hA_lt_b m x hx).trans_le (hb_mono.monotone hmk) |>.trans (hb_lt_A k y hy)
          have hI_ex : ∀ n, ∃ I : Set (ω ^ δ).ToType,
              I ⊆ A n ∧ G.IsIndepSet I ∧ typeLT I = αseq n := fun n => by
            have hIHn : HasPathOrIndepSetOfType (αseq n) :=
              ih (αseq n) (heq ▸ (hαseq n).2) ((hαseq n).2.trans hαc) (hαseq n).1
            have hno_n : ¬ ∃ p : ℕ → A n, Function.Injective p ∧
                ∀ k, (G.induce (A n)).Adj (p k) (p (k + 1)) := by
              rintro ⟨p, hinj, hadj⟩
              exact hpath ⟨fun k => (p k).1, Subtype.val_injective.comp hinj, hadj⟩
            obtain ⟨In, hIn_indep, hIn_type⟩ :=
              (hasPathOrIndep_of_orderIso (hA_type n) hIHn (G.induce (A n))).resolve_left hno_n
            refine ⟨Subtype.val '' In, fun x ⟨a, _, ha⟩ => ha ▸ a.2, ?_, ?_⟩
            · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne hadj
              exact hIn_indep ha hb (fun h => hne (congrArg Subtype.val h)) hadj
            · rw [typeLT_image_val, hIn_type]
          choose I hI_sub hI_indep hI_type using hI_ex
          let Iall : Set (ω ^ δ).ToType := ⋃ n : ℕ, I n
          refine ⟨Iall, ?_, le_antisymm ((typeLT_set_le_self Iall).trans_eq (Ordinal.type_toType _)) ?_⟩
          · intro x hx y hy hne hadj
            obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hx
            obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
            by_cases hmn : m = n
            · subst hmn; exact hI_indep m hm hn hne hadj
            · exact hUn_no_edge m n hmn x (hA_sub m (hI_sub m hm)) y (hA_sub n (hI_sub n hn)) hadj
          · have hiso : ∀ n, Nonempty ((αseq n).ToType ≃o I n) := fun n => by
              obtain ⟨e⟩ := exists_orderIso_toType (hI_type n)
              exact ⟨e.symm⟩
            let ψ := fun n => Classical.choice (hiso n)
            let emb : LexSigma ℕ (fun n => (αseq n).ToType) → Iall := fun p =>
              ⟨(ψ p.fst p.snd).1, Set.mem_iUnion.2 ⟨p.fst, (ψ p.fst p.snd).2⟩⟩
            have hemb : StrictMono emb := by
              intro a b hab
              rcases hab with h1 | ⟨h1, h2⟩
              · exact hA_ord a.fst b.fst h1 _ (hI_sub a.fst (ψ a.fst a.snd).2)
                  _ (hI_sub b.fst (ψ b.fst b.snd).2)
              · cases a with | mk ia xa => cases b with | mk ib xb =>
                dsimp at h1 h2 ⊢; subst h1
                exact (ψ ia).strictMono h2
            exact hsum_ge.trans (typeLT_le_of_strictMono hemb)
    · have hωδ_lt : ω ^ δ < α := lt_of_le_of_ne hωδ_le (Ne.symm heq)
      let r := α - ω ^ δ
      have hadd : ω ^ δ + r = α := Ordinal.add_sub_cancel_of_le hωδ_le
      have hr_lt : r < α := Ordinal.sub_omega0_opow_log_lt hα0
      have hr_ne : r ≠ 0 := fun h0 => heq (by simpa [h0] using hadd.symm)
      have hr_lim : Order.IsSuccLimit r := by
        rw [← hadd] at hαlim
        exact isSuccLimit_of_add_right hαlim hr_ne
      have hωδ_lim : Order.IsSuccLimit (ω ^ δ) :=
        Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (Order.one_le_iff_ne_zero.1 hδ1)
      rw [← hadd]
      refine attach_countable_limit hωδ_lim hr_lim (hr_lt.trans hαc)
        (ih (ω ^ δ) hωδ_lt (hωδ_lt.trans hαc) hωδ_lim) ?_
      intro η hη1 hηc hηle
      exact ih (ω ^ η) (hηle.trans_lt hr_lt) ((hηle.trans_lt hr_lt).trans hαc)
        (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (Order.one_le_iff_ne_zero.1 hη1))

end PeelingAndGluing

/- ## Section 6: Main Theorem -/

theorem erdos_hajnal_milner_1970_proof :
    ∀ α : Ordinal.{0},
      Order.IsSuccLimit α →
      α < ω_ 1 ^ (ω + 2) →
      HasPathOrIndepSetOfType α := by
  intro α hαlim hαlt
  let γ := α / ω₁
  let β := α % ω₁
  have hdiv : ω₁ * γ + β = α := Ordinal.div_add_mod α ω₁
  have hβlt : β < ω₁ := Ordinal.mod_lt α (Ordinal.omega_pos 1).ne'
  by_cases hγ0 : γ = 0
  · rw [hγ0, mul_zero, zero_add] at hdiv
    rw [← hdiv] at hαlim ⊢
    exact hasPathOrIndep_of_countable_limit β hβlt hαlim
  · have hmul_lt : ω₁ * γ < ω₁ ^ (ω + 2) :=
      (Ordinal.mul_div_le α ω₁).trans_lt hαlt
    have hH1 : HasPathOrIndepSetOfType (ω₁ * γ) := hasPathOrIndep_of_omega1_mul hmul_lt
    by_cases hβ0 : β = 0
    · rw [hβ0, add_zero] at hdiv
      rwa [← hdiv]
    · have hβlim : Order.IsSuccLimit β := by
        rw [← hdiv] at hαlim
        exact isSuccLimit_of_add_right hαlim hβ0
      have hmul_lim : Order.IsSuccLimit (ω₁ * γ) :=
        Ordinal.isSuccLimit_mul_left (Cardinal.isSuccLimit_omega 1) (pos_iff_ne_zero.2 hγ0)
      rw [← hdiv]
      refine attach_countable_limit hmul_lim hβlim hβlt hH1 ?_
      intro δ hδ1 hδc hδle
      exact hasPathOrIndep_of_countable_limit (ω ^ δ) (hδle.trans_lt hβlt)
        (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (Order.one_le_iff_ne_zero.1 hδ1))

end

end OMA.Erdos601EHM

theorem OMA.solution : type_of% @Erdos601.erdos_601.variants.erdos_hajnal_milner_1970 :=
  OMA.Erdos601EHM.erdos_hajnal_milner_1970_proof
