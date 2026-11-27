import FormalConjectures.ErdosProblems.«590»

/-!
# Proof of `Erdos590.erdos_590.variants.finite_cardinal`

We prove Milner's theorem (following Jean A. Larson, *A short proof of a partition theorem for
the ordinal `ω ^ ω`*, Ann. Math. Logic 6 (1973), 129–145): for every `m : ℕ`,
`OrdinalCardinalRamsey (ω ^ ω) (ω ^ ω) m`.

## Outline
1. **Finite-exponent ordinal Ramsey**: We prove `ω ^ ((n - 1) * (m - 1) + 1) → (ω ^ n, m)²`
   for all `n ≥ 1, m ≥ 1` by induction on `m`, using finite-union indivisibility of `ω ^ A` and
   diagonal construction along `Nat.unpair`.
2. **Nash-Williams Partition Theorem**: Proved for thin families of strictly sorted lists via
   Galvin–Prikry combinatorial forcing (accepts / strongly accepts / rejects).
3. **Larson's interaction schemes**: Modeled on strictly sorted lists `W` with `lenLex` order,
   using a deterministic decoder `decodeForm` that directly implies thinness (Lemma 3.11) and
   supports Nash-Williams diagonalization across all forms `l ≥ 1` (Lemma 3.6).
4. **Monotone-cursor constructions**: Lemma 3.7 (homogeneous `m`-clique for each form `l ≥ 1`)
   and Lemma 3.8 (order-type `ω ^ ω` subset `X ⊆ W` whose unequal-length pairs all admit valid
   interaction schemes via `mergeBlocks`).
5. **Main theorem**: Pull back along a levelwise red embedding `W → W` (from Step 1) to make
   all equal-length pairs red, apply Lemmas 3.6–3.8 to obtain a red `ω ^ ω`, and lift to
   universe `u`.
-/

namespace Erdos590Finite

open Cardinal Ordinal Filter Set

open scoped Classical

/- ### Section 1: `NatTuple` and Finite-Exponent Ordinal Ramsey -/

private abbrev NatTuple : ℕ → Type
  | 0 => PUnit
  | n + 1 => ℕ ×ₗ NatTuple n

private instance instLinearOrderNatTuple : ∀ n, LinearOrder (NatTuple n)
  | 0 => inferInstanceAs (LinearOrder PUnit)
  | n + 1 =>
    letI := instLinearOrderNatTuple n
    inferInstanceAs (LinearOrder (ℕ ×ₗ NatTuple n))

private lemma wellFoundedLT_natTuple : ∀ n, WellFoundedLT (NatTuple n)
  | 0 => inferInstanceAs (WellFoundedLT PUnit)
  | n + 1 =>
    letI := wellFoundedLT_natTuple n
    inferInstanceAs (WellFoundedLT (ℕ ×ₗ NatTuple n))

private instance instWellFoundedLTNatTuple (n : ℕ) : WellFoundedLT (NatTuple n) :=
  wellFoundedLT_natTuple n

private lemma countable_natTuple : ∀ n, Countable (NatTuple n)
  | 0 => inferInstanceAs (Countable PUnit)
  | n + 1 =>
    letI := countable_natTuple n
    show Countable (ℕ × NatTuple n) from inferInstance

private instance instCountableNatTuple (n : ℕ) : Countable (NatTuple n) :=
  countable_natTuple n

private lemma typeLT_prodLex {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] :
    typeLT (α ×ₗ β) = (typeLT β) * (typeLT α) := by
  have e : ((· < ·) : (α ×ₗ β) → (α ×ₗ β) → Prop) ≃r
      Prod.Lex ((· < ·) : α → α → Prop) ((· < ·) : β → β → Prop) :=
    { toEquiv := ofLex
      map_rel_iff' := by intro _ _; rfl }
  rw [e.ordinalType_congr, Ordinal.type_prod_lex]

private lemma typeLT_natTuple (n : ℕ) : typeLT (NatTuple n) = (ω : Ordinal.{0}) ^ n := by
  induction n with
  | zero =>
    change typeLT PUnit = 1
    exact Ordinal.type_eq_one_of_unique _
  | succ n ih =>
    change typeLT (ℕ ×ₗ NatTuple n) = (ω : Ordinal.{0}) ^ (n + 1)
    rw [typeLT_prodLex, ih, Ordinal.type_nat_lt, pow_succ]

private def relEmbeddingOfStrictMono {α β : Type} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) :
    ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  ⟨⟨f, hf.injective⟩, hf.lt_iff_lt⟩

private lemma typeLT_le_of_strictMono {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (f : α → β) (hf : StrictMono f) :
    typeLT α ≤ typeLT β :=
  Ordinal.type_le_iff'.2 ⟨relEmbeddingOfStrictMono f hf⟩

private lemma typeLT_subsingleton_le_one {α : Type} [LinearOrder α] [WellFoundedLT α]
    (S : Set α) (hS : S.Subsingleton) : typeLT S ≤ 1 := by
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have huniq : Unique S :=
      { default := ⟨x, hx⟩
        uniq := fun y => Subtype.ext (hS y.2 hx) }
    exact le_of_eq (Ordinal.type_eq_one_of_unique _)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hempty : IsEmpty S := ⟨fun y => by rw [hne] at y; exact y.2⟩
    rw [Ordinal.type_eq_zero_of_empty]
    exact bot_le

private lemma exists_not_mem_of_typeLT_lt :
    ∀ (A : ℕ) {r : ℕ} (Z : Fin r → Set (NatTuple A)),
      (∀ j, typeLT (Z j) < (ω : Ordinal.{0}) ^ A) →
      ∃ y : NatTuple A, ∀ j, y ∉ Z j
  | 0, r, Z, hZ => by
    refine ⟨PUnit.unit, fun j hmem => ?_⟩
    have h1 : (1 : Ordinal.{0}) ≤ typeLT (Z j) := by
      have hsub : typeLT PUnit ≤ typeLT (Z j) :=
        typeLT_le_of_strictMono (fun _ => ⟨PUnit.unit, hmem⟩) (fun _ _ h => (lt_irrefl _ h).elim)
      simpa [Ordinal.type_eq_one_of_unique] using hsub
    have hlt := hZ j
    rw [pow_zero] at hlt
    exact not_lt_of_ge h1 hlt
  | a + 1, r, Z, hZ => by
    let S : Fin r → Set ℕ := fun j =>
      { i : ℕ | (ω : Ordinal.{0}) ^ a ≤ typeLT ({ u : NatTuple a | toLex (i, u) ∈ Z j } : Set _) }
    have hSfin : ∀ j, (S j).Finite := by
      intro j
      by_contra hinf
      have hSinf : (S j).Infinite := hinf
      let p : ℕ → ℕ := Nat.nth (· ∈ S j)
      have hp_mono : StrictMono p := Nat.nth_strictMono hSinf
      have hp_mem : ∀ k, p k ∈ S j := fun k => Nat.nth_mem_of_infinite hSinf k
      have hφ : ∀ k, Nonempty (((· < ·) : NatTuple a → _ → Prop) ↪r
          ((· < ·) : ({ u : NatTuple a | toLex (p k, u) ∈ Z j } : Set _) → _ → Prop)) := by
        intro k
        have hle : typeLT (NatTuple a) ≤
            typeLT ({ u : NatTuple a | toLex (p k, u) ∈ Z j } : Set _) := by
          rw [typeLT_natTuple]
          exact hp_mem k
        exact Ordinal.type_le_iff'.1 hle
      let φ : ∀ k, ((· < ·) : NatTuple a → _ → Prop) ↪r
          ((· < ·) : ({ u : NatTuple a | toLex (p k, u) ∈ Z j } : Set _) → _ → Prop) :=
        fun k => Classical.choice (hφ k)
      let F : NatTuple (a + 1) → Z j := fun x =>
        ⟨toLex (p (ofLex x).1, (φ (ofLex x).1 (ofLex x).2).1),
         (φ (ofLex x).1 (ofLex x).2).2⟩
      have hF_mono : StrictMono F := by
        intro x y hxy
        change toLex (p (ofLex x).1, (φ (ofLex x).1 (ofLex x).2).1) <
          toLex (p (ofLex y).1, (φ (ofLex y).1 (ofLex y).2).1)
        rw [Prod.Lex.lt_iff] at hxy ⊢
        rcases hxy with hlt | ⟨heq, hlt⟩
        · exact Or.inl (hp_mono hlt)
        · refine Or.inr ⟨congrArg p heq, ?_⟩
          revert hlt
          rw [heq]
          intro hlt
          exact (φ (ofLex y).1).map_rel_iff.mpr hlt
      have hle : (ω : Ordinal.{0}) ^ (a + 1) ≤ typeLT (Z j) := by
        rw [← typeLT_natTuple (a + 1)]
        exact typeLT_le_of_strictMono F hF_mono
      exact not_lt_of_ge hle (hZ j)
    have hUfin : (⋃ j : Fin r, S j).Finite := Set.finite_iUnion hSfin
    obtain ⟨i, _, hi⟩ := (Set.infinite_univ.sdiff hUfin).nonempty
    have hlt_a : ∀ j : Fin r,
        typeLT ({ u : NatTuple a | toLex (i, u) ∈ Z j } : Set _) < (ω : Ordinal.{0}) ^ a := by
      intro j
      by_contra hge
      exact hi (Set.mem_iUnion.mpr ⟨j, not_lt.mp hge⟩)
    obtain ⟨u, hu⟩ := exists_not_mem_of_typeLT_lt a (fun j => { u | toLex (i, u) ∈ Z j }) hlt_a
    exact ⟨toLex (i, u), hu⟩

private lemma nat_pair_strictMono_right (a : ℕ) : StrictMono (Nat.pair a) := by
  intro k₁ k₂ hk
  simp only [Nat.pair]
  split_ifs with h1 h2 h2
  · nlinarith
  · omega
  · nlinarith
  · omega

private lemma one_lt_omega_pow {A : ℕ} (hA : 1 ≤ A) : (1 : Ordinal.{0}) < (ω : Ordinal.{0}) ^ A := by
  calc (1 : Ordinal.{0}) < ω := by simp
    _ = ω ^ (1 : ℕ) := (pow_one _).symm
    _ ≤ ω ^ A := by
      have h1 : (1 : Ordinal.{0}) ≤ ω := le_of_lt (by simp)
      exact pow_le_pow_right₀ h1 hA

private lemma ramsey_natTuple (n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, 1 ≤ m →
      ∀ (R B : SimpleGraph (NatTuple ((n - 1) * (m - 1) + 1))), IsCompl R B →
        (∃ s : Set (NatTuple ((n - 1) * (m - 1) + 1)), R.IsClique s ∧ typeLT s = (ω : Ordinal.{0}) ^ n) ∨
        (∃ s : Finset (NatTuple ((n - 1) * (m - 1) + 1)), B.IsClique (s : Set _) ∧ s.card = m) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ R B hcomp
    by_cases hm0 : m = 0
    · subst hm0
      right
      have hne : Nonempty (NatTuple ((n - 1) * 0 + 1)) := by
        simp only [mul_zero, zero_add]
        exact ⟨toLex (0, PUnit.unit)⟩
      obtain ⟨x⟩ := hne
      exact ⟨{x}, by simp [SimpleGraph.IsClique], by simp⟩
    by_cases hm1 : m = 1
    · subst hm1
      by_cases hblue : ∃ x y, B.Adj x y
      · right
        obtain ⟨x, y, hxy⟩ := hblue
        have hne : x ≠ y := B.ne_of_adj hxy
        refine ⟨{x, y}, ?_, by rw [Finset.card_pair hne]⟩
        intro u hu v hv huv
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact (huv rfl).elim
        · exact hxy
        · exact hxy.symm
        · exact (huv rfl).elim
      · left
        push Not at hblue
        refine ⟨Set.univ, ?_, ?_⟩
        · intro x _ y _ hxy
          have htop : (R ⊔ B).Adj x y := by
            rw [hcomp.codisjoint.eq_top]
            exact hxy
          exact htop.resolve_right (hblue x y)
        · have heq : (n - 1) * 1 + 1 = n := by omega
          have e : ((· < ·) : ↥(Set.univ : Set (NatTuple ((n - 1) * 1 + 1))) → _ → Prop) ≃r
              ((· < ·) : NatTuple ((n - 1) * 1 + 1) → _ → Prop) :=
            { toEquiv := Equiv.Set.univ _
              map_rel_iff' := by intro _ _; rfl }
          rw [e.ordinalType_congr, typeLT_natTuple, heq]
    have hm_ge : 1 ≤ m := by omega
    set A := (n - 1) * (m - 1) + 1 with hA_def
    have hA1 : 1 ≤ A := by omega
    have hE : (n - 1) * m + 1 = A + (n - 1) := by
      have : (n - 1) * m = (n - 1) * (m - 1) + (n - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        ring
      omega
    by_contra hno
    push Not at hno
    obtain ⟨hnoR, hnoB⟩ := hno
    have hNB_lt : ∀ x : NatTuple ((n - 1) * m + 1),
        typeLT ({ y | B.Adj x y } : Set _) < (ω : Ordinal.{0}) ^ A := by
      intro x
      by_contra hge
      have hle : typeLT (NatTuple A) ≤ typeLT ({ y | B.Adj x y } : Set _) := by
        rw [typeLT_natTuple]
        exact not_lt.mp hge
      obtain ⟨emb⟩ := Ordinal.type_le_iff'.1 hle
      let f : NatTuple A → NatTuple ((n - 1) * m + 1) := fun a => (emb a).1
      have hf_mono : StrictMono f := fun a b hab => emb.map_rel_iff.mpr hab
      have hf_adj : ∀ a, B.Adj x (f a) := fun a => (emb a).2
      let R' : SimpleGraph (NatTuple A) := R.comap f
      let B' : SimpleGraph (NatTuple A) := B.comap f
      have hcomp' : IsCompl R' B' := by
        refine ⟨?_, ?_⟩
        · rw [disjoint_iff]
          ext a b
          simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and, R', B',
            SimpleGraph.comap_adj]
          intro hr hb
          have hbot : (R ⊓ B).Adj (f a) (f b) := ⟨hr, hb⟩
          rw [hcomp.disjoint.eq_bot] at hbot
          exact hbot
        · rw [codisjoint_iff]
          ext a b
          simp only [SimpleGraph.sup_adj, SimpleGraph.top_adj, R', B', SimpleGraph.comap_adj]
          constructor
          · rintro (hr | hb)
            · exact fun h => R.loopless.irrefl _ (h ▸ hr)
            · exact fun h => B.loopless.irrefl _ (h ▸ hb)
          · intro hne
            have htop : (R ⊔ B).Adj (f a) (f b) := by
              rw [hcomp.codisjoint.eq_top]
              exact hf_mono.injective.ne hne
            exact htop
      rcases ih hm_ge R' B' hcomp' with ⟨s, hsR, hstype⟩ | ⟨s, hsB, hscard⟩
      · refine hnoR (f '' s) ?_ ?_
        · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
          exact hsR ha hb (fun h => hne (congrArg f h))
        · let iso : ((· < ·) : s → s → Prop) ≃r ((· < ·) : (f '' s) → (f '' s) → Prop) :=
            { toEquiv := Equiv.ofBijective (fun a => ⟨f a.1, a.1, a.2, rfl⟩)
                ⟨fun a b h => Subtype.ext (hf_mono.injective (by simpa using congrArg Subtype.val h)),
                 fun ⟨_, a, ha, hfa⟩ => ⟨⟨a, ha⟩, Subtype.ext hfa⟩⟩
              map_rel_iff' := by intro _ _; exact hf_mono.lt_iff_lt }
          exact iso.symm.ordinalType_congr.trans hstype
      · have hx_not : x ∉ s.image f := by
          intro hxmem
          rcases Finset.mem_image.mp hxmem with ⟨a, _, ha⟩
          exact B.loopless.irrefl x (ha ▸ hf_adj a)
        refine hnoB (insert x (s.image f)) ?_ ?_
        · intro u hu v hv huv
          simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff,
            Set.mem_image] at hu hv
          rcases hu with rfl | ⟨a, ha, rfl⟩ <;> rcases hv with rfl | ⟨b, hb, rfl⟩
          · exact (huv rfl).elim
          · exact hf_adj b
          · exact (hf_adj a).symm
          · exact hsB ha hb (fun h => huv (congrArg f h))
        · rw [Finset.card_insert_of_notMem hx_not, Finset.card_image_of_injective s hf_mono.injective,
            hscard]
    -- Decompose `NatTuple ((n - 1) * m + 1)` as `NatTuple (n - 1) ×ₗ NatTuple A`.
    have htype_split :
        typeLT (NatTuple (n - 1) ×ₗ NatTuple A) = typeLT (NatTuple ((n - 1) * m + 1)) := by
      rw [typeLT_prodLex, typeLT_natTuple, typeLT_natTuple, typeLT_natTuple, ← pow_add, hE]
    obtain ⟨eSplit⟩ := Ordinal.type_eq.mp htype_split
    obtain ⟨enc, henc⟩ := Countable.exists_injective_nat (NatTuple (n - 1))
    let blockOf (t : ℕ) : NatTuple (n - 1) :=
      if h : (Nat.unpair t).1 ∈ Set.range enc then Classical.choose h
      else Classical.choice (by
        clear h
        induction (n - 1) with
        | zero => exact ⟨PUnit.unit⟩
        | succ k ihk => exact ⟨toLex (0, Classical.choice ihk)⟩)
    have hblockOf_eq : ∀ i k, blockOf (Nat.pair (enc i) k) = i := by
      intro i k
      have hmem : (Nat.unpair (Nat.pair (enc i) k)).1 ∈ Set.range enc := by
        rw [Nat.unpair_pair]
        exact ⟨i, rfl⟩
      dsimp only [blockOf]
      rw [dif_pos hmem]
      apply henc
      have hspec := Classical.choose_spec hmem
      exact hspec.trans (by rw [Nat.unpair_pair])
    -- Step lemma: given `f : Fin t → NatTuple A`, pick next `y : NatTuple A` in block `blockOf t`
    have hstep : ∀ (t : ℕ) (f : Fin t → NatTuple A),
        ∃ y : NatTuple A,
          (∀ s : Fin t, R.Adj (eSplit (toLex (blockOf s.1, f s)))
            (eSplit (toLex (blockOf t, y)))) ∧
          (∀ s : Fin t, blockOf s.1 = blockOf t → f s < y) := by
      intro t f
      let bt := blockOf t
      let Z : Fin (4 * t) → Set (NatTuple A) := fun idx =>
        let s : Fin t := ⟨idx.1 / 4, by omega⟩
        match idx.1 % 4 with
        | 0 => { y | B.Adj (eSplit (toLex (blockOf s.1, f s))) (eSplit (toLex (bt, y))) }
        | 1 => { y | eSplit (toLex (blockOf s.1, f s)) = eSplit (toLex (bt, y)) }
        | 2 => if blockOf s.1 = bt then { y | y < f s } else ∅
        | _ => { y | y = f s }
      have hZ_lt : ∀ idx : Fin (4 * t), typeLT (Z idx) < (ω : Ordinal.{0}) ^ A := by
        intro idx
        let s : Fin t := ⟨idx.1 / 4, by omega⟩
        have hm4 : idx.1 % 4 = 0 ∨ idx.1 % 4 = 1 ∨ idx.1 % 4 = 2 ∨ idx.1 % 4 = 3 := by omega
        rcases hm4 with h0 | h1 | h2 | h3
        · have hEq : Z idx = { y | B.Adj (eSplit (toLex (blockOf s.1, f s)))
              (eSplit (toLex (bt, y))) } := by simp [Z, s, h0]
          refine lt_of_eq_of_lt (congrArg (fun S : Set (NatTuple A) => typeLT S) hEq) ?_
          let emb : ({ y : NatTuple A | B.Adj (eSplit (toLex (blockOf s.1, f s)))
              (eSplit (toLex (bt, y))) } : Set _) →
              ({ z | B.Adj (eSplit (toLex (blockOf s.1, f s))) z } : Set _) :=
            fun y => ⟨eSplit (toLex (bt, y.1)), y.2⟩
          have hemb : StrictMono emb := by
            intro y₁ y₂ hy
            exact eSplit.map_rel_iff.mpr (Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hy⟩))
          exact lt_of_le_of_lt (typeLT_le_of_strictMono emb hemb)
            (hNB_lt (eSplit (toLex (blockOf s.1, f s))))
        · have hEq : Z idx = { y | eSplit (toLex (blockOf s.1, f s)) = eSplit (toLex (bt, y)) } := by
            simp [Z, s, h1]
          refine lt_of_eq_of_lt (congrArg (fun S : Set (NatTuple A) => typeLT S) hEq) ?_
          refine lt_of_le_of_lt (typeLT_subsingleton_le_one _ ?_) (one_lt_omega_pow hA1)
          intro y₁ hy₁ y₂ hy₂
          have h := eSplit.injective (hy₁.symm.trans hy₂)
          exact congrArg Prod.snd (toLex.injective h)
        · by_cases hbeq : blockOf s.1 = bt
          · have hEq : Z idx = { y | y < f s } := by simp [Z, s, h2, hbeq]
            refine lt_of_eq_of_lt (congrArg (fun S : Set (NatTuple A) => typeLT S) hEq) ?_
            have hlt : typeLT ({ y : NatTuple A | y < f s } : Set _) < typeLT (NatTuple A) := by
              refine Ordinal.type_lt_iff.mpr ⟨{
                toFun := Subtype.val
                inj' := Subtype.val_injective
                map_rel_iff' := by intro _ _; rfl
                top := f s
                mem_range_iff_rel' := by
                  intro y
                  simp }⟩
            rwa [typeLT_natTuple] at hlt
          · have hEq : Z idx = ∅ := by simp [Z, s, h2, hbeq]
            refine lt_of_eq_of_lt (congrArg (fun S : Set (NatTuple A) => typeLT S) hEq) ?_
            rw [Ordinal.type_eq_zero_of_empty]
            exact lt_trans zero_lt_one (one_lt_omega_pow hA1)
        · have hEq : Z idx = { y | y = f s } := by simp [Z, s, h3]
          refine lt_of_eq_of_lt (congrArg (fun S : Set (NatTuple A) => typeLT S) hEq) ?_
          refine lt_of_le_of_lt (typeLT_subsingleton_le_one _ ?_) (one_lt_omega_pow hA1)
          intro y₁ hy₁ y₂ hy₂
          exact hy₁.trans hy₂.symm
      obtain ⟨y, hy⟩ := exists_not_mem_of_typeLT_lt A Z hZ_lt
      refine ⟨y, fun s => ?_, fun s hbeq => ?_⟩
      · have hnotB : ¬ B.Adj (eSplit (toLex (blockOf s.1, f s))) (eSplit (toLex (bt, y))) := by
          have := hy ⟨4 * s.1, by omega⟩
          simpa [Z, show (4 * s.1) / 4 = s.1 by omega] using this
        have hne : eSplit (toLex (blockOf s.1, f s)) ≠ eSplit (toLex (bt, y)) := by
          have := hy ⟨4 * s.1 + 1, by omega⟩
          simpa [Z, show (4 * s.1 + 1) / 4 = s.1 by omega,
            show (4 * s.1 + 1) % 4 = 1 by omega] using this
        have htop : (R ⊔ B).Adj (eSplit (toLex (blockOf s.1, f s))) (eSplit (toLex (bt, y))) := by
          rw [hcomp.codisjoint.eq_top]
          exact hne
        exact htop.resolve_right hnotB
      · have hnotlt : ¬ y < f s := by
          have := hy ⟨4 * s.1 + 2, by omega⟩
          have hbeq' : blockOf s.1 = bt := hbeq
          simpa [Z, show (4 * s.1 + 2) / 4 = s.1 by omega,
            show (4 * s.1 + 2) % 4 = 2 by omega, hbeq'] using this
        have hneq : y ≠ f s := by
          have := hy ⟨4 * s.1 + 3, by omega⟩
          simpa [Z, show (4 * s.1 + 3) / 4 = s.1 by omega,
            show (4 * s.1 + 3) % 4 = 3 by omega] using this
        exact lt_of_le_of_ne (not_lt.mp hnotlt) hneq.symm
    -- Build the infinite sequence `F : ℕ → NatTuple A` by prefix recursion
    let build : ∀ t : ℕ, { f : Fin t → NatTuple A //
        (∀ s₁ s₂ : Fin t, s₁ < s₂ → R.Adj (eSplit (toLex (blockOf s₁.1, f s₁)))
          (eSplit (toLex (blockOf s₂.1, f s₂)))) ∧
        (∀ s₁ s₂ : Fin t, s₁ < s₂ → blockOf s₁.1 = blockOf s₂.1 → f s₁ < f s₂) } :=
      Nat.rec ⟨Fin.elim0, fun s => s.elim0, fun s => s.elim0⟩ fun t prev =>
        let y := Classical.choose (hstep t prev.1)
        let hy := Classical.choose_spec (hstep t prev.1)
        ⟨Fin.snoc prev.1 y,
          by
            intro s₁ s₂
            refine Fin.lastCases ?_ (fun s₂' => ?_) s₂
            · refine Fin.lastCases ?_ (fun s₁' => ?_) s₁
              · intro hs; exact (lt_irrefl _ hs).elim
              · intro _
                simp only [Fin.snoc_last, Fin.snoc_castSucc]
                exact hy.1 s₁'
            · refine Fin.lastCases ?_ (fun s₁' => ?_) s₁
              · intro hs; exact (not_lt_of_ge (Fin.le_last _) hs).elim
              · intro hs
                simp only [Fin.snoc_castSucc]
                exact prev.2.1 s₁' s₂' (Fin.castSucc_lt_castSucc_iff.mp hs),
          by
            intro s₁ s₂
            refine Fin.lastCases ?_ (fun s₂' => ?_) s₂
            · refine Fin.lastCases ?_ (fun s₁' => ?_) s₁
              · intro hs _; exact (lt_irrefl _ hs).elim
              · intro _ hbeq
                simp only [Fin.snoc_last, Fin.snoc_castSucc] at hbeq ⊢
                exact hy.2 s₁' hbeq
            · refine Fin.lastCases ?_ (fun s₁' => ?_) s₁
              · intro hs _; exact (not_lt_of_ge (Fin.le_last _) hs).elim
              · intro hs hbeq
                simp only [Fin.snoc_castSucc] at hbeq ⊢
                exact prev.2.2 s₁' s₂' (Fin.castSucc_lt_castSucc_iff.mp hs) hbeq⟩
    have hagree : ∀ (t : ℕ) (i : Fin t), (build (t + 1)).1 i.castSucc = (build t).1 i := by
      intro t i
      dsimp only [build]
      exact Fin.snoc_castSucc _ _ i
    have hagree_le : ∀ {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) (i : Fin t₁),
        (build t₂).1 (Fin.castLE h i) = (build t₁).1 i := by
      intro t₁ t₂ h
      induction t₂, h using Nat.le_induction with
      | base => intro i; rfl
      | succ t₂ h ih' => intro i; exact (hagree t₂ (Fin.castLE h i)).trans (ih' i)
    let F : ℕ → NatTuple A := fun t => (build (t + 1)).1 (Fin.last t)
    have hF_red : ∀ t₁ t₂, t₁ < t₂ →
        R.Adj (eSplit (toLex (blockOf t₁, F t₁))) (eSplit (toLex (blockOf t₂, F t₂))) := by
      intro t₁ t₂ hlt
      have h1 : F t₁ = (build (t₂ + 1)).1 ⟨t₁, by omega⟩ :=
        (hagree_le (by omega : t₁ + 1 ≤ t₂ + 1) (Fin.last t₁)).symm
      rw [h1]
      exact (build (t₂ + 1)).2.1 ⟨t₁, by omega⟩ (Fin.last t₂) (Fin.mk_lt_mk.mpr hlt)
    have hF_mono : ∀ t₁ t₂, t₁ < t₂ → blockOf t₁ = blockOf t₂ → F t₁ < F t₂ := by
      intro t₁ t₂ hlt hbeq
      have h1 : F t₁ = (build (t₂ + 1)).1 ⟨t₁, by omega⟩ :=
        (hagree_le (by omega : t₁ + 1 ≤ t₂ + 1) (Fin.last t₁)).symm
      rw [h1]
      exact (build (t₂ + 1)).2.2 ⟨t₁, by omega⟩ (Fin.last t₂) (Fin.mk_lt_mk.mpr hlt) hbeq
    let G : (NatTuple (n - 1) ×ₗ ℕ) → NatTuple ((n - 1) * m + 1) :=
      fun p => eSplit (toLex ((ofLex p).1, F (Nat.pair (enc (ofLex p).1) (ofLex p).2)))
    have hG_mono : StrictMono G := by
      intro p q hpq
      dsimp only [G]
      apply eSplit.map_rel_iff.mpr
      rw [Prod.Lex.lt_iff] at hpq ⊢
      rcases hpq with hlt | ⟨heq, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨heq, ?_⟩
        rw [heq]
        exact hF_mono _ _ (nat_pair_strictMono_right (enc (ofLex q).1) hlt)
          (by rw [hblockOf_eq, hblockOf_eq])
    refine hnoR (Set.range G) ?_ ?_
    · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hne
      have hpair_ne : Nat.pair (enc (ofLex p).1) (ofLex p).2 ≠
          Nat.pair (enc (ofLex q).1) (ofLex q).2 := by
        intro hpeq
        have hu := congrArg Nat.unpair hpeq
        simp only [Nat.unpair_pair] at hu
        have h1 : (ofLex p).1 = (ofLex q).1 := henc (Prod.mk.inj hu).1
        have h2 : (ofLex p).2 = (ofLex q).2 := (Prod.mk.inj hu).2
        have hpq : p = q := ofLex.injective (Prod.ext h1 h2)
        exact hne (congrArg G hpq)
      rcases lt_or_gt_of_ne hpair_ne with hlt | hgt
      · have h := hF_red _ _ hlt
        simpa [G, hblockOf_eq] using h
      · have h := (hF_red _ _ hgt).symm
        simpa [G, hblockOf_eq] using h
    · have htype_dom : typeLT (NatTuple (n - 1) ×ₗ ℕ) = (ω : Ordinal.{0}) ^ n := by
        rw [typeLT_prodLex, Ordinal.type_nat_lt, typeLT_natTuple, ← pow_succ']
        congr 1; omega
      let iso : ((· < ·) : (NatTuple (n - 1) ×ₗ ℕ) → _ → Prop) ≃r
          ((· < ·) : Set.range G → _ → Prop) :=
        { toEquiv := Equiv.ofBijective (fun p => ⟨G p, p, rfl⟩)
            ⟨fun p q h => hG_mono.injective (congrArg Subtype.val h),
             fun ⟨_, p, hp⟩ => ⟨p, Subtype.ext hp⟩⟩
          map_rel_iff' := by intro _ _; exact hG_mono.lt_iff_lt }
      exact iso.symm.ordinalType_congr.trans htype_dom

/- ### Section 2: Nash-Williams Partition Theorem on Strictly Sorted Lists -/

private def StrictSorted (l : List ℕ) : Prop := l.Pairwise (· < ·)

private def ListAllIn (s : List ℕ) (B : Set ℕ) : Prop := ∀ x ∈ s, x ∈ B

private lemma mem_le_list_sum : ∀ {s : List ℕ} {a : ℕ}, a ∈ s → a ≤ s.sum
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · have := mem_le_list_sum h'; simp; omega

private lemma infinite_gt_nat {B : Set ℕ} (hB : B.Infinite) (x : ℕ) :
    { b ∈ B | x < b }.Infinite :=
  (hB.sdiff (Set.finite_le_nat x)).mono (fun _ h => ⟨h.1, not_le.mp h.2⟩)

private lemma infinite_gt_list {B : Set ℕ} (hB : B.Infinite) (s : List ℕ) :
    { b ∈ B | ∀ a ∈ s, a < b }.Infinite :=
  (infinite_gt_nat hB s.sum).mono fun _ h =>
    ⟨h.1, fun _ ha => lt_of_le_of_lt (mem_le_list_sum ha) h.2⟩

private def Accepts (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  ∃ t ∈ F, t <+: s ∨ ∃ u, t = s ++ u ∧ ListAllIn u B

private def StronglyAccepts (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  ∀ C, C ⊆ B → C.Infinite → Accepts F C s

private def Rejects (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  ¬ Accepts F B s

private def Decides (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  StronglyAccepts F B s ∨ Rejects F B s

private lemma accepts_mono {F : Set (List ℕ)} {B C : Set ℕ} {s : List ℕ}
    (hCB : C ⊆ B) (h : Accepts F C s) : Accepts F B s := by
  rcases h with ⟨t, htF, hpre | ⟨u, rfl, hu⟩⟩
  · exact ⟨t, htF, Or.inl hpre⟩
  · exact ⟨s ++ u, htF, Or.inr ⟨u, rfl, fun x hx => hCB (hu x hx)⟩⟩

private lemma decides_mono {F : Set (List ℕ)} {B C : Set ℕ} {s : List ℕ}
    (hCB : C ⊆ B) (h : Decides F B s) : Decides F C s := by
  rcases h with hsa | hrej
  · exact Or.inl fun D hDC hDinf => hsa D (hDC.trans hCB) hDinf
  · exact Or.inr fun hacc => hrej (accepts_mono hCB hacc)

private lemma exists_decides {F : Set (List ℕ)} {B : Set ℕ} (hB : B.Infinite) (s : List ℕ) :
    ∃ C, C ⊆ B ∧ C.Infinite ∧ Decides F C s := by
  by_cases hsa : StronglyAccepts F B s
  · exact ⟨B, Subset.rfl, hB, Or.inl hsa⟩
  · unfold StronglyAccepts at hsa
    push Not at hsa
    obtain ⟨C, hCB, hCinf, hrej⟩ := hsa
    exact ⟨C, hCB, hCinf, Or.inr hrej⟩

private lemma exists_decides_list {F : Set (List ℕ)} :
    ∀ (L : List (List ℕ)) {B : Set ℕ}, B.Infinite →
      ∃ C, C ⊆ B ∧ C.Infinite ∧ ∀ s ∈ L, Decides F C s
  | [], B, hB => ⟨B, Subset.rfl, hB, fun _ h => by simp at h⟩
  | s :: L, B, hB => by
    obtain ⟨C₁, hC₁B, hC₁inf, hdec⟩ := exists_decides (F := F) hB s
    obtain ⟨C₂, hC₂C₁, hC₂inf, hL⟩ := exists_decides_list L hC₁inf
    refine ⟨C₂, hC₂C₁.trans hC₁B, hC₂inf, fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | htL
    · exact decides_mono hC₂C₁ hdec
    · exact hL t htL

private lemma accepts_iff_tail {F : Set (List ℕ)} (hF : ∀ t ∈ F, StrictSorted t)
    {B : Set ℕ} {s : List ℕ} :
    Accepts F B s ↔ Accepts F { b ∈ B | ∀ a ∈ s, a < b } s := by
  constructor
  · rintro ⟨t, htF, hpre | ⟨u, rfl, hu⟩⟩
    · exact ⟨t, htF, Or.inl hpre⟩
    · refine ⟨s ++ u, htF, Or.inr ⟨u, rfl, fun x hx => ⟨hu x hx, fun a ha => ?_⟩⟩⟩
      exact (List.pairwise_append.mp (hF (s ++ u) htF)).2.2 a ha x hx
  · exact accepts_mono (fun _ h => h.1)

private lemma decides_of_tail {F : Set (List ℕ)} (hF : ∀ t ∈ F, StrictSorted t)
    {B C : Set ℕ} {s : List ℕ}
    (hsub : { b ∈ B | ∀ a ∈ s, a < b } ⊆ C) (hdec : Decides F C s) :
    Decides F B s := by
  rcases hdec with hsa | hrej
  · left
    intro D hDB hDinf
    have hDtail : { b ∈ D | ∀ a ∈ s, a < b }.Infinite := infinite_gt_list hDinf s
    have hacc := hsa { b ∈ D | ∀ a ∈ s, a < b }
      (fun x hx => hsub ⟨hDB hx.1, hx.2⟩) hDtail
    exact (accepts_iff_tail hF).mpr hacc
  · right
    intro hacc
    exact hrej (accepts_mono hsub ((accepts_iff_tail hF).mp hacc))

private lemma sublist_of_strictSorted_mem {s t : List ℕ}
    (hs : StrictSorted s) (ht : StrictSorted t) (hsub : ∀ x ∈ s, x ∈ t) :
    List.Sublist s t := by
  induction t generalizing s with
  | nil =>
    cases s with
    | nil => exact List.Sublist.slnil
    | cons a _ => exact absurd (hsub a (by simp)) (by simp)
  | cons b t' ih =>
    have hb_lt : ∀ y ∈ t', b < y := (List.pairwise_cons.mp ht).1
    have ht' : StrictSorted t' := (List.pairwise_cons.mp ht).2
    cases s with
    | nil => exact List.nil_sublist _
    | cons a s' =>
      have ha_lt : ∀ y ∈ s', a < y := (List.pairwise_cons.mp hs).1
      have hs' : StrictSorted s' := (List.pairwise_cons.mp hs).2
      have ha_mem : a = b ∨ a ∈ t' := by simpa using hsub a (by simp)
      rcases ha_mem with rfl | ha_t'
      · refine List.Sublist.cons_cons a (ih hs' ht' ?_)
        intro y hy
        have hy_mem : y = a ∨ y ∈ t' := by simpa using hsub y (by simp [hy])
        rcases hy_mem with rfl | hy'
        · exact absurd (ha_lt y hy) (lt_irrefl _)
        · exact hy'
      · refine List.Sublist.cons b (ih hs ht' ?_)
        intro y hy
        have hy_mem : y = b ∨ y ∈ t' := by simpa using hsub y hy
        rcases hy_mem with hyb | hy'
        · have hba : b < a := hb_lt a ha_t'
          rw [hyb] at hy
          rcases List.mem_cons.mp hy with h | hys'
          · exact absurd (h ▸ hba) (lt_irrefl _)
          · exact absurd (ha_lt b hys') (by omega)
        · exact hy'

private lemma nash_williams_diag {F : Set (List ℕ)} (hF : ∀ t ∈ F, StrictSorted t)
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ ∀ s, StrictSorted s → ListAllIn s B → Decides F B s := by
  obtain ⟨A₀, hA₀A, hA₀inf, hA₀dec⟩ := exists_decides (F := F) hA []
  let step : { p : List ℕ × Set ℕ //
      StrictSorted p.1 ∧ ListAllIn p.1 A ∧ p.2 ⊆ A ∧ p.2.Infinite ∧
      (∀ a ∈ p.1, ∀ b ∈ p.2, a < b) ∧ (∀ s ∈ p.1.sublists, Decides F p.2 s) } →
      { p : List ℕ × Set ℕ //
      StrictSorted p.1 ∧ ListAllIn p.1 A ∧ p.2 ⊆ A ∧ p.2.Infinite ∧
      (∀ a ∈ p.1, ∀ b ∈ p.2, a < b) ∧ (∀ s ∈ p.1.sublists, Decides F p.2 s) } := fun cur =>
    let x := Nat.nth (· ∈ cur.1.2) 0
    have hx_mem : x ∈ cur.1.2 := Nat.nth_mem_of_infinite cur.2.2.2.2.1 0
    let s' := cur.1.1 ++ [x]
    have htail_inf : { b ∈ cur.1.2 | x < b }.Infinite :=
      infinite_gt_nat cur.2.2.2.2.1 x
    let ex := exists_decides_list (F := F) s'.sublists htail_inf
    let C := Classical.choose ex
    let hC := Classical.choose_spec ex
    ⟨(s', C),
      by
        refine List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact cur.2.2.2.2.2.1 a ha x hx_mem,
      fun y hy => by
        rcases List.mem_append.mp hy with h1 | h2
        · exact cur.2.2.1 y h1
        · simp only [List.mem_singleton] at h2; subst h2; exact cur.2.2.2.1 hx_mem,
      fun y hy => cur.2.2.2.1 (hC.1 hy).1,
      hC.2.1,
      fun a ha b hb => by
        rcases List.mem_append.mp ha with h1 | h2
        · exact lt_trans (cur.2.2.2.2.2.1 a h1 x hx_mem) (hC.1 hb).2
        · simp only [List.mem_singleton] at h2; subst h2; exact (hC.1 hb).2,
      hC.2.2⟩
  let seq : ℕ → { p : List ℕ × Set ℕ //
      StrictSorted p.1 ∧ ListAllIn p.1 A ∧ p.2 ⊆ A ∧ p.2.Infinite ∧
      (∀ a ∈ p.1, ∀ b ∈ p.2, a < b) ∧ (∀ s ∈ p.1.sublists, Decides F p.2 s) } :=
    Nat.rec ⟨([], A₀), List.Pairwise.nil, fun _ h => by simp at h, hA₀A, hA₀inf,
      fun _ h => by simp at h, fun s hs => by
        have : s = [] := by simpa using hs
        subst this; exact hA₀dec⟩ (fun _ cur => step cur)
  have hlen : ∀ n, (seq n).1.1.length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show ((seq n).1.1 ++ [_]).length = n + 1
      simp [ih]
  have hpref : ∀ n, (seq n).1.1 <+: (seq (n + 1)).1.1 := fun n => ⟨[_], rfl⟩
  have hpref_le : ∀ {m n}, m ≤ n → (seq m).1.1 <+: (seq n).1.1 := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ n _ ih => exact ih.trans (hpref n)
  have hA_anti : ∀ n, (seq (n + 1)).1.2 ⊆ (seq n).1.2 := by
    intro n y hy
    let cur := seq n
    let x := Nat.nth (· ∈ cur.1.2) 0
    have htail_inf : { b ∈ cur.1.2 | x < b }.Infinite :=
      infinite_gt_nat cur.2.2.2.2.1 x
    have hC := Classical.choose_spec
      (exists_decides_list (F := F) (cur.1.1 ++ [x]).sublists htail_inf)
    exact (hC.1 hy).1
  have hA_anti_le : ∀ {m n}, m ≤ n → (seq n).1.2 ⊆ (seq m).1.2 := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => exact Subset.rfl
    | succ n _ ih => exact (hA_anti n).trans ih
  let xseq : ℕ → ℕ := fun n => Nat.nth (· ∈ (seq n).1.2) 0
  have hx_in_next : ∀ n, (seq (n + 1)).1.1 = (seq n).1.1 ++ [xseq n] := fun _ => rfl
  have hx_mem_A : ∀ n, xseq n ∈ (seq n).1.2 := fun n =>
    Nat.nth_mem_of_infinite (seq n).2.2.2.2.1 0
  have hx_mono : StrictMono xseq := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have h1 : xseq n ∈ (seq (n + 1)).1.1 := by rw [hx_in_next]; simp
    exact (seq (n + 1)).2.2.2.2.2.1 (xseq n) h1 (xseq (n + 1)) (hx_mem_A (n + 1))
  have hseq_mem_iff : ∀ n y, y ∈ (seq n).1.1 ↔ ∃ k < n, xseq k = y := by
    intro n
    induction n with
    | zero => intro y; simp [seq]
    | succ n ih =>
      intro y
      rw [hx_in_next, List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨k, hk, rfl⟩ | rfl)
        · exact ⟨k, by omega, rfl⟩
        · exact ⟨n, by omega, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        by_cases hkn : k < n
        · exact Or.inl ⟨k, hkn, rfl⟩
        · have : k = n := by omega
          subst this; exact Or.inr rfl
  let B : Set ℕ := Set.range xseq
  have hB_sub_A : B ⊆ A := by
    rintro _ ⟨n, rfl⟩
    exact (seq n).2.2.2.1 (hx_mem_A n)
  have hB_inf : B.Infinite := Set.infinite_range_of_injective hx_mono.injective
  refine ⟨B, hB_sub_A, hB_inf, fun s hs_sort hs_B => ?_⟩
  by_cases hs_nil : s = []
  · subst hs_nil
    refine decides_of_tail hF (C := (seq 0).1.2) ?_ ((seq 0).2.2.2.2.2.2 [] (by simp))
    rintro _ ⟨⟨k, rfl⟩, _⟩
    exact hA_anti_le (Nat.zero_le k) (hx_mem_A k)
  · have hlast_mem : s.getLast hs_nil ∈ s := List.getLast_mem hs_nil
    obtain ⟨m, hm⟩ := hs_B _ hlast_mem
    have hs_in_seq : ∀ y ∈ s, y ∈ (seq (m + 1)).1.1 := by
      intro y hy
      obtain ⟨k, rfl⟩ := hs_B y hy
      have hkle : k ≤ m := by
        have hle_last : xseq k ≤ s.getLast hs_nil := by
          have : ∀ {L : List ℕ} (hne : L ≠ []), StrictSorted L → ∀ a ∈ L, a ≤ L.getLast hne := by
            intro L
            induction L with
            | nil => intro hne; exact absurd rfl hne
            | cons a t ihL =>
              intro _ hst x hx
              cases t with
              | nil =>
                simp only [List.mem_singleton] at hx
                simp [hx]
              | cons b t' =>
                have hab : a < b := (List.pairwise_cons.mp hst).1 b (by simp)
                have hst' : StrictSorted (b :: t') := (List.pairwise_cons.mp hst).2
                have hgl : (a :: b :: t').getLast (List.cons_ne_nil _ _) =
                    (b :: t').getLast (List.cons_ne_nil _ _) := rfl
                rw [hgl]
                rcases List.mem_cons.mp hx with rfl | hxt
                · exact le_trans (le_of_lt hab) (ihL _ hst' b (by simp))
                · exact ihL _ hst' x hxt
          exact this hs_nil hs_sort (xseq k) hy
        rw [← hm] at hle_last
        exact hx_mono.le_iff_le.mp hle_last
      exact (hseq_mem_iff (m + 1) (xseq k)).mpr ⟨k, by omega, rfl⟩
    have hsublist : s ∈ (seq (m + 1)).1.1.sublists :=
      List.mem_sublists.mpr (sublist_of_strictSorted_mem hs_sort (seq (m + 1)).2.1 hs_in_seq)
    refine decides_of_tail hF (C := (seq (m + 1)).1.2) ?_
      ((seq (m + 1)).2.2.2.2.2.2 s hsublist)
    rintro _ ⟨⟨k, rfl⟩, hgt⟩
    have hmk : m + 1 ≤ k := by
      have hlt : xseq m < xseq k := hm ▸ hgt _ hlast_mem
      have := hx_mono.lt_iff_lt.mp hlt
      omega
    exact hA_anti_le hmk (hx_mem_A k)

private lemma nash_williams_finite_bad {F : Set (List ℕ)} {B : Set ℕ} {s : List ℕ}
    (hsa : StronglyAccepts F B s) :
    { n ∈ B | (∀ a ∈ s, a < n) ∧ Rejects F B (s ++ [n]) }.Finite := by
  by_contra hinf
  let C := { n ∈ B | (∀ a ∈ s, a < n) ∧ Rejects F B (s ++ [n]) }
  have hCinf : C.Infinite := hinf
  have hCB : C ⊆ B := fun _ h => h.1
  obtain ⟨t, htF, hpre | ⟨u, rfl, hu⟩⟩ := hsa C hCB hCinf
  · obtain ⟨n, hn⟩ := hCinf.nonempty
    exact hn.2.2 ⟨t, htF, Or.inl (hpre.trans ⟨[n], rfl⟩)⟩
  · cases u with
    | nil =>
      obtain ⟨n, hn⟩ := hCinf.nonempty
      simp only [List.append_nil] at htF
      exact hn.2.2 ⟨s, htF, Or.inl ⟨[n], rfl⟩⟩
    | cons n u' =>
      have hnC : n ∈ C := hu n (by simp)
      refine hnC.2.2 ⟨s ++ n :: u', htF, Or.inr ⟨u', by simp, fun x hx => hCB (hu x (by simp [hx]))⟩⟩

private theorem nash_williams (F : Set (List ℕ)) (hF_sort : ∀ s ∈ F, StrictSorted s)
    (hF_thin : ∀ s ∈ F, ∀ t ∈ F, s <+: t → s = t)
    (c : List ℕ → Bool) (A : Set ℕ) (hA : A.Infinite) :
    ∃ (b : Bool) (B : Set ℕ), B ⊆ A ∧ B.Infinite ∧
      ∀ s ∈ F, ListAllIn s B → c s = b := by
  let F₀ : Set (List ℕ) := { s ∈ F | c s = false }
  have hF₀_sort : ∀ s ∈ F₀, StrictSorted s := fun s hs => hF_sort s hs.1
  obtain ⟨B, hBA, hBinf, hBdec⟩ := nash_williams_diag hF₀_sort hA
  rcases hBdec [] List.Pairwise.nil (fun _ h => by simp at h) with hsa0 | hrej0
  · -- Strongly accepts `[]`: build infinite `H ⊆ B` where every strictly sorted `s ⊆ H` is strongly accepted
    let step : { L : List ℕ // StrictSorted L ∧ ListAllIn L B ∧
        ∀ s ∈ L.sublists, StronglyAccepts F₀ B s } →
        { L : List ℕ // StrictSorted L ∧ ListAllIn L B ∧
        ∀ s ∈ L.sublists, StronglyAccepts F₀ B s } := fun cur =>
      let bad : Set ℕ :=
        { n : ℕ | ¬ ∀ a ∈ cur.1, a < n } ∪
        ⋃ s ∈ cur.1.sublists, { n ∈ B | (∀ a ∈ s, a < n) ∧ Rejects F₀ B (s ++ [n]) }
      have hbad_fin : bad.Finite := by
        refine Set.Finite.union ?_ ?_
        · refine (Set.finite_le_nat cur.1.sum).subset fun n hn => ?_
          push Not at hn
          obtain ⟨a, ha, han⟩ := hn
          have ham := mem_le_list_sum ha
          show n ≤ cur.1.sum
          omega
        · refine (cur.1.sublists.finite_toSet).biUnion fun s hs =>
            nash_williams_finite_bad (cur.2.2.2 s hs)
      have hgood : (B \ bad).Nonempty := (hBinf.sdiff hbad_fin).nonempty
      let x := Classical.choose hgood
      have hx : x ∈ B ∧ x ∉ bad := Classical.choose_spec hgood
      have hx_gt : ∀ a ∈ cur.1, a < x := by
        by_contra h
        exact hx.2 (Or.inl h)
      ⟨cur.1 ++ [x],
        List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, fun a ha b hb => by
          simp only [List.mem_singleton] at hb; subst hb; exact hx_gt a ha⟩,
        fun y hy => by
          rcases List.mem_append.mp hy with h1 | h2
          · exact cur.2.2.1 y h1
          · simp only [List.mem_singleton] at h2; subst h2; exact hx.1,
        fun s hs => by
          have hsub : List.Sublist s (cur.1 ++ [x]) := List.mem_sublists.mp hs
          by_cases hx_in : x ∈ s
          · -- `x` is the last element of `s`, so `s = s' ++ [x]` with `s' <+ cur.1`
            have hs_sort : StrictSorted s :=
              (List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, fun a ha b hb => by
                simp only [List.mem_singleton] at hb; subst hb; exact hx_gt a ha⟩).sublist hsub
            have hs_ne : s ≠ [] := List.ne_nil_of_mem hx_in
            have hlast : s.getLast hs_ne = x := by
              have hle1 : x ≤ s.getLast hs_ne := by
                have hgl_mem : s.getLast hs_ne ∈ s := List.getLast_mem hs_ne
                have : ∀ {L : List ℕ} (hne : L ≠ []), StrictSorted L → ∀ a ∈ L, a ≤ L.getLast hne := by
                  intro L
                  induction L with
                  | nil => intro hne; exact absurd rfl hne
                  | cons a t ihL =>
                    intro _ hst u hu
                    cases t with
                    | nil => simp only [List.mem_singleton] at hu; simp [hu]
                    | cons b t' =>
                      have hab : a < b := (List.pairwise_cons.mp hst).1 b (by simp)
                      have hst' : StrictSorted (b :: t') := (List.pairwise_cons.mp hst).2
                      have hgl : (a :: b :: t').getLast (List.cons_ne_nil _ _) =
                          (b :: t').getLast (List.cons_ne_nil _ _) := rfl
                      rw [hgl]
                      rcases List.mem_cons.mp hu with rfl | hut
                      · exact le_trans (le_of_lt hab) (ihL _ hst' b (by simp))
                      · exact ihL _ hst' u hut
                exact this hs_ne hs_sort x hx_in
              have hle2 : s.getLast hs_ne ≤ x := by
                have hmem := hsub.subset (List.getLast_mem hs_ne)
                rcases List.mem_append.mp hmem with h1 | h2
                · exact le_of_lt (hx_gt _ h1)
                · simp only [List.mem_singleton] at h2; omega
              omega
            let s' := s.dropLast
            have hs_eq : s = s' ++ [x] := by
              rw [← hlast]
              exact (List.dropLast_append_getLast hs_ne).symm
            have hs'_lt : ∀ a ∈ s', a < x := by
              intro a ha
              have hp := List.pairwise_append.mp (hs_eq ▸ hs_sort)
              exact hp.2.2 a ha x (by simp)
            have hs'_sub : List.Sublist s' cur.1 := by
              refine sublist_of_strictSorted_mem (List.pairwise_append.mp (hs_eq ▸ hs_sort)).1 cur.2.1 ?_
              intro a ha
              have hmem := hsub.subset (hs_eq ▸ List.mem_append_left [x] ha)
              rcases List.mem_append.mp hmem with h1 | h2
              · exact h1
              · simp only [List.mem_singleton] at h2
                exact absurd (h2 ▸ hs'_lt a ha) (lt_irrefl _)
            have hs'_mem_sub : s' ∈ cur.1.sublists := List.mem_sublists.mpr hs'_sub
            have hdec_s := hBdec s hs_sort (fun y hy => by
              rcases List.mem_append.mp (hsub.subset hy) with h1 | h2
              · exact cur.2.2.1 y h1
              · simp only [List.mem_singleton] at h2; subst h2; exact hx.1)
            rcases hdec_s with hsa_s | hrej_s
            · exact hsa_s
            · exfalso
              apply hx.2
              right
              exact Set.mem_iUnion₂.mpr ⟨s', hs'_mem_sub, hx.1, hs'_lt, hs_eq ▸ hrej_s⟩
          · have hs_sub : List.Sublist s cur.1 := by
              have hs_sort : StrictSorted s :=
                (List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, fun a ha b hb => by
                  simp only [List.mem_singleton] at hb; subst hb; exact hx_gt a ha⟩).sublist hsub
              refine sublist_of_strictSorted_mem hs_sort cur.2.1 ?_
              intro a ha
              rcases List.mem_append.mp (hsub.subset ha) with h1 | h2
              · exact h1
              · simp only [List.mem_singleton] at h2
                exact absurd (h2 ▸ ha) hx_in
            exact cur.2.2.2 s (List.mem_sublists.mpr hs_sub)⟩
    let chain : ℕ → { L : List ℕ // StrictSorted L ∧ ListAllIn L B ∧
        ∀ s ∈ L.sublists, StronglyAccepts F₀ B s } :=
      Nat.rec ⟨[], List.Pairwise.nil, fun _ h => by simp at h, fun s hs => by
        have : s = [] := by simpa using hs
        subst this; exact hsa0⟩ (fun _ cur => step cur)
    have hlen : ∀ n, (chain n).1.length = n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        show ((chain n).1 ++ [_]).length = n + 1
        simp [ih]
    let H : Set ℕ := ⋃ n, { x | x ∈ (chain n).1 }
    have hH_sub_B : H ⊆ B := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
      exact (chain n).2.2.1 x hxn
    have hH_inf : H.Infinite := by
      intro hfin
      have hcard : ∀ n, n ≤ hfin.toFinset.card := by
        intro n
        have hsub : (chain n).1.toFinset ⊆ hfin.toFinset := by
          intro x hx
          rw [Set.Finite.mem_toFinset]
          exact Set.mem_iUnion.mpr ⟨n, List.mem_toFinset.mp hx⟩
        have hnodup : (chain n).1.Nodup := (chain n).2.1.imp ne_of_lt
        calc n = (chain n).1.length := (hlen n).symm
          _ = (chain n).1.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
          _ ≤ hfin.toFinset.card := Finset.card_le_card hsub
      exact absurd (hcard (hfin.toFinset.card + 1)) (by omega)
    have hchain_mono : ∀ {m n}, m ≤ n → ∀ x ∈ (chain m).1, x ∈ (chain n).1 := by
      intro m n h
      induction n, h using Nat.le_induction with
      | base => intro _ hx; exact hx
      | succ n _ ih =>
        intro x hx
        show x ∈ (chain n).1 ++ [_]
        exact List.mem_append_left _ (ih x hx)
    refine ⟨false, H, hH_sub_B.trans hBA, hH_inf, fun s hsF hsH => ?_⟩
    -- Find `N` containing all elements of `s`
    have hexN : ∀ {L : List ℕ}, ListAllIn L H → ∃ N, ∀ x ∈ L, x ∈ (chain N).1 := by
      intro L
      induction L with
      | nil => intro _; exact ⟨0, fun _ h => by simp at h⟩
      | cons a t ihL =>
        intro hL
        obtain ⟨n₁, hn₁⟩ := Set.mem_iUnion.mp (hL a (by simp))
        obtain ⟨n₂, hn₂⟩ := ihL (fun x hx => hL x (by simp [hx]))
        refine ⟨max n₁ n₂, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact hchain_mono (le_max_left n₁ n₂) _ hn₁
        · exact hchain_mono (le_max_right n₁ n₂) _ (hn₂ x hxt)
    obtain ⟨N, hN⟩ := hexN hsH
    have hs_sub : s ∈ (chain N).1.sublists :=
      List.mem_sublists.mpr (sublist_of_strictSorted_mem (hF_sort s hsF) (chain N).2.1 hN)
    have hsa_s := (chain N).2.2.2 s hs_sub
    obtain ⟨t, htF₀, hpre | ⟨u, rfl, _⟩⟩ := hsa_s B Subset.rfl hBinf
    · have hts : t = s := hF_thin t htF₀.1 s hsF hpre
      rw [← hts]
      exact htF₀.2
    · have hst : s = s ++ u := hF_thin s hsF (s ++ u) htF₀.1 ⟨u, rfl⟩
      rw [hst]
      exact htF₀.2
  · refine ⟨true, B, hBA, hBinf, fun s hsF hsB => ?_⟩
    by_contra hne
    have hfalse : c s = false := by cases h : c s <;> simp_all
    exact hrej0 ⟨s, ⟨hsF, hfalse⟩, Or.inr ⟨s, by simp, hsB⟩⟩

/- ### Section 3: Interaction Schemes, Deterministic Decoder, Lemma 3.11 & Lemma 3.6 -/

private def accLengths (acc : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | l :: ls => (acc + l.length) :: accLengths (acc + l.length) ls

private def interact : List (List ℕ) → List (List ℕ) → List ℕ
  | [], ys => ys.flatten
  | xs, [] => xs.flatten
  | x :: xs, y :: ys => x ++ y ++ interact xs ys

private lemma accLengths_length (acc : ℕ) (ls : List (List ℕ)) :
    (accLengths acc ls).length = ls.length := by
  induction ls generalizing acc with
  | nil => rfl
  | cons l ls ih => simp [accLengths, ih]

private def diffs (prev : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => (c - prev) :: diffs c cs

private lemma diffs_accLengths (acc : ℕ) (ls : List (List ℕ)) :
    diffs acc (accLengths acc ls) = ls.map List.length := by
  induction ls generalizing acc with
  | nil => rfl
  | cons l ls ih =>
    rw [accLengths, diffs, Nat.add_sub_cancel_left, ih]
    rfl

private lemma sum_map_length (ls : List (List ℕ)) :
    (ls.map List.length).sum = ls.flatten.length :=
  List.length_flatten.symm

private def deinteract : List ℕ → List ℕ → List ℕ → List ℕ × List ℕ
  | [], [], _ => ([], [])
  | [], lb :: lbs, rem => ([], rem.take (lb + lbs.sum))
  | la :: las, [], rem => (rem.take (la + las.sum), [])
  | la :: las, lb :: lbs, rem =>
    let a := rem.take la
    let r1 := rem.drop la
    let b := r1.take lb
    let r2 := r1.drop lb
    let p := deinteract las lbs r2
    (a ++ p.1, b ++ p.2)

private lemma deinteract_interact :
    ∀ (as bs : List (List ℕ)),
      deinteract (as.map List.length) (bs.map List.length) (interact as bs) =
        (as.flatten, bs.flatten)
  | [], [] => rfl
  | [], b :: bs => by
    simp only [List.map_nil, List.map_cons, interact, deinteract, List.flatten_nil,
      List.flatten_cons, Prod.mk.injEq, true_and]
    rw [sum_map_length, ← List.length_append, List.take_length]
  | a :: as, [] => by
    simp only [List.map_nil, List.map_cons, interact, deinteract, List.flatten_nil,
      List.flatten_cons, Prod.mk.injEq, and_true]
    rw [sum_map_length, ← List.length_append, List.take_length]
  | a :: as, b :: bs => by
    simp only [List.map_cons, interact, deinteract, List.flatten_cons]
    rw [List.append_assoc, List.take_left, List.drop_left, List.take_left, List.drop_left,
      deinteract_interact as bs]

private lemma interact_length :
    ∀ (as bs : List (List ℕ)), (interact as bs).length = as.flatten.length + bs.flatten.length
  | [], bs => by simp [interact]
  | a :: as, [] => by simp [interact]
  | a :: as, b :: bs => by
    simp only [interact, List.flatten_cons, List.length_append, interact_length as bs]
    omega

private def decodeForm (ka kb : ℕ) (zs : List ℕ) : List ℕ × List ℕ :=
  let c := zs.take ka
  let r1 := zs.drop ka
  match diffs 0 c with
  | [] => ([], [])
  | la :: las =>
    let a := r1.take la
    let r2 := r1.drop la
    let d := r2.take kb
    let r3 := r2.drop kb
    match diffs 0 d with
    | [] => ([], [])
    | lb :: lbs =>
      let b := r3.take lb
      let r4 := r3.drop lb
      let p := deinteract las lbs r4
      (a ++ p.1, b ++ p.2)

private def FormBody (ka kb : ℕ) (x y zs : List ℕ) : Prop :=
  ∃ (a : List ℕ) (as : List (List ℕ)) (b : List ℕ) (bs : List (List ℕ)),
    x.length < y.length ∧
    x = (a :: as).flatten ∧
    y = (b :: bs).flatten ∧
    (∀ u ∈ a :: as, u ≠ []) ∧
    (∀ v ∈ b :: bs, v ≠ []) ∧
    (a :: as).length = ka ∧
    (b :: bs).length = kb ∧
    zs = accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs ∧
    StrictSorted zs

private def kaOf (l : ℕ) : ℕ := l / 2 + 1
private def kbOf (l : ℕ) : ℕ := (l + 1) / 2

private lemma decodeForm_of_formBody {ka kb : ℕ} {x y zs : List ℕ}
    (h : FormBody ka kb x y zs) : decodeForm ka kb zs = (x, y) := by
  rcases h with ⟨a, as, b, bs, _, rfl, rfl, _, _, hka, hkb, rfl, _⟩
  have hclen : (accLengths 0 (a :: as)).length = ka := by rw [accLengths_length, hka]
  have hdlen : (accLengths 0 (b :: bs)).length = kb := by rw [accLengths_length, hkb]
  unfold decodeForm
  simp only [List.append_assoc]
  rw [← hclen, List.take_left, List.drop_left, diffs_accLengths, List.map_cons]
  dsimp only
  rw [List.take_left, List.drop_left, ← hdlen, List.take_left, List.drop_left,
    diffs_accLengths, List.map_cons]
  dsimp only
  rw [List.take_left, List.drop_left, deinteract_interact]
  simp

private lemma formBody_length {ka kb : ℕ} {x y zs : List ℕ}
    (h : FormBody ka kb x y zs) : zs.length = ka + kb + x.length + y.length := by
  rcases h with ⟨a, as, b, bs, _, rfl, rfl, _, _, hka, hkb, rfl, _⟩
  have hclen : (accLengths 0 (a :: as)).length = ka := by rw [accLengths_length, hka]
  have hdlen : (accLengths 0 (b :: bs)).length = kb := by rw [accLengths_length, hkb]
  simp only [List.length_append, hclen, hdlen, interact_length, List.flatten_cons]
  omega

private lemma schemes_thin (ka kb : ℕ) :
    ∀ zs ∈ { z | ∃ x y, FormBody ka kb x y z },
      ∀ zs' ∈ { z | ∃ x y, FormBody ka kb x y z },
        zs <+: zs' → zs = zs' := by
  rintro zs ⟨x, y, h1⟩ zs' ⟨x', y', h2⟩ hpre
  rcases h1 with ⟨a, as, b, bs, _, rfl, rfl, _, _, hka, hkb, rfl, _⟩
  rcases h2 with ⟨a', as', b', bs', _, rfl, rfl, _, _, hka', hkb', rfl, _⟩
  have hclen : (accLengths 0 (a :: as)).length = ka := by rw [accLengths_length, hka]
  have hclen' : (accLengths 0 (a' :: as')).length = ka := by rw [accLengths_length, hka']
  have hdlen : (accLengths 0 (b :: bs)).length = kb := by rw [accLengths_length, hkb]
  have hdlen' : (accLengths 0 (b' :: bs')).length = kb := by rw [accLengths_length, hkb']
  obtain ⟨rest, hrest⟩ := hpre
  have hc_eq : accLengths 0 (a :: as) = accLengths 0 (a' :: as') := by
    have htake := congrArg (List.take ka) hrest
    simp only [List.append_assoc] at htake
    rw [← hclen, List.take_left, hclen, ← hclen', List.take_left] at htake
    exact htake
  have hlenA_eq : (a :: as).map List.length = (a' :: as').map List.length := by
    rw [← diffs_accLengths 0 (a :: as), ← diffs_accLengths 0 (a' :: as'), hc_eq]
  have ha_len : a.length = a'.length := by
    have := congrArg List.head? hlenA_eq
    simpa using this
  have hx_len : (a :: as).flatten.length = (a' :: as').flatten.length := by
    rw [← sum_map_length, ← sum_map_length, hlenA_eq]
  have hd_eq : accLengths 0 (b :: bs) = accLengths 0 (b' :: bs') := by
    have hdrop := congrArg (fun l => (l.drop (ka + a.length)).take kb) hrest
    simp only [List.append_assoc] at hdrop
    have hL : ((accLengths 0 (a :: as) ++ (a ++ (accLengths 0 (b :: bs) ++
        (b ++ (interact as bs ++ rest))))).drop (ka + a.length)).take kb =
        accLengths 0 (b :: bs) := by
      rw [← List.append_assoc (accLengths 0 (a :: as)) a,
        show ka + a.length = (accLengths 0 (a :: as) ++ a).length by simp [hclen],
        List.drop_left, ← hdlen, List.take_left]
    have hR : ((accLengths 0 (a' :: as') ++ (a' ++ (accLengths 0 (b' :: bs') ++
        (b' ++ interact as' bs')))).drop (ka + a.length)).take kb =
        accLengths 0 (b' :: bs') := by
      rw [ha_len, ← List.append_assoc (accLengths 0 (a' :: as')) a',
        show ka + a'.length = (accLengths 0 (a' :: as') ++ a').length by simp [hclen'],
        List.drop_left, ← hdlen', List.take_left]
    rw [hL, hR] at hdrop
    exact hdrop
  have hlenB_eq : (b :: bs).map List.length = (b' :: bs').map List.length := by
    rw [← diffs_accLengths 0 (b :: bs), ← diffs_accLengths 0 (b' :: bs'), hd_eq]
  have hy_len : (b :: bs).flatten.length = (b' :: bs').flatten.length := by
    rw [← sum_map_length, ← sum_map_length, hlenB_eq]
  have htot : (accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs).length =
      (accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++ interact as' bs').length := by
    simp only [List.length_append, hclen, hclen', hdlen, hdlen', interact_length]
    simp only [List.flatten_cons, List.length_append] at hx_len hy_len
    omega
  have hrest_nil : rest = [] := by
    have hlen := congrArg List.length hrest
    rw [List.length_append, htot] at hlen
    exact List.eq_nil_of_length_eq_zero (by omega)
  simpa [hrest_nil] using hrest

private lemma larson_lemma_3_6 (g : List ℕ → List ℕ → Bool) :
    ∃ (e : ℕ → ℕ) (j : ℕ → Bool),
      StrictMono e ∧ 1 ≤ e 0 ∧
      ∀ l ≥ 1, ∀ x y zs, FormBody (kaOf l) (kbOf l) x y zs →
        (∀ u ∈ zs, e l < u ∧ u ∈ Set.range e) → g x y = j l := by
  let step : ℕ → { p : Set ℕ × Bool // p.1.Infinite } →
      { p : Set ℕ × Bool // p.1.Infinite } := fun k cur =>
    let x := Nat.nth (· ∈ cur.1.1) 0
    have htail : { y ∈ cur.1.1 | x < y }.Infinite := infinite_gt_nat cur.2 x
    let F : Set (List ℕ) := { z | ∃ a b, FormBody (kaOf (k + 1)) (kbOf (k + 1)) a b z }
    have hF_sort : ∀ z ∈ F, StrictSorted z := by
      rintro z ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hs⟩; exact hs
    have hF_thin : ∀ z ∈ F, ∀ z' ∈ F, z <+: z' → z = z' := schemes_thin _ _
    let col : List ℕ → Bool := fun z =>
      let p := decodeForm (kaOf (k + 1)) (kbOf (k + 1)) z
      g p.1 p.2
    let ex := nash_williams F hF_sort hF_thin col _ htail
    let b := Classical.choose ex
    let ex2 := Classical.choose_spec ex
    let B := Classical.choose ex2
    let hB := Classical.choose_spec ex2
    ⟨(B, b), hB.2.1⟩
  let startSet : Set ℕ := { n : ℕ | 1 ≤ n }
  have hstart_inf : startSet.Infinite :=
    (infinite_gt_nat Set.infinite_univ 0).mono (fun _ h => h.2)
  let seq : ℕ → { p : Set ℕ × Bool // p.1.Infinite } :=
    Nat.rec ⟨(startSet, false), hstart_inf⟩ (fun k cur => step k cur)
  let e : ℕ → ℕ := fun k => Nat.nth (· ∈ (seq k).1.1) 0
  let j : ℕ → Bool := fun k => (seq k).1.2
  have he_mem : ∀ k, e k ∈ (seq k).1.1 := fun k => Nat.nth_mem_of_infinite (seq k).2 0
  have hstep_sub : ∀ k, (seq (k + 1)).1.1 ⊆ { y ∈ (seq k).1.1 | e k < y } := by
    intro k
    let cur := seq k
    let x := Nat.nth (· ∈ cur.1.1) 0
    have htail : { y ∈ cur.1.1 | x < y }.Infinite := infinite_gt_nat cur.2 x
    let F : Set (List ℕ) := { z | ∃ a b, FormBody (kaOf (k + 1)) (kbOf (k + 1)) a b z }
    have hF_sort : ∀ z ∈ F, StrictSorted z := by
      rintro z ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hs⟩; exact hs
    have hF_thin : ∀ z ∈ F, ∀ z' ∈ F, z <+: z' → z = z' := schemes_thin _ _
    let col : List ℕ → Bool := fun z =>
      let p := decodeForm (kaOf (k + 1)) (kbOf (k + 1)) z
      g p.1 p.2
    have hB := Classical.choose_spec (Classical.choose_spec
      (nash_williams F hF_sort hF_thin col _ htail))
    exact hB.1
  have hstep_mono_col : ∀ k z,
      (∃ a b, FormBody (kaOf (k + 1)) (kbOf (k + 1)) a b z) →
      ListAllIn z (seq (k + 1)).1.1 →
      (let p := decodeForm (kaOf (k + 1)) (kbOf (k + 1)) z; g p.1 p.2) = j (k + 1) := by
    intro k z hzF hzB
    let cur := seq k
    let x := Nat.nth (· ∈ cur.1.1) 0
    have htail : { y ∈ cur.1.1 | x < y }.Infinite := infinite_gt_nat cur.2 x
    let F : Set (List ℕ) := { z | ∃ a b, FormBody (kaOf (k + 1)) (kbOf (k + 1)) a b z }
    have hF_sort : ∀ z ∈ F, StrictSorted z := by
      rintro z ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hs⟩; exact hs
    have hF_thin : ∀ z ∈ F, ∀ z' ∈ F, z <+: z' → z = z' := schemes_thin _ _
    let col : List ℕ → Bool := fun z =>
      let p := decodeForm (kaOf (k + 1)) (kbOf (k + 1)) z
      g p.1 p.2
    have hB := Classical.choose_spec (Classical.choose_spec
      (nash_williams F hF_sort hF_thin col _ htail))
    exact hB.2.2 z hzF hzB
  have hseq_anti : ∀ {m n}, m ≤ n → (seq n).1.1 ⊆ (seq m).1.1 := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => exact Subset.rfl
    | succ n _ ih => exact Set.Subset.trans (fun y hy => (hstep_sub n hy).1) ih
  have he_mono : StrictMono e := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    exact (hstep_sub k (he_mem (k + 1))).2
  refine ⟨e, j, he_mono, he_mem 0, fun l hl x y zs hfb hzs => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have hzs_in : ListAllIn zs (seq (k + 1)).1.1 := by
    intro u hu
    obtain ⟨hgt, ⟨r, rfl⟩⟩ := hzs u hu
    have hle : k + 1 ≤ r := by
      have hlt : k + 1 < r := (he_mono.lt_iff_lt (a := k + 1) (b := r)).mp hgt
      omega
    exact hseq_anti hle (he_mem r)
  have hcol := hstep_mono_col k zs ⟨x, y, hfb⟩ hzs_in
  rw [decodeForm_of_formBody hfb] at hcol
  exact hcol

/- ### Section 4: Block Cursor Utilities and Larson's Lemma 3.7 -/

private def ListLt (u v : List ℕ) : Prop := ∀ a ∈ u, ∀ b ∈ v, a < b

private lemma listLt_trans {u v w : List ℕ} (hv : v ≠ [])
    (h1 : ListLt u v) (h2 : ListLt v w) : ListLt u w := by
  intro a ha c hc
  cases v with
  | nil => exact absurd rfl hv
  | cons b _ => exact lt_trans (h1 a ha b (by simp)) (h2 b (by simp) c hc)

private lemma listLt_append_right {u v w : List ℕ} :
    ListLt u (v ++ w) ↔ ListLt u v ∧ ListLt u w := by
  simp only [ListLt, List.mem_append]
  constructor
  · intro h; exact ⟨fun a ha b hb => h a ha b (Or.inl hb), fun a ha c hc => h a ha c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ a ha x (hx | hx)
    · exact h1 a ha x hx
    · exact h2 a ha x hx

private lemma listLt_append_left {u v w : List ℕ} :
    ListLt (u ++ v) w ↔ ListLt u w ∧ ListLt v w := by
  simp only [ListLt, List.mem_append]
  constructor
  · intro h; exact ⟨fun a ha c hc => h a (Or.inl ha) c hc, fun b hb c hc => h b (Or.inr hb) c hc⟩
  · rintro ⟨h1, h2⟩ x (hx | hx) c hc
    · exact h1 x hx c hc
    · exact h2 x hx c hc

private lemma strictSorted_append {u v : List ℕ}
    (hu : StrictSorted u) (hv : StrictSorted v) (huv : ListLt u v) :
    StrictSorted (u ++ v) :=
  List.pairwise_append.mpr ⟨hu, hv, huv⟩

private lemma listAllIn_append {u v : List ℕ} {S : Set ℕ} :
    ListAllIn (u ++ v) S ↔ ListAllIn u S ∧ ListAllIn v S := by
  simp only [ListAllIn, List.mem_append]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx

private lemma mem_interact_iff :
    ∀ (as bs : List (List ℕ)) (x : ℕ),
      x ∈ interact as bs ↔ (∃ u ∈ as, x ∈ u) ∨ (∃ v ∈ bs, x ∈ v)
  | [], bs, x => by simp [interact]
  | a :: as, [], x => by simp [interact]
  | a :: as, b :: bs, x => by
    simp only [interact, List.mem_append, mem_interact_iff as bs, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · rintro ((h | h) | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

private lemma listAllIn_interact {as bs : List (List ℕ)} {S : Set ℕ}
    (ha : ∀ u ∈ as, ListAllIn u S) (hb : ∀ v ∈ bs, ListAllIn v S) :
    ListAllIn (interact as bs) S := by
  intro x hx
  rcases (mem_interact_iff as bs x).mp hx with ⟨u, hu, hxu⟩ | ⟨v, hv, hxv⟩
  · exact ha u hu x hxu
  · exact hb v hv x hxv

private lemma strictSorted_interact :
    ∀ (as bs : List (List ℕ)),
      bs.length ≤ as.length → as.length ≤ bs.length + 1 →
      (∀ u ∈ as, u ≠ [] ∧ StrictSorted u) →
      (∀ v ∈ bs, v ≠ [] ∧ StrictSorted v) →
      (∀ (t : ℕ) (h1 : t < as.length) (h2 : t < bs.length), ListLt (as[t]) (bs[t])) →
      (∀ (t : ℕ) (h1 : t < bs.length) (h2 : t + 1 < as.length), ListLt (bs[t]) (as[t + 1])) →
      StrictSorted (interact as bs)
  | [], [], _, _, _, _, _, _ => List.Pairwise.nil
  | [], _ :: _, hle, _, _, _, _, _ => by simp at hle
  | [a], [], _, _, has, _, _, _ => by
    simp only [interact, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact (has a (by simp)).2
  | _ :: _ :: _, [], _, hge, _, _, _, _ => by simp at hge
  | a :: as, b :: bs, hle, hge, has, hbs, hab, hba => by
    have hle' : bs.length ≤ as.length := by simp at hle; omega
    have hge' : as.length ≤ bs.length + 1 := by simp at hge; omega
    have ha := has a (by simp)
    have hb := hbs b (by simp)
    have has' : ∀ u ∈ as, u ≠ [] ∧ StrictSorted u := fun u hu => has u (by simp [hu])
    have hbs' : ∀ v ∈ bs, v ≠ [] ∧ StrictSorted v := fun v hv => hbs v (by simp [hv])
    have hab0 : ListLt a b := hab 0 (by simp) (by simp)
    have hab' : ∀ (t : ℕ) (h1 : t < as.length) (h2 : t < bs.length), ListLt (as[t]) (bs[t]) :=
      fun t h1 h2 => hab (t + 1) (by simp; omega) (by simp; omega)
    have hba' : ∀ (t : ℕ) (h1 : t < bs.length) (h2 : t + 1 < as.length),
        ListLt (bs[t]) (as[t + 1]) :=
      fun t h1 h2 => hba (t + 1) (by simp; omega) (by simp; omega)
    have hrest : StrictSorted (interact as bs) :=
      strictSorted_interact as bs hle' hge' has' hbs' hab' hba'
    -- Show `ListLt b (interact as bs)` by bounding every element of `as` and `bs` from below by `b`
    have hchain : ∀ k (hk : k < as.length), ListLt b (as[k]) := by
      intro k
      induction k with
      | zero => intro hk; exact hba 0 (by simp) (by simp; omega)
      | succ k ihk =>
        intro hk
        have hk' : k < as.length := by omega
        have hkb : k < bs.length := by omega
        have h1 : ListLt b (as[k]) := ihk hk'
        have h2 : ListLt (as[k]) (bs[k]) := hab' k hk' hkb
        have h3 : ListLt (bs[k]) (as[k + 1]) := hba' k hkb hk
        have hne_ak : as[k] ≠ [] := (has' _ (List.getElem_mem hk')).1
        have hne_bk : bs[k] ≠ [] := (hbs' _ (List.getElem_mem hkb)).1
        exact listLt_trans hne_bk (listLt_trans hne_ak h1 h2) h3
    have hb_lt_rest : ListLt b (interact as bs) := by
      intro x hx y hy
      rcases (mem_interact_iff as bs y).mp hy with ⟨u, hu, hyu⟩ | ⟨v, hv, hyv⟩
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
        exact hchain k hk x hx y hyu
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
        have hka : k < as.length := by omega
        have h1 : ListLt b (as[k]) := hchain k hka
        have h2 : ListLt (as[k]) (bs[k]) := hab' k hka hk
        exact listLt_trans (has' _ (List.getElem_mem hka)).1 h1 h2 x hx y hyv
    have ha_lt_rest : ListLt a (interact as bs) := listLt_trans hb.1 hab0 hb_lt_rest
    simp only [interact, List.append_assoc]
    exact strictSorted_append ha.2 (strictSorted_append hb.2 hrest hb_lt_rest)
      (listLt_append_right.mpr ⟨hab0, ha_lt_rest⟩)

private def block (e : ℕ → ℕ) (start len : ℕ) : List ℕ :=
  (List.range len).map (fun t => e (start + t))

private lemma block_length (e : ℕ → ℕ) (s l : ℕ) : (block e s l).length = l := by
  simp [block]

private lemma block_ne_nil {e : ℕ → ℕ} {s l : ℕ} (hl : 0 < l) : block e s l ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [block] at this
  omega

private lemma block_mem_iff {e : ℕ → ℕ} {s l u : ℕ} :
    u ∈ block e s l ↔ ∃ t < l, e (s + t) = u := by
  simp [block]

private lemma block_mem_range {e : ℕ → ℕ} {s l : ℕ} :
    ListAllIn (block e s l) (Set.range e) := by
  intro u hu
  rcases block_mem_iff.mp hu with ⟨t, _, rfl⟩
  exact ⟨s + t, rfl⟩

private lemma block_strictSorted {e : ℕ → ℕ} (he : StrictMono e) (s l : ℕ) :
    StrictSorted (block e s l) := by
  unfold StrictSorted block
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun h => he (by omega)

private lemma block_lt_block {e : ℕ → ℕ} (he : StrictMono e) {s₁ l₁ s₂ l₂ : ℕ}
    (h : s₁ + l₁ ≤ s₂) : ListLt (block e s₁ l₁) (block e s₂ l₂) := by
  intro a ha b hb
  rcases block_mem_iff.mp ha with ⟨t₁, ht₁, rfl⟩
  rcases block_mem_iff.mp hb with ⟨t₂, ht₂, rfl⟩
  exact he (by omega)

private lemma accLengths_append (acc : ℕ) (ls₁ ls₂ : List (List ℕ)) :
    accLengths acc (ls₁ ++ ls₂) =
      accLengths acc ls₁ ++ accLengths (acc + ls₁.flatten.length) ls₂ := by
  induction ls₁ generalizing acc with
  | nil => simp [accLengths]
  | cons l ls₁ ih =>
    simp only [List.cons_append, accLengths, List.flatten_cons, List.length_append, ih,
      Nat.add_assoc]

private lemma larson_lemma_3_7 {e : ℕ → ℕ} (he : StrictMono e) (he0 : 1 ≤ e 0)
    (m l : ℕ) (hm : 1 ≤ m) (hl : 1 ≤ l) :
    ∃ x : Fin m → List ℕ,
      (∀ i, StrictSorted (x i)) ∧
      (∀ i₁ i₂ : Fin m, i₁ < i₂ →
        ∃ zs, FormBody (kaOf l) (kbOf l) (x i₁) (x i₂) zs ∧ ListAllIn zs (Set.range e)) := by
  let k : ℕ := kbOf l
  have hk1 : 1 ≤ k := by dsimp only [k, kbOf]; omega
  -- Phase 1 cursor: for each `i`, reserve `k + 1` slots for `d_i` and `e (pos1 i)` slots for `a(i, 0)`
  let pos1 : ℕ → ℕ := Nat.rec 0 (fun _ p => p + (k + 1) + e p)
  let dVal (i r : ℕ) : ℕ := e (pos1 i + r)
  let blkLen (i j : ℕ) : ℕ := if j = 0 then dVal i 0 else dVal i j - dVal i (j - 1)
  have he_ge1 : ∀ t, 1 ≤ e t := fun t => le_trans he0 (he.monotone (Nat.zero_le t))
  have hblkLen_pos : ∀ i j, 1 ≤ blkLen i j := by
    intro i j
    dsimp only [blkLen]
    split_ifs with hj
    · exact he_ge1 _
    · have hlt : dVal i (j - 1) < dVal i j := he (by omega)
      omega
  have hpos1_step : ∀ i, pos1 i + (k + 1) + blkLen i 0 = pos1 (i + 1) := by
    intro i
    simp [pos1, blkLen, dVal]
  have hpos1_mono : ∀ {i₁ i₂}, i₁ ≤ i₂ → pos1 i₁ ≤ pos1 i₂ := by
    intro i₁ i₂ h
    induction i₂, h using Nat.le_induction with
    | base => exact le_refl _
    | succ i₂ _ ih =>
      have : pos1 i₂ ≤ pos1 (i₂ + 1) := by rw [← hpos1_step]; omega
      exact le_trans ih this
  have hpos1_lt : ∀ {i₁ i₂}, i₁ < i₂ → pos1 i₁ + (k + 1) + blkLen i₁ 0 ≤ pos1 i₂ := by
    intro i₁ i₂ h
    rw [hpos1_step]
    exact hpos1_mono h
  -- Phase 2 & 3 linearized cursor
  let jOf (t : ℕ) : ℕ := t / m + 1
  let iOf (t : ℕ) : ℕ := if t / m + 1 < k then t % m else m - 1 - t % m
  let stepLen (t : ℕ) : ℕ := blkLen (iOf t) (jOf t)
  let cur : ℕ → ℕ := Nat.rec (pos1 m) (fun t p => p + stepLen t)
  let stepIdx (i j : ℕ) : ℕ :=
    if j < k then (j - 1) * m + i else (k - 1) * m + (m - 1 - i)
  have hstepIdx_inv : ∀ i j, i < m → 1 ≤ j → j ≤ k →
      jOf (stepIdx i j) = j ∧ iOf (stepIdx i j) = i := by
    intro i j him hj1 hjk
    dsimp only [stepIdx, jOf, iOf]
    by_cases hlt : j < k
    · rw [if_pos hlt]
      have hdiv : ((j - 1) * m + i) / m = j - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt him, add_zero]
      have hmod : ((j - 1) * m + i) % m = i := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt him]
      rw [hdiv, hmod, if_pos (by omega)]
      exact ⟨by omega, rfl⟩
    · rw [if_neg hlt]
      have hjeq : j = k := by omega
      have hltm : m - 1 - i < m := by omega
      have hdiv : ((k - 1) * m + (m - 1 - i)) / m = k - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hltm, add_zero]
      have hmod : ((k - 1) * m + (m - 1 - i)) % m = m - 1 - i := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hltm]
      rw [hdiv, hmod, if_neg (by omega)]
      exact ⟨by omega, by omega⟩
  have hcur_mono : ∀ {t₁ t₂}, t₁ ≤ t₂ → cur t₁ ≤ cur t₂ := by
    intro t₁ t₂ h
    induction t₂, h using Nat.le_induction with
    | base => exact le_refl _
    | succ t₂ _ ih => exact le_trans ih (Nat.le_add_right _ _)
  have hcur_lt : ∀ {t₁ t₂}, t₁ < t₂ → cur t₁ + stepLen t₁ ≤ cur t₂ := by
    intro t₁ t₂ h
    exact hcur_mono h
  have hcur_ge : ∀ t, pos1 m ≤ cur t := fun t => hcur_mono (Nat.zero_le t)
  let aPos (i j : ℕ) : ℕ := if j = 0 then pos1 i + (k + 1) else cur (stepIdx i j)
  let aBlk (i j : ℕ) : List ℕ := block e (aPos i j) (blkLen i j)
  have haBlk_len : ∀ i j, (aBlk i j).length = blkLen i j := fun i j => block_length e _ _
  have haBlk_ne : ∀ i j, aBlk i j ≠ [] := fun i j => block_ne_nil (by have := hblkLen_pos i j; omega)
  have haBlk_sort : ∀ i j, StrictSorted (aBlk i j) := fun i j => block_strictSorted he _ _
  have haBlk_range : ∀ i j, ListAllIn (aBlk i j) (Set.range e) := fun i j => block_mem_range
  have hstepLen_eq : ∀ i j, i < m → 1 ≤ j → j ≤ k → stepLen (stepIdx i j) = blkLen i j := by
    intro i j him hj1 hjk
    have hinv := hstepIdx_inv i j him hj1 hjk
    simp [stepLen, hinv.1, hinv.2]
  have haPos_end_le : ∀ {i₁ j₁ i₂ j₂},
      i₁ < m → i₂ < m → j₁ ≤ k → j₂ ≤ k →
      (j₁ = 0 ∧ j₂ = 0 ∧ i₁ < i₂) ∨
      (j₁ = 0 ∧ 1 ≤ j₂) ∨
      (1 ≤ j₁ ∧ 1 ≤ j₂ ∧ stepIdx i₁ j₁ < stepIdx i₂ j₂) →
      aPos i₁ j₁ + blkLen i₁ j₁ ≤ aPos i₂ j₂ := by
    intro i₁ j₁ i₂ j₂ hi₁ hi₂ hj₁ hj₂ hcase
    rcases hcase with ⟨rfl, rfl, hlt⟩ | ⟨rfl, hj₂1⟩ | ⟨hj₁1, hj₂1, hst⟩
    · dsimp only [aPos]
      simp only [↓reduceIte]
      have := hpos1_lt hlt
      omega
    · dsimp only [aPos]
      rw [if_pos rfl, if_neg (by omega)]
      have h1 : pos1 i₁ + (k + 1) + blkLen i₁ 0 ≤ pos1 m := hpos1_lt hi₁
      exact le_trans h1 (hcur_ge _)
    · dsimp only [aPos]
      rw [if_neg (by omega), if_neg (by omega), ← hstepLen_eq i₁ j₁ hi₁ hj₁1 hj₁]
      exact hcur_lt hst
  -- Key `accLengths` and `flatten.length` identities for `aBlk`
  have hflat_len : ∀ i r, 1 ≤ r → r ≤ k + 1 →
      ((List.range r).map (aBlk i)).flatten.length = dVal i (r - 1) := by
    intro i r
    induction r with
    | zero => intro h; omega
    | succ r ih =>
      intro _ hr
      rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton, List.length_append, haBlk_len]
      cases r with
      | zero => simp [blkLen]
      | succ r' =>
        rw [ih (by omega) (by omega)]
        simp only [Nat.add_sub_cancel, blkLen, Nat.succ_ne_zero, ↓reduceIte]
        have hlt : dVal i r' < dVal i (r' + 1) := he (by omega)
        omega
  have hacc_eq : ∀ i r, 1 ≤ r → r ≤ k + 1 →
      accLengths 0 ((List.range r).map (aBlk i)) = block e (pos1 i) r := by
    intro i r
    induction r with
    | zero => intro h; omega
    | succ r ih =>
      intro _ hr
      rw [List.range_succ, List.map_append, List.map_singleton, accLengths_append]
      cases r with
      | zero =>
        simp [accLengths, haBlk_len, blkLen, block, dVal]
      | succ r' =>
        rw [ih (by omega) (by omega), hflat_len i (r' + 1) (by omega) (by omega)]
        simp only [Nat.add_sub_cancel, zero_add, accLengths, haBlk_len, blkLen,
          Nat.succ_ne_zero, ↓reduceIte]
        have hlt : dVal i r' < dVal i (r' + 1) := he (by omega)
        have hsum : dVal i r' + (dVal i (r' + 1) - dVal i r') = dVal i (r' + 1) := by omega
        rw [hsum]
        simp only [block, List.range_succ, List.map_append, List.map_singleton, dVal]
  have hblocks_sort : ∀ i r, i < m → r ≤ k + 1 →
      StrictSorted ((List.range r).map (aBlk i)).flatten := by
    intro i r hi
    induction r with
    | zero => intro _; simp [StrictSorted]
    | succ r ih =>
      intro hr
      rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton]
      refine strictSorted_append (ih (by omega)) (haBlk_sort i r) ?_
      intro u hu v hv
      rw [List.mem_flatten] at hu
      rcases hu with ⟨w, hw, huw⟩
      rcases List.mem_map.mp hw with ⟨j, hj, rfl⟩
      rw [List.mem_range] at hj
      have hpos_le : aPos i j + blkLen i j ≤ aPos i r := by
        apply haPos_end_le hi hi (by omega) (by omega)
        by_cases hj0 : j = 0
        · exact Or.inr (Or.inl ⟨hj0, by omega⟩)
        · refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
          dsimp only [stepIdx]
          split_ifs with h1 h2 h2
          · have : (j - 1) * m + m ≤ (r - 1) * m := by
              rw [← Nat.succ_mul]
              exact Nat.mul_le_mul_right m (by omega)
            omega
          · have : (j - 1) * m + m ≤ (k - 1) * m := by
              rw [← Nat.succ_mul]
              exact Nat.mul_le_mul_right m (by omega)
            omega
          · omega
          · omega
      exact block_lt_block he hpos_le u huw v hv
  -- Split on parity of `l` (`l = 2k - 1` vs `l = 2k`)
  by_cases hodd : l % 2 = 1
  · have hka : kaOf l = k := by dsimp only [kaOf, k, kbOf]; omega
    have hkb : kbOf l = k := rfl
    refine ⟨fun i => ((List.range k).map (aBlk i.1)).flatten,
      fun i => hblocks_sort i.1 k i.2 (by omega), fun i₁ i₂ hi => ?_⟩
    have hi_lt : i₁.1 < i₂.1 := hi
    let A := (List.range k).map (aBlk i₁.1)
    let B := (List.range k).map (aBlk i₂.1)
    let as := (List.range (k - 1)).map (fun t => aBlk i₁.1 (t + 1))
    let bs := (List.range (k - 1)).map (fun t => aBlk i₂.1 (t + 1))
    have hA_eq : A = aBlk i₁.1 0 :: as := by
      dsimp only [A, as]
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl
    have hB_eq : B = aBlk i₂.1 0 :: bs := by
      dsimp only [B, bs]
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl
    let c := accLengths 0 (aBlk i₁.1 0 :: as)
    let d := accLengths 0 (aBlk i₂.1 0 :: bs)
    let zs := c ++ aBlk i₁.1 0 ++ d ++ aBlk i₂.1 0 ++ interact as bs
    have hc_eq : c = block e (pos1 i₁.1) k := by
      change accLengths 0 (aBlk i₁.1 0 :: as) = _
      rw [← hA_eq]; exact hacc_eq i₁.1 k hk1 (by omega)
    have hd_eq : d = block e (pos1 i₂.1) k := by
      change accLengths 0 (aBlk i₂.1 0 :: bs) = _
      rw [← hB_eq]; exact hacc_eq i₂.1 k hk1 (by omega)
    have h_inter_sort : StrictSorted (interact as bs) := by
      refine strictSorted_interact as bs (by simp [as, bs]) (by simp [as, bs])
        (fun u hu => by rcases List.mem_map.mp hu with ⟨t, _, rfl⟩; exact ⟨haBlk_ne _ _, haBlk_sort _ _⟩)
        (fun v hv => by rcases List.mem_map.mp hv with ⟨t, _, rfl⟩; exact ⟨haBlk_ne _ _, haBlk_sort _ _⟩)
        (fun t h1 h2 => ?_) (fun t h1 h2 => ?_)
      · simp only [as, bs, List.getElem_map, List.getElem_range]
        simp only [as, List.length_map, List.length_range] at h1
        apply block_lt_block he
        refine haPos_end_le i₁.2 i₂.2 (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))
        dsimp only [stepIdx]
        rw [if_pos (by omega), if_pos (by omega)]
        omega
      · simp only [as, bs, List.getElem_map, List.getElem_range]
        simp only [as, List.length_map, List.length_range] at h2
        apply block_lt_block he
        refine haPos_end_le i₂.2 i₁.2 (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))
        dsimp only [stepIdx]
        rw [if_pos (by omega), if_pos (by omega)]
        simp only [Nat.add_sub_cancel]
        have : t * m + m = (t + 1) * m := (Nat.succ_mul t m).symm
        omega
    have ha2_lt_inter : ListLt (aBlk i₂.1 0) (interact as bs) := by
      intro u hu v hv
      rcases (mem_interact_iff as bs v).mp hv with ⟨w, hw, hvw⟩ | ⟨w, hw, hvw⟩
      · rcases List.mem_map.mp hw with ⟨t, ht, rfl⟩
        rw [List.mem_range] at ht
        exact block_lt_block he (haPos_end_le i₂.2 i₁.2 (by omega) (by omega)
          (Or.inr (Or.inl ⟨rfl, by omega⟩))) u hu v hvw
      · rcases List.mem_map.mp hw with ⟨t, ht, rfl⟩
        rw [List.mem_range] at ht
        exact block_lt_block he (haPos_end_le i₂.2 i₂.2 (by omega) (by omega)
          (Or.inr (Or.inl ⟨rfl, by omega⟩))) u hu v hvw
    have hd_lt_a2 : ListLt d (aBlk i₂.1 0) := by
      rw [hd_eq]; exact block_lt_block he (by simp [aPos])
    have ha1_lt_d : ListLt (aBlk i₁.1 0) d := by
      rw [hd_eq]; exact block_lt_block he (by simp [aPos]; exact hpos1_lt hi_lt)
    have hc_lt_a1 : ListLt c (aBlk i₁.1 0) := by
      rw [hc_eq]; exact block_lt_block he (by simp [aPos])
    have hzs_sort : StrictSorted zs := by
      have h4 : StrictSorted (aBlk i₂.1 0 ++ interact as bs) :=
        strictSorted_append (haBlk_sort _ _) h_inter_sort ha2_lt_inter
      have h3 : StrictSorted (d ++ (aBlk i₂.1 0 ++ interact as bs)) :=
        strictSorted_append (hd_eq ▸ block_strictSorted he _ _) h4
          (listLt_append_right.mpr ⟨hd_lt_a2, listLt_trans (haBlk_ne _ _) hd_lt_a2 ha2_lt_inter⟩)
      have h2 : StrictSorted (aBlk i₁.1 0 ++ (d ++ (aBlk i₂.1 0 ++ interact as bs))) :=
        strictSorted_append (haBlk_sort _ _) h3
          (listLt_append_right.mpr ⟨ha1_lt_d,
            listLt_trans (hd_eq ▸ block_ne_nil (by omega)) ha1_lt_d
              (listLt_append_right.mpr ⟨hd_lt_a2, listLt_trans (haBlk_ne _ _) hd_lt_a2 ha2_lt_inter⟩)⟩)
      have h1 : StrictSorted (c ++ (aBlk i₁.1 0 ++ (d ++ (aBlk i₂.1 0 ++ interact as bs)))) :=
        strictSorted_append (hc_eq ▸ block_strictSorted he _ _) h2
          (listLt_append_right.mpr ⟨hc_lt_a1,
            listLt_trans (haBlk_ne _ _) hc_lt_a1
              (listLt_append_right.mpr ⟨ha1_lt_d,
                listLt_trans (hd_eq ▸ block_ne_nil (by omega)) ha1_lt_d
                  (listLt_append_right.mpr ⟨hd_lt_a2, listLt_trans (haBlk_ne _ _) hd_lt_a2 ha2_lt_inter⟩)⟩)⟩)
      simpa [zs, List.append_assoc] using h1
    refine ⟨zs, ?_, ?_⟩
    · refine ⟨aBlk i₁.1 0, as, aBlk i₂.1 0, bs, ?_, by rw [← hA_eq], by rw [← hB_eq],
        ?_, ?_, by rw [← hA_eq]; simp [A, hka], by rw [← hB_eq]; simp [B, hkb], rfl, hzs_sort⟩
      · rw [hflat_len i₁.1 k hk1 (by omega), hflat_len i₂.1 k hk1 (by omega)]
        exact he (by have := hpos1_lt hi_lt; omega)
      · intro u hu; rw [← hA_eq] at hu; rcases List.mem_map.mp hu with ⟨j, _, rfl⟩; exact haBlk_ne _ _
      · intro v hv; rw [← hB_eq] at hv; rcases List.mem_map.mp hv with ⟨j, _, rfl⟩; exact haBlk_ne _ _
    · simp only [zs, listAllIn_append]
      exact ⟨⟨⟨⟨hc_eq ▸ block_mem_range, haBlk_range _ _⟩, hd_eq ▸ block_mem_range⟩, haBlk_range _ _⟩,
        listAllIn_interact (fun u hu => by rcases List.mem_map.mp hu with ⟨t, _, rfl⟩; exact haBlk_range _ _)
          (fun v hv => by rcases List.mem_map.mp hv with ⟨t, _, rfl⟩; exact haBlk_range _ _)⟩
  · -- Even case `l = 2 * k`: `kaOf l = k + 1`, `kbOf l = k`
    have hka : kaOf l = k + 1 := by dsimp only [kaOf, k, kbOf]; omega
    have hkb : kbOf l = k := rfl
    refine ⟨fun i => ((List.range (k + 1)).map (aBlk i.1)).flatten,
      fun i => hblocks_sort i.1 (k + 1) i.2 (le_refl _), fun i₁ i₂ hi => ?_⟩
    have hi_lt : i₁.1 < i₂.1 := hi
    let A := (List.range (k + 1)).map (aBlk i₁.1)
    let as := (List.range k).map (fun t => aBlk i₁.1 (t + 1))
    have hA_eq : A = aBlk i₁.1 0 :: as := by
      simp [A, as, List.range_succ_eq_map]
    -- `x i₂` is split into `k` blocks: merge the last two blocks `aBlk i₂ (k - 1)` and `aBlk i₂ k`
    let B := (List.range (k - 1)).map (aBlk i₂.1) ++ [aBlk i₂.1 (k - 1) ++ aBlk i₂.1 k]
    have hB_len : B.length = k := by simp [B]; omega
    have hB_flat : B.flatten = ((List.range (k + 1)).map (aBlk i₂.1)).flatten := by
      have hr : List.range (k + 1) = List.range (k - 1) ++ [k - 1, k] := by
        conv_lhs => rw [show k + 1 = (k - 1) + 1 + 1 by omega]
        rw [List.range_succ, List.range_succ, List.append_assoc]
        simp [show k - 1 + 1 = k by omega]
      rw [hr, List.map_append, List.flatten_append]
      simp
    have hB_acc : accLengths 0 B = block e (pos1 i₂.1) (k - 1) ++ [dVal i₂.1 k] := by
      dsimp only [B]
      rw [accLengths_append]
      by_cases hk_eq1 : k = 1
      · rw [hk_eq1]
        simp only [Nat.sub_self, List.range_zero, List.map_nil, accLengths, List.flatten_nil,
          List.length_nil, add_zero, zero_add, List.nil_append, List.length_append, haBlk_len,
          blkLen, ↓reduceIte, Nat.one_ne_zero, block]
        have hlt : dVal i₂.1 0 < dVal i₂.1 1 := he (by omega)
        have : dVal i₂.1 0 + (dVal i₂.1 1 - dVal i₂.1 0) = dVal i₂.1 1 := by omega
        rw [this]
      · rw [hacc_eq i₂.1 (k - 1) (by omega) (by omega),
          hflat_len i₂.1 (k - 1) (by omega) (by omega)]
        simp only [zero_add, accLengths, List.length_append, haBlk_len, blkLen,
          show k - 1 ≠ 0 by omega, show k ≠ 0 by omega, ↓reduceIte]
        have h1 : dVal i₂.1 (k - 2) < dVal i₂.1 (k - 1) := he (by omega)
        have h2 : dVal i₂.1 (k - 1) < dVal i₂.1 k := he (by omega)
        have hsum : dVal i₂.1 (k - 1 - 1) + (dVal i₂.1 (k - 1) - dVal i₂.1 (k - 1 - 1) +
            (dVal i₂.1 k - dVal i₂.1 (k - 1))) = dVal i₂.1 k := by
          have : k - 1 - 1 = k - 2 := by omega
          rw [this]; omega
        rw [hsum]
    have hB_sort_last : StrictSorted (aBlk i₂.1 (k - 1) ++ aBlk i₂.1 k) := by
      refine strictSorted_append (haBlk_sort _ _) (haBlk_sort _ _) (block_lt_block he ?_)
      apply haPos_end_le i₂.2 i₂.2 (by omega) (le_refl k)
      by_cases hk_eq1 : k = 1
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · refine Or.inr (Or.inr ⟨by omega, hk1, ?_⟩)
        dsimp only [stepIdx]
        rw [if_pos (by omega), if_neg (lt_irrefl k)]
        have hmul : (k - 1 - 1) * m + m = (k - 1) * m := by
          rw [← Nat.succ_mul]
          congr 1; omega
        omega
    have hd_sort : StrictSorted (accLengths 0 B) := by
      rw [hB_acc]
      refine strictSorted_append (block_strictSorted he _ _) (List.pairwise_singleton _ _) ?_
      intro u hu v hv
      rcases block_mem_iff.mp hu with ⟨t, ht, rfl⟩
      simp only [List.mem_singleton] at hv; subst hv
      exact he (by omega)
    have hd_range : ListAllIn (accLengths 0 B) (Set.range e) := by
      rw [hB_acc, listAllIn_append]
      exact ⟨block_mem_range, fun v hv => by
        simp only [List.mem_singleton] at hv; subst hv; exact ⟨pos1 i₂.1 + k, rfl⟩⟩
    have hB_ne : B ≠ [] := by intro h; rw [h] at hB_len; simp at hB_len; omega
    let b0 := B.head hB_ne
    let bs := B.tail
    have hB_cons : B = b0 :: bs := (List.cons_head_tail hB_ne).symm
    let c := accLengths 0 (aBlk i₁.1 0 :: as)
    let d := accLengths 0 (b0 :: bs)
    let zs := c ++ aBlk i₁.1 0 ++ d ++ b0 ++ interact as bs
    have hc_eq : c = block e (pos1 i₁.1) (k + 1) := by
      change accLengths 0 (aBlk i₁.1 0 :: as) = _
      rw [← hA_eq]; exact hacc_eq i₁.1 (k + 1) (by omega) (le_refl _)
    have hd_eq : d = accLengths 0 B := by
      change accLengths 0 (b0 :: bs) = _
      rw [← hB_cons]
    have hb0_eq : b0 = if k = 1 then aBlk i₂.1 0 ++ aBlk i₂.1 1 else aBlk i₂.1 0 := by
      dsimp only [b0, B]
      by_cases hk_eq1 : k = 1
      · rw [if_pos hk_eq1]
        simp [hk_eq1]
      · rw [if_neg hk_eq1]
        have hr : List.range (k - 1) = 0 :: (List.range (k - 2)).map (· + 1) := by
          conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega]
          rw [List.range_succ_eq_map]
        simp [hr]
    have hbs_eq : bs = if k = 1 then [] else
        (List.range (k - 2)).map (fun t => aBlk i₂.1 (t + 1)) ++ [aBlk i₂.1 (k - 1) ++ aBlk i₂.1 k] := by
      dsimp only [bs, B]
      by_cases hk_eq1 : k = 1
      · rw [if_pos hk_eq1]
        simp [hk_eq1]
      · rw [if_neg hk_eq1]
        have hr : List.range (k - 1) = 0 :: (List.range (k - 2)).map (· + 1) := by
          conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega]
          rw [List.range_succ_eq_map]
        simp [hr]
    have h_a2_lt_a1k : ListLt (aBlk i₂.1 k) (aBlk i₁.1 k) := by
      apply block_lt_block he
      refine haPos_end_le i₂.2 i₁.2 (le_refl k) (le_refl k) (Or.inr (Or.inr ⟨hk1, hk1, ?_⟩))
      dsimp only [stepIdx]
      rw [if_neg (lt_irrefl k), if_neg (lt_irrefl k)]
      omega
    have hbs_get : ∀ (t : ℕ) (ht : t < bs.length),
        bs[t] = if t < k - 2 then aBlk i₂.1 (t + 1) else aBlk i₂.1 (k - 1) ++ aBlk i₂.1 k := by
      intro t ht
      have hbs_len : bs.length = k - 1 := by
        have := congrArg List.length hB_cons; simp only [List.length_cons] at this; omega
      have hk2 : k ≠ 1 := by omega
      have hbs_eq2 : bs = (List.range (k - 2)).map (fun t => aBlk i₂.1 (t + 1)) ++
          [aBlk i₂.1 (k - 1) ++ aBlk i₂.1 k] := by rw [hbs_eq, if_neg hk2]
      have hget : bs[t]'ht = ((List.range (k - 2)).map (fun t => aBlk i₂.1 (t + 1)) ++
          [aBlk i₂.1 (k - 1) ++ aBlk i₂.1 k])[t]'(hbs_eq2 ▸ ht) := by
        congr 1
      rw [hget]
      split_ifs with ht2
      · rw [List.getElem_append_left (by simp; omega)]; simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp
    have h_inter_sort : StrictSorted (interact as bs) := by
      have hbs_len : bs.length = k - 1 := by
        have := congrArg List.length hB_cons; simp only [List.length_cons] at this; omega
      refine strictSorted_interact as bs (by simp [as, hbs_len]) (by simp [as, hbs_len]; omega)
        (fun u hu => by rcases List.mem_map.mp hu with ⟨t, _, rfl⟩; exact ⟨haBlk_ne _ _, haBlk_sort _ _⟩)
        (fun v hv => ?_) (fun t h1 h2 => ?_) (fun t h1 h2 => ?_)
      · rw [hbs_eq] at hv
        split_ifs at hv with hk_eq1
        · simp at hv
        · rcases List.mem_append.mp hv with h1 | h2
          · rcases List.mem_map.mp h1 with ⟨t, _, rfl⟩; exact ⟨haBlk_ne _ _, haBlk_sort _ _⟩
          · simp only [List.mem_singleton] at h2; subst h2
            exact ⟨List.append_ne_nil_of_left_ne_nil (haBlk_ne _ _) _, hB_sort_last⟩
      · have ht : t < k - 1 := by omega
        have has_t : as[t] = aBlk i₁.1 (t + 1) := by simp [as]
        rw [has_t, hbs_get t h2]
        split_ifs with ht2
        · apply block_lt_block he
          refine haPos_end_le i₁.2 i₂.2 (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))
          dsimp only [stepIdx]; rw [if_pos (by omega), if_pos (by omega)]; omega
        · have ht_eq : t + 1 = k - 1 := by omega
          rw [ht_eq, listLt_append_right]
          refine ⟨block_lt_block he (haPos_end_le i₁.2 i₂.2 (by omega) (by omega)
            (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))),
            block_lt_block he (haPos_end_le i₁.2 i₂.2 (by omega) (le_refl k)
            (Or.inr (Or.inr ⟨by omega, hk1, ?_⟩)))⟩
          · dsimp only [stepIdx]; rw [if_pos (by omega), if_pos (by omega)]; omega
          · dsimp only [stepIdx]; rw [if_pos (by omega), if_neg (lt_irrefl k)]
            have hmul : (k - 1 - 1) * m + m = (k - 1) * m := by
              rw [← Nat.succ_mul]; congr 1; omega
            omega
      · have ht : t < k - 1 := by omega
        have has_t1 : as[t + 1] = aBlk i₁.1 (t + 2) := by simp [as]
        rw [has_t1, hbs_get t h1]
        split_ifs with ht2
        · apply block_lt_block he
          refine haPos_end_le i₂.2 i₁.2 (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))
          dsimp only [stepIdx]; rw [if_pos (by omega), if_pos (by omega)]
          simp only [Nat.add_sub_cancel, show t + 2 - 1 = t + 1 by omega]
          have : t * m + m = (t + 1) * m := (Nat.succ_mul t m).symm
          omega
        · have ht_eq : t + 2 = k := by omega
          rw [ht_eq, listLt_append_left]
          refine ⟨block_lt_block he (haPos_end_le i₂.2 i₁.2 (by omega) (le_refl k)
            (Or.inr (Or.inr ⟨by omega, hk1, ?_⟩))), h_a2_lt_a1k⟩
          dsimp only [stepIdx]; rw [if_pos (by omega), if_neg (lt_irrefl k)]
          have hmul : (k - 1 - 1) * m + m = (k - 1) * m := by
            rw [← Nat.succ_mul]; congr 1; omega
          omega
    have hb0_ne : b0 ≠ [] := by
      rw [hb0_eq]; split_ifs
      · exact List.append_ne_nil_of_left_ne_nil (haBlk_ne _ _) _
      · exact haBlk_ne _ _
    have hb0_sort : StrictSorted b0 := by
      rw [hb0_eq]; split_ifs with hk1'
      · simpa [hk1'] using hB_sort_last
      · exact haBlk_sort _ _
    have hb0_lt_inter : ListLt b0 (interact as bs) := by
      rw [hb0_eq]
      split_ifs with hk1'
      · have has_eq : as = [aBlk i₁.1 1] := by simp [as, hk1']
        have hbs_eq' : bs = [] := by rw [hbs_eq, if_pos hk1']
        rw [has_eq, hbs_eq']
        simp only [interact, List.flatten_cons, List.flatten_nil, List.append_nil, listLt_append_left]
        refine ⟨block_lt_block he (haPos_end_le i₂.2 i₁.2 (by omega) (by omega)
          (Or.inr (Or.inl ⟨rfl, by omega⟩))), ?_⟩
        simpa [hk1'] using h_a2_lt_a1k
      · intro u hu v hv
        rcases (mem_interact_iff as bs v).mp hv with ⟨w, hw, hvw⟩ | ⟨w, hw, hvw⟩
        · rcases List.mem_map.mp hw with ⟨t, ht, rfl⟩
          rw [List.mem_range] at ht
          exact block_lt_block he (haPos_end_le i₂.2 i₁.2 (by omega) (by omega)
            (Or.inr (Or.inl ⟨rfl, by omega⟩))) u hu v hvw
        · rw [hbs_eq, if_neg hk1'] at hw
          rcases List.mem_append.mp hw with h1 | h2
          · rcases List.mem_map.mp h1 with ⟨t, ht, rfl⟩
            rw [List.mem_range] at ht
            exact block_lt_block he (haPos_end_le i₂.2 i₂.2 (by omega) (by omega)
              (Or.inr (Or.inl ⟨rfl, by omega⟩))) u hu v hvw
          · simp only [List.mem_singleton] at h2; subst h2
            rcases List.mem_append.mp hvw with hvw1 | hvw2
            · exact block_lt_block he (haPos_end_le i₂.2 i₂.2 (by omega) (by omega)
                (Or.inr (Or.inl ⟨rfl, by omega⟩))) u hu v hvw1
            · exact block_lt_block he (haPos_end_le i₂.2 i₂.2 (by omega) (le_refl k)
                (Or.inr (Or.inl ⟨rfl, hk1⟩))) u hu v hvw2
    have hd_lt_b0 : ListLt d b0 := by
      rw [hd_eq, hB_acc, hb0_eq]
      have h_d_lt_a20 : ListLt (block e (pos1 i₂.1) (k - 1) ++ [dVal i₂.1 k]) (aBlk i₂.1 0) := by
        rw [listLt_append_left]
        refine ⟨block_lt_block he (by simp [aPos]; omega), fun u hu v hv => ?_⟩
        simp only [List.mem_singleton] at hu; subst hu
        rcases block_mem_iff.mp hv with ⟨t, _, rfl⟩
        exact he (by simp [aPos]; omega)
      split_ifs with hk1'
      · rw [listLt_append_right]
        exact ⟨h_d_lt_a20, listLt_trans (haBlk_ne _ _) h_d_lt_a20
          (block_lt_block he (haPos_end_le i₂.2 i₂.2 (by omega) (by omega) (Or.inr (Or.inl ⟨rfl, by omega⟩))))⟩
      · exact h_d_lt_a20
    have ha1_lt_d : ListLt (aBlk i₁.1 0) d := by
      rw [hd_eq, hB_acc, listLt_append_right]
      refine ⟨block_lt_block he (by simp [aPos]; exact hpos1_lt hi_lt), fun u hu v hv => ?_⟩
      simp only [List.mem_singleton] at hv; subst hv
      rcases block_mem_iff.mp hu with ⟨t, ht, rfl⟩
      have := hpos1_lt hi_lt
      exact he (by simp [aPos] at ht ⊢; omega)
    have hc_lt_a1 : ListLt c (aBlk i₁.1 0) := by
      rw [hc_eq]; exact block_lt_block he (by simp [aPos])
    have hd_ne : d ≠ [] := by
      rw [hd_eq, hB_acc]
      exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    have hzs_sort : StrictSorted zs := by
      have h4 : StrictSorted (b0 ++ interact as bs) :=
        strictSorted_append hb0_sort h_inter_sort hb0_lt_inter
      have h3 : StrictSorted (d ++ (b0 ++ interact as bs)) :=
        strictSorted_append (hd_eq ▸ hd_sort) h4
          (listLt_append_right.mpr ⟨hd_lt_b0, listLt_trans hb0_ne hd_lt_b0 hb0_lt_inter⟩)
      have h2 : StrictSorted (aBlk i₁.1 0 ++ (d ++ (b0 ++ interact as bs))) :=
        strictSorted_append (haBlk_sort _ _) h3
          (listLt_append_right.mpr ⟨ha1_lt_d,
            listLt_trans hd_ne ha1_lt_d
              (listLt_append_right.mpr ⟨hd_lt_b0, listLt_trans hb0_ne hd_lt_b0 hb0_lt_inter⟩)⟩)
      have h1 : StrictSorted (c ++ (aBlk i₁.1 0 ++ (d ++ (b0 ++ interact as bs)))) :=
        strictSorted_append (hc_eq ▸ block_strictSorted he _ _) h2
          (listLt_append_right.mpr ⟨hc_lt_a1,
            listLt_trans (haBlk_ne _ _) hc_lt_a1
              (listLt_append_right.mpr ⟨ha1_lt_d,
                listLt_trans hd_ne ha1_lt_d
                  (listLt_append_right.mpr ⟨hd_lt_b0, listLt_trans hb0_ne hd_lt_b0 hb0_lt_inter⟩)⟩)⟩)
      simpa [zs, List.append_assoc] using h1
    refine ⟨zs, ?_, ?_⟩
    · refine ⟨aBlk i₁.1 0, as, b0, bs, ?_, by rw [← hA_eq], by rw [← hB_cons, hB_flat],
        ?_, ?_, by rw [← hA_eq]; simp [A, hka], by rw [← hB_cons, hB_len], rfl, hzs_sort⟩
      · rw [hflat_len i₁.1 (k + 1) (by omega) (le_refl _),
          hflat_len i₂.1 (k + 1) (by omega) (le_refl _)]
        exact he (by have := hpos1_lt hi_lt; omega)
      · intro u hu; rw [← hA_eq] at hu; rcases List.mem_map.mp hu with ⟨j, _, rfl⟩; exact haBlk_ne _ _
      · intro v hv
        rw [← hB_cons] at hv
        rcases List.mem_append.mp hv with h1 | h2
        · rcases List.mem_map.mp h1 with ⟨j, _, rfl⟩; exact haBlk_ne _ _
        · simp only [List.mem_singleton] at h2; subst h2
          exact List.append_ne_nil_of_left_ne_nil (haBlk_ne _ _) _
    · simp only [zs, listAllIn_append]
      refine ⟨⟨⟨⟨hc_eq ▸ block_mem_range, haBlk_range _ _⟩, hd_eq ▸ hd_range⟩, ?_⟩,
        listAllIn_interact (fun u hu => by rcases List.mem_map.mp hu with ⟨t, _, rfl⟩; exact haBlk_range _ _)
          (fun v hv => ?_)⟩
      · rw [hb0_eq]; split_ifs
        · exact listAllIn_append.mpr ⟨haBlk_range _ _, haBlk_range _ _⟩
        · exact haBlk_range _ _
      · rw [hbs_eq] at hv; split_ifs at hv with hk1'
        · simp at hv
        · rcases List.mem_append.mp hv with h1 | h2
          · rcases List.mem_map.mp h1 with ⟨t, _, rfl⟩; exact haBlk_range _ _
          · simp only [List.mem_singleton] at h2; subst h2
            exact listAllIn_append.mpr ⟨haBlk_range _ _, haBlk_range _ _⟩

/- ### Section 5: `mergeBlocks` and Larson's Lemma 3.8 -/

private lemma interact_cons_shift :
    ∀ (as bs : List (List ℕ)) (a b : List ℕ),
      interact (a :: as) (b :: bs) = a ++ interact (b :: bs) as
  | [], bs, a, b => by simp [interact]
  | a' :: as, [], a, b => by simp [interact]
  | a' :: as, b' :: bs, a, b => by
    simp only [interact, List.append_assoc]
    congr 1
    congr 1
    simpa [interact, List.append_assoc] using interact_cons_shift as bs a' b'

private lemma strictSorted_accLengths (acc : ℕ) (ls : List (List ℕ))
    (hne : ∀ u ∈ ls, u ≠ []) : StrictSorted (accLengths acc ls) := by
  induction ls generalizing acc with
  | nil => exact List.Pairwise.nil
  | cons u ls ih =>
    have hu_pos : 0 < u.length := List.length_pos_of_ne_nil (hne u (by simp))
    have hgt : ∀ x ∈ accLengths (acc + u.length) ls, acc + u.length < x := by
      have : ∀ (a : ℕ) (L : List (List ℕ)), (∀ v ∈ L, v ≠ []) → ∀ x ∈ accLengths a L, a < x := by
        intro a L
        induction L generalizing a with
        | nil => intro _ _ h; simp [accLengths] at h
        | cons v L ihL =>
          intro hL x hx
          have hv_pos : 0 < v.length := List.length_pos_of_ne_nil (hL v (by simp))
          simp only [accLengths, List.mem_cons] at hx
          rcases hx with rfl | hx'
          · omega
          · exact lt_trans (by omega) (ihL (a + v.length) (fun w hw => hL w (by simp [hw])) x hx')
      exact this (acc + u.length) ls (fun v hv => hne v (by simp [hv]))
    exact List.pairwise_cons.mpr ⟨hgt, ih (acc + u.length) (fun v hv => hne v (by simp [hv]))⟩

private lemma accLengths_mem_total (acc : ℕ) :
    ∀ (G : List (List ℕ)), G ≠ [] → acc + G.flatten.length ∈ accLengths acc G
  | [], h => absurd rfl h
  | [a], _ => by simp [accLengths]
  | a :: b :: t, _ => by
    have hih := accLengths_mem_total (acc + a.length) (b :: t) (List.cons_ne_nil b t)
    simp only [accLengths, List.flatten_cons, List.length_append, List.mem_cons] at hih ⊢
    right
    simpa only [Nat.add_assoc] using hih

private lemma flatten_map_flatten {α : Type*} :
    ∀ (L : List (List (List α))), (L.map List.flatten).flatten = L.flatten.flatten
  | [] => rfl
  | G :: Gs => by simp [flatten_map_flatten Gs]

private lemma mem_takeWhile_true {α : Type*} {p : α → Bool} :
    ∀ {L : List α} {x : α}, x ∈ L.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: t, x, h => by
    by_cases ha : p a = true
    · simp only [List.takeWhile_cons, ha, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h'
      · exact ha
      · exact mem_takeWhile_true h'
    · have haf : p a = false := Bool.eq_false_iff.mpr ha
      simp [haf] at h

private lemma head_dropWhile_false {α : Type*} {p : α → Bool} :
    ∀ {L : List α} (hne : L.dropWhile p ≠ []), p ((L.dropWhile p).head hne) = false
  | [], hne => absurd rfl hne
  | a :: t, hne => by
    by_cases ha : p a = true
    · simp only [List.dropWhile_cons, ha, ↓reduceIte] at hne ⊢
      exact head_dropWhile_false hne
    · have haf : p a = false := Bool.eq_false_iff.mpr ha
      simp [haf]

private lemma accLengths_map_flatten_subset (acc : ℕ) :
    ∀ (Ps : List (List (List ℕ))), (∀ G ∈ Ps, G ≠ []) →
      ∀ x ∈ accLengths acc (Ps.map List.flatten), x ∈ accLengths acc Ps.flatten
  | [], _, _, hx => by simp [accLengths] at hx
  | G :: Ps, hPs, x, hx => by
    simp only [List.map_cons, accLengths, List.mem_cons, List.flatten_cons, accLengths_append,
      List.mem_append] at hx ⊢
    rcases hx with rfl | hx'
    · exact Or.inl (accLengths_mem_total acc G (hPs G (by simp)))
    · exact Or.inr (accLengths_map_flatten_subset (acc + G.flatten.length) Ps
        (fun H hH => hPs H (by simp [hH])) x hx')

private lemma mergeBlocks :
    ∀ (n : ℕ) (P Q : List (List ℕ)),
      P.length + Q.length ≤ n →
      P ≠ [] → Q ≠ [] →
      (∀ u ∈ P, u ≠ [] ∧ StrictSorted u) →
      (∀ v ∈ Q, v ≠ [] ∧ StrictSorted v) →
      StrictSorted P.flatten → StrictSorted Q.flatten →
      (∀ u ∈ P, ∀ v ∈ Q, ListLt u v ∨ ListLt v u) →
      (∀ (hP : P ≠ []) (hQ : Q ≠ []), ListLt (P.head hP) (Q.head hQ)) →
      ∃ (Ps Qs : List (List (List ℕ))),
        Ps.flatten = P ∧ Qs.flatten = Q ∧
        (∀ G ∈ Ps, G ≠ []) ∧ (∀ G ∈ Qs, G ≠ []) ∧
        1 ≤ Qs.length ∧ Qs.length ≤ Ps.length ∧ Ps.length ≤ Qs.length + 1 ∧
        StrictSorted (interact (Ps.map List.flatten) (Qs.map List.flatten)) ∧
        ∀ (hPs : Ps ≠ []) (hQ : Q ≠ []), ∀ u ∈ Ps.head hPs, ListLt u (Q.head hQ) := by
  intro n
  induction n with
  | zero => intro P Q hlen hP; cases P with | nil => exact absurd rfl hP | cons _ _ => simp at hlen
  | succ n ih =>
    intro P Q hlen hP hQ hPprop hQprop hPsort hQsort hcomp hhead
    let q0 := Q.head hQ
    let pred : List ℕ → Bool := fun u => decide (ListLt u q0)
    let Ppre := P.takeWhile pred
    let Psuf := P.dropWhile pred
    have hP_eq : Ppre ++ Psuf = P := List.takeWhile_append_dropWhile
    have hPpre_ne : Ppre ≠ [] := by
      cases P with
      | nil => exact absurd rfl hP
      | cons p0 P' =>
        have hp0 : pred p0 = true := by
          simp only [pred, decide_eq_true_eq]
          exact hhead (List.cons_ne_nil _ _) hQ
        simp [Ppre, hp0]
    have hPpre_lt_q0 : ∀ u ∈ Ppre, ListLt u q0 := by
      intro u hu
      have := mem_takeWhile_true hu
      simpa [pred] using this
    have hPpre_lt_Q : ListLt Ppre.flatten Q.flatten := by
      intro a ha b hb
      rcases List.mem_flatten.mp ha with ⟨u, hu, hau⟩
      have hQ_cons : Q = q0 :: Q.tail := (List.cons_head_tail hQ).symm
      rw [hQ_cons, List.flatten_cons, List.mem_append] at hb
      rcases hb with hbq0 | hbtail
      · exact hPpre_lt_q0 u hu a hau b hbq0
      · have hq0_lt_tail : ListLt q0 Q.tail.flatten := by
          have := hQsort
          rw [hQ_cons, List.flatten_cons] at this
          exact (List.pairwise_append.mp this).2.2
        have hq0_ne : q0 ≠ [] := (hQprop q0 (List.head_mem hQ)).1
        exact listLt_trans hq0_ne (hPpre_lt_q0 u hu) hq0_lt_tail a hau b hbtail
    have hPpre_sort : StrictSorted Ppre.flatten := by
      have := hPsort
      rw [← hP_eq, List.flatten_append] at this
      exact (List.pairwise_append.mp this).1
    by_cases hPsuf_nil : Psuf = []
    · have hPpre_eq : Ppre = P := by rw [← hP_eq, hPsuf_nil, List.append_nil]
      refine ⟨[Ppre], [Q], by simp [hPpre_eq], by simp,
        fun G hG => by simp only [List.mem_singleton] at hG; subst hG; exact hPpre_ne,
        fun G hG => by simp only [List.mem_singleton] at hG; subst hG; exact hQ,
        by simp, by simp, by simp, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, interact, List.flatten_nil, List.append_nil]
        exact strictSorted_append hPpre_sort hQsort hPpre_lt_Q
      · intro _ _ u hu
        simp only [List.head_cons] at hu
        exact hPpre_lt_q0 u hu
    · have hPsuf_len : Q.length + Psuf.length ≤ n := by
        have h1 : Ppre.length + Psuf.length = P.length := by
          rw [← List.length_append, hP_eq]
        have h2 : 0 < Ppre.length := List.length_pos_of_ne_nil hPpre_ne
        omega
      have hPsuf_sub : ∀ u ∈ Psuf, u ∈ P := fun u hu => hP_eq ▸ List.mem_append_right _ hu
      have hPsuf_sort : StrictSorted Psuf.flatten := by
        have := hPsort
        rw [← hP_eq, List.flatten_append] at this
        exact (List.pairwise_append.mp this).2.1
      have hPpre_lt_Psuf : ListLt Ppre.flatten Psuf.flatten := by
        have := hPsort
        rw [← hP_eq, List.flatten_append] at this
        exact (List.pairwise_append.mp this).2.2
      have hq0_lt_p1 : ListLt q0 (Psuf.head hPsuf_nil) := by
        have hnot : pred (Psuf.head hPsuf_nil) = false := head_dropWhile_false hPsuf_nil
        have hnotlt : ¬ ListLt (Psuf.head hPsuf_nil) q0 := by
          simpa [pred] using hnot
        have hp1_mem : Psuf.head hPsuf_nil ∈ P := hPsuf_sub _ (List.head_mem hPsuf_nil)
        have hq0_mem : q0 ∈ Q := List.head_mem hQ
        exact (hcomp _ hp1_mem _ hq0_mem).resolve_left hnotlt
      obtain ⟨Qs, Ps', hQs_flat, hPs'_flat, hQs_ne, hPs'_ne, hPs'_len1, hPs'_le_Qs, hQs_le_Ps',
          hinter_sort, _⟩ :=
        ih Q Psuf hPsuf_len hQ hPsuf_nil hQprop (fun u hu => hPprop u (hPsuf_sub u hu))
          hQsort hPsuf_sort (fun v hv u hu => (hcomp u (hPsuf_sub u hu) v hv).symm)
          (fun _ _ => hq0_lt_p1)
      have hQs_nonempty : Qs ≠ [] := List.ne_nil_of_length_pos (by omega)
      refine ⟨Ppre :: Ps', Qs, by simp [hPs'_flat, hP_eq], hQs_flat,
        fun G hG => by rcases List.mem_cons.mp hG with rfl | hG'; exact hPpre_ne; exact hPs'_ne G hG',
        hQs_ne, by omega, by simp; omega, by simp; omega, ?_, ?_⟩
      · cases hQs_eq : Qs with
        | nil => exact absurd hQs_eq hQs_nonempty
        | cons Q0 Qs' =>
          simp only [List.map_cons]
          rw [interact_cons_shift]
          refine strictSorted_append hPpre_sort (by simpa [hQs_eq] using hinter_sort) ?_
          intro a ha b hb
          rcases (mem_interact_iff (Q0.flatten :: Qs'.map List.flatten) (Ps'.map List.flatten) b).mp hb with
              ⟨v, hv, hbv⟩ | ⟨u, hu, hbu⟩
          · have hbQ : b ∈ Q.flatten := by
              rw [← hQs_flat, hQs_eq]
              simp only [List.mem_cons, List.mem_map] at hv
              rcases hv with rfl | ⟨G, hG, rfl⟩
              · rw [List.flatten_cons, List.flatten_append]; exact List.mem_append_left _ hbv
              · rw [List.flatten_cons, List.flatten_append]
                refine List.mem_append_right _ (List.mem_flatten.mpr ?_)
                rcases List.mem_flatten.mp hbv with ⟨w, hw, hbw⟩
                exact ⟨w, List.mem_flatten.mpr ⟨G, hG, hw⟩, hbw⟩
            exact hPpre_lt_Q a ha b hbQ
          · have hbPsuf : b ∈ Psuf.flatten := by
              rw [← hPs'_flat]
              rcases List.mem_map.mp hu with ⟨G, hG, rfl⟩
              rcases List.mem_flatten.mp hbu with ⟨w, hw, hbw⟩
              exact List.mem_flatten.mpr ⟨w, List.mem_flatten.mpr ⟨G, hG, hw⟩, hbw⟩
            exact hPpre_lt_Psuf a ha b hbPsuf
      · intro _ _ u hu
        simp only [List.head_cons] at hu
        exact hPpre_lt_q0 u hu

private def pairsBefore (s : ℕ) : List (ℕ × ℕ) :=
  (List.range s).flatMap fun j =>
    if j = 0 then [] else (List.range j).map fun i => (j, i + 1)

private lemma mem_pairsBefore_iff (s j i : ℕ) :
    (j, i) ∈ pairsBefore s ↔ 1 ≤ i ∧ i ≤ j ∧ j < s := by
  simp only [pairsBefore, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨j', hj', hmem⟩
    split_ifs at hmem with hj0
    · simp at hmem
    · rcases List.mem_map.mp hmem with ⟨i', hi', heq⟩
      rw [List.mem_range] at hi'
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      omega
  · rintro ⟨hi1, hij, hjs⟩
    refine ⟨j, hjs, ?_⟩
    rw [if_neg (by omega)]
    exact List.mem_map.mpr ⟨i - 1, List.mem_range.mpr (by omega), by ext; simp; omega⟩

private lemma pairsBefore_nodup (s : ℕ) : (pairsBefore s).Nodup := by
  dsimp only [pairsBefore]
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · split_ifs
    · exact List.nodup_nil
    · exact List.nodup_range.map (fun _ _ h => by have := (Prod.mk.inj h).2; omega)
  · refine List.pairwise_lt_range.imp fun {j₁ j₂} hlt => ?_
    intro x hx₁ hx₂
    by_cases h1 : j₁ = 0
    · simp [h1] at hx₁
    · simp only [h1, ↓reduceIte, List.mem_map] at hx₁
      rcases hx₁ with ⟨i₁, _, rfl⟩
      by_cases h2 : j₂ = 0
      · simp [h2] at hx₂
      · simp only [h2, ↓reduceIte, List.mem_map] at hx₂
        rcases hx₂ with ⟨i₂, _, heq⟩
        have := (Prod.mk.inj heq).1
        omega

private def stageState (e : ℕ → ℕ) : ℕ → ℕ × (ℕ → ℕ)
  | 0 => (4, fun _ => 4)
  | s + 1 =>
    let cur := (stageState e s).1
    let tbl := (stageState e s).2
    let bTot := ((pairsBefore (s + 1)).map
      (fun p => e (tbl p.1 + p.2) - e (tbl p.1 + p.2 - 1))).sum
    (cur + (s + 2) + e cur + bTot, fun j => if j = s + 1 then cur else tbl j)

private lemma stageState_tbl_eq (e : ℕ → ℕ) :
    ∀ {j s : ℕ}, 1 ≤ j → j ≤ s → (stageState e s).2 j = (stageState e (j - 1)).1 := by
  intro j s hj hjs
  induction s, hjs using Nat.le_induction with
  | base =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [stageState]
  | succ s hjs ih =>
    simp only [stageState, show j ≠ s + 1 by omega, ↓reduceIte]
    exact ih

private lemma list_take_sum_lt {α : Type*} (L : List α) (w : α → ℕ) {i₁ i₂ : ℕ}
    (h12 : i₁ < i₂) (hi₂ : i₂ ≤ L.length) :
    ((L.take i₁).map w).sum + w (L[i₁]'(by omega)) ≤ ((L.take i₂).map w).sum := by
  have htake1 : L.take (i₁ + 1) = L.take i₁ ++ [L[i₁]'(by omega)] := by
    rw [List.take_succ_eq_append_getElem (by omega)]
  have htake2 : L.take (i₁ + 1) <+: L.take i₂ := by
    have hmin : min (i₁ + 1) i₂ = i₁ + 1 := min_eq_left (by omega)
    rw [← hmin, ← List.take_take]
    exact List.take_prefix _ _
  obtain ⟨rest, hrest⟩ := htake2
  have hsum : ((L.take i₂).map w).sum = ((L.take (i₁ + 1)).map w).sum + (rest.map w).sum := by
    rw [← hrest, List.map_append, List.sum_append]
  rw [htake1, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton] at hsum
  omega

private def toListAux : ∀ (n : ℕ), ℕ → NatTuple n → List ℕ
  | 0, _, _ => []
  | n + 1, off, p => (off + (ofLex p).1) :: toListAux n (off + (ofLex p).1 + 1) (ofLex p).2

private lemma toListAux_length (n off : ℕ) (x : NatTuple n) : (toListAux n off x).length = n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih => simp [toListAux, ih]

private lemma toListAux_ge (n off : ℕ) (x : NatTuple n) : ∀ u ∈ toListAux n off x, off ≤ u := by
  induction n generalizing off with
  | zero => intro _ h; simp [toListAux] at h
  | succ n ih =>
    intro u hu
    simp only [toListAux, List.mem_cons] at hu
    rcases hu with rfl | hu'
    · omega
    · have := ih (off + (ofLex x).1 + 1) (ofLex x).2 u hu'; omega

private lemma toListAux_strictSorted (n off : ℕ) (x : NatTuple n) :
    StrictSorted (toListAux n off x) := by
  induction n generalizing off with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    exact List.pairwise_cons.mpr ⟨fun u hu => by
      have := toListAux_ge n (off + (ofLex x).1 + 1) (ofLex x).2 u hu; omega,
      ih _ _⟩

private lemma toListAux_first_diff (n off : ℕ) (a b : NatTuple n) (hab : a < b) :
    ∃ r < n, (∀ t < r, (toListAux n off a).getD t 0 = (toListAux n off b).getD t 0) ∧
      (toListAux n off a).getD r 0 < (toListAux n off b).getD r 0 := by
  induction n generalizing off with
  | zero => exact (lt_irrefl _ hab).elim
  | succ n ih =>
    rw [Prod.Lex.lt_iff] at hab
    rcases hab with hlt | ⟨heq, hlt⟩
    · refine ⟨0, by omega, fun _ h => by omega, ?_⟩
      simp [toListAux]; omega
    · obtain ⟨r, hr, hprev, hlt'⟩ := ih (off + (ofLex a).1 + 1) (ofLex a).2 (ofLex b).2 hlt
      refine ⟨r + 1, by omega, fun t ht => ?_, ?_⟩
      · cases t with
        | zero => simp [toListAux, heq]
        | succ t' =>
          have := hprev t' (by omega)
          simpa [toListAux, heq] using this
      · simpa [toListAux, heq] using hlt'

private lemma larson_lemma_3_8 {e : ℕ → ℕ} (he : StrictMono e) (he0 : 1 ≤ e 0) :
    ∃ (X : Set (List ℕ)),
      (∀ x ∈ X, StrictSorted x) ∧
      (∀ j ≥ 1, ∃ f : NatTuple j → List ℕ,
        (∀ a, f a ∈ X) ∧
        (∀ a b, (f a).length = (f b).length) ∧
        (∀ a b, a < b → List.Lex (· < ·) (f a) (f b))) ∧
      (∀ x ∈ X, ∀ y ∈ X, x.length < y.length →
        ∃ l ≥ 1, ∃ zs, FormBody (kaOf l) (kbOf l) x y zs ∧
          ∀ u ∈ zs, e l < u ∧ u ∈ Set.range e) := by
  have he_ge1 : ∀ t, 1 ≤ e t := fun t => le_trans he0 (he.monotone (Nat.zero_le t))
  let dPos (s : ℕ) : ℕ := (stageState e (s - 1)).1
  let dVal (s r : ℕ) : ℕ := e (dPos s + r)
  let aPos (s : ℕ) : ℕ := dPos s + (s + 1)
  let bStart (s : ℕ) : ℕ := aPos s + dVal s 0
  let bLen (p : ℕ × ℕ) : ℕ := dVal p.1 p.2 - dVal p.1 (p.2 - 1)
  let bPos (s j i : ℕ) : ℕ :=
    bStart s + (((pairsBefore s).take ((pairsBefore s).idxOf (j, i))).map bLen).sum
  let dBlk (s : ℕ) : List ℕ := block e (dPos s) (s + 1)
  let aBlk (s : ℕ) : List ℕ := block e (aPos s) (dVal s 0)
  let bBlk (i j s : ℕ) : List ℕ := block e (bPos s j i) (bLen (j, i))
  have hdPos_step : ∀ s ≥ 1,
      dPos (s + 1) = bStart s + ((pairsBefore s).map bLen).sum := by
    intro s hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    dsimp only [dPos, bStart, aPos, dVal, bLen]
    simp only [Nat.add_sub_cancel, add_zero, stageState]
    congr 2
    refine List.map_congr_left fun p hp => ?_
    have hmem := (mem_pairsBefore_iff (s' + 1) p.1 p.2).mp hp
    rw [stageState_tbl_eq e (by omega) (by omega)]
    congr 2
    omega
  have hdPos_ge : ∀ s ≥ 1, 2 * s + 2 ≤ dPos s := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => simp [dPos, stageState]
    | succ s hs ih =>
      rw [hdPos_step s hs]
      have h1 : 1 ≤ dVal s 0 := he_ge1 _
      dsimp only [bStart, aPos]
      omega
  have hdPos_mono : ∀ {s₁ s₂}, 1 ≤ s₁ → s₁ ≤ s₂ → dPos s₁ ≤ dPos s₂ := by
    intro s₁ s₂ hs₁ hle
    induction s₂, hle using Nat.le_induction with
    | base => exact le_refl _
    | succ s₂ hle ih =>
      rw [hdPos_step s₂ (by omega)]
      dsimp only [bStart, aPos]
      omega
  have hbLen_pos : ∀ j i, 1 ≤ i → 1 ≤ bLen (j, i) := by
    intro j i hi
    have hlt : dVal j (i - 1) < dVal j i := he (by omega)
    dsimp only [bLen]; omega
  have hbPos_end_le : ∀ {s j i}, 1 ≤ i → i ≤ j → j < s →
      bPos s j i + bLen (j, i) ≤ dPos (s + 1) := by
    intro s j i hi hij hjs
    have hmem : (j, i) ∈ pairsBefore s := (mem_pairsBefore_iff s j i).mpr ⟨hi, hij, hjs⟩
    have hidx : (pairsBefore s).idxOf (j, i) < (pairsBefore s).length :=
      List.idxOf_lt_length_of_mem hmem
    have hget : (pairsBefore s)[(pairsBefore s).idxOf (j, i)]'hidx = (j, i) :=
      List.getElem_idxOf hidx
    have hsum := list_take_sum_lt (pairsBefore s) bLen hidx (le_refl _)
    rw [hget, List.take_length] at hsum
    rw [hdPos_step s (by omega)]
    dsimp only [bPos]
    omega
  have haPos_end_le_next : ∀ s ≥ 1, aPos s + dVal s 0 ≤ dPos (s + 1) := by
    intro s hs
    rw [hdPos_step s hs]
    dsimp only [bStart]
    omega
  have hbBlk_disj : ∀ {s j₁ i₁ j₂ i₂},
      1 ≤ i₁ → i₁ ≤ j₁ → j₁ < s →
      1 ≤ i₂ → i₂ ≤ j₂ → j₂ < s →
      (j₁, i₁) ≠ (j₂, i₂) →
      ListLt (bBlk i₁ j₁ s) (bBlk i₂ j₂ s) ∨ ListLt (bBlk i₂ j₂ s) (bBlk i₁ j₁ s) := by
    intro s j₁ i₁ j₂ i₂ hi₁ hj₁ hs₁ hi₂ hj₂ hs₂ hne
    have hm1 : (j₁, i₁) ∈ pairsBefore s := (mem_pairsBefore_iff s j₁ i₁).mpr ⟨hi₁, hj₁, hs₁⟩
    have hm2 : (j₂, i₂) ∈ pairsBefore s := (mem_pairsBefore_iff s j₂ i₂).mpr ⟨hi₂, hj₂, hs₂⟩
    have hidx1 : (pairsBefore s).idxOf (j₁, i₁) < (pairsBefore s).length :=
      List.idxOf_lt_length_of_mem hm1
    have hidx2 : (pairsBefore s).idxOf (j₂, i₂) < (pairsBefore s).length :=
      List.idxOf_lt_length_of_mem hm2
    have hidx_ne : (pairsBefore s).idxOf (j₁, i₁) ≠ (pairsBefore s).idxOf (j₂, i₂) := by
      intro heq
      apply hne
      rw [← List.getElem_idxOf hidx1, ← List.getElem_idxOf hidx2]
      congr 1
    rcases lt_or_gt_of_ne hidx_ne with hlt | hgt
    · left
      apply block_lt_block he
      have hsum := list_take_sum_lt (pairsBefore s) bLen hlt (le_of_lt hidx2)
      rw [List.getElem_idxOf hidx1] at hsum
      dsimp only [bPos]; omega
    · right
      apply block_lt_block he
      have hsum := list_take_sum_lt (pairsBefore s) bLen hgt (le_of_lt hidx1)
      rw [List.getElem_idxOf hidx2] at hsum
      dsimp only [bPos]; omega
  -- Define pieces `xPieces j k` for `j ≥ 1`, `StrictSorted k`, `k.length = j`, `∀ t ∈ k, j < t`
  let xPieces (j : ℕ) (k : List ℕ) : List (List ℕ) :=
    aBlk j :: (List.range j).map (fun r => bBlk (r + 1) j (k.getD r 0))
  have hxPieces_len : ∀ j k, (xPieces j k).length = j + 1 := by
    intro j k; simp [xPieces]
  have hxPieces_acc : ∀ j k, 1 ≤ j → StrictSorted k → k.length = j → (∀ t ∈ k, j < t) →
      accLengths 0 (xPieces j k) = dBlk j ∧ (xPieces j k).flatten.length = dVal j j := by
    intro j k hj hks hklen hkgt
    have haux : ∀ r, r ≤ j →
        accLengths 0 (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (k.getD t 0))) =
          block e (dPos j) (r + 1) ∧
        (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (k.getD t 0))).flatten.length =
          dVal j r := by
      intro r
      induction r with
      | zero =>
        intro _
        simp [accLengths, aBlk, block, dVal]
      | succ r ih =>
        intro hr
        obtain ⟨hacc, hflen⟩ := ih (by omega)
        have heq_list :
            aBlk j :: (List.range (r + 1)).map (fun t => bBlk (t + 1) j (k.getD t 0)) =
            (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (k.getD t 0))) ++
            [bBlk (r + 1) j (k.getD r 0)] := by
          rw [List.range_succ, List.map_append, List.map_singleton, List.cons_append]
        have hbl : (bBlk (r + 1) j (k.getD r 0)).length = dVal j (r + 1) - dVal j r := by
          simp [bBlk, block_length, bLen]
        have hlt : dVal j r < dVal j (r + 1) := he (by omega)
        have hsum : dVal j r + (dVal j (r + 1) - dVal j r) = dVal j (r + 1) := by omega
        refine ⟨?_, ?_⟩
        · rw [heq_list, accLengths_append, hacc, hflen]
          simp only [zero_add, accLengths, hbl, hsum]
          simp only [block, List.range_succ, List.map_append, List.map_singleton, dVal]
        · rw [heq_list, List.flatten_append, List.flatten_singleton, List.length_append, hflen,
            hbl, hsum]
    exact haux j (le_refl j)
  have hxPieces_sort : ∀ j k, 1 ≤ j → StrictSorted k → k.length = j → (∀ t ∈ k, j < t) →
      StrictSorted (xPieces j k).flatten := by
    intro j k hj hks hklen hkgt
    have hk_get : ∀ r (hr : r < j), k.getD r 0 = k[r]'(by omega) := fun r hr => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : r < k.length)]
    have hk_lt : ∀ r₁ r₂, r₁ < r₂ → r₂ < j → k.getD r₁ 0 < k.getD r₂ 0 := by
      intro r₁ r₂ h12 h2
      rw [hk_get r₁ (by omega), hk_get r₂ h2]
      exact List.pairwise_iff_getElem.mp hks r₁ r₂ (by omega) (by omega) h12
    have hk_gtj : ∀ r, r < j → j < k.getD r 0 := by
      intro r hr
      rw [hk_get r hr]
      exact hkgt _ (List.getElem_mem _)
    have haux : ∀ r, r ≤ j →
        StrictSorted (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (k.getD t 0))).flatten := by
      intro r
      induction r with
      | zero => intro _; simp [aBlk, block_strictSorted he]
      | succ r ih =>
        intro hr
        have heq_list :
            aBlk j :: (List.range (r + 1)).map (fun t => bBlk (t + 1) j (k.getD t 0)) =
            (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (k.getD t 0))) ++
            [bBlk (r + 1) j (k.getD r 0)] := by
          rw [List.range_succ, List.map_append, List.map_singleton, List.cons_append]
        rw [heq_list, List.flatten_append, List.flatten_singleton]
        refine strictSorted_append (ih (by omega)) (block_strictSorted he _ _) ?_
        intro u hu v hv
        rw [List.flatten_cons, List.mem_append] at hu
        rcases hu with hua | hub
        · have hkr : j < k.getD r 0 := hk_gtj r (by omega)
          have h1 : aPos j + dVal j 0 ≤ dPos (k.getD r 0) :=
            le_trans (haPos_end_le_next j hj) (hdPos_mono (by omega) hkr)
          have h2 : dPos (k.getD r 0) ≤ bPos (k.getD r 0) j (r + 1) := by
            dsimp only [bPos, bStart, aPos]; omega
          exact block_lt_block he (le_trans h1 h2) u hua v hv
        · rcases List.mem_flatten.mp hub with ⟨w, hw, huw⟩
          rcases List.mem_map.mp hw with ⟨t, ht, rfl⟩
          rw [List.mem_range] at ht
          have htk : k.getD t 0 < k.getD r 0 := hk_lt t r ht (by omega)
          have h1 : bPos (k.getD t 0) j (t + 1) + bLen (j, t + 1) ≤ dPos (k.getD t 0 + 1) :=
            hbPos_end_le (by omega) (by omega) (hk_gtj t (by omega))
          have h2 : dPos (k.getD t 0 + 1) ≤ dPos (k.getD r 0) :=
            hdPos_mono (by omega) htk
          have h3 : dPos (k.getD r 0) ≤ bPos (k.getD r 0) j (r + 1) := by
            dsimp only [bPos, bStart, aPos]; omega
          exact block_lt_block he (le_trans h1 (le_trans h2 h3)) u huw v hv
    exact haux j (le_refl j)
  let X : Set (List ℕ) := { x | ∃ j ≥ 1, ∃ k : List ℕ,
    StrictSorted k ∧ k.length = j ∧ (∀ t ∈ k, j < t) ∧ x = (xPieces j k).flatten }
  refine ⟨X, ?_, ?_, ?_⟩
  · rintro x ⟨j, hj, k, hks, hklen, hkgt, rfl⟩
    exact hxPieces_sort j k hj hks hklen hkgt
  · -- Order-type `ω ^ j` embedding for every `j ≥ 1`
    intro j hj
    refine ⟨fun a => (xPieces j (toListAux j (j + 1) a)).flatten,
      fun a => ⟨j, hj, toListAux j (j + 1) a, toListAux_strictSorted j (j + 1) a,
        toListAux_length j (j + 1) a,
        fun t ht => by have := toListAux_ge j (j + 1) a t ht; omega, rfl⟩,
      fun a b => ?_, fun a b hab => ?_⟩
    · have h1 := (hxPieces_acc j (toListAux j (j + 1) a) hj (toListAux_strictSorted j (j + 1) a)
        (toListAux_length j (j + 1) a)
        (fun t ht => by have := toListAux_ge j (j + 1) a t ht; omega)).2
      have h2 := (hxPieces_acc j (toListAux j (j + 1) b) hj (toListAux_strictSorted j (j + 1) b)
        (toListAux_length j (j + 1) b)
        (fun t ht => by have := toListAux_ge j (j + 1) b t ht; omega)).2
      rw [h1, h2]
    · obtain ⟨r, hr, hprev, hlt_r⟩ := toListAux_first_diff j (j + 1) a b hab
      let ka := toListAux j (j + 1) a
      let kb := toListAux j (j + 1) b
      have hsplit : ∀ k : List ℕ,
          (xPieces j k).flatten =
            (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (k.getD t 0))).flatten ++
            bBlk (r + 1) j (k.getD r 0) ++
            ((List.range (j - r - 1)).map (fun t => bBlk (r + 1 + t + 1) j (k.getD (r + 1 + t) 0))).flatten := by
        intro k
        have hrj : List.range j = List.range r ++ [r] ++ (List.range (j - r - 1)).map (fun t => r + 1 + t) := by
          apply List.ext_getElem
          · simp; omega
          · intro i h1 h2
            simp only [List.getElem_range]
            by_cases hi1 : i < r
            · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
              simp
            · by_cases hi2 : i = r
              · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
                simp [hi2]
              · rw [List.getElem_append_right (by simp; omega)]
                simp; omega
        dsimp only [xPieces]
        rw [hrj, List.map_append, List.map_append, List.map_singleton, List.map_map]
        simp only [List.flatten_cons, List.flatten_append, List.flatten_nil, List.nil_append,
          List.append_assoc, Function.comp_def]
      have hpre_eq :
          (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (ka.getD t 0))).flatten =
          (aBlk j :: (List.range r).map (fun t => bBlk (t + 1) j (kb.getD t 0))).flatten := by
        congr 2
        refine List.map_congr_left fun t ht => ?_
        rw [List.mem_range] at ht
        rw [hprev t ht]
      change List.Lex (· < ·) (xPieces j ka).flatten (xPieces j kb).flatten
      rw [hsplit ka, hsplit kb, hpre_eq]
      have hlex_pre : ∀ (p u v : List ℕ), List.Lex (· < ·) u v → List.Lex (· < ·) (p ++ u) (p ++ v) := by
        intro p u v huv
        induction p with
        | nil => exact huv
        | cons x p ihp => exact List.Lex.cons ihp
      rw [List.append_assoc, List.append_assoc]
      apply hlex_pre
      have hbl_ne1 : bBlk (r + 1) j (ka.getD r 0) ≠ [] :=
        block_ne_nil (by have := hbLen_pos j (r + 1) (by omega); omega)
      have hbl_ne2 : bBlk (r + 1) j (kb.getD r 0) ≠ [] :=
        block_ne_nil (by have := hbLen_pos j (r + 1) (by omega); omega)
      have hka_gt : j < ka.getD r 0 := by
        have hlen_ka : r < ka.length := by rw [toListAux_length]; omega
        have hget : ka.getD r 0 = ka[r]'hlen_ka := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_ka]
        rw [hget]
        have := toListAux_ge j (j + 1) a (ka[r]'hlen_ka) (List.getElem_mem hlen_ka)
        omega
      have hbl_lt : ListLt (bBlk (r + 1) j (ka.getD r 0)) (bBlk (r + 1) j (kb.getD r 0)) := by
        apply block_lt_block he
        have h1 : bPos (ka.getD r 0) j (r + 1) + bLen (j, r + 1) ≤ dPos (ka.getD r 0 + 1) :=
          hbPos_end_le (by omega) (by omega) hka_gt
        have h2 : dPos (ka.getD r 0 + 1) ≤ dPos (kb.getD r 0) :=
          hdPos_mono (by omega) hlt_r
        have h3 : dPos (kb.getD r 0) ≤ bPos (kb.getD r 0) j (r + 1) := by
          dsimp only [bPos, bStart, aPos]; omega
        exact le_trans h1 (le_trans h2 h3)
      cases h1 : bBlk (r + 1) j (ka.getD r 0) with
      | nil => exact absurd h1 hbl_ne1
      | cons u₁ t₁ =>
        cases h2 : bBlk (r + 1) j (kb.getD r 0) with
        | nil => exact absurd h2 hbl_ne2
        | cons u₂ t₂ =>
          simp only [List.cons_append]
          exact List.Lex.rel (hbl_lt u₁ (by rw [h1]; simp) u₂ (by rw [h2]; simp))
  · -- Unequal-length pairs in `X` admit valid `FormBody` with `e l < zs ⊆ range e`
    rintro x ⟨j, hj, k, hks, hklen, hkgt, rfl⟩ y ⟨r, hr, p, hps, hplen, hpgt, rfl⟩ hxy_len
    have haccX := hxPieces_acc j k hj hks hklen hkgt
    have haccY := hxPieces_acc r p hr hps hplen hpgt
    have hjr : j < r := by
      rw [haccX.2, haccY.2] at hxy_len
      by_contra hge
      have hle : r ≤ j := by omega
      have : dVal r r ≤ dVal j j := he.monotone (by have := hdPos_mono hr hle; omega)
      omega
    let P := xPieces j k
    let Q := xPieces r p
    have hP_ne : P ≠ [] := List.cons_ne_nil _ _
    have hQ_ne : Q ≠ [] := List.cons_ne_nil _ _
    have hP_prop : ∀ u ∈ P, u ≠ [] ∧ StrictSorted u := by
      intro u hu
      simp only [P, xPieces, List.mem_cons, List.mem_map, List.mem_range] at hu
      rcases hu with rfl | ⟨t, ht, rfl⟩
      · exact ⟨block_ne_nil (by dsimp only [dVal]; rw [add_zero]; have := he_ge1 (dPos j); omega),
          block_strictSorted he _ _⟩
      · exact ⟨block_ne_nil (by have := hbLen_pos j (t + 1) (by omega); omega), block_strictSorted he _ _⟩
    have hQ_prop : ∀ v ∈ Q, v ≠ [] ∧ StrictSorted v := by
      intro v hv
      simp only [Q, xPieces, List.mem_cons, List.mem_map, List.mem_range] at hv
      rcases hv with rfl | ⟨t, ht, rfl⟩
      · exact ⟨block_ne_nil (by dsimp only [dVal]; rw [add_zero]; have := he_ge1 (dPos r); omega),
          block_strictSorted he _ _⟩
      · exact ⟨block_ne_nil (by have := hbLen_pos r (t + 1) (by omega); omega), block_strictSorted he _ _⟩
    have hk_gtj : ∀ t < j, j < k.getD t 0 := fun t ht => by
      have hget : k.getD t 0 = k[t]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < k.length)]
      rw [hget]; exact hkgt _ (List.getElem_mem _)
    have hp_gtr : ∀ t < r, r < p.getD t 0 := fun t ht => by
      have hget : p.getD t 0 = p[t]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < p.length)]
      rw [hget]; exact hpgt _ (List.getElem_mem _)
    have hcomp_PQ : ∀ u ∈ P, ∀ v ∈ Q, ListLt u v ∨ ListLt v u := by
      intro u hu v hv
      simp only [P, Q, xPieces, List.mem_cons, List.mem_map, List.mem_range] at hu hv
      rcases hu with rfl | ⟨t₁, ht₁, rfl⟩ <;> rcases hv with rfl | ⟨t₂, ht₂, rfl⟩
      · left; apply block_lt_block he
        exact le_trans (haPos_end_le_next j hj) (le_trans (hdPos_mono (by omega) hjr) (by dsimp only [aPos]; omega))
      · left; apply block_lt_block he
        have hp2 := hp_gtr t₂ ht₂
        exact le_trans (haPos_end_le_next j hj)
          (le_trans (hdPos_mono (by omega) (by omega : j + 1 ≤ p.getD t₂ 0))
            (by dsimp only [bPos, bStart, aPos]; omega))
      · have hk1 := hk_gtj t₁ ht₁
        by_cases hkr : k.getD t₁ 0 < r
        · left; apply block_lt_block he
          exact le_trans (hbPos_end_le (by omega) (by omega) hk1)
            (le_trans (hdPos_mono (by omega) hkr) (by dsimp only [aPos]; omega))
        · right; apply block_lt_block he
          by_cases hkeq : k.getD t₁ 0 = r
          · rw [hkeq]; dsimp only [bPos, bStart]; omega
          · exact le_trans (haPos_end_le_next r hr)
              (le_trans (hdPos_mono (by omega) (by omega : r + 1 ≤ k.getD t₁ 0))
                (by dsimp only [bPos, bStart, aPos]; omega))
      · have hk1 := hk_gtj t₁ ht₁
        have hp2 := hp_gtr t₂ ht₂
        rcases lt_trichotomy (k.getD t₁ 0) (p.getD t₂ 0) with hlt | heq | hgt
        · left; apply block_lt_block he
          exact le_trans (hbPos_end_le (by omega) (by omega) hk1)
            (le_trans (hdPos_mono (by omega) hlt) (by dsimp only [bPos, bStart, aPos]; omega))
        · rw [heq]
          exact hbBlk_disj (by omega) (by omega) (heq ▸ hk1) (by omega) (by omega) hp2
            (fun h => by have := (Prod.mk.inj h).1; omega)
        · right; apply block_lt_block he
          exact le_trans (hbPos_end_le (by omega) (by omega) hp2)
            (le_trans (hdPos_mono (by omega) hgt) (by dsimp only [bPos, bStart, aPos]; omega))
    have hhead_PQ : ∀ (h1 : P ≠ []) (h2 : Q ≠ []), ListLt (P.head h1) (Q.head h2) := by
      intro _ _
      simp only [P, Q, xPieces, List.head_cons]
      apply block_lt_block he
      exact le_trans (haPos_end_le_next j hj) (le_trans (hdPos_mono (by omega) hjr) (by dsimp only [aPos]; omega))
    obtain ⟨Ps, Qs, hPs_flat, hQs_flat, hPs_ne, hQs_ne, hQs_len1, hQs_le_Ps, hPs_le_Qs1,
        hinter_sort, hPs_head_lt⟩ :=
      mergeBlocks (P.length + Q.length) P Q (le_refl _) hP_ne hQ_ne hP_prop hQ_prop
        (hxPieces_sort j k hj hks hklen hkgt) (hxPieces_sort r p hr hps hplen hpgt)
        hcomp_PQ hhead_PQ
    let ka := Ps.length
    let kb := Qs.length
    let l := ka + kb - 1
    have hl1 : 1 ≤ l := by dsimp only [l, ka, kb]; omega
    have hka_eq : kaOf l = ka := by dsimp only [kaOf, l, ka, kb]; omega
    have hkb_eq : kbOf l = kb := by dsimp only [kbOf, l, ka, kb]; omega
    have hka_le : ka ≤ j + 1 := by
      have hlen_le : ∀ (Gs : List (List (List ℕ))), (∀ G ∈ Gs, G ≠ []) → Gs.length ≤ Gs.flatten.length := by
        intro Gs
        induction Gs with
        | nil => intro _; simp
        | cons G Gs' ihG =>
          intro hGs
          have hG1 : 1 ≤ G.length := List.length_pos_of_ne_nil (hGs G (by simp))
          have hih := ihG (fun H hH => hGs H (by simp [hH]))
          simp only [List.length_cons, List.flatten_cons, List.length_append]
          omega
      have := hlen_le Ps hPs_ne
      rw [hPs_flat, hxPieces_len] at this
      exact this
    have hl_le : l ≤ 2 * j + 1 := by dsimp only [l, ka, kb]; omega
    have hPs_nonempty : Ps ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hQs_nonempty : Qs ≠ [] := List.ne_nil_of_length_pos (by omega)
    cases hPs_cons : Ps with
    | nil => exact absurd hPs_cons hPs_nonempty
    | cons P0 Ps' =>
      cases hQs_cons : Qs with
      | nil => exact absurd hQs_cons hQs_nonempty
      | cons Q0 Qs' =>
        let A0 := P0.flatten
        let As := Ps'.map List.flatten
        let B0 := Q0.flatten
        let Bs := Qs'.map List.flatten
        let c := accLengths 0 (A0 :: As)
        let d := accLengths 0 (B0 :: Bs)
        let zs := c ++ A0 ++ d ++ B0 ++ interact As Bs
        have hc_sub : ∀ u ∈ c, u ∈ dBlk j := by
          intro u hu
          have h := accLengths_map_flatten_subset 0 (P0 :: Ps') (hPs_cons ▸ hPs_ne) u
            (by simpa [c, A0, As] using hu)
          rw [← hPs_cons, hPs_flat, haccX.1] at h
          exact h
        have hd_sub : ∀ u ∈ d, u ∈ dBlk r := by
          intro u hu
          have h := accLengths_map_flatten_subset 0 (Q0 :: Qs') (hQs_cons ▸ hQs_ne) u
            (by simpa [d, B0, Bs] using hu)
          rw [← hQs_cons, hQs_flat, haccY.1] at h
          exact h
        have hA_ne : ∀ u ∈ A0 :: As, u ≠ [] := by
          intro u hu
          have hmem : ∃ G ∈ Ps, u = G.flatten := by
            rw [hPs_cons]
            rcases List.mem_cons.mp hu with rfl | hu'
            · exact ⟨P0, by simp, rfl⟩
            · rcases List.mem_map.mp hu' with ⟨G, hG, rfl⟩
              exact ⟨G, by simp [hG], rfl⟩
          rcases hmem with ⟨G, hG, rfl⟩
          have hGne : G ≠ [] := hPs_ne G hG
          cases hGeq : G with
          | nil => exact absurd hGeq hGne
          | cons g G' =>
            have hgP : g ∈ P := hPs_flat ▸ List.mem_flatten.mpr ⟨G, hG, by rw [hGeq]; simp⟩
            exact List.append_ne_nil_of_left_ne_nil (hP_prop g hgP).1 _
        have hB_ne : ∀ v ∈ B0 :: Bs, v ≠ [] := by
          intro v hv
          have hmem : ∃ G ∈ Qs, v = G.flatten := by
            rw [hQs_cons]
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact ⟨Q0, by simp, rfl⟩
            · rcases List.mem_map.mp hv' with ⟨G, hG, rfl⟩
              exact ⟨G, by simp [hG], rfl⟩
          rcases hmem with ⟨G, hG, rfl⟩
          have hGne : G ≠ [] := hQs_ne G hG
          cases hGeq : G with
          | nil => exact absurd hGeq hGne
          | cons g G' =>
            have hgQ : g ∈ Q := hQs_flat ▸ List.mem_flatten.mpr ⟨G, hG, by rw [hGeq]; simp⟩
            exact List.append_ne_nil_of_left_ne_nil (hQ_prop g hgQ).1 _
        have hc_sort : StrictSorted c := strictSorted_accLengths 0 (A0 :: As) hA_ne
        have hd_sort : StrictSorted d := strictSorted_accLengths 0 (B0 :: Bs) hB_ne
        -- Every element of `A0` is `< dBlk r` because every block `u ∈ P0` has `ListLt u (aBlk r)`
        have hA0_lt_d : ListLt A0 d := by
          intro a ha b hb
          have hb_dr : b ∈ dBlk r := hd_sub b hb
          rcases List.mem_flatten.mp ha with ⟨u, hu, hau⟩
          have hu_lt_ar : ListLt u (aBlk r) := by
            have := hPs_head_lt hPs_nonempty hQ_ne u (by simp [hPs_cons, hu])
            simpa [Q, xPieces] using this
          have huP : u ∈ P := hPs_flat ▸ List.mem_flatten.mpr ⟨P0, by rw [hPs_cons]; simp, hu⟩
          simp only [P, xPieces, List.mem_cons, List.mem_map, List.mem_range] at huP
          rcases huP with rfl | ⟨t, ht, rfl⟩
          · exact block_lt_block he
              (le_trans (haPos_end_le_next j hj) (hdPos_mono (by omega) hjr)) a hau b hb_dr
          · have hkt_lt_r : k.getD t 0 < r := by
              by_contra hge
              have hkr : r ≤ k.getD t 0 := by omega
              have hnot : ListLt (aBlk r) (bBlk (t + 1) j (k.getD t 0)) := by
                apply block_lt_block he
                by_cases hkeq : k.getD t 0 = r
                · rw [hkeq]; dsimp only [bPos, bStart]; omega
                · exact le_trans (haPos_end_le_next r hr)
                    (le_trans (hdPos_mono (by omega) (by omega : r + 1 ≤ k.getD t 0))
                      (by dsimp only [bPos, bStart, aPos]; omega))
              have hne_ar : aBlk r ≠ [] :=
                block_ne_nil (by dsimp only [dVal]; rw [add_zero]; have := he_ge1 (dPos r); omega)
              cases har : aBlk r with
              | nil => exact absurd har hne_ar
              | cons v _ =>
                exact lt_asymm (hu_lt_ar a hau v (by rw [har]; simp))
                  (hnot v (by rw [har]; simp) a hau)
            exact block_lt_block he
              (le_trans (hbPos_end_le (by omega) (by omega) (hk_gtj t ht))
                (hdPos_mono (by omega) hkt_lt_r)) a hau b hb_dr
        have hc_lt_A0 : ListLt c A0 := by
          intro a ha b hb
          have ha_dj : a ∈ dBlk j := hc_sub a ha
          rcases List.mem_flatten.mp hb with ⟨u, hu, hbu⟩
          have huP : u ∈ P := hPs_flat ▸ List.mem_flatten.mpr ⟨P0, by rw [hPs_cons]; simp, hu⟩
          simp only [P, xPieces, List.mem_cons, List.mem_map, List.mem_range] at huP
          rcases huP with rfl | ⟨t, ht, rfl⟩
          · exact block_lt_block he (by dsimp only [aPos]; omega) a ha_dj b hbu
          · exact block_lt_block he (by
              have h1 : dPos j + (j + 1) ≤ dPos (j + 1) :=
                le_trans (by dsimp only [aPos]; omega) (haPos_end_le_next j hj)
              have h2 : dPos (j + 1) ≤ dPos (k.getD t 0) :=
                hdPos_mono (by omega) (hk_gtj t ht)
              have h3 : dPos (k.getD t 0) ≤ bPos (k.getD t 0) j (t + 1) := by
                dsimp only [bPos, bStart, aPos]; omega
              exact le_trans h1 (le_trans h2 h3)) a ha_dj b hbu
        have hd_lt_B0 : ListLt d B0 := by
          intro a ha b hb
          have ha_dr : a ∈ dBlk r := hd_sub a ha
          rcases List.mem_flatten.mp hb with ⟨v, hv, hbv⟩
          have hvQ : v ∈ Q := hQs_flat ▸ List.mem_flatten.mpr ⟨Q0, by rw [hQs_cons]; simp, hv⟩
          simp only [Q, xPieces, List.mem_cons, List.mem_map, List.mem_range] at hvQ
          rcases hvQ with rfl | ⟨t, ht, rfl⟩
          · exact block_lt_block he (by dsimp only [aPos]; omega) a ha_dr b hbv
          · exact block_lt_block he (by
              have h1 : dPos r + (r + 1) ≤ dPos (r + 1) :=
                le_trans (by dsimp only [aPos]; omega) (haPos_end_le_next r hr)
              have h2 : dPos (r + 1) ≤ dPos (p.getD t 0) :=
                hdPos_mono (by omega) (hp_gtr t ht)
              have h3 : dPos (p.getD t 0) ≤ bPos (p.getD t 0) r (t + 1) := by
                dsimp only [bPos, bStart, aPos]; omega
              exact le_trans h1 (le_trans h2 h3)) a ha_dr b hbv
        have hinter_eq : interact (Ps.map List.flatten) (Qs.map List.flatten) =
            A0 ++ B0 ++ interact As Bs := by
          simp [hPs_cons, hQs_cons, A0, As, B0, Bs, interact]
        rw [hinter_eq] at hinter_sort
        have hA0_sort : StrictSorted A0 :=
          (List.pairwise_append.mp (List.pairwise_append.mp hinter_sort).1).1
        have hB0_inter_sort : StrictSorted (B0 ++ interact As Bs) := by
          rw [List.append_assoc] at hinter_sort
          exact (List.pairwise_append.mp hinter_sort).2.1
        have hB0_lt_inter : ListLt B0 (interact As Bs) :=
          (List.pairwise_append.mp hB0_inter_sort).2.2
        have hB0_ne : B0 ≠ [] := hB_ne B0 (by simp)
        have hA0_ne : A0 ≠ [] := hA_ne A0 (by simp)
        have hd_ne : d ≠ [] := by simp [d, accLengths]
        have hzs_sort : StrictSorted zs := by
          have h3 : StrictSorted (d ++ (B0 ++ interact As Bs)) :=
            strictSorted_append hd_sort hB0_inter_sort
              (listLt_append_right.mpr ⟨hd_lt_B0, listLt_trans hB0_ne hd_lt_B0 hB0_lt_inter⟩)
          have h2 : StrictSorted (A0 ++ (d ++ (B0 ++ interact As Bs))) :=
            strictSorted_append hA0_sort h3
              (listLt_append_right.mpr ⟨hA0_lt_d,
                listLt_trans hd_ne hA0_lt_d
                  (listLt_append_right.mpr ⟨hd_lt_B0, listLt_trans hB0_ne hd_lt_B0 hB0_lt_inter⟩)⟩)
          have h1 : StrictSorted (c ++ (A0 ++ (d ++ (B0 ++ interact As Bs)))) :=
            strictSorted_append hc_sort h2
              (listLt_append_right.mpr ⟨hc_lt_A0,
                listLt_trans hA0_ne hc_lt_A0
                  (listLt_append_right.mpr ⟨hA0_lt_d,
                    listLt_trans hd_ne hA0_lt_d
                      (listLt_append_right.mpr ⟨hd_lt_B0, listLt_trans hB0_ne hd_lt_B0 hB0_lt_inter⟩)⟩)⟩)
          simpa [zs, List.append_assoc] using h1
        have hA_flat : (A0 :: As).flatten = P.flatten := by
          have h1 : (Ps.map List.flatten).flatten = Ps.flatten.flatten := flatten_map_flatten Ps
          rw [hPs_flat, hPs_cons] at h1
          simpa [A0, As] using h1
        have hB_flat : (B0 :: Bs).flatten = Q.flatten := by
          have h1 : (Qs.map List.flatten).flatten = Qs.flatten.flatten := flatten_map_flatten Qs
          rw [hQs_flat, hQs_cons] at h1
          simpa [B0, Bs] using h1
        have hzs_gt : ∀ u ∈ zs, e l < u ∧ u ∈ Set.range e := by
          have h_dj_gt : ∀ u ∈ dBlk j, e l < u ∧ u ∈ Set.range e := by
            intro u hu
            rcases block_mem_iff.mp hu with ⟨t, _, rfl⟩
            have hdge := hdPos_ge j hj
            exact ⟨he (by omega), ⟨dPos j + t, rfl⟩⟩
          have h_c_gt : ∀ u ∈ c, e l < u ∧ u ∈ Set.range e := fun u hu => h_dj_gt u (hc_sub u hu)
          have h_d_gt : ∀ u ∈ d, e l < u ∧ u ∈ Set.range e := by
            intro u hu
            rcases block_mem_iff.mp (hd_sub u hu) with ⟨t, _, rfl⟩
            have hdge := hdPos_ge r hr
            exact ⟨he (by omega), ⟨dPos r + t, rfl⟩⟩
          have h_P_gt : ∀ u ∈ P.flatten, e l < u ∧ u ∈ Set.range e := by
            intro u hu
            rcases List.mem_flatten.mp hu with ⟨w, hw, huw⟩
            simp only [P, xPieces, List.mem_cons, List.mem_map, List.mem_range] at hw
            rcases hw with rfl | ⟨t, ht, rfl⟩
            · rcases block_mem_iff.mp huw with ⟨q, _, rfl⟩
              have hdge := hdPos_ge j hj
              exact ⟨he (by dsimp only [aPos]; omega), ⟨aPos j + q, rfl⟩⟩
            · rcases block_mem_iff.mp huw with ⟨q, _, rfl⟩
              have hkt := hk_gtj t ht
              have hdge := hdPos_ge (k.getD t 0) (by omega)
              exact ⟨he (by dsimp only [bPos, bStart, aPos]; omega), ⟨bPos (k.getD t 0) j (t + 1) + q, rfl⟩⟩
          have h_Q_gt : ∀ u ∈ Q.flatten, e l < u ∧ u ∈ Set.range e := by
            intro u hu
            rcases List.mem_flatten.mp hu with ⟨w, hw, huw⟩
            simp only [Q, xPieces, List.mem_cons, List.mem_map, List.mem_range] at hw
            rcases hw with rfl | ⟨t, ht, rfl⟩
            · rcases block_mem_iff.mp huw with ⟨q, _, rfl⟩
              have hdge := hdPos_ge r hr
              exact ⟨he (by dsimp only [aPos]; omega), ⟨aPos r + q, rfl⟩⟩
            · rcases block_mem_iff.mp huw with ⟨q, _, rfl⟩
              have hpt := hp_gtr t ht
              have hdge := hdPos_ge (p.getD t 0) (by omega)
              exact ⟨he (by dsimp only [bPos, bStart, aPos]; omega), ⟨bPos (p.getD t 0) r (t + 1) + q, rfl⟩⟩
          intro u hu
          simp only [zs, List.mem_append] at hu
          rcases hu with (((h1 | h2) | h3) | h4) | h5
          · exact h_c_gt u h1
          · exact h_P_gt u (by rw [← hA_flat, List.flatten_cons]; exact List.mem_append_left _ h2)
          · exact h_d_gt u h3
          · exact h_Q_gt u (by rw [← hB_flat, List.flatten_cons]; exact List.mem_append_left _ h4)
          · rcases (mem_interact_iff As Bs u).mp h5 with ⟨w, hw, huw⟩ | ⟨w, hw, huw⟩
            · exact h_P_gt u (by rw [← hA_flat, List.flatten_cons]; exact List.mem_append_right _ (List.mem_flatten.mpr ⟨w, hw, huw⟩))
            · exact h_Q_gt u (by rw [← hB_flat, List.flatten_cons]; exact List.mem_append_right _ (List.mem_flatten.mpr ⟨w, hw, huw⟩))
        refine ⟨l, hl1, zs, ?_, hzs_gt⟩
        refine ⟨A0, As, B0, Bs, hxy_len, hA_flat.symm, hB_flat.symm, hA_ne, hB_ne,
          by simp [As, hka_eq, ka, hPs_cons], by simp [Bs, hkb_eq, kb, hQs_cons], rfl, hzs_sort⟩

/- ### Section 6: Canonical `ω ^ ω` Model `W`, Main Theorem, and Universe Lifting -/

private structure W where
  len : ℕ
  tuple : NatTuple len

private def wLt (x y : W) : Prop :=
  x.len < y.len ∨ ∃ h : x.len = y.len, h ▸ x.tuple < y.tuple

private instance : LT W := ⟨wLt⟩
private instance : LE W := ⟨fun x y => x = y ∨ wLt x y⟩

private lemma wLt_irrefl (x : W) : ¬ (x < x) := by
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

private lemma wLt_trans {x y z : W} (hxy : x < y) (hyz : y < z) : x < z := by
  rcases x with ⟨nx, tx⟩
  rcases y with ⟨ny, ty⟩
  rcases z with ⟨nz, tz⟩
  rcases hxy with h1 | ⟨heq1, h1⟩ <;> rcases hyz with h2 | ⟨heq2, h2⟩
  · exact Or.inl (lt_trans h1 h2)
  · dsimp only at heq2; subst heq2; exact Or.inl h1
  · dsimp only at heq1; subst heq1; exact Or.inl h2
  · dsimp only at heq1 h1 heq2 h2; subst heq1; subst heq2; exact Or.inr ⟨rfl, lt_trans h1 h2⟩

private lemma wLt_trichotomy (x y : W) : x < y ∨ x = y ∨ y < x := by
  rcases x with ⟨nx, tx⟩
  rcases y with ⟨ny, ty⟩
  rcases lt_trichotomy nx ny with hlt | rfl | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases lt_trichotomy tx ty with hlt | rfl | hgt
    · exact Or.inl (Or.inr ⟨rfl, hlt⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hgt⟩))
  · exact Or.inr (Or.inr (Or.inl hgt))

private noncomputable instance : LinearOrder W where
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | h1
    · exact hyz
    · rcases hyz with rfl | h2
      · exact Or.inr h1
      · exact Or.inr (wLt_trans h1 h2)
  le_antisymm x y hxy hyx := by
    rcases hxy with rfl | h1
    · rfl
    · rcases hyx with rfl | h2
      · rfl
      · exact (wLt_irrefl x (wLt_trans h1 h2)).elim
  le_total x y := by
    rcases wLt_trichotomy x y with h | rfl | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr h)
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (rfl | h2)
      · exact wLt_irrefl _ h
      · exact wLt_irrefl _ (wLt_trans h h2)
    · rintro ⟨rfl | h, hnot⟩
      · exact (hnot (Or.inl rfl)).elim
      · exact h
  toDecidableLE := Classical.decRel _

private instance : WellFoundedLT W := by
  constructor
  refine ⟨fun ⟨n, t⟩ => ?_⟩
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    induction t using WellFounded.induction (wellFounded_lt (α := NatTuple n)) with
    | h t iht =>
      refine Acc.intro (⟨n, t⟩ : W) fun y hlt => ?_
      rcases y with ⟨m, s⟩
      rcases hlt with hmn | ⟨heq, hst⟩
      · exact ihn m hmn s
      · dsimp only at heq hst; subst heq; exact iht s hst

private def toTupleAux : ℕ → ∀ l : List ℕ, NatTuple l.length
  | _, [] => PUnit.unit
  | off, a :: t => toLex (a - off, toTupleAux (a + 1) t)

private lemma toListAux_toTupleAux :
    ∀ (l : List ℕ) (off : ℕ), StrictSorted l → (∀ u ∈ l, off ≤ u) →
      toListAux l.length off (toTupleAux off l) = l
  | [], _, _, _ => rfl
  | a :: t, off, hs, hge => by
    have ha : off ≤ a := hge a (by simp)
    have hts : StrictSorted t := (List.pairwise_cons.mp hs).2
    have htge : ∀ u ∈ t, a + 1 ≤ u := fun u hu => by
      have := (List.pairwise_cons.mp hs).1 u hu; omega
    simp only [List.length_cons, toTupleAux, toListAux, ofLex_toLex, Nat.add_sub_of_le ha]
    congr 1
    exact toListAux_toTupleAux t (a + 1) hts htge

private lemma list_lex_cons_iff {a b : ℕ} {s t : List ℕ} :
    List.Lex (· < ·) (a :: s) (b :: t) ↔ a < b ∨ (a = b ∧ List.Lex (· < ·) s t) := by
  constructor
  · intro h
    cases h with
    | rel hlt => exact Or.inl hlt
    | cons hrest => exact Or.inr ⟨rfl, hrest⟩
  · rintro (hlt | ⟨rfl, hrest⟩)
    · exact List.Lex.rel hlt
    · exact List.Lex.cons hrest

private lemma toListAux_lt_iff (n off : ℕ) (x y : NatTuple n) :
    x < y ↔ List.Lex (· < ·) (toListAux n off x) (toListAux n off y) := by
  induction n generalizing off with
  | zero =>
    constructor
    · intro h; exact (lt_irrefl _ h).elim
    · intro h; cases h
  | succ n ih =>
    rw [Prod.Lex.lt_iff]
    simp only [toListAux, list_lex_cons_iff]
    constructor
    · rintro (hlt | ⟨heq, hlt⟩)
      · exact Or.inl (by omega)
      · refine Or.inr ⟨by omega, ?_⟩
        rw [heq]
        exact (ih (off + (ofLex y).1 + 1) (ofLex x).2 (ofLex y).2).mp hlt
    · rintro (hlt | ⟨heq, hrest⟩)
      · exact Or.inl (by omega)
      · have h1 : (ofLex x).1 = (ofLex y).1 := by omega
        refine Or.inr ⟨h1, (ih (off + (ofLex x).1 + 1) (ofLex x).2 (ofLex y).2).mpr ?_⟩
        simpa [h1] using hrest

private def wToList (w : W) : List ℕ := toListAux w.len 0 w.tuple

private def listToW (l : List ℕ) : W := ⟨l.length, toTupleAux 0 l⟩

private lemma wToList_sorted (w : W) : StrictSorted (wToList w) :=
  toListAux_strictSorted w.len 0 w.tuple

private lemma wToList_length (w : W) : (wToList w).length = w.len :=
  toListAux_length w.len 0 w.tuple

private lemma wToList_listToW {l : List ℕ} (hl : StrictSorted l) : wToList (listToW l) = l :=
  toListAux_toTupleAux l 0 hl (fun _ _ => Nat.zero_le _)

private lemma w_lt_iff_lex (x y : W) :
    x < y ↔ (wToList x).length < (wToList y).length ∨
      ((wToList x).length = (wToList y).length ∧ List.Lex (· < ·) (wToList x) (wToList y)) := by
  rcases x with ⟨nx, tx⟩
  rcases y with ⟨ny, ty⟩
  simp only [wToList_length]
  change (nx < ny ∨ ∃ h : nx = ny, h ▸ tx < ty) ↔ _
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, (toListAux_lt_iff nx 0 tx ty).mp h⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, (toListAux_lt_iff nx 0 tx ty).mpr h⟩

private lemma listToW_lt_iff {l₁ l₂ : List ℕ} (h₁ : StrictSorted l₁) (h₂ : StrictSorted l₂) :
    listToW l₁ < listToW l₂ ↔ l₁.length < l₂.length ∨ (l₁.length = l₂.length ∧ List.Lex (· < ·) l₁ l₂) := by
  rw [w_lt_iff_lex, wToList_listToW h₁, wToList_listToW h₂]

private lemma wToList_injective : Function.Injective wToList := by
  intro x y h
  rcases wLt_trichotomy x y with hlt | rfl | hgt
  · rw [w_lt_iff_lex, h] at hlt
    rcases hlt with h1 | ⟨_, h2⟩
    · exact (lt_irrefl _ h1).elim
    · have : ∀ l : List ℕ, ¬ List.Lex (· < ·) l l := by
        intro l; induction l with
        | nil => intro hl; cases hl
        | cons a t iht => intro hl; cases hl with | rel hr => exact lt_irrefl _ hr | cons hr => exact iht hr
      exact (this _ h2).elim
  · rfl
  · rw [w_lt_iff_lex, h] at hgt
    rcases hgt with h1 | ⟨_, h2⟩
    · exact (lt_irrefl _ h1).elim
    · have : ∀ l : List ℕ, ¬ List.Lex (· < ·) l l := by
        intro l; induction l with
        | nil => intro hl; cases hl
        | cons a t iht => intro hl; cases hl with | rel hr => exact lt_irrefl _ hr | cons hr => exact iht hr
      exact (this _ h2).elim

private def padNatTuple : ∀ {k n : ℕ}, k ≤ n → NatTuple k → NatTuple n
  | 0, 0, _, x => x
  | 0, n + 1, _, x => toLex (0, padNatTuple (Nat.zero_le n) x)
  | k + 1, 0, h, _ => absurd h (by omega)
  | k + 1, n + 1, h, x => toLex ((ofLex x).1, padNatTuple (by omega) (ofLex x).2)

private lemma padNatTuple_strictMono : ∀ {k n : ℕ} (h : k ≤ n), StrictMono (padNatTuple h)
  | 0, 0, _, _, _, hab => (lt_irrefl _ hab).elim
  | 0, _ + 1, _, _, _, hab => (lt_irrefl _ hab).elim
  | _ + 1, 0, h, _, _, _ => absurd h (by omega)
  | k + 1, n + 1, h, a, b, hab => by
    simp only [padNatTuple]
    rw [Prod.Lex.lt_iff] at hab ⊢
    rcases hab with hlt | ⟨heq, hlt⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, padNatTuple_strictMono (by omega) hlt⟩

private lemma omega_opow_omega_eq_iSup.{u} :
    ((ω : Ordinal.{u}) ^ (ω : Ordinal.{u})) = ⨆ n : ℕ, (ω : Ordinal.{u}) ^ n := by
  apply le_antisymm
  · rw [(Ordinal.isNormal_opow (a := (ω : Ordinal.{u})) Ordinal.one_lt_omega0).le_iff_forall_le
      Ordinal.isSuccLimit_omega0]
    intro a ha
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
    rw [Ordinal.opow_natCast]
    exact le_ciSup Ordinal.bddAbove_of_small n
  · refine ciSup_le fun n => ?_
    rw [← Ordinal.opow_natCast]
    exact le_of_lt ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (Ordinal.natCast_lt_omega0 n))

private lemma lift_omega_pow_nat.{u} (n : ℕ) :
    Ordinal.lift.{u, 0} ((ω : Ordinal.{0}) ^ n) = (ω : Ordinal.{u}) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Ordinal.lift_mul, ih, Ordinal.lift_omega0]

private lemma lift_omega_opow_omega.{u} :
    Ordinal.lift.{u, 0} ((ω : Ordinal.{0}) ^ (ω : Ordinal.{0})) =
      (ω : Ordinal.{u}) ^ (ω : Ordinal.{u}) := by
  apply le_antisymm
  · rw [omega_opow_omega_eq_iSup.{u}]
    by_contra hgt
    have hlt : (⨆ n : ℕ, (ω : Ordinal.{u}) ^ n) <
        Ordinal.lift.{u, 0} ((ω : Ordinal.{0}) ^ (ω : Ordinal.{0})) := not_le.mp hgt
    obtain ⟨y, hy_lt, hy_eq⟩ := Ordinal.lt_lift_iff.mp hlt
    rw [omega_opow_omega_eq_iSup.{0}] at hy_lt
    have hex : ∃ n : ℕ, y < (ω : Ordinal.{0}) ^ n := by
      by_contra hall
      push Not at hall
      have hle : (⨆ n : ℕ, (ω : Ordinal.{0}) ^ n) ≤ y := ciSup_le hall
      exact not_lt_of_ge hle hy_lt
    obtain ⟨n, hn⟩ := hex
    have hlt_u : Ordinal.lift.{u, 0} y < (ω : Ordinal.{u}) ^ n := by
      rw [← lift_omega_pow_nat.{u} n]
      exact Ordinal.lift_lt.mpr hn
    rw [hy_eq] at hlt_u
    exact not_lt_of_ge (le_ciSup Ordinal.bddAbove_of_small n) hlt_u
  · rw [omega_opow_omega_eq_iSup.{u}]
    refine ciSup_le fun n => ?_
    rw [← lift_omega_pow_nat.{u} n, Ordinal.lift_le, omega_opow_omega_eq_iSup.{0}]
    exact le_ciSup Ordinal.bddAbove_of_small n

private lemma typeLT_W : typeLT W = (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) := by
  apply le_antisymm
  · by_contra hgt
    have hlt : (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) < typeLT W := not_le.mp hgt
    let x : W := Ordinal.enum ((· < ·) : W → W → Prop) ⟨(ω : Ordinal.{0}) ^ (ω : Ordinal.{0}), hlt⟩
    have htypein : Ordinal.typein ((· < ·) : W → W → Prop) x = (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) :=
      Ordinal.typein_enum _ _
    have hseg_eq : typeLT ({ y : W | y < x } : Set W) = (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) := by
      rw [← htypein]
      rfl
    let emb : ({ y : W | y < x } : Set W) → (Fin (x.len + 1) ×ₗ NatTuple x.len) := fun y =>
      have hy : y.1.len ≤ x.len := by
        rcases y.2 with h1 | ⟨h1, _⟩ <;> omega
      toLex (⟨y.1.len, by omega⟩, padNatTuple hy y.1.tuple)
    have hemb : StrictMono emb := by
      intro y₁ y₂ hy
      dsimp only [emb]
      rw [Prod.Lex.lt_iff]
      rcases hy with h1 | ⟨h1, h2⟩
      · exact Or.inl (Fin.mk_lt_mk.mpr h1)
      · refine Or.inr ⟨Fin.ext h1, ?_⟩
        cases y₁ with | mk y₁ hy₁ =>
        cases y₂ with | mk y₂ hy₂ =>
        cases y₁ with | mk n₁ t₁ =>
        cases y₂ with | mk n₂ t₂ =>
        dsimp only at h1 h2 ⊢
        subst h1
        exact padNatTuple_strictMono _ h2
    have hle : (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) ≤
        (ω : Ordinal.{0}) ^ x.len * ((x.len + 1 : ℕ) : Ordinal.{0}) := by
      rw [← hseg_eq]
      calc typeLT ({ y : W | y < x } : Set W)
          ≤ typeLT (Fin (x.len + 1) ×ₗ NatTuple x.len) := typeLT_le_of_strictMono emb hemb
        _ = (typeLT (NatTuple x.len)) * (typeLT (Fin (x.len + 1))) := typeLT_prodLex
        _ = (ω : Ordinal.{0}) ^ x.len * ((x.len + 1 : ℕ) : Ordinal.{0}) := by
            rw [typeLT_natTuple, Ordinal.type_fin]
    have hlt2 : (ω : Ordinal.{0}) ^ x.len * ((x.len + 1 : ℕ) : Ordinal.{0}) <
        (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) := by
      have hpos : (0 : Ordinal.{0}) < (ω : Ordinal.{0}) ^ x.len := by
        rw [← Ordinal.opow_natCast]
        exact Ordinal.opow_pos _ Ordinal.omega0_pos
      calc (ω : Ordinal.{0}) ^ x.len * ((x.len + 1 : ℕ) : Ordinal.{0})
          < (ω : Ordinal.{0}) ^ x.len * ω :=
            mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 _) hpos
        _ = (ω : Ordinal.{0}) ^ (x.len + 1) := (pow_succ ω x.len).symm
        _ = (ω : Ordinal.{0}) ^ ((x.len + 1 : ℕ) : Ordinal.{0}) := (Ordinal.opow_natCast ω _).symm
        _ < (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) :=
            (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Ordinal.natCast_lt_omega0 _)
    exact not_lt_of_ge hle hlt2
  · rw [omega_opow_omega_eq_iSup]
    refine ciSup_le fun n => ?_
    rw [← typeLT_natTuple n]
    exact typeLT_le_of_strictMono (fun t => ⟨n, t⟩) (fun _ _ h => Or.inr ⟨rfl, h⟩)

private lemma ramsey_W (m : ℕ) (R B : SimpleGraph W) (hcomp : IsCompl R B) :
    (∃ s : Set W, R.IsClique s ∧ typeLT s = (ω : Ordinal.{0}) ^ (ω : Ordinal.{0})) ∨
    (∃ s : Finset W, B.IsClique (s : Set W) ∧ s.card = m) := by
  by_cases hm0 : m = 0
  · subst hm0; right; exact ⟨∅, by simp, by simp⟩
  by_cases hm1 : m = 1
  · subst hm1; right; exact ⟨{⟨0, PUnit.unit⟩}, by simp [SimpleGraph.IsClique], by simp⟩
  have hm2 : 2 ≤ m := by omega
  by_contra hno
  push Not at hno
  obtain ⟨hnoR, hnoB⟩ := hno
  -- Step 1: For each `n ≥ 0`, embed `NatTuple n` strictly monotonically into level `n * m` as a red clique
  have hlevel : ∀ n : ℕ, ∃ ψ : NatTuple n → W,
      StrictMono ψ ∧ (∀ t, (ψ t).len = n * m) ∧ R.IsClique (Set.range ψ) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨fun _ => ⟨0, PUnit.unit⟩, fun _ _ h => (lt_irrefl _ h).elim, fun _ => by simp, ?_⟩
      rintro _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ hne; exact (hne rfl).elim
    have hn1 : 1 ≤ n := by omega
    have hE_le : (n - 1) * (m - 1) + 1 ≤ n * m := by
      calc (n - 1) * (m - 1) + 1
          ≤ (n - 1) * m + m := by
            have := Nat.mul_le_mul_left (n - 1) (show m - 1 ≤ m by omega)
            omega
        _ = n * m := by rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn1]
    let emb : NatTuple ((n - 1) * (m - 1) + 1) → W :=
      fun t => ⟨n * m, padNatTuple hE_le t⟩
    have hemb : StrictMono emb := fun _ _ h => Or.inr ⟨rfl, padNatTuple_strictMono hE_le h⟩
    let Rn : SimpleGraph (NatTuple ((n - 1) * (m - 1) + 1)) := R.comap emb
    let Bn : SimpleGraph (NatTuple ((n - 1) * (m - 1) + 1)) := B.comap emb
    have hcomp_n : IsCompl Rn Bn := by
      refine ⟨?_, ?_⟩
      · rw [disjoint_iff]; ext a b
        simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and, Rn, Bn,
          SimpleGraph.comap_adj]
        intro hr hb
        have hbot : (R ⊓ B).Adj (emb a) (emb b) := ⟨hr, hb⟩
        rw [hcomp.disjoint.eq_bot] at hbot; exact hbot
      · rw [codisjoint_iff]; ext a b
        simp only [SimpleGraph.sup_adj, SimpleGraph.top_adj, Rn, Bn, SimpleGraph.comap_adj]
        constructor
        · rintro (hr | hb)
          · exact fun h => R.loopless.irrefl _ (h ▸ hr)
          · exact fun h => B.loopless.irrefl _ (h ▸ hb)
        · intro hne
          have htop : (R ⊔ B).Adj (emb a) (emb b) := by
            rw [hcomp.codisjoint.eq_top]; exact hemb.injective.ne hne
          exact htop
    rcases ramsey_natTuple n hn1 m (by omega) Rn Bn hcomp_n with ⟨s, hsR, hstype⟩ | ⟨s, hsB, hscard⟩
    · have hiso : Nonempty (((· < ·) : NatTuple n → _ → Prop) ≃r ((· < ·) : s → _ → Prop)) :=
        Ordinal.type_eq.mp (by rw [typeLT_natTuple, hstype])
      obtain ⟨iso⟩ := hiso
      refine ⟨fun t => emb (iso t).1,
        fun a b hab => hemb (iso.map_rel_iff.mpr hab),
        fun _ => rfl, ?_⟩
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
      exact hsR (iso a).2 (iso b).2 (fun h => hne (by simp [h]))
    · exfalso
      refine hnoB (s.image emb) ?_ (by rw [Finset.card_image_of_injective s hemb.injective, hscard])
      intro u hu v hv huv
      simp only [Finset.coe_image, Set.mem_image] at hu hv
      rcases hu with ⟨a, ha, rfl⟩; rcases hv with ⟨b, hb, rfl⟩
      exact hsB ha hb (fun h => huv (congrArg emb h))
  let ψ : ∀ n, NatTuple n → W := fun n => Classical.choose (hlevel n)
  have hψ : ∀ n, StrictMono (ψ n) ∧ (∀ t, (ψ n t).len = n * m) ∧ R.IsClique (Set.range (ψ n)) :=
    fun n => Classical.choose_spec (hlevel n)
  let Ψ : W → W := fun w => ψ w.len w.tuple
  have hΨ_mono : StrictMono Ψ := by
    rintro ⟨n₁, t₁⟩ ⟨n₂, t₂⟩ hlt
    rcases hlt with h1 | ⟨heq, h1⟩
    · left
      rw [(hψ n₁).2.1, (hψ n₂).2.1]
      exact Nat.mul_lt_mul_of_pos_right h1 (by omega)
    · dsimp only at heq h1
      subst heq
      exact (hψ n₁).1 h1
  let R' : SimpleGraph W := R.comap Ψ
  let B' : SimpleGraph W := B.comap Ψ
  have hcomp' : IsCompl R' B' := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]; ext a b
      simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and, R', B',
        SimpleGraph.comap_adj]
      intro hr hb
      have hbot : (R ⊓ B).Adj (Ψ a) (Ψ b) := ⟨hr, hb⟩
      rw [hcomp.disjoint.eq_bot] at hbot; exact hbot
    · rw [codisjoint_iff]; ext a b
      simp only [SimpleGraph.sup_adj, SimpleGraph.top_adj, R', B', SimpleGraph.comap_adj]
      constructor
      · rintro (hr | hb)
        · exact fun h => R.loopless.irrefl _ (h ▸ hr)
        · exact fun h => B.loopless.irrefl _ (h ▸ hb)
      · intro hne
        have htop : (R ⊔ B).Adj (Ψ a) (Ψ b) := by
          rw [hcomp.codisjoint.eq_top]; exact hΨ_mono.injective.ne hne
        exact htop
  have hsame_len_red : ∀ x y : W, x.len = y.len → x ≠ y → R'.Adj x y := by
    rintro ⟨nx, tx⟩ ⟨ny, ty⟩ hlen hne
    dsimp only at hlen; subst hlen
    exact (hψ nx).2.2 ⟨tx, rfl⟩ ⟨ty, rfl⟩ (fun h => hne (hΨ_mono.injective h))
  -- Step 2: Apply Lemma 3.6 to `B'` on strictly sorted lists
  let g : List ℕ → List ℕ → Bool := fun x y => decide (B'.Adj (listToW x) (listToW y))
  obtain ⟨e, j, he, he0, hj_spec⟩ := larson_lemma_3_6 g
  -- Step 3: Rule out `j l = true` for every `l ≥ 1` via Lemma 3.7
  have hj_false : ∀ l ≥ 1, j l = false := by
    intro l hl
    by_contra hne
    have hj_true : j l = true := by cases h : j l <;> simp_all
    let e' : ℕ → ℕ := fun t => e (l + 1 + t)
    have he' : StrictMono e' := fun a b hab => he (by omega)
    have he'0 : 1 ≤ e' 0 := le_trans he0 (he.monotone (Nat.zero_le _))
    obtain ⟨x, hx_sort, hx_fb⟩ := larson_lemma_3_7 he' he'0 m l (by omega) hl
    let M : Finset W := Finset.univ.image (fun i : Fin m => Ψ (listToW (x i)))
    have hx_inj : Function.Injective (fun i : Fin m => listToW (x i)) := by
      intro i₁ i₂ heq
      by_contra hne_i
      rcases lt_or_gt_of_ne hne_i with hlt | hgt
      · obtain ⟨zs, ⟨_, _, _, _, hlen_lt, _, _, _, _, _, _, _, _⟩, _⟩ := hx_fb i₁ i₂ hlt
        have := congrArg W.len heq
        simp only [listToW] at this; omega
      · obtain ⟨zs, ⟨_, _, _, _, hlen_lt, _, _, _, _, _, _, _, _⟩, _⟩ := hx_fb i₂ i₁ hgt
        have := congrArg W.len heq
        simp only [listToW] at this; omega
    have hM_card : M.card = m := by
      change (Finset.univ.image (Ψ ∘ fun i : Fin m => listToW (x i))).card = m
      rw [Finset.card_image_of_injective _ (hΨ_mono.injective.comp hx_inj), Finset.card_univ,
        Fintype.card_fin]
    refine hnoB M ?_ hM_card
    intro u hu v hv huv
    simp only [M, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hu hv
    rcases hu with ⟨i₁, rfl⟩; rcases hv with ⟨i₂, rfl⟩
    have hi_ne : i₁ ≠ i₂ := fun h => huv (by simp [h])
    rcases lt_or_gt_of_ne hi_ne with hlt | hgt
    · obtain ⟨zs, hfb, hzs_in⟩ := hx_fb i₁ i₂ hlt
      have hzs_gt : ∀ u ∈ zs, e l < u ∧ u ∈ Set.range e := by
        intro u hu
        rcases hzs_in u hu with ⟨t, rfl⟩
        exact ⟨he (by omega), ⟨l + 1 + t, rfl⟩⟩
      have hcol := hj_spec l hl (x i₁) (x i₂) zs hfb hzs_gt
      rw [hj_true] at hcol
      exact of_decide_eq_true hcol
    · obtain ⟨zs, hfb, hzs_in⟩ := hx_fb i₂ i₁ hgt
      have hzs_gt : ∀ u ∈ zs, e l < u ∧ u ∈ Set.range e := by
        intro u hu
        rcases hzs_in u hu with ⟨t, rfl⟩
        exact ⟨he (by omega), ⟨l + 1 + t, rfl⟩⟩
      have hcol := hj_spec l hl (x i₂) (x i₁) zs hfb hzs_gt
      rw [hj_true] at hcol
      exact (of_decide_eq_true hcol).symm
  -- Step 4: Apply Lemma 3.8 to obtain a red `ω ^ ω` in `R'`, hence in `R`
  obtain ⟨X, hX_sort, hX_emb, hX_fb⟩ := larson_lemma_3_8 he he0
  let S : Set W := listToW '' X
  have hS_red : R'.IsClique S := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    rcases lt_trichotomy x.length y.length with hlt | heq | hgt
    · obtain ⟨l, hl, zs, hfb, hzs⟩ := hX_fb x hx y hy hlt
      have hcol := hj_spec l hl x y zs hfb hzs
      rw [hj_false l hl] at hcol
      have hnotB : ¬ B'.Adj (listToW x) (listToW y) := of_decide_eq_false hcol
      have htop : (R' ⊔ B').Adj (listToW x) (listToW y) := by
        rw [hcomp'.codisjoint.eq_top]; exact hne
      exact htop.resolve_right hnotB
    · exact hsame_len_red _ _ heq hne
    · obtain ⟨l, hl, zs, hfb, hzs⟩ := hX_fb y hy x hx hgt
      have hcol := hj_spec l hl y x zs hfb hzs
      rw [hj_false l hl] at hcol
      have hnotB : ¬ B'.Adj (listToW y) (listToW x) := of_decide_eq_false hcol
      have htop : (R' ⊔ B').Adj (listToW y) (listToW x) := by
        rw [hcomp'.codisjoint.eq_top]; exact hne.symm
      exact (htop.resolve_right hnotB).symm
  have hS_type : typeLT S = (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) := by
    apply le_antisymm
    · rw [← typeLT_W]
      exact typeLT_le_of_strictMono Subtype.val (fun _ _ h => h)
    · rw [omega_opow_omega_eq_iSup]
      refine ciSup_le fun j => ?_
      by_cases hj0 : j = 0
      · subst hj0
        obtain ⟨f, hfX, _, _⟩ := hX_emb 1 (le_refl 1)
        have hne : S.Nonempty := ⟨listToW (f (toLex (0, PUnit.unit))), f _, hfX _, rfl⟩
        obtain ⟨s0, hs0⟩ := hne
        have h1 : typeLT PUnit ≤ typeLT S :=
          typeLT_le_of_strictMono (fun _ => ⟨s0, hs0⟩) (fun _ _ h => (lt_irrefl _ h).elim)
        simpa [Ordinal.type_eq_one_of_unique] using h1
      · obtain ⟨f, hfX, hflen, hflex⟩ := hX_emb j (by omega)
        rw [← typeLT_natTuple j]
        refine typeLT_le_of_strictMono (fun a => ⟨listToW (f a), f a, hfX a, rfl⟩) ?_
        intro a b hab
        change listToW (f a) < listToW (f b)
        rw [listToW_lt_iff (hX_sort _ (hfX a)) (hX_sort _ (hfX b))]
        exact Or.inr ⟨hflen a b, hflex a b hab⟩
  refine hnoR (Ψ '' S) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    exact hS_red ha hb (fun h => hne (congrArg Ψ h))
  · let iso : ((· < ·) : S → S → Prop) ≃r ((· < ·) : (Ψ '' S) → (Ψ '' S) → Prop) :=
      { toEquiv := Equiv.ofBijective (fun a => ⟨Ψ a.1, a.1, a.2, rfl⟩)
          ⟨fun a b h => Subtype.ext (hΨ_mono.injective (by simpa using congrArg Subtype.val h)),
           fun ⟨_, a, ha, hfa⟩ => ⟨⟨a, ha⟩, Subtype.ext hfa⟩⟩
        map_rel_iff' := by intro _ _; exact hΨ_mono.lt_iff_lt }
    exact iso.symm.ordinalType_congr.trans hS_type

private lemma milner_larson_ordinal.{u} (m : ℕ) :
    OrdinalCardinalRamsey.{u} (ω ^ ω) (ω ^ ω) m := by
  intro red blue hcomp
  have htype : typeLT (ULift.{u, 0} W) = (ω : Ordinal.{u}) ^ (ω : Ordinal.{u}) := by
    rw [Ordinal.type_lt_ulift, typeLT_W, lift_omega_opow_omega.{u}]
  have he_ex : Nonempty (((· < ·) : ULift.{u, 0} W → _ → Prop) ≃r
      ((· < ·) : ((ω : Ordinal.{u}) ^ (ω : Ordinal.{u})).ToType → _ → Prop)) :=
    Ordinal.type_eq.mp (htype.trans (Ordinal.type_toType _).symm)
  obtain ⟨e⟩ := he_ex
  let emb : W → ((ω : Ordinal.{u}) ^ (ω : Ordinal.{u})).ToType := fun w => e (ULift.up w)
  have hemb_mono : StrictMono emb := fun _ _ h => e.map_rel_iff.mpr h
  let R : SimpleGraph W := red.comap emb
  let B : SimpleGraph W := blue.comap emb
  have hRB_comp : IsCompl R B := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]; ext p q
      simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and, R, B,
        SimpleGraph.comap_adj]
      intro hr hb
      have hbot : (red ⊓ blue).Adj (emb p) (emb q) := ⟨hr, hb⟩
      rw [hcomp.disjoint.eq_bot] at hbot; exact hbot
    · rw [codisjoint_iff]; ext p q
      simp only [SimpleGraph.sup_adj, SimpleGraph.top_adj, R, B, SimpleGraph.comap_adj]
      constructor
      · rintro (hr | hb)
        · exact fun h => red.loopless.irrefl _ (h ▸ hr)
        · exact fun h => blue.loopless.irrefl _ (h ▸ hb)
      · intro hne
        have htop : (red ⊔ blue).Adj (emb p) (emb q) := by
          rw [hcomp.codisjoint.eq_top]; exact hemb_mono.injective.ne hne
        exact htop
  rcases ramsey_W m R B hRB_comp with ⟨s, hsR, hstype⟩ | ⟨s, hsB, hscard⟩
  · left
    refine ⟨emb '' s, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
      exact hsR ha hb (fun h => hne (congrArg emb h))
    · let iso : ((· < ·) : ULift.{u, 0} s → _ → Prop) ≃r
          ((· < ·) : (emb '' s) → _ → Prop) :=
        { toEquiv := Equiv.ofBijective (fun a => ⟨emb a.down.1, a.down.1, a.down.2, rfl⟩)
            ⟨fun a b h => ULift.ext _ _ (Subtype.ext
                (hemb_mono.injective (by simpa using congrArg Subtype.val h))),
             fun ⟨_, a, ha, hfa⟩ => ⟨ULift.up ⟨a, ha⟩, Subtype.ext hfa⟩⟩
          map_rel_iff' := by intro _ _; exact hemb_mono.lt_iff_lt }
      rw [iso.symm.ordinalType_congr, Ordinal.type_lt_ulift, hstype, lift_omega_opow_omega.{u}]
  · right
    refine ⟨(s.image emb : Set _), ?_, ?_⟩
    · intro u hu v hv huv
      simp only [Finset.coe_image, Set.mem_image] at hu hv
      rcases hu with ⟨a, ha, rfl⟩; rcases hv with ⟨b, hb, rfl⟩
      exact hsB ha hb (fun h => huv (congrArg emb h))
    · simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset,
        Finset.card_image_of_injective s hemb_mono.injective, hscard]

end Erdos590Finite

theorem OMA.solution : type_of% @Erdos590.erdos_590.variants.finite_cardinal :=
  fun m => Erdos590Finite.milner_larson_ordinal m
