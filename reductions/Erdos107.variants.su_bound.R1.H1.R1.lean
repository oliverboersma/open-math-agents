import OMAReductions.R_Erdos107_variants_su_bound_R1
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds

-- Reduction Erdos107.variants.su_bound.R1.H1.R1 of step Erdos107.variants.su_bound.R1.H1
-- Credit: @mucoucah

/-! Suk's planar theorem (even n) is reduced to
* H1: the Erdos-Szekeres cups-caps theorem in sampling form (every m-point set in general
  position contains an x-ordered (2k+1)-cup or (2k+1)-cap), and
* H2: Suk's region step: given an x-ordered cup/cap of k+1 anchors such that each of the
  k gaps contains more than 2^((1+e)n) points positioned like a cup/cap insertion, a convex
  n-subset exists.
The weak positive-fraction Erdos-Szekeres step (density of good (2k+1)-sets, double counting,
pigeonhole over anchor chains, completion regions) and the asymptotic bookkeeping are proved. -/

open Filter Finset

namespace OMA.R_Erdos107_variants_su_bound_R1_H1_R1

private theorem dense_subsets {α : Type*} (S : Finset α) {k m : ℕ}
    (hkm : k ≤ m) (hmS : m ≤ S.card) (good : Finset α → Prop) [DecidablePred good]
    (hit : ∀ U ⊆ S, U.card = m → ∃ T ⊆ U, T.card = k ∧ good T) :
    S.card.choose k ≤ ((S.powersetCard k).filter good).card * m.choose k := by
  classical
  let G := (S.powersetCard k).filter good
  have hcount :
      (S.powersetCard m).card * 1 ≤ G.card * (S.card - k).choose (m - k) := by
    apply Finset.card_mul_le_card_mul (fun U T : Finset α => T ⊆ U)
    · intro U hU
      obtain ⟨hUS, hUm⟩ := mem_powersetCard.mp hU
      obtain ⟨T, hTU, hTk, hg⟩ := hit U hUS hUm
      exact card_pos.mpr ⟨T, by
        exact mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_powersetCard.mpr ⟨hTU.trans hUS, hTk⟩, hg⟩, hTU⟩⟩
    · intro T hT
      obtain ⟨hTS, hTk⟩ := mem_powersetCard.mp (mem_filter.mp hT).1
      change ((S.powersetCard m).filter (T ⊆ ·)).card ≤ _
      rw [card_filter_powersetCard_subset T S m hTS (hTk ▸ hkm), hTk]
  rw [card_powersetCard, mul_one] at hcount
  have hp : 0 < (S.card - k).choose (m - k) := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    S.card.choose k * (S.card - k).choose (m - k) =
        S.card.choose m * m.choose k := (Nat.choose_mul hkm).symm
    _ ≤ (G.card * (S.card - k).choose (m - k)) * m.choose k :=
      Nat.mul_le_mul_right _ hcount
    _ = (G.card * m.choose k) * (S.card - k).choose (m - k) := by ac_rfl

/-- Longest chains below a point stratify a finite strict partial order into
antichains. -/

private theorem large_completion_regions {α β γ : Type*}
    {k L : ℕ} (S : Finset α) (G : Finset β) (A : Finset γ)
    (anchor : β → γ) (completion : β → Fin k → α) (R : γ → Fin k → Finset α)
    (hA : ∀ g ∈ G, anchor g ∈ A)
    (hR : ∀ a ∈ A, ∀ i, R a i ⊆ S)
    (hmem : ∀ g ∈ G, ∀ i, completion g i ∈ R (anchor g) i)
    (hinj : ∀ g ∈ G, ∀ g' ∈ G, anchor g = anchor g' →
      completion g = completion g' → g = g')
    (hsize : A.card * (L * S.card ^ (k - 1)) < G.card) :
    ∃ a ∈ A, ∀ i, L < (R a i).card := by
  classical
  obtain ⟨a, haA, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hA hsize
  refine ⟨a, haA, fun i => lt_of_not_ge fun hi => ?_⟩
  let F := G.filter fun g => anchor g = a
  have hm : F.card ≤ (Fintype.piFinset (R a)).card := by
    apply Finset.card_le_card_of_injOn completion
    · intro g hg
      obtain ⟨hgG, hga⟩ := mem_filter.mp hg
      exact Fintype.mem_piFinset.mpr fun j => hga ▸ hmem g hgG j
    · intro g hg g' hg' he
      obtain ⟨hgG, hga⟩ := mem_filter.mp hg
      obtain ⟨hg'G, hg'a⟩ := mem_filter.mp hg'
      exact hinj g hgG g' hg'G (hga.trans hg'a.symm) he
  have hp : (Fintype.piFinset (R a)).card ≤ L * S.card ^ (k - 1) := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (mem_univ i)]
    refine Nat.mul_le_mul hi ?_
    calc
      ∏ j ∈ univ.erase i, (R a j).card ≤ ∏ _j ∈ univ.erase i, S.card :=
        Finset.prod_le_prod' fun j _ => card_le_card (hR a haA j)
      _ = S.card ^ (k - 1) := by simp [Finset.prod_const, Finset.card_erase_of_mem]
  exact (not_lt_of_ge (hm.trans hp)) ha

private theorem pow_le_mul_choose {N d : ℕ} (h : 2 * (d - 1) ≤ N) :
    N ^ d ≤ (2 ^ d * d.factorial) * N.choose d := by
  have h₁ : N ≤ 2 * (N + 1 - d) := by omega
  calc
    N ^ d ≤ (2 * (N + 1 - d)) ^ d := Nat.pow_le_pow_left h₁ _
    _ = 2 ^ d * (N + 1 - d) ^ d := Nat.mul_pow _ _ _
    _ ≤ 2 ^ d * N.descFactorial d := Nat.mul_le_mul_left _ (N.pow_sub_le_descFactorial d)
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_assoc]

private theorem inGap_of_orderedTurns_abs {k : ℕ} {up : Bool}
    (tn : Bool → ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → Prop)
    {e : Fin (2 * k + 1) → ℝ × ℝ}
    (he : StrictMono (fun i => (e i).1) ∧
      ∀ i j l, i < j → j < l → tn up (e i) (e j) (e l)) (i : Fin k) :
    (e ⟨2 * i.val, by omega⟩).1 < (e ⟨2 * i.val + 1, by omega⟩).1 ∧
      (e ⟨2 * i.val + 1, by omega⟩).1 < (e ⟨2 * (i.val + 1), by omega⟩).1 ∧
      ∀ j l : Fin (k + 1), j < l →
        if l.val ≤ i.val then tn up (e ⟨2 * j.val, by omega⟩) (e ⟨2 * l.val, by omega⟩)
          (e ⟨2 * i.val + 1, by omega⟩)
        else if i.val < j.val then tn up (e ⟨2 * i.val + 1, by omega⟩)
          (e ⟨2 * j.val, by omega⟩) (e ⟨2 * l.val, by omega⟩)
        else tn up (e ⟨2 * j.val, by omega⟩) (e ⟨2 * i.val + 1, by omega⟩)
          (e ⟨2 * l.val, by omega⟩) := by
  refine ⟨he.1 (show (⟨2 * i.val, by omega⟩ : Fin (2 * k + 1)) < ⟨2 * i.val + 1, by omega⟩ from
      Fin.mk_lt_mk.mpr (by omega)),
    he.1 (show (⟨2 * i.val + 1, by omega⟩ : Fin (2 * k + 1)) < ⟨2 * (i.val + 1), by omega⟩ from
      Fin.mk_lt_mk.mpr (by omega)), ?_⟩
  intro j l hjl
  have hjl' : (⟨2 * j.val, by omega⟩ : Fin (2 * k + 1)) < ⟨2 * l.val, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by have := Fin.lt_def.mp hjl; omega)
  by_cases hl : l.val ≤ i.val
  · simp only [if_pos hl]
    exact he.2 _ _ _ hjl' (Fin.mk_lt_mk.mpr (by omega))
  · by_cases hj : i.val < j.val
    · simp only [if_neg hl, if_pos hj]
      exact he.2 _ _ _ (Fin.mk_lt_mk.mpr (by omega)) hjl'
    · simp only [if_neg hl, if_neg hj]
      exact he.2 _ _ _ (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

private theorem even_odd_determine_abs {α : Type*} {k : ℕ} {e f : Fin (2 * k + 1) → α}
    (he : ∀ i : Fin (k + 1), e ⟨2 * i.val, by omega⟩ = f ⟨2 * i.val, by omega⟩)
    (ho : ∀ i : Fin k, e ⟨2 * i.val + 1, by omega⟩ = f ⟨2 * i.val + 1, by omega⟩) :
    e = f := by
  funext i
  by_cases h : i.val % 2 = 0
  · have hj : (⟨2 * (i.val / 2), by omega⟩ : Fin (2 * k + 1)) = i := by
      apply Fin.ext
      change 2 * (i.val / 2) = i.val
      omega
    have := he ⟨i.val / 2, by omega⟩
    simpa only [hj] using this
  · have hj : (⟨2 * (i.val / 2) + 1, by omega⟩ : Fin (2 * k + 1)) = i := by
      apply Fin.ext
      change 2 * (i.val / 2) + 1 = i.val
      omega
    have := ho ⟨i.val / 2, by omega⟩
    simpa only [hj] using this

private theorem image_eq_of_orderedTurns_abs {d : ℕ} {e : Fin d → ℝ × ℝ}
    {T : Finset (ℝ × ℝ)} (hTd : T.card = d) (hsub : ∀ i, e i ∈ T)
    (he : StrictMono (fun i => (e i).1)) : Finset.univ.image e = T := by
  classical
  have hi : Function.Injective e := fun i j hij => he.injective (congrArg Prod.fst hij)
  have hs : Finset.univ.image e ⊆ T := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact hsub i
  apply Finset.eq_of_subset_of_card_le hs
  rw [Finset.card_image_of_injective _ hi, card_univ, Fintype.card_fin, hTd]

open scoped Classical in
/-- Weak positive-fraction Erdos-Szekeres: an ordered chain of k+1 anchors with more than L
insertions in every gap. -/
private theorem dense_ordered_regions_abs (tn : Bool → ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → Prop)
    {k L m : ℕ} (S : Finset (ℝ × ℝ)) (hk : 0 < k)
    (hm : 2 * k + 1 ≤ m) (hmS : m ≤ S.card) (h4k : 4 * k ≤ S.card)
    (hit : ∀ U ⊆ S, U.card = m → ∃ (up : Bool) (e : Fin (2 * k + 1) → ℝ × ℝ),
      (∀ i, e i ∈ U) ∧ StrictMono (fun i => (e i).1) ∧
        ∀ i j l, i < j → j < l → tn up (e i) (e j) (e l))
    (hlarge : 2 * (2 ^ (2 * k + 1) * (2 * k + 1).factorial * m.choose (2 * k + 1)) * L
      < S.card) :
    ∃ (up : Bool) (a : Fin (k + 1) → ℝ × ℝ), (∀ i, a i ∈ S) ∧
      StrictMono (fun i => (a i).1) ∧ (∀ i j l, i < j → j < l → tn up (a i) (a j) (a l)) ∧
      ∀ i : Fin k, L < (S.filter (fun p => (a ⟨i, by omega⟩).1 < p.1 ∧
        p.1 < (a ⟨i.val + 1, by omega⟩).1 ∧
        ∀ j l : Fin (k + 1), j < l →
          if l.val ≤ i.val then tn up (a j) (a l) p
          else if i.val < j.val then tn up p (a j) (a l)
          else tn up (a j) p (a l))).card := by
  classical
  let d := 2 * k + 1
  let good : Finset (ℝ × ℝ) → Prop := fun T => ∃ (up : Bool) (e : Fin d → ℝ × ℝ),
    (∀ i, e i ∈ T) ∧ StrictMono (fun i => (e i).1) ∧
      ∀ i j l, i < j → j < l → tn up (e i) (e j) (e l)
  have hit' : ∀ U ⊆ S, U.card = m → ∃ T ⊆ U, T.card = d ∧ good T := by
    intro U hUS hUm
    obtain ⟨up, e, hem, he1, he2⟩ := hit U hUS hUm
    have hi : Function.Injective e := fun i j hij => he1.injective (congrArg Prod.fst hij)
    refine ⟨Finset.univ.image e, ?_, by simp [d, Finset.card_image_of_injective _ hi],
      up, e, fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, he1, he2⟩
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hem i
  let G := (S.powersetCard d).filter good
  have hgood (T : ↑G) : good T.val := (mem_filter.mp T.property).2
  let up (T : ↑G) := (hgood T).choose
  let e (T : ↑G) := (hgood T).choose_spec.choose
  have he (T : ↑G) : (∀ i, e T i ∈ T.val) ∧ StrictMono (fun i => (e T i).1) ∧
      ∀ i j l, i < j → j < l → tn (up T) (e T i) (e T j) (e T l) :=
    (hgood T).choose_spec.choose_spec
  have hT (T : ↑G) := mem_powersetCard.mp (mem_filter.mp T.property).1
  let anchor (T : ↑G) : Bool × (Fin (k + 1) → ℝ × ℝ) :=
    (up T, fun i : Fin (k + 1) => e T ⟨2 * i.val, by omega⟩)
  let completion (T : ↑G) : Fin k → ℝ × ℝ := fun i => e T ⟨2 * i.val + 1, by omega⟩
  let A := G.attach.image anchor
  let A₀ := (Finset.univ : Finset Bool) ×ˢ Fintype.piFinset (fun _ : Fin (k + 1) => S)
  let R (a : Bool × (Fin (k + 1) → ℝ × ℝ)) (i : Fin k) :=
    S.filter (fun p => (a.2 ⟨i, by omega⟩).1 < p.1 ∧
        p.1 < (a.2 ⟨i.val + 1, by omega⟩).1 ∧
        ∀ j l : Fin (k + 1), j < l →
          if l.val ≤ i.val then tn a.1 (a.2 j) (a.2 l) p
          else if i.val < j.val then tn a.1 p (a.2 j) (a.2 l)
          else tn a.1 (a.2 j) p (a.2 l))
  have hAA₀ : A ⊆ A₀ := by
    intro a ha
    obtain ⟨T, _, rfl⟩ := mem_image.mp ha
    exact mem_product.mpr ⟨mem_univ _, Fintype.mem_piFinset.mpr
      (fun i => (hT T).1 ((he T).1 _))⟩
  have hAc : A.card ≤ 2 * S.card ^ (k + 1) := by
    simpa [A₀, Fintype.card_piFinset_const] using card_le_card hAA₀
  have hbound : S.card ^ d ≤ G.card * (2 ^ d * d.factorial * m.choose d) := by
    calc
      S.card ^ d ≤ (2 ^ d * d.factorial) * S.card.choose d :=
        pow_le_mul_choose (by dsimp [d]; omega)
      _ ≤ (2 ^ d * d.factorial) * (G.card * m.choose d) :=
        Nat.mul_le_mul_left _ (dense_subsets S hm hmS good hit')
      _ = _ := by ac_rfl
  have hexp : k + 1 + (k - 1) = 2 * k := by omega
  have hcount : A.card * (L * S.card ^ (k - 1)) < G.attach.card := by
    rw [card_attach]
    by_contra! hc
    have hab := (Nat.mul_le_mul_right (L * S.card ^ (k - 1)) hAc)
    have hb := hbound.trans (Nat.mul_le_mul_right _ (hc.trans hab))
    exact (lt_irrefl (S.card ^ d)) (calc
      S.card ^ d ≤
          (2 * S.card ^ (k + 1) * (L * S.card ^ (k - 1))) *
            (2 ^ d * d.factorial * m.choose d) := hb
      _ = (2 * (2 ^ d * d.factorial * m.choose d) * L) * S.card ^ (2 * k) := by
        rw [← hexp, pow_add S.card (k + 1) (k - 1)]
        ac_rfl
      _ < S.card * S.card ^ (2 * k) :=
        Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos (by omega))
      _ = S.card ^ d := by dsimp [d]; rw [pow_succ'])
  obtain ⟨a, ha, hLa⟩ := large_completion_regions S G.attach A anchor completion R
    (fun T hT' => mem_image.mpr ⟨T, hT', rfl⟩)
    (fun _ _ _ => filter_subset _ _)
    (fun T _ i => mem_filter.mpr ⟨(hT T).1 ((he T).1 _),
      inGap_of_orderedTurns_abs tn ⟨(he T).2.1, (he T).2.2⟩ i⟩)
    (fun T _ U _ ha' hc' => by
      have hfun : e T = e U := even_odd_determine_abs
        (fun i => congrFun (congrArg Prod.snd ha') i) (fun i => congrFun hc' i)
      apply Subtype.ext
      rw [← image_eq_of_orderedTurns_abs (hT T).2 (he T).1 (he T).2.1,
        ← image_eq_of_orderedTurns_abs (hT U).2 (he U).1 (he U).2.1, hfun])
    hcount
  obtain ⟨T, -, rfl⟩ := mem_image.mp ha
  refine ⟨up T, fun i : Fin (k + 1) => e T ⟨2 * i.val, by omega⟩,
    fun i => (hT T).1 ((he T).1 _), ?_, ?_, hLa⟩
  · intro i j hij
    exact (he T).2.1 (Fin.mk_lt_mk.mpr (by have := Fin.lt_def.mp hij; omega))
  · intro i j l hij hjl
    exact (he T).2.2 _ _ _ (Fin.mk_lt_mk.mpr (by have := Fin.lt_def.mp hij; omega))
      (Fin.mk_lt_mk.mpr (by have := Fin.lt_def.mp hjl; omega))

private theorem growth_eventually {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C ≤ (2 : ℝ) ^ (δ * n) := by
  have h1 : (1 : ℝ) < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have ht := tendsto_pow_atTop_atTop_of_one_lt h1
  filter_upwards [tendsto_atTop.mp ht C] with n hn
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  exact hn

private theorem threshold_bound {ε : ℝ} {n : ℕ} (R L c : ℕ) (hε : 0 ≤ ε)
    (hL : (L : ℝ) ≤ (2 : ℝ) ^ ((1 + ε / 2) * n))
    (hC : ((R : ℝ) + 1 + c) ≤ (2 : ℝ) ^ (ε / 2 * n)) :
    ((R * L + 1 + c : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) := by
  have hpos : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 + ε / 2) * n) := by
    apply Real.one_le_rpow (by norm_num)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    positivity
  have hsplit : (2 : ℝ) ^ ((1 + ε) * n) =
      (2 : ℝ) ^ (ε / 2 * n) * (2 : ℝ) ^ ((1 + ε / 2) * n) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  rw [hsplit]
  push_cast
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  calc (R : ℝ) * L + 1 + c ≤ R * (2 : ℝ) ^ ((1 + ε / 2) * n) + 1 + c := by
        gcongr
    _ ≤ ((R : ℝ) + 1 + c) * (2 : ℝ) ^ ((1 + ε / 2) * n) := by nlinarith
    _ ≤ _ := by gcongr

/-- Erdos-Szekeres cups-caps in sampling form: for every k there is a sample size m such
that every m-point set with distinct abscissas and no flat x-sorted triple contains an
x-ordered (2k+1)-point cup or cap. -/
def H1 : Prop :=
  ∀ k : ℕ, 0 < k → ∃ m : ℕ, 2 * k + 1 ≤ m ∧
    ∀ U : Finset (ℝ × ℝ), U.card = m → Set.InjOn Prod.fst (U : Set (ℝ × ℝ)) →
      (∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a.1 < b.1 → b.1 < c.1 →
        (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
      ∃ (up : Bool) (e : Fin (2 * k + 1) → ℝ × ℝ), (∀ i, e i ∈ U) ∧
        StrictMono (fun i => (e i).1) ∧ ∀ i j l, i < j → j < l →
          0 < (if up then (1 : ℝ) else -1) * (((e j).1 - (e i).1) * ((e l).2 - (e j).2) -
            ((e j).2 - (e i).2) * ((e l).1 - (e j).1))

/-- Suk's region step: an x-ordered cup or cap of k+1 anchors whose k gaps each contain more
than 2^((1+e)n) points that complete the anchors to a cup or cap forces a convex n-subset. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ k : ℕ, 0 < k ∧ ∀ᶠ n : ℕ in atTop, Even n →
    ∀ S : Finset (ℝ × ℝ), Set.InjOn Prod.fst (S : Set (ℝ × ℝ)) →
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a.1 < b.1 → b.1 < c.1 →
        (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
      ∀ (up : Bool) (a : Fin (k + 1) → ℝ × ℝ), (∀ i, a i ∈ S) →
        StrictMono (fun i => (a i).1) →
        (∀ i j l, i < j → j < l → 0 < (if up then (1 : ℝ) else -1) *
          (((a j).1 - (a i).1) * ((a l).2 - (a j).2) - ((a j).2 - (a i).2) * ((a l).1 - (a j).1))) →
        (∀ i : Fin k, ∃ T ⊆ S, (2 : ℝ) ^ ((1 + ε) * n) < T.card ∧ ∀ p ∈ T,
          (a ⟨i, by omega⟩).1 < p.1 ∧ p.1 < (a ⟨i.val + 1, by omega⟩).1 ∧
          ∀ j l : Fin (k + 1), j < l →
            let t := fun x y z : ℝ × ℝ => 0 < (if up then (1 : ℝ) else -1) *
              ((y.1 - x.1) * (z.2 - y.2) - (y.2 - x.2) * (z.1 - y.1))
            if l.val ≤ i.val then t (a j) (a l) p
            else if i.val < j.val then t p (a j) (a l) else t (a j) p (a l)) →
        ∃ Y ⊆ S, Y.card = n ∧
          ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

theorem main : H1 → H2 → OMA.R_Erdos107_variants_su_bound_R1.H1 := by
  classical
  intro h1 h2 ε hε hε1
  obtain ⟨k, hk, hev⟩ := h2 (ε / 2) (by positivity) (by linarith)
  obtain ⟨m, hm, hU⟩ := h1 k hk
  let R := 2 * (2 ^ (2 * k + 1) * (2 * k + 1).factorial * m.choose (2 * k + 1))
  filter_upwards [hev, growth_eventually (half_pos hε) ((R : ℝ) + 1 + (m + 4 * k : ℕ))]
    with n hn hg heven
  let L := ⌊(2 : ℝ) ^ ((1 + ε / 2) * n)⌋₊
  refine ⟨R * L + 1 + (m + 4 * k), threshold_bound R L (m + 4 * k) hε.le
    (Nat.floor_le (by positivity)) hg, ?_⟩
  intro X hX hinj hgen
  obtain ⟨up, a, haS, hmono, hturn, hgap⟩ := dense_ordered_regions_abs
    (fun up x y z => 0 < (if up then (1 : ℝ) else -1) *
      ((y.1 - x.1) * (z.2 - y.2) - (y.2 - x.2) * (z.1 - y.1)))
    (L := L) X hk hm (by rw [hX]; omega) (by rw [hX]; omega)
    (fun U hUX hUm => hU U hUm (hinj.mono hUX)
      (fun p hp q hq r hr => hgen p (hUX hp) q (hUX hq) r (hUX hr)))
    (show R * L < X.card by rw [hX]; omega)
  refine hn heven X hinj hgen up a haS hmono hturn (fun i => ⟨_, filter_subset _ _, ?_,
    fun p hp => (mem_filter.mp hp).2⟩)
  have h := hgap i
  calc (2 : ℝ) ^ ((1 + ε / 2) * n) < L + 1 := Nat.lt_floor_add_one _
    _ ≤ _ := by exact_mod_cast h

end OMA.R_Erdos107_variants_su_bound_R1_H1_R1
