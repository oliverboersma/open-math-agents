import OMAReductions.R_Erdos107_variants_su_bound_R1_H2_R1
import Mathlib

/-! The sampling and double-counting lemmas are adapted from @mucoucah’s
merged Erdős 107 even reduction (f28bdc2). We use the cups–caps and four-point
lemmas from the odd reduction. Alternating completion gaps give large parts
whose transversal triples have a single orientation. -/

namespace Layout107
open Finset
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


end Layout107
namespace Layout107
open Finset
open OMA.R_Erdos107_variants_su_bound_R1_H2_R1.SukOdd
abbrev P := ℝ × ℝ
def det (a b c : P) := (b.1-a.1)*(c.2-b.2) - (b.2-a.2)*(c.1-b.1)
instance : Fact (∀ a b c : P, det a b c = (b.1-a.1)*(c.2-b.2) - (b.2-a.2)*(c.1-b.1)) := ⟨fun _ _ _ => rfl⟩
def turn (up : Bool) (p q r : P) : Prop := if up then 0 < det p q r else det p q r < 0

lemma splice {u : Bool} {p a b q c d r : P}
    (hpa : p.1<a.1) (hab : a.1<b.1) (hbq : b.1<q.1)
    (hqc : q.1<c.1) (hcd : c.1<d.1) (hdr : d.1<r.1)
    (h1 : turn u p a b) (h2 : turn u a b q) (h3 : turn u b q c)
    (h4 : turn u q c d) (h5 : turn u c d r) : turn u p q r := by
  have h₆ := (turn_quad (orient:=det) (up:=u) hpa hab hbq h1 h2).2
  have h₇ := (turn_quad (orient:=det) (up:=u) (hpa.trans hab) hbq hqc h₆ h3).2
  have h₈ := (turn_quad (orient:=det) (up:=u) ((hpa.trans hab).trans hbq) hqc hcd h₇ h4).1
  have h₉ := (turn_quad (orient:=det) (up:=u) hqc hcd hdr h4 h5).2
  exact (turn_quad (orient:=det) (up:=u) ((hpa.trans hab).trans hbq) (hqc.trans hcd) hdr h₈ h₉).1

def gap {k : ℕ} (u : Bool) (a : Fin (k+1) → P) (i : Fin k) (p : P) : Prop :=
  (a ⟨i,by omega⟩).1 < p.1 ∧ p.1 < (a ⟨i.val+1,by omega⟩).1 ∧
    ∀ j l : Fin (k+1), j<l →
      if l.val ≤ i.val then turn u (a j) (a l) p
      else if i.val < j.val then turn u p (a j) (a l) else turn u (a j) p (a l)

lemma separated {k : ℕ} {u : Bool} {a : Fin (k+1) → P}
    (ha : StrictMono fun i => (a i).1) {i j : Fin k} (hij : i<j)
    {p q : P} (hp : gap u a i p) (hq : gap u a j q) : p.1<q.1 :=
  (hp.2.1.trans_le (ha.monotone (show (⟨i.val+1,by omega⟩ : Fin (k+1)) ≤ ⟨j,by omega⟩ by
    exact Fin.mk_le_mk.mpr (by have := Fin.lt_def.mp hij; omega)))).trans hq.1

lemma sparse_turn {k : ℕ} {u : Bool} {a : Fin (k+1) → P}
    (ha : StrictMono fun i => (a i).1) {i j l : Fin k}
    (hij : i.val+2 ≤ j.val) (hjl : j.val+2 ≤ l.val)
    {p q r : P} (hp : gap u a i p) (hq : gap u a j q) (hr : gap u a l r) : turn u p q r := by
  let A : Fin (k+1) := ⟨j.val-1,by omega⟩
  let B : Fin (k+1) := ⟨j.val,by omega⟩
  let C : Fin (k+1) := ⟨j.val+1,by omega⟩
  let D : Fin (k+1) := ⟨j.val+2,by omega⟩
  have ab : A<B := Fin.mk_lt_mk.mpr (by omega)
  have bc : B<C := Fin.mk_lt_mk.mpr (by omega)
  have cd : C<D := Fin.mk_lt_mk.mpr (by omega)
  apply splice (a:=a A) (b:=a B) (c:=a C) (d:=a D)
  · exact hp.2.1.trans_le (ha.monotone (Fin.mk_le_mk.mpr (by omega)))
  · exact ha ab
  · exact hq.1
  · exact hq.2.1
  · exact ha cd
  · exact (ha.monotone (show D ≤ ⟨l.val,by omega⟩ from Fin.mk_le_mk.mpr hjl)).trans_lt hr.1
  · simpa only [if_neg (show ¬B.val ≤ i.val by dsimp [B]; omega),
      if_pos (show i.val < A.val by dsimp [A]; omega)] using hp.2.2 A B ab
  · simpa only [if_pos (show B.val ≤ j.val by rfl)] using hq.2.2 A B ab
  · simpa only [if_neg (show ¬C.val ≤ j.val by dsimp [C]; omega),
      if_neg (show ¬j.val < B.val by dsimp [B]; omega)] using hq.2.2 B C bc
  · simpa only [if_neg (show ¬D.val ≤ j.val by dsimp [D]; omega),
      if_pos (show j.val < C.val by dsimp [C]; omega)] using hq.2.2 C D cd
  · simpa only [if_pos (show D.val ≤ l.val from hjl)] using hr.2.2 C D cd

lemma ordered {d : ℕ} {u : Bool} {Y : Finset P} (hy : Y.card = d)
    (hinj : Set.InjOn Prod.fst (Y : Set P))
    (ht : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1<b.1 → b.1<c.1 → turn u a b c) :
    ∃ e : Fin d → P, (∀ i, e i ∈ Y) ∧ StrictMono (fun i => (e i).1) ∧
      ∀ i j l, i<j → j<l → turn u (e i) (e j) (e l) := by
  classical
  let Z := Y.image Prod.fst
  have hz : Z.card=d := (Finset.card_image_of_injOn hinj).trans hy
  let g := Z.orderEmbOfFin hz
  choose e he hyx using fun i : Fin d => Finset.mem_image.mp (Z.orderEmbOfFin_mem hz i)
  have hm : StrictMono fun i => (e i).1 := by
    intro i j hij
    simpa only [hyx] using g.strictMono hij
  exact ⟨e,he,hm,fun i j l hij hjl => ht _ (he i) _ (he j) _ (he l) (hm hij) (hm hjl)⟩

lemma hit (k : ℕ) (hk : 0<k) : ∃ n : ℕ, 2*k+1≤n ∧
    ∀ X : Finset P, X.card=n → Set.InjOn Prod.fst (X:Set P) →
    (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1<b.1 → b.1<c.1 → det a b c ≠ 0) →
    ∃ (u : Bool) (e : Fin (2*k+1) → P), (∀ i, e i ∈ X) ∧ StrictMono (fun i => (e i).1) ∧
      ∀ i j l, i<j → j<l → turn u (e i) (e j) (e l) := by
  let s := 2*k-1
  have hs : s+2=2*k+1 := by dsimp [s]; omega
  refine ⟨(s+s).choose s+(2*k+1),by omega,?_⟩
  intro X hn hi hg
  rcases cups_caps_planar (orient:=det) s s X ⟨hi,hg⟩ (by omega) with h|h
  · obtain ⟨Y,hY,hy,hinj,ht⟩ := h
    obtain ⟨e,he,hm,hv⟩ := ordered (u:=true) (hy.trans hs) hinj ht
    exact ⟨true,e,fun i => hY (he i),hm,hv⟩
  · obtain ⟨Y,hY,hy,hinj,ht⟩ := h
    obtain ⟨e,he,hm,hv⟩ := ordered (u:=false) (hy.trans hs) hinj ht
    exact ⟨false,e,fun i => hY (he i),hm,hv⟩
end Layout107

namespace Layout107
open Finset
open OMA.R_Erdos107_variants_su_bound_R1_H2_R1.SukOdd

theorem layout (m : ℕ) : ∃ C : ℕ, ∀ (X : Finset P) (L : ℕ),
    Set.InjOn Prod.fst (X:Set P) →
    (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1<b.1 → b.1<c.1 → det a b c ≠ 0) →
    C*(L+1)<X.card → ∃ S : ℕ → Finset P,
      (∀ i < m, S i ⊆ X ∧ L<(S i).card) ∧
      (∀ i < m, ∀ j < m, i≠j → Disjoint (S i) (S j)) ∧
      ∀ i j l, i<j → j<l → l < m → ∀ p ∈ S i, ∀ q ∈ S j, ∀ r ∈ S l, det p q r<0 := by
  classical
  let k := 2*m+3
  have hk : 0<k := by dsimp [k]; omega
  obtain ⟨n,hn,hsamp⟩ := hit k hk
  let F := 2 * (2 ^ (2*k+1) * (2*k+1).factorial * n.choose (2*k+1))
  let C := max n (max (4*k) F)
  refine ⟨C,?_⟩
  intro X L hi hg hx
  have hC : C ≤ C*(L+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hnX : n≤X.card := (le_max_left _ _).trans (hC.trans hx.le)
  have hkX : 4*k≤X.card := (le_max_left _ _).trans ((le_max_right _ _).trans (hC.trans hx.le))
  have hFX : F*L<X.card :=
    (Nat.mul_le_mul ((le_max_right _ _).trans (le_max_right _ _)) (Nat.le_succ _)).trans_lt hx
  obtain ⟨u,a,_,ha,_,hr⟩ := dense_ordered_regions_abs turn X hk hn hnX hkX
    (fun U hU hnU => hsamp U hnU (hi.mono hU) (fun p hp q hq r hr => hg p (hU hp) q (hU hq) r (hU hr))) hFX
  let g (i : ℕ) : Fin k := ⟨2*min i m, by dsimp [k]; have := Nat.min_le_right i m; omega⟩
  let R (i : ℕ) := X.filter (gap u a (g i))
  have hs (i : ℕ) : R i ⊆ X ∧ L < (R i).card := by
    refine ⟨filter_subset _ _, ?_⟩
    convert! hr (g i) using 2
    ext p
    simp [R,gap]
  have hg' (i : ℕ) (h : i < m) : (g i).val = 2*i := by simp [g,min_eq_left h.le]
  have dis {i j : ℕ} (hij : i<j) (hj : j < m) : Disjoint (R i) (R j) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hf : g i<g j := Fin.lt_def.mpr (by rw [hg' i (hij.trans hj),hg' j hj]; omega)
    exact (separated ha hf (mem_filter.mp hp).2 (mem_filter.mp hq).2).false
  have ds (i : ℕ) (hi : i < m) (j : ℕ) (hj : j < m) (hij : i≠j) : Disjoint (R i) (R j) := by
    rcases lt_or_gt_of_ne hij with hl|hr
    · exact dis hl hj
    · exact (dis hr hi).symm
  have triple {i j l : ℕ} (hij : i<j) (hjl : j<l) (hl : l < m)
      {p q r : P} (hp : p∈R i) (hq : q∈R j) (hr : r∈R l) : turn u p q r := by
    apply sparse_turn ha (i:=g i) (j:=g j) (l:=g l) _ _
      (mem_filter.mp hp).2 (mem_filter.mp hq).2 (mem_filter.mp hr).2
    · rw [hg' i (hij.trans (hjl.trans hl)),hg' j (hjl.trans hl)]; omega
    · rw [hg' j (hjl.trans hl),hg' l hl]; omega
  cases hh : u with
  | false =>
    exact ⟨R,fun i _ => hs i,ds,fun _ _ _ hij hjl hl _ hp _ hq _ hr =>
      by simpa only [hh,turn,Bool.false_eq_true,if_false] using triple hij hjl hl hp hq hr⟩
  | true =>
    refine ⟨fun i => R (m-1-i),fun i _ => hs _,fun i hi j hj h => ds _ (by omega) _ (by omega) (by omega),?_⟩
    intro i j l hij hjl hl p hp q hq r hr
    have hturn := triple (i:=m-1-l) (j:=m-1-j) (l:=m-1-i) (by omega) (by omega) (by omega) hr hq hp
    have hrev := orient_reverse (orient:=det) p q r
    simp only [hh,turn,if_true] at hturn
    linarith

end Layout107

theorem OMA.solution : OMA.R_Erdos107_variants_su_bound_R1_H2_R1.H1 := by
  intro m
  obtain ⟨C,hC⟩ := Layout107.layout m
  exact ⟨C,fun X L _ hi hg hx => hC X L hi hg hx⟩

