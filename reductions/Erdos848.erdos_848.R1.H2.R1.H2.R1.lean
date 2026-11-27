import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1
import Mathlib

/-! The residue and parity classification is adapted from MacchaCat/erdos848,
commit 99b8d9bf40fdd090a2a117328c5707ca21ec748e, Apache-2.0. Every
point of the enlarged set is tested against a representative of its type.
The points of the enlarged set need not be pairwise compatible. -/
namespace OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
open Finset Classical

def H1 : Prop := open scoped Classical in ∀ N : ℕ, 160000000≤N → N<2^2300 →
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  ∀ b b', Witness b → b % 25 = 7 → Witness b' → b' % 25 = 18 →
    badCount (fun a => a % 25 = 18) b + badCount (fun a => a % 25 = 7) b' ≤ c7

def H2 : Prop := open scoped Classical in ∀ N : ℕ, 2^2300≤N →
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  ∀ b b', Witness b → b % 25 = 7 → Witness b' → b' % 25 = 18 →
    badCount (fun a => a % 25 = 18) b + badCount (fun a => a % 25 = 7) b' ≤ c7

def H3 : Prop := open scoped Classical in ∀ N : ℕ, 160000000≤N →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let lemCCount (b : ℕ) := ((Icc 1 N).filter (fun a => IsStar a ∧ ¬ Squarefree (a*a+1) ∧ ¬ Squarefree (a*b+1))).card
  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b, Witness b → IsStar b → b % 2 = 0 →
    badCount (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount b ≤ c7) ∧
  (∀ b₁ b₃, Witness b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount (fun x => IsStar x ∧ x % 2 = 1) ≤ c7)

def H4 : Prop := open scoped Classical in ∀ N : ℕ, 160000000≤N →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let classCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter P).card
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 18) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 7) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7)

lemma card_le_two {A : Finset ℕ} (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a ∈ A, P a ∨ Q a) : A.card ≤ (A.filter P).card + (A.filter Q).card := by
  calc A.card ≤ (A.filter P ∪ A.filter Q).card := by
        apply card_le_card; intro a ha
        rcases h a ha with hp | hq
        · exact mem_union_left _ (mem_filter.mpr ⟨ha, hp⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨ha, hq⟩)
    _ ≤ _ := card_union_le _ _

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos848_erdos_848_R1_H2_R1.H2 := by
  classical
  intro low high mixed single N hN W
  obtain ⟨pcaseII,pcaseIII1⟩ := mixed N hN
  obtain ⟨pcaseIII2a,pcaseIII2b7,pcaseIII2b18⟩ := single N hN
  intro key subW _size _inj compat _mixed7 _mixed18
  let A := (Icc 1 N).filter fun x =>
    ¬ Squarefree (x*x+1) ∧ (∀ w ∈ W, ¬ Squarefree (x*w+1)) ∧ ∃ w ∈ W, key w=key x ∧ w≤x
  change A.card ≤ _
  have represented (x : ℕ) (hx : x∈A) : ∃ w∈W,key w=key x := by
    obtain ⟨w,hw,e,_⟩ := (mem_filter.mp hx).2.2.2
    exact ⟨w,hw,e⟩
  let rep (x : ℕ) := if hx : x∈A then (represented x hx).choose else x
  have repFacts {x : ℕ} (hx : x∈A) : rep x∈W ∧ key (rep x)=key x := by
    simpa only [rep,dif_pos hx] using (represented x hx).choose_spec
  have repr {x : ℕ} (hx : x∈A) : (rep x%25=7 ↔ x%25=7) ∧
      (rep x%25=18 ↔ x%25=18) ∧ rep x%4=x%4 ∧ rep x%2=x%2 := by
    have eq := (repFacts hx).2
    dsimp only [key] at eq
    split_ifs at eq <;> omega
  have diag {x : ℕ} (hx : x∈A) := (mem_filter.mp hx).2.1
  have edge {x b : ℕ} (hx : x∈A) (hb : b∈A) := (mem_filter.mp hx).2.2.1 (rep b) (repFacts hb).1
  have hsub : A ⊆ Icc 1 N := filter_subset _ _
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let classCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter P).card
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*rep b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let lemCCount (b : ℕ) := ((Icc 1 N).filter (fun a => IsStar a ∧ ¬ Squarefree (a*a+1) ∧ ¬ Squarefree (a*rep b+1))).card
  let Witness (b : ℕ) := b∈Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  change A.card ≤ c7
  have caseIb : ∀ b b', (fun b => b∈A) b → b % 25 = 7 → (fun b => b∈A) b' → b' % 25 = 18 →
    badCount (fun a => a % 25 = 18) b + badCount (fun a => a % 25 = 7) b' ≤ c7 := by
    intro b b' hb h7 hb' h18
    have orig (b b' : ℕ) (hb : Witness b) (h7 : b%25=7) (hb' : Witness b') (h18 : b'%25=18) :
        ((Icc 1 N).filter (fun a => a%25=18 ∧ ¬Squarefree (a*b+1))).card +
        ((Icc 1 N).filter (fun a => a%25=7 ∧ ¬Squarefree (a*b'+1))).card ≤ c7 := by
      by_cases h : N<2^2300
      · exact low N hN h b b' hb h7 hb' h18
      · exact high N (by omega) b b' hb h7 hb' h18
    apply orig (rep b) (rep b')
    all_goals first
      | exact ⟨subW (repFacts hb).1,compat _ (repFacts hb).1 _ (repFacts hb).1⟩
      | exact ⟨subW (repFacts hb').1,compat _ (repFacts hb').1 _ (repFacts hb').1⟩
      | exact (repr hb).1.mpr h7
      | exact (repr hb').2.1.mpr h18
      | exact (repr hb').1.mpr h7
      | exact ⟨fun h => hs.1 ((repr hb).1.mp h),fun h => hs.2 ((repr hb).2.1.mp h)⟩
      | exact ⟨fun h => hs'.1 ((repr hb').1.mp h),fun h => hs'.2 ((repr hb').2.1.mp h)⟩
      | exact (repr hb).2.2.1.trans he
      | exact (repr hb).2.2.2.trans he
      | exact (repr hb').2.2.1.trans he'
      | exact (repr hb').2.2.2.trans he'
      | exact hr
  have caseII : ∀ b, (fun b => b∈A) b → IsStar b → b % 2 = 0 →
    badCount (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount b ≤ c7 := by
    intro b hb hs he
    apply pcaseII (rep b)
    all_goals first
      | exact ⟨subW (repFacts hb).1,compat _ (repFacts hb).1 _ (repFacts hb).1⟩
      | exact ⟨subW (repFacts hb').1,compat _ (repFacts hb').1 _ (repFacts hb').1⟩
      | exact (repr hb).1.mpr h7
      | exact (repr hb').2.1.mpr h18
      | exact (repr hb').1.mpr h7
      | exact ⟨fun h => hs.1 ((repr hb).1.mp h),fun h => hs.2 ((repr hb).2.1.mp h)⟩
      | exact ⟨fun h => hs'.1 ((repr hb').1.mp h),fun h => hs'.2 ((repr hb').2.1.mp h)⟩
      | exact (repr hb).2.2.1.trans he
      | exact (repr hb).2.2.2.trans he
      | exact (repr hb').2.2.1.trans he'
      | exact (repr hb').2.2.2.trans he'
      | exact hr
  have caseIII1 : ∀ b₁ b₃, (fun b => b∈A) b₁ → IsStar b₁ → b₁ % 4 = 1 → (fun b => b∈A) b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount (fun x => IsStar x ∧ x % 2 = 1) ≤ c7 := by
    intro b b' hb hs he hb' hs' he'
    apply pcaseIII1 (rep b) (rep b')
    all_goals first
      | exact ⟨subW (repFacts hb).1,compat _ (repFacts hb).1 _ (repFacts hb).1⟩
      | exact ⟨subW (repFacts hb').1,compat _ (repFacts hb').1 _ (repFacts hb').1⟩
      | exact (repr hb).1.mpr h7
      | exact (repr hb').2.1.mpr h18
      | exact (repr hb').1.mpr h7
      | exact ⟨fun h => hs.1 ((repr hb).1.mp h),fun h => hs.2 ((repr hb).2.1.mp h)⟩
      | exact ⟨fun h => hs'.1 ((repr hb').1.mp h),fun h => hs'.2 ((repr hb').2.1.mp h)⟩
      | exact (repr hb).2.2.1.trans he
      | exact (repr hb).2.2.2.trans he
      | exact (repr hb').2.2.1.trans he'
      | exact (repr hb').2.2.2.trans he'
      | exact hr
  have caseIII2a : ∀ b r, (fun b => b∈A) b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7 := by
    intro b r hb hs he hr
    apply pcaseIII2a (rep b) r
    all_goals first
      | exact ⟨subW (repFacts hb).1,compat _ (repFacts hb).1 _ (repFacts hb).1⟩
      | exact ⟨subW (repFacts hb').1,compat _ (repFacts hb').1 _ (repFacts hb').1⟩
      | exact (repr hb).1.mpr h7
      | exact (repr hb').2.1.mpr h18
      | exact (repr hb').1.mpr h7
      | exact ⟨fun h => hs.1 ((repr hb).1.mp h),fun h => hs.2 ((repr hb).2.1.mp h)⟩
      | exact ⟨fun h => hs'.1 ((repr hb').1.mp h),fun h => hs'.2 ((repr hb').2.1.mp h)⟩
      | exact (repr hb).2.2.1.trans he
      | exact (repr hb).2.2.2.trans he
      | exact (repr hb').2.2.1.trans he'
      | exact (repr hb').2.2.2.trans he'
      | exact hr
  have caseIII2b7 : ∀ b b' r, (fun b => b∈A) b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    (fun b => b∈A) b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 18) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7 := by
    intro b b' r hb hs he hr hb' h7 he'
    apply pcaseIII2b7 (rep b) (rep b') r
    all_goals first
      | exact ⟨subW (repFacts hb).1,compat _ (repFacts hb).1 _ (repFacts hb).1⟩
      | exact ⟨subW (repFacts hb').1,compat _ (repFacts hb').1 _ (repFacts hb').1⟩
      | exact (repr hb).1.mpr h7
      | exact (repr hb').2.1.mpr h18
      | exact (repr hb').1.mpr h7
      | exact ⟨fun h => hs.1 ((repr hb).1.mp h),fun h => hs.2 ((repr hb).2.1.mp h)⟩
      | exact ⟨fun h => hs'.1 ((repr hb').1.mp h),fun h => hs'.2 ((repr hb').2.1.mp h)⟩
      | exact (repr hb).2.2.1.trans he
      | exact (repr hb).2.2.2.trans he
      | exact (repr hb').2.2.1.trans he'
      | exact (repr hb').2.2.2.trans he'
      | exact hr
  have caseIII2b18 : ∀ b b' r, (fun b => b∈A) b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    (fun b => b∈A) b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 7) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7 := by
    intro b b' r hb hs he hr hb' h18 he'
    apply pcaseIII2b18 (rep b) (rep b') r
    all_goals first
      | exact ⟨subW (repFacts hb).1,compat _ (repFacts hb).1 _ (repFacts hb).1⟩
      | exact ⟨subW (repFacts hb').1,compat _ (repFacts hb').1 _ (repFacts hb').1⟩
      | exact (repr hb).1.mpr h7
      | exact (repr hb').2.1.mpr h18
      | exact (repr hb').1.mpr h7
      | exact ⟨fun h => hs.1 ((repr hb).1.mp h),fun h => hs.2 ((repr hb).2.1.mp h)⟩
      | exact ⟨fun h => hs'.1 ((repr hb').1.mp h),fun h => hs'.2 ((repr hb').2.1.mp h)⟩
      | exact (repr hb).2.2.1.trans he
      | exact (repr hb).2.2.2.trans he
      | exact (repr hb').2.2.1.trans he'
      | exact (repr hb').2.2.2.trans he'
      | exact hr
  have filter_le_bad {b : ℕ} (hb : b ∈ A)
      (P : ℕ → Prop) [DecidablePred P] : (A.filter P).card ≤ badCount P b := by
    apply card_le_card; intro a ha
    rw [mem_filter] at ha
    exact mem_filter.mpr ⟨hsub ha.1, ha.2, edge ha.1 hb⟩

  have filter_le_class (P : ℕ → Prop) [DecidablePred P] :
      (A.filter P).card ≤ classCount P := by
    apply card_le_card; intro a ha
    rw [mem_filter] at ha
    exact mem_filter.mpr ⟨hsub ha.1, ha.2⟩

  have filter_le_v (P : ℕ → Prop) [DecidablePred P] :
      (A.filter P).card ≤ vCount P := by
    apply card_le_card; intro a ha
    rw [mem_filter] at ha
    exact mem_filter.mpr ⟨hsub ha.1, ha.2, diag ha.1⟩

  have class7_eq_c7 : classCount (fun a => a%25=7)=c7 := rfl
  have class18_le_c7 : classCount (fun a => a%25=18) ≤ c7 := by
    apply card_le_card_of_injOn (fun a => a-11)
    · intro a ha; simp only [coe_filter,Set.mem_ofPred_eq,mem_Icc] at ha ⊢
      exact ⟨⟨by omega,by omega⟩,by omega⟩
    · intro a ha b hb h
      simp only [coe_filter,Set.mem_ofPred_eq,mem_Icc] at ha hb
      change a-11=b-11 at h
      omega
  -- the three parts
  have hsplit : A.card ≤ (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card +
      (A.filter IsStar).card :=
    card_le_two _ _ (fun a _ => by dsimp [IsStar]; omega)
  by_cases hII : ∃ b ∈ A, IsStar b ∧ b % 2 = 0
  · -- Case II
    obtain ⟨b, hb, hbs, hbe⟩ := hII
    have h1 := filter_le_bad hb (fun a => a % 25 = 7 ∨ a % 25 = 18)
    have h2 : (A.filter IsStar).card ≤ lemCCount b := by
      apply card_le_card; intro x hx
      rw [mem_filter] at hx
      exact mem_filter.mpr ⟨hsub hx.1, hx.2, diag hx.1, edge hx.1 hb⟩
    have := caseII b (hb) hbs hbe
    omega
  push Not at hII
  -- from here on every element of A* is odd
  have hodd : ∀ x ∈ A, IsStar x → x % 2 = 1 := fun x hx hs => by
    have := hII x hx hs; omega
  by_cases hIII1 : ∃ b₁ ∈ A, ∃ b₃ ∈ A, IsStar b₁ ∧ b₁ % 4 = 1 ∧ IsStar b₃ ∧ b₃ % 4 = 3
  · -- Case III.1
    obtain ⟨b₁, hb₁, b₃, hb₃, hs₁, hr₁, hs₃, hr₃⟩ := hIII1
    have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
        badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ := by
      have := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 4 = 1 ∨ a % 2 = 0) (fun a => a % 4 = 3) (fun a _ => by omega)
      have unionBound := this
      have subbound (P : ℕ → Prop) [DecidablePred P] :
          ((A.filter (fun a => a%25=7 ∨ a%25=18)).filter P).card ≤
            (A.filter (fun a => (a%25=7 ∨ a%25=18) ∧ P a)).card := by
        apply card_le_card; intro a ha
        obtain ⟨ha,hp⟩ := mem_filter.mp ha
        obtain ⟨ha,hc⟩ := mem_filter.mp ha
        exact mem_filter.mpr ⟨ha,hc,hp⟩
      have c₁ := subbound (fun a => a%4=1 ∨ a%2=0)
      have c₂ := subbound (fun a => a%4=3)
      have e1 := filter_le_bad hb₁ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0))
      have e2 := filter_le_bad hb₃ (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3)
      omega
    have hS : (A.filter IsStar).card ≤ vCount (fun x => IsStar x ∧ x % 2 = 1) := by
      calc (A.filter IsStar).card = (A.filter (fun x => IsStar x ∧ x % 2 = 1)).card := by
            congr 1; apply filter_congr; intro x hx
            exact ⟨fun hs => ⟨hs, hodd x hx hs⟩, fun h => h.1⟩
        _ ≤ _ := filter_le_v _
    have := caseIII1 b₁ b₃ (hb₁) hs₁ hr₁ (hb₃) hs₃ hr₃
    omega
  push Not at hIII1
  by_cases hStar : ∃ b ∈ A, IsStar b
  · -- Case III.2: all of A* lies in the residue class r = b mod 4
    obtain ⟨b, hb, hbs⟩ := hStar
    set r := b % 4 with hr
    have hr13 : r = 1 ∨ r = 3 := by have := hodd b hb hbs; omega
    have hAllr : ∀ x ∈ A, IsStar x → x % 4 = r := by
      intro x hx hxs
      have hxo := hodd x hx hxs
      rcases hr13 with h1 | h3
      · by_contra hne
        exact hIII1 b hb x hx hbs (by omega) hxs (by omega)
      · by_contra hne
        exact hIII1 x hx b hb hxs (by omega) hbs (by omega)
    have hS : (A.filter IsStar).card ≤ vCount (fun x => IsStar x ∧ x % 4 = r) := by
      calc (A.filter IsStar).card = (A.filter (fun x => IsStar x ∧ x % 4 = r)).card := by
            congr 1; apply filter_congr; intro x hx
            exact ⟨fun hs => ⟨hs, hAllr x hx hs⟩, fun h => h.1⟩
        _ ≤ _ := filter_le_v _
    have hwb := hb
    by_cases hEven : ∃ b' ∈ A, (b' % 25 = 7 ∨ b' % 25 = 18) ∧ b' % 2 = 0
    · obtain ⟨b', hb', h78, hbe'⟩ := hEven
      have hwb' := hb'
      rcases h78 with h7 | h18
      · -- III.2.b, even witness in A₇
        have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
            classCount (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
            badCount (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
            badCount (fun a => a % 25 = 18) b' := by
          have c1 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
            (fun a => a % 25 = 7) (fun a => a % 25 = 18) (fun a ha => (mem_filter.mp ha).2)
          have c2 := card_le_two (A := (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter (fun a => a % 25 = 7))
            (fun a => a % 4 = 4 - r) (fun a => a % 4 = r ∨ a % 2 = 0) (fun a _ => by omega)
          simp only [filter_filter] at c1 c2
          have e1 := filter_le_class (fun a => a % 25 = 7 ∧ a % 4 = 4 - r)
          have e2 := filter_le_bad hb (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0))
          have e3 := filter_le_bad hb' (fun a => a % 25 = 18)
          have s1 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7) ∧ a % 4 = 4 - r)).card ≤
              (A.filter fun a => a % 25 = 7 ∧ a % 4 = 4 - r).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s2 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7) ∧ (a % 4 = r ∨ a % 2 = 0))).card ≤
              (A.filter fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s3 : ((A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18)).card ≤
              (A.filter fun a => a % 25 = 18).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
          omega
        have := caseIII2b7 b b' r hwb hbs rfl hr13 hwb' h7 hbe'
        omega
      · -- III.2.b, even witness in A₁₈
        have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
            classCount (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
            badCount (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
            badCount (fun a => a % 25 = 7) b' := by
          have c1 := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
            (fun a => a % 25 = 18) (fun a => a % 25 = 7) (fun a ha => (mem_filter.mp ha).2.symm)
          have c2 := card_le_two (A := (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).filter (fun a => a % 25 = 18))
            (fun a => a % 4 = 4 - r) (fun a => a % 4 = r ∨ a % 2 = 0) (fun a _ => by omega)
          simp only [filter_filter] at c1 c2
          have e1 := filter_le_class (fun a => a % 25 = 18 ∧ a % 4 = 4 - r)
          have e2 := filter_le_bad hb (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0))
          have e3 := filter_le_bad hb' (fun a => a % 25 = 7)
          have s1 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18) ∧ a % 4 = 4 - r)).card ≤
              (A.filter fun a => a % 25 = 18 ∧ a % 4 = 4 - r).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s2 : ((A.filter fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18) ∧ (a % 4 = r ∨ a % 2 = 0))).card ≤
              (A.filter fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1.2, ha.2.2⟩)
          have s3 : ((A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7)).card ≤
              (A.filter fun a => a % 25 = 7).card :=
            card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
          omega
        have := caseIII2b18 b b' r hwb hbs rfl hr13 hwb' h18 hbe'
        omega
    · -- III.2.a: A₇ ∪ A₁₈ all odd
      push Not at hEven
      have hA78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
          classCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
          badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b := by
        have c := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
          (fun a => a % 4 = 4 - r) (fun a => a % 4 = r) (fun a ha => by
            have ha' := mem_filter.mp ha
            have := hEven a ha'.1 ha'.2
            omega)
        simp only [filter_filter] at c
        have e1 := filter_le_class (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r)
        have e2 := filter_le_bad hb (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r)
        omega
      have := caseIII2a b r hwb hbs rfl hr13
      omega
  · -- Case I: A* = ∅
    push Not at hStar
    have hS0 : (A.filter IsStar).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => hStar x hx
    have h78 : (A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18)).card ≤
        (A.filter (fun a => a % 25 = 7)).card + (A.filter (fun a => a % 25 = 18)).card := by
      have c := card_le_two (A := A.filter (fun a => a % 25 = 7 ∨ a % 25 = 18))
        (fun a => a % 25 = 7) (fun a => a % 25 = 18) (fun a ha => (mem_filter.mp ha).2)
      simp only [filter_filter] at c
      have s1 : (A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 7).card ≤ (A.filter fun a => a % 25 = 7).card :=
        card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
      have s2 : (A.filter fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 25 = 18).card ≤ (A.filter fun a => a % 25 = 18).card :=
        card_le_card (fun a ha => by simp only [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.2⟩)
      omega
    by_cases h7 : ∃ b ∈ A, b % 25 = 7
    · by_cases h18 : ∃ b' ∈ A, b' % 25 = 18
      · -- I.b
        obtain ⟨b, hb, hb7⟩ := h7
        obtain ⟨b', hb', hb18⟩ := h18
        have e1 := filter_le_bad hb (fun a => a % 25 = 18)
        have e2 := filter_le_bad hb' (fun a => a % 25 = 7)
        have := caseIb b b' (hb) hb7 (hb') hb18
        omega
      · -- I.a with A₁₈ = ∅
        push Not at h18
        have h0 : (A.filter (fun a => a % 25 = 18)).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h18 x hx
        have e := filter_le_class (fun a => a % 25 = 7)
        rw [class7_eq_c7] at e
        omega
    · -- I.a with A₇ = ∅
      push Not at h7
      have h0 : (A.filter (fun a => a % 25 = 7)).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]; exact fun x hx => h7 x hx
      have e := filter_le_class (fun a => a % 25 = 18)
      have := class18_le_c7
      omega

end OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
