import FormalConjectures.ErdosProblems.«604»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1
open Filter Finset Erdos604
open scoped Classical EuclideanGeometry

private lemma image_count {α β γ : Type} [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a b, f a = f b ↔ g a = g b) : (S.image f).card = (S.image g).card := by
  classical
  have one {X Y : Type} [DecidableEq X] [DecidableEq Y] (u : α → X) (v : α → Y)
      (hle : ∀ a b, u a = u b → v a = v b) : (S.image v).card ≤ (S.image u).card := by
    by_cases hS : S.Nonempty
    · haveI : Nonempty α := ⟨hS.choose⟩
      let pick (x : X) : α := Function.invFun u x
      have eq : S.image v = (S.image u).image (fun x ↦ v (pick x)) := by
        rw [image_image]
        apply image_congr
        intro a ha
        apply hle
        exact (Function.invFun_eq ⟨a,rfl⟩).symm
      rw [eq]
      exact card_image_le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  exact le_antisymm (one g f fun a b ↦ (h a b).mpr) (one f g fun a b ↦ (h a b).mp)

/-- The weak pinned bound in the arithmetic model. Only patterns of product
equalities realizable by planar distances are needed. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)), NumberField K →
  (∃ i : K, i^2 = -1) → ∀ u v : ι → K, Function.Injective u → Function.Injective v →
  let d := fun a b ↦ (u a - u b) * (v a - v b)
  (∃ x : ι → ℝ², Function.Injective x ∧
    ∀ a b c e, d a b = d c e ↔ dist (x a) (x b) = dist (x c) (x e)) →
  ∃ a : ι, (n : ℝ)^(1-ε) ≤ (((univ.erase a).image (fun b ↦ d b a)).card : ℝ)

/-- Finite planar configurations admit a faithful factorization of their
distance equalities over a number field containing a square root of minus one. -/
def H2 : Prop := ∀ (ι : Type) [Finite ι] (x : ι → ℝ²), Function.Injective x →
  ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), NumberField K ∧
  ∃ (i : K) (u v : ι → K), i^2 = -1 ∧ Function.Injective u ∧ Function.Injective v ∧
  ∀ a b c d, (u a - u b) * (v a - v b) = (u c - u d) * (v c - v d) ↔
    dist (x a) (x b) = dist (x c) (x d)

theorem main : H1 → H2 → type_of% @Erdos604.erdos_604.variants.katz_tardos := by
  classical
  intro arith model ε hε
  filter_upwards [arith ε hε, eventually_ge_atTop 1] with n ha hn
  let vals := {m : ℕ | ∃ A : Finset ℝ², A.card = n ∧ A.sup (distinctDistancesFrom A) = m}
  have nonempty : vals.Nonempty := by
    obtain ⟨A,hA⟩ := Infinite.exists_subset_card_eq ℝ² n
    exact ⟨_,A,hA,rfl⟩
  obtain ⟨A,hA,hmin⟩ := Nat.sInf_mem nonempty
  change A.sup (distinctDistancesFrom A) = pinnedDistinctDistances n at hmin
  let x (a : A) : ℝ² := a.val
  obtain ⟨K,hK,i,u,v,hi,hu,hv,hp⟩ := model A x Subtype.val_injective
  obtain ⟨a,hpin⟩ := ha A (by simpa using hA) K hK ⟨i,hi⟩ u v hu hv ⟨x,Subtype.val_injective,hp⟩
  have im := image_count (univ.erase a) (fun b ↦ (u b-u a)*(v b-v a))
    (fun b ↦ dist (x b) (x a)) (fun p q ↦ hp p a q a)
  have eq : ((univ.erase a).image (fun b ↦ dist (x b) (x a))) =
      (A.erase a.val).image (fun b ↦ dist b a.val) := by
    ext d
    simp only [mem_image,mem_erase,mem_univ,true_and,and_true]
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.val,⟨fun h ↦ hb (Subtype.ext h),b.property⟩,rfl⟩
    · rintro ⟨b,⟨hne,hb⟩,rfl⟩
      exact ⟨⟨b,hb⟩,fun h ↦ hne (congrArg Subtype.val h),rfl⟩
  change (n : ℝ)^(1-ε) ≤ ((((univ.erase a).image (fun b ↦ (u b-u a)*(v b-v a))).card : ℕ) : ℝ) at hpin
  rw [im,eq] at hpin
  have le := Finset.le_sup (f := distinctDistancesFrom A) a.property
  rw [hmin] at le
  have he := Real.exp_one_lt_d9
  have hc : (48 - 14 * Real.exp 1) / (55 - 16 * Real.exp 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < 55-16*Real.exp 1)).mpr
    linarith
  apply (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (sub_le_sub_right hc ε)).trans
  have le' : ((A.erase a.val).image (fun b ↦ dist b a.val)).card ≤ pinnedDistinctDistances n := by
    have count : ((A.erase a.val).image (fun b ↦ dist b a.val)).card = distinctDistancesFrom A a.val := by
      unfold distinctDistancesFrom
      apply congrArg Finset.card
      ext y
      simp
    exact count.trans_le le
  exact hpin.trans (by exact_mod_cast le')

end OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1
