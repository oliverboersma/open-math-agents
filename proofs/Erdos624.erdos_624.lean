import FormalConjectures.ErdosProblems.«624»

/-!
Disproof of Erdős Problem 624. Ported from the certified conjectures.io result
6f349986-c876-4902-8b27-52f19652d5cb (solver credited in the PR body; Lean-verified 16 Nov 2026,
certified 19 Nov 2026). Changes: restated the final theorem against the catalogue
declaration, and replaced three lemma names that changed in Mathlib.
-/

theorem omaProdMonoSubset {ι : Type*} {s t : Finset ι} {f g : ι → ℝ} (h : s ⊆ t)
    (hf0 : ∀ i ∈ t, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) (hf1 : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, g i :=
  (Finset.prod_le_prod_of_subset_of_le_one h hf0 hf1).trans
    (Finset.prod_le_prod (fun i hi => hf0 i (h hi)) hfg)

/- Source module Erdos624.Statement. -/

namespace Erdos624

def Statement : Prop :=
  Filter.Tendsto
    (fun n : ℕ => (_root_.Erdos624.H n : ℝ) - Real.logb 2 (n : ℝ))
    Filter.atTop Filter.atTop

end Erdos624

/- Source module Erdos624.Basic. -/

/-!
The covering predicate used by the construction and its connection to the
unchanged Erdős 624 declaration in Formal Conjectures.
-/

namespace Erdos624.Disproof

open Finset Filter

variable {X C D : Type*}

/-- Every sufficiently large source contains a witness for every color. -/
def Covers (f : Finset X → C) (h : ℕ) : Prop :=
  ∀ Y : Finset X, h ≤ Y.card → ∀ c : C, ∃ A : Finset X, A ⊆ Y ∧ f A = c

theorem covers_mono {f : Finset X → C} {h k : ℕ}
    (hf : Covers f h) (hhk : h ≤ k) : Covers f k := by
  intro Y hY c
  exact hf Y (hhk.trans hY) c

theorem covers_of_exact_size {f : Finset X → C} {h : ℕ}
    (hf : ∀ Y : Finset X, Y.card = h → ∀ c : C,
      ∃ A : Finset X, A ⊆ Y ∧ f A = c) : Covers f h := by
  intro Y hY c
  obtain ⟨Z, hZY, hZ⟩ := Finset.exists_subset_card_eq hY
  obtain ⟨A, hAZ, hA⟩ := hf Z hZ c
  exact ⟨A, hAZ.trans hZY, hA⟩

theorem covers_comp {f : Finset X → C} {h : ℕ} (hf : Covers f h)
    {g : C → D} (hg : Function.Surjective g) : Covers (g ∘ f) h := by
  intro Y hY d
  obtain ⟨c, rfl⟩ := hg d
  obtain ⟨A, hAY, hA⟩ := hf Y hY c
  exact ⟨A, hAY, congrArg g hA⟩

theorem covers_restrict {X' : Type*} {f : Finset X → C} {h : ℕ}
    (hf : Covers f h) (e : X' ↪ X) : Covers (fun A => f (A.map e)) h := by
  classical
  intro Y hY c
  obtain ⟨A, hAY, hA⟩ := hf (Y.map e) (by simpa using hY) c
  let A' := Y.filter fun x => e x ∈ A
  have hmap : A'.map e = A := by
    ext x
    simp only [Finset.mem_map, A', Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩
      exact ha
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (hAY hx)
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
  exact ⟨A', Finset.filter_subset _ _, by simpa [hmap] using hA⟩

theorem existsEventuallySurjective_iff_covers (N h : ℕ) :
    _root_.Erdos624.ExistsEventuallySurjective N h ↔
      ∃ f : Finset (Fin N) → Fin N, Covers f h := by
  classical
  unfold _root_.Erdos624.ExistsEventuallySurjective Covers
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro Y hY c
    have hc : c ∈ Y.powerset.image f := by rw [hf Y hY]; exact Finset.mem_univ c
    obtain ⟨A, hA, hAc⟩ := Finset.mem_image.mp hc
    exact ⟨A, Finset.mem_powerset.mp hA, hAc⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro Y hY
    apply Finset.eq_univ_of_forall
    intro c
    obtain ⟨A, hAY, hAc⟩ := hf Y hY c
    exact Finset.mem_image.mpr ⟨A, Finset.mem_powerset.mpr hAY, hAc⟩

theorem H_le_of_cover {N h : ℕ} (hN : 0 < N)
    (hf : ∃ f : Finset (Fin N) → Fin N, Covers f h) : _root_.Erdos624.H N ≤ h := by
  unfold _root_.Erdos624.H
  simp only [hN, ↓reduceIte]
  exact csInf_le (OrderBot.bddBelow _) ((existsEventuallySurjective_iff_covers N h).mpr hf)

/-- A constant upper gap on all sufficiently large multiples of 100 suffices. -/
theorem not_tendsto_of_eventual_power_cover (C : ℕ)
    (hc : ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 100 ∣ d →
      ∃ f : Finset (Fin (2 ^ d)) → Fin (2 ^ d), Covers f (d + C)) :
    ¬ Filter.Tendsto
      (fun N : ℕ => (_root_.Erdos624.H N : ℝ) - Real.logb 2 (N : ℝ))
      Filter.atTop Filter.atTop := by
  intro hlim
  obtain ⟨D, hD⟩ := hc
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (C : ℝ) + 1 ≤ (_root_.Erdos624.H N : ℝ) - Real.logb 2 (N : ℝ) :=
    hlim.eventually (Filter.eventually_ge_atTop ((C : ℝ) + 1))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  let d := 100 * (D + M + 1)
  have hDd : D ≤ d := by dsimp [d]; omega
  have hMd : M ≤ d := by dsimp [d]; omega
  have hddiv : 100 ∣ d := ⟨D + M + 1, rfl⟩
  have hN : 0 < (2 : ℕ) ^ d := by positivity
  have hH := H_le_of_cover hN (hD d hDd hddiv)
  have hlarge : M ≤ (2 : ℕ) ^ d := hMd.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hlog : Real.logb 2 (((2 : ℕ) ^ d : ℕ) : ℝ) = (d : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow]
    norm_num [Real.logb_self_eq_one]
  have hupper : (_root_.Erdos624.H (2 ^ d) : ℝ) ≤ (d : ℝ) + C := by exact_mod_cast hH
  have hlower := hM (2 ^ d) hlarge
  rw [hlog] at hlower
  linarith

end Erdos624.Disproof

/- Source module Erdos624.Linear. -/

namespace Erdos624.Disproof

open Module

section Kernels

variable {F V A B : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup A] [Module F A]
  [AddCommGroup B] [Module F B]

/-- Two proper linear kernels cannot cover the whole domain. -/
theorem zero_or_zero_of_kernel_cover (u : V →ₗ[F] A) (v : V →ₗ[F] B)
    (h : ∀ w : V, u w = 0 ∨ v w = 0) : u = 0 ∨ v = 0 := by
  by_cases hu : u = 0
  · exact Or.inl hu
  right
  apply LinearMap.ext
  intro y
  change v y = 0
  by_contra hy
  obtain ⟨x, hx⟩ : ∃ x : V, u x ≠ 0 := by
    by_contra! hn
    apply hu
    ext x
    exact hn x
  have hvx : v x = 0 := (h x).resolve_left hx
  have huy : u y = 0 := (h y).resolve_right hy
  have hsum := h (x + y)
  rw [map_add, huy, add_zero, map_add, hvx, zero_add] at hsum
  exact hsum.elim hx hy

/-- The preceding dichotomy also holds after restricting to a subspace. -/
theorem vanishes_on_subspace_or (K : Submodule F V)
    (u : V →ₗ[F] A) (v : V →ₗ[F] B)
    (h : ∀ w ∈ K, u w = 0 ∨ v w = 0) :
    (∀ w ∈ K, u w = 0) ∨ (∀ w ∈ K, v w = 0) := by
  have h' := zero_or_zero_of_kernel_cover (u.comp K.subtype) (v.comp K.subtype)
    (fun w => h w w.property)
  rcases h' with hu | hv
  · left
    intro w hw
    exact congrArg (fun f : K →ₗ[F] A => f ⟨w, hw⟩) hu
  · right
    intro w hw
    exact congrArg (fun f : K →ₗ[F] B => f ⟨w, hw⟩) hv

variable [FiniteDimensional F V] [FiniteDimensional F A] [FiniteDimensional F B]

/-- Counting the parity equation and the two field-valued ratio equations. -/
theorem three_constraints_dimension (parity : V →ₗ[F] F)
    (outer : V →ₗ[F] A) (inner : V →ₗ[F] B) :
    finrank F V ≤ finrank F (LinearMap.ker (parity.prod (outer.prod inner))) +
      1 + finrank F A + finrank F B := by
  have hrank := (parity.prod (outer.prod inner)).finrank_range_add_finrank_ker
  have hle := (LinearMap.range (parity.prod (outer.prod inner))).finrank_le
  simp only [Module.finrank_prod, Module.finrank_self] at hle
  omega

theorem sixteen_le_constraint_kernel (parity : V →ₗ[F] F)
    (outer : V →ₗ[F] A) (inner : V →ₗ[F] B)
    (hdim : 1 + finrank F A + finrank F B + 16 ≤ finrank F V) :
    16 ≤ finrank F (LinearMap.ker (parity.prod (outer.prod inner))) := by
  have := three_constraints_dimension parity outer inner
  omega

omit [FiniteDimensional F V] [FiniteDimensional F A] in
theorem finrank_inf_ker (K : Submodule F V) (f : V →ₗ[F] A) :
    finrank F (K ⊓ LinearMap.ker f : Submodule F V) =
      finrank F (LinearMap.ker (f.comp K.subtype)) := by
  let L := LinearMap.ker (f.comp K.subtype)
  let g := K.subtype.comp L.subtype
  have hg : Function.Injective g := K.subtype_injective.comp L.subtype_injective
  have hrange : LinearMap.range g = K ⊓ LinearMap.ker f := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.val.property, w.property⟩
    · rintro ⟨hvK, hvf⟩
      exact ⟨⟨⟨v, hvK⟩, hvf⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hg]

/-- Imposing a linear equation costs at most the dimension of its target. -/
theorem finrank_le_inf_ker_add (K : Submodule F V) (f : V →ₗ[F] A) :
    finrank F K ≤ finrank F (K ⊓ LinearMap.ker f : Submodule F V) + finrank F A := by
  have hnull := (f.comp K.subtype).finrank_range_add_finrank_ker
  have hrange := (LinearMap.range (f.comp K.subtype)).finrank_le
  rw [finrank_inf_ker K f]
  omega

end Kernels

section Labels

variable {I W : Type*} [Fintype I] [AddCommGroup W] [Module (ZMod 2) W]

/-- Point labels extend uniquely to binary linear sums. -/
noncomputable def labelMap (labels : I → W) : (I → ZMod 2) →ₗ[ZMod 2] W :=
  Fintype.linearCombination (ZMod 2) labels

theorem labelMap_apply (labels : I → W) (w : I → ZMod 2) :
    labelMap labels w = ∑ i, w i • labels i :=
  Fintype.linearCombination_apply _ _ _

end Labels

end Erdos624.Disproof

/- Source module Erdos624.Counting. -/

namespace Erdos624.Disproof

open Finset

variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]

/-- A finite union bound, stated directly in cardinalities. -/
theorem exists_avoiding_events (bad : I → Finset Ω)
    (h : ∑ i, (bad i).card < Fintype.card Ω) :
    ∃ x : Ω, ∀ i, x ∉ bad i := by
  classical
  by_contra! hn
  have hcover : Finset.univ.biUnion bad = (Finset.univ : Finset Ω) := by
    apply Finset.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := hn x
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hcard := Finset.card_biUnion_le (s := (Finset.univ : Finset I)) (t := bad)
  rw [hcover, Finset.card_univ] at hcard
  exact (not_lt_of_ge hcard) h

/-- Independent coordinate constraints multiply their numbers of choices. -/
theorem card_coordinate_constraints [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)]
    (bad : ∀ i, Finset (A i)) :
    (Fintype.piFinset bad).card = ∏ i, (bad i).card :=
  Fintype.card_piFinset bad

/-- A small average cost on the whole space leaves a low-cost point outside a small bad set. -/
theorem exists_outside_with_small_value (bad : Finset Ω) (cost : Ω → ℕ) (a b : ℕ)
    (h : a * (∑ x, cost x) < b * (Fintype.card Ω - bad.card)) :
    ∃ x, x ∉ bad ∧ a * cost x < b := by
  classical
  by_contra! hn
  let good := (Finset.univ : Finset Ω) \ bad
  have hpoint : ∀ x ∈ good, b ≤ a * cost x := by
    intro x hx
    exact hn x (Finset.mem_sdiff.mp hx).2
  have hgood : good.card = Fintype.card Ω - bad.card := by
    simp [good, Finset.card_sdiff_of_subset (Finset.subset_univ bad)]
  have hle : b * (Fintype.card Ω - bad.card) ≤ a * (∑ x, cost x) := by
    calc
      b * (Fintype.card Ω - bad.card) = ∑ _x ∈ good, b := by simp [hgood, Nat.mul_comm]
      _ ≤ ∑ x ∈ good, a * cost x := Finset.sum_le_sum hpoint
      _ = a * (∑ x ∈ good, cost x) := (Finset.mul_sum _ _ _).symm
      _ ≤ a * (∑ x, cost x) := Nat.mul_le_mul_left a
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp))
  exact (not_lt_of_ge hle) h

end Erdos624.Disproof

/- Source module Erdos624.Support. -/

namespace Erdos624.Disproof

open Finset

theorem binary_ne_zero_iff_eq_one (z : ZMod 2) : z ≠ 0 ↔ z = 1 := by
  classical
  fin_cases z
  · change (0 : ZMod 2) ≠ 0 ↔ (0 : ZMod 2) = 1
    simp
  · change (1 : ZMod 2) ≠ 0 ↔ (1 : ZMod 2) = 1
    simp

theorem binary_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  by_cases hz : z = 0
  · exact Or.inl hz
  · exact Or.inr ((binary_ne_zero_iff_eq_one z).mp hz)

section CoordinateCount

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Each binary linear coordinate is active on at most half the vectors. -/
theorem binary_hom_nonzero_card_le (f : G →+ ZMod 2) (q : ℕ)
    (hcard : Fintype.card G ≤ 2 * q) :
    (Finset.univ.filter fun x : G => f x ≠ 0).card ≤ q := by
  classical
  by_cases hf : ∀ x, f x = 0
  · simp [hf]
  obtain ⟨x, hx⟩ := not_forall.mp hf
  have hx1 : f x = 1 := (binary_ne_zero_iff_eq_one _).mp hx
  have heq := AddMonoidHom.card_fiber_eq_of_mem_range f
    (show (0 : ZMod 2) ∈ Set.range f from ⟨0, map_zero f⟩)
    (show (1 : ZMod 2) ∈ Set.range f from ⟨x, hx1⟩)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G)) (p := fun x => f x = 0)
  have hfilter : (Finset.univ.filter fun x : G => f x ≠ 0) =
      (Finset.univ.filter fun x : G => f x = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact binary_ne_zero_iff_eq_one _
  rw [← hfilter] at heq
  simp only [Finset.card_univ] at hpartition
  change (Finset.univ.filter fun x : G => f x = 0).card +
    (Finset.univ.filter fun x : G => f x ≠ 0).card = Fintype.card G at hpartition
  omega

end CoordinateCount

section ShortVector

variable {I : Type*} [Fintype I]

def vectorSupport (v : I → ZMod 2) : Finset I :=
  Finset.univ.filter fun i => v i ≠ 0

theorem mem_vectorSupport {v : I → ZMod 2} {i : I} :
    i ∈ vectorSupport v ↔ v i ≠ 0 := by
  simp [vectorSupport]

theorem vectorSupport_nonempty_iff (v : I → ZMod 2) : (vectorSupport v).Nonempty ↔ v ≠ 0 := by
  classical
  constructor
  · rintro ⟨i, hi⟩ hv
    have hne := mem_vectorSupport.mp hi
    apply hne
    simp [hv]
  · intro hv
    have hex : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, mem_vectorSupport.mpr hi⟩

noncomputable def subspaceSupport (K : Submodule (ZMod 2) (I → ZMod 2)) : Finset I := by
  classical
  exact Finset.univ.filter fun i => ∃ v ∈ K, v i ≠ 0

theorem mem_subspaceSupport {K : Submodule (ZMod 2) (I → ZMod 2)} {i : I} :
    i ∈ subspaceSupport K ↔ ∃ v ∈ K, v i ≠ 0 := by
  classical
  simp [subspaceSupport]

theorem subspaceSupport_mono {K L : Submodule (ZMod 2) (I → ZMod 2)} (h : K ≤ L) :
    subspaceSupport K ⊆ subspaceSupport L := by
  classical
  intro i hi
  obtain ⟨_, v, hv, hvi⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, h hv, hvi⟩

/-- A five-dimensional binary subspace contains a short nonzero vector. -/
theorem short_vector_of_card_32 (K : Submodule (ZMod 2) (I → ZMod 2))
    [Fintype K] (hK : Fintype.card K = 32) :
    ∃ v : K, v ≠ 0 ∧ 31 * (vectorSupport v.val).card ≤ 16 * Fintype.card I := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  have hcoord (i : I) :
      (Finset.univ.filter fun v : K => v.val i ≠ 0).card ≤ 16 := by
    exact binary_hom_nonzero_card_le
      (((LinearMap.proj i).comp K.subtype).toAddMonoidHom) 16 (by omega)
  have hsum : ∑ v : K, (vectorSupport v.val).card ≤ 16 * Fintype.card I := by
    calc
      ∑ v : K, (vectorSupport v.val).card =
          ∑ i : I, (Finset.univ.filter fun v : K => v.val i ≠ 0).card := by
        simp only [vectorSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
        exact Finset.sum_comm
      _ ≤ ∑ _ : I, 16 := Finset.sum_le_sum fun i _ => hcoord i
      _ = 16 * Fintype.card I := by simp [Nat.mul_comm]
  let S : Finset K := Finset.univ.erase 0
  have hS : S.card = 31 := by simp [S, hK]
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsumS : ∑ v ∈ S, (vectorSupport v.val).card ≤ 16 * Fintype.card I := by
    apply le_trans _ hsum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by simp)
  obtain ⟨v, hv, hsmall⟩ := Finset.exists_le_of_sum_le hSne
    (show ∑ v ∈ S, 31 * (vectorSupport v.val).card ≤
      ∑ _v ∈ S, 16 * Fintype.card I by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_const, hS, smul_eq_mul]
        exact Nat.mul_le_mul_left 31 hsumS)
  exact ⟨v, (Finset.mem_erase.mp hv).1, hsmall⟩

/-- The short vector estimate only needs a lower bound on the dimension. -/
theorem short_vector_of_finrank_ge_five (K : Submodule (ZMod 2) (I → ZMod 2))
    (hK : 5 ≤ Module.finrank (ZMod 2) K) :
    ∃ v : K, v ≠ 0 ∧ 31 * (vectorSupport v.val).card ≤ 16 * Fintype.card I := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  have hdim : Module.finrank (ZMod 2) (Fin 5 → ZMod 2) ≤
      Module.finrank (ZMod 2) K := by simpa using hK
  obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hdim
  let f := K.subtype.comp e
  have hf : Function.Injective f := K.subtype_injective.comp he
  let L := LinearMap.range f
  let : Fintype L := Fintype.ofFinite L
  have hLdim : Module.finrank (ZMod 2) L = 5 := by
    simpa [L] using LinearMap.finrank_range_of_inj hf
  have hLcard : Fintype.card L = 32 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), hLdim]
    norm_num
  obtain ⟨v, hv, hsmall⟩ := short_vector_of_card_32 L hLcard
  have hvK : v.val ∈ K := by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw]
    exact (e w).property
  refine ⟨⟨v.val, hvK⟩, ?_, hsmall⟩
  intro hz
  apply hv
  apply Subtype.ext
  exact congrArg (fun z : K => z.val) hz

end ShortVector

end Erdos624.Disproof

/- Source module Erdos624.Probability. -/

namespace Erdos624.Disproof

open Finset

section UnionBound

variable {Ω R : Type*} [Fintype Ω] [Fintype R]

theorem weighted_union_bound (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (event : Finset Ω) (bad : R → Finset Ω)
    (hcover : ∀ x ∈ event, ∃ r, x ∈ bad r) :
    ∑ x ∈ event, w x ≤ ∑ r, ∑ x ∈ bad r, w x := by
  classical
  have hpoint (x : Ω) : (if x ∈ event then w x else 0) ≤
      ∑ r, if x ∈ bad r then w x else 0 := by
    by_cases hx : x ∈ event
    · obtain ⟨r, hr⟩ := hcover x hx
      rw [if_pos hx]
      calc
        w x = if x ∈ bad r then w x else 0 := by simp [hr]
        _ ≤ ∑ s, if x ∈ bad s then w x else 0 :=
          Finset.single_le_sum (f := fun s => if x ∈ bad s then w x else 0)
            (fun s _ => by split <;> simp_all) (Finset.mem_univ r)
    · rw [if_neg hx]
      exact Finset.sum_nonneg fun r _ => by split <;> simp_all
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at hsum
  simpa only [← Finset.sum_filter, Finset.filter_univ_mem] using hsum

/-- The union bound for nonnegative weights on a finite sample space. -/
theorem exists_avoiding_weighted_events (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (bad : R → Finset Ω)
    (h : ∑ r, ∑ x ∈ bad r, w x < ∑ x, w x) :
    ∃ x, ∀ r, x ∉ bad r := by
  classical
  by_contra! hn
  have hpoint (x : Ω) : w x ≤ ∑ r, if x ∈ bad r then w x else 0 := by
    obtain ⟨r, hr⟩ := hn x
    calc
      w x = if x ∈ bad r then w x else 0 := by simp [hr]
      _ ≤ ∑ s, if x ∈ bad s then w x else 0 :=
        Finset.single_le_sum (f := fun s => if x ∈ bad s then w x else 0)
          (fun s _ => by split <;> simp_all) (Finset.mem_univ r)
  have hle : ∑ x, w x ≤ ∑ r, ∑ x ∈ bad r, w x := by
    calc
      ∑ x, w x ≤ ∑ x, ∑ r, if x ∈ bad r then w x else 0 :=
        Finset.sum_le_sum fun x _ => hpoint x
      _ = ∑ r, ∑ x ∈ bad r, w x := by
        rw [Finset.sum_comm]
        congr 1 with r
        rw [← Finset.sum_filter]
        simp
  exact (not_lt_of_ge hle) h

end UnionBound

section IndependentChoices

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*}

/-- Summing product weights over coordinatewise constraints factors exactly. -/
theorem restricted_product_weight (w : ∀ i, A i → ℝ) (allowed : ∀ i, Finset (A i)) :
    ∑ x ∈ Fintype.piFinset allowed, ∏ i, w i (x i) =
      ∏ i, ∑ a ∈ allowed i, w i a := by
  classical
  exact (Finset.prod_univ_sum allowed w).symm

theorem total_product_weight [∀ i, Fintype (A i)] (w : ∀ i, A i → ℝ)
    (htotal : ∀ i, ∑ a, w i a = 1) :
    ∑ x : ∀ i, A i, ∏ i, w i (x i) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [htotal]

/-- Independent failures are exponentially unlikely when enough trials are available. -/
theorem independent_miss_weight_le [∀ i, Fintype (A i)]
    (w : ∀ i, A i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (htotal : ∀ i, ∑ a, w i a = 1) (bad : ∀ i, Finset (A i))
    (trials : Finset I) (p : ℝ) (hp : p ≤ 1)
    (htrial : ∀ i ∈ trials, ∑ a ∈ bad i, w i a ≤ 1 - p) :
    ∑ x ∈ Fintype.piFinset bad, ∏ i, w i (x i) ≤
      Real.exp (-p * trials.card) := by
  classical
  have hnonneg (i : I) : 0 ≤ ∑ a ∈ bad i, w i a :=
    Finset.sum_nonneg fun a _ => hw i a
  have hle (i : I) : ∑ a ∈ bad i, w i a ≤ 1 := by
    rw [← htotal i]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hw i a)
  calc
    ∑ x ∈ Fintype.piFinset bad, ∏ i, w i (x i) =
        ∏ i, ∑ a ∈ bad i, w i a := restricted_product_weight w bad
    _ ≤ ∏ _i ∈ trials, (1 - p) :=
      omaProdMonoSubset (Finset.subset_univ _)
        (fun i _ => hnonneg i) htrial (fun i _ _ => hle i)
    _ = (1 - p) ^ trials.card := by simp
    _ ≤ (Real.exp (-p)) ^ trials.card :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp) (Real.one_sub_le_exp_neg p) _
    _ = Real.exp (-p * trials.card) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A finite family of requests can all succeed under independent choices. -/
theorem exists_simultaneous_coordinate_success [∀ i, Fintype (A i)]
    {R : Type*} [Fintype R]
    (w : ∀ i, A i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (htotal : ∀ i, ∑ a, w i a = 1) (bad : R → ∀ i, Finset (A i))
    (h : ∑ r, ∏ i, ∑ a ∈ bad r i, w i a < 1) :
    ∃ x : ∀ i, A i, ∀ r, ∃ i, x i ∉ bad r i := by
  classical
  have hav := exists_avoiding_weighted_events (fun x : ∀ i, A i => ∏ i, w i (x i))
    (fun x => Finset.prod_nonneg fun i _ => hw i (x i))
    (fun r => Fintype.piFinset (bad r))
    (by simpa only [restricted_product_weight, total_product_weight w htotal] using h)
  obtain ⟨x, hx⟩ := hav
  refine ⟨x, fun r => ?_⟩
  have hr := hx r
  simpa only [Fintype.mem_piFinset, not_forall] using hr

end IndependentChoices

end Erdos624.Disproof

/- Source module Erdos624.ListSampling. -/

namespace Erdos624.Disproof

open Finset

variable {C : Type*} [DecidableEq C]

/-- Uniform sampling from a finite list, with a fixed value for an empty list. -/
noncomputable def uniformListWeight (fallback : C) (s : Finset C) (c : C) : ℝ :=
  if s.Nonempty then
    if c ∈ s then (s.card : ℝ)⁻¹ else 0
  else if c = fallback then 1 else 0

theorem uniformListWeight_nonneg (fallback : C) (s : Finset C) (c : C) :
    0 ≤ uniformListWeight fallback s c := by
  unfold uniformListWeight
  split <;> split <;> positivity

theorem uniformListWeight_total [Fintype C] (fallback : C) (s : Finset C) :
    ∑ c, uniformListWeight fallback s c = 1 := by
  classical
  by_cases hs : s.Nonempty
  · have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    simp [uniformListWeight, hs, hcard]
  · simp [uniformListWeight, hs]

/-- The repair chooses either list with equal probability. -/
noncomputable def twoListWeight (fallback : C) (s t : Finset C) (c : C) : ℝ :=
  (uniformListWeight fallback s c + uniformListWeight fallback t c) / 2

theorem twoListWeight_nonneg (fallback : C) (s t : Finset C) (c : C) :
    0 ≤ twoListWeight fallback s t c := by
  exact div_nonneg (add_nonneg (uniformListWeight_nonneg _ _ _)
    (uniformListWeight_nonneg _ _ _)) (by norm_num)

theorem twoListWeight_total [Fintype C] (fallback : C) (s t : Finset C) :
    ∑ c, twoListWeight fallback s t c = 1 := by
  simp only [twoListWeight, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    uniformListWeight_total]
  norm_num

theorem twoListWeight_ge_left (fallback : C) (s t : Finset C) (c : C)
    (hc : c ∈ s) (M : ℕ) (hM : s.card ≤ M) :
    (2 * (M : ℝ))⁻¹ ≤ twoListWeight fallback s t c := by
  have hs : s.Nonempty := ⟨c, hc⟩
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hMcast : (s.card : ℝ) ≤ M := by exact_mod_cast hM
  have hinv : (M : ℝ)⁻¹ ≤ (s.card : ℝ)⁻¹ := inv_anti₀ hspos hMcast
  have ht := uniformListWeight_nonneg fallback t c
  have hleft : uniformListWeight fallback s c = (s.card : ℝ)⁻¹ := by
    simp [uniformListWeight, hs, hc]
  rw [twoListWeight, hleft, mul_inv_rev]
  norm_num
  linarith

theorem twoListWeight_ge_right (fallback : C) (s t : Finset C) (c : C)
    (hc : c ∈ t) (M : ℕ) (hM : t.card ≤ M) :
    (2 * (M : ℝ))⁻¹ ≤ twoListWeight fallback s t c := by
  have h := twoListWeight_ge_left fallback t s c hc M hM
  simpa only [twoListWeight, add_comm] using h

end Erdos624.Disproof

/- Source module Erdos624.Extensions. -/

namespace Erdos624.Disproof

open Finset

variable {X : Type*} [DecidableEq X]

def smallSubsets (s : Finset X) (k : ℕ) : Finset (Finset X) :=
  s.powerset.filter fun A => A.card ≤ k

/-- Complementation shows that at least half of the subsets have size at most half. -/
theorem card_smallSubsets (s : Finset X) (k : ℕ) (hs : s.card = 2 * k) :
    2 ^ s.card ≤ 2 * (smallSubsets s k).card := by
  let large := s.powerset.filter fun A => ¬ A.card ≤ k
  have hle : large.card ≤ (smallSubsets s k).card := by
    apply Finset.card_le_card_of_injOn (fun A => s \ A)
    · intro A hA
      obtain ⟨hAs, hAk⟩ := Finset.mem_filter.mp hA
      have hsub : A ⊆ s := Finset.mem_powerset.mp hAs
      have hcard := Finset.card_mono hsub
      change (s \ A) ∈ smallSubsets s k
      simp only [smallSubsets, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset hsub, hs]; omega⟩
    · intro A hA B hB hAB
      have hAs := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
      have hBs := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
      have h := congrArg (fun T => s \ T) hAB
      simpa only [Finset.sdiff_sdiff_eq_self hAs, Finset.sdiff_sdiff_eq_self hBs] using h
  have hpart := Finset.card_filter_add_card_filter_not (s := s.powerset)
    (p := fun A => A.card ≤ k)
  rw [Finset.card_powerset] at hpart
  change (smallSubsets s k).card + large.card = 2 ^ s.card at hpart
  omega

def adjustParity (a : X) (p : ℕ) (A : Finset X) : Finset X :=
  if A.card % 2 = p then A else insert a A

theorem adjustParity_subset {s A : Finset X} {a : X} (hA : A ⊆ s) (p : ℕ) :
    adjustParity a p A ⊆ insert a s := by
  unfold adjustParity
  split
  · exact hA.trans (Finset.subset_insert _ _)
  · exact Finset.insert_subset_insert a hA

theorem adjustParity_card_le (A : Finset X) (a : X) (p : ℕ) :
    (adjustParity a p A).card ≤ A.card + 1 := by
  unfold adjustParity
  split
  · omega
  · exact Finset.card_insert_le _ _

theorem adjustParity_mod {s A : Finset X} {a : X} (hA : A ⊆ s)
    (ha : a ∉ s) (p : ℕ) (hp : p < 2) :
    (adjustParity a p A).card % 2 = p := by
  have haA : a ∉ A := fun h => ha (hA h)
  unfold adjustParity
  split
  · assumption
  · rw [Finset.card_insert_of_notMem haA]
    omega

theorem erase_adjustParity {s A : Finset X} {a : X} (hA : A ⊆ s)
    (ha : a ∉ s) (p : ℕ) : (adjustParity a p A).erase a = A := by
  have haA : a ∉ A := fun h => ha (hA h)
  unfold adjustParity
  split
  · exact Finset.erase_eq_of_notMem haA
  · simp [haA]

/-- Parity correction preserves distinct subsets and adds at most one point. -/
theorem exists_many_parity_subsets (s : Finset X) (a : X) (ha : a ∉ s)
    (k p : ℕ) (hs : s.card = 2 * k) (hp : p < 2) :
    ∃ F : Finset (Finset X),
      (∀ A ∈ F, A ⊆ insert a s ∧ A.card ≤ k + 1 ∧ A.card % 2 = p) ∧
      2 ^ s.card ≤ 2 * F.card := by
  let F := (smallSubsets s k).image (adjustParity a p)
  have hinj : Set.InjOn (adjustParity a p) (smallSubsets s k) := by
    intro A hA B hB hAB
    have hAs := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
    have hBs := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have h := congrArg (fun T => T.erase a) hAB
    simpa only [erase_adjustParity hAs ha, erase_adjustParity hBs ha] using h
  refine ⟨F, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hBs, hBk⟩ := Finset.mem_filter.mp hB
    have hsub := Finset.mem_powerset.mp hBs
    exact ⟨adjustParity_subset hsub p, (adjustParity_card_le B a p).trans (by omega),
      adjustParity_mod hsub ha p hp⟩
  · simpa only [F, Finset.card_image_of_injOn hinj] using card_smallSubsets s k hs

/-- A marker with enough unused points has exponentially many short odd extensions. -/
theorem exists_many_odd_extensions (C Y : Finset X) (hCY : C ⊆ Y) (k : ℕ)
    (hsize : C.card + 2 * k + 1 ≤ Y.card) :
    ∃ F : Finset (Finset X),
      (∀ B ∈ F, C ⊆ B ∧ B ⊆ Y ∧ B.card ≤ C.card + k + 1 ∧ B.card % 2 = 1) ∧
      2 ^ (2 * k) ≤ 2 * F.card := by
  have hrem : 2 * k + 1 ≤ (Y \ C).card := by
    rw [Finset.card_sdiff_of_subset hCY]
    omega
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hrem
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hTne
  let S := T.erase a
  have haS : a ∉ S := Finset.notMem_erase _ _
  have hSc : S.card = 2 * k := by
    dsimp [S]
    rw [Finset.card_erase_of_mem ha, hTc]
    omega
  have hinsert : insert a S = T := Finset.insert_erase ha
  obtain ⟨F₀, hF₀, hcount⟩ := exists_many_parity_subsets S a haS k
    ((C.card + 1) % 2) hSc (Nat.mod_lt _ (by decide))
  have hsub (A : Finset X) (hA : A ∈ F₀) : A ⊆ Y \ C := by
    have hAT := (hF₀ A hA).1
    rw [hinsert] at hAT
    exact hAT.trans hT
  have hdis (A : Finset X) (hA : A ∈ F₀) : Disjoint C A := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxA
    exact (Finset.mem_sdiff.mp (hsub A hA hxA)).2 hxC
  have hinj : Set.InjOn (fun A => C ∪ A) F₀ := by
    intro A hA B hB hAB
    change C ∪ A = C ∪ B at hAB
    apply Finset.ext
    intro x
    constructor
    · intro hxA
      have hx : x ∈ C ∪ B := by rw [← hAB]; exact Finset.mem_union_right _ hxA
      rcases Finset.mem_union.mp hx with hxC | hxB
      · exact False.elim ((Finset.mem_sdiff.mp (hsub A hA hxA)).2 hxC)
      · exact hxB
    · intro hxB
      have hx : x ∈ C ∪ A := by rw [hAB]; exact Finset.mem_union_right _ hxB
      rcases Finset.mem_union.mp hx with hxC | hxA
      · exact False.elim ((Finset.mem_sdiff.mp (hsub B hB hxB)).2 hxC)
      · exact hxA
  refine ⟨F₀.image (fun A => C ∪ A), ?_, ?_⟩
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨_, hAc, hAp⟩ := hF₀ A hA
    have hcard : (C ∪ A).card = C.card + A.card := Finset.card_union_of_disjoint (hdis A hA)
    refine ⟨Finset.subset_union_left, Finset.union_subset hCY ?_, ?_, ?_⟩
    · exact (hsub A hA).trans Finset.sdiff_subset
    · rw [hcard]
      omega
    · rw [hcard]
      omega
  · rw [Finset.card_image_of_injOn hinj]
    simpa only [hSc] using hcount

end Erdos624.Disproof

/- Source module Erdos624.Triple. -/

namespace Erdos624.Disproof

open Finset

section TripleCounts

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Three independent binary coordinates are active on at most seven eighths of triples. -/
theorem binary_three_active_card_le (f : G →+ ZMod 2) (q : ℕ)
    (hG : Fintype.card G = 2 * q) :
    (Finset.univ.filter fun t : G × G × G =>
      f t.1 ≠ 0 ∨ f t.2.1 ≠ 0 ∨ f t.2.2 ≠ 0).card ≤ 7 * q ^ 3 := by
  classical
  let Z := Finset.univ.filter fun x : G => f x = 0
  have hactive := binary_hom_nonzero_card_le f q hG.le
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G)) (p := fun x => f x = 0)
  simp only [Finset.card_univ] at hpartition
  have hZ : q ≤ Z.card := by
    change q ≤ (Finset.univ.filter fun x : G => f x = 0).card
    change (Finset.univ.filter fun x : G => f x = 0).card +
      (Finset.univ.filter fun x : G => f x ≠ 0).card = Fintype.card G at hpartition
    omega
  have hzero : (Finset.univ.filter fun t : G × G × G =>
      ¬(f t.1 ≠ 0 ∨ f t.2.1 ≠ 0 ∨ f t.2.2 ≠ 0)) = Z ×ˢ (Z ×ˢ Z) := by
    ext t
    simp [Z]
  have htpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (G × G × G)))
    (p := fun t => f t.1 ≠ 0 ∨ f t.2.1 ≠ 0 ∨ f t.2.2 ≠ 0)
  rw [hzero, Finset.card_product, Finset.card_product] at htpart
  simp only [Finset.card_univ, Fintype.card_prod, hG] at htpart
  have hcube : q ^ 3 ≤ Z.card ^ 3 := Nat.pow_le_pow_left hZ 3
  nlinarith [hcube]

end TripleCounts

section ForbiddenTriples

variable {G : Type*} [Fintype G]

theorem card_triple_first (P : G → Prop) [DecidablePred P] :
    (Finset.univ.filter fun t : G × G × G => P t.1).card =
      (Finset.univ.filter P).card * Fintype.card G ^ 2 := by
  have hset : (Finset.univ.filter fun t : G × G × G => P t.1) =
      (Finset.univ.filter P) ×ˢ (Finset.univ ×ˢ Finset.univ) := by
    ext t
    simp
  rw [hset, Finset.card_product, Finset.card_product]
  simp [pow_two]

theorem card_triple_middle [DecidableEq G] (g : G → G) :
    (Finset.univ.filter fun t : G × G × G => t.2.1 = g t.1).card =
      Fintype.card G ^ 2 := by
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  simp [pow_two, apply_ite]

theorem card_triple_last [DecidableEq G] (g : G → G → G) :
    (Finset.univ.filter fun t : G × G × G => t.2.2 = g t.1 t.2.1).card =
      Fintype.card G ^ 2 := by
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  simp [pow_two]

variable {W : Type*} [DecidableEq G] [Add G] [Zero G] [Zero W] [DecidableEq W]

/-- The first event excludes the inner kernel, and the other six ensure independence. -/
def forbiddenTripleEvents (f : G → W) : Fin 7 → Finset (G × G × G) :=
  ![Finset.univ.filter (fun t => f t.1 = 0),
    Finset.univ.filter (fun t => t.2.1 = 0),
    Finset.univ.filter (fun t => t.2.1 = t.1),
    Finset.univ.filter (fun t => t.2.2 = 0),
    Finset.univ.filter (fun t => t.2.2 = t.1),
    Finset.univ.filter (fun t => t.2.2 = t.2.1),
    Finset.univ.filter (fun t => t.2.2 = t.1 + t.2.1)]

theorem card_forbiddenTripleEvents (f : G → W) (b : ℕ)
    (hker : (Finset.univ.filter fun x => f x = 0).card ≤ b) :
    (Finset.univ.biUnion (forbiddenTripleEvents f)).card ≤
      (b + 6) * Fintype.card G ^ 2 := by
  have hcounts (i : Fin 7) : (forbiddenTripleEvents f i).card =
      ![(Finset.univ.filter fun x => f x = 0).card * Fintype.card G ^ 2,
        Fintype.card G ^ 2, Fintype.card G ^ 2, Fintype.card G ^ 2,
        Fintype.card G ^ 2, Fintype.card G ^ 2, Fintype.card G ^ 2] i := by
    fin_cases i
    · exact card_triple_first (fun x => f x = 0)
    · exact card_triple_middle (fun _ => 0)
    · exact card_triple_middle id
    · exact card_triple_last (fun _ _ => 0)
    · exact card_triple_last (fun x _ => x)
    · exact card_triple_last (fun _ y => y)
    · exact card_triple_last (fun x y => x + y)
  calc
    (Finset.univ.biUnion (forbiddenTripleEvents f)).card ≤
        ∑ i, (forbiddenTripleEvents f i).card := Finset.card_biUnion_le
    _ = (Finset.univ.filter fun x => f x = 0).card * Fintype.card G ^ 2 +
        6 * Fintype.card G ^ 2 := by
      simp_rw [hcounts]
      simp [Fin.sum_univ_succ]
      ring
    _ ≤ (b + 6) * Fintype.card G ^ 2 := by
      nlinarith [Nat.mul_le_mul_right (Fintype.card G ^ 2) hker]

end ForbiddenTriples

section SupportAverage

variable {I G : Type*} [Fintype I] [AddCommGroup G] [Fintype G]
  [Module (ZMod 2) G]

def tripleSupport (e : G →ₗ[ZMod 2] (I → ZMod 2)) (t : G × G × G) : Finset I :=
  Finset.univ.filter fun i => e t.1 i ≠ 0 ∨ e t.2.1 i ≠ 0 ∨ e t.2.2 i ≠ 0

theorem sum_tripleSupport_le (e : G →ₗ[ZMod 2] (I → ZMod 2)) (q : ℕ)
    (hG : Fintype.card G = 2 * q) :
    ∑ t : G × G × G, (tripleSupport e t).card ≤
      (7 * q ^ 3) * Fintype.card I := by
  classical
  have hcoord (i : I) :
      (Finset.univ.filter fun t : G × G × G =>
        e t.1 i ≠ 0 ∨ e t.2.1 i ≠ 0 ∨ e t.2.2 i ≠ 0).card ≤ 7 * q ^ 3 :=
    binary_three_active_card_le (((LinearMap.proj i).comp e).toAddMonoidHom) q hG
  calc
    ∑ t : G × G × G, (tripleSupport e t).card =
        ∑ i : I, (Finset.univ.filter fun t : G × G × G =>
          e t.1 i ≠ 0 ∨ e t.2.1 i ≠ 0 ∨ e t.2.2 i ≠ 0).card := by
      simp only [tripleSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ _i : I, 7 * q ^ 3 := Finset.sum_le_sum fun i _ => hcoord i
    _ = (7 * q ^ 3) * Fintype.card I := by simp [Nat.mul_comm]

/-- A sixteen-dimensional space supplies three independent vectors with small combined support. -/
theorem exists_short_admissible_triple [DecidableEq G]
    {W : Type*} [Zero W] [DecidableEq W]
    (e : G →ₗ[ZMod 2] (I → ZMod 2)) (f : G → W)
    (hG : Fintype.card G = 65536)
    (hker : (Finset.univ.filter fun x => f x = 0).card ≤ 16)
    (hI : 0 < Fintype.card I) :
    ∃ t : G × G × G, (∀ i, t ∉ forbiddenTripleEvents f i) ∧
      10 * (tripleSupport e t).card ≤ 9 * Fintype.card I := by
  classical
  let bad := Finset.univ.biUnion (forbiddenTripleEvents f)
  have hbad : bad.card ≤ 94489280512 := by
    simpa [bad, hG] using card_forbiddenTripleEvents f 16 hker
  have hcard : Fintype.card (G × G × G) = 281474976710656 := by
    simp [Fintype.card_prod, hG]
  have hgood : 281380487430144 ≤ Fintype.card (G × G × G) - bad.card := by omega
  have hsum : ∑ t : G × G × G, (tripleSupport e t).card ≤
      246290604621824 * Fintype.card I := by
    simpa using sum_tripleSupport_le e 32768 (by omega)
  have hbound : 10 * (∑ t : G × G × G, (tripleSupport e t).card) <
      (9 * Fintype.card I) * (Fintype.card (G × G × G) - bad.card) := by
    have := Nat.mul_le_mul_left (9 * Fintype.card I) hgood
    nlinarith
  obtain ⟨t, ht, hsmall⟩ := exists_outside_with_small_value bad
    (fun t => (tripleSupport e t).card) 10 (9 * Fintype.card I) hbound
  refine ⟨t, ?_, hsmall.le⟩
  intro i hi
  exact ht (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)

end SupportAverage

section Independence

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]

theorem binary_triple_independent (x y z : G)
    (hx : x ≠ 0) (hy : y ≠ 0) (hyx : y ≠ x)
    (hz : z ≠ 0) (hzx : z ≠ x) (hzy : z ≠ y) (hzxy : z ≠ x + y) :
    LinearIndependent (ZMod 2) ![x, y, z] := by
  have hpair : LinearIndependent (ZMod 2) ![x, y] := by
    apply (LinearIndependent.pair_iff' hx).mpr
    intro a
    rcases binary_eq_zero_or_one a with rfl | rfl
    · simpa using hy.symm
    · simpa using hyx.symm
  have hrange : Set.range (![x, y] : Fin 2 → G) = {x, y} := by
    ext v
    simp [or_comm]
  have hspan : z ∉ Submodule.span (ZMod 2) (Set.range (![x, y] : Fin 2 → G)) := by
    rw [hrange, Submodule.mem_span_pair]
    rintro ⟨a, b, hab⟩
    rcases binary_eq_zero_or_one a with rfl | rfl <;>
      rcases binary_eq_zero_or_one b with rfl | rfl
    · exact hz (by simpa using hab.symm)
    · exact hzy (by simpa using hab.symm)
    · exact hzx (by simpa using hab.symm)
    · exact hzxy (by simpa using hab.symm)
  have hsnoc := hpair.finSnoc hspan
  have heq : Fin.snoc (![x, y] : Fin 2 → G) z = ![x, y, z] := by
    ext i
    fin_cases i <;> rfl
  rw [heq] at hsnoc
  exact hsnoc

end Independence

section ThreeSubspace

variable {I G W : Type*} [Fintype I] [AddCommGroup G] [Module (ZMod 2) G]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem support_span_triple_subset (e : G →ₗ[ZMod 2] (I → ZMod 2)) (t : G × G × G) :
    subspaceSupport (Submodule.span (ZMod 2)
      (Set.range (fun j : Fin 3 => e (![t.1, t.2.1, t.2.2] j)))) ⊆ tripleSupport e t := by
  classical
  intro i hi
  obtain ⟨_, v, hv, hvi⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hn
  simp only [not_or, not_not] at hn
  have hcoords (j : Fin 3) : e (![t.1, t.2.1, t.2.2] j) i = 0 := by
    fin_cases j
    · exact hn.1
    · exact hn.2.1
    · exact hn.2.2
  have hspan : Submodule.span (ZMod 2)
      (Set.range (fun j : Fin 3 => e (![t.1, t.2.1, t.2.2] j))) ≤
      LinearMap.ker (LinearMap.proj i) := by
    apply Submodule.span_le.mpr
    rintro w ⟨j, rfl⟩
    exact hcoords j
  exact hvi (hspan hv)

/-- A small three-dimensional subspace on which the inner denominator is nonzero. -/
theorem exists_short_three_subspace_of_embedding [Fintype G] [DecidableEq W]
    (e : G →ₗ[ZMod 2] (I → ZMod 2)) (he : Function.Injective e)
    (f : (I → ZMod 2) →ₗ[ZMod 2] W)
    (hG : Fintype.card G = 65536)
    (hker : (Finset.univ.filter fun x : G => f (e x) = 0).card ≤ 16)
    (hI : 0 < Fintype.card I) :
    ∃ D : Submodule (ZMod 2) (I → ZMod 2),
      D ≤ LinearMap.range e ∧ Module.finrank (ZMod 2) D = 3 ∧
      10 * (subspaceSupport D).card ≤ 9 * Fintype.card I ∧
      ∃ v ∈ D, f v ≠ 0 := by
  classical
  obtain ⟨t, ht, hsmall⟩ := exists_short_admissible_triple e (fun x => f (e x)) hG hker hI
  have h0 : f (e t.1) ≠ 0 := by simpa [forbiddenTripleEvents] using ht 0
  have hy : t.2.1 ≠ 0 := by simpa [forbiddenTripleEvents] using ht 1
  have hyx : t.2.1 ≠ t.1 := by simpa [forbiddenTripleEvents] using ht 2
  have hz : t.2.2 ≠ 0 := by simpa [forbiddenTripleEvents] using ht 3
  have hzx : t.2.2 ≠ t.1 := by simpa [forbiddenTripleEvents] using ht 4
  have hzy : t.2.2 ≠ t.2.1 := by simpa [forbiddenTripleEvents] using ht 5
  have hzxy : t.2.2 ≠ t.1 + t.2.1 := by simpa [forbiddenTripleEvents] using ht 6
  have hx : t.1 ≠ 0 := by
    intro h
    apply h0
    simp [h]
  have hlin := binary_triple_independent t.1 t.2.1 t.2.2 hx hy hyx hz hzx hzy hzxy
  have himage : LinearIndependent (ZMod 2)
      (fun j : Fin 3 => e (![t.1, t.2.1, t.2.2] j)) :=
    (e.linearIndependent_iff_of_injOn he.injOn).mpr hlin
  let D := Submodule.span (ZMod 2)
    (Set.range (fun j : Fin 3 => e (![t.1, t.2.1, t.2.2] j)))
  refine ⟨D, ?_, ?_, ?_, e t.1, ?_, h0⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    exact ⟨![t.1, t.2.1, t.2.2] j, rfl⟩
  · exact (finrank_span_eq_card himage).trans (by decide)
  · exact (Nat.mul_le_mul_left 10 (Finset.card_le_card (support_span_triple_subset e t))).trans hsmall
  · exact Submodule.subset_span ⟨0, rfl⟩

end ThreeSubspace

end Erdos624.Disproof

/- Source module Erdos624.Markers. -/

namespace Erdos624.Disproof

open Module

variable {I W : Type*} [Fintype I] [AddCommGroup W] [Module (ZMod 2) W]

/-- A large subspace with a small inner kernel contains the required short three-space. -/
theorem exists_short_three_subspace (K : Submodule (ZMod 2) (I → ZMod 2))
    (f : (I → ZMod 2) →ₗ[ZMod 2] W)
    (hK : 16 ≤ finrank (ZMod 2) K)
    (hker : finrank (ZMod 2) (LinearMap.ker (f.comp K.subtype)) ≤ 4)
    (hI : 0 < Fintype.card I) :
    ∃ D : Submodule (ZMod 2) (I → ZMod 2),
      D ≤ K ∧ finrank (ZMod 2) D = 3 ∧
      10 * (subspaceSupport D).card ≤ 9 * Fintype.card I ∧
      ∃ v ∈ D, f v ≠ 0 := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  have hdim : finrank (ZMod 2) (Fin 16 → ZMod 2) ≤ finrank (ZMod 2) K := by
    simpa using hK
  obtain ⟨e₀, he₀⟩ := finrank_le_iff_exists_linearMap.mp hdim
  let e := K.subtype.comp e₀
  have he : Function.Injective e := K.subtype_injective.comp he₀
  let L := LinearMap.ker (f.comp K.subtype)
  let : Fintype L := Fintype.ofFinite L
  have hLcard : Fintype.card L ≤ 16 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]
    have hp : (2 : ℕ) ^ finrank (ZMod 2) L ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by decide) hker
    simpa using hp
  let j : {x : Fin 16 → ZMod 2 // f (e x) = 0} → L :=
    fun x => ⟨e₀ x.val, x.property⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply he₀
    exact congrArg Subtype.val hxy
  have heker : (Finset.univ.filter fun x : Fin 16 → ZMod 2 => f (e x) = 0).card ≤ 16 := by
    rw [← Fintype.card_subtype (fun x : Fin 16 → ZMod 2 => f (e x) = 0)]
    exact (Fintype.card_le_of_injective j hj).trans hLcard
  have hcard : Fintype.card (Fin 16 → ZMod 2) = 65536 := by norm_num
  obtain ⟨D, hDe, hDdim, hDsmall, hDnonzero⟩ :=
    exists_short_three_subspace_of_embedding e he f hcard heker hI
  refine ⟨D, hDe.trans ?_, hDdim, hDsmall, hDnonzero⟩
  rintro v ⟨x, rfl⟩
  exact (e₀ x).property

/-- A large kernel of the inner denominator supplies a short nonzero marker. -/
theorem exists_short_inner_marker (K : Submodule (ZMod 2) (I → ZMod 2))
    (f : (I → ZMod 2) →ₗ[ZMod 2] W)
    (hker : 5 ≤ finrank (ZMod 2) (LinearMap.ker (f.comp K.subtype))) :
    ∃ v : I → ZMod 2, v ∈ K ∧ v ≠ 0 ∧ f v = 0 ∧
      31 * (vectorSupport v).card ≤ 16 * Fintype.card I := by
  let L := LinearMap.ker (f.comp K.subtype)
  let g := K.subtype.comp L.subtype
  have hg : Function.Injective g := K.subtype_injective.comp L.subtype_injective
  have hdim : 5 ≤ finrank (ZMod 2) (LinearMap.range g) := by
    rw [LinearMap.finrank_range_of_inj hg]
    exact hker
  obtain ⟨v, hv, hsmall⟩ := short_vector_of_finrank_ge_five (LinearMap.range g) hdim
  obtain ⟨w, hw⟩ := v.property
  refine ⟨v.val, ?_, ?_, ?_, hsmall⟩
  · rw [← hw]
    exact w.val.property
  · intro hz
    exact hv (Subtype.ext hz)
  · rw [← hw]
    exact w.property

/-- Every sufficiently large constraint space gives an even witness or one of the two markers. -/
theorem marker_dichotomy {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (K : Submodule (ZMod 2) (I → ZMod 2))
    (outer : (I → ZMod 2) →ₗ[ZMod 2] A)
    (inner : (I → ZMod 2) →ₗ[ZMod 2] W)
    (hK : 16 ≤ finrank (ZMod 2) K) (hI : 0 < Fintype.card I) :
    (∃ v ∈ K, outer v ≠ 0 ∧ inner v ≠ 0) ∨
    (∃ v : I → ZMod 2, v ∈ K ∧ v ≠ 0 ∧ inner v = 0 ∧
      31 * (vectorSupport v).card ≤ 16 * Fintype.card I) ∨
    (∃ D : Submodule (ZMod 2) (I → ZMod 2),
      D ≤ K ∧ finrank (ZMod 2) D = 3 ∧
      10 * (subspaceSupport D).card ≤ 9 * Fintype.card I ∧
      (∀ v ∈ D, outer v = 0) ∧ ∃ v ∈ D, inner v ≠ 0) := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  by_cases heven : ∃ v ∈ K, outer v ≠ 0 ∧ inner v ≠ 0
  · exact Or.inl heven
  right
  by_cases hlarge : 5 ≤ finrank (ZMod 2) (LinearMap.ker (inner.comp K.subtype))
  · exact Or.inl (exists_short_inner_marker K inner hlarge)
  right
  have hcover (v : I → ZMod 2) (hv : v ∈ K) : outer v = 0 ∨ inner v = 0 := by
    by_cases ho : outer v = 0
    · exact Or.inl ho
    · right
      by_contra hi
      exact heven ⟨v, hv, ho, hi⟩
  have houter : ∀ v ∈ K, outer v = 0 := by
    rcases vanishes_on_subspace_or K outer inner hcover with ho | hi
    · exact ho
    · have hz : inner.comp K.subtype = 0 := by
        ext v
        exact hi v v.property
      have hdim : finrank (ZMod 2) (LinearMap.ker (inner.comp K.subtype)) =
          finrank (ZMod 2) K := by
        rw [hz, LinearMap.ker_zero]
        exact finrank_top (ZMod 2) K
      omega
  obtain ⟨D, hDK, hDdim, hDsmall, hDnonzero⟩ :=
    exists_short_three_subspace K inner hK (by omega) hI
  exact ⟨D, hDK, hDdim, hDsmall, (fun v hv => houter v (hDK hv)), hDnonzero⟩

end Erdos624.Disproof

/- Source module Erdos624.Uniform. -/

namespace Erdos624.Disproof

open Finset

noncomputable def uniformWeight (Ω : Type*) [Fintype Ω] (_ : Ω) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹

theorem uniformWeight_nonneg (Ω : Type*) [Fintype Ω] (x : Ω) :
    0 ≤ uniformWeight Ω x := by
  unfold uniformWeight
  positivity

theorem uniformWeight_total (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    ∑ x : Ω, uniformWeight Ω x = 1 := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [uniformWeight, hcard]

/-- Every fiber of a surjective homomorphism has the same cardinality. -/
theorem surjective_hom_fiber_card {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (Finset.univ.filter fun x => f x = y).card * Fintype.card H = Fintype.card G := by
  classical
  have heq (z : H) : (Finset.univ.filter fun x => f x = z).card =
      (Finset.univ.filter fun x => f x = y).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  have hpart : (Finset.univ : Finset G).card =
      ∑ z : H, (Finset.univ.filter fun x => f x = z).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.card_univ, heq, Finset.sum_const, smul_eq_mul, Nat.mul_comm] using hpart.symm

/-- Uniform input induces the uniform distribution on the target of a surjective homomorphism. -/
theorem surjective_hom_fiber_weight {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    ∑ x ∈ Finset.univ.filter (fun x => f x = y), uniformWeight G x =
      (Fintype.card H : ℝ)⁻¹ := by
  classical
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : ((Finset.univ.filter fun x => f x = y).card : ℝ) * Fintype.card H =
      Fintype.card G := by exact_mod_cast surjective_hom_fiber_card f hf y
  simp only [uniformWeight, Finset.sum_const, nsmul_eq_mul]
  field_simp
  exact hcard

theorem surjective_hom_preimage_weight {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (s : Finset H) :
    ∑ x ∈ Finset.univ.filter (fun x => f x ∈ s), uniformWeight G x =
      ∑ y ∈ s, uniformWeight H y := by
  calc
    ∑ x ∈ Finset.univ.filter (fun x => f x ∈ s), uniformWeight G x =
        ∑ y ∈ s, ∑ x ∈ Finset.univ.filter (fun x => f x = y), uniformWeight G x :=
      (Finset.sum_fiberwise_eq_sum_filter Finset.univ s f (uniformWeight G)).symm
    _ = ∑ y ∈ s, uniformWeight H y := by
      apply Finset.sum_congr rfl
      intro y _
      exact surjective_hom_fiber_weight f hf y

end Erdos624.Disproof

/- Source module Erdos624.RandomLinear. -/

namespace Erdos624.Disproof

open Module

section Restriction

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- Restriction of a linear map to a subspace is a surjective additive homomorphism. -/
def restrictLinearHom (K : Submodule F V) : (V →ₗ[F] W) →+ (K →ₗ[F] W) where
  toFun f := f.comp K.subtype
  map_zero' := by rfl
  map_add' f g := by rfl

theorem restrictLinearHom_surjective (K : Submodule F V) :
    Function.Surjective (restrictLinearHom (W := W) K) := by
  intro f
  exact f.exists_extend

theorem linear_restriction_fiber_card (K : Submodule F V)
    [Fintype (V →ₗ[F] W)] [Fintype (K →ₗ[F] W)] [DecidableEq (K →ₗ[F] W)]
    (g : K →ₗ[F] W) :
    (Finset.univ.filter fun f : V →ₗ[F] W => f.comp K.subtype = g).card *
      Fintype.card (K →ₗ[F] W) = Fintype.card (V →ₗ[F] W) := by
  classical
  exact surjective_hom_fiber_card (restrictLinearHom K) (restrictLinearHom_surjective K) g

theorem linear_restriction_fiber_weight (K : Submodule F V)
    [Fintype (V →ₗ[F] W)] [Fintype (K →ₗ[F] W)] [DecidableEq (K →ₗ[F] W)]
    (g : K →ₗ[F] W) :
    ∑ f ∈ Finset.univ.filter (fun f : V →ₗ[F] W => f.comp K.subtype = g),
      uniformWeight (V →ₗ[F] W) f = (Fintype.card (K →ₗ[F] W) : ℝ)⁻¹ := by
  classical
  exact surjective_hom_fiber_weight (restrictLinearHom K) (restrictLinearHom_surjective K) g

theorem linear_restriction_event_weight (K : Submodule F V)
    [Fintype (V →ₗ[F] W)] [Fintype (K →ₗ[F] W)] [DecidableEq (K →ₗ[F] W)]
    (s : Finset (K →ₗ[F] W)) :
    ∑ f ∈ Finset.univ.filter (fun f : V →ₗ[F] W => f.comp K.subtype ∈ s),
      uniformWeight (V →ₗ[F] W) f = ∑ g ∈ s, uniformWeight (K →ₗ[F] W) g := by
  exact surjective_hom_preimage_weight (restrictLinearHom K) (restrictLinearHom_surjective K) s

def evalLinearHom (v : V) : (V →ₗ[F] W) →+ W where
  toFun f := f v
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalLinearHom_surjective (v : V) (hv : v ≠ 0) :
    Function.Surjective (evalLinearHom (F := F) (W := W) v) := by
  intro w
  obtain ⟨f, _, hfv⟩ := (0 : (⊥ : Submodule F V) →ₗ[F] W).exists_extend_of_notMem
    (by simpa using hv) w
  exact ⟨f, hfv⟩

theorem linear_evaluation_fiber_weight [Fintype W] [DecidableEq W] [Fintype (V →ₗ[F] W)]
    (v : V) (hv : v ≠ 0) (w : W) :
    ∑ f ∈ Finset.univ.filter (fun f : V →ₗ[F] W => f v = w), uniformWeight (V →ₗ[F] W) f =
      (Fintype.card W : ℝ)⁻¹ :=
  surjective_hom_fiber_weight (evalLinearHom (F := F) v) (evalLinearHom_surjective (F := F) v hv) w

/-- A finite set of nonzero vectors gives a union bound for vanishing of a random linear map. -/
theorem linear_vanishing_union_bound [Fintype W] [Fintype (V →ₗ[F] W)]
    (vectors : Finset V) (hnonzero : ∀ v ∈ vectors, v ≠ 0)
    (event : Finset (V →ₗ[F] W))
    (hcover : ∀ f ∈ event, ∃ v ∈ vectors, f v = 0) :
    ∑ f ∈ event, uniformWeight (V →ₗ[F] W) f ≤
      (vectors.card : ℝ) * (Fintype.card W : ℝ)⁻¹ := by
  classical
  let bad (v : vectors) : Finset (V →ₗ[F] W) := Finset.univ.filter fun f => f v = 0
  have h := weighted_union_bound (uniformWeight (V →ₗ[F] W))
    (uniformWeight_nonneg _) event bad (by
      intro f hf
      obtain ⟨v, hv, hfv⟩ := hcover f hf
      exact ⟨⟨v, hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfv⟩⟩)
  have hsum : (∑ v : vectors, ∑ f ∈ bad v, uniformWeight (V →ₗ[F] W) f) =
      (vectors.card : ℝ) * (Fintype.card W : ℝ)⁻¹ := by
    have hfiber (v : vectors) := linear_evaluation_fiber_weight (F := F) v.val (hnonzero v.val v.property)
      (0 : W)
    simp_rw [bad, hfiber]
    simp
  exact h.trans_eq hsum

end Restriction

section BinaryCardinality

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [Fintype V] [Fintype (V →ₗ[ZMod 2] W)]

theorem binary_linear_map_card :
    Fintype.card (V →ₗ[ZMod 2] W) =
      2 ^ (finrank (ZMod 2) V * finrank (ZMod 2) W) := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap]
  norm_num

end BinaryCardinality

section Subspaces

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype V]

noncomputable def subspaceBasisCode (r : ℕ)
    (K : {K : Submodule F V // finrank F K = r}) : Fin r → V :=
  fun i => (Module.finBasisOfFinrankEq F K.val K.property i).val

theorem span_subspaceBasisCode (r : ℕ) (K : {K : Submodule F V // finrank F K = r}) :
    Submodule.span F (Set.range (subspaceBasisCode r K)) = K.val := by
  let b := Module.finBasisOfFinrankEq F K.val K.property
  have h := congrArg (Submodule.map K.val.subtype) b.span_eq
  change Submodule.span F (Set.range (fun i : Fin r => (b i).val)) = K.val
  simpa only [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp,
    Function.comp_def, Submodule.subtype_apply] using h

/-- Coding each subspace by one ordered basis bounds the number of subspaces. -/
theorem subspaceBasisCode_injective (r : ℕ) :
    Function.Injective (subspaceBasisCode (F := F) (V := V) r) := by
  intro K L hKL
  apply Subtype.ext
  rw [← span_subspaceBasisCode r K, ← span_subspaceBasisCode r L, hKL]

theorem card_subspaces_of_finrank (r : ℕ) :
    Nat.card {K : Submodule F V // finrank F K = r} ≤ (Fintype.card V) ^ r := by
  have h := Nat.card_le_card_of_injective (subspaceBasisCode (F := F) (V := V) r)
    (subspaceBasisCode_injective r)
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin] using h

noncomputable def containedSubspaceCode (K : Submodule F V) (r : ℕ)
    (D : {D : Submodule F V // D ≤ K ∧ finrank F D = r}) : Fin r → K :=
  fun i => ⟨(Module.finBasisOfFinrankEq F D.val D.property.2 i).val,
    D.property.1 (Module.finBasisOfFinrankEq F D.val D.property.2 i).property⟩

theorem containedSubspaceCode_injective (K : Submodule F V) (r : ℕ) :
    Function.Injective (containedSubspaceCode K r) := by
  intro D E hDE
  have hraw : subspaceBasisCode r ⟨D.val, D.property.2⟩ =
      subspaceBasisCode r ⟨E.val, E.property.2⟩ := by
    funext i
    exact congrArg (fun v : K => v.val) (congrFun hDE i)
  apply Subtype.ext
  rw [← span_subspaceBasisCode r ⟨D.val, D.property.2⟩,
    ← span_subspaceBasisCode r ⟨E.val, E.property.2⟩, hraw]

theorem card_contained_subspaces (K : Submodule F V) (r : ℕ) :
    Nat.card {D : Submodule F V // D ≤ K ∧ finrank F D = r} ≤ (Nat.card K) ^ r := by
  have h := Nat.card_le_card_of_injective (containedSubspaceCode K r)
    (containedSubspaceCode_injective K r)
  simpa only [Nat.card_fun, Nat.card_fin] using h

theorem kernel_contains_subspace_of_finrank_le {W : Type*}
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) (r : ℕ)
    (hr : r ≤ finrank F (LinearMap.ker f)) :
    ∃ K : Submodule F V, K ≤ LinearMap.ker f ∧ finrank F K = r := by
  have hdim : finrank F (Fin r → F) ≤ finrank F (LinearMap.ker f) := by simpa using hr
  obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hdim
  let g := (LinearMap.ker f).subtype.comp e
  have hg : Function.Injective g := (LinearMap.ker f).subtype_injective.comp he
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rintro v ⟨x, rfl⟩
    exact (e x).property
  · simpa using LinearMap.finrank_range_of_inj hg

end Subspaces

end Erdos624.Disproof

/- Source module Erdos624.KernelBounds. -/

namespace Erdos624.Disproof

open Module Finset

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [Fintype V] [Fintype W] [Fintype (V →ₗ[ZMod 2] W)]

noncomputable def mapsVanishingOn (K : Submodule (ZMod 2) V) :
    Finset (V →ₗ[ZMod 2] W) := by
  classical
  exact Finset.univ.filter fun f => f.comp K.subtype = 0

noncomputable def mapsWithLargeKernel (r : ℕ) : Finset (V →ₗ[ZMod 2] W) := by
  classical
  exact Finset.univ.filter fun f => r ≤ finrank (ZMod 2) (LinearMap.ker f)

noncomputable def mapsWithLargeRestrictedKernel (K : Submodule (ZMod 2) V) (r : ℕ) :
    Finset (V →ₗ[ZMod 2] W) := by
  classical
  exact Finset.univ.filter fun f => r ≤ finrank (ZMod 2) (LinearMap.ker (f.comp K.subtype))

/-- The counting union bound for a random binary linear map with a large kernel. -/
theorem large_kernel_card_bound (r : ℕ) :
    (mapsWithLargeKernel (V := V) (W := W) r).card *
      2 ^ (r * finrank (ZMod 2) W) ≤
      Fintype.card (V →ₗ[ZMod 2] W) * 2 ^ (r * finrank (ZMod 2) V) := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  let S := {K : Submodule (ZMod 2) V // finrank (ZMod 2) K = r}
  let : Fintype S := Fintype.ofInjective (subspaceBasisCode r) (subspaceBasisCode_injective r)
  have hcover : mapsWithLargeKernel (V := V) (W := W) r ⊆
      Finset.univ.biUnion (fun K : S => mapsVanishingOn (W := W) K.val) := by
    intro f hf
    have hdim := (Finset.mem_filter.mp hf).2
    obtain ⟨K, hKker, hKdim⟩ := kernel_contains_subspace_of_finrank_le f r hdim
    refine Finset.mem_biUnion.mpr ⟨⟨K, hKdim⟩, Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    ext v
    exact hKker v.property
  have hcard : (mapsWithLargeKernel (V := V) (W := W) r).card ≤
      ∑ K : S, (mapsVanishingOn (W := W) K.val).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hfiber (K : S) : (mapsVanishingOn (W := W) K.val).card *
      2 ^ (r * finrank (ZMod 2) W) = Fintype.card (V →ₗ[ZMod 2] W) := by
    letI : Module (ZMod 2) K.val := SMulMemClass.toModule K.val
    let : Fintype K.val := Fintype.ofFinite K.val
    let : Fintype (K.val →ₗ[ZMod 2] W) :=
      Fintype.ofInjective (fun f : K.val →ₗ[ZMod 2] W => (f : K.val → W)) DFunLike.coe_injective
    have h := linear_restriction_fiber_card K.val (0 : K.val →ₗ[ZMod 2] W)
    rw [binary_linear_map_card, K.property] at h
    simpa only [mapsVanishingOn, DFunLike.ext_iff, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.subtype_apply] using h
  have hS : Fintype.card S ≤ 2 ^ (r * finrank (ZMod 2) V) := by
    have h := card_subspaces_of_finrank (F := ZMod 2) (V := V) r
    rw [Nat.card_eq_fintype_card] at h
    have hV : Fintype.card V = 2 ^ finrank (ZMod 2) V := by
      simpa using Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV, ← pow_mul, Nat.mul_comm] at h
    exact h
  calc
    (mapsWithLargeKernel (V := V) (W := W) r).card * 2 ^ (r * finrank (ZMod 2) W) ≤
        (∑ K : S, (mapsVanishingOn (W := W) K.val).card) * 2 ^ (r * finrank (ZMod 2) W) :=
      Nat.mul_le_mul_right _ hcard
    _ = ∑ K : S, Fintype.card (V →ₗ[ZMod 2] W) := by rw [Finset.sum_mul]; simp_rw [hfiber]
    _ = Fintype.card (V →ₗ[ZMod 2] W) * Fintype.card S := by simp [Nat.mul_comm]
    _ ≤ Fintype.card (V →ₗ[ZMod 2] W) * 2 ^ (r * finrank (ZMod 2) V) :=
      Nat.mul_le_mul_left _ hS

theorem large_kernel_weight_bound (r : ℕ) :
    ∑ f ∈ mapsWithLargeKernel (V := V) (W := W) r, uniformWeight (V →ₗ[ZMod 2] W) f ≤
      (2 : ℝ) ^ (r * finrank (ZMod 2) V) / (2 : ℝ) ^ (r * finrank (ZMod 2) W) := by
  have hcard : ((mapsWithLargeKernel (V := V) (W := W) r).card : ℝ) *
      (2 : ℝ) ^ (r * finrank (ZMod 2) W) ≤
      (Fintype.card (V →ₗ[ZMod 2] W) : ℝ) * (2 : ℝ) ^ (r * finrank (ZMod 2) V) := by
    exact_mod_cast large_kernel_card_bound (V := V) (W := W) r
  have hpos : (0 : ℝ) < Fintype.card (V →ₗ[ZMod 2] W) := by
    exact_mod_cast Fintype.card_pos
  simp only [uniformWeight, Finset.sum_const, nsmul_eq_mul]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ hpos (by positivity)).mpr
  simpa only [mul_comm] using hcard

/-- The same kernel bound holds after restricting global labels to any coordinate subspace. -/
theorem large_restricted_kernel_weight_bound (K : Submodule (ZMod 2) V) (r : ℕ) :
    ∑ f ∈ mapsWithLargeRestrictedKernel (W := W) K r, uniformWeight (V →ₗ[ZMod 2] W) f ≤
      (2 : ℝ) ^ (r * finrank (ZMod 2) K) / (2 : ℝ) ^ (r * finrank (ZMod 2) W) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (K →ₗ[ZMod 2] W) :=
    Fintype.ofInjective (fun f : K →ₗ[ZMod 2] W => (f : K → W)) DFunLike.coe_injective
  have hset : mapsWithLargeRestrictedKernel (W := W) K r =
      Finset.univ.filter (fun f : V →ₗ[ZMod 2] W =>
        f.comp K.subtype ∈ mapsWithLargeKernel (V := K) (W := W) r) := by
    ext f
    simp [mapsWithLargeRestrictedKernel, mapsWithLargeKernel]
  rw [hset, linear_restriction_event_weight]
  exact large_kernel_weight_bound r

end Erdos624.Disproof

/- Source module Erdos624.Coordinates. -/

namespace Erdos624.Disproof

open Finset Module

variable {I : Type*} [Fintype I] [DecidableEq I]

def indicatorVector (B : Finset I) : I → ZMod 2 :=
  fun i => if i ∈ B then 1 else 0

omit [Fintype I] in
theorem indicatorVector_ne_zero {B : Finset I} (hB : B.Nonempty) : indicatorVector B ≠ 0 := by
  obtain ⟨i, hi⟩ := hB
  intro h
  have heq := congrFun h i
  simp [indicatorVector, hi] at heq

theorem vectorSupport_indicatorVector (B : Finset I) :
    vectorSupport (indicatorVector B) = B := by
  ext i
  simp [vectorSupport, indicatorVector]

theorem indicatorVector_vectorSupport (v : I → ZMod 2) :
    indicatorVector (vectorSupport v) = v := by
  ext i
  rcases binary_eq_zero_or_one (v i) with h | h <;> simp [indicatorVector, vectorSupport, h]

def subsetVectorEquiv : Finset I ≃ (I → ZMod 2) where
  toFun := indicatorVector
  invFun := vectorSupport
  left_inv := vectorSupport_indicatorVector
  right_inv := indicatorVector_vectorSupport

/-- Coordinates on a subset extend by zero to the common ambient space. -/
def extendByZero (B : Finset I) : (B → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) where
  toFun v i := if h : i ∈ B then v ⟨i, h⟩ else 0
  map_add' v w := by
    ext i
    by_cases hi : i ∈ B <;> simp [hi]
  map_smul' a v := by
    ext i
    by_cases hi : i ∈ B <;> simp [hi]

omit [Fintype I] in
theorem extendByZero_injective (B : Finset I) : Function.Injective (extendByZero B) := by
  intro v w hvw
  ext i
  have h := congrFun hvw i.val
  simpa [extendByZero, i.property] using h

theorem support_extendByZero (B : Finset I) (v : B → ZMod 2) :
    vectorSupport (extendByZero B v) =
      (vectorSupport v).map ⟨Subtype.val, Subtype.val_injective⟩ := by
  ext i
  simp only [mem_vectorSupport, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hi
    by_cases hB : i ∈ B
    · exact ⟨⟨i, hB⟩, by simpa [extendByZero, hB] using hi, rfl⟩
    · exact False.elim (hi (by simp [extendByZero, hB]))
  · rintro ⟨j, hj, rfl⟩
    simpa [extendByZero, j.property] using hj

theorem card_support_extendByZero (B : Finset I) (v : B → ZMod 2) :
    (vectorSupport (extendByZero B v)).card = (vectorSupport v).card := by
  rw [support_extendByZero, Finset.card_map]

theorem subspaceSupport_map_extendByZero (B : Finset I)
    (D : Submodule (ZMod 2) (B → ZMod 2)) :
    subspaceSupport (D.map (extendByZero B)) =
      (subspaceSupport D).map ⟨Subtype.val, Subtype.val_injective⟩ := by
  ext i
  simp only [mem_subspaceSupport, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨v, hv, hvi⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have hs : i ∈ vectorSupport (extendByZero B w) := mem_vectorSupport.mpr hvi
    rw [support_extendByZero] at hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hs
    exact ⟨j, ⟨w, hw, mem_vectorSupport.mp hj⟩, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨w, hw, hwi⟩ := hj
    exact ⟨extendByZero B w, Submodule.mem_map.mpr ⟨w, hw, rfl⟩,
      by simpa [extendByZero, j.property] using hwi⟩

theorem card_subspaceSupport_map_extendByZero (B : Finset I)
    (D : Submodule (ZMod 2) (B → ZMod 2)) :
    (subspaceSupport (D.map (extendByZero B))).card = (subspaceSupport D).card := by
  rw [subspaceSupport_map_extendByZero, Finset.card_map]

omit [Fintype I] in
theorem finrank_map_extendByZero (B : Finset I) (D : Submodule (ZMod 2) (B → ZMod 2)) :
    finrank (ZMod 2) (D.map (extendByZero B)) = finrank (ZMod 2) D :=
  (Submodule.equivMapOfInjective (extendByZero B) (extendByZero_injective B) D).finrank_eq.symm

def coordinateSpace (B : Finset I) : Submodule (ZMod 2) (I → ZMod 2) :=
  LinearMap.range (extendByZero B)

omit [Fintype I] in
theorem coordinateSpace_finrank (B : Finset I) :
    finrank (ZMod 2) (coordinateSpace B) = B.card := by
  rw [coordinateSpace, LinearMap.finrank_range_of_inj (extendByZero_injective B)]
  simp

theorem mem_coordinateSpace_iff {B : Finset I} {v : I → ZMod 2} :
    v ∈ coordinateSpace B ↔ vectorSupport v ⊆ B := by
  constructor
  · rintro ⟨w, rfl⟩ i hi
    have hne : extendByZero B w i ≠ 0 := (Finset.mem_filter.mp hi).2
    by_contra hnot
    apply hne
    simp [extendByZero, hnot]
  · intro hv
    refine ⟨(fun i : B => v i.val), ?_⟩
    ext i
    by_cases hi : i ∈ B
    · simp [extendByZero, hi]
    · have hzero : v i = 0 := by
        by_contra hne
        exact hi (hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩))
      simp [extendByZero, hi, hzero]

theorem coordinateSpace_mono {B C : Finset I} (hBC : B ⊆ C) :
    coordinateSpace B ≤ coordinateSpace C := by
  intro v hv
  exact mem_coordinateSpace_iff.mpr ((mem_coordinateSpace_iff.mp hv).trans hBC)

theorem subspaceSupport_subset_of_le_coordinateSpace {K : Submodule (ZMod 2) (I → ZMod 2)}
    {B : Finset I} (hKB : K ≤ coordinateSpace B) : subspaceSupport K ⊆ B := by
  classical
  intro i hi
  obtain ⟨v, hv, hvi⟩ := mem_subspaceSupport.mp hi
  exact mem_coordinateSpace_iff.mp (hKB hv) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩)

theorem le_coordinateSpace_iff {K : Submodule (ZMod 2) (I → ZMod 2)} {B : Finset I} :
    K ≤ coordinateSpace B ↔ subspaceSupport K ⊆ B := by
  constructor
  · exact subspaceSupport_subset_of_le_coordinateSpace
  · intro h v hv
    apply mem_coordinateSpace_iff.mpr
    intro i hi
    exact h (mem_subspaceSupport.mpr ⟨v, hv, mem_vectorSupport.mp hi⟩)

noncomputable def parityMap : (I → ZMod 2) →ₗ[ZMod 2] ZMod 2 := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  exact labelMap (fun _ : I => 1)

omit [DecidableEq I] in
theorem parityMap_apply (v : I → ZMod 2) : parityMap v = ∑ i, v i := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  simp [parityMap, labelMap_apply, smul_eq_mul]

theorem parityMap_indicatorVector (B : Finset I) :
    parityMap (indicatorVector B) = (B.card : ZMod 2) := by
  simp [parityMap_apply, indicatorVector]

theorem parityMap_eq_card_support (v : I → ZMod 2) :
    parityMap v = ((vectorSupport v).card : ZMod 2) := by
  rw [← indicatorVector_vectorSupport v, parityMap_indicatorVector]
  rw [vectorSupport_indicatorVector]

theorem parityMap_eq_zero_iff (v : I → ZMod 2) :
    parityMap v = 0 ↔ (vectorSupport v).card % 2 = 0 := by
  rw [parityMap_eq_card_support, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

theorem supported_three_constraints_dimension
    {A C : Type*} [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    [AddCommGroup C] [Module (ZMod 2) C] [FiniteDimensional (ZMod 2) C]
    (B : Finset I) (outer : (I → ZMod 2) →ₗ[ZMod 2] A)
    (inner : (I → ZMod 2) →ₗ[ZMod 2] C) :
    B.card ≤ finrank (ZMod 2)
      (coordinateSpace B ⊓ LinearMap.ker (parityMap.prod (outer.prod inner)) :
        Submodule (ZMod 2) (I → ZMod 2)) +
      1 + finrank (ZMod 2) A + finrank (ZMod 2) C := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  have h := finrank_le_inf_ker_add (coordinateSpace B) (parityMap.prod (outer.prod inner))
  simpa only [coordinateSpace_finrank, Module.finrank_prod, Module.finrank_self, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

end Erdos624.Disproof

/- Source module Erdos624.Assembly. -/

namespace Erdos624.Disproof

open Finset

variable {I C : Type*} [LinearOrder I]

/-- The minimum of a nonempty mask selects its unique branch. -/
def assembleColour (fallback : C) (branch : I → Finset I → C) (A : Finset I) : C :=
  if h : A.Nonempty then branch (A.min' h) (A.erase (A.min' h)) else fallback

theorem assembleColour_insert (fallback : C) (branch : I → Finset I → C)
    (x : I) (B : Finset I) (hB : ∀ z ∈ B, x < z) :
    assembleColour fallback branch (insert x B) = branch x B := by
  have hx : x ∉ B := by
    intro h
    exact (lt_irrefl x) (hB x h)
  have hmin : (insert x B).min' (Finset.insert_nonempty x B) = x := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_insert_self x B)
    · have hmem := Finset.min'_mem (insert x B) (Finset.insert_nonempty x B)
      rcases Finset.mem_insert.mp hmem with heq | hmem
      · exact heq.ge
      · exact (hB _ hmem).le
  simp [assembleColour, hmin, hx]

/-- Branch coverage on every source assembles into one coloring of all masks. -/
theorem assembleColour_covers (fallback : C) (branch : I → Finset I → C) (h : ℕ)
    (hbranch : ∀ Y : Finset I, Y.card = h → ∃ x ∈ Y, ∀ c : C,
      ∃ B : Finset I, B ⊆ Y ∧ (∀ z ∈ B, x < z) ∧ branch x B = c) :
    Covers (assembleColour fallback branch) h := by
  apply covers_of_exact_size
  intro Y hY c
  obtain ⟨x, hx, hxc⟩ := hbranch Y hY
  obtain ⟨B, hBY, hB, hBc⟩ := hxc c
  refine ⟨insert x B, Finset.insert_subset hx hBY, ?_⟩
  rw [assembleColour_insert fallback branch x B hB, hBc]

end Erdos624.Disproof

/- Source module Erdos624.Labels. -/

namespace Erdos624.Disproof

open Module

variable (I F G : Type*) [Field F] [Field G]
  [Algebra (ZMod 2) F] [Algebra (ZMod 2) G]

structure BranchLabels where
  outerU : (I → ZMod 2) →ₗ[ZMod 2] F
  outerV : (I → ZMod 2) →ₗ[ZMod 2] F
  innerU : F → (I → ZMod 2) →ₗ[ZMod 2] G
  innerV : F → (I → ZMod 2) →ₗ[ZMod 2] G

namespace BranchLabels

variable {I F G} [Fintype I] [DecidableEq I]

def restrict (L : BranchLabels I F G) (B : Finset I) : BranchLabels B F G where
  outerU := L.outerU.comp (extendByZero B)
  outerV := L.outerV.comp (extendByZero B)
  innerU a := (L.innerU a).comp (extendByZero B)
  innerV a := (L.innerV a).comp (extendByZero B)

noncomputable def ratioColour (L : BranchLabels I F G) (v : I → ZMod 2) : F × G := by
  classical
  exact if L.outerV v = 0 then (0, 0) else
    let a := L.outerU v / L.outerV v
    if L.innerV a v = 0 then (0, 0) else (a, L.innerU a v / L.innerV a v)

omit [Fintype I] in
theorem ratioColour_restrict (L : BranchLabels I F G) (B : Finset I) (v : B → ZMod 2) :
    (L.restrict B).ratioColour v = L.ratioColour (extendByZero B v) := rfl

omit [Fintype I] [DecidableEq I] in
theorem ratioColour_eq (L : BranchLabels I F G) (v : I → ZMod 2) (a : F) (b : G)
    (hV : L.outerV v ≠ 0) (hiV : L.innerV a v ≠ 0)
    (hU : L.outerU v = a * L.outerV v) (hiU : L.innerU a v = b * L.innerV a v) :
    L.ratioColour v = (a, b) := by
  have ha : L.outerU v / L.outerV v = a := (div_eq_iff hV).mpr hU
  have hb : L.innerU a v / L.innerV a v = b := (div_eq_iff hiV).mpr hiU
  simp [ratioColour, hV, ha, hiV, hb]

noncomputable def constraintKernel (L : BranchLabels I F G) (a : F) (b : G) :
    Submodule (ZMod 2) (I → ZMod 2) :=
  LinearMap.ker (parityMap.prod ((L.outerU - a • L.outerV).prod (L.innerU a - b • L.innerV a)))

omit [DecidableEq I] in
theorem mem_constraintKernel (L : BranchLabels I F G) (a : F) (b : G) (v : I → ZMod 2) :
    v ∈ L.constraintKernel a b ↔
      parityMap v = 0 ∧ L.outerU v = a * L.outerV v ∧ L.innerU a v = b * L.innerV a v := by
  simp [constraintKernel, LinearMap.mem_ker, sub_eq_zero, smul_eq_mul]

omit [DecidableEq I] in
theorem constraintKernel_finrank [FiniteDimensional (ZMod 2) F] [FiniteDimensional (ZMod 2) G]
    (L : BranchLabels I F G) (a : F) (b : G)
    (hdim : 1 + finrank (ZMod 2) F + finrank (ZMod 2) G + 16 ≤ Fintype.card I) :
    16 ≤ finrank (ZMod 2) (L.constraintKernel a b) := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  apply sixteen_le_constraint_kernel
  simpa using hdim

omit [DecidableEq I] in
/-- On a source domain, every color has a ratio witness or one of the two repair markers. -/
theorem classification [FiniteDimensional (ZMod 2) F] [FiniteDimensional (ZMod 2) G]
    (L : BranchLabels I F G) (a : F) (b : G)
    (hdim : 1 + finrank (ZMod 2) F + finrank (ZMod 2) G + 16 ≤ Fintype.card I) :
    (∃ v ∈ L.constraintKernel a b, L.ratioColour v = (a, b)) ∨
    (∃ v : I → ZMod 2, v ∈ L.constraintKernel a b ∧ v ≠ 0 ∧ L.innerV a v = 0 ∧
      31 * (vectorSupport v).card ≤ 16 * Fintype.card I) ∨
    (∃ D : Submodule (ZMod 2) (I → ZMod 2),
      D ≤ L.constraintKernel a b ∧ finrank (ZMod 2) D = 3 ∧
      10 * (subspaceSupport D).card ≤ 9 * Fintype.card I ∧
      (∀ v ∈ D, L.outerU v = 0 ∧ L.outerV v = 0) ∧
      ∃ v ∈ D, L.innerV a v ≠ 0) := by
  have hI : 0 < Fintype.card I := by omega
  rcases marker_dichotomy (L.constraintKernel a b) L.outerV (L.innerV a)
    (L.constraintKernel_finrank a b hdim) hI with he | hi | ho
  · obtain ⟨v, hv, hV, hiV⟩ := he
    have hconstraints := (L.mem_constraintKernel a b v).mp hv
    exact Or.inl ⟨v, hv, L.ratioColour_eq v a b hV hiV hconstraints.2.1 hconstraints.2.2⟩
  · exact Or.inr (Or.inl hi)
  · obtain ⟨D, hDK, hDdim, hDsmall, hzero, hnonzero⟩ := ho
    refine Or.inr (Or.inr ⟨D, hDK, hDdim, hDsmall, ?_, hnonzero⟩)
    intro v hv
    have hconstraints := (L.mem_constraintKernel a b v).mp (hDK hv)
    refine ⟨?_, hzero v hv⟩
    rw [hconstraints.2.1, hzero v hv, mul_zero]

end BranchLabels

end Erdos624.Disproof

/- Source module Erdos624.RareEvents. -/

namespace Erdos624.Disproof

open Finset

theorem weighted_markov {Ω : Type*} [Fintype Ω]
    (w value : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hvalue : ∀ x, 0 ≤ value x)
    (event : Finset Ω) (t : ℝ) (ht : 0 < t) (hevent : ∀ x ∈ event, t ≤ value x) :
    ∑ x ∈ event, w x ≤ (∑ x, w x * value x) / t := by
  apply (le_div_iff₀ ht).mpr
  calc
    (∑ x ∈ event, w x) * t = ∑ x ∈ event, w x * t := Finset.sum_mul _ _ _
    _ ≤ ∑ x ∈ event, w x * value x :=
      Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hevent x hx) (hw x)
    _ ≤ ∑ x, w x * value x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => mul_nonneg (hw x) (hvalue x))

theorem event_exponential_moment {A : Type*} [Fintype A] [DecidableEq A]
    (w : A → ℝ) (htotal : ∑ a, w a = 1) (event : Finset A) (t : ℝ) :
    ∑ a, w a * (if a ∈ event then t else 1) =
      1 + (t - 1) * ∑ a ∈ event, w a := by
  have hpoint (a : A) : w a * (if a ∈ event then t else 1) =
      w a + (t - 1) * (if a ∈ event then w a else 0) := by
    split <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, ← Finset.sum_filter]
  simp

section IndependentEvents

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
  [∀ i, DecidableEq (A i)]

def appearanceCount (event : ∀ i, Finset (A i)) (x : ∀ i, A i) : ℕ :=
  (Finset.univ.filter fun i => x i ∈ event i).card

omit [DecidableEq I] in
theorem appearanceCount_power (event : ∀ i, Finset (A i)) (x : ∀ i, A i) (t : ℝ) :
    t ^ appearanceCount event x = ∏ i, if x i ∈ event i then t else 1 := by
  simp [appearanceCount, Finset.prod_ite]

theorem independent_exponential_moment [∀ i, Fintype (A i)]
    (w : ∀ i, A i → ℝ) (htotal : ∀ i, ∑ a, w i a = 1)
    (event : ∀ i, Finset (A i)) (t : ℝ) :
    ∑ x : ∀ i, A i, (∏ i, w i (x i)) * t ^ appearanceCount event x =
      ∏ i, (1 + (t - 1) * ∑ a ∈ event i, w i a) := by
  simp_rw [appearanceCount_power, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => w i a * if a ∈ event i then t else 1)]
  apply Finset.prod_congr rfl
  intro i _
  exact event_exponential_moment (w i) (htotal i) (event i) t

/-- Exponential Markov bounds the chance that many independent rare events occur. -/
theorem independent_many_events_bound [∀ i, Fintype (A i)]
    (w : ∀ i, A i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (htotal : ∀ i, ∑ a, w i a = 1) (event : ∀ i, Finset (A i))
    (r : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    ∑ x ∈ Finset.univ.filter (fun x : ∀ i, A i => r ≤ appearanceCount event x),
      (∏ i, w i (x i)) ≤
      Real.exp ((t - 1) * ∑ i, ∑ a ∈ event i, w i a) / t ^ r := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hmarkov := weighted_markov (fun x : ∀ i, A i => ∏ i, w i (x i))
    (fun x => t ^ appearanceCount event x)
    (fun x => Finset.prod_nonneg fun i _ => hw i (x i))
    (fun _ => pow_nonneg htpos.le _)
    (Finset.univ.filter fun x : ∀ i, A i => r ≤ appearanceCount event x) (t ^ r)
    (pow_pos htpos _) (fun x hx => pow_le_pow_right₀ ht (Finset.mem_filter.mp hx).2)
  apply hmarkov.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg htpos.le _)
  rw [independent_exponential_moment w htotal event t]
  calc
    ∏ i, (1 + (t - 1) * ∑ a ∈ event i, w i a) ≤
        Real.exp (∑ i, (t - 1) * ∑ a ∈ event i, w i a) :=
      Real.prod_one_add_le_exp_sum Finset.univ
        (fun i => mul_nonneg (sub_nonneg.mpr ht) (Finset.sum_nonneg fun a _ => hw i a))
    _ = Real.exp ((t - 1) * ∑ i, ∑ a ∈ event i, w i a) := by rw [Finset.mul_sum]

theorem independent_many_events_small_sum [∀ i, Fintype (A i)]
    (w : ∀ i, A i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (htotal : ∀ i, ∑ a, w i a = 1) (event : ∀ i, Finset (A i))
    (r : ℕ) (t : ℝ) (ht : 1 ≤ t)
    (hsum : (∑ i, ∑ a ∈ event i, w i a) ≤ t⁻¹) :
    ∑ x ∈ Finset.univ.filter (fun x : ∀ i, A i => r ≤ appearanceCount event x),
      (∏ i, w i (x i)) ≤ Real.exp 1 / t ^ r := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hnonneg : 0 ≤ ∑ i, ∑ a ∈ event i, w i a :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => hw i a
  have hmul : t * (∑ i, ∑ a ∈ event i, w i a) ≤ 1 := by
    calc
      t * (∑ i, ∑ a ∈ event i, w i a) ≤ t * t⁻¹ :=
        mul_le_mul_of_nonneg_left hsum htpos.le
      _ = 1 := mul_inv_cancel₀ htpos.ne'
  have hexp : (t - 1) * (∑ i, ∑ a ∈ event i, w i a) ≤ 1 := by nlinarith
  apply (independent_many_events_bound w hw htotal event r t ht).trans
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (pow_nonneg htpos.le _)

/-- One product-space choice simultaneously keeps every requested event count small. -/
theorem exists_uniformly_few_events [∀ i, Fintype (A i)]
    {R : Type*} [Fintype R]
    (w : ∀ i, A i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (htotal : ∀ i, ∑ a, w i a = 1) (events : R → ∀ i, Finset (A i))
    (m : ℕ) (t : ℝ) (ht : 1 ≤ t)
    (hsum : ∀ r, (∑ i, ∑ a ∈ events r i, w i a) ≤ t⁻¹)
    (hbudget : (Fintype.card R : ℝ) * (Real.exp 1 / t ^ m) < 1) :
    ∃ x : ∀ i, A i, ∀ r, appearanceCount (events r) x < m := by
  classical
  let bad (r : R) : Finset (∀ i, A i) :=
    Finset.univ.filter fun x => m ≤ appearanceCount (events r) x
  have hprob (r : R) : (∑ x ∈ bad r, ∏ i, w i (x i)) ≤ Real.exp 1 / t ^ m :=
    independent_many_events_small_sum w hw htotal (events r) m t ht (hsum r)
  have htotalBad : (∑ r, ∑ x ∈ bad r, ∏ i, w i (x i)) < 1 := by
    apply lt_of_le_of_lt (Finset.sum_le_sum (fun r _ => hprob r))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hbudget
  obtain ⟨x, hx⟩ := exists_avoiding_weighted_events (fun x : ∀ i, A i => ∏ i, w i (x i))
    (fun x => Finset.prod_nonneg fun i _ => hw i (x i)) bad
    (by simpa only [total_product_weight w htotal] using htotalBad)
  refine ⟨x, ?_⟩
  intro r
  have hnot : ¬ m ≤ appearanceCount (events r) x := by
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hx r
  omega

end IndependentEvents

end Erdos624.Disproof

/- Source module Erdos624.RepairLists. -/

namespace Erdos624.Disproof

open Finset Module

variable {I F G : Type*} [Fintype I] [DecidableEq I]
  [Field F] [Field G] [Algebra (ZMod 2) F] [Algebra (ZMod 2) G]

def outerKernel (L : BranchLabels I F G) (B : Finset I) : Submodule (ZMod 2) (I → ZMod 2) :=
  coordinateSpace B ⊓ (LinearMap.ker L.outerU ⊓ LinearMap.ker L.outerV)

def goodOuter (L : BranchLabels I F G) (B : Finset I) (k : ℕ) : Prop :=
  finrank (ZMod 2) (outerKernel L B) ≤ k

theorem goodOuter_mono (L : BranchLabels I F G) {B C : Finset I} {k : ℕ}
    (hBC : B ⊆ C) (hC : goodOuter L C k) : goodOuter L B k := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  apply le_trans (Submodule.finrank_mono ?_) hC
  exact inf_le_inf_right _ (coordinateSpace_mono hBC)

def innerMarker (L : BranchLabels I F G) (a : F) (A : Finset I) : Prop :=
  A.Nonempty ∧ A.card % 2 = 0 ∧
    L.outerU (indicatorVector A) = a * L.outerV (indicatorVector A) ∧
    L.innerU a (indicatorVector A) = 0 ∧ L.innerV a (indicatorVector A) = 0

def outerMarker (L : BranchLabels I F G) (a : F) (b : G)
    (D : Submodule (ZMod 2) (I → ZMod 2)) : Prop :=
  finrank (ZMod 2) D = 3 ∧
    (∀ v ∈ D, L.outerU v = 0 ∧ L.outerV v = 0 ∧ L.innerU a v = b * L.innerV a v) ∧
    ∃ v ∈ D, L.innerV a v ≠ 0

section Lists

variable [Fintype F] [Fintype G]

noncomputable def firstRepairGroups (L : BranchLabels I F G) (B : Finset I) (k : ℕ) : Finset F := by
  classical
  exact Finset.univ.filter fun a => ∃ A ⊆ B, A.card ≤ 53 * k ∧ innerMarker L a A

noncomputable def firstRepairList (L : BranchLabels I F G) (B : Finset I) (k : ℕ) : Finset (F × G) := by
  classical
  exact if goodOuter L B k ∧ B.card % 2 = 1 ∧ B.card ≤ 75 * k + 1 then
    (firstRepairGroups L B k) ×ˢ Finset.univ else ∅

noncomputable def secondRepairList (L : BranchLabels I F G) (B : Finset I) (k : ℕ) : Finset (F × G) := by
  classical
  exact if goodOuter L B k ∧ B.card % 2 = 1 ∧ B.card ≤ 100 * k + 1217 then
    Finset.univ.filter fun c : F × G =>
      ∃ D : Submodule (ZMod 2) (I → ZMod 2),
        subspaceSupport D ⊆ B ∧ (subspaceSupport D).card ≤ 91 * k ∧ outerMarker L c.1 c.2 D
  else ∅

omit [Fintype I] in
theorem firstRepairList_card_le (L : BranchLabels I F G) (B : Finset I) (k R : ℕ)
    (hgroups : (firstRepairGroups L B k).card ≤ R) :
    (firstRepairList L B k).card ≤ R * Fintype.card G := by
  classical
  unfold firstRepairList
  split
  · simpa only [Finset.card_product, Finset.card_univ] using Nat.mul_le_mul_right _ hgroups
  · simp

omit [Fintype I] in
theorem firstRepairList_mem (L : BranchLabels I F G) (B A : Finset I) (k : ℕ) (a : F) (b : G)
    (hgood : goodOuter L B k) (hodd : B.card % 2 = 1) (hsize : B.card ≤ 75 * k + 1)
    (hAB : A ⊆ B) (hA : A.card ≤ 53 * k) (hmarker : innerMarker L a A) :
    (a, b) ∈ firstRepairList L B k := by
  classical
  simp only [firstRepairList, hgood, hodd, hsize, and_self, ↓reduceIte, Finset.mem_product,
    Finset.mem_univ, and_true]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, A, hAB, hA, hmarker⟩

theorem secondRepairList_mem (L : BranchLabels I F G) (B : Finset I) (k : ℕ) (a : F) (b : G)
    (hgood : goodOuter L B k) (hodd : B.card % 2 = 1) (hsize : B.card ≤ 100 * k + 1217)
    (D : Submodule (ZMod 2) (I → ZMod 2)) (hDB : subspaceSupport D ⊆ B)
    (hDsize : (subspaceSupport D).card ≤ 91 * k) (hmarker : outerMarker L a b D) :
    (a, b) ∈ secondRepairList L B k := by
  classical
  simp only [secondRepairList, hgood, hodd, hsize, and_self, ↓reduceIte,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨D, hDB, hDsize, hmarker⟩

theorem secondRepairList_witness (L : BranchLabels I F G) (B : Finset I) (k : ℕ)
    (a : F) (b : G) (hc : (a, b) ∈ secondRepairList L B k) :
    ∃ v ∈ outerKernel L B, L.innerV a v ≠ 0 ∧ L.innerU a v = b * L.innerV a v := by
  classical
  unfold secondRepairList at hc
  split at hc
  · obtain ⟨_, D, hDB, _, hDdim, heq, v, hv, hne⟩ := Finset.mem_filter.mp hc
    obtain ⟨hU, hV, hi⟩ := heq v hv
    refine ⟨v, ?_, hne, hi⟩
    exact ⟨le_coordinateSpace_iff.mpr hDB hv, hU, hV⟩
  · simp at hc

theorem secondRepairList_group_card_le [DecidableEq F] [DecidableEq G]
    (L : BranchLabels I F G) (B : Finset I) (k : ℕ)
    (hgood : goodOuter L B k) (a : F) :
    (Finset.univ.filter fun b : G => (a, b) ∈ secondRepairList L B k).card ≤ 2 ^ k := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  let W := outerKernel L B
  let : Fintype W := Fintype.ofFinite W
  let candidates : Finset G := Finset.univ.image fun v : W => L.innerU a v / L.innerV a v
  have hsub : (Finset.univ.filter fun b : G => (a, b) ∈ secondRepairList L B k) ⊆ candidates := by
    intro b hb
    obtain ⟨v, hv, hne, heq⟩ := secondRepairList_witness L B k a b (Finset.mem_filter.mp hb).2
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, (div_eq_iff hne).mpr heq⟩
  calc
    (Finset.univ.filter fun b : G => (a, b) ∈ secondRepairList L B k).card ≤ candidates.card :=
      Finset.card_le_card hsub
    _ ≤ Fintype.card W := by
      simpa only [Finset.card_univ] using
        (Finset.card_image_le (s := (Finset.univ : Finset W))
          (f := fun v : W => L.innerU a v / L.innerV a v))
    _ ≤ 2 ^ k := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2)]
      simpa using Nat.pow_le_pow_right (n := 2) (by decide) hgood

theorem secondRepairList_fibre_card_le [DecidableEq F]
    (L : BranchLabels I F G) (B : Finset I) (k : ℕ)
    (hgood : goodOuter L B k) (a : F) :
    ((secondRepairList L B k).filter fun c : F × G => c.1 = a).card ≤ 2 ^ k := by
  classical
  apply le_trans _ (secondRepairList_group_card_le L B k hgood a)
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro c hc
    obtain ⟨hc, ha⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [← ha, Prod.mk.eta] using hc
  · intro c hc d hd hcd
    exact Prod.ext ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm) hcd

theorem secondRepairList_card_le [DecidableEq F]
    (L : BranchLabels I F G) (B : Finset I) (k R : ℕ)
    (hgood : goodOuter L B k)
    (hgroups : ((secondRepairList L B k).image Prod.fst).card ≤ R) :
    (secondRepairList L B k).card ≤ R * 2 ^ k := by
  classical
  calc
    (secondRepairList L B k).card =
        ∑ a ∈ (secondRepairList L B k).image Prod.fst,
          ((secondRepairList L B k).filter fun c => c.1 = a).card :=
      Finset.card_eq_sum_card_image Prod.fst (secondRepairList L B k)
    _ ≤ ∑ _a ∈ (secondRepairList L B k).image Prod.fst, 2 ^ k :=
      Finset.sum_le_sum fun a _ => secondRepairList_fibre_card_le L B k hgood a
    _ = ((secondRepairList L B k).image Prod.fst).card * 2 ^ k := by simp
    _ ≤ R * 2 ^ k := Nat.mul_le_mul_right _ hgroups

end Lists

end Erdos624.Disproof

/- Source module Erdos624.PairLabels. -/

namespace Erdos624.Disproof

variable {I F G : Type*}
  [Field F] [Field G] [Algebra (ZMod 2) F] [Algebra (ZMod 2) G]

def labelsFromPairs
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F)
    (inner : F → (I → ZMod 2) →ₗ[ZMod 2] G × G) : BranchLabels I F G where
  outerU := (LinearMap.fst (ZMod 2) F F).comp outer
  outerV := (LinearMap.snd (ZMod 2) F F).comp outer
  innerU a := (LinearMap.fst (ZMod 2) G G).comp (inner a)
  innerV a := (LinearMap.snd (ZMod 2) G G).comp (inner a)

theorem outerKernel_labelsFromPairs [DecidableEq I]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F)
    (inner : F → (I → ZMod 2) →ₗ[ZMod 2] G × G) (B : Finset I) :
    outerKernel (labelsFromPairs outer inner) B = coordinateSpace B ⊓ LinearMap.ker outer := by
  ext v
  simp [outerKernel, labelsFromPairs, LinearMap.mem_ker, Prod.ext_iff]

theorem goodOuter_labelsFromPairs [DecidableEq I]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F)
    (inner : F → (I → ZMod 2) →ₗ[ZMod 2] G × G) (B : Finset I) (k : ℕ) :
    goodOuter (labelsFromPairs outer inner) B k ↔
      Module.finrank (ZMod 2)
        (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2)) ≤ k := by
  rw [goodOuter, outerKernel_labelsFromPairs]

def pairDifference (b : G) : (G × G) →ₗ[ZMod 2] G :=
  LinearMap.fst (ZMod 2) G G - b • LinearMap.snd (ZMod 2) G G

def pairDifferenceRestriction (D : Submodule (ZMod 2) (I → ZMod 2)) (b : G) :
    ((I → ZMod 2) →ₗ[ZMod 2] G × G) →+ (D →ₗ[ZMod 2] G) where
  toFun f := ((pairDifference b).comp f).comp D.subtype
  map_zero' := by ext v; simp
  map_add' f g := by ext v; simp

theorem pairDifferenceRestriction_surjective (D : Submodule (ZMod 2) (I → ZMod 2)) (b : G) :
    Function.Surjective (pairDifferenceRestriction D b) := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  intro f
  obtain ⟨g, hg⟩ := f.exists_extend
  refine ⟨g.prod 0, ?_⟩
  ext v
  have h := LinearMap.congr_fun hg v
  simpa [pairDifferenceRestriction, pairDifference] using h

theorem pairDifferenceRestriction_zero_weight
    (D : Submodule (ZMod 2) (I → ZMod 2)) (b : G)
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] G × G)] [Fintype (D →ₗ[ZMod 2] G)]
    [DecidableEq (D →ₗ[ZMod 2] G)] :
    ∑ f ∈ Finset.univ.filter (fun f : (I → ZMod 2) →ₗ[ZMod 2] G × G =>
      pairDifferenceRestriction D b f = 0), uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G) f =
      (Fintype.card (D →ₗ[ZMod 2] G) : ℝ)⁻¹ :=
  surjective_hom_fiber_weight (pairDifferenceRestriction D b)
    (pairDifferenceRestriction_surjective D b) 0

end Erdos624.Disproof

/- Source module Erdos624.RatioCounting. -/

namespace Erdos624.Disproof

open Finset

/-- Each vector with a nonzero denominator specifies one group. A common zero allows all groups. -/
theorem ratio_group_count_bound {X F : Type*} [Fintype X] [Field F] [Fintype F] [DecidableEq F]
    (U V : X → F) :
    ∑ a : F, (Finset.univ.filter fun x : X => U x = a * V x).card ≤
      Fintype.card X + Fintype.card F *
        (Finset.univ.filter fun x : X => U x = 0 ∧ V x = 0).card := by
  classical
  have hpoint (x : X) : (Finset.univ.filter fun a : F => U x = a * V x).card ≤
      1 + if U x = 0 ∧ V x = 0 then Fintype.card F else 0 := by
    by_cases hV : V x = 0
    · by_cases hU : U x = 0 <;> simp [hV, hU]
    · have heq (a : F) : U x = a * V x ↔ a = U x / V x := by
        constructor
        · intro h
          exact ((div_eq_iff hV).mpr h).symm
        · intro h
          exact (div_eq_iff hV).mp h.symm
      simp [heq, hV]
      exact Finset.card_le_one.mpr (fun a ha b hb =>
        (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hcommon : (∑ x : X, if U x = 0 ∧ V x = 0 then Fintype.card F else 0) =
      Fintype.card F * (Finset.univ.filter fun x : X => U x = 0 ∧ V x = 0).card := by
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  calc
    ∑ a : F, (Finset.univ.filter fun x : X => U x = a * V x).card =
        ∑ x : X, (Finset.univ.filter fun a : F => U x = a * V x).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ x : X, (1 + if U x = 0 ∧ V x = 0 then Fintype.card F else 0) :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = Fintype.card X + Fintype.card F *
        (Finset.univ.filter fun x : X => U x = 0 ∧ V x = 0).card := by
      rw [Finset.sum_add_distrib, hcommon]
      simp

end Erdos624.Disproof

/- Source module Erdos624.GroupProbabilities. -/

namespace Erdos624.Disproof

open Finset

variable {I F G : Type*} [Fintype I] [DecidableEq I]
  [Field F] [Field G] [Algebra (ZMod 2) F] [Algebra (ZMod 2) G]

noncomputable def firstMaskRequests
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F) (B : Finset I) (k : ℕ) (a : F) :
    Finset (Finset I) := by
  classical
  exact B.powerset.filter fun A => A.Nonempty ∧ A.card % 2 = 0 ∧ A.card ≤ 53 * k ∧
    (outer (indicatorVector A)).1 = a * (outer (indicatorVector A)).2

noncomputable def firstGroupEvent [Fintype ((I → ZMod 2) →ₗ[ZMod 2] G × G)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F) (B : Finset I) (k : ℕ) (a : F) :
    Finset ((I → ZMod 2) →ₗ[ZMod 2] G × G) := by
  classical
  exact Finset.univ.filter fun inner =>
    ∃ A ∈ firstMaskRequests outer B k a, inner (indicatorVector A) = 0

theorem firstGroupEvent_weight_le [Fintype G] [Fintype ((I → ZMod 2) →ₗ[ZMod 2] G × G)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F) (B : Finset I) (k : ℕ) (a : F) :
    ∑ inner ∈ firstGroupEvent (G := G) outer B k a,
      uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G) inner ≤
      ((firstMaskRequests outer B k a).card : ℝ) * (Fintype.card (G × G) : ℝ)⁻¹ := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  let vectors := (firstMaskRequests outer B k a).image indicatorVector
  have hnonzero : ∀ v ∈ vectors, v ≠ 0 := by
    intro v hv
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hv
    exact indicatorVector_ne_zero (Finset.mem_filter.mp hA).2.1
  have hcover : ∀ inner ∈ firstGroupEvent (G := G) outer B k a,
      ∃ v ∈ vectors, inner v = 0 := by
    intro inner hinner
    obtain ⟨_, A, hA, hzero⟩ := Finset.mem_filter.mp hinner
    exact ⟨indicatorVector A, Finset.mem_image.mpr ⟨A, hA, rfl⟩, hzero⟩
  have h := linear_vanishing_union_bound (F := ZMod 2) vectors hnonzero
    (firstGroupEvent (G := G) outer B k a) hcover
  apply h.trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

omit [Fintype I] in
theorem firstRepairGroups_mem_iff [Fintype F] [Fintype G]
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] G × G)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F)
    (inner : F → (I → ZMod 2) →ₗ[ZMod 2] G × G) (B : Finset I) (k : ℕ) (a : F) :
    a ∈ firstRepairGroups (labelsFromPairs outer inner) B k ↔ inner a ∈ firstGroupEvent outer B k a := by
  classical
  simp only [firstRepairGroups, firstGroupEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, hAB, hsize, hne, heven, houter, hU, hV⟩
    refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAB, hne, heven, hsize, houter⟩, ?_⟩
    exact Prod.ext hU hV
  · rintro ⟨A, hA, hzero⟩
    obtain ⟨hAB, hne, heven, hsize, houter⟩ := Finset.mem_filter.mp hA
    refine ⟨A, Finset.mem_powerset.mp hAB, hsize, hne, heven, houter, ?_, ?_⟩
    · exact congrArg Prod.fst hzero
    · exact congrArg Prod.snd hzero

omit [Fintype I] in
theorem firstRepairGroups_count [Fintype F] [Fintype G]
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] G × G)]
    [DecidableEq ((I → ZMod 2) →ₗ[ZMod 2] G × G)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F)
    (inner : F → (I → ZMod 2) →ₗ[ZMod 2] G × G) (B : Finset I) (k : ℕ) :
    (firstRepairGroups (labelsFromPairs outer inner) B k).card =
      appearanceCount (fun a => firstGroupEvent (G := G) outer B k a) inner := by
  classical
  unfold appearanceCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact firstRepairGroups_mem_iff outer inner B k a

end Erdos624.Disproof

/- Source module Erdos624.FirstListBound. -/

namespace Erdos624.Disproof

open Finset Module

variable {I F : Type*} [Fintype I] [DecidableEq I]
  [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- The outer equations bound the total number of possible first-marker requests. -/
theorem sum_firstMaskRequests_card_le
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F) (B : Finset I) (k : ℕ)
    (hgood : finrank (ZMod 2)
      (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2)) ≤ k) :
    ∑ a : F, (firstMaskRequests outer B k a).card ≤
      2 ^ B.card + Fintype.card F * 2 ^ k := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  let W := coordinateSpace B
  let Z := (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2))
  let : Fintype W := Fintype.ofFinite W
  let : Fintype Z := Fintype.ofFinite Z
  let S (a : F) : Finset W := Finset.univ.filter fun v => (outer v).1 = a * (outer v).2
  have hrequests (a : F) : (firstMaskRequests outer B k a).card ≤ (S a).card := by
    let g (A : firstMaskRequests outer B k a) : S a :=
      ⟨⟨indicatorVector A.val, mem_coordinateSpace_iff.mpr (by
        rw [vectorSupport_indicatorVector]
        exact Finset.mem_powerset.mp (Finset.mem_filter.mp A.property).1)⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp A.property).2.2.2.2⟩⟩
    have hg : Function.Injective g := by
      intro A A' hAA
      apply Subtype.ext
      have hv := congrArg (fun v : S a => ((v.val : W).val)) hAA
      have hs := congrArg vectorSupport hv
      simpa only [g, vectorSupport_indicatorVector] using hs
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg
  let C : Finset W := Finset.univ.filter fun v => (outer v).1 = 0 ∧ (outer v).2 = 0
  have hcommon : C.card ≤ Fintype.card Z := by
    let j (v : C) : Z :=
      ⟨(v.val : W).val, (v.val : W).property,
        Prod.ext (Finset.mem_filter.mp v.property).2.1 (Finset.mem_filter.mp v.property).2.2⟩
    have hj : Function.Injective j := by
      intro v w hvw
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Z => z.val) hvw
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective j hj
  have hZcard : Fintype.card Z ≤ 2 ^ k := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) hgood
  have hWcard : Fintype.card W = 2 ^ B.card := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), coordinateSpace_finrank]
    norm_num
  calc
    ∑ a : F, (firstMaskRequests outer B k a).card ≤ ∑ a : F, (S a).card :=
      Finset.sum_le_sum fun a _ => hrequests a
    _ ≤ Fintype.card W + Fintype.card F * C.card :=
      ratio_group_count_bound (fun v : W => (outer v).1) (fun v : W => (outer v).2)
    _ ≤ 2 ^ B.card + Fintype.card F * 2 ^ k := by
      rw [hWcard]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hcommon.trans hZcard)) _

theorem sum_firstGroupEvent_weight_le
    {G : Type*} [Field G] [Fintype G] [Algebra (ZMod 2) G]
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] G × G)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F) (B : Finset I) (k : ℕ)
    (hgood : finrank (ZMod 2)
      (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2)) ≤ k) :
    ∑ a : F, ∑ inner ∈ firstGroupEvent (G := G) outer B k a,
      uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G) inner ≤
      ((2 ^ B.card + Fintype.card F * 2 ^ k : ℕ) : ℝ) * (Fintype.card (G × G) : ℝ)⁻¹ := by
  calc
    ∑ a : F, ∑ inner ∈ firstGroupEvent (G := G) outer B k a,
        uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G) inner ≤
        ∑ a : F, ((firstMaskRequests outer B k a).card : ℝ) * (Fintype.card (G × G) : ℝ)⁻¹ :=
      Finset.sum_le_sum fun a _ => firstGroupEvent_weight_le outer B k a
    _ = ((∑ a : F, (firstMaskRequests outer B k a).card : ℕ) : ℝ) *
        (Fintype.card (G × G) : ℝ)⁻¹ := by rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ((2 ^ B.card + Fintype.card F * 2 ^ k : ℕ) : ℝ) * (Fintype.card (G × G) : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast sum_firstMaskRequests_card_le outer B k hgood

end Erdos624.Disproof

/- Source module Erdos624.SecondListBound. -/

namespace Erdos624.Disproof

open Finset Module

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [Field G] [Fintype G] [Algebra (ZMod 2) G]
  [Fintype ((I → ZMod 2) →ₗ[ZMod 2] G × G)]

noncomputable def secondGroupEvent (K : Submodule (ZMod 2) (I → ZMod 2)) :
    Finset ((I → ZMod 2) →ₗ[ZMod 2] G × G) := by
  classical
  exact Finset.univ.filter fun inner =>
    ∃ D : Submodule (ZMod 2) (I → ZMod 2), D ≤ K ∧ finrank (ZMod 2) D = 3 ∧
      ∃ b : G, pairDifferenceRestriction D b inner = 0

theorem secondGroupEvent_weight_le (K : Submodule (ZMod 2) (I → ZMod 2)) (k : ℕ)
    (hK : finrank (ZMod 2) K ≤ k) :
    ∑ inner ∈ secondGroupEvent (G := G) K, uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G) inner ≤
      ((2 ^ (3 * k) * Fintype.card G : ℕ) : ℝ) * ((2 : ℝ) ^ (3 * finrank (ZMod 2) G))⁻¹ := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  let S := {D : Submodule (ZMod 2) (I → ZMod 2) // D ≤ K ∧ finrank (ZMod 2) D = 3}
  let : Fintype K := Fintype.ofFinite K
  let : Fintype S := Fintype.ofInjective (containedSubspaceCode K 3) (containedSubspaceCode_injective K 3)
  let bad (r : S × G) : Finset ((I → ZMod 2) →ₗ[ZMod 2] G × G) :=
    Finset.univ.filter fun inner => pairDifferenceRestriction r.1.val r.2 inner = 0
  have hcover : ∀ inner ∈ secondGroupEvent (G := G) K, ∃ r : S × G, inner ∈ bad r := by
    intro inner hinner
    obtain ⟨_, D, hDK, hDdim, b, hzero⟩ := Finset.mem_filter.mp hinner
    exact ⟨(⟨D, hDK, hDdim⟩, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩⟩
  have hfiber (r : S × G) : (∑ inner ∈ bad r,
      uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G) inner) =
      ((2 : ℝ) ^ (3 * finrank (ZMod 2) G))⁻¹ := by
    letI : Module (ZMod 2) r.1.val := SMulMemClass.toModule r.1.val
    let : Fintype r.1.val := Fintype.ofFinite r.1.val
    let : Fintype (r.1.val →ₗ[ZMod 2] G) :=
      Fintype.ofInjective (fun f : r.1.val →ₗ[ZMod 2] G => (f : r.1.val → G)) DFunLike.coe_injective
    dsimp only [bad]
    have hw := pairDifferenceRestriction_zero_weight (I := I) (G := G) r.1.val r.2
    rw [binary_linear_map_card (V := r.1.val) (W := G), r.1.property.2,
      Nat.cast_pow, Nat.cast_ofNat] at hw
    simpa only [DFunLike.ext_iff, pairDifferenceRestriction, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.subtype_apply] using hw
  have hKcard : Fintype.card K ≤ 2 ^ k := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) hK
  have hScard : Fintype.card S ≤ 2 ^ (3 * k) := by
    have h := card_contained_subspaces K 3
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    calc
      Fintype.card S ≤ Fintype.card K ^ 3 := h
      _ ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left hKcard 3
      _ = 2 ^ (3 * k) := by rw [← pow_mul, Nat.mul_comm]
  have h := weighted_union_bound (uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G))
    (uniformWeight_nonneg _) (secondGroupEvent (G := G) K) bad hcover
  have hsum : (∑ r : S × G, ∑ inner ∈ bad r,
      uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] G × G) inner) =
      (Fintype.card (S × G) : ℝ) * ((2 : ℝ) ^ (3 * finrank (ZMod 2) G))⁻¹ := by
    simp_rw [hfiber]
    simp
  apply (h.trans_eq hsum).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast (show Fintype.card (S × G) ≤ 2 ^ (3 * k) * Fintype.card G by
    simpa only [Fintype.card_prod] using Nat.mul_le_mul_right (Fintype.card G) hScard)

theorem secondRepairList_mem_event {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F)
    (inner : F → (I → ZMod 2) →ₗ[ZMod 2] G × G) (B : Finset I) (k : ℕ) (a : F) (b : G)
    (hc : (a, b) ∈ secondRepairList (labelsFromPairs outer inner) B k) :
    inner a ∈ secondGroupEvent
      (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2)) := by
  classical
  unfold secondRepairList at hc
  split at hc
  · obtain ⟨_, D, hDB, _, hDdim, heq, _⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, D, ?_, hDdim, b, ?_⟩
    · intro v hv
      have hcoords := le_coordinateSpace_iff.mpr hDB hv
      have houter := heq v hv
      exact ⟨hcoords, Prod.ext houter.1 houter.2.1⟩
    · ext v
      have hinner := (heq v.val v.property).2.2
      simpa [pairDifferenceRestriction, pairDifference, labelsFromPairs, sub_eq_zero] using hinner
  · simp at hc

theorem secondRepairList_groups_count {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [DecidableEq F] [DecidableEq ((I → ZMod 2) →ₗ[ZMod 2] G × G)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] F × F)
    (inner : F → (I → ZMod 2) →ₗ[ZMod 2] G × G) (B : Finset I) (k : ℕ) :
    ((secondRepairList (labelsFromPairs outer inner) B k).image Prod.fst).card ≤
      appearanceCount (fun _a : F => secondGroupEvent (G := G)
        (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2))) inner := by
  classical
  apply Finset.card_le_card
  intro a ha
  obtain ⟨⟨a', b⟩, hc, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, secondRepairList_mem_event outer inner B k a' b hc⟩

end Erdos624.Disproof

/- Source module Erdos624.Fields. -/

namespace Erdos624.Disproof

abbrev OuterField (k : ℕ) := GaloisField 2 (60 * k)
abbrev InnerField (k : ℕ) := GaloisField 2 (40 * k)

noncomputable def outerFieldFintype (k : ℕ) : Fintype (OuterField k) :=
  Fintype.ofFinite _

noncomputable def innerFieldFintype (k : ℕ) : Fintype (InnerField k) :=
  Fintype.ofFinite _

theorem outerField_finrank (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    Module.finrank (ZMod 2) (OuterField k) = 60 * k :=
  GaloisField.finrank 2 (by omega)

theorem innerField_finrank (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    Module.finrank (ZMod 2) (InnerField k) = 40 * k :=
  GaloisField.finrank 2 (by omega)

theorem outerField_card (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    Fintype.card (OuterField k) = 2 ^ (60 * k) := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 (60 * k) (by omega)

theorem innerField_card (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    Fintype.card (InnerField k) = 2 ^ (40 * k) := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 (40 * k) (by omega)

theorem palette_card (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    Fintype.card (OuterField k × InnerField k) = 2 ^ (100 * k) := by
  rw [Fintype.card_prod, outerField_card k hk, innerField_card k hk, ← pow_add]
  congr 1
  omega

noncomputable def paletteEquiv (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    (OuterField k × InnerField k) ≃ Fin (2 ^ (100 * k)) :=
  Fintype.equivFinOfCardEq (palette_card k hk)

end Erdos624.Disproof

/- Source module Erdos624.Parameters. -/

namespace Erdos624.Disproof

theorem inner_marker_size (k u s : ℕ) (hk : 2000 ≤ k) (hu : u ≤ 100 * k + 1217)
    (hs : 31 * s ≤ 16 * u) : s ≤ 53 * k := by omega

theorem outer_marker_size (k u s : ℕ) (hk : 2000 ≤ k) (hu : u ≤ 100 * k + 1217)
    (hs : 10 * s ≤ 9 * u) : s ≤ 91 * k := by omega

theorem inner_extension_parameters (k u s : ℕ) (hu : 100 * k + 17 ≤ u) (hs : s ≤ 53 * k) :
    s + 2 * (22 * k) + 1 ≤ u ∧ s + 22 * k + 1 ≤ 75 * k + 1 := by omega

theorem outer_extension_parameters (k u s : ℕ) (hu : 100 * k + 17 ≤ u) (hs : s ≤ 91 * k) :
    s + 2 * (4 * k) + 1 ≤ u ∧ s + 4 * k + 1 ≤ 100 * k + 1217 := by omega

theorem first_group_nat_bound (k u : ℕ) (hk : 1 ≤ k) (hu : u ≤ 75 * k + 1) :
    ((2 : ℕ) ^ u + 2 ^ (60 * k) * 2 ^ k) * 2 ^ (3 * k) ≤ 2 ^ (80 * k) := by
  have h1 : (2 : ℕ) ^ u * 2 ^ (3 * k) ≤ 2 ^ (78 * k + 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : ((2 : ℕ) ^ (60 * k) * 2 ^ k) * 2 ^ (3 * k) ≤ 2 ^ (78 * k + 1) := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  calc
    ((2 : ℕ) ^ u + 2 ^ (60 * k) * 2 ^ k) * 2 ^ (3 * k) ≤
        2 ^ (78 * k + 1) + 2 ^ (78 * k + 1) := by
      rw [add_mul]
      exact Nat.add_le_add h1 h2
    _ = 2 ^ ((78 * k + 1) + 1) := by
      exact (by omega : 2 ^ (78 * k + 1) + 2 ^ (78 * k + 1) = 2 ^ (78 * k + 1) * 2).trans
        (pow_succ (2 : ℕ) (78 * k + 1)).symm
    _ ≤ 2 ^ (80 * k) := Nat.pow_le_pow_right (by decide) (by omega)

theorem first_group_real_bound (k u : ℕ) (hk : 1 ≤ k) (hu : u ≤ 75 * k + 1) :
    (((2 : ℕ) ^ u + 2 ^ (60 * k) * 2 ^ k : ℕ) : ℝ) / (2 : ℝ) ^ (80 * k) ≤
      ((2 : ℝ) ^ (3 * k))⁻¹ := by
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  exact_mod_cast first_group_nat_bound k u hk hu

theorem second_group_nat_bound (k : ℕ) :
    (((2 : ℕ) ^ (60 * k) * 2 ^ (3 * k)) * 2 ^ (40 * k)) * 2 ^ (3 * k) ≤ 2 ^ (120 * k) := by
  rw [← pow_add, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem second_group_real_bound (k : ℕ) :
    ((((2 : ℕ) ^ (60 * k) * 2 ^ (3 * k)) * 2 ^ (40 * k) : ℕ) : ℝ) /
      (2 : ℝ) ^ (120 * k) ≤ ((2 : ℝ) ^ (3 * k))⁻¹ := by
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  exact_mod_cast second_group_nat_bound k

theorem bad_branch_nat_bound (k u : ℕ) (hk : 2000 ≤ k) (hu : u ≤ 100 * k + 1217) :
    (2 : ℕ) ^ ((k + 1) * u) * 2 ^ (10 * k * k) ≤ 2 ^ ((k + 1) * (120 * k)) := by
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hgap : u + 10 * k ≤ 120 * k := by omega
  have hmul := Nat.mul_le_mul_left (k + 1) hgap
  nlinarith

theorem bad_branch_real_bound (k u : ℕ) (hk : 2000 ≤ k) (hu : u ≤ 100 * k + 1217) :
    (2 : ℝ) ^ ((k + 1) * u) / (2 : ℝ) ^ ((k + 1) * (120 * k)) ≤
      ((2 : ℝ) ^ (10 * k * k))⁻¹ := by
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  exact_mod_cast bad_branch_nat_bound k u hk hu

theorem outer_union_exponent (k : ℕ) (hk : 2000 ≤ k) :
    100 * k * (100 * k + 1217) < 1200 * (10 * k * k) := by
  have hkpos : 0 < k := by omega
  have hmul := Nat.mul_le_mul_right k hk
  nlinarith

theorem inner_union_exponent (k : ℕ) (hk : 2000 ≤ k) :
    200 * k + 100 * k * (100 * k + 1217) + 3 < (3 * k) * (10000 * k) := by
  have hkpos : 0 < k := by omega
  have hmul := Nat.mul_le_mul_right k hk
  nlinarith

theorem small_mask_factor_bound (k : ℕ) (hk : 2000 ≤ k) :
    (100 * k + 1218) * ((2 : ℕ) ^ (100 * k)) ^ (100 * k + 1217) ≤
      2 ^ (200 * k + 100 * k * (100 * k + 1217)) := by
  have hlinear : 100 * k + 1218 ≤ 200 * k := by omega
  have hpow : 200 * k ≤ (2 : ℕ) ^ (200 * k) := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    (100 * k + 1218) * ((2 : ℕ) ^ (100 * k)) ^ (100 * k + 1217) ≤
        2 ^ (200 * k) * ((2 : ℕ) ^ (100 * k)) ^ (100 * k + 1217) :=
      Nat.mul_le_mul_right _ (hlinear.trans hpow)
    _ = 2 ^ (200 * k + 100 * k * (100 * k + 1217)) := by rw [← pow_mul, ← pow_add]

theorem inner_union_budget (k n : ℕ) (hk : 2000 ≤ k)
    (hn : n ≤ (100 * k + 1218) * ((2 : ℕ) ^ (100 * k)) ^ (100 * k + 1217)) :
    ((2 * n : ℕ) : ℝ) * (Real.exp 1 / ((2 : ℝ) ^ (3 * k)) ^ (10000 * k)) < 1 := by
  let E := 200 * k + 100 * k * (100 * k + 1217)
  have hn' : n ≤ (2 : ℕ) ^ E := hn.trans (small_mask_factor_bound k hk)
  have h2n : ((2 * n : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ E := by exact_mod_cast Nat.mul_le_mul_left 2 hn'
  have hexp : Real.exp 1 ≤ 4 := Real.exp_one_lt_three.le.trans (by norm_num)
  have hnum : ((2 * n : ℕ) : ℝ) * Real.exp 1 ≤ 8 * (2 : ℝ) ^ E := by
    calc
      ((2 * n : ℕ) : ℝ) * Real.exp 1 ≤ (2 * (2 : ℝ) ^ E) * Real.exp 1 :=
        mul_le_mul_of_nonneg_right h2n (Real.exp_nonneg _)
      _ ≤ (2 * (2 : ℝ) ^ E) * 4 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 8 * (2 : ℝ) ^ E := by ring
  calc
    ((2 * n : ℕ) : ℝ) * (Real.exp 1 / ((2 : ℝ) ^ (3 * k)) ^ (10000 * k)) =
        (((2 * n : ℕ) : ℝ) * Real.exp 1) / (2 : ℝ) ^ ((3 * k) * (10000 * k)) := by
      rw [← pow_mul]
      ring
    _ ≤ (8 * (2 : ℝ) ^ E) / (2 : ℝ) ^ ((3 * k) * (10000 * k)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (2 : ℝ) ^ (E + 3) / (2 : ℝ) ^ ((3 * k) * (10000 * k)) := by
      rw [pow_add]
      norm_num
      ring
    _ < 1 := by
      apply (div_lt_one (by positivity)).mpr
      exact pow_lt_pow_right₀ (by norm_num) (inner_union_exponent k hk)

end Erdos624.Disproof

/- Source module Erdos624.SpecializedBounds. -/

namespace Erdos624.Disproof

open Finset Module

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem innerPair_card (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    Fintype.card (InnerField k × InnerField k) = 2 ^ (80 * k) := by
  rw [Fintype.card_prod, innerField_card k hk, ← pow_add]
  congr 1
  omega

theorem outerPair_finrank (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 0 < k) :
    finrank (ZMod 2) (OuterField k × OuterField k) = 120 * k := by
  rw [Module.finrank_prod, outerField_finrank k hk]
  omega

theorem first_group_sum_small (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] OuterField k × OuterField k) (B : Finset I)
    (hB : B.card ≤ 75 * k + 1)
    (hgood : finrank (ZMod 2)
      (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2)) ≤ k) :
    ∑ a : OuterField k, ∑ inner ∈ firstGroupEvent (G := InnerField k) outer B k a,
      uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k) inner ≤
      ((2 : ℝ) ^ (3 * k))⁻¹ := by
  have hkpos : 0 < k := by omega
  have h := sum_firstGroupEvent_weight_le (G := InnerField k) outer B k hgood
  rw [outerField_card k hkpos, innerPair_card k hkpos] at h
  apply h.trans
  simpa only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using
    first_group_real_bound k B.card (by omega) hB

theorem second_group_sum_small (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k)]
    (K : Submodule (ZMod 2) (I → ZMod 2)) (hK : finrank (ZMod 2) K ≤ k) :
    ∑ _a : OuterField k, ∑ inner ∈ secondGroupEvent (G := InnerField k) K,
      uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k) inner ≤
      ((2 : ℝ) ^ (3 * k))⁻¹ := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  have hkpos : 0 < k := by omega
  have h := secondGroupEvent_weight_le (G := InnerField k) K k hK
  rw [innerField_card k hkpos, innerField_finrank k hkpos] at h
  have he : 3 * (40 * k) = 120 * k := by omega
  rw [he] at h
  calc
    ∑ _a : OuterField k, ∑ inner ∈ secondGroupEvent (G := InnerField k) K,
        uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k) inner ≤
        (Fintype.card (OuterField k) : ℝ) *
          (((2 ^ (3 * k) * 2 ^ (40 * k) : ℕ) : ℝ) * ((2 : ℝ) ^ (120 * k))⁻¹) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using
        (Finset.sum_le_sum (fun (_a : OuterField k) (_ : _a ∈ Finset.univ) => h))
    _ = ((((2 ^ (60 * k) * 2 ^ (3 * k)) * 2 ^ (40 * k) : ℕ) : ℝ) /
        (2 : ℝ) ^ (120 * k)) := by
      rw [outerField_card k hkpos, div_eq_mul_inv]
      push_cast
      ring
    _ ≤ ((2 : ℝ) ^ (3 * k))⁻¹ := second_group_real_bound k

theorem bad_source_small (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] OuterField k × OuterField k)]
    (B : Finset I) (hB : B.card ≤ 100 * k + 1217) :
    letI : CommRing (ZMod 2) := ZMod.commRing 2
    letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
    letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
    letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
    letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
    ∑ outer ∈ mapsWithLargeRestrictedKernel (W := OuterField k × OuterField k)
        (coordinateSpace B) (k + 1),
      uniformWeight ((I → ZMod 2) →ₗ[ZMod 2] OuterField k × OuterField k) outer ≤
      ((2 : ℝ) ^ (10 * k * k))⁻¹ := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  have h := large_restricted_kernel_weight_bound (W := OuterField k × OuterField k)
    (coordinateSpace B) (k + 1)
  rw [coordinateSpace_finrank, outerPair_finrank k (by omega)] at h
  exact h.trans (bad_branch_real_bound k B.card hk hB)

end Erdos624.Disproof

/- Source module Erdos624.SourceCounts. -/

namespace Erdos624.Disproof

open Finset

variable {I : Type*} [Fintype I]

noncomputable def smallMasks (h : ℕ) : Finset (Finset I) := by
  classical
  exact (Finset.univ : Finset I).powerset.filter fun B => B.card ≤ h

theorem mem_smallMasks (h : ℕ) (B : Finset I) : B ∈ smallMasks h ↔ B.card ≤ h := by
  classical
  simp [smallMasks]

theorem exact_sources_card_le (h : ℕ) :
    ((Finset.univ : Finset I).powersetCard h).card ≤ (Fintype.card I) ^ h := by
  rw [Finset.card_powersetCard, Finset.card_univ]
  exact Nat.choose_le_pow _ _

theorem smallMasks_card_le (h : ℕ) (hI : 0 < Fintype.card I) :
    (smallMasks (I := I) h).card ≤ (h + 1) * (Fintype.card I) ^ h := by
  classical
  have hpartition : (smallMasks (I := I) h).card =
      ∑ r ∈ Finset.range (h + 1), ((smallMasks (I := I) h).filter fun B => B.card = r).card :=
    Finset.card_eq_sum_card_fiberwise (fun B hB =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_smallMasks h B).mp hB)))
  have hfibre (r : ℕ) (hr : r ∈ Finset.range (h + 1)) :
      ((smallMasks (I := I) h).filter fun B => B.card = r).card ≤ (Fintype.card I) ^ h := by
    have hsub : (smallMasks (I := I) h).filter (fun B => B.card = r) ⊆
        (Finset.univ : Finset I).powersetCard r := by
      intro B hB
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hB).2⟩
    apply (Finset.card_le_card hsub).trans
    apply (exact_sources_card_le r).trans
    exact Nat.pow_le_pow_right hI (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
  calc
    (smallMasks (I := I) h).card =
        ∑ r ∈ Finset.range (h + 1), ((smallMasks (I := I) h).filter fun B => B.card = r).card := hpartition
    _ ≤ ∑ _r ∈ Finset.range (h + 1), (Fintype.card I) ^ h := Finset.sum_le_sum hfibre
    _ = (h + 1) * (Fintype.card I) ^ h := by simp

end Erdos624.Disproof

/- Source module Erdos624.BranchCandidates. -/

namespace Erdos624.Disproof

open Finset

variable {I : Type*} [LinearOrder I]

def sourceTail (Y : Finset I) (x : I) : Finset I := Y.filter fun z => x < z

theorem sourceTail_subset (Y : Finset I) (x : I) : sourceTail Y x ⊆ Y :=
  Finset.filter_subset _ _

theorem sourceTail_gt (Y : Finset I) (x z : I) (hz : z ∈ sourceTail Y x) : x < z :=
  (Finset.mem_filter.mp hz).2

/-- The first J points each leave a suffix with at least card(Y) - J points. -/
theorem exists_branch_candidates (Y : Finset I) (J : ℕ) (hJ : J ≤ Y.card) :
    ∃ P : Finset I, P ⊆ Y ∧ P.card = J ∧
      ∀ x ∈ P, Y.card - J ≤ (sourceTail Y x).card := by
  let e := Y.orderEmbOfFin rfl
  let first : Fin J ↪ I :=
    ⟨fun i => e ⟨i.val, lt_of_lt_of_le i.isLt hJ⟩,
      fun i j hij => Fin.ext (congrArg (fun v : Fin Y.card => v.val) (e.injective hij))⟩
  let rest : Fin (Y.card - J) ↪ I :=
    ⟨fun i => e ⟨J + i.val, by omega⟩,
      fun i j hij => Fin.ext
        (Nat.add_left_cancel (congrArg (fun v : Fin Y.card => v.val) (e.injective hij)))⟩
  let P := Finset.univ.map first
  let R := Finset.univ.map rest
  have hPcard : P.card = J := by simp [P]
  have hRcard : R.card = Y.card - J := by simp [R]
  have hPY : P ⊆ Y := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact Y.orderEmbOfFin_mem rfl _
  have hRtail (x : I) (hx : x ∈ P) : R ⊆ sourceTail Y x := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    intro z hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Y.orderEmbOfFin_mem rfl _, ?_⟩
    apply e.strictMono
    change i.val < J + j.val
    omega
  refine ⟨P, hPY, hPcard, fun x hx => ?_⟩
  rw [← hRcard]
  exact Finset.card_le_card (hRtail x hx)

end Erdos624.Disproof

/- Source module Erdos624.OuterSystems. -/

namespace Erdos624.Disproof

open Finset Module

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- Outer labels can be chosen so that every source has a good minimum branch. -/
theorem exists_good_outer_system (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    (hcard : Fintype.card I = 2 ^ (100 * k))
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] OuterField k × OuterField k)] :
    ∃ outer : I → ((I → ZMod 2) →ₗ[ZMod 2] OuterField k × OuterField k),
      ∀ Y : Finset I, Y.card = 100 * k + 1217 →
        ∃ x ∈ Y, 100 * k + 17 ≤ (sourceTail Y x).card ∧
          finrank (ZMod 2) (coordinateSpace (sourceTail Y x) ⊓ LinearMap.ker (outer x) :
            Submodule (ZMod 2) (I → ZMod 2)) ≤ k := by
  letI : CommRing (ZMod 2) := ZMod.commRing 2
  letI : Ring (ZMod 2) := (ZMod.commRing 2).toRing
  letI : Semiring (ZMod 2) := (ZMod.commRing 2).toSemiring
  letI : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
  letI : AddCommMonoid (ZMod 2) := (ZMod.commRing 2).toAddCommMonoid
  classical
  let H := 100 * k + 1217
  let Ω := (I → ZMod 2) →ₗ[ZMod 2] OuterField k × OuterField k
  let sources := (Finset.univ : Finset I).powersetCard H
  let YType := sources
  have hYcard (Y : YType) : Y.val.card = H := (Finset.mem_powersetCard.mp Y.property).2
  have hchoose (Y : YType) : ∃ P : Finset I, P ⊆ Y.val ∧ P.card = 1200 ∧
      ∀ x ∈ P, Y.val.card - 1200 ≤ (sourceTail Y.val x).card :=
    exists_branch_candidates Y.val 1200 (by rw [hYcard Y]; dsimp [H]; omega)
  let candidates (Y : YType) := Classical.choose (hchoose Y)
  have hcandidates (Y : YType) := Classical.choose_spec (hchoose Y)
  have hPcard (Y : YType) : (candidates Y).card = 1200 := (hcandidates Y).2.1
  let bad (Y : YType) (x : I) : Finset Ω :=
    if x ∈ candidates Y then
      mapsWithLargeRestrictedKernel (W := OuterField k × OuterField k)
        (coordinateSpace (sourceTail Y.val x)) (k + 1)
    else Finset.univ
  let p : ℝ := ((2 : ℝ) ^ (10 * k * k))⁻¹
  have hproduct (Y : YType) :
      (∏ x : I, ∑ f ∈ bad Y x, uniformWeight Ω f) ≤ p ^ 1200 := by
    have hnonneg (x : I) : 0 ≤ ∑ f ∈ bad Y x, uniformWeight Ω f :=
      Finset.sum_nonneg fun f _ => uniformWeight_nonneg Ω f
    have hle (x : I) : (∑ f ∈ bad Y x, uniformWeight Ω f) ≤ 1 := by
      calc
        (∑ f ∈ bad Y x, uniformWeight Ω f) ≤ ∑ f : Ω, uniformWeight Ω f :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => uniformWeight_nonneg Ω f)
        _ = 1 := uniformWeight_total Ω
    have hlocal (x : I) (hx : x ∈ candidates Y) :
        (∑ f ∈ bad Y x, uniformWeight Ω f) ≤ p := by
      dsimp only [bad]
      rw [if_pos hx]
      apply bad_source_small (I := I) k hk
      exact (Finset.card_le_card (sourceTail_subset Y.val x)).trans_eq (hYcard Y)
    calc
      (∏ x : I, ∑ f ∈ bad Y x, uniformWeight Ω f) ≤ ∏ _x ∈ candidates Y, p :=
        omaProdMonoSubset (Finset.subset_univ _)
          (fun x _ => hnonneg x) hlocal (fun x _ _ => hle x)
      _ = p ^ 1200 := by simp only [Finset.prod_const, hPcard Y]
  have hsourceCount : Fintype.card YType ≤ (Fintype.card I) ^ H := by
    simpa only [YType, sources, Fintype.card_coe] using exact_sources_card_le (I := I) H
  have hppos : 0 ≤ p ^ 1200 := by positivity
  have hpPower : p ^ 1200 = ((2 : ℝ) ^ (1200 * (10 * k * k)))⁻¹ := by
    dsimp only [p]
    rw [inv_pow, ← pow_mul, Nat.mul_comm]
  have hnumber : (((Fintype.card I) ^ H : ℕ) : ℝ) =
      (2 : ℝ) ^ (100 * k * (100 * k + 1217)) := by
    rw [hcard, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  have hsmall : (Fintype.card YType : ℝ) * p ^ 1200 < 1 := by
    have hsourceReal : (Fintype.card YType : ℝ) ≤ (((Fintype.card I) ^ H : ℕ) : ℝ) := by
      exact_mod_cast hsourceCount
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsourceReal hppos)
    rw [hnumber, hpPower, ← div_eq_mul_inv]
    apply (div_lt_one (by positivity)).mpr
    exact pow_lt_pow_right₀ (by norm_num) (outer_union_exponent k hk)
  have hsum : (∑ Y : YType, ∏ x : I, ∑ f ∈ bad Y x, uniformWeight Ω f) < 1 := by
    apply lt_of_le_of_lt (Finset.sum_le_sum (fun Y _ => hproduct Y))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsmall
  obtain ⟨outer, houter⟩ := exists_simultaneous_coordinate_success
    (fun (_x : I) (f : Ω) => uniformWeight Ω f)
    (fun _ f => uniformWeight_nonneg Ω f) (fun _ => uniformWeight_total Ω) bad hsum
  refine ⟨outer, ?_⟩
  intro Y hY
  let Y' : YType := ⟨Y, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hY⟩⟩
  obtain ⟨x, hx⟩ := houter Y'
  have hxc : x ∈ candidates Y' := by
    by_contra hnot
    simp [bad, hnot] at hx
  have hnot : ¬ k + 1 ≤ finrank (ZMod 2)
      (LinearMap.ker ((outer x).comp (coordinateSpace (sourceTail Y x)).subtype)) := by
    simpa [bad, hxc, mapsWithLargeRestrictedKernel] using hx
  refine ⟨x, (hcandidates Y').1 hxc, ?_, ?_⟩
  · have htail := (hcandidates Y').2.2 x hxc
    change Y.card - 1200 ≤ (sourceTail Y x).card at htail
    rw [hY] at htail
    omega
  · rw [finrank_inf_ker]
    omega

end Erdos624.Disproof

/- Source module Erdos624.InnerSystems. -/

namespace Erdos624.Disproof

open Finset Module

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- For fixed outer labels, one inner system makes every relevant repair list small. -/
theorem exists_bounded_inner_system (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    (hcard : Fintype.card I = 2 ^ (100 * k))
    [Fintype ((I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k)]
    (outer : (I → ZMod 2) →ₗ[ZMod 2] OuterField k × OuterField k) :
    ∃ inner : OuterField k → ((I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k),
      ∀ B : Finset I, B.card ≤ 100 * k + 1217 →
        (firstRepairList (labelsFromPairs outer inner) B k).card ≤ (10000 * k) * 2 ^ (40 * k) ∧
        (secondRepairList (labelsFromPairs outer inner) B k).card ≤ (10000 * k) * 2 ^ k := by
  classical
  let H := 100 * k + 1217
  let Ω := (I → ZMod 2) →ₗ[ZMod 2] InnerField k × InnerField k
  let masks := smallMasks (I := I) H
  let R := Fin 2 × masks
  let K (B : Finset I) :=
    (coordinateSpace B ⊓ LinearMap.ker outer : Submodule (ZMod 2) (I → ZMod 2))
  let events (r : R) (a : OuterField k) : Finset Ω :=
    if r.1 = 0 then
      if finrank (ZMod 2) (K r.2.val) ≤ k ∧ r.2.val.card ≤ 75 * k + 1 then
        firstGroupEvent (G := InnerField k) outer r.2.val k a else ∅
    else if finrank (ZMod 2) (K r.2.val) ≤ k then
      secondGroupEvent (G := InnerField k) (K r.2.val) else ∅
  have hprob (r : R) :
      (∑ a : OuterField k, ∑ f ∈ events r a, uniformWeight Ω f) ≤ ((2 : ℝ) ^ (3 * k))⁻¹ := by
    rcases r with ⟨i, B⟩
    fin_cases i
    · by_cases h : finrank (ZMod 2) (K B.val) ≤ k ∧ B.val.card ≤ 75 * k + 1
      · simpa [events, h] using first_group_sum_small k hk outer B.val h.2 h.1
      · simp [events, h]
    · by_cases h : finrank (ZMod 2) (K B.val) ≤ k
      · simpa [events, h] using second_group_sum_small k hk (K B.val) h
      · simp [events, h]
  have hmaskCount : masks.card ≤ (100 * k + 1218) * ((2 : ℕ) ^ (100 * k)) ^ (100 * k + 1217) := by
    simpa [masks, H, hcard] using smallMasks_card_le (I := I) H (by rw [hcard]; positivity)
  have hRcard : Fintype.card R = 2 * masks.card := by
    simp [R, Fintype.card_prod, Fintype.card_coe]
  have hbudget : (Fintype.card R : ℝ) *
      (Real.exp 1 / ((2 : ℝ) ^ (3 * k)) ^ (10000 * k)) < 1 := by
    rw [hRcard]
    exact inner_union_budget k masks.card hk hmaskCount
  obtain ⟨inner, hcounts⟩ := exists_uniformly_few_events
    (fun (_a : OuterField k) (f : Ω) => uniformWeight Ω f)
    (fun _ f => uniformWeight_nonneg Ω f) (fun _ => uniformWeight_total Ω)
    events (10000 * k) ((2 : ℝ) ^ (3 * k)) (one_le_pow₀ (by norm_num)) hprob hbudget
  refine ⟨inner, ?_⟩
  intro B hB
  let B' : masks := ⟨B, (mem_smallMasks H B).mpr hB⟩
  by_cases hgood : finrank (ZMod 2) (K B) ≤ k
  · have hgoodL : goodOuter (labelsFromPairs outer inner) B k :=
      (goodOuter_labelsFromPairs outer inner B k).mpr hgood
    have hsecondEvents : events (1, B') =
        (fun _a : OuterField k => secondGroupEvent (G := InnerField k) (K B)) := by
      funext a
      simp [events, B', hgood]
    have hsecond := hcounts (1, B')
    rw [hsecondEvents] at hsecond
    have hsecondGroups : ((secondRepairList (labelsFromPairs outer inner) B k).image Prod.fst).card ≤
        10000 * k := (secondRepairList_groups_count outer inner B k).trans hsecond.le
    refine ⟨?_, secondRepairList_card_le (labelsFromPairs outer inner) B k (10000 * k)
      hgoodL hsecondGroups⟩
    by_cases hfirstSize : B.card ≤ 75 * k + 1
    · have hfirstEvents : events (0, B') =
          (fun a : OuterField k => firstGroupEvent (G := InnerField k) outer B k a) := by
        funext a
        simp [events, B', hgood, hfirstSize]
      have hfirst := hcounts (0, B')
      rw [hfirstEvents, ← firstRepairGroups_count] at hfirst
      have hbound := firstRepairList_card_le (labelsFromPairs outer inner) B k (10000 * k) hfirst.le
      simpa only [innerField_card k (by omega)] using hbound
    · simp [firstRepairList, hfirstSize]
  · have hnotgood : ¬goodOuter (labelsFromPairs outer inner) B k := by
      simpa only [goodOuter_labelsFromPairs] using hgood
    simp [firstRepairList, secondRepairList, hnotgood]

end Erdos624.Disproof

/- Source module Erdos624.RepairBounds. -/

namespace Erdos624.Disproof

theorem exponential_dominates_linear (k : ℕ) (hk : 16 ≤ k) :
    40000 * k ≤ (2 : ℕ) ^ (3 * k) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpow : (2 : ℕ) ^ (3 * (n + 1)) = 8 * 2 ^ (3 * n) := by
      rw [show 3 * (n + 1) = 3 * n + 3 by omega, pow_add]
      norm_num
      omega
    rw [hpow]
    nlinarith

theorem exponential_dominates_quadratic (k : ℕ) (hk : 32 ≤ k) :
    40000 * k * k ≤ (2 : ℕ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

theorem first_repair_trials (k N : ℕ) (hk : 2000 ≤ k)
    (hN : (2 : ℕ) ^ (44 * k) ≤ 2 * N) :
    (2 * (10000 * k) * 2 ^ (40 * k)) * 2 ^ k ≤ N := by
  have hg := exponential_dominates_linear k (by omega)
  have hmul := Nat.mul_le_mul_right ((2 : ℕ) ^ (41 * k)) hg
  have hpow : (2 : ℕ) ^ (3 * k) * 2 ^ (41 * k) = 2 ^ (44 * k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hmul
  have hfactor : 2 * ((2 * (10000 * k) * (2 : ℕ) ^ (40 * k)) * 2 ^ k) =
      40000 * k * 2 ^ (41 * k) := by
    rw [show 41 * k = 40 * k + k by omega, pow_add]
    ring
  rw [← hfactor] at hmul
  omega

theorem second_repair_trials (k N : ℕ) (hk : 2000 ≤ k)
    (hN : (2 : ℕ) ^ (8 * k) ≤ 2 * N) :
    (2 * (10000 * k) * 2 ^ k) * 2 ^ k ≤ N := by
  have hg := exponential_dominates_linear k (by omega)
  have hmul := Nat.mul_le_mul_right ((2 : ℕ) ^ (2 * k)) hg
  have hpow : (2 : ℕ) ^ (3 * k) * 2 ^ (2 * k) = 2 ^ (5 * k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hmul
  have h58 : (2 : ℕ) ^ (5 * k) ≤ 2 ^ (8 * k) := Nat.pow_le_pow_right (by decide) (by omega)
  have hfactor : 2 * ((2 * (10000 * k) * (2 : ℕ) ^ k) * 2 ^ k) =
      40000 * k * 2 ^ (2 * k) := by
    rw [show 2 * k = k + k by omega, pow_add]
    ring
  rw [← hfactor] at hmul
  omega

theorem first_repair_expectation (k N : ℕ) (hk : 2000 ≤ k)
    (hN : (2 : ℕ) ^ (44 * k) ≤ 2 * N) :
    (2 : ℝ) ^ k ≤ (2 * (10000 * k) * ((2 : ℝ) ^ (40 * k)))⁻¹ * N := by
  have hkpos : 0 < k := by omega
  apply (le_inv_mul_iff₀ (by positivity)).mpr
  exact_mod_cast first_repair_trials k N hk hN

theorem second_repair_expectation (k N : ℕ) (hk : 2000 ≤ k)
    (hN : (2 : ℕ) ^ (8 * k) ≤ 2 * N) :
    (2 : ℝ) ^ k ≤ (2 * (10000 * k) * ((2 : ℝ) ^ k))⁻¹ * N := by
  have hkpos : 0 < k := by omega
  apply (le_inv_mul_iff₀ (by positivity)).mpr
  exact_mod_cast second_repair_trials k N hk hN

theorem repair_request_count_bound (k n : ℕ) (hk : 2000 ≤ k)
    (hn : n ≤ (100 * k + 1218) * ((2 : ℕ) ^ (100 * k)) ^ (100 * k + 1217) * 2 ^ (100 * k)) :
    n ≤ (2 : ℕ) ^ (20000 * k * k) := by
  have hbase := Nat.mul_le_mul_right ((2 : ℕ) ^ (100 * k)) (small_mask_factor_bound k hk)
  have hmul := Nat.mul_le_mul_right k hk
  apply hn.trans (hbase.trans ?_)
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

theorem repair_union_budget (k n : ℕ) (hk : 2000 ≤ k) (hn : n ≤ (2 : ℕ) ^ (20000 * k * k)) :
    (n : ℝ) * Real.exp (-(2 : ℝ) ^ k) < 1 := by
  let M := 20000 * k * k
  have hlarge : (M : ℝ) < (2 : ℝ) ^ k := by
    have h := exponential_dominates_quadratic k (by omega)
    have hc : ((40000 * k * k : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast h
    dsimp [M]
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    push_cast at hc ⊢
    nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpow : (2 : ℝ) ^ M ≤ Real.exp (M : ℝ) := by
    calc
      (2 : ℝ) ^ M ≤ (Real.exp 1) ^ M := pow_le_pow_left₀ (by norm_num) htwo M
      _ = Real.exp (M : ℝ) := by rw [← Real.exp_nat_mul]; simp
  have hn' : (n : ℝ) ≤ Real.exp (M : ℝ) := by
    apply le_trans _ hpow
    exact_mod_cast hn
  calc
    (n : ℝ) * Real.exp (-(2 : ℝ) ^ k) ≤ Real.exp (M : ℝ) * Real.exp (-(2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hn' (Real.exp_nonneg _)
    _ = Real.exp ((M : ℝ) - (2 : ℝ) ^ k) := by rw [← Real.exp_add, sub_eq_add_neg]
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

end Erdos624.Disproof

/- Source module Erdos624.SourceClassification. -/

namespace Erdos624.Disproof

open Module Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def evenWitness {F G : Type*} [Field F] [Field G] [Algebra (ZMod 2) F] [Algebra (ZMod 2) G]
    (L : BranchLabels I F G) (Y : Finset I) (c : F × G) : Prop :=
  ∃ A ⊆ Y, A.card % 2 = 0 ∧ L.ratioColour (indicatorVector A) = c

/-- Local source vectors give global masks and subspaces with the required support bounds. -/
theorem source_classification (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    (L : BranchLabels I (OuterField k) (InnerField k)) (Y : Finset I)
    (hYlow : 100 * k + 17 ≤ Y.card) (hYup : Y.card ≤ 100 * k + 1217)
    (a : OuterField k) (b : InnerField k) :
    evenWitness L Y (a, b) ∨
      (∃ A ⊆ Y, A.card ≤ 53 * k ∧ innerMarker L a A) ∨
      (∃ D : Submodule (ZMod 2) (I → ZMod 2),
        subspaceSupport D ⊆ Y ∧ (subspaceSupport D).card ≤ 91 * k ∧ outerMarker L a b D) := by
  classical
  let L' := L.restrict Y
  have hkpos : 0 < k := by omega
  have hdim : 1 + finrank (ZMod 2) (OuterField k) + finrank (ZMod 2) (InnerField k) + 16 ≤
      Fintype.card Y := by
    rw [outerField_finrank k hkpos, innerField_finrank k hkpos, Fintype.card_coe]
    omega
  rcases L'.classification a b hdim with he | hi | ho
  · obtain ⟨w, hw, hcolour⟩ := he
    let A := vectorSupport (extendByZero Y w)
    have hAY : A ⊆ Y := mem_coordinateSpace_iff.mp ⟨w, rfl⟩
    have hconstraints := (L'.mem_constraintKernel a b w).mp hw
    have hparity : A.card % 2 = 0 := by
      dsimp [A]
      rw [card_support_extendByZero]
      exact (parityMap_eq_zero_iff w).mp hconstraints.1
    refine Or.inl ⟨A, hAY, hparity, ?_⟩
    dsimp [A]
    rw [indicatorVector_vectorSupport, ← L.ratioColour_restrict Y w]
    exact hcolour
  · obtain ⟨w, hw, hwne, hV, hsize⟩ := hi
    let v := extendByZero Y w
    let A := vectorSupport v
    have hvne : v ≠ 0 := by
      intro h
      apply hwne
      apply extendByZero_injective Y
      simpa [v] using h
    have hAY : A ⊆ Y := mem_coordinateSpace_iff.mp ⟨w, rfl⟩
    have hconstraints := (L'.mem_constraintKernel a b w).mp hw
    have hparity : A.card % 2 = 0 := by
      dsimp [A, v]
      rw [card_support_extendByZero]
      exact (parityMap_eq_zero_iff w).mp hconstraints.1
    have hAsize : A.card ≤ 53 * k := by
      apply inner_marker_size k Y.card A.card hk hYup
      simpa only [A, v, card_support_extendByZero, Fintype.card_coe] using hsize
    refine Or.inr (Or.inl ⟨A, hAY, hAsize, ?_⟩)
    refine ⟨(vectorSupport_nonempty_iff v).mpr hvne, hparity, ?_, ?_, ?_⟩
    · dsimp [A]
      rw [indicatorVector_vectorSupport]
      exact hconstraints.2.1
    · dsimp [A]
      rw [indicatorVector_vectorSupport]
      have hU := hconstraints.2.2
      rw [hV, mul_zero] at hU
      exact hU
    · dsimp [A]
      rw [indicatorVector_vectorSupport]
      exact hV
  · obtain ⟨D₀, hDker, hDdim, hDsmall, hDzero, w, hw, hV⟩ := ho
    let D := D₀.map (extendByZero Y)
    have hDY : subspaceSupport D ⊆ Y := by
      apply subspaceSupport_subset_of_le_coordinateSpace
      rintro v ⟨z, _, rfl⟩
      exact ⟨z, rfl⟩
    have hDsize : (subspaceSupport D).card ≤ 91 * k := by
      apply outer_marker_size k Y.card (subspaceSupport D).card hk hYup
      simpa only [D, card_subspaceSupport_map_extendByZero, Fintype.card_coe] using hDsmall
    refine Or.inr (Or.inr ⟨D, hDY, hDsize, ?_⟩)
    refine ⟨?_, ?_, extendByZero Y w, Submodule.mem_map.mpr ⟨w, hw, rfl⟩, hV⟩
    · rw [finrank_map_extendByZero]
      exact hDdim
    · rintro v ⟨z, hz, rfl⟩
      have hconstraints := (L'.mem_constraintKernel a b z).mp (hDker hz)
      exact ⟨(hDzero z hz).1, (hDzero z hz).2, hconstraints.2.2⟩

end Erdos624.Disproof

/- Source module Erdos624.TrialFamilies. -/

namespace Erdos624.Disproof

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def repairWeight (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (L : BranchLabels I (OuterField k) (InnerField k))
    (B : Finset I) (c : OuterField k × InnerField k) : ℝ := by
  classical
  exact twoListWeight (0, 0) (firstRepairList L B k) (secondRepairList L B k) c

theorem repairWeight_nonneg (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (L : BranchLabels I (OuterField k) (InnerField k))
    (B : Finset I) (c : OuterField k × InnerField k) : 0 ≤ repairWeight k L B c := by
  classical
  exact twoListWeight_nonneg _ _ _ _

theorem repairWeight_total (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (L : BranchLabels I (OuterField k) (InnerField k)) (B : Finset I) :
    ∑ c, repairWeight k L B c = 1 := by
  classical
  exact twoListWeight_total _ _ _

/-- Every color missed by the ratio rule has a family of sufficiently many repair trials. -/
theorem exists_repair_trials (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    (L : BranchLabels I (OuterField k) (InnerField k))
    (hbounded : ∀ B : Finset I, B.card ≤ 100 * k + 1217 →
      (firstRepairList L B k).card ≤ (10000 * k) * 2 ^ (40 * k) ∧
      (secondRepairList L B k).card ≤ (10000 * k) * 2 ^ k)
    (Y : Finset I) (hYlow : 100 * k + 17 ≤ Y.card) (hYup : Y.card ≤ 100 * k + 1217)
    (hgood : goodOuter L Y k) (a : OuterField k) (b : InnerField k)
    (hmiss : ¬evenWitness L Y (a, b)) :
    ∃ T : Finset (Finset I), ∃ p : ℝ,
      (∀ B ∈ T, B ⊆ Y ∧ B.card % 2 = 1 ∧ p ≤ repairWeight k L B (a, b)) ∧
      (2 : ℝ) ^ k ≤ p * T.card := by
  classical
  rcases source_classification k hk L Y hYlow hYup a b with he | hi | ho
  · exact False.elim (hmiss he)
  · obtain ⟨A, hAY, hAsize, hmarker⟩ := hi
    have hparams := inner_extension_parameters k Y.card A.card hYlow hAsize
    obtain ⟨T, hT, hcount⟩ := exists_many_odd_extensions A Y hAY (22 * k) hparams.1
    let p : ℝ := (2 * (10000 * k) * (2 : ℝ) ^ (40 * k))⁻¹
    refine ⟨T, p, ?_, ?_⟩
    · intro B hB
      obtain ⟨hAB, hBY, hBsize, hBodd⟩ := hT B hB
      have hBfirst : B.card ≤ 75 * k + 1 := hBsize.trans hparams.2
      have hBup : B.card ≤ 100 * k + 1217 := (Finset.card_le_card hBY).trans hYup
      have hc := firstRepairList_mem L B A k a b (goodOuter_mono L hBY hgood)
        hBodd hBfirst hAB hAsize hmarker
      refine ⟨hBY, hBodd, ?_⟩
      have hweight := twoListWeight_ge_left (0, 0) (firstRepairList L B k) (secondRepairList L B k)
        (a, b) hc ((10000 * k) * 2 ^ (40 * k)) (hbounded B hBup).1
      simpa only [repairWeight, p, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hweight
    · have hc : (2 : ℕ) ^ (44 * k) ≤ 2 * T.card := by
        simpa only [show 2 * (22 * k) = 44 * k by omega] using hcount
      exact first_repair_expectation k T.card hk hc
  · obtain ⟨D, hDY, hDsize, hmarker⟩ := ho
    let C := subspaceSupport D
    have hparams := outer_extension_parameters k Y.card C.card hYlow hDsize
    obtain ⟨T, hT, hcount⟩ := exists_many_odd_extensions C Y hDY (4 * k) hparams.1
    let p : ℝ := (2 * (10000 * k) * (2 : ℝ) ^ k)⁻¹
    refine ⟨T, p, ?_, ?_⟩
    · intro B hB
      obtain ⟨hCB, hBY, _, hBodd⟩ := hT B hB
      have hBup : B.card ≤ 100 * k + 1217 := (Finset.card_le_card hBY).trans hYup
      have hc := secondRepairList_mem L B k a b (goodOuter_mono L hBY hgood)
        hBodd hBup D hCB hDsize hmarker
      refine ⟨hBY, hBodd, ?_⟩
      have hweight := twoListWeight_ge_right (0, 0) (firstRepairList L B k) (secondRepairList L B k)
        (a, b) hc ((10000 * k) * 2 ^ k) (hbounded B hBup).2
      simpa only [repairWeight, p, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hweight
    · have hc : (2 : ℕ) ^ (8 * k) ≤ 2 * T.card := by
        simpa only [show 2 * (4 * k) = 8 * k by omega] using hcount
      exact second_repair_expectation k T.card hk hc

end Erdos624.Disproof

/- Source module Erdos624.RepairSelection. -/

namespace Erdos624.Disproof

open Finset

theorem exists_hitting_assignment {J C R : Type*} [Fintype J] [DecidableEq J]
    [Fintype C] [DecidableEq C] [Fintype R]
    (w : J → C → ℝ) (hw : ∀ j c, 0 ≤ w j c) (htotal : ∀ j, ∑ c, w j c = 1)
    (trials : R → Finset J) (target : R → C) (p : R → ℝ) (E : ℝ) (hE : 0 < E)
    (htrial : ∀ r j, j ∈ trials r → p r ≤ w j (target r))
    (hexpect : ∀ r, E ≤ p r * (trials r).card)
    (hbudget : (Fintype.card R : ℝ) * Real.exp (-E) < 1) :
    ∃ choice : J → C, ∀ r, ∃ j ∈ trials r, choice j = target r := by
  classical
  let bad (r : R) (j : J) : Finset C :=
    if j ∈ trials r then Finset.univ.erase (target r) else Finset.univ
  have hweight_le_one (j : J) (c : C) : w j c ≤ 1 := by
    rw [← htotal j]
    exact Finset.single_le_sum (fun d _ => hw j d) (Finset.mem_univ c)
  have hp (r : R) : p r ≤ 1 := by
    have hcard : 0 < (trials r).card := by
      by_contra hn
      have hzero : (trials r).card = 0 := by omega
      have he := hexpect r
      rw [hzero, Nat.cast_zero, mul_zero] at he
      linarith
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
    exact (htrial r j hj).trans (hweight_le_one j (target r))
  have hmiss (r : R) (j : J) (hj : j ∈ trials r) :
      ∑ c ∈ bad r j, w j c ≤ 1 - p r := by
    have hsum := Finset.sum_erase_add Finset.univ (w j) (Finset.mem_univ (target r))
    rw [htotal j] at hsum
    simp only [bad, hj, ↓reduceIte]
    linarith [htrial r j hj]
  have hprob (r : R) : (∏ j, ∑ c ∈ bad r j, w j c) ≤ Real.exp (-E) := by
    rw [← restricted_product_weight w (bad r)]
    apply (independent_miss_weight_le w hw htotal (bad r) (trials r) (p r) (hp r) (hmiss r)).trans
    exact Real.exp_le_exp.mpr (by linarith [hexpect r])
  have hsum : (∑ r, ∏ j, ∑ c ∈ bad r j, w j c) < 1 := by
    apply lt_of_le_of_lt (Finset.sum_le_sum (fun r _ => hprob r))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hbudget
  obtain ⟨choice, hchoice⟩ := exists_simultaneous_coordinate_success w hw htotal bad hsum
  refine ⟨choice, ?_⟩
  intro r
  obtain ⟨j, hj⟩ := hchoice r
  have hmem : j ∈ trials r := by
    by_contra hnot
    simp [bad, hnot] at hj
  refine ⟨j, hmem, ?_⟩
  simpa [bad, hmem] using hj

end Erdos624.Disproof

/- Source module Erdos624.RepairSystems. -/

namespace Erdos624.Disproof

open Finset Module

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def branchColour (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (L : BranchLabels I (OuterField k) (InnerField k))
    (choice : Finset I → OuterField k × InnerField k) (B : Finset I) : OuterField k × InnerField k :=
  if B.card % 2 = 0 then L.ratioColour (indicatorVector B) else choice B

/-- The odd-mask assignment can serve every good source and every color simultaneously. -/
theorem exists_covering_branch (k : ℕ) [Fintype (OuterField k)] [Fintype (InnerField k)] (hk : 2000 ≤ k)
    (hcard : Fintype.card I = 2 ^ (100 * k))
    (L : BranchLabels I (OuterField k) (InnerField k))
    (hbounded : ∀ B : Finset I, B.card ≤ 100 * k + 1217 →
      (firstRepairList L B k).card ≤ (10000 * k) * 2 ^ (40 * k) ∧
      (secondRepairList L B k).card ≤ (10000 * k) * 2 ^ k) :
    ∃ f : Finset I → OuterField k × InnerField k,
      ∀ Y : Finset I, 100 * k + 17 ≤ Y.card → Y.card ≤ 100 * k + 1217 →
        goodOuter L Y k → ∀ c, ∃ A ⊆ Y, f A = c := by
  classical
  let H := 100 * k + 1217
  let sources := smallMasks (I := I) H
  let Full := sources × (OuterField k × InnerField k)
  let R := {r : Full // 100 * k + 17 ≤ r.1.val.card ∧
    goodOuter L r.1.val k ∧ ¬evenWitness L r.1.val r.2}
  have hcount : Fintype.card R ≤ sources.card * Fintype.card (OuterField k × InnerField k) := by
    have h := Fintype.card_le_of_injective (fun r : R => r.val) Subtype.val_injective
    simpa only [Full, Fintype.card_prod, Fintype.card_coe] using h
  have hsources : sources.card ≤ (H + 1) * (Fintype.card I) ^ H :=
    smallMasks_card_le H (by rw [hcard]; positivity)
  have hcount' : Fintype.card R ≤ (100 * k + 1218) *
      ((2 : ℕ) ^ (100 * k)) ^ (100 * k + 1217) * 2 ^ (100 * k) := by
    apply hcount.trans
    rw [palette_card k (by omega)]
    simpa only [H, hcard, Nat.add_assoc] using Nat.mul_le_mul_right (2 ^ (100 * k)) hsources
  have hbudget : (Fintype.card R : ℝ) * Real.exp (-(2 : ℝ) ^ k) < 1 :=
    repair_union_budget k (Fintype.card R) hk (repair_request_count_bound k (Fintype.card R) hk hcount')
  have hrequest (r : R) : ∃ T : Finset (Finset I), ∃ p : ℝ,
      (∀ B ∈ T, B ⊆ r.val.1.val ∧ B.card % 2 = 1 ∧ p ≤ repairWeight k L B r.val.2) ∧
      (2 : ℝ) ^ k ≤ p * T.card := by
    have hYup : r.val.1.val.card ≤ 100 * k + 1217 := (mem_smallMasks H r.val.1.val).mp r.val.1.property
    exact exists_repair_trials k hk L hbounded r.val.1.val r.property.1 hYup r.property.2.1
      r.val.2.1 r.val.2.2 r.property.2.2
  let trials (r : R) := Classical.choose (hrequest r)
  let p (r : R) := Classical.choose (Classical.choose_spec (hrequest r))
  have hspec (r : R) := Classical.choose_spec (Classical.choose_spec (hrequest r))
  obtain ⟨choice, hchoice⟩ := exists_hitting_assignment (repairWeight k L)
    (repairWeight_nonneg k L) (repairWeight_total k L) trials (fun r : R => r.val.2) p
    ((2 : ℝ) ^ k) (by positivity) (fun r B hB => ((hspec r).1 B hB).2.2)
    (fun r => (hspec r).2) hbudget
  refine ⟨branchColour k L choice, ?_⟩
  intro Y hYlow hYup hgood c
  by_cases heven : evenWitness L Y c
  · obtain ⟨A, hAY, hAeven, hAc⟩ := heven
    exact ⟨A, hAY, by simpa only [branchColour, hAeven, ↓reduceIte] using hAc⟩
  · let Y' : sources := ⟨Y, (mem_smallMasks H Y).mpr hYup⟩
    let r : R := ⟨(Y', c), hYlow, hgood, heven⟩
    obtain ⟨B, hB, hBc⟩ := hchoice r
    have hproperties := (hspec r).1 B hB
    have hodd : B.card % 2 ≠ 0 := by have := hproperties.2.1; omega
    exact ⟨B, hproperties.1, by simpa only [branchColour, hodd, ↓reduceIte] using hBc⟩

end Erdos624.Disproof

/- Source module Erdos624.Construction. -/

namespace Erdos624.Disproof

open Finset

/-- The constant-gap coloring constructed from the outer, inner, and repair choices. -/
theorem constant_gap_colouring (k : ℕ) (hk : 2000 ≤ k) :
    ∃ f : Finset (Fin (2 ^ (100 * k))) → Fin (2 ^ (100 * k)), Covers f (100 * k + 1217) := by
  classical
  letI : Fintype (OuterField k) := outerFieldFintype k
  letI : Fintype (InnerField k) := innerFieldFintype k
  let I := Fin (2 ^ (100 * k))
  let V := I → ZMod 2
  let O := V →ₗ[ZMod 2] OuterField k × OuterField k
  let J := V →ₗ[ZMod 2] InnerField k × InnerField k
  let : Fintype O := Fintype.ofInjective (fun f : O => (f : V → OuterField k × OuterField k))
    DFunLike.coe_injective
  let : Fintype J := Fintype.ofInjective (fun f : J => (f : V → InnerField k × InnerField k))
    DFunLike.coe_injective
  have hcard : Fintype.card I = 2 ^ (100 * k) := Fintype.card_fin _
  obtain ⟨outer, houter⟩ := exists_good_outer_system (I := I) k hk hcard
  have hinner (x : I) := exists_bounded_inner_system (I := I) k hk hcard (outer x)
  let inner (x : I) := Classical.choose (hinner x)
  have hbounded (x : I) := Classical.choose_spec (hinner x)
  let labels (x : I) := labelsFromPairs (outer x) (inner x)
  have hbranchExists (x : I) := exists_covering_branch k hk hcard (labels x) (hbounded x)
  let branch (x : I) := Classical.choose (hbranchExists x)
  have hbranch (x : I) := Classical.choose_spec (hbranchExists x)
  have hcover : Covers (assembleColour (0, 0) branch) (100 * k + 1217) := by
    apply assembleColour_covers
    intro Y hY
    obtain ⟨x, hxY, hlow, hgood⟩ := houter Y hY
    refine ⟨x, hxY, ?_⟩
    intro c
    have hupp : (sourceTail Y x).card ≤ 100 * k + 1217 :=
      (Finset.card_le_card (sourceTail_subset Y x)).trans_eq hY
    have hgoodLabels : goodOuter (labels x) (sourceTail Y x) k :=
      (goodOuter_labelsFromPairs (outer x) (inner x) (sourceTail Y x) k).mpr hgood
    obtain ⟨B, hB, hBc⟩ := hbranch x (sourceTail Y x) hlow hupp hgoodLabels c
    exact ⟨B, hB.trans (sourceTail_subset Y x), (fun z hz => sourceTail_gt Y x z (hB hz)), hBc⟩
  have hkpos : 0 < k := by omega
  refine ⟨(paletteEquiv k hkpos) ∘ assembleColour (0, 0) branch, ?_⟩
  exact covers_comp hcover (paletteEquiv k hkpos).surjective

theorem eventual_power_cover : ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 100 ∣ d →
    ∃ f : Finset (Fin (2 ^ d)) → Fin (2 ^ d), Covers f (d + 1217) := by
  refine ⟨200000, ?_⟩
  intro d hd hdiv
  obtain ⟨k, rfl⟩ := hdiv
  exact constant_gap_colouring k (by omega)

/-- A refutation of the exact proposition extracted from the pinned Erdős 624 statement. -/
theorem erdos_624_false : ¬ Erdos624.Statement := by
  unfold Erdos624.Statement
  exact not_tendsto_of_eventual_power_cover 1217 eventual_power_cover

end Erdos624.Disproof

theorem OMA.disproof : ¬ (type_of% @Erdos624.erdos_624) := by
  exact Erdos624.Disproof.erdos_624_false
