import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.Tactic.Group

-- Step Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H1: hypothesis H1 of reduction Erdos1160.erdos_1160.variants.sum.R3.H2.R1
-- Credit: @ahmeterdempmk

/-!
# Step R3.H2.R1.H1 of Erdős Problem 1160 (sum variant)

With kernel `N`, quotient `H` and a fixed lift `action : H → MulAut N` of the outer action,
pairwise inequivalent extensions inject into `H × H → center N`.

This is the classical factor-set argument (Schreier). For each extension pick a section
`s` with `conjAct (s h) = action h`; its factor set `f h k = s h * s k * (s (h * k))⁻¹` lies
in `N` and induces the inner automorphism `action h * action k * (action (h * k))⁻¹`, which
does not depend on the extension. So two factor sets differ by a function into the centre.
Extensions with equal factor sets are equivalent: `inl n * s h ↦ inl' n * s' h` is a
homomorphism compatible with both maps (`GroupExtension.Equiv.ofMonoidHom`).
-/

namespace Erdos1160FactorSets

/-- Conjugating by the image of `n` acts on the kernel as the inner automorphism of `n`. -/
theorem conjAct_inl {N E G : Type*} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G) (n : N) : S.conjAct (S.inl n) = MulAut.conj n := by
  refine MulEquiv.ext fun x => ?_
  apply S.inl_injective
  rw [GroupExtension.inl_conjAct_comm, MulAut.conj_apply, map_mul S.inl, map_mul S.inl,
    map_inv S.inl]

/-- Two extensions of `G` by `N` with sections inducing the same automorphisms of `N` and the
same factor set are equivalent. -/
theorem equiv_of_factor {N G E E' : Type*} [Group N] [Group G] [Group E] [Group E']
    (S : GroupExtension N E G) (S' : GroupExtension N E' G) (s : G → E) (s' : G → E')
    (hs : ∀ g, S.rightHom (s g) = g) (hs' : ∀ g, S'.rightHom (s' g) = g)
    (hc : ∀ g, S.conjAct (s g) = S'.conjAct (s' g)) (f : G → G → N)
    (hf : ∀ a b, S.inl (f a b) = s a * s b * (s (a * b))⁻¹)
    (hf' : ∀ a b, S'.inl (f a b) = s' a * s' b * (s' (a * b))⁻¹) :
    Nonempty (S.Equiv S') := by
  have hmem : ∀ x : E, ∃ n : N, S.inl n = x * (s (S.rightHom x))⁻¹ := by
    intro x
    have hx : x * (s (S.rightHom x))⁻¹ ∈ S.rightHom.ker := by
      rw [MonoidHom.mem_ker, map_mul S.rightHom, map_inv S.rightHom, hs, mul_inv_cancel]
    rw [← S.range_inl_eq_ker_rightHom] at hx
    exact MonoidHom.mem_range.mp hx
  choose ν hν using hmem
  have key : ∀ x y : E, ν (x * y) =
      ν x * S.conjAct (s (S.rightHom x)) (ν y) * f (S.rightHom x) (S.rightHom y) := by
    intro x y
    apply S.inl_injective
    rw [map_mul S.inl, map_mul S.inl, hν (x * y), hν x, hf, S.inl_conjAct_comm, hν y,
      map_mul S.rightHom]
    group
  have hψ : ∀ x y : E, S'.inl (ν (x * y)) * s' (S.rightHom (x * y)) =
      S'.inl (ν x) * s' (S.rightHom x) * (S'.inl (ν y) * s' (S.rightHom y)) := by
    intro x y
    rw [key x y, map_mul S.rightHom, map_mul S'.inl, map_mul S'.inl, hc, S'.inl_conjAct_comm,
      hf']
    group
  have e1 : S.inl (f 1 1) = s 1 := by
    rw [hf, mul_one (1 : G), mul_inv_cancel_right]
  have e1' : S'.inl (f 1 1) = s' 1 := by
    rw [hf', mul_one (1 : G), mul_inv_cancel_right]
  refine ⟨GroupExtension.Equiv.ofMonoidHom
    (MonoidHom.mk' (fun x => S'.inl (ν x) * s' (S.rightHom x)) hψ) ?_ ?_⟩
  · refine MonoidHom.ext fun n => ?_
    show S'.inl (ν (S.inl n)) * s' (S.rightHom (S.inl n)) = S'.inl n
    have e2 : ν (S.inl n) = n * (f 1 1)⁻¹ := by
      apply S.inl_injective
      rw [hν, S.rightHom_inl, map_mul S.inl, map_inv S.inl, e1]
    rw [e2, S.rightHom_inl, map_mul S'.inl, map_inv S'.inl, e1', inv_mul_cancel_right]
  · refine MonoidHom.ext fun x => ?_
    show S'.rightHom (S'.inl (ν x) * s' (S.rightHom x)) = S.rightHom x
    rw [map_mul S'.rightHom, S'.rightHom_inl, one_mul, hs']

end Erdos1160FactorSets

open Erdos1160FactorSets in
theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1.H1 := by
  intro N H I D S action hact hinj
  classical
  -- a section whose conjugation action is exactly `action`
  obtain ⟨s, hs, hc⟩ : ∃ s : ∀ i, H → D i, (∀ i h, (S i).rightHom (s i h) = h) ∧
      (∀ i h, (S i).conjAct (s i h) = action h) := by
    choose e n he hn using hact
    refine ⟨fun i h => (S i).inl (n i h) * e i h, ?_, ?_⟩
    · intro i h
      show (S i).rightHom ((S i).inl (n i h) * e i h) = h
      rw [map_mul (S i).rightHom, GroupExtension.rightHom_inl, one_mul, he]
    · intro i h
      show (S i).conjAct ((S i).inl (n i h) * e i h) = action h
      rw [map_mul (S i).conjAct, conjAct_inl, hn]
  -- its factor set, an element of the kernel
  have hfac : ∀ i a b, ∃ m : N, (S i).inl m = s i a * s i b * (s i (a * b))⁻¹ := by
    intro i a b
    have hm : s i a * s i b * (s i (a * b))⁻¹ ∈ (S i).rightHom.ker := by
      rw [MonoidHom.mem_ker, map_mul (S i).rightHom, map_mul (S i).rightHom,
        map_inv (S i).rightHom, hs, hs, hs, mul_inv_cancel]
    rw [← (S i).range_inl_eq_ker_rightHom] at hm
    exact MonoidHom.mem_range.mp hm
  choose f hf using hfac
  -- the inner automorphism of a factor set does not depend on the extension
  have hconj : ∀ i a b, MulAut.conj (f i a b) = action a * action b * (action (a * b))⁻¹ := by
    intro i a b
    rw [← conjAct_inl (S i), hf, map_mul (S i).conjAct, map_mul (S i).conjAct,
      map_inv (S i).conjAct, hc, hc, hc]
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · exact ⟨Function.Embedding.ofIsEmpty⟩
  · have hcen : ∀ i a b, f i a b * (f i₀ a b)⁻¹ ∈ Subgroup.center N := by
      intro i a b
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : MulAut.conj (f i a b * (f i₀ a b)⁻¹) = 1 := by
        rw [map_mul MulAut.conj, map_inv MulAut.conj, hconj, hconj, mul_inv_cancel]
      have h2 := DFunLike.congr_fun h1 g
      rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    refine ⟨⟨fun i p => ⟨f i p.1 p.2 * (f i₀ p.1 p.2)⁻¹, hcen i p.1 p.2⟩, ?_⟩⟩
    intro i j hij
    apply hinj
    have hfij : ∀ a b, f i a b = f j a b := by
      intro a b
      have h3 : (f i a b * (f i₀ a b)⁻¹ : N) = f j a b * (f i₀ a b)⁻¹ :=
        congrArg Subtype.val (congrFun hij (a, b))
      exact mul_right_cancel h3
    exact equiv_of_factor (S i) (S j) (s i) (s j) (hs i) (hs j)
      (fun g => (hc i g).trans (hc j g).symm) (f i) (hf i)
      (fun a b => by rw [hfij a b]; exact hf j a b)
