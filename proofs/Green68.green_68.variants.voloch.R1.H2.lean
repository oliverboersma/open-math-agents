import OMAReductions.R_Green68_green_68_variants_voloch_R1
import Mathlib

open MvPolynomial Module Submodule Finset

private lemma quad_dim (K : Type) [Field K] :
    Module.finrank K (restrictTotalDegree (Fin 2) K 2) ≤ 6 := by
  classical
  let E := {s : Fin 2 →₀ ℕ // s.sum (fun _ e ↦ e) ≤ 2}
  let T := {v : Fin 3 × Fin 3 // v.1.val + v.2.val ≤ 2}
  have bound (s : E) : s.val 0 + s.val 1 ≤ 2 := by
    have h := s.property
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl), Fin.sum_univ_two] at h
    exact h
  let f (s : E) : T := ⟨(⟨s.val 0,by have := bound s; omega⟩,
    ⟨s.val 1,by have := bound s; omega⟩),bound s⟩
  have inj : Function.Injective f := by
    intro x y he
    have h0 := congrArg (fun z : T ↦ z.val.1.val) he
    have h1 := congrArg (fun z : T ↦ z.val.2.val) he
    apply Subtype.ext
    ext i
    fin_cases i
    · exact h0
    · exact h1
  letI : Finite E := Finite.of_injective f inj
  letI := Fintype.ofFinite E
  let basis : Basis E K (restrictTotalDegree (Fin 2) K 2) :=
    basisRestrictSupport K _
  rw [Module.finrank_eq_card_basis basis]
  exact (Fintype.card_le_of_injective f inj).trans (by decide : Fintype.card T ≤ 6)

theorem OMA.solution : OMA.R_Green68_green_68_variants_voloch_R1.H2 := by
  classical
  intro p _ A hlocal
  let K := ZMod p
  let U := restrictTotalDegree (Fin 2) K 2
  let ev (a : Fin 2 → K) : Module.Dual K U := (aeval a).toLinearMap.comp U.subtype
  let D := ev '' (A : Set (Fin 2 → K))
  obtain ⟨t,ht,hcard,hspan,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn K D
  choose x hx he using (fun f : ↥t ↦ ht f.property)
  let S := t.attach.image x
  have hSA : S ⊆ A := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    exact hx i
  have hsc : S.card ≤ 6 := calc
    S.card ≤ t.attach.card := card_image_le
    _ = t.card := card_attach
    _ = Module.finrank K (Submodule.span K D) := hcard
    _ ≤ Module.finrank K (Module.Dual K U) := Submodule.finrank_le _
    _ = Module.finrank K U := Subspace.dual_finrank_eq
    _ ≤ 6 := quad_dim K
  obtain ⟨F,hn,hd,hv⟩ := hlocal S hSA hsc
  let u : U := ⟨F,(mem_restrictTotalDegree _ _ _).2 hd⟩
  let L := LinearMap.ker (Module.Dual.eval K U u)
  have ann : Submodule.span K (↑t : Set (Module.Dual K U)) ≤ L := by
    apply Submodule.span_le.mpr
    intro f hf
    change f u = 0
    have ef : ev (x ⟨f,hf⟩) = f := he ⟨f,hf⟩
    rw [← ef]
    exact hv _ (mem_image_of_mem x (mem_attach t ⟨f,hf⟩))
  rw [hspan] at ann
  refine ⟨F,hn,hd,fun a ha ↦ ?_⟩
  exact ann (Submodule.subset_span (show ev a ∈ D from ⟨a,ha,rfl⟩))

