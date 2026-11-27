import OMAReductions.R_Green100_green_100_parts_i_R1
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Module

/-! Separate permutation amplification from the finite rank obstruction of Elek and
Szabó. The unrestricted linear cellular map is the algebraic dual of right
multiplication on the group algebra, including when the group is infinite. -/
namespace OMA.R_Green100_green_100_parts_i_R1_H2_R1
open Green100 Finset
open scoped Classical

/-- Simultaneous separation and multiplication on a large set of points in a
finite permutation model. The integer parameter specifies the error tolerance. -/
def H1 : Prop := ∀ (G : Type) [Group G], IsSofic G → ∀ (F : Finset G) (k : ℕ),
  ∃ (n : ℕ) (θ : G → Equiv.Perm (Fin n)) (U : Finset (Fin n)),
    k*(n-U.card) < n ∧ ∀ i ∈ U, θ 1 i = i ∧ Set.InjOn (fun g => θ g i) F ∧
      ∀ g ∈ F, ∀ h ∈ F, θ (g*h) i = θ g (θ h i)

/-- A failure of direct finiteness forces a positive proportion of bad points.
This is a finite-dimensional rank estimate, without a soficity assumption. -/
def H2 : Prop := ∀ (K G : Type) [Field K] [Fintype K] [Group G] (a b : MonoidAlgebra K G),
  a*b = 1 → b*a ≠ 1 → ∃ (F : Finset G) (k : ℕ),
    ∀ (n : ℕ) (θ : G → Equiv.Perm (Fin n)) (U : Finset (Fin n)),
      (∀ i ∈ U, θ 1 i = i ∧ Set.InjOn (fun g => θ g i) F ∧
        ∀ g ∈ F, ∀ h ∈ F, θ (g*h) i = θ g (θ h i)) → n ≤ k*(n-U.card)

set_option maxHeartbeats 1200000 in
theorem main : H1 → H2 → OMA.R_Green100_green_100_parts_i_R1.H2 := by
  classical
  intro amplify obstruct K _ _ G _ sofic b inject
  let B := MonoidAlgebra.basis G K
  let D : (G → K) ≃ₗ[K] Module.Dual K (MonoidAlgebra K G) := B.constr K
  let R := LinearMap.mulRight K b
  let cell (x : G → K) (g : G) := b.coeff.sum fun u c => c*x (g*u)
  have eval_single (x : G → K) (g : G) : D x (MonoidAlgebra.single g 1) = x g := by
    simpa only [B,MonoidAlgebra.basis_apply] using B.constr_basis K x g
  have intertwine (x : G → K) : R.dualMap (D x) = D (cell x) := by
    apply B.ext
    intro g
    simp only [B,MonoidAlgebra.basis_apply,LinearMap.dualMap_apply,
      R,LinearMap.mulRight_apply]
    rw [eval_single]
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single b]
    simp only [cell,Finsupp.sum,Finset.mul_sum,map_sum,MonoidAlgebra.single_mul_single,one_mul]
    refine sum_congr rfl ?_
    intro u _
    have eq : MonoidAlgebra.single (g*u) (b.coeff u) =
        b.coeff u • (MonoidAlgebra.single (g*u) 1 : MonoidAlgebra K G) := by
      simp
    rw [eq,map_smul,eval_single,smul_eq_mul]
  have injDual : Function.Injective R.dualMap := by
    intro φ ψ eq
    obtain ⟨x,rfl⟩ := D.surjective φ
    obtain ⟨y,rfl⟩ := D.surjective ψ
    rw [intertwine,intertwine] at eq
    exact congrArg D (inject (D.injective eq))
  obtain ⟨a,hab⟩ := LinearMap.dualMap_injective_iff.mp injDual 1
  change a*b = 1 at hab
  have hba : b*a = 1 := by
    by_contra h
    obtain ⟨F,k,lower⟩ := obstruct K G a b hab h
    obtain ⟨n,θ,U,small,good⟩ := amplify G sofic F k
    exact small.not_ge (lower n θ U good)
  have injR : Function.Injective R := by
    intro u v h
    change u*b = v*b at h
    simpa only [mul_assoc,hba,mul_one] using congrArg (fun z => z*a) h
  intro y
  obtain ⟨φ,hφ⟩ := LinearMap.dualMap_surjective_iff.mpr injR (D y)
  obtain ⟨x,rfl⟩ := D.surjective φ
  exact ⟨x,D.injective ((intertwine x).symm.trans hφ)⟩

end OMA.R_Green100_green_100_parts_i_R1_H2_R1
