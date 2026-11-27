import OMAReductions.R_Green100_green_100_parts_i_R1
import Mathlib

/-! The matrix obstruction and fixed-field transfer are separated in OpenAI's
OddKaplansky development, openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The faithful action argument below adapts its Cellular module under Apache-2.0.
The action on a configuration supported at one group element recovers the
coefficient there. Thus a one-sided inverse in the group ring supplies an
injective cellular operator whose surjectivity would force a two-sided inverse. -/
namespace OMA.R_Green100_green_100_parts_i_R1_H1_R1

def H1 : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (L : Type) (_ : Group L),
    3 ≤ Fintype.card K ∧ ∃ r : ℕ, 0 < r ∧
    ∃ A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L), A * B = 1 ∧ B * A ≠ 1

def H2 : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Group L], 3 ≤ Fintype.card K →
  ∀ r : ℕ, 0 < r → ∀ A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L),
    A * B = 1 → B * A ≠ 1 →
    ∃ (Λ : Type) (_ : Group Λ) (_ : Fintype Λ),
      ∃ a b : MonoidAlgebra K (L × Λ), a * b = 1 ∧ b * a ≠ 1

lemma cellular_witness (K G : Type) [Field K] [Group G]
    (a b : MonoidAlgebra K G) (hab : a*b=1) (hba : b*a≠1) :
    let T := fun (d : MonoidAlgebra K G) (x : G → K) (g : G) =>
      d.coeff.sum fun u c => c * x (g*u)
    Function.Injective (T b) ∧ ¬ Function.Surjective (T b) := by
  classical
  let R (u : G) : Module.End K (G → K) :=
    { toFun := fun x g => x (g*u), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let S : G →* Module.End K (G → K) :=
    { toFun := R, map_one' := by ext x g; simp [R]
      map_mul' := by intro u v; ext x g; simp [R,mul_assoc] }
  let T := MonoidAlgebra.lift K (Module.End K (G → K)) G S
  have single (u : G) (c : K) (x : G → K) (g : G) :
      T (MonoidAlgebra.single u c) x g = c*x (g*u) := by
    dsimp only [T]
    rw [MonoidAlgebra.lift_single]
    rfl
  have formula (d : MonoidAlgebra K G) (x : G → K) (g : G) :
      T d x g = d.coeff.sum fun u c => c*x (g*u) := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single d]
    simp only [Finsupp.sum,map_sum,LinearMap.sum_apply,Finset.sum_apply,single]
  have coeff (d : MonoidAlgebra K G) (h : G) : T d (Pi.single h 1) 1 = d.coeff h := by
    rw [formula]
    simp only [Finsupp.sum,one_mul,Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq']
    split_ifs with hh
    · rfl
    · exact (Finsupp.notMem_support_iff.mp hh).symm
  have left : Function.LeftInverse (T a) (T b) := by
    intro x
    change (T a * T b) x = x
    rw [← map_mul,hab,map_one]
    rfl
  have eqfun : (fun (x : G → K) (g : G) => b.coeff.sum fun u c => c*x (g*u)) = T b := by
    funext x g
    exact (formula b x g).symm
  dsimp only
  rw [eqfun]
  refine ⟨left.injective,fun surj => hba ?_⟩
  have right := left.rightInverse_of_surjective surj
  ext h
  rw [← coeff, ← coeff (1 : MonoidAlgebra K G),map_mul,map_one]
  exact congrFun (right (Pi.single h 1)) 1

theorem main : H1 → H2 → OMA.R_Green100_green_100_parts_i_R1.H1 := by
  rintro ⟨K,fK,ftK,L,gL,hK,r,hr,A,B,hAB,hBA⟩ transfer
  letI := fK
  letI := ftK
  letI := gL
  obtain ⟨Λ,gΛ,_,a,b,hab,hba⟩ := transfer K L hK r hr A B hAB hBA
  letI := gΛ
  exact ⟨K,fK,ftK,L × Λ,inferInstance,b,cellular_witness K (L × Λ) a b hab hba⟩

end OMA.R_Green100_green_100_parts_i_R1_H1_R1
