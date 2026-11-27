import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1
import Mathlib
/- Adapted from openai/math, Apache-2.0, 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1
open scoped Classical

def H1 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let U := fun {A : Type} [Fintype A] (f : A → ℝ) => (∑ a, f a) / (Fintype.card A : ℝ)
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
  let S := fun (d : ℕ) (q : Q) => {A : Matrix (Fin d) (Fin d) (ZMod q.val) // A.IsSymm}
  ∃ d : ℕ, Even d ∧ 12 ≤ d ∧ ∃ (M : Q → Type) (_ : ∀ q, AddCommGroup (M q)) (_ : ∀ q, Fintype (M q))
    (R : ∀ q, ℤ → M q → ℝ),
    (∀ q ξ z, 0 ≤ R q ξ z) ∧ (∀ q ξ, (ξ = 1 ∨ ξ = -1) → U (R q ξ) = 1) ∧
    (∀ q ξ z, R q ξ (-z) = R q ξ z) ∧
    ∀ (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ), (∀ j k, ξ j k = 1 ∨ ξ j k = -1) →
      let b := fun (q : Q) (X : Fin 13 → S d q) (j : Fin 22) (k : Fin 3) => haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; decide (quadraticChar (ZMod q.val) ((X (t j (sL k))).val - (X (t j (sR k))).val).det = 1)
      Filter.Tendsto (fun q => U (fun xy : (Fin 13 → M q) × (Fin 22 → M q) => ∏ j, ∏ k ∈ T j, R q (ξ j k) (xy.1 (t j k) - xy.2 j)) - (haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; U (fun X : Fin 13 → S d q => ∏ j, ∏ k, if sL k ∈ T j ∧ sR k ∈ T j then 1 + (if b q X j k then (1:ℝ) else -1)*(ξ j (sL k):ℝ)*(ξ j (sR k):ℝ) else 1))) (Filter.comap (fun q : Q => q.val) Filter.atTop) (nhds 0)

def H2 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let U := fun {A : Type} [Fintype A] (f : A → ℝ) => (∑ a, f a) / (Fintype.card A : ℝ)
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
  let S := fun (d : ℕ) (q : Q) => {A : Matrix (Fin d) (Fin d) (ZMod q.val) // A.IsSymm}
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  ∀ d : ℕ, Even d → 12 ≤ d → ∀ f : (Fin 22 → Fin 3 → Bool) → ℝ,
    let b := fun (q : Q) (X : Fin 13 → S d q) (j : Fin 22) (k : Fin 3) => haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; decide (quadraticChar (ZMod q.val) ((X (t j (sL k))).val - (X (t j (sR k))).val).det = 1)
    Filter.Tendsto (fun q : Q => haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; U (fun X : Fin 13 → S d q => f (b q X))) (Filter.comap (fun q : Q => q.val) Filter.atTop) (nhds (U (fun η : Fin 33 → Bool => f (fun j k => η (p j k)))))

theorem main : H1 → H2 → OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1.H1 := by
  classical
  rintro ⟨d,he,hd,M,G,I,R,hn,hm,hs,ha⟩ hb
  letI := G
  letI := I
  refine ⟨M,G,I,R,hn,hm,hs,?_⟩
  intro T ξ hξ
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let f := fun b : Fin 22 → Fin 3 → Bool => ∏ j, ∏ k, if sL k ∈ T j ∧ sR k ∈ T j then 1 + (if b j k then (1:ℝ) else -1)*(ξ j (sL k):ℝ)*(ξ j (sR k):ℝ) else 1
  have h := (ha T ξ hξ).add (hb d he hd f)
  rw [zero_add] at h
  exact h.congr (fun q => sub_add_cancel _ _)
end OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1
