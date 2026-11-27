import OMAReductions.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1

-- Reduction Erdos13.erdos_13.variants.general.R1.H1.R1.H3.R1.H2.R1.H3.R1 of the remaining sparse witness problem
-- Credit: @jenil-bodhani

namespace OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1_H3_R1

open Finset
open scoped Classical

/-- A positive proportion of the sparse set belongs to the exact residue class two modulo four. -/
def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ W D : ℕ, 0 < W ∧ ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) →
    (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m ≤ A.card → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    m ≤ W*(A.filter (fun a => a%4=2)).card+D

/-- The remaining witness problem when the exact dyadic valuation one occurs at positive density. -/
def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → r < 2^(2^102 : ℕ) → ∀ V C W D : ℕ, 0 < V → 0 < W → ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → m+K < A.card →
    (∀ j < m, m-j < (A.filter fun a => (r+1)*j < a).card) →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    m < (24*r*r*(r+1)+1)*(A.filter (fun a => r*a < (r+1)*m)).card →
    m < (3*r+4)*(A.filter (fun a => 3 ∣ a)).card →
    m < (r+2)*(A.filter (fun a => 2 ∣ a)).card →
    m ≤ V*(A.filter (fun a => if r=3 then 4*m < 377916808*a ∧ (5*a ≤ 4*m ∨ (217*a < 200*m ∧ 5 ∣ a))
      else if 11 ≤ r then (r+2)*a ≤ (r+1)*m else ((4*r-1)*(r+1)+1)*a ≤ (4*r-1)*((r+1)*m))).card+C →
    m ≤ W*(A.filter (fun a => a%4=2)).card+D →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i

theorem main : H1 → H2 → OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1.H3 := by
  intro mass finish r hr bound V C vp
  obtain ⟨W,D,wp,rec⟩:=mass r hr
  obtain ⟨K,goal⟩:=finish r hr bound V C W D vp wp
  refine ⟨K,?_⟩
  intro m A sub large suffix sparse terminal low thirds evens middle
  by_contra no
  have free : ∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬ a ∣ ∑ i, b i :=
    fun a ha b hb hlt dvd=>no ⟨a,ha,b,fun i=>⟨hb i,hlt i⟩,dvd⟩
  exact no (goal m A sub large suffix sparse terminal low thirds evens middle
    (rec m A sub free ((Nat.le_add_right m K).trans large.le) sparse terminal))

end OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1_H3_R1
