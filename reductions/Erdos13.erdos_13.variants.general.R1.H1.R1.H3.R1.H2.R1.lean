import OMAReductions.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1

-- Reduction Erdos13.erdos_13.variants.general.R1.H1.R1.H3.R1.H2.R1 of step Erdos13.erdos_13.variants.general.R1.H1.R1.H3.R1.H2
-- Credit: @jenil-bodhani

namespace OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1

open Finset
open scoped Classical

/-- An explicit intermediate range contains a positive proportion of every large sparse ternary set. -/
def H1 : Prop :=
  ∃ V C : ℕ, 0 < V ∧ ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Icc 1 (4*m) →
    (∀ a ∈ A, ∀ b : Fin 3 → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m ≤ A.card → 2*(Ioc (3*m) (4*m) ∩ A).card ≤ m →
    m ≤ V*(A.filter (fun a => 4*m < 377916808*a ∧ (5*a ≤ 4*m ∨ (217*a < 200*m ∧ 5 ∣ a)))).card+C

/-- At every arity from four onward a positive proportion lies below the indicated support cutoff. -/
def H2 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∃ V C : ℕ, 0 < V ∧ ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Icc 1 ((r+1)*m) →
    (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    m ≤ A.card → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    m ≤ V*(A.filter (fun a => if 11 ≤ r then (r+2)*a ≤ (r+1)*m else ((4*r-1)*(r+1)+1)*a ≤ (4*r-1)*((r+1)*m))).card+C

/-- The remaining witness problem with a positive proportion of pivots in the necessary range. -/
def H3 : Prop :=
  ∀ r : ℕ, 3 ≤ r → r < 2^(2^102 : ℕ) → ∀ V C : ℕ, 0 < V → ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → m+K < A.card →
    (∀ j < m, m-j < (A.filter fun a => (r+1)*j < a).card) →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    m < (24*r*r*(r+1)+1)*(A.filter (fun a => r*a < (r+1)*m)).card →
    m < (3*r+4)*(A.filter (fun a => 3 ∣ a)).card →
    m < (r+2)*(A.filter (fun a => 2 ∣ a)).card →
    m ≤ V*(A.filter (fun a => if r=3 then 4*m < 377916808*a ∧ (5*a ≤ 4*m ∨ (217*a < 200*m ∧ 5 ∣ a))
      else if 11 ≤ r then (r+2)*a ≤ (r+1)*m else ((4*r-1)*(r+1)+1)*a ≤ (4*r-1)*((r+1)*m))).card+C →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i

theorem main : H1 → H2 → H3 → OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1.H2 := by
  classical
  intro three wider residual r hr top
  by_cases eq : r=3
  · subst r
    obtain ⟨V,C,vp,range⟩ := three
    obtain ⟨K,finish⟩ := residual 3 hr top V C vp
    refine ⟨K,?_⟩
    intro m A sub large suffix sparse terminal low thirds evens
    by_contra no
    have free : (∀ a ∈ A, ∀ b : Fin 3 → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) := fun a ha b hb lt div =>
      no ⟨a,ha,b,fun i=>⟨hb i,lt i⟩,div⟩
    apply no (finish m A sub large suffix sparse terminal low thirds evens ?_)
    simpa only [if_true] using range m A sub free ((Nat.le_add_right m K).trans large.le) sparse
  · obtain ⟨V,C,vp,range⟩ := wider r (Nat.lt_of_le_of_ne hr (Ne.symm eq))
    obtain ⟨K,finish⟩ := residual r hr top V C vp
    refine ⟨K,?_⟩
    intro m A sub large suffix sparse terminal low thirds evens
    by_contra no
    have free : (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) := fun a ha b hb lt div =>
      no ⟨a,ha,b,fun i=>⟨hb i,lt i⟩,div⟩
    apply no (finish m A sub large suffix sparse terminal low thirds evens ?_)
    simpa only [if_neg eq] using range m A sub free ((Nat.le_add_right m K).trans large.le) sparse

end OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1
