import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1

/-! A weight-sixteen support has at most two six-secants. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H3.R1.lean by @avivorly (PR #864) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H3.

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1

-- Pass from a codeword to the incidence data on its support.
def H1 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card
    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card
    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=
      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card
    let profile (S : Finset (Fin 111)) := S.card = 16 ∧
      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧
      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧
      ∀ p∈S, d S p 4 + 2*d S p 6 = 2
    let weight (a : Fin 111 → ZMod 2) := hammingNorm
      (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))
    ∀ a, weight a = 16 → ∃ S, profile S

-- The three possible numbers of six-secants.
def H2 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card
    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card
    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=
      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card
    let profile (S : Finset (Fin 111)) := S.card = 16 ∧
      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧
      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧
      ∀ p∈S, d S p 4 + 2*d S p 6 = 2
    ¬ ∃ S, profile S ∧ n S 6 = 0

def H3 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card
    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card
    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=
      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card
    let profile (S : Finset (Fin 111)) := S.card = 16 ∧
      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧
      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧
      ∀ p∈S, d S p 4 + 2*d S p 6 = 2
    ¬ ∃ S, profile S ∧ n S 6 = 1

def H4 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    let k (S : Finset (Fin 111)) (l : Fin 111) := (S.filter fun p => incidence l p = true).card
    let n (S : Finset (Fin 111)) (j : Nat) := (Finset.univ.filter fun l => k S l = j).card
    let d (S : Finset (Fin 111)) (p : Fin 111) (j : Nat) :=
      (Finset.univ.filter fun l => k S l = j ∧ incidence l p = true).card
    let profile (S : Finset (Fin 111)) := S.card = 16 ∧
      (∀ l, 2 ∣ k S l ∧ k S l ≤ 6) ∧
      (n S 4 + 3*n S 6 = 8 ∧ n S 2 = 72 + 3*n S 6 ∧ n S 0 + n S 6 = 31) ∧
      ∀ p∈S, d S p 4 + 2*d S p 6 = 2
    ¬ ∃ S, profile S ∧ n S 6 = 2

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1.H3 := by
  intro support zero one two incidence row_size column_size row_pairs column_pairs
  dsimp only
  rintro ⟨a, weight⟩
  obtain ⟨S, geometry⟩ := support incidence row_size column_size row_pairs column_pairs a weight
  let n (j : Nat) := (Finset.univ.filter fun l => (S.filter fun p => incidence l p = true).card = j).card
  have balance : n 4 + 3*n 6 = 8 := geometry.2.2.1.1
  have shape : n 6 = 0 ∨ n 6 = 1 ∨ n 6 = 2 := by omega
  rcases shape with h | h | h
  · exact zero incidence row_size column_size row_pairs column_pairs ⟨S, geometry, h⟩
  · exact one incidence row_size column_size row_pairs column_pairs ⟨S, geometry, h⟩
  · exact two incidence row_size column_size row_pairs column_pairs ⟨S, geometry, h⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1
