import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1

/-! Reduce the primitive weight-nineteen case to the line and point incidence counts. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.lean by @avivorly (PR #944) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H4.

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1

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
    let profile (S : Finset (Fin 111)) := S.card = 19 ∧
      (∀ l, k S l = 1 ∨ k S l = 3 ∨ k S l = 5) ∧
      (n S 1 = 68 ∧ n S 3 = 37 ∧ n S 5 = 6) ∧
      ∀ p, d S p 3 + 2*d S p 5 = if p∈S then 9 else 4
    let word : (Fin 111 → ZMod 2) → Fin 112 → ZMod 2 := fun a =>
      Fin.cons (∑ l, a l) (fun p : Fin 111 => ∑ l, a l * (if incidence l p = true then 1 else 0))
    let wt := fun a => hammingNorm (fun p : Fin 111 => word a p.succ)
    ∀ a, wt a = 19 → (∀ b c, wt b < 19 → wt c < 19 → word a ≠ word b + word c) →
      ∃ S, profile S

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
    let profile (S : Finset (Fin 111)) := S.card = 19 ∧
      (∀ l, k S l = 1 ∨ k S l = 3 ∨ k S l = 5) ∧
      (n S 1 = 68 ∧ n S 3 = 37 ∧ n S 5 = 6) ∧
      ∀ p, d S p 3 + 2*d S p 5 = if p∈S then 9 else 4
    ¬ ∃ S, profile S

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1.H4 := by
  intro support impossible incidence row_size column_size row_pairs column_pairs
  dsimp only
  rintro ⟨a, weight, primitive⟩
  exact impossible incidence row_size column_size row_pairs column_pairs
    (support incidence row_size column_size row_pairs column_pairs a weight primitive)

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1
