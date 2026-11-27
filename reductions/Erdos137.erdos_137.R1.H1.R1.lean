import OMAReductions.R_Erdos137_erdos_137_R1
import Mathlib

/-! A width-three product is powerful exactly when there is a powerful triple
or a consecutive powerful pair whose remaining outer term is twice an odd
powerful number. This leaves a search over consecutive powerful pairs. -/

open Finset

namespace OMA.R_Erdos137_erdos_137_R1_H1_R1

def H1 : Prop :=
  ∃ a : ℕ, 0 < a ∧
    ((a.Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful) ∨
    (4 ∣ a ∧ a.Powerful ∧ (a+1).Powerful ∧ ((a+2)/2).Powerful) ∨
    (4 ∣ a+2 ∧ (a/2).Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful))

def H2 : Prop :=
  ∀ a : ℕ, 0 < a →
    ((a*(a+1)*(a+2)).Powerful ↔
    (a.Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful) ∨
    (4 ∣ a ∧ a.Powerful ∧ (a+1).Powerful ∧ ((a+2)/2).Powerful) ∨
    (4 ∣ a+2 ∧ (a/2).Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful))

section Proof

private theorem block_three (n : ℕ) :
    (∏ x ∈ Ioc n (n+3), x) = (n+1)*((n+1)+1)*((n+1)+2) := by
  have hRange : Ioc n (n+3) = insert (n+1) {n+2,n+3} := by
    ext x
    simp only [mem_Ioc,mem_insert,mem_singleton]
    omega
  have h₁ : n+1 ∉ ({n+2,n+3} : Finset ℕ) := by simp
  have h₂ : n+2 ∉ ({n+3} : Finset ℕ) := by simp
  rw [hRange,prod_insert h₁,prod_insert h₂,prod_singleton]
  ring

theorem main : H1 → H2 → OMA.R_Erdos137_erdos_137_R1.H1 := by
  rintro ⟨a,ha,h⟩ hh
  use a-1
  rw [block_three,Nat.sub_add_cancel ha]
  exact (hh a ha).mpr h

theorem converse (h2 : H2) :
    OMA.R_Erdos137_erdos_137_R1.H1 → H1 := by
  rintro ⟨n,h⟩
  rw [block_three] at h
  exact ⟨n+1,by omega,(h2 (n+1) (by omega)).mp h⟩

end Proof

end OMA.R_Erdos137_erdos_137_R1_H1_R1
