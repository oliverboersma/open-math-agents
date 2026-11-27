import OMAReductions.R_Erdos137_erdos_137_R1
import Mathlib

/-!
A length-four block can share only factors 2 and 3. Every prime above 3
must appear twice in its own term. The power of 2 is supplied automatically,
so one additional congruence handles the prime 3.
-/

open Finset

namespace OMA.R_Erdos137_erdos_137_R1_H2_R1

def H1 : Prop :=
  ∃ a : ℕ, 0 < a ∧
    (∀ x ∈ Ico a (a+4), ∀ p : ℕ, p.Prime → 3 < p → p ∣ x → p^2 ∣ x) ∧
    (a%3 = 0 ∨ 9 ∣ a+3-a%3)

def H2 : Prop :=
  ∀ a : ℕ, 0 < a →
    ((∏ x ∈ Ico a (a+4), x).Powerful ↔
      (∀ x ∈ Ico a (a+4), ∀ p : ℕ, p.Prime → 3 < p → p ∣ x → p^2 ∣ x) ∧
      (a%3 = 0 ∨ 9 ∣ a+3-a%3))

section Proof

private theorem block_four (n : ℕ) : Ioc n (n+4) = Ico (n+1) ((n+1)+4) := by
  ext x
  simp only [mem_Ioc,mem_Ico]
  omega

theorem main : H1 → H2 → OMA.R_Erdos137_erdos_137_R1.H2 := by
  rintro ⟨a,ha,h⟩ ht
  use a-1
  rw [block_four,Nat.sub_add_cancel ha]
  exact (ht a ha).mpr h

theorem converse (h2 : H2) : OMA.R_Erdos137_erdos_137_R1.H2 → H1 := by
  rintro ⟨n,h⟩
  rw [block_four] at h
  exact ⟨n+1,by omega,(h2 (n+1) (by omega)).mp h⟩

end Proof

end OMA.R_Erdos137_erdos_137_R1_H2_R1
