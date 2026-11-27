import FormalConjectures.ErdosProblems.«242»
import Mathlib

/-!
Separate the prime denominators congruent to one modulo 24 from the
denominators covered by explicit identities. A solution for an odd
prime divisor scales to a solution for the entire denominator.
-/

namespace OMA.R_Erdos242_erdos_242_R1

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4/p : ℚ) = 1/x+1/y+1/z

def H2 : Prop :=
  ∀ n : ℕ, 2 < n → n%24 ≠ 1 →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4/n : ℚ) = 1/x+1/y+1/z

section Proof

private theorem scale_expansion {a d n : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (h : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a/d : ℚ) = 1/x+1/y+1/z) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a/n : ℚ) = 1/x+1/y+1/z := by
  obtain ⟨k,hk⟩ := hd
  obtain ⟨x,y,z,hx,hxy,hyz,hEq⟩ := h
  have hk0 : 0 < k := by
    by_contra! h
    have hk' := Nat.eq_zero_of_le_zero h
    rw [hk',mul_zero] at hk
    omega
  refine ⟨x*k,y*k,z*k,(Nat.mul_pos (by omega) hk0),Nat.mul_lt_mul_of_pos_right hxy hk0,
    Nat.mul_lt_mul_of_pos_right hyz hk0,?_⟩
  have hh := congrArg (fun r : ℚ => r/(k : ℚ)) hEq
  simpa only [hk,Nat.cast_mul,div_div,add_div] using hh

theorem main : H1 → H2 → type_of% @Erdos242.erdos_242 := by
  intro hpmod hOther n hn
  by_cases h : n%24=1
  · let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega : n ≠ 1)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hp2 : p ≠ 2 := by
      intro he
      have hd : 2 ∣ n := he ▸ hpn
      omega
    have hp3 : 2 < p := by have := hp.two_le; omega
    have hex : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (4/p : ℚ) = 1/x+1/y+1/z := by
      by_cases hP : p%24=1
      · exact hpmod p hp hP
      · exact hOther p hp3 hP
    exact scale_expansion (a := 4) (by omega) hpn hex
  · exact hOther n hn h

end Proof

end OMA.R_Erdos242_erdos_242_R1
