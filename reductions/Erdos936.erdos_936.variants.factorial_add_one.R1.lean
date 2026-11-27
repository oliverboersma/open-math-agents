import FormalConjectures.ErdosProblems.«936»
import Mathlib.NumberTheory.Primorial

/-!
The factorial-plus-one case of the conditional argument of Cushing and
Pascoe, Theorem 4.1 of [Powerful numbers and the ABC-conjecture](https://arxiv.org/abs/1611.01192).
A fixed exponent of 3/2 in an abc bound suffices for the triples
(1, n!, n!+1). The radical of n! is the primorial of n.
-/

open Finset Filter Nat

namespace OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1

/-- The square of the radical divides each positive powerful number. -/
def H1 : Prop :=
  ∀ c : ℕ, 0 < c → c.Powerful → (∏ p ∈ c.primeFactors, p) ^ 2 ∣ c

/-- Factorials eventually dominate every fixed power of the primorial. -/
def H2 : Prop :=
  ∀ C e : ℕ, ∀ᶠ n : ℕ in atTop, C * (primorial n) ^ e < n.factorial

/-- The remaining abc estimate for factorials, written with integer powers. -/
def H3 : Prop :=
  ∃ C : ℕ, ∀ n : ℕ,
    let c := n.factorial + 1
    c ^ 2 ≤ C * (primorial n * (∏ p ∈ c.primeFactors, p)) ^ 3

section Proof

theorem main : H1 → H2 → H3 → type_of% @Erdos936.erdos_936.variants.factorial_add_one := by
  intro radicalSquare growth ⟨C, hABC⟩
  change ∀ᶠ n : ℕ in atTop, ¬ (n.factorial + 1).Powerful
  filter_upwards [growth (C ^ 2) 6] with n hn
  intro hpower
  let c := n.factorial + 1
  let r := ∏ p ∈ c.primeFactors, p
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : r ^ 2 ≤ c := Nat.le_of_dvd hc (radicalSquare c hc hpower)
  have hABCn : c ^ 2 ≤ C * (primorial n * r) ^ 3 := hABC n
  have hbound : c * c ^ 3 ≤ (C ^ 2 * (primorial n) ^ 6) * c ^ 3 := by
    calc
      c * c ^ 3 = (c ^ 2) ^ 2 := by ring
      _ ≤ (C * (primorial n * r) ^ 3) ^ 2 := Nat.pow_le_pow_left hABCn 2
      _ = (C ^ 2 * (primorial n) ^ 6) * (r ^ 2) ^ 3 := by ring
      _ ≤ (C ^ 2 * (primorial n) ^ 6) * c ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 3)
  have hcancel := Nat.le_of_mul_le_mul_right hbound (Nat.pow_pos hc)
  have hfac : n.factorial ≤ c := by simp [c]
  exact (not_le_of_gt hn) (hfac.trans hcancel)

end Proof

end OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1
