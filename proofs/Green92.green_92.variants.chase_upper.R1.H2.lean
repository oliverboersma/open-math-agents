import OMAReductions.R_Green92_green_92_variants_chase_upper_R1
import Mathlib

-- Step Green92.green_92.variants.chase_upper.R1.H2: hypothesis H2 of reduction Green92.green_92.variants.chase_upper.R1
-- Credit: @ivillar

/-!
# From pairwise tests to a decoder (union bound)

The decoder returns the unique `x` that wins every pairwise test `D x y`, when there is one.
Antisymmetry of the tests makes such an `x` unique. For a fixed `x`, the decoder can only fail on
the samples where some test `D x y` with `y ≠ x` fails, and there are at most
`2 ^ n * (N / (10 * 2 ^ n)) ≤ N / 10` of those among the `N` samples.
-/

namespace Green92DecodeStep

open Finset Filter Green92
open scoped Classical

theorem decode :
  ∀ (n m : ℕ) (D : (Fin n → Bool) → (Fin n → Bool) → (Fin m → List Bool) → Prop),
    (∀ x y o, x ≠ y → D x y o → ¬ D y x o) → (∀ x y, x ≠ y →
      (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D x y (fun j => Green92.trace x (S j))).card ≤
        Fintype.card (Fin m → Finset (Fin n)) / (10 * 2^n)) →
    ∃ R : (Fin m → List Bool) → Fin n → Bool, ∀ x, (9/10 : ℝ) ≤ successProb R x := by
  intro n m D hanti hsmall
  have hex : ∀ o : Fin m → List Bool, ∃ r : Fin n → Bool,
      ∀ x, (∀ y, y ≠ x → D x y o) → r = x := by
    intro o
    by_cases h : ∃ x, ∀ y, y ≠ x → D x y o
    · obtain ⟨c, hc⟩ := h
      refine ⟨c, fun x hx => ?_⟩
      by_contra hne
      exact hanti c x o hne (hc x (fun e => hne e.symm)) (hx c hne)
    · exact ⟨fun _ => false, fun x hx => absurd ⟨x, hx⟩ h⟩
  choose R hR using hex
  refine ⟨R, fun x => ?_⟩
  have hN : 0 < Fintype.card (Fin m → Finset (Fin n)) := Fintype.card_pos
  have hsplit : (univ.filter fun S : Fin m → Finset (Fin n) =>
        R (fun j => trace x (S j)) = x).card +
      (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ R (fun j => trace x (S j)) = x).card =
      Fintype.card (Fin m → Finset (Fin n)) := by
    rw [card_filter_add_card_filter_not, card_univ]
  have hbad : (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ R (fun j => trace x (S j)) = x) ⊆
      (univ.erase x).biUnion (fun y => univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D x y (fun j => trace x (S j))) := by
    intro S hS
    rw [mem_filter] at hS
    have h1 : ¬ ∀ y, y ≠ x → D x y (fun j => trace x (S j)) := fun h => hS.2 (hR _ x h)
    obtain ⟨y, hy⟩ := not_forall.mp h1
    have hy' : y ≠ x ∧ ¬ D x y (fun j => trace x (S j)) := Classical.not_imp.mp hy
    exact mem_biUnion.mpr ⟨y, mem_erase.mpr ⟨hy'.1, mem_univ _⟩,
      mem_filter.mpr ⟨mem_univ _, hy'.2⟩⟩
  have hcard : (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ R (fun j => trace x (S j)) = x).card ≤
      2 ^ n * (Fintype.card (Fin m → Finset (Fin n)) / (10 * 2 ^ n)) := by
    calc (univ.filter fun S : Fin m → Finset (Fin n) =>
          ¬ R (fun j => trace x (S j)) = x).card
        ≤ ((univ.erase x).biUnion (fun y => univ.filter fun S : Fin m → Finset (Fin n) =>
            ¬ D x y (fun j => trace x (S j)))).card := card_le_card hbad
      _ ≤ ∑ y ∈ univ.erase x, (univ.filter fun S : Fin m → Finset (Fin n) =>
            ¬ D x y (fun j => trace x (S j))).card := card_biUnion_le
      _ ≤ ∑ _y ∈ univ.erase x, Fintype.card (Fin m → Finset (Fin n)) / (10 * 2 ^ n) :=
          sum_le_sum (fun y hy => hsmall x y (mem_erase.mp hy).1.symm)
      _ = (univ.erase x).card * (Fintype.card (Fin m → Finset (Fin n)) / (10 * 2 ^ n)) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ 2 ^ n * (Fintype.card (Fin m → Finset (Fin n)) / (10 * 2 ^ n)) := by
          refine Nat.mul_le_mul_right _ ?_
          calc (univ.erase x).card ≤ (univ : Finset (Fin n → Bool)).card := card_erase_le
            _ = 2 ^ n := by simp
  have hten : 10 * (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ R (fun j => trace x (S j)) = x).card ≤ Fintype.card (Fin m → Finset (Fin n)) := by
    have h2 := Nat.mul_div_le (Fintype.card (Fin m → Finset (Fin n))) (10 * 2 ^ n)
    nlinarith
  have hgood : (9 : ℝ) * Fintype.card (Fin m → Finset (Fin n)) ≤
      10 * ((univ.filter fun S : Fin m → Finset (Fin n) =>
        R (fun j => trace x (S j)) = x).card : ℝ) := by
    have h3 : 9 * Fintype.card (Fin m → Finset (Fin n)) ≤
        10 * (univ.filter fun S : Fin m → Finset (Fin n) =>
          R (fun j => trace x (S j)) = x).card := by omega
    exact_mod_cast h3
  have hNr : (0 : ℝ) < Fintype.card (Fin m → Finset (Fin n)) := by exact_mod_cast hN
  unfold successProb
  rw [le_div_iff₀ hNr]
  linarith

end Green92DecodeStep

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_upper_R1.H2 :=
  Green92DecodeStep.decode
