import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2
import Mathlib

/-!
Weak reflection via a polynomial congruence in the ramified residue ring.
The congruence separates the global cyclotomic-unit index from a calculation
in characteristic p. Taking successive differences of the unweighted
moments leaves a square Vandermonde system on the nontrivial square nodes.
The third input is a consequence of the project's proved relative criterion
(R2.H3, PR 6699). Credit for this reduction: @Iraeeee.
-/

namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1

open NumberField Polynomial

/-- A real class-number factor gives a nontrivial relation among reduced
cyclotomic units in the truncated polynomial ring at a prime above p. -/
def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime],
  p ∣ classNumber (maximalRealSubfield (CyclotomicField p ℚ)) →
  let m := (p - 3) / 2
  ∃ (e : Fin m → Fin p) (s : ℕ) (c : ZMod p), c ≠ 0 ∧
    (∃ a, ((e a).val : ZMod p) ≠ 0) ∧
    (X : (ZMod p)[X]) ^ (p - 1) ∣
      (∏ a : Fin m, (∑ i ∈ Finset.range (a.val + 2), (1 + (X : (ZMod p)[X])) ^ i) ^ (2 * (e a).val)) -
        Polynomial.C c * (1 + (X : (ZMod p)[X])) ^ s

/-- An identity of truncated geometric sums forces the Bernoulli-weighted
even moments of its exponents to vanish. This is entirely over F_p. -/
def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime],
  let m := (p - 3) / 2
  ∀ (e : Fin m → Fin p) (s : ℕ) (c : ZMod p), c ≠ 0 →
    (X : (ZMod p)[X]) ^ (p - 1) ∣
      (∏ a : Fin m, (∑ i ∈ Finset.range (a.val + 2), (1 + (X : (ZMod p)[X])) ^ i) ^ (2 * (e a).val)) -
        Polynomial.C c * (1 + (X : (ZMod p)[X])) ^ s →
    ∀ j : Fin m, ((_root_.bernoulli (2 * (j.val + 1))).num : ZMod p) *
      (∑ a, ((e a).val : ZMod p) * (((((a.val + 2 : ℕ) : ZMod p) ^ 2) ^ (j.val + 1)) - 1)) = 0

/-- The divisibility direction of the relative Bernoulli criterion. -/
def H3 : Prop := ∀ (p : ℕ) [Fact p.Prime] (j : Fin ((p - 3) / 2)),
  (p : ℤ) ∣ (_root_.bernoulli (2 * (j.val + 1))).num →
  p ∣ classNumber (CyclotomicField p ℚ) /
    classNumber (maximalRealSubfield (CyclotomicField p ℚ))

lemma half_square_eq {p a b : ℕ} [Fact p.Prime]
    (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 2 * a < p) (hb' : 2 * b < p)
    (heq : (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2) : a = b := by
  have hz : ((a : ZMod p) - b) * (a + b) = 0 := by
    calc
      _ = (a : ZMod p) ^ 2 - b ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp hz with h | h
  · have hc := sub_eq_zero.mp h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (show a < p by omega),
      Nat.mod_eq_of_lt (show b < p by omega)] at hc
    exact hc
  · have hd : p ∣ a + b := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using h)
    have := Nat.le_of_dvd (show 0 < a + b by omega) hd
    omega

lemma weights_vanish {F : Type*} [Field F] {m : ℕ} (x v : Fin m → F)
    (hinj : Function.Injective x) (hne : ∀ a, x a ≠ 1)
    (hm : ∀ j : Fin m, (∑ a, v a * (x a ^ (j.val + 1) - 1)) = 0) :
    ∀ a, v a = 0 := by
  have hall (i : ℕ) (hi : i ≤ m) : (∑ a, v a * (x a ^ i - 1)) = 0 := by
    cases i with
    | zero => simp
    | succ i => exact hm ⟨i, by omega⟩
  have hv : (fun a => v a * (x a - 1)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro i
    calc
      _ = ∑ a, (v a * (x a ^ (i.val + 1) - 1) - v a * (x a ^ i.val - 1)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [pow_succ]
        ring
      _ = 0 := by rw [Finset.sum_sub_distrib, hm i, hall i.val i.isLt.le, sub_zero]
  intro a
  exact (mul_eq_zero.mp (congrFun hv a)).resolve_right (sub_ne_zero.mpr (hne a))

theorem main : H1 → H2 → H3 → OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2.H2 := by
  intro hindex hlocal hrelative p hp
  dsimp only
  intro hplus
  obtain ⟨e, s, c, hc, ⟨a, ha⟩, hpoly⟩ := hindex p hplus
  by_contra hminus
  let x (b : Fin ((p - 3) / 2)) : ZMod p := ((b.val + 2 : ℕ) : ZMod p) ^ 2
  have half (b : Fin ((p - 3) / 2)) : 2 * (b.val + 2) < p := by
    have := b.isLt
    omega
  have hinj : Function.Injective x := by
    intro b d h
    have he := half_square_eq (by omega) (by omega) (half b) (half d) h
    exact Fin.ext (by omega)
  have hone (b : Fin ((p - 3) / 2)) : x b ≠ 1 := by
    intro h
    have hh : ((b.val + 2 : ℕ) : ZMod p) ^ 2 = ((1 : ℕ) : ZMod p) ^ 2 := by simpa [x] using h
    have hb := half b
    have := half_square_eq (by omega) (by decide) hb (by omega) hh
    omega
  apply ha
  apply weights_vanish x (fun b => ((e b).val : ZMod p)) hinj hone _ a
  intro j
  have hB : ((_root_.bernoulli (2 * (j.val + 1))).num : ZMod p) ≠ 0 := by
    intro hz
    exact hminus (hrelative p j ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
  have hm := hlocal p e s c hc hpoly j
  exact (mul_eq_zero.mp hm).resolve_left hB

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1
