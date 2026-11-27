import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1
import Mathlib

/-!
Real cyclotomic-unit independence from the classical Kummer congruence
and the nonvanishing of a finite Vandermonde determinant.
Interfaces and bridge: Hanan Beer (@hananzlt), following the formalization of
Riccardo Brasca (@riccardobrasca) and the KummerCriterion contributors,
Apache-2.0, pinned commit 470de714f3de5a1ec8c0f6209502c1c5272c2c43.
This is a conditional reduction of the independence input only.
-/

namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1
open NumberField
open scoped NumberField BigOperators

/-- A pth-power relation among real cyclotomic generators satisfies Kummer's congruences. -/
def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  let m := (p - 3) / 2
  ∀ g : Fin m → (𝓞 L)ˣ,
    (∀ a, algebraMap (𝓞 L) K (g a : 𝓞 L) =
      (∑ i ∈ Finset.range (a.val + 2), z ^ i) *
        (∑ i ∈ Finset.range (a.val + 2), (z⁻¹) ^ i)) →
    ∀ (s : ℤ) (e : Fin m → ℤ) (u : (𝓞 L)ˣ),
      u ^ p = (-1) ^ s * ∏ a, g a ^ e a → ∀ j : Fin m,
      ((bernoulli (2 * (j.val + 1))).num : ZMod p) *
        (∑ a : Fin m, (((a.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1) *
          (e a : ZMod p)) = 0

/-- The even-power nodes give a nonsingular finite-field Vandermonde difference matrix. -/
def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime], 3 ≤ p →
  (Matrix.det (fun j a : Fin ((p - 3) / 2) =>
    ((a.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1)) ≠ 0

theorem main : H1 → H2 →
    OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1.H2 := by
  intro hcongruence hdet p hp hp2
  dsimp only
  intro g hg hB s e u hpow a
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  by_cases heq3 : p = 3
  · have ha : a.val < 0 := by simpa [heq3] using a.isLt
    omega
  · have hp5 : 5 ≤ p := by
      obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
      omega
    let M : Matrix (Fin ((p - 3) / 2)) (Fin ((p - 3) / 2)) (ZMod p) :=
      fun j b => ((b.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1
    have hM : M.det ≠ 0 := hdet p hp3
    have hker : M.mulVec (fun b => (e b : ZMod p)) = 0 := by
      funext j
      have hbound : 2 * (j.val + 1) ≤ p - 3 := by have := j.isLt; omega
      have hnum : ((bernoulli (2 * (j.val + 1))).num : ZMod p) ≠ 0 := by
        intro hz
        exact hB (j.val + 1) (by omega) hbound
          ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
      exact (mul_eq_zero.mp (hcongruence p hp5 g hg s e u hpow j)).resolve_left hnum
    have hz := congr_fun (Matrix.eq_zero_of_mulVec_eq_zero hM hker) a
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e a) p).mp hz

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1
