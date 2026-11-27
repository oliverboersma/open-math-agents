import FormalConjectures.Wikipedia.AlgebraicNormality

-- Reduction AlgebraicNormality.irrational_algebraic_absolutely_normal.R1 of Normality of Irrational Algebraic Numbers — irrational algebraic absolutely normal
-- Credit: @sobrien032
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of absolute normality to integers and non-power bases

H1 is the rational-scaling case of Wall's theorem (1949): a nonzero rational multiple of a
number normal in base b is normal in base b. It reduces the problem from irrational algebraic
numbers to irrational algebraic integers, since some nonzero integer multiple of an algebraic
number is an algebraic integer.

H2 is the classical fact that normality in base b implies normality in every power base b ^ k.
Every base B at least 2 is a power c ^ j of a base c that is not itself a perfect power
(take the least such c), so H2 reduces the problem to bases that are not perfect powers.

H3 is the remaining open core: every irrational algebraic integer is normal in every base that
is not a perfect power.
-/

open AlgebraicNormality NormalNumber

namespace OMA.R_AlgebraicNormality_irrational_algebraic_absolutely_normal_R1

/-- Every base at least 2 is a power `c ^ j`, with `j ≥ 1`, of a base `c` that is not a perfect power. -/
private theorem exists_root_not_power {b : ℕ} (hb : 2 ≤ b) :
    ∃ c j : ℕ, 2 ≤ c ∧ 1 ≤ j ∧ (∀ d i : ℕ, 2 ≤ i → d ^ i ≠ c) ∧ c ^ j = b := by
  classical
  have hex : ∃ c, 2 ≤ c ∧ ∃ j, 1 ≤ j ∧ c ^ j = b := ⟨b, hb, 1, le_rfl, pow_one b⟩
  obtain ⟨hc2, j, hj, hcj⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, j, hc2, hj, ?_, hcj⟩
  intro d i hi hdi
  have hd2 : 2 ≤ d := by
    by_contra hd
    have hd' : d = 0 ∨ d = 1 := by omega
    rcases hd' with rfl | rfl
    · rw [zero_pow (by omega)] at hdi
      omega
    · rw [one_pow] at hdi
      omega
  have hlt : d < Nat.find hex := by
    calc d < d ^ 2 := by nlinarith
      _ ≤ d ^ i := Nat.pow_le_pow_right (by omega) hi
      _ = Nat.find hex := hdi
  exact Nat.find_min hex hlt
    ⟨hd2, i * j, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      by rw [pow_mul, hdi, hcj]⟩

def H1 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (x : ℝ) (r : ℚ), r ≠ 0 →
    IsNormalInBase b x → IsNormalInBase b ((r : ℝ) * x)

def H2 : Prop :=
  ∀ (b k : ℕ), 2 ≤ b → 1 ≤ k → ∀ x : ℝ,
    IsNormalInBase b x → IsNormalInBase (b ^ k) x

def H3 : Prop :=
  ∀ x : ℝ, IsIntegral ℤ x → Irrational x → ∀ b : ℕ, 2 ≤ b →
    (∀ c j : ℕ, 2 ≤ j → c ^ j ≠ b) → IsNormalInBase b x

theorem main : H1 → H2 → H3 → type_of% @AlgebraicNormality.irrational_algebraic_absolutely_normal := by
  intro hScale hPow hCore x hx b hb
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors ℤ) (Rₘ := ℚ) x hx.1.isIntegral
  have hm0 : (m : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp m.property
  have hyInt : IsIntegral ℤ (((m : ℤ) : ℝ) * x) := by
    simpa only [Submonoid.smul_def, zsmul_eq_mul] using hm
  have hyIrr : Irrational (((m : ℤ) : ℝ) * x) := hx.2.intCast_mul hm0
  obtain ⟨c, j, hc, hj, hcp, rfl⟩ := exists_root_not_power hb
  have hy := hCore _ hyInt hyIrr c hc hcp
  have hmQ : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hmR : ((m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hxc : IsNormalInBase c x := by
    have h := hScale c hc _ (((m : ℤ) : ℚ)⁻¹) (inv_ne_zero hmQ) hy
    simpa [← mul_assoc, inv_mul_cancel₀ hmR] using h
  exact hPow c j hc hj x hxc

end OMA.R_AlgebraicNormality_irrational_algebraic_absolutely_normal_R1
