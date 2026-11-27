import FormalConjectures.ErdosProblems.«143»
import Mathlib

/-
Erdős Problem 143 (ii): disproof, a formalization of a known result.
Source of the argument and of the original Lean proof: Mattia Apicella,
A rational counterexample to the reciprocal-logarithmic assertion in Erdős problem 143 (2026),
github.com/mapice/erdos-143-candidate-disproof, cited at erdosproblems.com/143.
Ported to the formal-conjectures toolchain (Lean 4.33.1) in one file; namespace renamed to Apicella143.
-/

-- module Apicella143.Definitions
noncomputable section
/-!
# Exact statements for the candidate for Erdős problem 143

This file defines the requested conclusion; it does not assert or prove it.
The weight is summed in `ENNReal`, so a divergent nonnegative series is
represented by `⊤`, rather than by Lean's default value for a divergent real tsum.
-/


open scoped BigOperators ENNReal

namespace Apicella143

/-- The quantifiers are over ordered distinct pairs and every positive integer. -/
def Original (A : Set ℚ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b|

/-- The nonnegative version of the logarithmic weight. -/
def weight (a : ℚ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((a : ℝ) * Real.log a))

def totalWeight (A : Set ℚ) : ℝ≥0∞ := ∑' a : A, weight a

/-- A primitive set of natural numbers, with the lower bound recorded separately. -/
def Primitive (P : Set ℕ) : Prop :=
  ∀ m ∈ P, ∀ n ∈ P, m ∣ n → m = n

/-- Every bounded initial interval contains only finitely many points. -/
def LocallyFiniteAbove (A : Set ℚ) : Prop :=
  ∀ x : ℚ, (A ∩ Set.Iic x).Finite

/-- The additional small positive displacement in the candidate. -/
def TinyPositiveDisplacement (a : ℚ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ 0 < a - m ∧ a - m ≤ 1 / (2 * (m : ℚ) ^ 12)

/-- The exact main existence claim. No proof is supplied by this definition. -/
def MainConclusion : Prop :=
  ∃ A : Set ℚ, A.Countable ∧ (∀ a ∈ A, (2 : ℚ) ≤ a) ∧
    Original A ∧ totalWeight A = ⊤

/-- The stronger existence claim made by the manuscript. -/
def StrongConclusion : Prop :=
  ∃ A : Set ℚ, A.Countable ∧ (∀ a ∈ A, (2 : ℚ) ≤ a) ∧
    Original A ∧ totalWeight A = ⊤ ∧ LocallyFiniteAbove A ∧
    ∀ a ∈ A, TinyPositiveDisplacement a

/-- Free lattice labels; the half-open interval is deliberately asymmetric. -/
def RightFree (F : Set ℚ) (D : ℕ) (n : ℕ) : Prop :=
  ∀ a ∈ F, ∀ k : ℤ, ¬ ((-1 : ℚ) < k * a - D * n ∧ k * a - D * n ≤ 1)

/-- The analytic finite-selection interface, proved by `periodicPrimitiveSelection_proved`. -/
def PeriodicPrimitiveSelection : Prop :=
  ∀ (L : ℕ) (_ : 0 < L) (S : Finset (Fin L)),
    (2 / 3 : ℚ) < (S.card : ℚ) / L →
    ∀ N : ℕ, 2 ≤ N → ∃ P : Finset ℕ,
      (∀ n ∈ P, N ≤ n ∧ (⟨n % L, Nat.mod_lt _ ‹0 < L›⟩ : Fin L) ∈ S) ∧
      Primitive (P : Set ℕ) ∧
      (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n

end Apicella143

end

-- module Apicella143.Arithmetic
noncomputable section
namespace Apicella143

lemma prime_not_dvd_finset_prod {α : Type*} (S : Finset α) (f : α → ℕ) {H : ℕ}
    (hH : H.Prime) (hS : ∀ x ∈ S, ¬ H ∣ f x) : ¬ H ∣ ∏ x ∈ S, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hH.not_dvd_one
  | @insert x S hx ih =>
    rw [Finset.prod_insert hx]
    exact hH.not_dvd_mul (hS x (by simp)) (ih (fun y hy => hS y (by simp [hy])))

/-- A single prime can exceed every member of any finite threshold list. -/
lemma exists_prime_above_finset (S : Finset ℕ) :
    ∃ H : ℕ, H.Prime ∧ ∀ x ∈ S, x < H := by
  obtain ⟨H, hlarge, hprime⟩ := Nat.exists_infinite_primes (S.sup id + 1)
  refine ⟨H, hprime, ?_⟩
  intro x hx
  have hxle : x ≤ S.sup id := Finset.le_sup (f := id) hx
  omega

/-- The current invariant forbids each private prime in every newly stored nonprivate part. -/
lemma private_prime_preserved {H G D n : ℕ} (hH : H.Prime)
    (hG : ¬ H ∣ G) (hD : ¬ H ∣ D) (hn : ¬ H ∣ n) : ¬ H ∣ G * D * n :=
  hH.not_dvd_mul (hH.not_dvd_mul hG hD) hn

/-- Choosing the new prime above all positive stored parts handles the reverse direction. -/
lemma fresh_prime_avoids_old_part {H N : ℕ} (hN : 0 < N) (hHN : N < H) : ¬ H ∣ N :=
  Nat.not_dvd_of_pos_of_lt hN hHN

/-- A product of the stored parts may replace their lcm. This proves the existence of
an arbitrarily large grid divisible by every stored part and avoiding every private prime. -/
lemma exists_private_compatible_grid (N H : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) (hH : ∀ h ∈ H, h.Prime ∧ 2 < h)
    (havoid : ∀ h ∈ H, ∀ n ∈ N, ¬ h ∣ n) (M : ℕ) :
    ∃ D : ℕ, M < D ∧ 48 ≤ D ∧ (∀ n ∈ N, n ∣ D) ∧ ∀ h ∈ H, ¬ h ∣ D := by
  classical
  let Q : ℕ := ∏ n ∈ N, n
  have hQ : 0 < Q := Finset.prod_pos hN
  obtain ⟨v, hv⟩ := pow_unbounded_of_one_lt (max M 48) (by decide : 1 < (2 : ℕ))
  refine ⟨2 ^ v * Q, ?_, ?_, ?_, ?_⟩
  · nlinarith [le_max_left M 48]
  · nlinarith [le_max_right M 48]
  · intro n hn
    exact (Finset.dvd_prod_of_mem id hn).trans (dvd_mul_left Q (2 ^ v))
  · intro h hh
    have hprime := (hH h hh).1
    have hnot2 : ¬ h ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (hH h hh).2
    have hnotpow : ¬ h ∣ 2 ^ v := fun hd => hnot2 (hprime.dvd_of_dvd_pow hd)
    have hnotQ : ¬ h ∣ Q := prime_not_dvd_finset_prod N id hprime (havoid h hh)
    exact hprime.not_dvd_mul hnotpow hnotQ

end Apicella143

end

-- module Apicella143.Geometry
noncomputable section
open scoped BigOperators ENNReal

namespace Apicella143

lemma original_mono {A B : Set ℚ} (hB : Original B) (hAB : A ⊆ B) : Original A := by
  intro a ha b hb hab k hk
  exact hB a (hAB ha) b (hAB hb) hab k hk

lemma original_empty : Original ∅ := by
  intro a ha
  simp at ha

lemma original_union {A B : Set ℚ} (hA : Original A) (hB : Original B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b|)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * b - a|) :
    Original (A ∪ B) := by
  intro a ha b hb hab k hk
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hA a ha b hb hab k hk
  · exact hAB a ha b hb k hk
  · exact hBA a ha b hb k hk
  · exact hB a ha b hb hab k hk

lemma new_source_separated {a b : ℚ} (hb : 0 ≤ b) (hab : a + 1 < b)
    {k : ℕ} (hk : 1 ≤ k) : 1 < |(k : ℚ) * b - a| := by
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hmul : b ≤ (k : ℚ) * b := by nlinarith
  have hpos : 0 < (k : ℚ) * b - a := by linarith
  rw [abs_of_pos hpos]
  linarith

/-- The fixed-denominator gap used for all multipliers simultaneously. -/
lemma rational_grid_gap {B : ℕ} (hB : 0 < B) {z : ℤ}
    (hz : (1 : ℚ) < (z : ℚ) / B) : 1 + 1 / (B : ℚ) ≤ (z : ℚ) / B := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hlt : (B : ℚ) < z := by simpa using (lt_div_iff₀ hBq).mp hz
  have hzint : (B : ℤ) + 1 ≤ z := by
    have : (B : ℤ) < z := by exact_mod_cast hlt
    omega
  have hzq : (B : ℚ) + 1 ≤ z := by exact_mod_cast hzint
  apply (le_div_iff₀ hBq).2
  calc
    (1 + 1 / (B : ℚ)) * B = B + 1 := by field_simp
    _ ≤ z := hzq

/-- Moving a free lattice point a small positive distance preserves its old-source gap. -/
lemma right_perturbation_safe {B : ℕ} (hB : 0 < B) {z : ℤ} {η : ℚ}
    (hfree : ¬ ((-1 : ℚ) < (z : ℚ) / B ∧ (z : ℚ) / B ≤ 1))
    (hη : 0 < η) (hηB : η < 1 / (B : ℚ)) :
    1 < |(z : ℚ) / B - η| := by
  by_cases hlo : (z : ℚ) / B ≤ -1
  · have hneg : (z : ℚ) / B - η < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · have hhi : (1 : ℚ) < (z : ℚ) / B := by
      by_contra! h
      exact hfree ⟨lt_of_not_ge hlo, h⟩
    have hgap := rational_grid_gap hB hhi
    have hpos : 0 < (z : ℚ) / B - η := by linarith
    rw [abs_of_pos hpos]
    linarith

/-- Separation inside a scaled primitive block, including both pair orders. -/
lemma scaled_primitive_original {P : Set ℕ} (hP : Primitive P) {c : ℚ}
    (hc : 1 ≤ c) : Original ((fun n : ℕ => c * n) '' P) := by
  intro a ha b hb hab k hk
  rcases ha with ⟨m, hm, rfl⟩
  rcases hb with ⟨n, hn, rfl⟩
  have hmn : m ≠ n := by rintro rfl; exact hab rfl
  have hdiff : (k : ℤ) * m - n ≠ 0 := by
    intro hzero
    have heq : n = m * k := by
      have heq' : (k : ℤ) * m = n := by omega
      exact_mod_cast (heq'.symm.trans (mul_comm _ _))
    have hdvd : m ∣ n := ⟨k, heq⟩
    exact hmn (hP m hm n hn hdvd)
  have habs : (1 : ℚ) ≤ |(k : ℚ) * m - n| := by
    have hi : (1 : ℤ) ≤ |(k : ℤ) * m - n| := by
      have : 0 < |(k : ℤ) * m - n| := abs_pos.mpr hdiff
      omega
    exact_mod_cast hi
  have hc0 : 0 ≤ c := by linarith
  calc
    1 ≤ c * |(k : ℚ) * m - n| := by nlinarith
    _ = |c * ((k : ℚ) * m - n)| := by rw [abs_mul, abs_of_nonneg hc0]
    _ = |(k : ℚ) * (c * m) - c * n| := by congr 1; ring

/-- The lattice-gap argument applied to a rational source in any (not necessarily reduced)
representation. Its statement quantifies over all integer multipliers. -/
lemma old_source_perturbation_safe {A : ℤ} {B : ℕ} (hB : 0 < B) {m : ℤ} {η : ℚ}
    (hfree : ∀ k : ℤ, ¬ ((-1 : ℚ) < k * ((A : ℚ) / B) - m ∧
      k * ((A : ℚ) / B) - m ≤ 1))
    (hη : 0 < η) (hηB : η < 1 / (B : ℚ)) :
    ∀ k : ℤ, 1 < |k * ((A : ℚ) / B) - ((m : ℚ) + η)| := by
  intro k
  have hid : (((k * A - m * B : ℤ) : ℚ) / B) = k * ((A : ℚ) / B) - m := by
    push_cast
    field_simp
  have hfree' : ¬ ((-1 : ℚ) < ((k * A - m * B : ℤ) : ℚ) / B ∧
      ((k * A - m * B : ℤ) : ℚ) / B ≤ 1) := by rw [hid]; exact hfree k
  have h := right_perturbation_safe hB hfree' hη hηB
  rw [hid] at h
  convert h using 2
  ring

/-- The discrete numerator in the private-prime argument is nonzero for every integer k. -/
lemma private_prime_numerator_ne_zero {H t q n : ℕ} (hH : H.Prime)
    (ht : ¬ H ∣ t) (hq : ¬ H ∣ q) (hn : ¬ H ∣ n) (k : ℤ) :
    k * H - (t : ℤ) * q * n ≠ 0 := by
  intro hz
  have hdZ : (H : ℤ) ∣ (t : ℤ) * q * n := ⟨k, by nlinarith⟩
  have hdN : H ∣ t * q * n := by exact_mod_cast hdZ
  exact (hH.not_dvd_mul (hH.not_dvd_mul ht hq) hn) hdN

/-- The exact private-grid spacing bound, with no assumption that a rational presentation
is reduced and no upper bound on the integer multiplier. -/
lemma private_grid_separated {H t q n D : ℕ} {a : ℚ} (hH : H.Prime)
    (ht : ¬ H ∣ t) (hq : ¬ H ∣ q) (hn : ¬ H ∣ n)
    (hspacing : 4 < a / H)
    (hrelation : (D : ℚ) * H = a * t * q) (k : ℤ) :
    4 < |(k : ℚ) * a - (D : ℚ) * n| := by
  have hHq : (H : ℚ) ≠ 0 := by exact_mod_cast hH.ne_zero
  have hid : (k : ℚ) * a - (D : ℚ) * n =
      (a / H) * ((k * H - (t : ℤ) * q * n : ℤ) : ℚ) := by
    push_cast
    field_simp
    nlinarith [hrelation]
  have hz := private_prime_numerator_ne_zero hH ht hq hn k
  have hi : (1 : ℤ) ≤ |k * H - (t : ℤ) * q * n| := by
    have := abs_pos.mpr hz
    omega
  have hiq : (1 : ℚ) ≤ |((k * H - (t : ℤ) * q * n : ℤ) : ℚ)| := by
    exact_mod_cast hi
  have haspace : 0 ≤ a / H := by linarith
  rw [hid, abs_mul, abs_of_nonneg haspace]
  nlinarith

/-- The natural-number formulation has exactly the same positive-integer quantifiers. -/
lemma original_iff_integer_multipliers (A : Set ℚ) :
    Original A ↔ ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ∀ k : ℤ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b| := by
  constructor
  · intro h a ha b hb hab k hk
    have hk0 : 0 ≤ k := by omega
    have hcast : ((k.toNat : ℕ) : ℚ) = (k : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hk0
    have hkn : 1 ≤ k.toNat := by omega
    simpa [hcast] using h a ha b hb hab k.toNat hkn
  · intro h a ha b hb hab k hk
    have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk
    simpa using h a ha b hb hab (k : ℤ) hkZ

/-- The rational inequalities are exactly the corresponding inequalities in the reals. -/
lemma original_iff_real_inequalities (A : Set ℚ) :
    Original A ↔ ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ |(k : ℝ) * (a : ℝ) - (b : ℝ)| := by
  constructor
  · intro h a ha b hb hab k hk
    exact_mod_cast h a ha b hb hab k hk
  · intro h a ha b hb hab k hk
    exact_mod_cast h a ha b hb hab k hk

end Apicella143

end

-- module Apicella143.Perturbation
noncomputable section
namespace Apicella143

/-- The chosen denominator gives the exact twelfth-power displacement bound. -/
lemma perturbation_bound {m U q : ℕ} (hm : 2 ≤ m) (hmU : m ≤ U)
    (hq : 2 * U ^ 13 ≤ q) :
    (m : ℚ) / q ≤ 1 / (2 * (m : ℚ) ^ 12) := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hU0 : 0 < U := by omega
  have hq0 : 0 < q := by
    have hpow : 0 < U ^ 13 := pow_pos hU0 _
    omega
  have hq0q : (0 : ℚ) < q := by exact_mod_cast hq0
  have hp : m ^ 13 ≤ U ^ 13 := Nat.pow_le_pow_left hmU 13
  have hpq : (m : ℚ) ^ 13 ≤ (U : ℚ) ^ 13 := by exact_mod_cast hp
  have hqq : 2 * (U : ℚ) ^ 13 ≤ q := by exact_mod_cast hq
  apply (div_le_div_iff₀ hq0q (by positivity : (0 : ℚ) < 2 * (m : ℚ) ^ 12)).2
  nlinarith [show (m : ℚ) ^ 13 = (m : ℚ) ^ 12 * m from pow_succ _ _]

lemma perturbed_point_tiny {m U q : ℕ} (hm : 2 ≤ m) (hmU : m ≤ U)
    (hq : 2 * U ^ 13 ≤ q) : TinyPositiveDisplacement ((m : ℚ) + (m : ℚ) / q) := by
  refine ⟨m, hm, ?_, ?_⟩
  · have hm0 : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    have hU0 : 0 < U := by omega
    have hq0 : 0 < q := by
      have hpow : 0 < U ^ 13 := pow_pos hU0 _
      omega
    have hq0q : (0 : ℚ) < q := by exact_mod_cast hq0
    simpa using div_pos hm0 hq0q
  · simpa using perturbation_bound hm hmU hq

end Apicella143

end

-- module Apicella143.Weight
noncomputable section
open scoped ENNReal

namespace Apicella143

/-- The quantitative block estimate from §8, over the reals before taking nonnegative sums. -/
lemma scaled_real_weight_lower_bound {c D n : ℝ} (hc : 1 < c) (hc2 : c < 2)
    (hD : 1 ≤ D) (hn : 2 * D ≤ n) :
    (1 / (n * Real.log n)) / (4 * D) ≤ 1 / ((c * D * n) * Real.log (c * D * n)) := by
  have hD0 : 0 < D := by linarith
  have hn1 : 1 < n := by linarith
  have hn0 : 0 < n := by linarith
  have hc0 : 0 < c := by linarith
  have hcd1 : 1 ≤ c * D := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ c * D := mul_le_mul hc.le hD (by norm_num) hc0.le
  have hncn : n ≤ c * D * n := by
    simpa using mul_le_mul_of_nonneg_right hcd1 hn0.le
  have hcn : 1 < c * D * n := hn1.trans_le hncn
  have hcn0 : 0 < c * D * n := by positivity
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hlogcn : 0 < Real.log (c * D * n) := Real.log_pos hcn
  have hcdn : c * D ≤ n := (mul_le_mul_of_nonneg_right hc2.le hD0.le).trans hn
  have hcnle : c * D * n ≤ n ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcdn hn0.le]
  have hlog : Real.log (c * D * n) ≤ 2 * Real.log n := by
    have h := Real.log_le_log hcn0 hcnle
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hscale : c * D * n ≤ 2 * D * n := by nlinarith
  have hprod := mul_le_mul hscale hlog hlogcn.le (by positivity : (0 : ℝ) ≤ 2 * D * n)
  have hden : (c * D * n) * Real.log (c * D * n) ≤ 4 * D * (n * Real.log n) := by
    nlinarith [hprod]
  calc
    (1 / (n * Real.log n)) / (4 * D) = 1 / (4 * D * (n * Real.log n)) := by
      rw [div_div]
      congr 1
      ring
    _ ≤ 1 / ((c * D * n) * Real.log (c * D * n)) :=
      one_div_le_one_div_of_le (by positivity) hden

/-- Positivity ensures that `ofReal` does not discard any term in the requested range. -/
lemma real_weight_pos {a : ℚ} (ha : (2 : ℚ) ≤ a) :
    0 < 1 / ((a : ℝ) * Real.log a) := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
  positivity

lemma weight_pos {a : ℚ} (ha : (2 : ℚ) ≤ a) : 0 < weight a := by
  exact ENNReal.ofReal_pos.mpr (real_weight_pos ha)

/-- Every individual term is finite; divergence cannot come from an infinite summand. -/
lemma weight_ne_top (a : ℚ) : weight a ≠ ⊤ := ENNReal.ofReal_ne_top

/-- A complete round contains enough blocks for the uniform gain. -/
lemma round_blocks_lower_bound {D : ℕ} (hD : 48 ≤ D) : (D : ℚ) / 24 ≤ ((D / 12 : ℕ) : ℚ) := by
  have hq : D < 12 * (D / 12 + 1) := Nat.lt_mul_div_succ D (by decide : 0 < 12)
  have hQ : 2 * (D / 12) * 12 ≥ D := by omega
  have hQrat : (2 : ℚ) * (D / 12 : ℕ) * 12 ≥ D := by exact_mod_cast hQ
  linarith

/-- The same block estimate for the actual extended-nonnegative weight used in the target. -/
lemma scaled_weight_lower_bound {c : ℚ} {D n : ℕ} (hc : 1 < c) (hc2 : c < 2)
    (hD : 1 ≤ D) (hn : 2 * D ≤ n) :
    weight n / (4 * (D : ℝ≥0∞)) ≤ weight (c * D * n) := by
  have hcR : (1 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hc2R : (c : ℝ) < 2 := by exact_mod_cast hc2
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hnR : (2 : ℝ) * D ≤ n := by exact_mod_cast hn
  have h := ENNReal.ofReal_le_ofReal (scaled_real_weight_lower_bound hcR hc2R hDR hnR)
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 4 * D)] at h
  simpa [weight, ENNReal.ofReal_mul, Nat.cast_nonneg] using h

end Apicella143

end

-- module Apicella143.NestedUnion
noncomputable section
open scoped BigOperators ENNReal

namespace Apicella143

/-- Every pair is captured by one prefix; the bound holds for every k, without a cutoff. -/
lemma original_iUnion_of_monotone {F : ℕ → Set ℚ} (hmono : Monotone F)
    (hF : ∀ i, Original (F i)) : Original (⋃ i, F i) := by
  intro a ha b hb hab k hk
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  exact hF (max i j) a (hmono (le_max_left i j) hi)
    b (hmono (le_max_right i j) hj) hab k hk

/-- A rational set is countable without any extra enumeration hypothesis. -/
lemma rational_set_countable (A : Set ℚ) : A.Countable := Set.to_countable A

lemma lower_bound_iUnion {F : ℕ → Set ℚ} (hF : ∀ i, ∀ a ∈ F i, (2 : ℚ) ≤ a) :
    ∀ a ∈ ⋃ i, F i, (2 : ℚ) ≤ a := by
  intro a ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  exact hF i a hi

lemma totalWeight_mono {A B : Set ℚ} (hAB : A ⊆ B) : totalWeight A ≤ totalWeight B := by
  let f : A → B := fun a => ⟨a.val, hAB a.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : B => x.val) h
  exact ENNReal.tsum_comp_le_tsum_of_injective hf (fun b : B => weight b)

/-- Arbitrarily large finite-prefix weights force the actual nonnegative series to diverge. -/
lemma totalWeight_iUnion_eq_top_of_unbounded {F : ℕ → Set ℚ}
    (hF : ∀ n : ℕ, ∃ i : ℕ, (n : ℝ≥0∞) < totalWeight (F i)) :
    totalWeight (⋃ i, F i) = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  obtain ⟨i, hi⟩ := hF n
  exact hi.le.trans (totalWeight_mono (Set.subset_iUnion F i))

/-- The manuscript's precise round bound suffices; 576 is kept explicit. -/
lemma totalWeight_iUnion_eq_top_of_round_bound {F : ℕ → Set ℚ}
    (hF : ∀ R : ℕ, 1 ≤ R → (R : ℝ≥0∞) / 576 < totalWeight (F R)) :
    totalWeight (⋃ i, F i) = ⊤ := by
  apply totalWeight_iUnion_eq_top_of_unbounded
  intro n
  refine ⟨(n + 1) * 576, ?_⟩
  have hR : 1 ≤ (n + 1) * 576 := by omega
  have h := hF ((n + 1) * 576) hR
  have heq : (((n + 1) * 576 : ℕ) : ℝ≥0∞) / 576 = (n : ℝ≥0∞) + 1 := by
    push_cast
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  rw [heq] at h
  exact (le_add_right le_rfl).trans_lt h

/-- For a finite prefix the subtype sum is exactly its usual finite sum. -/
lemma totalWeight_finset (F : Finset ℚ) : totalWeight (F : Set ℚ) = ∑ a ∈ F, weight a := by
  rw [totalWeight, tsum_fintype]
  exact Finset.sum_coe_sort F weight

end Apicella143

end

-- module Apicella143.BlockWeight
noncomputable section
open scoped ENNReal BigOperators

namespace Apicella143

/-- The finite primitive-selection weight, once supplied, yields the exact claimed block gain.
Primitivity is irrelevant to this weight calculation and is handled separately by geometry. -/
lemma block_weight_lower_bound (P : Finset ℕ) {c : ℚ} {D : ℕ}
    (hc : 1 < c) (hc2 : c < 2) (hD : 1 ≤ D) (hn : ∀ n ∈ P, 2 * D ≤ n)
    (hweight : (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n) :
    (1 : ℝ≥0∞) / (24 * D) <
      totalWeight ((P.image (fun n : ℕ => c * D * n) : Finset ℚ) : Set ℚ) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast (by omega : 0 < D)
  have hcq : (0 : ℚ) < c := by linarith
  have hcD : c * (D : ℚ) ≠ 0 := ne_of_gt (mul_pos hcq hDq)
  have hinj : Function.Injective (fun n : ℕ => c * D * n) := by
    intro n m hnm
    exact_mod_cast (mul_left_cancel₀ hcD hnm)
  have himage : totalWeight ((P.image (fun n : ℕ => c * D * n) : Finset ℚ) : Set ℚ) =
      ∑ n ∈ P, weight (c * D * n) := by
    rw [totalWeight_finset, Finset.sum_image]
    intro a ha b hb hab
    exact hinj hab
  have hsum : (∑ n ∈ P, weight n) / (4 * (D : ℝ≥0∞)) ≤
      ∑ n ∈ P, weight (c * D * n) := by
    calc
      _ = ∑ n ∈ P, weight n / (4 * (D : ℝ≥0∞)) := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum (fun n hnp => scaled_weight_lower_bound hc hc2 hD (hn n hnp))
  have hD0 : (4 * (D : ℝ≥0∞)) ≠ 0 := by
    have hd : D ≠ 0 := by omega
    simp [hd]
  have hDt : (4 * (D : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (by simp)
  rw [himage]
  calc
    (1 : ℝ≥0∞) / (24 * D) = (1 / 6) / (4 * (D : ℝ≥0∞)) := by
      rw [show (24 : ℝ≥0∞) * D = 6 * (4 * D) by ring]
      simp only [div_eq_mul_inv, one_mul]
      exact ENNReal.mul_inv (a := 6) (b := 4 * D) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    _ < (∑ n ∈ P, weight n) / (4 * (D : ℝ≥0∞)) :=
      ENNReal.div_lt_div_right hD0 hDt hweight
    _ ≤ _ := hsum

end Apicella143

end

-- module Apicella143.FiniteDensity
noncomputable section
open scoped BigOperators
namespace Apicella143

/-- A surjective homomorphism between finite additive groups preserves uniform density. -/
lemma preimage_density_of_surjective {G M : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    [AddGroup M] [Fintype M] [DecidableEq M] (f : G →+ M) (hf : Function.Surjective f)
    (S : Finset M) :
    ((Finset.univ.filter (fun x => f x ∈ S)).card : ℚ) / Fintype.card G =
      (S.card : ℚ) / Fintype.card M := by
  classical
  let K := (Finset.univ.filter (fun x => f x = 0)).card
  have hfiber (b : M) : (Finset.univ.filter (fun x => f x = b)).card = K :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf 0)
  have hall : Fintype.card G = Fintype.card M * K := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset M))
      (f := f) (by intro x hx; exact Finset.mem_univ _)
    simpa only [Finset.card_univ, hfiber, Finset.sum_const, Finset.card_univ,
      smul_eq_mul] using h
  have hpart : (Finset.univ.filter (fun x => f x ∈ S)).card = S.card * K := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun x => f x ∈ S)) (t := S) (f := f)
      (by intro x hx; exact (Finset.mem_filter.mp hx).2)
    have heq (b : M) (hb : b ∈ S) :
        {a ∈ Finset.univ.filter (fun x => f x ∈ S) | f a = b} =
          Finset.univ.filter (fun x => f x = b) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro hxb
      simpa [hxb] using hb
    rw [h]
    calc
      _ = ∑ _b ∈ S, K := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [heq b hb, hfiber]
      _ = _ := by simp only [Finset.sum_const, smul_eq_mul]
  have hK : K ≠ 0 := by
    intro h
    have := Fintype.card_pos (α := G)
    simp [h] at hall
  rw [hpart, hall]
  push_cast
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hK)

/-- Pulling back any set of residues to a multiple period keeps its density. -/
lemma zmod_preimage_density {L m : ℕ} [NeZero L] [NeZero m]
    (h : m ∣ L) (S : Finset (ZMod m)) :
    ((Finset.univ.filter (fun x : ZMod L => ZMod.castHom h (ZMod m) x ∈ S)).card : ℚ) / L =
      (S.card : ℚ) / m := by
  have key := preimage_density_of_surjective
    (ZMod.castHom h (ZMod m)).toAddMonoidHom (ZMod.castHom_surjective h) S
  simp only [ZMod.card] at key
  exact key

/-- The elementary union bound, expressed as the density of the complementary filter. -/
lemma complement_union_density {α ι : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (I : Finset ι) (B : ι → Finset α) :
    1 - ∑ i ∈ I, ((B i).card : ℚ) / Fintype.card α ≤
      (((I.biUnion B)ᶜ).card : ℚ) / Fintype.card α := by
  classical
  have hcard := (Finset.card_biUnion_le (s := I) (t := B))
  have hle := Finset.card_le_univ (I.biUnion B)
  have hpos : (0 : ℚ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  rw [Finset.card_compl, Nat.cast_sub hle, ← Finset.sum_div]
  apply (le_div_iff₀ hpos).mpr
  have hc : ((I.biUnion B).card : ℚ) ≤ ∑ i ∈ I, ((B i).card : ℚ) := by
    exact_mod_cast hcard
  field_simp
  linarith

end Apicella143

end

-- module Apicella143.EulerFactorBounds
noncomputable section
/-!
Elementary factor inequalities for an alternative Abel-average proof.
They do not assert the remaining infinite-product or periodic-selection result.
-/

namespace Apicella143

lemma rpow_one_add_le_linear {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) :
    (1 + x) ^ u ≤ 1 + u * x := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - u) (w₂ := u) (p₁ := 1) (p₂ := 1 + x)
    (by linarith) hu0 (by norm_num) (by linarith) (by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at h
  nlinarith

lemma rpow_one_sub_le_linear {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hx : x < 1) :
    (1 - x) ^ u ≤ 1 - u * x := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - u) (w₂ := u) (p₁ := 1) (p₂ := 1 - x)
    (by linarith) hu0 (by norm_num) (by linarith) (by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at h
  nlinarith

/-- Lower comparison of the positive generating-function Euler factor with a squarefree factor. -/
lemma positive_euler_factor_lower {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : (1 + x) ^ u ≤ (1 - u * x)⁻¹ := by
  have hux : u * x < 1 := (mul_le_mul_of_nonneg_right hu1 hx0).trans_lt (by simpa using hx1)
  have hden : 0 < 1 - u * x := by linarith
  calc
    (1 + x) ^ u ≤ 1 + u * x := rpow_one_add_le_linear hu0 hu1 hx0
    _ ≤ (1 - u * x)⁻¹ := by
      rw [← one_div, le_div_iff₀ hden]
      nlinarith [sq_nonneg (u * x)]

/-- Upper comparison with the u-th power of the ordinary Euler factor. -/
lemma positive_euler_factor_upper {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hx1 : x < 1) : (1 - u * x)⁻¹ ≤ ((1 - x) ^ u)⁻¹ := by
  have hp : 0 < (1 - x) ^ u := Real.rpow_pos_of_pos (by linarith) _
  have hle := rpow_one_sub_le_linear hu0 hu1 hx1
  simpa only [one_div] using one_div_le_one_div_of_le hp hle

lemma complex_norm_sq_interpolation (u : ℝ) (z : ℂ) :
    ‖1 - (u : ℂ) * z‖ ^ 2 =
      (1 - u) + u * ‖1 - z‖ ^ 2 - u * (1 - u) * ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- A uniform twisted-factor bound needing no choice of a complex logarithm.
The correction factors have a convergent Euler product when |z_p| ≤ 1/p. -/
lemma complex_euler_factor_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    (‖1 - z‖ ^ 2) ^ u * (1 - ‖z‖ ^ 2) ≤ ‖1 - (u : ℂ) * z‖ ^ 2 := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hnorm : (1 : ℝ) - ‖z‖ ≤ ‖1 - z‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) z
  have hnorm0 : 0 ≤ ‖1 - z‖ := norm_nonneg _
  have hA : (1 / 4 : ℝ) ≤ ‖1 - z‖ ^ 2 := by nlinarith
  have hS : (1 / 4 : ℝ) ≤ (1 - u) + u * ‖1 - z‖ ^ 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hA)]
  have hvar : u * (1 - u) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hcorrection : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  have hmean := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - u) (w₂ := u) (p₁ := 1) (p₂ := ‖1 - z‖ ^ 2)
    (by linarith) hu0 (by norm_num) (sq_nonneg _) (by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at hmean
  have hproduct := mul_le_mul_of_nonneg_right hmean hcorrection
  have hvariance := mul_le_mul_of_nonneg_right (hvar.trans hS) (sq_nonneg ‖z‖)
  rw [complex_norm_sq_interpolation]
  nlinarith [hproduct, hvariance]

/-- The inverse-factor estimate in the form used for finite Euler products. -/
lemma complex_inverse_euler_factor_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - (u : ℂ) * z)⁻¹‖ ^ 2 ≤
      ‖(1 - z)⁻¹‖ ^ (2 * u) * (1 - ‖z‖ ^ 2)⁻¹ := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hnorm : (1 : ℝ) - ‖z‖ ≤ ‖1 - z‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) z
  have hbase : 0 < ‖1 - z‖ := by linarith
  have hcor : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  have hpow : 0 < (‖1 - z‖ ^ 2) ^ u :=
    Real.rpow_pos_of_pos (pow_pos hbase _) _
  have hi := one_div_le_one_div_of_le (mul_pos hpow hcor)
    (complex_euler_factor_lower hu0 hu1 hz)
  rw [norm_inv, inv_pow]
  simp only [one_div, mul_inv_rev] at hi
  calc
    (‖1 - (u : ℂ) * z‖ ^ 2)⁻¹ ≤
        (1 - ‖z‖ ^ 2)⁻¹ * ((‖1 - z‖ ^ 2) ^ u)⁻¹ := hi
    _ = ‖(1 - z)⁻¹‖ ^ (2 * u) * (1 - ‖z‖ ^ 2)⁻¹ := by
      rw [norm_inv, Real.inv_rpow (norm_nonneg _), Real.rpow_mul (norm_nonneg _), Real.rpow_two]
      ring

/-- A finite product version; all correction factors stay positive. -/
lemma complex_finite_euler_product_upper {ι : Type*} (S : Finset ι)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖∏ i ∈ S, (1 - (u : ℂ) * z i)⁻¹‖ ^ 2 ≤
      ‖∏ i ∈ S, (1 - z i)⁻¹‖ ^ (2 * u) * ∏ i ∈ S, (1 - ‖z i‖ ^ 2)⁻¹ := by
  have h := Finset.prod_le_prod
    (fun i hi => sq_nonneg ‖(1 - (u : ℂ) * z i)⁻¹‖)
    (fun i hi => complex_inverse_euler_factor_upper hu0 hu1 (hz i hi))
  simpa only [Finset.prod_mul_distrib, Finset.prod_pow, Real.finset_prod_rpow S
    (fun i => ‖(1 - z i)⁻¹‖) (fun _ _ => norm_nonneg _) (2 * u), norm_prod] using h

/-- Passing the finite comparison to convergent products does not need nonvanishing of L.
The rpow exponent is nonnegative, so the limiting norm may even be zero. -/
lemma complex_euler_product_upper {ι : Type*} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2) {F L : ℂ} {Q : ℝ}
    (hF : HasProd (fun i => (1 - (u : ℂ) * z i)⁻¹) F)
    (hL : HasProd (fun i => (1 - z i)⁻¹) L)
    (hQ : HasProd (fun i => (1 - ‖z i‖ ^ 2)⁻¹) Q) :
    ‖F‖ ^ 2 ≤ ‖L‖ ^ (2 * u) * Q := by
  change Filter.Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - (u : ℂ) * z i)⁻¹)
    Filter.atTop (nhds F) at hF
  change Filter.Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - z i)⁻¹)
    Filter.atTop (nhds L) at hL
  change Filter.Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - ‖z i‖ ^ 2)⁻¹)
    Filter.atTop (nhds Q) at hQ
  exact le_of_tendsto_of_tendsto (hF.norm.pow 2)
    ((hL.norm.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ 2 * u))).mul hQ)
    (Filter.Eventually.of_forall (fun S => complex_finite_euler_product_upper S hu0 hu1 z
      (fun i _ => hz i)))

end Apicella143

end

-- module Apicella143.CorrectionProducts
noncomputable section
open scoped BigOperators NNReal

namespace Apicella143

/-- A telescoping product controls all quadratic Euler remainders, even over all integers. -/
lemma correction_product_range (N : ℕ) :
    (∏ n ∈ Finset.range N, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹) =
      2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 3 ≠ 0 := by positivity
    have hfac : (1 - (((N : ℝ) + 2) ^ 2)⁻¹)⁻¹ =
        ((N : ℝ) + 2) ^ 2 / (((N : ℝ) + 1) * ((N : ℝ) + 3)) := by
      apply inv_injective
      rw [inv_inv, inv_div]
      field_simp
      ring
    rw [hfac]
    push_cast
    field_simp
    ring

lemma correction_factor_one_le (n : ℕ) : (1 : ℝ) ≤ (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
  have hpow : (1 : ℝ) < ((n : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hi : (((n : ℝ) + 2) ^ 2)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).2 hpow
  apply (one_le_inv₀ (by linarith : (0 : ℝ) < 1 - (((n : ℝ) + 2) ^ 2)⁻¹)).2
  have : 0 ≤ (((n : ℝ) + 2) ^ 2)⁻¹ := by positivity
  linarith

lemma correction_product_finset_le_two (S : Finset ℕ) :
    (∏ n ∈ S, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹) ≤ 2 := by
  let N := S.sup id + 1
  have hsub : S ⊆ Finset.range N := by
    intro n hn
    have hle : n ≤ S.sup id := Finset.le_sup (f := id) hn
    simp only [Finset.mem_range]
    omega
  calc
    _ ≤ ∏ n ∈ Finset.range N, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
      let f : ℕ → ℝ≥0 := fun n => ⟨(1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹,
        (by linarith [correction_factor_one_le n])⟩
      have hle : (∏ n ∈ S, f n) ≤ ∏ n ∈ Finset.range N, f n :=
        Finset.prod_le_prod_of_subset_of_one_le' hsub
          (fun n _ _ => correction_factor_one_le n)
      have h2 := NNReal.coe_le_coe.mpr hle
      rw [NNReal.coe_prod, NNReal.coe_prod] at h2
      exact h2
    _ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := correction_product_range N
    _ ≤ 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < N + 2)).2
      linarith

lemma prime_reciprocal_le_half (p : Nat.Primes) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp

lemma correction_factor_mono {r R : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R) (hR : R ≤ 1 / 2) :
    (1 - r ^ 2)⁻¹ ≤ (1 - R ^ 2)⁻¹ := by
  have hR0 : 0 ≤ R := hr0.trans hrR
  have hpos : 0 < 1 - R ^ 2 := by nlinarith
  have hsquare : r ^ 2 ≤ R ^ 2 := by nlinarith
  simpa only [one_div] using one_div_le_one_div_of_le hpos (sub_le_sub_left hsquare 1)

/-- No prime-distribution theorem is needed for the uniform quadratic correction. -/
lemma prime_correction_product_le_two (S : Finset Nat.Primes) (z : Nat.Primes → ℂ)
    (hz : ∀ p ∈ S, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    (∏ p ∈ S, (1 - ‖z p‖ ^ 2)⁻¹) ≤ 2 := by
  classical
  let e : Nat.Primes → ℕ := fun p => (p : ℕ) - 2
  have heinj : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    change (p : ℕ) - 2 = (q : ℕ) - 2 at hpq
    omega
  have hecast (p : Nat.Primes) : ((e p : ℕ) : ℝ) + 2 = (p : ℝ) := by
    have h : e p + 2 = (p : ℕ) := Nat.sub_add_cancel p.property.two_le
    exact_mod_cast h
  calc
    _ ≤ ∏ p ∈ S, (1 - ((((e p : ℕ) : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        have hnorm : ‖z p‖ ≤ 1 / 2 := (hz p hp).trans (prime_reciprocal_le_half p)
        have : 0 < 1 - ‖z p‖ ^ 2 := by nlinarith [norm_nonneg (z p)]
        positivity
      · intro p hp
        rw [hecast]
        simpa only [inv_pow] using correction_factor_mono (norm_nonneg _) (hz p hp)
          (prime_reciprocal_le_half p)
    _ = ∏ n ∈ S.image e, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
      rw [Finset.prod_image]
      intro p hp q hq hpq
      exact heinj hpq
    _ ≤ 2 := correction_product_finset_le_two (S.image e)

end Apicella143

end

-- module Apicella143.PositiveEulerBound
noncomputable section
open scoped BigOperators Topology

namespace Apicella143

lemma positive_finite_euler_product_lower (S : Finset Nat.Primes) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : Nat.Primes → ℝ)
    (hx0 : ∀ p ∈ S, 0 ≤ x p) (hx : ∀ p ∈ S, x p ≤ (p : ℝ)⁻¹) :
    ((∏ p ∈ S, (1 - x p)⁻¹) / 2) ^ u ≤ ∏ p ∈ S, (1 - u * x p)⁻¹ := by
  have hhalf : ∀ p ∈ S, x p ≤ 1 / 2 := fun p hp => (hx p hp).trans (prime_reciprocal_le_half p)
  have hcor : (∏ p ∈ S, (1 - (x p) ^ 2)⁻¹) ≤ 2 := by
    have h := prime_correction_product_le_two S (fun p => (x p : ℂ)) (fun p hp => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx0 p hp)] using hx p hp)
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  have hidentity : (∏ p ∈ S, (1 + x p)) * (∏ p ∈ S, (1 - (x p) ^ 2)⁻¹) =
      ∏ p ∈ S, (1 - x p)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 := hx0 p hp
    have hp1 := hhalf p hp
    have h1 : 1 - x p ≠ 0 := by linarith
    have h2 : 1 - (x p) ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  have hA : 0 ≤ ∏ p ∈ S, (1 + x p) := Finset.prod_nonneg (fun p hp => by linarith [hx0 p hp])
  have hZ : 0 ≤ ∏ p ∈ S, (1 - x p)⁻¹ := Finset.prod_nonneg (fun p hp => by
    apply inv_nonneg.mpr
    linarith [hhalf p hp])
  have hcompare : (∏ p ∈ S, (1 - x p)⁻¹) / 2 ≤ ∏ p ∈ S, (1 + x p) := by
    have hmul := mul_le_mul_of_nonneg_left hcor hA
    rw [hidentity] at hmul
    linarith
  calc
    _ ≤ (∏ p ∈ S, (1 + x p)) ^ u := Real.rpow_le_rpow (by positivity) hcompare hu0
    _ = ∏ p ∈ S, (1 + x p) ^ u :=
      (Real.finset_prod_rpow S (fun p => 1 + x p) (fun p hp => by linarith [hx0 p hp]) u).symm
    _ ≤ _ := Finset.prod_le_prod (fun p hp => Real.rpow_nonneg (by linarith [hx0 p hp]) _)
      (fun p hp => positive_euler_factor_lower hu0 hu1 (hx0 p hp) (by linarith [hhalf p hp]))

lemma positive_euler_product_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x : Nat.Primes → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx : ∀ p, x p ≤ (p : ℝ)⁻¹)
    {F Z : ℝ} (hF : HasProd (fun p => (1 - u * x p)⁻¹) F)
    (hZ : HasProd (fun p => (1 - x p)⁻¹) Z) : (Z / 2) ^ u ≤ F := by
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - u * x p)⁻¹)
    Filter.atTop (nhds F) at hF
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - x p)⁻¹)
    Filter.atTop (nhds Z) at hZ
  exact le_of_tendsto_of_tendsto ((hZ.div_const 2).rpow_const (Or.inr hu0)) hF
    (Filter.Eventually.of_forall (fun S => positive_finite_euler_product_lower S hu0 hu1 x
      (fun p _ => hx0 p) (fun p _ => hx p)))

end Apicella143

end

-- module Apicella143.GeneratingEulerProducts
noncomputable section
open scoped ArithmeticFunction.Omega
open Complex

namespace Apicella143

/-- The completely multiplicative Ω weight, with the required zero convention. -/
def omegaWeightHom (u : ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else u ^ Ω n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp [hm, hn, mul_ne_zero hm hn, ArithmeticFunction.cardFactors_mul hm hn, pow_add]

lemma omegaWeightHom_apply {u : ℂ} {n : ℕ} (hn : n ≠ 0) :
    omegaWeightHom u n = u ^ Ω n := by simp [omegaWeightHom, hn]

lemma omegaWeightHom_norm_le_one {u : ℂ} (hu : ‖u‖ ≤ 1) (n : ℕ) :
    ‖omegaWeightHom u n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [omegaWeightHom_apply hn, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hu

/-- Completely multiplicative twisted generating summand. -/
def generatingSummandHom {L : ℕ} (χ : DirichletCharacter ℂ L) (u : ℂ)
    {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := omegaWeightHom u n * dirichletSummandHom χ hs n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by simp only [map_mul]; ring

lemma generatingSummand_norm_summable {L : ℕ} (χ : DirichletCharacter ℂ L)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun n => ‖generatingSummandHom χ u (ne_zero_of_one_lt_re hs) n‖) := by
  apply (summable_dirichletSummand χ hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  change ‖omegaWeightHom u n * dirichletSummandHom χ _ n‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (omegaWeightHom_norm_le_one hu n)

/-- Euler product for the Ω generating series in the full absolute-convergence region needed
by the real Abel-parameter route. -/
lemma generating_eulerProduct_hasProd {L : ℕ} (χ : DirichletCharacter ℂ L)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      (1 - generatingSummandHom χ u (ne_zero_of_one_lt_re hs) p)⁻¹)
      (∑' n, generatingSummandHom χ u (ne_zero_of_one_lt_re hs) n) :=
  EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (generatingSummand_norm_summable χ hu hs)

lemma generatingSummand_at_prime {L : ℕ} (χ : DirichletCharacter ℂ L)
    {u s : ℂ} (hs : s ≠ 0) (p : Nat.Primes) :
    generatingSummandHom χ u hs p = u * (χ p * (p : ℂ) ^ (-s)) := by
  simp [generatingSummandHom, omegaWeightHom, p.property.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime p.property, dirichletSummandHom]

/-- A parameter-independent presentation of the generating series. -/
def generatingValue {L : ℕ} (χ : DirichletCharacter ℂ L) (u s : ℂ) : ℂ :=
  ∑' n : ℕ, omegaWeightHom u n * (χ n * (n : ℂ) ^ (-s))

lemma generatingValue_eq_tsum {L : ℕ} (χ : DirichletCharacter ℂ L) (u : ℂ)
    {s : ℂ} (hs : s ≠ 0) :
    generatingValue χ u s = ∑' n, generatingSummandHom χ u hs n := rfl

end Apicella143

end

-- module Apicella143.AnalyticInputs
noncomputable section
/-!
These are checked applications of existing mathlib theorems. They are not a proof
of the bespoke weighted periodic-selection lemma.
-/

namespace Apicella143

/-- Nonvanishing on the real segment, including its endpoint at 1. -/
lemma nonprincipal_LFunction_nonzero_segment {L : ℕ} [NeZero L]
    (χ : DirichletCharacter ℂ L) (hχ : χ ≠ 1) {t : ℝ} (ht : 0 ≤ t) :
    χ.LFunction (1 + (t : ℂ)) ≠ 0 := by
  apply χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ)
  simpa using ht

/-- Continuation near the segment is available as an entire function for a nonprincipal character. -/
lemma nonprincipal_LFunction_continuous {L : ℕ} [NeZero L]
    (χ : DirichletCharacter ℂ L) (hχ : χ ≠ 1) : Continuous χ.LFunction :=
  (DirichletCharacter.differentiable_LFunction hχ).continuous

end Apicella143

end

-- module Apicella143.TwistedBound
noncomputable section
open Complex
open scoped Topology

namespace Apicella143

lemma dirichlet_prime_factor_norm_le_reciprocal {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) p‖ ≤ (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  change ‖χ p * (p : ℂ) ^ (-s)‖ ≤ _
  rw [norm_mul]
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (by positivity)
      (re_neg_ne_zero_of_one_lt_re hs), neg_re]
  rw [hnorm]
  calc
    ‖χ p‖ * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-s.re) :=
      mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (χ.norm_le_one p)
    _ ≤ (p : ℝ)⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le hp (show -s.re ≤ (-1 : ℝ) by linarith)
      simpa only [Real.rpow_neg_one] using h

/-- Uniform generating-function norm bound from a genuine Euler product and a telescoping
quadratic correction. No complex logarithm or L(1,χ) nonvanishing is assumed. -/
lemma generating_norm_sq_le_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖∑' n, generatingSummandHom χ (u : ℂ) (ne_zero_of_one_lt_re hs) n‖ ^ 2 ≤
      2 * ‖LSeries (fun n : ℕ => (χ n : ℂ)) s‖ ^ (2 * u) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] using hu1
  let z : Nat.Primes → ℂ := fun p => dirichletSummandHom χ (ne_zero_of_one_lt_re hs) p
  have hz : ∀ p, ‖z p‖ ≤ (p : ℝ)⁻¹ := dirichlet_prime_factor_norm_le_reciprocal χ hs
  have hhalf : ∀ p, ‖z p‖ ≤ 1 / 2 := fun p => (hz p).trans (prime_reciprocal_le_half p)
  have hF := generating_eulerProduct_hasProd χ hu hs
  have hL := χ.LSeries_eulerProduct_hasProd hs
  have hFp : HasProd (fun p : Nat.Primes => (1 - (u : ℂ) * z p)⁻¹)
      (∑' n, generatingSummandHom χ (u : ℂ) (ne_zero_of_one_lt_re hs) n) := by
    simpa [generatingSummand_at_prime, z, dirichletSummandHom] using hF
  have hLp : HasProd (fun p : Nat.Primes => (1 - z p)⁻¹) (LSeries (fun n : ℕ => (χ n : ℂ)) s) := by
    simpa [z, dirichletSummandHom] using hL
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - (u : ℂ) * z p)⁻¹)
    Filter.atTop (nhds _) at hFp
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - z p)⁻¹)
    Filter.atTop (nhds _) at hLp
  apply le_of_tendsto_of_tendsto (hFp.norm.pow 2)
    ((hLp.norm.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ 2 * u))).const_mul 2)
  apply Filter.Eventually.of_forall
  intro S
  have hfinite := complex_finite_euler_product_upper S hu0 hu1 z (fun p _ => hhalf p)
  have hcor := prime_correction_product_le_two S z (fun p _ => hz p)
  have hmul := mul_le_mul_of_nonneg_left hcor
    (Real.rpow_nonneg (norm_nonneg (∏ p ∈ S, (1 - z p)⁻¹)) (2 * u))
  exact hfinite.trans (by nlinarith [hmul])

lemma generatingValue_norm_sq_le_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖generatingValue χ (u : ℂ) s‖ ^ 2 ≤ 2 * ‖LSeries (fun n : ℕ => (χ n : ℂ)) s‖ ^ (2 * u) := by
  rw [generatingValue_eq_tsum χ (u : ℂ) (ne_zero_of_one_lt_re hs)]
  exact generating_norm_sq_le_LSeries χ hu0 hu1 hs

lemma generatingValue_norm_le_two_rpow_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖generatingValue χ (u : ℂ) s‖ ≤ 2 * ‖LSeries (fun n : ℕ => (χ n : ℂ)) s‖ ^ u := by
  have h := generatingValue_norm_sq_le_LSeries χ hu0 hu1 hs
  have hid : ‖LSeries (fun n : ℕ => (χ n : ℂ)) s‖ ^ (2 * u) = (‖LSeries (fun n : ℕ => (χ n : ℂ)) s‖ ^ u) ^ 2 := by
    rw [mul_comm (2 : ℝ) u, Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  rw [hid] at h
  nlinarith [norm_nonneg (generatingValue χ (u : ℂ) s), Real.rpow_nonneg (norm_nonneg (LSeries (fun n : ℕ => (χ n : ℂ)) s)) u]

/-- The uniform bound near s=1 needed for the Abel-average method. It is proved from
continuity of the nonprincipal L-function and does not use nonvanishing at 1. -/
lemma nonprincipal_generatingValue_bounded {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖generatingValue χ (u : ℂ) (1 + (t : ℂ))‖ ≤ C := by
  have hcont : Continuous (fun t : ℝ => χ.LFunction (1 + (t : ℂ))) :=
    (nonprincipal_LFunction_continuous χ hχ).comp (continuous_const.add Complex.continuous_ofReal)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hcont.continuousOn
  let K : ℝ := max 1 B
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨2 * K, by positivity, ?_⟩
  intro u hu0 hu1 t ht0 ht1
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht0
  have hL : ‖LSeries (fun n : ℕ => (χ n : ℂ)) (1 + (t : ℂ))‖ ≤ K := by
    rw [← χ.LFunction_eq_LSeries hs]
    exact (hB t ⟨ht0.le, ht1⟩).trans (le_max_right _ _)
  have he : (0 : ℝ) ≤ 2 * u := by positivity
  have hpow : ‖LSeries (fun n : ℕ => (χ n : ℂ)) (1 + (t : ℂ))‖ ^ (2 * u) ≤ K ^ 2 := by
    calc
      _ ≤ K ^ (2 * u) := Real.rpow_le_rpow (norm_nonneg _) hL he
      _ ≤ K ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
      _ = K ^ 2 := Real.rpow_two _
  have hnorm := generatingValue_norm_sq_le_LSeries χ hu0 hu1 hs
  nlinarith [norm_nonneg (generatingValue χ (u : ℂ) (1 + (t : ℂ)))]

end Apicella143

end

-- module Apicella143.PrincipalBound
noncomputable section
open Complex
open scoped BigOperators Topology

namespace Apicella143

lemma principal_prime_factor_real {N : ℕ} {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    dirichletSummandHom (1 : DirichletCharacter ℂ N)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) p =
    (‖dirichletSummandHom (1 : DirichletCharacter ℂ N)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) p‖ : ℂ) := by
  change (1 : DirichletCharacter ℂ N) p * (p : ℂ) ^ (-(s : ℂ)) =
    (‖(1 : DirichletCharacter ℂ N) p * (p : ℂ) ^ (-(s : ℂ))‖ : ℂ)
  by_cases hunit : IsUnit ((p : ℕ) : ZMod N)
  · rw [MulChar.one_apply hunit, one_mul]
    have hpow : (p : ℂ) ^ (-(s : ℂ)) = Complex.ofReal ((p : ℝ) ^ (-s)) := by
      rw [ofReal_cpow (by positivity), ofReal_neg, ofReal_natCast]
    rw [hpow, Complex.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  · rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ N) hunit, zero_mul]
    simp

/-- A principal generating series is at least the u-th power of half its ordinary L-series.
This suffices for a positive Abel-average residue after integration near s=1. -/
lemma principal_generatingValue_lower {N : ℕ} {u s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) :
    (‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ N) n : ℂ)) (s : ℂ)‖ / 2) ^ u ≤
      ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ)‖ := by
  let χ : DirichletCharacter ℂ N := 1
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  let z : Nat.Primes → ℂ := fun p => dirichletSummandHom χ (ne_zero_of_one_lt_re hsC) p
  let x : Nat.Primes → ℝ := fun p => ‖z p‖
  have hx0 : ∀ p, 0 ≤ x p := fun p => norm_nonneg _
  have hx : ∀ p, x p ≤ (p : ℝ)⁻¹ := dirichlet_prime_factor_norm_le_reciprocal χ hsC
  have hhalf : ∀ p, x p ≤ 1 / 2 := fun p => (hx p).trans (prime_reciprocal_le_half p)
  have hreal : ∀ p, z p = (x p : ℂ) := principal_prime_factor_real hs
  have hu : ‖(u : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] using hu1
  have hF : HasProd (fun p : Nat.Primes => (1 - (u : ℂ) * z p)⁻¹)
      (generatingValue χ (u : ℂ) (s : ℂ)) := by
    simpa [generatingValue_eq_tsum χ (u : ℂ) (ne_zero_of_one_lt_re hsC),
      generatingSummand_at_prime, z, dirichletSummandHom] using
      generating_eulerProduct_hasProd χ hu hsC
  have hZ : HasProd (fun p : Nat.Primes => (1 - z p)⁻¹) (LSeries (fun n : ℕ => (χ n : ℂ)) (s : ℂ)) := by
    simpa [z, dirichletSummandHom] using χ.LSeries_eulerProduct_hasProd hsC
  have hfactors (v : ℝ) (_hv0 : 0 ≤ v) (hv1 : v ≤ 1) (p : Nat.Primes) :
      ‖(1 - (v : ℂ) * z p)⁻¹‖ = (1 - v * x p)⁻¹ := by
    have hp : 0 ≤ 1 - v * x p := by
      have hmul := mul_le_mul_of_nonneg_right hv1 (hx0 p)
      linarith [hhalf p]
    rw [hreal]
    have heq : (1 - (v : ℂ) * (x p : ℂ))⁻¹ = (((1 - v * x p)⁻¹ : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [heq, Complex.norm_of_nonneg (inv_nonneg.mpr hp)]
  have hFnorm : HasProd (fun p => (1 - u * x p)⁻¹)
      ‖generatingValue χ (u : ℂ) (s : ℂ)‖ := by
    change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - (u : ℂ) * z p)⁻¹)
      Filter.atTop (nhds _) at hF
    have h := hF.norm
    simp only [norm_prod, hfactors u hu0 hu1] at h
    exact h
  have hZnorm : HasProd (fun p => (1 - x p)⁻¹) ‖LSeries (fun n : ℕ => (χ n : ℂ)) (s : ℂ)‖ := by
    change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - z p)⁻¹)
      Filter.atTop (nhds _) at hZ
    have hone (p : Nat.Primes) : ‖(1 - z p)⁻¹‖ = (1 - x p)⁻¹ := by
      simpa using hfactors 1 (by norm_num) (by norm_num) p
    have h := hZ.norm
    simp only [norm_prod, hone] at h
    exact h
  exact positive_euler_product_lower hu0 hu1 x hx0 hx hFnorm hZnorm

end Apicella143

end

-- module Apicella143.PrincipalReality
noncomputable section
open Complex
open scoped ArithmeticFunction.Omega

namespace Apicella143

def principalGeneratingTerm (N : ℕ) (u s : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if IsUnit (n : ZMod N) then u ^ Ω n * (n : ℝ) ^ (-s) else 0

lemma principalGeneratingTerm_nonneg {N : ℕ} {u s : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ principalGeneratingTerm N u s n := by
  unfold principalGeneratingTerm
  split_ifs <;> positivity

lemma principalGeneratingTerm_one (N : ℕ) (u s : ℝ) : principalGeneratingTerm N u s 1 = 1 := by
  simp [principalGeneratingTerm]

lemma principalGeneratingTerm_cast {N : ℕ} {u s : ℝ} (hs : 1 < s) (n : ℕ) :
    generatingSummandHom (1 : DirichletCharacter ℂ N) (u : ℂ)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) n =
      (principalGeneratingTerm N u s n : ℂ) := by
  by_cases hn : n = 0
  · have hs0 : -s ≠ 0 := by linarith
    simp [hn, principalGeneratingTerm, Real.zero_rpow hs0]
  · change omegaWeightHom (u : ℂ) n * ((1 : DirichletCharacter ℂ N) n * (n : ℂ) ^ (-(s : ℂ))) = _
    rw [omegaWeightHom_apply hn]
    by_cases hunit : IsUnit (n : ZMod N)
    · rw [MulChar.one_apply hunit, one_mul]
      simp only [principalGeneratingTerm, if_pos hunit, ofReal_mul, ofReal_pow,
        ofReal_cpow (Nat.cast_nonneg n), ofReal_neg, ofReal_natCast]
    · rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ N) hunit, zero_mul, mul_zero]
      simp [principalGeneratingTerm, hunit]

lemma principalGeneratingTerm_summable {N : ℕ} {u s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) : Summable (principalGeneratingTerm N u s) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have h := generatingSummand_norm_summable (1 : DirichletCharacter ℂ N) hu
    (show 1 < (s : ℂ).re by simpa using hs)
  simpa only [principalGeneratingTerm_cast hs, Complex.norm_of_nonneg (principalGeneratingTerm_nonneg hu0 _)] using h

lemma principalGeneratingValue_eq_real_sum {N : ℕ} {u s : ℝ} (hs : 1 < s) :
    generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ) =
      (∑' n, principalGeneratingTerm N u s n : ℝ) := by
  rw [generatingValue_eq_tsum _ _ (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs))]
  simp only [principalGeneratingTerm_cast hs, Complex.ofReal_tsum]

lemma principalGeneratingValue_norm_eq_sum {N : ℕ} {u s : ℝ} (hu0 : 0 ≤ u) (hs : 1 < s) :
    ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ)‖ =
      ∑' n, principalGeneratingTerm N u s n := by
  rw [principalGeneratingValue_eq_real_sum hs]
  exact Complex.norm_of_nonneg (tsum_nonneg (principalGeneratingTerm_nonneg hu0))

lemma principalGeneratingValue_norm_one_le {N : ℕ} {u s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) :
    1 ≤ ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ)‖ := by
  rw [principalGeneratingValue_norm_eq_sum hu0 hs]
  have h := (principalGeneratingTerm_summable (N := N) hu0 hu1 hs).le_tsum 1
    (fun n _ => principalGeneratingTerm_nonneg hu0 n)
  simpa only [principalGeneratingTerm_one] using h

end Apicella143

end

-- module Apicella143.GeneratingRegularity
noncomputable section
open Complex
open scoped Topology

namespace Apicella143

def generatingCoefficient {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℂ) (n : ℕ) : ℂ :=
  omegaWeightHom u n * χ n

lemma generatingValue_eq_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N) (u s : ℂ) :
    generatingValue χ u s = LSeries (generatingCoefficient χ u) s := by
  unfold generatingValue LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · simp only [LSeries.term_of_ne_zero hn, generatingCoefficient, div_eq_mul_inv, cpow_neg]
    ring

lemma generatingCoefficient_norm_le_one {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖generatingCoefficient χ u n‖ ≤ 1 := by
  unfold generatingCoefficient
  rw [norm_mul]
  simpa using mul_le_mul (omegaWeightHom_norm_le_one hu n) (χ.norm_le_one n)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

lemma generatingCoefficient_abscissa_le_one {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) : LSeries.abscissaOfAbsConv (generatingCoefficient χ u) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => generatingCoefficient_norm_le_one χ hu n⟩

/-- Ordinary continuity in the exponent away from the boundary s=1. -/
lemma generatingValue_continuousAt {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    ContinuousAt (generatingValue χ u) s := by
  have h := generatingCoefficient_abscissa_le_one χ hu
  have hs' : (1 : EReal) < (s.re : EReal) := by exact_mod_cast hs
  have heq : generatingValue χ u = LSeries (generatingCoefficient χ u) := by
    funext z
    exact generatingValue_eq_LSeries χ u z
  rw [heq]
  exact (LSeries_hasDerivAt (h.trans_lt hs')).continuousAt

lemma generatingValue_continuousOn_positive {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ContinuousOn (fun t : ℝ => generatingValue χ u (1 + (t : ℂ))) (Set.Ioi 0) := by
  intro t ht
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
  have hinner : ContinuousAt (fun x : ℝ => 1 + (x : ℂ)) t :=
    (continuous_const.add continuous_ofReal).continuousAt
  exact (ContinuousAt.comp (f := fun x : ℝ => 1 + (x : ℂ)) (x := t)
    (generatingValue_continuousAt χ hu hs) hinner).continuousWithinAt

end Apicella143

end

-- module Apicella143.GeneratingTail
noncomputable section
open Complex
open scoped BigOperators

namespace Apicella143

lemma generatingSummand_norm_le_rpow {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) {s : ℝ} (hs : 1 < s) (n : ℕ) :
    ‖generatingSummandHom χ u (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) n‖ ≤
      (n : ℝ) ^ (-s) := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hid : generatingSummandHom χ u (ne_zero_of_one_lt_re hsC) n =
      generatingCoefficient χ u n * (n : ℂ) ^ (-(s : ℂ)) := by
    simp only [generatingSummandHom, generatingCoefficient, dirichletSummandHom,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring
  rw [hid, norm_mul]
  have hnorm : ‖(n : ℂ) ^ (-(s : ℂ))‖ = (n : ℝ) ^ (-s) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
      (re_neg_ne_zero_of_one_lt_re hsC), neg_re, ofReal_re]
  rw [hnorm]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (generatingCoefficient_norm_le_one χ hu n)

lemma generatingValue_sub_one_eq_tail {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    generatingValue χ u s - 1 =
      ∑' n : ℕ, generatingSummandHom χ u (ne_zero_of_one_lt_re hs) (n + 2) := by
  have hsum := (generatingSummand_norm_summable χ hu hs).of_norm
  have h := hsum.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_zero, map_one, zero_add] at h
  rw [generatingValue_eq_tsum χ u (ne_zero_of_one_lt_re hs)]
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)).symm

lemma shifted_square_reciprocal_summable :
    Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by decide)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using (summable_nat_add_iff 2).2 h

def tailMajorantConst : ℝ := 2 * ∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹

lemma tailMajorantConst_nonneg : 0 ≤ tailMajorantConst := by
  unfold tailMajorantConst
  positivity

lemma rpow_tail_comparison {x t : ℝ} (hx : 2 ≤ x) (ht : 1 ≤ t) :
    x ^ (-(1 + t)) ≤ (x ^ 2)⁻¹ * (2 : ℝ) ^ (-(t - 1)) := by
  have hx0 : 0 < x := by linarith
  have hexp : -(1 + t) = (-2 : ℝ) + -(t - 1) := by ring
  rw [hexp, Real.rpow_add hx0, Real.rpow_neg hx0.le, Real.rpow_two]
  have hpow := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hx
    (show -(t - 1) ≤ 0 by linarith)
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

lemma two_rpow_tail_eq_exp (t : ℝ) :
    (2 : ℝ) ^ (-(t - 1)) = 2 * Real.exp ((-Real.log 2) * t) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc
    Real.exp (Real.log 2 * -(t - 1)) = Real.exp (Real.log 2 + (-Real.log 2) * t) := by
      congr 1
      ring
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Uniform exponential decay of G−1 for large t, for every character and every |u|≤1. -/
lemma generatingValue_tail_bound {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖generatingValue χ u (1 + (t : ℂ)) - 1‖ ≤
      tailMajorantConst * Real.exp ((-Real.log 2) * t) := by
  have hs : (1 : ℝ) < 1 + t := by linarith
  have hsC : 1 < (1 + (t : ℂ)).re := by simpa using hs
  let f : ℕ → ℂ := fun n => generatingSummandHom χ u (ne_zero_of_one_lt_re hsC) (n + 2)
  have hsum : Summable (fun n => ‖f n‖) :=
    (generatingSummand_norm_summable χ hu hsC).comp_injective (fun _ _ h => by omega)
  have hpoint (n : ℕ) : ‖f n‖ ≤ (((n : ℝ) + 2) ^ 2)⁻¹ * (2 : ℝ) ^ (-(t - 1)) := by
    have h := generatingSummand_norm_le_rpow χ hu hs (n + 2)
    simp only [ofReal_add, ofReal_one, Nat.cast_add, Nat.cast_ofNat] at h
    exact h.trans (rpow_tail_comparison (by linarith [Nat.cast_nonneg (α := ℝ) n] : (2 : ℝ) ≤ (n : ℝ) + 2) ht)
  rw [generatingValue_sub_one_eq_tail χ hu hsC]
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹ * (2 : ℝ) ^ (-(t - 1)) :=
      hsum.tsum_le_tsum hpoint (shifted_square_reciprocal_summable.mul_right _)
    _ = tailMajorantConst * Real.exp ((-Real.log 2) * t) := by
      rw [tsum_mul_right, two_rpow_tail_eq_exp]
      unfold tailMajorantConst
      ring

end Apicella143

end

-- module Apicella143.GeneratingDomination
noncomputable section
open Complex
open scoped ArithmeticFunction.Omega

namespace Apicella143

lemma principalGeneratingTerm_mod_one (u s : ℝ) (n : ℕ) :
    principalGeneratingTerm 1 u s n = u ^ Ω n * (n : ℝ) ^ (-s) := by
  simp only [principalGeneratingTerm, isUnit_of_subsingleton, if_true]

lemma generatingSummand_norm_le_principalTerm {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℝ} (hu0 : 0 ≤ u) (hs : 1 < s) (n : ℕ) :
    ‖generatingSummandHom χ (u : ℂ)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) n‖ ≤
      principalGeneratingTerm 1 u s n := by
  rw [principalGeneratingTerm_mod_one]
  by_cases hn : n = 0
  · have hs0 : -s ≠ 0 := by linarith
    simp [hn, Real.zero_rpow hs0]
  · have hsC : 1 < (s : ℂ).re := by simpa using hs
    change ‖omegaWeightHom (u : ℂ) n * (χ n * (n : ℂ) ^ (-(s : ℂ)))‖ ≤ _
    rw [omegaWeightHom_apply hn, norm_mul, norm_mul, norm_pow, Complex.norm_of_nonneg hu0]
    have hnorm : ‖(n : ℂ) ^ (-(s : ℂ))‖ = (n : ℝ) ^ (-s) := by
      rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
        (re_neg_ne_zero_of_one_lt_re hsC), neg_re, ofReal_re]
    rw [hnorm]
    have hχ := mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) (-s)) (χ.norm_le_one n)
    exact mul_le_mul_of_nonneg_left hχ (pow_nonneg hu0 _)

lemma generatingValue_norm_le_global {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) :
    ‖generatingValue χ (u : ℂ) (s : ℂ)‖ ≤
      ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (s : ℂ)‖ := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have hsum := generatingSummand_norm_summable χ hu hsC
  rw [generatingValue_eq_tsum χ _ (ne_zero_of_one_lt_re hsC),
    principalGeneratingValue_norm_eq_sum hu0 hs]
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum
    (generatingSummand_norm_le_principalTerm χ hu0 hs)
    (principalGeneratingTerm_summable (N := 1) hu0 hu1 hs))

end Apicella143

end

-- module Apicella143.PrincipalResidue
noncomputable section
open Filter Complex
open scoped Topology BigOperators

namespace Apicella143

def totientRatio (N : ℕ) : ℝ := (N.totient : ℝ) / N

lemma totientRatio_pos (N : ℕ) [NeZero N] : 0 < totientRatio N := by
  unfold totientRatio
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N))
    (by exact_mod_cast NeZero.pos N)

lemma principal_residue_eq_ratio (N : ℕ) [NeZero N] :
    (∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) = (totientRatio N : ℂ) := by
  have h : (N.totient : ℂ) = (N : ℂ) * ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹) := by
    have h := congrArg (Rat.castHom ℂ) (Nat.totient_eq_mul_prod_factors N)
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀] using h
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  calc
    _ = (N.totient : ℂ) / N := by
      apply (eq_div_iff hN).2
      simpa [mul_comm] using h.symm
    _ = (totientRatio N : ℂ) := by simp [totientRatio]

/-- The real one-sided principal-character residue, with the exact φ(N)/N constant. -/
lemma principal_norm_residue (N : ℕ) [NeZero N] :
    Tendsto (fun t : ℝ => t * ‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ N) n : ℂ)) (1 + (t : ℂ))‖)
      (𝓝[>] 0) (𝓝 (totientRatio N)) := by
  have hcont : Continuous (fun t : ℝ => 1 + (t : ℂ)) := continuous_const.add continuous_ofReal
  have hmaps : Set.MapsTo (fun t : ℝ => 1 + (t : ℂ)) (Set.Ioi 0) ({1}ᶜ : Set ℂ) := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, one_re, ofReal_re] at hre
    have ht0 : 0 < t := ht
    linarith
  have hto : Tendsto (fun t : ℝ => 1 + (t : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    simpa using (hcont.continuousWithinAt (x := 0) (s := Set.Ioi 0)).tendsto_nhdsWithin hmaps
  have hres := (DirichletCharacter.LFunctionTrivChar_residue_one (N := N)).comp hto
  rw [principal_residue_eq_ratio] at hres
  have hnorm := hres.norm
  rw [Complex.norm_of_nonneg (totientRatio_pos N).le] at hnorm
  apply hnorm.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht0
  simp only [Function.comp_apply, add_sub_cancel_left, norm_mul,
    Complex.norm_of_nonneg ht0.le, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_eq_LSeries _ hs]

lemma principal_local_bounds (N : ℕ) [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ eps →
      totientRatio N / (2 * t) ≤ ‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ N) n : ℂ)) (1 + (t : ℂ))‖ ∧
      ‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ N) n : ℂ)) (1 + (t : ℂ))‖ ≤ 2 * totientRatio N / t := by
  have hκ := totientRatio_pos N
  have hevent := (principal_norm_residue N).eventually
    (Ioo_mem_nhds (show totientRatio N / 2 < totientRatio N by linarith)
      (show totientRatio N < 2 * totientRatio N by linarith))
  obtain ⟨d, hd, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hevent
  refine ⟨min d 1, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro t ht hteps
  have htm : t * ‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ N) n : ℂ)) (1 + (t : ℂ))‖ ∈
      Set.Ioo (totientRatio N / 2) (2 * totientRatio N) :=
    hsub ⟨ht, hteps.trans (min_le_left _ _)⟩
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * t)).2
    nlinarith [htm.1]
  · apply (le_div_iff₀ ht).2
    nlinarith [htm.2]

lemma principal_generating_local_lower (N : ℕ) [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ eps →
      (totientRatio N / (4 * t)) ^ u ≤
      ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ))‖ := by
  obtain ⟨eps, heps0, heps1, hbounds⟩ := principal_local_bounds N
  refine ⟨eps, heps0, heps1, ?_⟩
  intro u hu0 hu1 t ht hteps
  have hb := (hbounds t ht hteps).1
  have hdiv : totientRatio N / (4 * t) ≤
      ‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ N) n : ℂ)) (1 + (t : ℂ))‖ / 2 := by
    calc
      _ = (totientRatio N / (2 * t)) / 2 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right hb (by norm_num)
  have hnonneg : (0 : ℝ) ≤ totientRatio N / (4 * t) :=
    div_nonneg (totientRatio_pos N).le (by positivity)
  have hpow := Real.rpow_le_rpow hnonneg hdiv hu0
  have h := principal_generatingValue_lower (N := N) hu0 hu1 (show (1 : ℝ) < 1 + t by linarith)
  simp only [Complex.ofReal_add, Complex.ofReal_one] at h
  exact hpow.trans h

/-- An integrable majorant t^(-u), with a constant uniform in the real Abel parameter. -/
lemma global_generating_local_upper :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ eps →
      ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (1 + (t : ℂ))‖ ≤ 4 * t ^ (-u) := by
  obtain ⟨eps, heps0, heps1, hbounds⟩ := principal_local_bounds 1
  refine ⟨eps, heps0, heps1, ?_⟩
  intro u hu0 hu1 t ht hteps
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
  have hL : ‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ 1) n : ℂ)) (1 + (t : ℂ))‖ ≤ 2 / t := by
    simpa [totientRatio] using (hbounds t ht hteps).2
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hL hu0
  have h2 : (2 : ℝ) ^ u ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hu1
    simpa only [Real.rpow_one] using h
  calc
    _ ≤ 2 * ‖LSeries (fun n : ℕ => ((1 : DirichletCharacter ℂ 1) n : ℂ)) (1 + (t : ℂ))‖ ^ u :=
      generatingValue_norm_le_two_rpow_LSeries _ hu0 hu1 hs
    _ ≤ 2 * (2 / t) ^ u := by linarith
    _ ≤ 4 * t ^ (-u) := by
      rw [Real.div_rpow (by norm_num) ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
      nlinarith [inv_nonneg.mpr (Real.rpow_nonneg ht.le u),
        mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr (Real.rpow_nonneg ht.le u))]

end Apicella143

end

-- module Apicella143.ImproperControl
noncomputable section
open MeasureTheory Set

namespace Apicella143

/-- A reusable improper-integrability criterion with a power bound at zero and exponential
bound at infinity, avoiding any assertion that boundedness alone implies integrability. -/
lemma integrableOn_Ioi_of_power_exp_bounds {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Ioi 0)) {eps a C D E c : ℝ}
    (heps : 0 < eps) (_heps1 : eps ≤ 1) (ha : -1 < a) (hc : 0 < c)
    (hsmall : ∀ t, 0 < t → t ≤ eps → ‖f t‖ ≤ C * t ^ a + D)
    (htail : ∀ t, 1 ≤ t → ‖f t‖ ≤ E * Real.exp ((-c) * t)) :
    IntegrableOn f (Ioi 0) := by
  have hsmall_cont : ContinuousOn f (Ioo 0 eps) := hcont.mono Ioo_subset_Ioi_self
  have hp : IntegrableOn (fun t : ℝ => t ^ a) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps).2 ha
  have hconst : IntegrableOn (fun _ : ℝ => D) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  have hsmall_int : IntegrableOn f (Ioo 0 eps) :=
    ((hp.const_mul C).add hconst).mono' (hsmall_cont.aestronglyMeasurable measurableSet_Ioo)
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hsmall t ht.1 ht.2.le))
  have hmid_cont : ContinuousOn f (Icc eps 1) := hcont.mono (by
    intro t ht
    exact heps.trans_le ht.1)
  have hmid_int : IntegrableOn f (Icc eps 1) := hmid_cont.integrableOn_Icc
  have htail_cont : ContinuousOn f (Ioi 1) := hcont.mono (Ioi_subset_Ioi (by norm_num))
  have htail_int : IntegrableOn f (Ioi 1) :=
    ((integrableOn_exp_mul_Ioi (by linarith : -c < 0) 1).const_mul E).mono'
      (htail_cont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => htail t ht.le))
  apply ((hsmall_int.union hmid_int).union htail_int).mono_set
  intro t ht
  by_cases hteps : t < eps
  · exact Or.inl (Or.inl ⟨ht, hteps⟩)
  · by_cases ht1 : t ≤ 1
    · exact Or.inl (Or.inr ⟨le_of_not_gt hteps, ht1⟩)
    · exact Or.inr (lt_of_not_ge ht1)

end Apicella143

end

-- module Apicella143.GeneratingIntegrability
noncomputable section
open MeasureTheory Set

namespace Apicella143

/-- Absolute integrability of the subtracted generating function for each real 0≤u<1. -/
lemma generatingValue_sub_one_integrable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (fun t : ℝ => generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1) (Ioi 0) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1.le
  have hcont := (generatingValue_continuousOn_positive χ hu).sub (continuousOn_const (c := (1 : ℂ)))
  obtain ⟨eps, heps0, heps1, hsmall⟩ := global_generating_local_upper
  apply integrableOn_Ioi_of_power_exp_bounds hcont heps0 heps1
    (show -1 < -u by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (C := 4) (D := 1) (E := tailMajorantConst)
  · intro t ht hteps
    simp only [Pi.sub_apply]
    have hdom := generatingValue_norm_le_global χ hu0 hu1.le (show (1 : ℝ) < 1 + t by linarith)
    simp only [Complex.ofReal_add, Complex.ofReal_one] at hdom
    have hmajor := hsmall u hu0 hu1.le t ht hteps
    calc
      _ ≤ ‖generatingValue χ (u : ℂ) (1 + (t : ℂ))‖ + 1 := by
        simpa only [norm_one] using norm_sub_le (generatingValue χ (u : ℂ) (1 + (t : ℂ))) (1 : ℂ)
      _ ≤ _ := by linarith
  · intro t ht
    exact generatingValue_tail_bound χ hu ht

/-- For a nonprincipal character the endpoint u=1 is also integrable, using the uniform
boundedness proved directly from L-function continuity. -/
lemma nonprincipal_generatingValue_sub_one_integrable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IntegrableOn (fun t : ℝ => generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1) (Ioi 0) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have hcont := (generatingValue_continuousOn_positive χ hu).sub (continuousOn_const (c := (1 : ℂ)))
  obtain ⟨C, _hC0, hC⟩ := nonprincipal_generatingValue_bounded χ hχ
  apply integrableOn_Ioi_of_power_exp_bounds hcont (eps := 1) (by norm_num) (by norm_num)
    (a := 0) (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (C := 0) (D := C + 1) (E := tailMajorantConst)
  · intro t ht ht1
    simp only [Pi.sub_apply]
    have hb := hC u hu0 hu1 t ht ht1
    have hnorm := norm_sub_le (generatingValue χ (u : ℂ) (1 + (t : ℂ))) (1 : ℂ)
    simp only [norm_one] at hnorm
    simp only [Real.rpow_zero, mul_one, zero_add]
    linarith
  · intro t ht
    exact generatingValue_tail_bound χ hu ht

/-- The integrated generating function used by the Abel proof. -/
def integratedGeneratingValue {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1

end Apicella143

end

-- module Apicella143.PositiveInterchange
noncomputable section
open MeasureTheory

namespace Apicella143

/-- A nonnegative family with an integrable pointwise sum has a summable sequence of
integrals. This supplies the Tonelli finiteness needed before exchanging infinite sums. -/
lemma summable_integral_of_integrable_tsum_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : ℕ → α → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (hnonneg : ∀ n x, 0 ≤ F n x) (hsum : ∀ᵐ x ∂μ, Summable (fun n => F n x))
    (hInt : Integrable (fun x => ∑' n, F n x) μ) : Summable (fun n => ∫ x, F n x ∂μ) := by
  apply summable_of_sum_le (fun n => integral_nonneg (hnonneg n))
  intro S
  rw [← integral_finset_sum S (fun n _ => hF n)]
  apply integral_mono_ae (integrable_finset_sum S (fun n _ => hF n)) hInt
  filter_upwards [hsum] with x hx
  exact hx.sum_le_tsum S (fun n _ => hnonneg n x)

lemma integral_tsum_nonneg_of_integrable_tsum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : ℕ → α → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (hnonneg : ∀ n x, 0 ≤ F n x) (hsum : ∀ᵐ x ∂μ, Summable (fun n => F n x))
    (hInt : Integrable (fun x => ∑' n, F n x) μ) :
    (∑' n, ∫ x, F n x ∂μ) = ∫ x, ∑' n, F n x ∂μ := by
  have hint := summable_integral_of_integrable_tsum_nonneg F hF hnonneg hsum hInt
  have hnorm : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _ _)] using hint
  exact integral_tsum_of_summable_integral_norm hF hnorm

end Apicella143

end

-- module Apicella143.MellinWeight
noncomputable section
open MeasureTheory Set

namespace Apicella143

lemma weight_integrand_factorization {n : ℝ} (hn : 1 < n) (t : ℝ) :
    n ^ (-(1 + t)) = n⁻¹ * Real.exp ((-Real.log n) * t) := by
  have hn0 : 0 < n := by linarith
  rw [Real.rpow_def_of_pos hn0]
  calc
    Real.exp (Real.log n * -(1 + t)) = Real.exp (-Real.log n + (-Real.log n) * t) := by
      congr 1
      ring
    _ = Real.exp (-Real.log n) * Real.exp ((-Real.log n) * t) := Real.exp_add _ _
    _ = n⁻¹ * Real.exp ((-Real.log n) * t) := by rw [Real.exp_neg, Real.exp_log hn0]

/-- The elementary integral identity behind the nonnegative interchange in §3.1. -/
lemma real_weight_integral {n : ℝ} (hn : 1 < n) :
    (∫ t : ℝ in Ioi 0, n ^ (-(1 + t))) = 1 / (n * Real.log n) := by
  have hlog : 0 < Real.log n := Real.log_pos hn
  simp_rw [weight_integrand_factorization hn]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -Real.log n < 0) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div, mul_inv_rev]
  ring

lemma weight_integrand_integrable {n : ℝ} (hn : 1 < n) :
    IntegrableOn (fun t : ℝ => n ^ (-(1 + t))) (Ioi 0) := by
  simp_rw [weight_integrand_factorization hn]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos (Real.log_pos hn)) 0).const_mul _

end Apicella143

end

-- module Apicella143.WeightedIntegrability
noncomputable section
open MeasureTheory Set Complex
open scoped ArithmeticFunction.Omega

namespace Apicella143

def realGeneratingTailTerm (u : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  u ^ Ω (n + 2) * ((n : ℝ) + 2) ^ (-(1 + t))

lemma realGeneratingTailTerm_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) (t : ℝ) :
    0 ≤ realGeneratingTailTerm u n t := by unfold realGeneratingTailTerm; positivity

lemma realGeneratingTailTerm_integrable (u : ℝ) (n : ℕ) :
    IntegrableOn (realGeneratingTailTerm u n) (Ioi 0) := by
  exact (weight_integrand_integrable (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) < n + 2)).const_mul _

lemma integral_realGeneratingTailTerm (u : ℝ) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, realGeneratingTailTerm u n t) =
      u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
  unfold realGeneratingTailTerm
  rw [integral_const_mul, real_weight_integral (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) < n + 2)]
  ring

lemma realGeneratingTailTerm_summable {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht : 0 < t) :
    Summable (fun n => realGeneratingTailTerm u n t) := by
  have hs : (1 : ℝ) < 1 + t := by linarith
  have h := (principalGeneratingTerm_summable (N := 1) hu0 hu1 hs).comp_injective
    (fun m n (h : m + 2 = n + 2) => by omega)
  simpa only [Function.comp_def, principalGeneratingTerm_mod_one, realGeneratingTailTerm, Nat.cast_add, Nat.cast_ofNat] using h

lemma global_sub_one_norm_eq_real_tail {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht : 0 < t) :
    ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (1 + (t : ℂ)) - 1‖ =
      ∑' n : ℕ, realGeneratingTailTerm u n t := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have hsC : 1 < (1 + (t : ℂ)).re := by simpa using ht
  rw [generatingValue_sub_one_eq_tail _ hu hsC]
  have hterm (n : ℕ) : generatingSummandHom (1 : DirichletCharacter ℂ 1) (u : ℂ)
      (ne_zero_of_one_lt_re hsC) (n + 2) = (realGeneratingTailTerm u n t : ℂ) := by
    have h := principalGeneratingTerm_cast (N := 1) (u := u) (show (1 : ℝ) < 1 + t by linarith) (n + 2)
    simpa only [ofReal_add, ofReal_one, principalGeneratingTerm_mod_one, realGeneratingTailTerm,
      Nat.cast_add, Nat.cast_ofNat] using h
  simp only [hterm, ← Complex.ofReal_tsum]
  exact Complex.norm_of_nonneg (tsum_nonneg (realGeneratingTailTerm_nonneg hu0 · t))

lemma realGeneratingTail_sum_integrable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (fun t : ℝ => ∑' n, realGeneratingTailTerm u n t) (Ioi 0) := by
  have h := (generatingValue_sub_one_integrable (1 : DirichletCharacter ℂ 1) hu0 hu1).norm
  exact h.congr (ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => global_sub_one_norm_eq_real_tail hu0 hu1.le ht))

/-- Absolute convergence of the Ω-weighted logarithmic series is proved, rather than assumed. -/
lemma weighted_log_series_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun n : ℕ => u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  have h := summable_integral_of_integrable_tsum_nonneg (realGeneratingTailTerm u)
    (realGeneratingTailTerm_integrable u) (realGeneratingTailTerm_nonneg hu0)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => realGeneratingTailTerm_summable hu0 hu1.le ht))
    (realGeneratingTail_sum_integrable hu0 hu1)
  simpa only [integral_realGeneratingTailTerm] using h

end Apicella143

end

-- module Apicella143.TwistedIntegral
noncomputable section
open MeasureTheory Set Complex
open scoped ArithmeticFunction.Omega

namespace Apicella143

def complexGeneratingTailTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ)
    (n : ℕ) (t : ℝ) : ℂ := χ (n + 2) * (realGeneratingTailTerm u n t : ℂ)

def weightedCharacterTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) (n : ℕ) : ℂ :=
  χ (n + 2) * ((u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) : ℝ) : ℂ)

lemma complexGeneratingTailTerm_integrable {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : ℝ) (n : ℕ) : IntegrableOn (complexGeneratingTailTerm χ u n) (Ioi 0) :=
  (realGeneratingTailTerm_integrable u n).ofReal.const_mul _

lemma integral_complexGeneratingTailTerm {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : ℝ) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, complexGeneratingTailTerm χ u n t) = weightedCharacterTerm χ u n := by
  unfold complexGeneratingTailTerm weightedCharacterTerm
  rw [integral_const_mul, integral_complex_ofReal, integral_realGeneratingTailTerm]

lemma complexGeneratingTailTerm_norm_integral_le {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, ‖complexGeneratingTailTerm χ u n t‖) ≤
      u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
  simp only [complexGeneratingTailTerm, norm_mul,
    Complex.norm_of_nonneg (realGeneratingTailTerm_nonneg hu _ _)]
  rw [integral_const_mul, integral_realGeneratingTailTerm]
  have hw : 0 ≤ u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
    have hlog : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  exact mul_le_of_le_one_left hw (χ.norm_le_one (n + 2))

lemma complexGeneratingTailTerm_norm_integrals_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun n => ∫ t : ℝ in Ioi 0, ‖complexGeneratingTailTerm χ u n t‖) :=
  (weighted_log_series_summable hu0 hu1).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (complexGeneratingTailTerm_norm_integral_le χ hu0)

lemma complexGeneratingTailTerm_eq_summand {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : ℝ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    complexGeneratingTailTerm χ u n t =
      generatingSummandHom χ (u : ℂ)
        (ne_zero_of_one_lt_re (show 1 < (1 + (t : ℂ)).re by simpa using ht)) (n + 2) := by
  have hn : n + 2 ≠ 0 := by omega
  unfold complexGeneratingTailTerm realGeneratingTailTerm
  simp only [generatingSummandHom, dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rw [omegaWeightHom_apply hn]
  simp only [ofReal_mul, ofReal_pow, ofReal_cpow (by positivity : (0 : ℝ) ≤ n + 2),
    ofReal_neg, ofReal_add, ofReal_one, ofReal_natCast, ofReal_ofNat, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The exact termwise integral identity for every Dirichlet character, justified by absolute
summability of the integrals of norms. No coefficient-interchange hypothesis is assumed. -/
lemma integratedGeneratingValue_eq_weighted_series {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    integratedGeneratingValue χ u = ∑' n, weightedCharacterTerm χ u n := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1.le
  calc
    integratedGeneratingValue χ u = ∫ t : ℝ in Ioi 0, ∑' n, complexGeneratingTailTerm χ u n t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
      rw [generatingValue_sub_one_eq_tail χ hu hs]
      apply tsum_congr
      intro n
      exact (complexGeneratingTailTerm_eq_summand χ u ht n).symm
    _ = ∑' n, ∫ t : ℝ in Ioi 0, complexGeneratingTailTerm χ u n t :=
      (integral_tsum_of_summable_integral_norm (complexGeneratingTailTerm_integrable χ u)
        (complexGeneratingTailTerm_norm_integrals_summable χ hu0 hu1)).symm
    _ = _ := tsum_congr (fun n => integral_complexGeneratingTailTerm χ u n)

lemma weightedCharacterTerm_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (weightedCharacterTerm χ u) := by
  have h := (hasSum_integral_of_summable_integral_norm (complexGeneratingTailTerm_integrable χ u)
    (complexGeneratingTailTerm_norm_integrals_summable χ hu0 hu1)).summable
  simpa only [integral_complexGeneratingTailTerm] using h

end Apicella143

end

-- module Apicella143.LogWeights
noncomputable section
open Complex
open scoped ArithmeticFunction.Omega ENNReal

namespace Apicella143

def natWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.log n)

@[simp] lemma natWeight_zero : natWeight 0 = 0 := by simp [natWeight]
@[simp] lemma natWeight_one : natWeight 1 = 0 := by simp [natWeight]

lemma natWeight_nonneg (n : ℕ) : 0 ≤ natWeight n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hlog := Real.log_nonneg hnR
    unfold natWeight
    positivity

lemma natWeight_pos {n : ℕ} (hn : 2 ≤ n) : 0 < natWeight n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_pos (show (1 : ℝ) < n by linarith)
  unfold natWeight
  positivity

lemma weight_nat_eq_ofReal (n : ℕ) : weight n = ENNReal.ofReal (natWeight n) := by
  simp [weight, natWeight]

def realAbelTerm (u : ℝ) (n : ℕ) : ℝ := u ^ Ω n * natWeight n

@[simp] lemma realAbelTerm_zero (u : ℝ) : realAbelTerm u 0 = 0 := by simp [realAbelTerm]
@[simp] lemma realAbelTerm_one (u : ℝ) : realAbelTerm u 1 = 0 := by simp [realAbelTerm]

lemma realAbelTerm_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ realAbelTerm u n :=
  mul_nonneg (pow_nonneg hu _) (natWeight_nonneg n)

lemma realAbelTerm_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (realAbelTerm u) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [realAbelTerm, natWeight, Nat.cast_add, Nat.cast_ofNat, mul_one_div] using
    weighted_log_series_summable hu0 hu1

def fullWeightedCharacterTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) (n : ℕ) : ℂ :=
  χ n * (realAbelTerm u n : ℂ)

@[simp] lemma fullWeightedCharacterTerm_zero {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) :
    fullWeightedCharacterTerm χ u 0 = 0 := by simp [fullWeightedCharacterTerm]
@[simp] lemma fullWeightedCharacterTerm_one {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) :
    fullWeightedCharacterTerm χ u 1 = 0 := by simp [fullWeightedCharacterTerm]

lemma fullWeightedCharacterTerm_shift {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) (n : ℕ) :
    fullWeightedCharacterTerm χ u (n + 2) = weightedCharacterTerm χ u n := by
  unfold fullWeightedCharacterTerm weightedCharacterTerm realAbelTerm natWeight
  push_cast
  ring

lemma fullWeightedCharacterTerm_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (fullWeightedCharacterTerm χ u) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [fullWeightedCharacterTerm_shift] using weightedCharacterTerm_summable χ hu0 hu1

lemma integratedGeneratingValue_eq_full_series {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    integratedGeneratingValue χ u = ∑' n, fullWeightedCharacterTerm χ u n := by
  rw [integratedGeneratingValue_eq_weighted_series χ hu0 hu1]
  have h := (fullWeightedCharacterTerm_summable χ hu0 hu1).sum_add_tsum_nat_add 2
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, fullWeightedCharacterTerm_zero,
    fullWeightedCharacterTerm_one, zero_add, fullWeightedCharacterTerm_shift] using h

end Apicella143

end

-- module Apicella143.Progressions
noncomputable section
open Complex DirichletCharacter
open scoped BigOperators

namespace Apicella143

def progressionTerm (N : ℕ) (b : ZMod N) (u : ℝ) (n : ℕ) : ℝ :=
  if (n : ZMod N) = b then realAbelTerm u n else 0

def progressionMass (N : ℕ) (b : ZMod N) (u : ℝ) : ℝ := ∑' n, progressionTerm N b u n

lemma progressionTerm_nonneg {N : ℕ} (b : ZMod N) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ progressionTerm N b u n := by
  unfold progressionTerm
  split_ifs
  · exact realAbelTerm_nonneg hu n
  · exact le_rfl

lemma progressionTerm_summable {N : ℕ} (b : ZMod N) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (progressionTerm N b u) := by
  apply (realAbelTerm_summable hu0 hu1).of_nonneg_of_le (progressionTerm_nonneg b hu0)
  intro n
  unfold progressionTerm
  split_ifs
  · exact le_rfl
  · exact realAbelTerm_nonneg hu0 n

lemma progressionMass_nonneg {N : ℕ} (b : ZMod N) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ progressionMass N b u := tsum_nonneg (progressionTerm_nonneg b hu)

lemma progressionTerm_orthogonality {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    (u : ℝ) (n : ℕ) :
    (progressionTerm N b u n : ℂ) = (N.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ N, χ b⁻¹ * fullWeightedCharacterTerm χ u n := by
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'
  rw [eq_inv_mul_iff_mul_eq₀ hφ]
  simp only [fullWeightedCharacterTerm, ← mul_assoc, ← Finset.sum_mul,
    sum_char_inv_mul_char_eq ℂ hb (n : ZMod N)]
  by_cases hn : (n : ZMod N) = b
  · simp [progressionTerm, hn]
  · simp [progressionTerm, hn, Ne.symm hn]

/-- Orthogonality after the absolutely justified weighted summation. -/
lemma progressionMass_orthogonality {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (progressionMass N b u : ℂ) = (N.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ N, χ b⁻¹ * integratedGeneratingValue χ u := by
  unfold progressionMass
  rw [Complex.ofReal_tsum]
  simp_rw [progressionTerm_orthogonality hb]
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun χ _ => (fullWeightedCharacterTerm_summable χ hu0 hu1).mul_left _)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [tsum_mul_left, integratedGeneratingValue_eq_full_series χ hu0 hu1]

lemma principal_character_inverse_unit {N : ℕ} {b : ZMod N} (hb : IsUnit b) :
    (1 : DirichletCharacter ℂ N) b⁻¹ = 1 := by
  have h := congrArg (fun x : ZMod N => (1 : DirichletCharacter ℂ N) x) (ZMod.inv_mul_of_unit b hb)
  simpa only [map_mul, map_one, MulChar.one_apply hb, mul_one] using h

lemma progressionMass_natCast_congr {N M b c : ℕ} (hNM : N = M) (hbc : b = c) (u : ℝ) :
    progressionMass N (b : ZMod N) u = progressionMass M (c : ZMod M) u := by
  subst M
  subst c
  rfl

end Apicella143

end

-- module Apicella143.MomentKernel
noncomputable section
open MeasureTheory Set

namespace Apicella143

lemma real_log_moment_integral {n : ℝ} (hn : 1 < n) :
    (∫ t : ℝ in Ioi 0, t * n ^ (-(1 + t))) = 1 / (n * (Real.log n) ^ 2) := by
  have hlog := Real.log_pos hn
  have hgamma : Real.Gamma (2 : ℝ) = 1 := by
    simp
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := Real.log n) (by norm_num) hlog
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, hgamma, mul_one] at hI
  have hfun : (fun t : ℝ => t * n ^ (-(1 + t))) =
      fun t : ℝ => n⁻¹ * (t * Real.exp (-(Real.log n * t))) := by
    funext t
    rw [weight_integrand_factorization hn]
    simp only [neg_mul]
    ring
  rw [hfun, integral_const_mul, hI]
  simp only [one_div, mul_inv_rev, inv_pow]
  ring

/-- A polynomial factor can be absorbed by halving an exponential decay rate. -/
lemma linear_exp_tail {c : ℝ} (hc : 0 < c) (t : ℝ) :
    t * Real.exp ((-c) * t) ≤ (2 / c) * Real.exp ((-(c / 2)) * t) := by
  have h : (c / 2) * t ≤ Real.exp ((c / 2) * t) := by
    linarith [Real.add_one_le_exp ((c / 2) * t)]
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos ((-c) * t)).le
  rw [← Real.exp_add] at hmul
  have he : (c / 2) * t + (-c) * t = (-(c / 2)) * t := by ring
  rw [he] at hmul
  calc
    t * Real.exp ((-c) * t) ≤ Real.exp ((-(c / 2)) * t) / (c / 2) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < c / 2)).2
      nlinarith [hmul]
    _ = _ := by field_simp

end Apicella143

end

-- module Apicella143.MomentIntegrability
noncomputable section
open MeasureTheory Set Complex

namespace Apicella143

lemma global_first_moment_integrable :
    IntegrableOn (fun t : ℝ => (t : ℂ) *
      (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ)) - 1)) (Ioi 0) := by
  have hu : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) *
      (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ)) - 1)) (Ioi 0) :=
    continuous_ofReal.continuousOn.mul
      ((generatingValue_continuousOn_positive (1 : DirichletCharacter ℂ 1) hu).sub
        (continuousOn_const (c := (1 : ℂ))))
  obtain ⟨eps, heps0, heps1, hsmall⟩ := global_generating_local_upper
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply integrableOn_Ioi_of_power_exp_bounds hcont heps0 heps1
    (a := 0) (by norm_num) (show 0 < Real.log 2 / 2 by positivity)
    (C := 0) (D := 5) (E := tailMajorantConst * (2 / Real.log 2))
  · intro t ht hteps
    have hm := hsmall 1 (by norm_num) (by norm_num) t ht hteps
    simp only [Complex.ofReal_one, Real.rpow_neg_one] at hm
    have hm' := mul_le_mul_of_nonneg_left hm ht.le
    have hcancel : t * (4 * t⁻¹) = 4 := by field_simp
    rw [hcancel] at hm'
    have hn := norm_sub_le (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ))) (1 : ℂ)
    simp only [norm_one] at hn
    have hn' := mul_le_mul_of_nonneg_left hn ht.le
    rw [norm_mul, Complex.norm_of_nonneg ht.le]
    simp only [Real.rpow_zero, mul_one, zero_add]
    nlinarith [hteps.trans heps1]
  · intro t ht
    have ht0 : 0 ≤ t := by linarith
    rw [norm_mul, Complex.norm_of_nonneg ht0]
    have hb := mul_le_mul_of_nonneg_left (generatingValue_tail_bound (1 : DirichletCharacter ℂ 1) hu ht) ht0
    have he := mul_le_mul_of_nonneg_left (linear_exp_tail hc t) tailMajorantConst_nonneg
    nlinarith [hb, he]

def realMomentTerm (n : ℕ) (t : ℝ) : ℝ := max t 0 * realGeneratingTailTerm 1 n t

lemma realMomentTerm_nonneg (n : ℕ) (t : ℝ) : 0 ≤ realMomentTerm n t :=
  mul_nonneg (le_max_right _ _) (realGeneratingTailTerm_nonneg (by norm_num) n t)

lemma realMomentTerm_continuous (n : ℕ) : Continuous (realMomentTerm n) := by
  have hbase : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hp : Continuous (fun t : ℝ => ((n : ℝ) + 2) ^ (-(1 + t))) :=
    (Real.continuous_const_rpow hbase).comp ((continuous_const (y := (1 : ℝ))).add continuous_id).neg
  have hm : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  unfold realMomentTerm realGeneratingTailTerm
  have h := hm.mul hp
  simp only [Pi.mul_def] at h
  simpa only [one_pow, one_mul] using h

lemma realMomentTerm_summable {t : ℝ} (ht : 0 < t) : Summable (fun n => realMomentTerm n t) :=
  (realGeneratingTailTerm_summable (by norm_num : (0 : ℝ) ≤ 1) (by norm_num) ht).mul_left _

lemma realMoment_sum_eq_norm {t : ℝ} (ht : 0 < t) :
    (∑' n, realMomentTerm n t) = ‖(t : ℂ) *
      (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ)) - 1)‖ := by
  simp only [realMomentTerm, tsum_mul_left, max_eq_left ht.le, norm_mul, Complex.norm_of_nonneg ht.le]
  have h := global_sub_one_norm_eq_real_tail (u := 1) (by norm_num) (by norm_num) ht
  simpa only [Complex.ofReal_one] using congrArg (fun x : ℝ => t * x) h.symm

lemma realMoment_sum_integrable :
    IntegrableOn (fun t : ℝ => ∑' n, realMomentTerm n t) (Ioi 0) := by
  exact global_first_moment_integrable.norm.congr
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => (realMoment_sum_eq_norm ht).symm))

lemma realMomentTerm_integrable (n : ℕ) : IntegrableOn (realMomentTerm n) (Ioi 0) := by
  apply realMoment_sum_integrable.mono' (realMomentTerm_continuous n).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (realMomentTerm_nonneg n t)]
  exact (realMomentTerm_summable ht).le_tsum n (fun i _ => realMomentTerm_nonneg i t)

lemma integral_realMomentTerm (n : ℕ) :
    (∫ t : ℝ in Ioi 0, realMomentTerm n t) =
      1 / (((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ 2) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, t * ((n : ℝ) + 2) ^ (-(1 + t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      simp only [realMomentTerm, realGeneratingTailTerm, max_eq_left ht0.le, one_pow, one_mul]
    _ = _ := real_log_moment_integral (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- The full logarithmic second moment converges; this controls every fixed gcd/log shift
in the passage to noninvertible residue classes. -/
lemma log_squared_weight_summable :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ 2)) := by
  have h := summable_integral_of_integrable_tsum_nonneg realMomentTerm realMomentTerm_integrable
    realMomentTerm_nonneg
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => realMomentTerm_summable ht))
    realMoment_sum_integrable
  simpa only [integral_realMomentTerm] using h

end Apicella143

end

-- module Apicella143.LogShift
noncomputable section
open scoped ArithmeticFunction.Omega

namespace Apicella143

def momentWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) * (Real.log n) ^ 2)
@[simp] lemma momentWeight_zero : momentWeight 0 = 0 := by simp [momentWeight]
@[simp] lemma momentWeight_one : momentWeight 1 = 0 := by simp [momentWeight]

lemma momentWeight_nonneg (n : ℕ) : 0 ≤ momentWeight n := by unfold momentWeight; positivity

lemma momentWeight_summable : Summable momentWeight := by
  apply (summable_nat_add_iff 2).mp
  simpa only [momentWeight, Nat.cast_add, Nat.cast_ofNat] using log_squared_weight_summable

/-- The elementary logarithmic-shift loss, with both its sign and its summable bound. -/
lemma log_shift_difference {x y : ℝ} (hx : 1 < x) (hy : 0 ≤ y) :
    0 ≤ 1 / (x * Real.log x) - 1 / (x * (Real.log x + y)) ∧
    1 / (x * Real.log x) - 1 / (x * (Real.log x + y)) ≤ y / (x * (Real.log x) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hly : 0 < Real.log x + y := by linarith
  constructor
  · apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · have hid : 1 / (x * Real.log x) - 1 / (x * (Real.log x + y)) =
        y / (x * Real.log x * (Real.log x + y)) := by field_simp; ring
    rw [hid]
    apply div_le_div_of_nonneg_left hy (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hx0.le hl.le) hy]

lemma natWeight_mul_formula {g m : ℕ} (hg : 1 ≤ g) (hm : 2 ≤ m) :
    natWeight (g * m) = (g : ℝ)⁻¹ * (1 / ((m : ℝ) * (Real.log m + Real.log g))) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold natWeight
  rw [Nat.cast_mul, Real.log_mul hg0 hm0]
  simp only [one_div, mul_inv_rev]
  ring

lemma realAbelTerm_mul_lower_of_two_le {g m : ℕ} (hg : 1 ≤ g) (hm : 2 ≤ m)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u ^ Ω g / (g : ℝ)) * realAbelTerm u m - (Real.log g / (g : ℝ)) * momentWeight m ≤
      realAbelTerm u (g * m) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hmR : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlg : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by exact_mod_cast hg)
  have hA0 : 0 ≤ u ^ Ω g := pow_nonneg hu0 _
  have hB0 : 0 ≤ u ^ Ω m := pow_nonneg hu0 _
  have hA1 : u ^ Ω g ≤ 1 := pow_le_one₀ hu0 hu1
  have hB1 : u ^ Ω m ≤ 1 := pow_le_one₀ hu0 hu1
  have hAB0 : 0 ≤ u ^ Ω g * u ^ Ω m := mul_nonneg hA0 hB0
  have hAB1 : u ^ Ω g * u ^ Ω m ≤ 1 := by nlinarith
  have hloss := (log_shift_difference hmR hlg).2
  have hloss0 : 0 ≤ Real.log g / ((m : ℝ) * (Real.log m) ^ 2) := by positivity
  have hcoeff := div_le_div_of_nonneg_right hAB1 hgR.le
  have hbound : (u ^ Ω g * u ^ Ω m / (g : ℝ)) *
      (natWeight m - 1 / ((m : ℝ) * (Real.log m + Real.log g))) ≤
      (Real.log g / (g : ℝ)) * momentWeight m := by
    calc
      _ ≤ (u ^ Ω g * u ^ Ω m / (g : ℝ)) *
          (Real.log g / ((m : ℝ) * (Real.log m) ^ 2)) :=
        mul_le_mul_of_nonneg_left hloss (div_nonneg hAB0 hgR.le)
      _ ≤ (1 / (g : ℝ)) * (Real.log g / ((m : ℝ) * (Real.log m) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcoeff hloss0
      _ = _ := by unfold momentWeight; ring
  have hΩ := ArithmeticFunction.cardFactors_mul (by omega : g ≠ 0) (by omega : m ≠ 0)
  have hid : (u ^ Ω g / (g : ℝ)) * realAbelTerm u m - realAbelTerm u (g * m) =
      (u ^ Ω g * u ^ Ω m / (g : ℝ)) *
        (natWeight m - 1 / ((m : ℝ) * (Real.log m + Real.log g))) := by
    unfold realAbelTerm
    rw [hΩ, pow_add, natWeight_mul_formula hg hm]
    ring
  rw [← hid] at hbound
  linarith

lemma realAbelTerm_mul_lower {g m : ℕ} (hg : 1 ≤ g) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u ^ Ω g / (g : ℝ)) * realAbelTerm u m - (Real.log g / (g : ℝ)) * momentWeight m ≤
      realAbelTerm u (g * m) := by
  by_cases hm : 2 ≤ m
  · exact realAbelTerm_mul_lower_of_two_le hg hm hu0 hu1
  · have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · simp
    · simpa using realAbelTerm_nonneg hu0 g

end Apicella143

end

-- module Apicella143.ProgressionScaling
noncomputable section
open scoped ArithmeticFunction.Omega

namespace Apicella143

def shiftPenalty (g : ℕ) : ℝ := (Real.log g / (g : ℝ)) * ∑' n, momentWeight n

lemma progressionTerm_scale_lower {g M c n : ℕ} (hg : 1 ≤ g)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u ^ Ω g / (g : ℝ)) * progressionTerm M (c : ZMod M) u n -
      (Real.log g / (g : ℝ)) * momentWeight n ≤
      progressionTerm (g * M) ((g * c : ℕ) : ZMod (g * M)) u (g * n) := by
  by_cases hmod : (n : ZMod M) = (c : ZMod M)
  · have hnat := (ZMod.natCast_eq_natCast_iff n c M).mp hmod
    have hscaled : ((g * n : ℕ) : ZMod (g * M)) = ((g * c : ℕ) : ZMod (g * M)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hnat.mul_left' g)
    simpa only [progressionTerm, if_pos hmod, if_pos hscaled] using realAbelTerm_mul_lower (m := n) hg hu0 hu1
  · have hlg : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by exact_mod_cast hg)
    have hp : 0 ≤ (Real.log g / (g : ℝ)) * momentWeight n :=
      mul_nonneg (div_nonneg hlg (Nat.cast_nonneg _)) (momentWeight_nonneg n)
    calc
      _ = -(Real.log g / (g : ℝ)) * momentWeight n := by simp [progressionTerm, hmod]
      _ ≤ 0 := by nlinarith
      _ ≤ _ := progressionTerm_nonneg _ hu0 _

/-- Multiplication by g gives a subset of the required residue class. The loss is bounded
by one fixed, proved finite logarithmic moment, uniformly in 0≤u<1. -/
lemma progressionMass_scale_lower {g M c : ℕ} (hg : 1 ≤ g)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (u ^ Ω g / (g : ℝ)) * progressionMass M (c : ZMod M) u - shiftPenalty g ≤
      progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u := by
  have hinj : Function.Injective (fun n : ℕ => g * n) := by
    intro n m h
    exact mul_left_cancel₀ (by omega : g ≠ 0) h
  have hM := progressionTerm_summable (c : ZMod M) hu0 hu1
  have hT := progressionTerm_summable (((g * c : ℕ) : ZMod (g * M))) hu0 hu1
  have hmap := hT.comp_injective hinj
  have hsrc := (hM.mul_left (u ^ Ω g / (g : ℝ))).sub
    (momentWeight_summable.mul_left (Real.log g / (g : ℝ)))
  have hle := hsrc.tsum_le_tsum (fun n => progressionTerm_scale_lower (M := M) (c := c) (n := n) hg hu0 hu1.le) hmap
  rw [Summable.tsum_sub (hM.mul_left _) (momentWeight_summable.mul_left _), tsum_mul_left, tsum_mul_left] at hle
  have hsubset := hmap.tsum_le_tsum_of_inj (fun n : ℕ => g * n) hinj
    (fun n _ => progressionTerm_nonneg _ hu0 n) (fun _ => le_rfl) hT
  exact hle.trans hsubset

end Apicella143

end

-- module Apicella143.AbelBounds
noncomputable section
open Filter
open scoped Topology

namespace Apicella143

/-- A lower limit along the real Abel parameter u→1 from below, expressed without
conditional completeness conventions for `liminf`. -/
def HasAbelLowerBound (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ a : ℝ, a < c → ∀ᶠ u : ℝ in 𝓝[<] 1, a ≤ f u

lemma hasAbelLowerBound_of_tendsto_minorant {f g : ℝ → ℝ} {c : ℝ}
    (hg : Tendsto g (𝓝[<] 1) (𝓝 c)) (hfg : ∀ᶠ u : ℝ in 𝓝[<] 1, g u ≤ f u) :
    HasAbelLowerBound f c := by
  intro a ha
  filter_upwards [hg.eventually (eventually_gt_nhds ha), hfg] with u hu hgu
  exact hu.le.trans hgu

lemma HasAbelLowerBound.mono {f g : ℝ → ℝ} {c : ℝ} (hf : HasAbelLowerBound f c)
    (hfg : ∀ᶠ u : ℝ in 𝓝[<] 1, f u ≤ g u) : HasAbelLowerBound g c := by
  intro a ha
  filter_upwards [hf a ha, hfg] with u hau hfu
  exact hau.trans hfu

lemma HasAbelLowerBound.add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasAbelLowerBound f a) (hg : HasAbelLowerBound g b) :
    HasAbelLowerBound (fun u => f u + g u) (a + b) := by
  intro c hc
  let e := (a + b - c) / 2
  have he : 0 < e := by dsimp [e]; linarith
  filter_upwards [hf (a - e) (by linarith), hg (b - e) (by linarith)] with u hfu hgu
  dsimp [e] at hfu hgu
  linarith

lemma hasAbelLowerBound_of_tendsto {f : ℝ → ℝ} {a : ℝ} (hf : Tendsto f (𝓝[<] 1) (𝓝 a)) :
    HasAbelLowerBound f a := hasAbelLowerBound_of_tendsto_minorant hf (Eventually.of_forall (fun _ => le_rfl))

lemma HasAbelLowerBound.add_vanishing {f g : ℝ → ℝ} {a : ℝ}
    (hf : HasAbelLowerBound f a) (hg : Tendsto g (𝓝[<] 1) (𝓝 0)) :
    HasAbelLowerBound (fun u => f u + g u) a := by
  simpa only [add_zero] using hf.add (hasAbelLowerBound_of_tendsto hg)

lemma HasAbelLowerBound.mul_pos {f : ℝ → ℝ} {a b : ℝ} (hf : HasAbelLowerBound f a)
    (hb : 0 < b) : HasAbelLowerBound (fun u => b * f u) (b * a) := by
  intro c hc
  have hca : c / b < a := (div_lt_iff₀ hb).2 (by simpa [mul_comm] using hc)
  filter_upwards [hf (c / b) hca] with u hu
  have h := mul_le_mul_of_nonneg_left hu hb.le
  simpa only [mul_div_cancel₀ _ hb.ne'] using h

lemma HasAbelLowerBound.sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ} {a : ι → ℝ}
    (h : ∀ i ∈ S, HasAbelLowerBound (f i) (a i)) :
    HasAbelLowerBound (fun u => ∑ i ∈ S, f i u) (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (hasAbelLowerBound_of_tendsto (tendsto_const_nhds (x := (0 : ℝ))))
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using (h i (by simp)).add
      (ih (fun j hj => h j (by simp [hj])))

lemma HasAbelLowerBound.mul_tendsto_pos {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasAbelLowerBound f a) (ha : 0 < a) (hg : Tendsto g (𝓝[<] 1) (𝓝 b)) (hb : 0 < b) :
    HasAbelLowerBound (fun u => g u * f u) (b * a) := by
  intro c hc
  have hgpos := hg.eventually (eventually_gt_nhds hb)
  by_cases hc0 : c < 0
  · filter_upwards [hf (a / 2) (by linarith), hgpos] with u hfu hgu
    have hfu0 : 0 ≤ f u := by linarith
    exact hc0.le.trans (mul_nonneg hgu.le hfu0)
  · have hc0' : 0 ≤ c := le_of_not_gt hc0
    let d := (c / b + a) / 2
    have hdiv : c / b < a := (div_lt_iff₀ hb).2 (by simpa [mul_comm] using hc)
    have hda : d < a := by dsimp [d]; linarith
    have hcd : c < b * d := by
      dsimp [d]
      have hcancel : b * (c / b) = c := by field_simp
      nlinarith
    have hgd := (hg.mul_const d).eventually (eventually_gt_nhds hcd)
    filter_upwards [hf d hda, hgpos, hgd] with u hfu hgu hprod
    exact hprod.le.trans (mul_le_mul_of_nonneg_left hfu hgu.le)

end Apicella143

end

-- module Apicella143.PrincipalAbel
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Apicella143

def principalRealIntegrand (N : ℕ) (u t : ℝ) : ℝ :=
  ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ))‖ - 1

lemma principalRealIntegrand_eq_re {N : ℕ} {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    (generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ)) - 1).re =
      principalRealIntegrand N u t := by
  have hs : (1 : ℝ) < 1 + t := by linarith
  have heq := principalGeneratingValue_eq_real_sum (N := N) (u := u) hs
  simp only [ofReal_add, ofReal_one] at heq
  unfold principalRealIntegrand
  rw [heq, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.norm_of_nonneg (tsum_nonneg (principalGeneratingTerm_nonneg hu))]

lemma principalRealIntegrand_nonneg {N : ℕ} {u t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht : 0 < t) : 0 ≤ principalRealIntegrand N u t := by
  have h := principalGeneratingValue_norm_one_le (N := N) hu0 hu1 (show (1 : ℝ) < 1 + t by linarith)
  simp only [ofReal_add, ofReal_one] at h
  exact sub_nonneg.mpr h

lemma principalRealIntegrand_integrable {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (principalRealIntegrand N u) (Ioi 0) := by
  have h := (generatingValue_sub_one_integrable (1 : DirichletCharacter ℂ N) hu0 hu1).re
  apply h.congr
  exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => principalRealIntegrand_eq_re hu0 ht)

lemma principal_integrated_re_eq_real_integral {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re =
      ∫ t : ℝ in Ioi 0, principalRealIntegrand N u t := by
  have h := generatingValue_sub_one_integrable (1 : DirichletCharacter ℂ N) hu0 hu1
  calc
    _ = ∫ t : ℝ in Ioi 0, (generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ)) - 1).re := by
      exact (Complex.reCLM.integral_comp_comm h).symm
    _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun t ht => principalRealIntegrand_eq_re hu0 ht)

lemma integral_Ioo_neg_rpow {u eps : ℝ} (hu : u < 1) (heps : 0 < eps) :
    (∫ t : ℝ in Ioo 0 eps, t ^ (-u)) = eps ^ (1 - u) / (1 - u) := by
  have h := integral_rpow (a := 0) (b := eps) (r := -u) (Or.inl (by linarith : -1 < -u))
  rw [intervalIntegral.integral_of_le heps.le, integral_Ioc_eq_integral_Ioo] at h
  have he : -u + 1 = 1 - u := by ring
  simpa only [he, Real.zero_rpow (by linarith : 1 - u ≠ 0), sub_zero] using h

lemma integral_abel_power_kernel {u eps k : ℝ} (hu : u < 1) (heps : 0 < eps) :
    (∫ t : ℝ in Ioo 0 eps, (k / 4) ^ u * t ^ (-u) - 1) =
      (k / 4) ^ u * eps ^ (1 - u) / (1 - u) - eps := by
  have hp : IntegrableOn (fun t : ℝ => t ^ (-u)) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps).2 (by linarith)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  rw [integral_sub (hp.const_mul _) hc, integral_const_mul, integral_Ioo_neg_rpow hu heps,
    setIntegral_const, Real.volume_real_Ioo, sub_zero, max_eq_left heps.le]
  simp only [smul_eq_mul, mul_one]
  ring

lemma principal_integrated_re_lower {N : ℕ} [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ ∀ u : ℝ, 0 ≤ u → u < 1 →
      (totientRatio N / 4) ^ u * eps ^ (1 - u) / (1 - u) - eps ≤
        (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re := by
  obtain ⟨eps, heps0, _heps1, hpoint⟩ := principal_generating_local_lower N
  refine ⟨eps, heps0, ?_⟩
  intro u hu0 hu1
  have hF := principalRealIntegrand_integrable (N := N) hu0 hu1
  have hFI : IntegrableOn (principalRealIntegrand N u) (Ioo 0 eps) := hF.mono_set Ioo_subset_Ioi_self
  have hp : IntegrableOn (fun t : ℝ => t ^ (-u)) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps0).2 (by linarith)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  rw [principal_integrated_re_eq_real_integral hu0 hu1, ← integral_abel_power_kernel hu1 heps0]
  calc
    _ ≤ ∫ t : ℝ in Ioo 0 eps, principalRealIntegrand N u t := by
      apply integral_mono_ae ((hp.const_mul _).sub hc) hFI
      apply ae_restrict_of_forall_mem measurableSet_Ioo
      intro t ht
      have h := hpoint u hu0 hu1.le t ht.1 ht.2.le
      have hratio : totientRatio N / (4 * t) = (totientRatio N / 4) / t := by ring
      have hk0 : (0 : ℝ) ≤ totientRatio N / 4 := div_nonneg (totientRatio_pos N).le (by norm_num)
      rw [hratio, Real.div_rpow hk0 ht.1.le, div_eq_mul_inv, ← Real.rpow_neg ht.1.le] at h
      exact sub_le_sub_right h 1
    _ ≤ _ := setIntegral_mono_set hF
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => principalRealIntegrand_nonneg hu0 hu1.le ht))
      (Eventually.of_forall (fun _ ht => ht.1))

/-- The principal character supplies the positive Abel lower bound φ(N)/(4N). -/
lemma principal_abel_lower_bound (N : ℕ) [NeZero N] :
    HasAbelLowerBound (fun u : ℝ => (1 - u) *
      (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re) (totientRatio N / 4) := by
  obtain ⟨eps, heps, hlower⟩ := principal_integrated_re_lower (N := N)
  let g : ℝ → ℝ := fun u => (totientRatio N / 4) ^ u * eps ^ (1 - u) - (1 - u) * eps
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hk : totientRatio N / 4 ≠ 0 := ne_of_gt (div_pos (totientRatio_pos N) (by norm_num))
  have hg : Tendsto g (𝓝[<] 1) (𝓝 (totientRatio N / 4)) := by
    have ha := (tendsto_const_nhds (x := totientRatio N / 4)).rpow hid (Or.inl hk)
    have hb := (tendsto_const_nhds (x := eps)).rpow
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hid) (Or.inl heps.ne')
    have hc := ((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const eps
    simpa only [g, sub_self, Real.rpow_zero, Real.rpow_one, mul_one, zero_mul, sub_zero] using (ha.mul hb).sub hc
  apply hasAbelLowerBound_of_tendsto_minorant hg
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  have h := mul_le_mul_of_nonneg_left (hlower u hu.1.le hu.2) (sub_nonneg.mpr hu.2.le)
  have hne : 1 - u ≠ 0 := by linarith [hu.2]
  dsimp [g]
  have heq : (totientRatio N / 4) ^ u * eps ^ (1 - u) - (1 - u) * eps =
      (1 - u) * ((totientRatio N / 4) ^ u * eps ^ (1 - u) / (1 - u) - eps) := by
    rw [mul_sub, mul_div_cancel₀ _ hne]
  exact (le_of_eq heq).trans h

end Apicella143

end

-- module Apicella143.NonprincipalAbel
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Apicella143

/-- The character integrals stay bounded uniformly in the real Abel parameter, including u=1. -/
lemma nonprincipal_integratedGeneratingValue_bounded {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖integratedGeneratingValue χ u‖ ≤ K := by
  obtain ⟨C, hC0, hC⟩ := nonprincipal_generatingValue_bounded χ hχ
  let g : ℝ → ℝ := fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => C + 1) t +
    tailMajorantConst * Real.exp ((-Real.log 2) * t)
  have hind : IntegrableOn (fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => C + 1) t) (Ioi 0) := by
    have hc : IntegrableOn (fun _ : ℝ => C + 1) (Ioc 0 1) :=
      (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ioc_subset_Icc_self
    exact (hc.integrable_indicator measurableSet_Ioc).integrableOn
  have hexp : IntegrableOn (fun t => tailMajorantConst * Real.exp ((-Real.log 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]) 0).const_mul _
  have hg : IntegrableOn g (Ioi 0) := hind.add hexp
  have hg0 (t : ℝ) : 0 ≤ g t := by
    unfold g
    apply add_nonneg
    · by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem ht]
        linarith
      · rw [indicator_of_notMem ht]
    · exact mul_nonneg tailMajorantConst_nonneg (Real.exp_pos _).le
  refine ⟨∫ t : ℝ in Ioi 0, g t, integral_nonneg hg0, ?_⟩
  intro u hu0 hu1
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  apply norm_integral_le_of_norm_le hg
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  change ‖generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1‖ ≤ g t
  unfold g
  by_cases ht1 : t ≤ 1
  · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩)]
    have hb := hC u hu0 hu1 t ht ht1
    have hn := norm_sub_le (generatingValue χ (u : ℂ) (1 + (t : ℂ))) (1 : ℂ)
    simp only [norm_one] at hn
    have he := mul_nonneg tailMajorantConst_nonneg (Real.exp_pos ((-Real.log 2) * t)).le
    linarith
  · rw [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 by intro h; exact ht1 h.2), zero_add]
    exact generatingValue_tail_bound χ hu (le_of_not_ge ht1)

/-- The nonprincipal contribution vanishes after Abel normalization. -/
lemma nonprincipal_normalized_integral_tendsto_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Tendsto (fun u : ℝ => (1 - (u : ℂ)) * integratedGeneratingValue χ u) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨K, _hK0, hK⟩ := nonprincipal_integratedGeneratingValue_bounded χ hχ
  have hbound : ∀ᶠ u : ℝ in 𝓝[<] 1,
      ‖(1 - (u : ℂ)) * integratedGeneratingValue χ u‖ ≤ (1 - u) * K := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
    have hu0 : 0 ≤ u := hu.1.le
    have hu1 : u ≤ 1 := hu.2.le
    have hnorm : ‖1 - (u : ℂ)‖ = 1 - u := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith)]
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_left (hK u hu0 hu1) (by linarith)
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun u : ℝ => (1 - u) * K) (𝓝[<] 1) (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const K
  exact squeeze_zero_norm' hbound hlim

end Apicella143

end

-- module Apicella143.CoprimeAbel
noncomputable section
open Filter Complex
open scoped BigOperators Topology

namespace Apicella143

def characterError {N : ℕ} [NeZero N] (b : ZMod N) (u : ℝ) : ℂ := by
  classical
  exact ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ N)).erase 1,
    χ b⁻¹ * ((1 - (u : ℂ)) * integratedGeneratingValue χ u)

lemma characterError_tendsto_zero {N : ℕ} [NeZero N] (b : ZMod N) :
    Tendsto (characterError b) (𝓝[<] 1) (𝓝 0) := by
  classical
  have h := tendsto_finset_sum ((Finset.univ : Finset (DirichletCharacter ℂ N)).erase 1)
    (fun χ hχ => (nonprincipal_normalized_integral_tendsto_zero χ (Finset.mem_erase.mp hχ).1).const_mul (χ b⁻¹))
  simp only [mul_zero, Finset.sum_const_zero] at h
  exact h

lemma normalized_progression_identity {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (1 - u) * progressionMass N b u = (N.totient : ℝ)⁻¹ *
      ((1 - u) * (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re + (characterError b u).re) := by
  classical
  have horth := progressionMass_orthogonality hb hu0 hu1
  have hcomplex : (1 - (u : ℂ)) * (progressionMass N b u : ℂ) = (N.totient : ℂ)⁻¹ *
      ((1 - (u : ℂ)) * integratedGeneratingValue (1 : DirichletCharacter ℂ N) u + characterError b u) := by
    calc
      _ = (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N,
          χ b⁻¹ * ((1 - (u : ℂ)) * integratedGeneratingValue χ u) := by
        rw [horth, mul_left_comm (1 - (u : ℂ)) (N.totient : ℂ)⁻¹, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        congr 1
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ N))]
        simp only [principal_character_inverse_unit hb, one_mul]
        exact add_comm _ _
  have hphi : (N.totient : ℂ)⁻¹ = (((N.totient : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  have huco : 1 - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; rfl
  rw [hphi, huco] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using hreal

/-- The required positive Abel lower bound in every invertible residue class. -/
lemma coprime_progression_abel_lower_bound {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * progressionMass N b u) (1 / (4 * (N : ℝ))) := by
  have hE : Tendsto (fun u => (characterError b u).re) (𝓝[<] 1) (𝓝 0) := by
    have h := (continuous_re.tendsto 0).comp (characterError_tendsto_zero b)
    simp only [Complex.zero_re] at h
    exact h
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have hscaled := ((principal_abel_lower_bound N).add_vanishing hE).mul_pos (inv_pos.mpr hφ)
  have heq : (N.totient : ℝ)⁻¹ * (totientRatio N / 4) = 1 / (4 * (N : ℝ)) := by
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    unfold totientRatio
    field_simp
  rw [heq] at hscaled
  apply hscaled.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  exact (normalized_progression_identity hb hu.1.le hu.2).symm.le

end Apicella143

end

-- module Apicella143.AllResiduesAbel
noncomputable section
open Filter
open scoped Topology ArithmeticFunction.Omega

namespace Apicella143

lemma scaled_progression_abel_lower_bound {g M c : ℕ} [NeZero M] (hg : 1 ≤ g)
    (hc : IsUnit (c : ZMod M)) :
    HasAbelLowerBound
      (fun u : ℝ => (1 - u) * progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u)
      (1 / (4 * ((g * M : ℕ) : ℝ))) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hMR : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hbase := coprime_progression_abel_lower_bound hc
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hcoef : Tendsto (fun u : ℝ => u ^ Ω g / (g : ℝ)) (𝓝[<] 1) (𝓝 (1 / (g : ℝ))) := by
    simpa only [one_pow] using (hid.pow (Ω g)).div_const (g : ℝ)
  have hmul := hbase.mul_tendsto_pos (by positivity : (0 : ℝ) < 1 / (4 * (M : ℝ)))
    hcoef (by positivity : (0 : ℝ) < 1 / (g : ℝ))
  have herr : Tendsto (fun u : ℝ => -(1 - u) * shiftPenalty g) (𝓝[<] 1) (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hid).neg).mul_const (shiftPenalty g)
  have hbound := hmul.add_vanishing herr
  have hconst : (1 / (g : ℝ)) * (1 / (4 * (M : ℝ))) = 1 / (4 * ((g * M : ℕ) : ℝ)) := by
    push_cast
    field_simp
  rw [hconst] at hbound
  apply hbound.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  have h := mul_le_mul_of_nonneg_left (progressionMass_scale_lower (M := M) (c := c) hg hu.1.le hu.2)
    (show 0 ≤ 1 - u by linarith [hu.2])
  convert h using 1 <;> first | rfl | ring

/-- The positive Abel lower bound includes every residue, with no coprimality omission. -/
lemma all_residues_abel_lower_bound (N : ℕ) [NeZero N] (b : ZMod N) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * progressionMass N b u) (1 / (4 * (N : ℝ))) := by
  let n : ℕ := b.val
  let g : ℕ := Nat.gcd n N
  let M : ℕ := N / g
  let c : ℕ := n / g
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right n (NeZero.pos N)
  have hM0 : 0 < M := Nat.div_pos (Nat.gcd_le_right n (NeZero.pos N)) hg0
  letI : NeZero M := ⟨hM0.ne'⟩
  have hcop : Nat.Coprime c M := Nat.coprime_div_gcd_div_gcd hg0
  have hc : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).2 hcop
  have h := scaled_progression_abel_lower_bound (g := g) (M := M) (c := c) (by omega) hc
  have hN : g * M = N := Nat.mul_div_cancel' (Nat.gcd_dvd_right n N)
  have hn : g * c = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n N)
  have hfun : (fun u : ℝ => (1 - u) * progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u) =
      fun u : ℝ => (1 - u) * progressionMass N b u := by
    funext u
    congr 1
    calc
      _ = progressionMass N (n : ZMod N) u := progressionMass_natCast_congr hN hn u
      _ = _ := by rw [show (n : ZMod N) = b from ZMod.natCast_zmod_val b]
  rw [hfun] at h
  simpa only [hN] using h

end Apicella143

end

-- module Apicella143.Levels
noncomputable section
open scoped ArithmeticFunction.Omega

namespace Apicella143

/-- Every positive Ω level is primitive; multiplicities are counted. -/
lemma omega_level_primitive {r : ℕ} (hr : 0 < r) :
    Primitive {n : ℕ | Ω n = r} := by
  intro m hm n hn hdiv
  have hm0 : m ≠ 0 := by
    intro hmz
    subst m
    simp only [Set.mem_setOf_eq, ArithmeticFunction.cardFactors_zero] at hm
    omega
  have hn0 : n ≠ 0 := by
    intro hnz
    subst n
    simp only [Set.mem_setOf_eq, ArithmeticFunction.cardFactors_zero] at hn
    omega
  obtain ⟨k, rfl⟩ := hdiv
  have hk0 : k ≠ 0 := by
    intro hk
    simp [hk] at hn0
  have hmul := ArithmeticFunction.cardFactors_mul hm0 hk0
  have hkΩ : Ω k = 0 := by
    simp only [Set.mem_setOf_eq] at hm hn
    omega
  have hk1 : k = 1 :=
    (ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hkΩ).resolve_left hk0
  simp [hk1]

lemma primitive_mono {P Q : Set ℕ} (hQ : Primitive Q) (hPQ : P ⊆ Q) : Primitive P := by
  intro m hm n hn hdiv
  exact hQ m (hPQ hm) n (hPQ hn) hdiv

/-- Therefore any finite truncation or residue restriction of a positive level is primitive. -/
lemma primitive_of_constant_omega {P : Set ℕ} {r : ℕ} (hr : 0 < r)
    (hP : ∀ n ∈ P, Ω n = r) : Primitive P :=
  primitive_mono (omega_level_primitive hr) hP

end Apicella143

end

-- module Apicella143.LayerDecomposition
noncomputable section
open scoped Classical
open scoped ArithmeticFunction.Omega

namespace Apicella143

lemma two_pow_length_le_prod (l : List ℕ) (hl : ∀ p ∈ l, 2 ≤ p) : 2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp : 2 ≤ p := hl p (by simp)
    have ht : ∀ q ∈ l, 2 ≤ q := fun q hq => hl q (by simp [hq])
    simp only [List.length_cons, List.prod_cons, pow_succ]
    exact (Nat.mul_le_mul_right 2 (ih ht)).trans
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right l.prod hp)

lemma two_pow_omega_le {n : ℕ} (hn : n ≠ 0) : 2 ^ Ω n ≤ n := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    _ ≤ n.primeFactorsList.prod := two_pow_length_le_prod _ (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    _ = n := Nat.prod_primeFactorsList hn

def setAbelMass (E : Set ℕ) (u : ℝ) : ℝ := ∑' n, E.indicator (realAbelTerm u) n

def layerMass (E : Set ℕ) (r : ℕ) : ℝ := ∑' n : {n : ℕ | Ω n = r}, E.indicator natWeight n

lemma layerMass_nonneg (E : Set ℕ) (r : ℕ) : 0 ≤ layerMass E r := by
  apply tsum_nonneg
  intro n
  exact Set.indicator_nonneg (fun _ _ => natWeight_nonneg _) _

lemma layerMass_eq_tsum_conditional (E : Set ℕ) (r : ℕ) :
    layerMass E r = ∑' n : ℕ, if Ω n = r ∧ n ∈ E then natWeight n else 0 := by
  classical
  rw [layerMass, tsum_subtype]
  apply tsum_congr
  intro n
  by_cases hr : Ω n = r <;> by_cases hE : n ∈ E <;>
    simp [hr, hE]

lemma layer_weight_summable (E : Set ℕ) (r : ℕ) :
    Summable (fun n : ℕ => if Ω n = r ∧ n ∈ E then natWeight n else 0) := by
  classical
  have hsum := (realAbelTerm_summable (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ((2 : ℝ) ^ r)
  apply hsum.of_nonneg_of_le
  · intro n
    split_ifs
    · exact natWeight_nonneg n
    · exact le_rfl
  · intro n
    by_cases hn : Ω n = r ∧ n ∈ E
    · rw [if_pos hn]
      unfold realAbelTerm
      rw [hn.1]
      have hcancel : (2 : ℝ) ^ r * (1 / 2) ^ r = 1 := by rw [← mul_pow]; norm_num
      rw [← mul_assoc, hcancel, one_mul]
    · rw [if_neg hn]
      exact mul_nonneg (by positivity) (realAbelTerm_nonneg (by norm_num) n)

lemma setAbelTerm_summable (E : Set ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (E.indicator (realAbelTerm u)) := (realAbelTerm_summable hu0 hu1).indicator E

/-- Grouping by Ω is justified by absolute summability, and counts multiplicity exactly. -/
lemma layer_abel_hasSum (E : Set ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun r : ℕ => u ^ r * layerMass E r) (setAbelMass E u) := by
  classical
  have hsum := (setAbelTerm_summable E hu0 hu1).hasSum.tsum_fiberwise Ω
  have hfiber (r : ℕ) :
      (∑' n : {n : ℕ | Ω n = r}, E.indicator (realAbelTerm u) n) = u ^ r * layerMass E r := by
    calc
      _ = ∑' n : {n : ℕ | Ω n = r}, u ^ r * E.indicator natWeight n := by
        apply tsum_congr
        intro n
        have hn : Ω (n : ℕ) = r := n.property
        by_cases hE : (n : ℕ) ∈ E
        · simp only [Set.indicator_of_mem hE, realAbelTerm, hn]
        · simp only [Set.indicator_of_notMem hE, mul_zero]
      _ = _ := tsum_mul_left
  change HasSum (fun r => ∑' n : {n : ℕ | Ω n = r}, E.indicator (realAbelTerm u) n)
    (setAbelMass E u) at hsum
  simpa only [hfiber] using hsum

lemma nat_le_two_pow (r : ℕ) : r ≤ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : 0 < 2 ^ r := pow_pos (by decide) _
    rw [pow_succ]
    omega

lemma omega_le_self (n : ℕ) : Ω n ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (nat_le_two_pow _).trans (two_pow_omega_le hn)

end Apicella143

end

-- module Apicella143.PeriodicMass
noncomputable section
open Filter
open scoped BigOperators Topology

namespace Apicella143

def periodicResidueSet (L : ℕ) (S : Finset (ZMod L)) : Set ℕ := {n | (n : ZMod L) ∈ S}

lemma setAbelMass_periodic (L : ℕ) (S : Finset (ZMod L)) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    setAbelMass (periodicResidueSet L S) u = ∑ b ∈ S, progressionMass L b u := by
  classical
  have hterm (n : ℕ) : (periodicResidueSet L S).indicator (realAbelTerm u) n =
      ∑ b ∈ S, progressionTerm L b u n := by
    simp [periodicResidueSet, progressionTerm, Set.indicator_apply]
  unfold setAbelMass
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun b _ => progressionTerm_summable b hu0 hu1)]
  rfl

/-- A fixed periodic set has an Abel lower bound proportional to all its residue classes. -/
lemma periodic_abel_lower_bound (L : ℕ) [NeZero L] (S : Finset (ZMod L)) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * setAbelMass (periodicResidueSet L S) u)
      ((S.card : ℝ) / (4 * (L : ℝ))) := by
  have h := HasAbelLowerBound.sum S (fun b _ => all_residues_abel_lower_bound L b)
  have hconstant : (∑ _b ∈ S, (1 / (4 * (L : ℝ)))) = (S.card : ℝ) / (4 * (L : ℝ)) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [hconstant] at h
  apply h.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  rw [setAbelMass_periodic L S hu.1.le hu.2, Finset.mul_sum]

end Apicella143

end

-- module Apicella143.AbelLayerSelection
noncomputable section
open Filter
open scoped Topology BigOperators

namespace Apicella143

lemma normalized_power_series_upper_of_tail {a : ℕ → ℝ} (ha : ∀ r, 0 ≤ a r)
    {c : ℝ} (hc : 0 ≤ c) (R : ℕ) (htail : ∀ r, R ≤ r → a r ≤ c)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hsum : Summable (fun r => u ^ r * a r)) :
    (1 - u) * (∑' r, u ^ r * a r) ≤ c + (1 - u) * ∑ r ∈ Finset.range R, a r := by
  let p : ℕ → ℝ := fun r => if r < R then a r else 0
  have hp0 : ∀ r ∉ Finset.range R, p r = 0 := by
    intro r hr
    simp only [Finset.mem_range] at hr
    simp [p, hr]
  have hpsum : Summable p := summable_of_ne_finset_zero hp0
  have hptsum : ∑' r, p r = ∑ r ∈ Finset.range R, a r := by
    rw [tsum_eq_sum hp0]
    apply Finset.sum_congr rfl
    intro r hr
    exact if_pos (Finset.mem_range.mp hr)
  have hg := (summable_geometric_of_lt_one hu0 hu1).mul_left c
  have hpoint (r : ℕ) : u ^ r * a r ≤ c * u ^ r + p r := by
    by_cases hr : r < R
    · have hpow : u ^ r ≤ 1 := pow_le_one₀ hu0 hu1.le
      have hm := mul_le_of_le_one_left (ha r) hpow
      have hc' := mul_nonneg hc (pow_nonneg hu0 r)
      simp only [p, if_pos hr]
      linarith
    · have h := mul_le_mul_of_nonneg_left (htail r (le_of_not_gt hr)) (pow_nonneg hu0 r)
      simpa only [p, if_neg hr, add_zero, mul_comm] using h
  have hle := hsum.tsum_le_tsum hpoint (hg.add hpsum)
  rw [Summable.tsum_add hg hpsum, tsum_mul_left, tsum_geometric_of_lt_one hu0 hu1, hptsum] at hle
  have h := mul_le_mul_of_nonneg_left hle (show 0 ≤ 1 - u by linarith)
  have hne : 1 - u ≠ 0 := by linarith
  calc
    _ ≤ (1 - u) * (c * (1 - u)⁻¹ + ∑ r ∈ Finset.range R, a r) := h
    _ = _ := by field_simp

/-- An Abel lower bound strictly above c forces arbitrarily high individual Ω layers
whose weight exceeds c. No claim about a limit of every individual layer is made. -/
lemma exists_large_layer_of_abel_lower (E : Set ℕ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hAbel : HasAbelLowerBound (fun u : ℝ => (1 - u) * setAbelMass E u) d) (R : ℕ) :
    ∃ r : ℕ, R ≤ r ∧ c < layerMass E r := by
  by_contra hnot
  have htail : ∀ r, R ≤ r → layerMass E r ≤ c := by
    intro r hr
    by_contra hgt
    exact hnot ⟨r, hr, lt_of_not_ge hgt⟩
  let K : ℝ := ∑ r ∈ Finset.range R, layerMass E r
  have hupper : ∀ᶠ u : ℝ in 𝓝[<] 1, (1 - u) * setAbelMass E u ≤ c + (1 - u) * K := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
    have hs := layer_abel_hasSum E hu.1.le hu.2
    have h := normalized_power_series_upper_of_tail (layerMass_nonneg E) hc R htail hu.1.le hu.2 hs.summable
    rwa [hs.tsum_eq] at h
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun u : ℝ => c + (1 - u) * K) (𝓝[<] 1) (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const K)
  have hm1 : c < (c + d) / 2 := by linarith
  have hm2 : (c + d) / 2 < d := by linarith
  obtain ⟨u, hu, hl, hh⟩ := (hupper.and ((hAbel ((c + d) / 2) hm2).and
    (hlim.eventually (eventually_lt_nhds hm1)))).exists
  linarith

end Apicella143

end

-- module Apicella143.FiniteExtraction
noncomputable section
open Filter
open scoped Topology BigOperators ArithmeticFunction.Omega

namespace Apicella143

/-- Extract a genuinely finite primitive set from one convergent positive Ω layer. -/
lemma finite_primitive_from_layer (E : Set ℕ) {r N : ℕ} (hr : 0 < r) (hNr : N ≤ r)
    {c : ℝ} (hc : c < layerMass E r) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ n ∈ E) ∧ Primitive (P : Set ℕ) ∧
      c < ∑ n ∈ P, natWeight n := by
  classical
  let f : ℕ → ℝ := fun n => if Ω n = r ∧ n ∈ E then natWeight n else 0
  have hsum : HasSum f (layerMass E r) := by
    rw [layerMass_eq_tsum_conditional]
    exact (layer_weight_summable E r).hasSum
  change Tendsto (fun T : Finset ℕ => ∑ n ∈ T, f n) atTop (𝓝 (layerMass E r)) at hsum
  obtain ⟨T, hT⟩ := (hsum.eventually (eventually_gt_nhds hc)).exists
  let P := T.filter (fun n => Ω n = r ∧ n ∈ E)
  have hP : ∀ n ∈ P, Ω n = r ∧ n ∈ E := fun n hn => (Finset.mem_filter.mp hn).2
  refine ⟨P, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨?_, (hP n hn).2⟩
    calc
      N ≤ r := hNr
      _ = Ω n := (hP n hn).1.symm
      _ ≤ n := omega_le_self n
  · exact primitive_of_constant_omega hr (fun n hn => (hP n hn).1)
  · simpa only [P, Finset.sum_filter, f] using hT

end Apicella143

end

-- module Apicella143.PeriodicSelection
noncomputable section
open scoped BigOperators ENNReal

namespace Apicella143

/-- The sufficient periodic-selection lemma, now proved without an assumed analytic interface.
All quantifiers are in the intended order: the period and residue set are fixed first. -/
lemma periodic_primitive_selection_real (L : ℕ) [NeZero L] (S : Finset (ZMod L))
    (hd : (2 / 3 : ℝ) < (S.card : ℝ) / L) (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ (n : ZMod L) ∈ S) ∧ Primitive (P : Set ℕ) ∧
      (1 / 6 : ℝ) < ∑ n ∈ P, natWeight n := by
  have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hc : (1 / 6 : ℝ) < (S.card : ℝ) / (4 * (L : ℝ)) := by
    have hd' := (lt_div_iff₀ hL).mp hd
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * L)).2
    nlinarith
  obtain ⟨r, hrN, hr⟩ := exists_large_layer_of_abel_lower (periodicResidueSet L S)
    (by norm_num : (0 : ℝ) ≤ 1 / 6) hc (periodic_abel_lower_bound L S) N
  obtain ⟨P, hP, hprim, hweight⟩ := finite_primitive_from_layer (periodicResidueSet L S)
    (by omega : 0 < r) hrN hr
  exact ⟨P, hP, hprim, hweight⟩

lemma periodic_primitive_selection (L : ℕ) [NeZero L] (S : Finset (ZMod L))
    (hd : (2 / 3 : ℝ) < (S.card : ℝ) / L) (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ (n : ZMod L) ∈ S) ∧ Primitive (P : Set ℕ) ∧
      (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n := by
  obtain ⟨P, hP, hprim, hw⟩ := periodic_primitive_selection_real L S hd N hN
  refine ⟨P, hP, hprim, ?_⟩
  have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)).2 hw
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => natWeight_nonneg n)] at h
  simpa only [weight_nat_eq_ofReal, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 6),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h

/-- This closes exactly the finite-period interface stated at the start of the project,
including its original `Fin L` residue encoding and rational density comparison. -/
theorem periodicPrimitiveSelection_proved : PeriodicPrimitiveSelection := by
  intro L hL S hd N hN
  cases L with
  | zero => omega
  | succ L =>
    have hdR : (2 / 3 : ℝ) < (S.card : ℝ) / (L + 1 : ℕ) := by
      have hcast : (((2 / 3 : ℚ) : ℝ)) < (((S.card : ℚ) / (L + 1 : ℕ) : ℚ) : ℝ) :=
        Rat.cast_lt.mpr hd
      push_cast at hcast
      simpa only [Nat.cast_add, Nat.cast_one] using hcast
    obtain ⟨P, hP, hprim, hw⟩ := periodic_primitive_selection (L + 1) S hdR N hN
    refine ⟨P, ?_, hprim, hw⟩
    intro n hn
    refine ⟨(hP n hn).1, ?_⟩
    have heq : (n : ZMod (L + 1)) =
        (⟨n % (L + 1), Nat.mod_lt n hL⟩ : Fin (L + 1)) := by
      apply Fin.ext
      exact ZMod.val_natCast (L + 1) n
    rw [← heq]
    exact (hP n hn).2

end Apicella143

end

-- module Apicella143.ConstraintSelection
noncomputable section
open scoped BigOperators ENNReal
namespace Apicella143

/-- Finitely many residue exclusions with total forbidden density below one third
admit an arbitrarily far-out finite primitive set of logarithmic weight above one sixth.
No independence of the residue conditions is required. -/
lemma finite_constraints_primitive_selection {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (B : (i : ι) → Finset (ZMod (m i)))
    (hbudget : (∑ i, ((B i).card : ℚ) / m i) < 1 / 3)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ ∀ i, (n : ZMod (m i)) ∉ B i) ∧
      Primitive (P : Set ℕ) ∧ (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n := by
  classical
  let L := ∏ i, m i
  have hL : 0 < L := Finset.prod_pos (fun i _ => hm i)
  letI : NeZero L := ⟨ne_of_gt hL⟩
  letI (i : ι) : NeZero (m i) := ⟨ne_of_gt (hm i)⟩
  have hdvd (i : ι) : m i ∣ L := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  let C (i : ι) : Finset (ZMod L) :=
    Finset.univ.filter (fun x => ZMod.castHom (hdvd i) (ZMod (m i)) x ∈ B i)
  let S : Finset (ZMod L) := (Finset.univ.biUnion C)ᶜ
  have hden (i : ι) : ((C i).card : ℚ) / L = ((B i).card : ℚ) / m i :=
    zmod_preimage_density (hdvd i) (B i)
  have hS : (2 / 3 : ℚ) < (S.card : ℚ) / L := by
    have h := complement_union_density (Finset.univ : Finset ι) C
    simp only [ZMod.card, hden] at h
    change 1 - (∑ i, ((B i).card : ℚ) / m i) ≤ (S.card : ℚ) / L at h
    linarith
  have hSR : (2 / 3 : ℝ) < (S.card : ℝ) / L := by
    have hcast := Rat.cast_lt (K := ℝ) |>.mpr hS
    push_cast at hcast
    exact hcast
  obtain ⟨P, hP, hprim, hw⟩ := periodic_primitive_selection L S hSR N hN
  refine ⟨P, ?_, hprim, hw⟩
  intro n hn
  refine ⟨(hP n hn).1, ?_⟩
  intro i hi
  have hout : (n : ZMod L) ∉ Finset.univ.biUnion C := Finset.mem_compl.mp (hP n hn).2
  apply hout
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  change (n : ZMod L) ∈ Finset.univ.filter _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_natCast]
  exact hi

end Apicella143

end

-- module Apicella143.RootResidues
noncomputable section
open scoped BigOperators
namespace Apicella143

/-- A deliberately closed forbidden interval, larger than the candidate's half-open one. -/
def rootBadResidues (p D : ℕ) : Finset (ZMod p) :=
  (Finset.Icc (-((p - 1) / D : ℕ) : ℤ) (((p - 1) / D : ℕ) : ℤ)).image
    (fun z : ℤ => (z : ZMod p))

lemma rootBadResidues_card_le (p D : ℕ) :
    (rootBadResidues p D).card ≤ 2 * ((p - 1) / D) + 1 := by
  unfold rootBadResidues
  calc
    _ ≤ _ := Finset.card_image_le
    _ = _ := by rw [Int.card_Icc]; omega

lemma rootBadResidues_density {p D : ℕ} (hD : 0 < D) (hpD : D ≤ p) :
    ((rootBadResidues p D).card : ℚ) / p ≤ 3 / D := by
  have hp : 0 < p := lt_of_lt_of_le hD hpD
  have hcard : ((rootBadResidues p D).card : ℚ) ≤ 2 * (((p - 1) / D : ℕ) : ℚ) + 1 := by
    exact_mod_cast rootBadResidues_card_le p D
  have hquot : ((((p - 1) / D : ℕ) : ℚ)) * D ≤ (p - 1 : ℕ) := by
    exact_mod_cast Nat.div_mul_le_self (p - 1) D
  have hpD' : (D : ℚ) ≤ p := by exact_mod_cast hpD
  have hsub : ((p - 1 : ℕ) : ℚ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  have hp' : (0 : ℚ) < p := Nat.cast_pos.mpr hp
  rw [div_le_div_iff₀ hp' hD']
  nlinarith

/-- Because `p - 1 ≡ -1 mod p`, every near-collision forces the label itself
into the short interval of forbidden residues. -/
lemma root_collision_mem_bad {p D n : ℕ} (hp : 1 < p) (hD : 0 < D) (k : ℤ)
    (hcoll : |((p : ℚ) / (p - 1 : ℕ)) * D * k - D * n| ≤ 1) :
    (n : ZMod p) ∈ rootBadResidues p D := by
  let q := p - 1
  let d : ℤ := (p : ℤ) * k - (q : ℤ) * n
  have hq : 0 < q := by dsimp [q]; omega
  have hq' : (0 : ℚ) < q := Nat.cast_pos.mpr hq
  have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  have heq : (d : ℚ) * D = (((p : ℚ) / q) * D * k - D * n) * q := by
    dsimp [d]
    push_cast
    field_simp
  have habs : (d.natAbs : ℚ) * D ≤ q := by
    calc
      _ = |(d : ℚ) * D| := by rw [abs_mul, abs_of_pos hD', Nat.cast_natAbs, Int.cast_abs]
      _ = |(((p : ℚ) / q) * D * k - D * n) * q| := congrArg abs heq
      _ = |((p : ℚ) / q) * D * k - D * n| * q := by rw [abs_mul, abs_of_pos hq']
      _ ≤ 1 * q := mul_le_mul_of_nonneg_right hcoll hq'.le
      _ = _ := one_mul _
  have hnabs : d.natAbs ≤ q / D := (Nat.le_div_iff_mul_le hD).mpr (by exact_mod_cast habs)
  have hd : -((q / D : ℕ) : ℤ) ≤ d ∧ d ≤ ((q / D : ℕ) : ℤ) := by
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnabs
  have hres : (d : ZMod p) = (n : ZMod p) := by
    have hqeq : q + 1 = p := by dsimp [q]; omega
    have hqres : (q : ZMod p) = -1 := by
      have : (q : ZMod p) + 1 = 0 := by
        rw [← Nat.cast_add_one, hqeq, ZMod.natCast_self]
      linear_combination this
    dsimp [d]
    push_cast
    rw [ZMod.natCast_self, hqres]
    ring
  exact Finset.mem_image.mpr ⟨d, Finset.mem_Icc.mpr hd, hres⟩

lemma root_not_bad_separated {p D n : ℕ} (hp : 1 < p) (hD : 0 < D)
    (hn : (n : ZMod p) ∉ rootBadResidues p D) (k : ℤ) :
    1 < |((p : ℚ) / (p - 1 : ℕ)) * D * k - D * n| := by
  exact lt_of_not_ge (fun h => hn (root_collision_mem_bad hp hD k h))

end Apicella143

end

-- module Apicella143.RoundLabels
noncomputable section
open scoped BigOperators ENNReal
namespace Apicella143

/-- The exact finite-round union bound, using the private-prime filter and one
short forbidden-residue interval for each already inserted root. -/
lemma round_labels (H R : Finset ℕ) (D N : ℕ)
    (hH : ∀ h ∈ H, 0 < h) (hD : 0 < D) (hR : ∀ p ∈ R, D ≤ p)
    (hbudget : (∑ h ∈ H, (1 : ℚ) / h) < 1 / 100)
    (hcard : R.card ≤ D / 12) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ,
      (∀ n ∈ P, N ≤ n ∧ (∀ h ∈ H, ¬ h ∣ n) ∧
        ∀ p ∈ R, (n : ZMod p) ∉ rootBadResidues p D) ∧
      Primitive (P : Set ℕ) ∧ (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n := by
  classical
  let m : (H ⊕ R) → ℕ := Sum.elim Subtype.val Subtype.val
  let B : (i : H ⊕ R) → Finset (ZMod (m i)) := fun i =>
    match i with
    | Sum.inl _ => {0}
    | Sum.inr p => rootBadResidues p D
  have hm (i : H ⊕ R) : 0 < m i := by
    cases i with
    | inl h => exact hH h h.property
    | inr p => exact lt_of_lt_of_le hD (hR p p.property)
  have hroots : (∑ p ∈ R, ((rootBadResidues p D).card : ℚ) / p) ≤ 1 / 4 := by
    have hsum := Finset.sum_le_sum (s := R) (fun p hp => rootBadResidues_density hD (hR p hp))
    have hc : (R.card : ℚ) * 12 ≤ D := by
      have : R.card * 12 ≤ D := (Nat.mul_le_mul_right 12 hcard).trans (Nat.div_mul_le_self D 12)
      exact_mod_cast this
    have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hmul : (R.card : ℚ) * (3 / D) ≤ 1 / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).mpr
      field_simp
      nlinarith
    exact hsum.trans hmul
  have hb : (∑ i, ((B i).card : ℚ) / m i) < 1 / 3 := by
    have h1 : ∀ a : H, ((B (Sum.inl a)).card : ℚ) / m (Sum.inl a) = 1 / (a : ℕ) := by
      intro a
      show ((({0} : Finset (ZMod (a : ℕ))).card : ℚ)) / (a : ℕ) = 1 / (a : ℕ)
      rw [Finset.card_singleton, Nat.cast_one]
    have h2 : ∀ p : R, ((B (Sum.inr p)).card : ℚ) / m (Sum.inr p) =
        ((rootBadResidues p D).card : ℚ) / (p : ℕ) := fun p => rfl
    rw [Fintype.sum_sum_type]
    simp only [h1, h2]
    rw [Finset.sum_coe_sort H (fun h => (1 : ℚ) / h),
      Finset.sum_coe_sort R (fun p => ((rootBadResidues p D).card : ℚ) / p)]
    linarith
  obtain ⟨P, hP, hprim, hw⟩ := finite_constraints_primitive_selection m hm B hb N hN
  refine ⟨P, ?_, hprim, hw⟩
  intro n hn
  refine ⟨(hP n hn).1, ?_, ?_⟩
  · intro h hh hdvd
    have hnot := (hP n hn).2 (Sum.inl ⟨h, hh⟩)
    apply hnot
    change (n : ZMod h) ∈ ({0} : Finset (ZMod h))
    simp only [Finset.mem_singleton]
    exact (ZMod.natCast_eq_zero_iff n h).mpr hdvd
  · intro p hp
    exact (hP n hn).2 (Sum.inr ⟨p, hp⟩)

end Apicella143

end

-- module Apicella143.ConstructionState
noncomputable section
open scoped BigOperators ENNReal
namespace Apicella143

/-- Stored arithmetic data: the private prime, the nonprivate numerator part,
and the positive denominator. -/
structure StoredPoint where
  H : ℕ
  N : ℕ
  q : ℕ
  deriving DecidableEq

def StoredPoint.value (a : StoredPoint) : ℚ := a.H * a.N / a.q

structure ConstructionState where
  atoms : Finset StoredPoint
  primes : Finset ℕ
  deriving DecidableEq

def ConstructionState.points (F : ConstructionState) : Finset ℚ := F.atoms.image StoredPoint.value

def ConstructionState.mass (F : ConstructionState) : ℝ≥0∞ := ∑ a ∈ F.points, weight a

/-- Every field is a proved invariant of the finite construction, not an assumption
exported by the final theorem. -/
structure ValidState (F : ConstructionState) : Prop where
  prime : ∀ h ∈ F.primes, h.Prime ∧ 2 < h
  budget : (∑ h ∈ F.primes, (1 : ℚ) / h) < 1 / 100
  data : ∀ a ∈ F.atoms, a.H ∈ F.primes ∧ 0 < a.N ∧ 0 < a.q ∧
    ¬ a.H ∣ a.q ∧ 4 < a.value / a.H
  avoid : ∀ h ∈ F.primes, ∀ a ∈ F.atoms, ¬ h ∣ a.N
  lower : ∀ a ∈ F.points, (2 : ℚ) ≤ a
  original : Original (F.points : Set ℚ)
  tiny : ∀ a ∈ F.points, TinyPositiveDisplacement a

def emptyState : ConstructionState := ⟨∅, ∅⟩

lemma emptyState_valid : ValidState emptyState := by
  constructor
  · simp [emptyState]
  · norm_num [emptyState]
  · simp [emptyState]
  · simp [emptyState]
  · simp [emptyState, ConstructionState.points]
  · simpa [emptyState, ConstructionState.points] using original_empty
  · simp [emptyState, ConstructionState.points]

lemma state_grid_exists (F : ConstructionState) (hF : ValidState F) :
    ∃ D : ℕ, 48 ≤ D ∧ (∀ a ∈ F.atoms, a.N ∣ D) ∧
      ∀ h ∈ F.primes, ¬ h ∣ D := by
  obtain ⟨D, _, hD, hdiv, hav⟩ := exists_private_compatible_grid
    (F.atoms.image StoredPoint.N) F.primes
    (by intro n hn; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn; exact (hF.data a ha).2.1)
    hF.prime
    (by intro h hh n hn; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn; exact hF.avoid h hh a ha) 0
  exact ⟨D, hD, fun a ha => hdiv a.N (Finset.mem_image.mpr ⟨a, ha, rfl⟩), hav⟩

/-- A reset grid excludes all earlier-round collisions whenever the label avoids
the stored private prime. -/
lemma stored_point_grid_separated (a : StoredPoint) (hH : a.H.Prime)
    (hq : 0 < a.q) (hHq : ¬ a.H ∣ a.q)
    (hsize : 4 < a.value / a.H) {D n : ℕ} (hdiv : a.N ∣ D)
    (hHD : ¬ a.H ∣ D) (hHn : ¬ a.H ∣ n) (k : ℤ) :
    4 < |k * a.value - D * n| := by
  let t := D / a.N
  have hDt : a.N * t = D := Nat.mul_div_cancel' hdiv
  have hHt : ¬ a.H ∣ t := by
    intro ht
    apply hHD
    rw [← hDt]
    exact dvd_mul_of_dvd_right ht _
  apply private_grid_separated hH hHt hHq hHn hsize
  unfold StoredPoint.value
  have hq' : (a.q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  have hDt' : (a.N : ℚ) * t = D := by exact_mod_cast hDt
  field_simp
  nlinarith [hDt']

lemma state_grid_free (F : ConstructionState) (hF : ValidState F)
    {D n : ℕ} (hdiv : ∀ a ∈ F.atoms, a.N ∣ D)
    (hHD : ∀ h ∈ F.primes, ¬ h ∣ D)
    (hn : ∀ h ∈ F.primes, ¬ h ∣ n) : RightFree (F.points : Set ℚ) D n := by
  intro x hx k hcoll
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨haH, _, haq, haHq, hasize⟩ := hF.data a ha
  have h := stored_point_grid_separated a (hF.prime a.H haH).1 haq haHq hasize
    (hdiv a ha) (hHD a.H haH) (hn a.H haH) k
  have hle : |(k : ℚ) * a.value - D * n| ≤ 1 := abs_le.mpr ⟨hcoll.1.le, hcoll.2⟩
  linarith

/-- A fresh private prime can satisfy any finite size requirements while preserving
the strict reciprocal budget. -/
lemma fresh_private_prime (F : ConstructionState) (hF : ValidState F) (M : ℕ) :
    ∃ H : ℕ, H.Prime ∧ M < H ∧ 2 < H ∧ H ∉ F.primes ∧
      (∀ a ∈ F.atoms, a.N < H) ∧
      (∑ h ∈ insert H F.primes, (1 : ℚ) / h) < 1 / 100 := by
  let eps : ℚ := 1 / 100 - ∑ h ∈ F.primes, (1 : ℚ) / h
  have heps : 0 < eps := sub_pos.mpr hF.budget
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / eps)
  obtain ⟨H, hprime, hlarge⟩ := exists_prime_above_finset
    (insert K (insert M (insert 2 (F.primes ∪ F.atoms.image StoredPoint.N))))
  have hHM : M < H := hlarge M (by simp)
  have hH2 : 2 < H := hlarge 2 (by simp)
  have hnot : H ∉ F.primes := by
    intro hh
    exact (lt_irrefl H) (hlarge H (by simp [hh]))
  refine ⟨H, hprime, hHM, hH2, hnot, ?_, ?_⟩
  · intro a ha
    exact hlarge a.N (by simp [Finset.mem_image_of_mem StoredPoint.N ha])
  · rw [Finset.sum_insert hnot]
    have hHK : (K : ℚ) < H := by exact_mod_cast hlarge K (by simp)
    have hHpos : (0 : ℚ) < H := Nat.cast_pos.mpr hprime.pos
    have hi : (1 : ℚ) / H < eps := (div_lt_iff₀ hHpos).mpr (by
      have := (div_lt_iff₀ heps).mp (hK.trans hHK)
      nlinarith)
    dsimp [eps] at hi
    linarith

end Apicella143

end

-- module Apicella143.BlockParameters
noncomputable section
namespace Apicella143

def blockAtom (H G D n : ℕ) : StoredPoint := ⟨H, G * D * n, H * G - 1⟩
def blockScale (H G : ℕ) : ℚ := (H * G : ℕ) / (H * G - 1 : ℕ)

lemma blockAtom_value (H G D n : ℕ) :
    (blockAtom H G D n).value = blockScale H G * D * n := by
  simp only [blockAtom, StoredPoint.value, blockScale, Nat.cast_mul]
  ring

lemma blockScale_eq {H G : ℕ} (hp : 1 < H * G) :
    blockScale H G = 1 + 1 / (H * G - 1 : ℕ) := by
  have hq : (H * G - 1 : ℕ) ≠ 0 := by omega
  have heq : H * G = (H * G - 1) + 1 := by omega
  unfold blockScale
  conv_lhs => rw [heq]
  push_cast
  field_simp

lemma blockScale_bounds {H G : ℕ} (hp : 2 < H * G) :
    1 < blockScale H G ∧ blockScale H G < 2 := by
  rw [blockScale_eq (by omega)]
  have hq : (1 : ℚ) < (H * G - 1 : ℕ) := by exact_mod_cast (by omega : 1 < H * G - 1)
  constructor
  · have : (0 : ℚ) < 1 / (H * G - 1 : ℕ) := by positivity
    linarith
  · have : (1 : ℚ) / (H * G - 1 : ℕ) < 1 := (div_lt_one (by linarith)).mpr hq
    linarith

lemma block_shift_eq {H G D n : ℕ} (hp : 1 < H * G) :
    (blockScale H G - 1) * D * n = (D * n : ℕ) / (H * G - 1 : ℕ) := by
  rw [blockScale_eq hp]
  push_cast
  ring

lemma block_value_eq_perturbed {H G D n : ℕ} (hp : 1 < H * G) :
    (blockAtom H G D n).value = (D * n : ℕ) + (D * n : ℕ) / (H * G - 1 : ℕ) := by
  rw [blockAtom_value, blockScale_eq hp]
  push_cast
  ring

/-- The auxiliary prime is selected only after the finite label set, so its
size can dominate every perturbation and old-denominator requirement. -/
lemma auxiliary_prime_exists (H Q : ℕ) (hs : 1 < H) (S : Finset ℕ) :
    ∃ G : ℕ, G.Prime ∧ (∀ h ∈ S, h < G) ∧ Q < H * G - 1 := by
  obtain ⟨G, hG, hlarge⟩ := exists_prime_above_finset (insert (Q + 2) S)
  refine ⟨G, hG, fun h hh => hlarge h (by simp [hh]), ?_⟩
  have hq := hlarge (Q + 2) (by simp)
  have : G ≤ H * G := by nlinarith [hG.pos]
  omega

lemma block_private_denominator {H G : ℕ} (hH : H.Prime) (hG : 0 < G) :
    ¬ H ∣ H * G - 1 := by
  have hp : 0 < H * G := Nat.mul_pos hH.pos hG
  intro hd
  have hone : H ∣ 1 := by
    have hs : H * G - 1 + 1 = H * G := by omega
    have hm : H ∣ H * G - 1 + 1 := by rw [hs]; exact dvd_mul_right H G
    exact (Nat.dvd_add_right hd).mp hm
  exact hH.not_dvd_one hone

lemma block_private_spacing {H G D n : ℕ} (hp : 1 < H * G) (hH : 0 < H)
    (hn : 4 * H < D * n) : 4 < (blockAtom H G D n).value / H := by
  have hH' : (0 : ℚ) < H := Nat.cast_pos.mpr hH
  have hn' : (4 : ℚ) * H < (D * n : ℕ) := by exact_mod_cast hn
  have hq : (0 : ℚ) < (H * G - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  rw [block_value_eq_perturbed hp]
  apply (lt_div_iff₀ hH').mpr
  have hpos : (0 : ℚ) < (D * n : ℕ) / (H * G - 1 : ℕ) := div_pos (by linarith) hq
  linarith

end Apicella143

end

-- module Apicella143.Insertion
noncomputable section
namespace Apicella143

/-- All separation obligations for inserting one finite or infinite primitive block.
This lemma proves the geometric implication only; it does not assume or assert the
existence of parameters satisfying the hypotheses. -/
lemma insert_primitive_block_original {F : Set ℚ} {P : Set ℕ} {D : ℕ} {c : ℚ}
    (hF : Original F) (hP : Primitive P) (hD : 1 ≤ D) (hc : 1 < c)
    (hfree : ∀ n ∈ P, RightFree F D n)
    (hshift : ∀ n ∈ P, 0 < (c - 1) * D * n)
    (hsmall : ∀ a ∈ F, ∀ n ∈ P, (c - 1) * D * n < 1 / (a.den : ℚ))
    (habove : ∀ a ∈ F, ∀ n ∈ P, a + 1 < c * D * n)
    (hnonneg : ∀ n ∈ P, 0 ≤ c * D * n) :
    Original (F ∪ ((fun n : ℕ => c * D * n) '' P)) := by
  have hDq : (1 : ℚ) ≤ D := by exact_mod_cast hD
  have hcD : 1 ≤ c * D := by nlinarith
  apply original_union hF (scaled_primitive_original hP hcD)
  · intro a ha b hb k hk
    obtain ⟨n, hn, rfl⟩ := hb
    have hf := hfree n hn a ha
    have hpert := old_source_perturbation_safe (A := a.num) (B := a.den)
      (m := (D : ℤ) * n) (η := (c - 1) * D * n) a.den_pos
    have hf' : ∀ j : ℤ, ¬ ((-1 : ℚ) < j * ((a.num : ℚ) / a.den) -
        ((D : ℤ) * n : ℤ) ∧ j * ((a.num : ℚ) / a.den) - ((D : ℤ) * n : ℤ) ≤ 1) := by
      simpa only [Rat.num_div_den, Int.cast_mul, Int.cast_natCast] using hf
    have h := hpert hf' (hshift n hn) (hsmall a ha n hn) (k : ℤ)
    simp only [Rat.num_div_den, Int.cast_natCast, Int.cast_mul] at h
    convert h.le using 3 <;> first | rfl | ring | (push_cast; ring)
  · intro b hb a ha k hk
    obtain ⟨n, hn, rfl⟩ := hb
    exact (new_source_separated (hnonneg n hn) (habove a ha n hn) hk).le

end Apicella143

end

-- module Apicella143.BlockExtension
noncomputable section
open scoped BigOperators ENNReal
namespace Apicella143

def extendState (F : ConstructionState) (H G D : ℕ) (P : Finset ℕ) : ConstructionState :=
  ⟨F.atoms ∪ P.image (blockAtom H G D), insert H F.primes⟩

lemma extendState_points (F : ConstructionState) (H G D : ℕ) (P : Finset ℕ) :
    (extendState F H G D P).points = F.points ∪ P.image (fun n : ℕ => blockScale H G * D * n) := by
  simp only [extendState, ConstructionState.points, Finset.image_union,
    Finset.image_image, Function.comp_def, blockAtom_value]

lemma block_extension_valid (F : ConstructionState) (hF : ValidState F)
    (H G D U : ℕ) (P : Finset ℕ)
    (hH : H.Prime) (hH2 : 2 < H) (hG : G.Prime) (hD : 1 ≤ D)
    (hGlarge : ∀ h ∈ insert H F.primes, h < G)
    (hnew : ∀ a ∈ F.atoms, a.N < H)
    (hbudget : (∑ h ∈ insert H F.primes, (1 : ℚ) / h) < 1 / 100)
    (havoidD : ∀ h ∈ insert H F.primes, ¬ h ∣ D)
    (hP : Primitive (P : Set ℕ))
    (hn : ∀ n ∈ P, 2 * D ≤ n ∧ 4 * H < D * n ∧ D * n ≤ U ∧
      ∀ h ∈ insert H F.primes, ¬ h ∣ n)
    (hfree : ∀ n ∈ P, RightFree (F.points : Set ℚ) D n)
    (habove : ∀ a ∈ F.points, ∀ n ∈ P, a + 1 < (D * n : ℕ))
    (hq : 2 * U ^ 13 ≤ H * G - 1)
    (hsmall : ∀ a ∈ F.points, ∀ n ∈ P, (D * n : ℚ) / (H * G - 1 : ℕ) < 1 / a.den) :
    ValidState (extendState F H G D P) := by
  have hp : 2 < H * G := by nlinarith [hG.two_le]
  obtain ⟨hc, hc2⟩ := blockScale_bounds hp
  have hqpos : (0 : ℚ) < (H * G - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hn2 (n : ℕ) (hnP : n ∈ P) : 2 ≤ D * n := by
    have := (hn n hnP).1
    nlinarith
  have hshift (n : ℕ) (hnP : n ∈ P) :
      0 < (blockScale H G - 1) * D * n := by
    rw [block_shift_eq (by omega)]
    exact div_pos (Nat.cast_pos.mpr (by have := hn2 n hnP; omega)) hqpos
  have hvalabove (n : ℕ) (hnP : n ∈ P) : (D * n : ℕ) < blockScale H G * D * n := by
    have := hshift n hnP
    push_cast
    nlinarith
  have hprime (h : ℕ) (hh : h ∈ insert H F.primes) : h.Prime ∧ 2 < h := by
    rcases Finset.mem_insert.mp hh with rfl | hh
    · exact ⟨hH, hH2⟩
    · exact hF.prime h hh
  constructor
  · exact hprime
  · exact hbudget
  · intro a ha
    change a ∈ F.atoms ∪ P.image (blockAtom H G D) at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨haH, hN, haq, hav, hsize⟩ := hF.data a ha
      exact ⟨Finset.mem_insert_of_mem haH, hN, haq, hav, hsize⟩
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      refine ⟨by simp [blockAtom, extendState], ?_, ?_, ?_, ?_⟩
      · change 0 < G * D * n
        have : 0 < n := by have := (hn n hnP).1; omega
        exact Nat.mul_pos (Nat.mul_pos hG.pos (by omega)) this
      · change 0 < H * G - 1
        omega
      · exact block_private_denominator hH hG.pos
      · exact block_private_spacing (by omega) hH.pos (hn n hnP).2.1
  · intro h hh a ha
    change h ∈ insert H F.primes at hh
    change a ∈ F.atoms ∪ P.image (blockAtom H G D) at ha
    rcases Finset.mem_union.mp ha with haold | hanew
    · rcases Finset.mem_insert.mp hh with heq | hhold
      · subst h
        exact fresh_prime_avoids_old_part (hF.data a haold).2.1 (hnew a haold)
      · exact hF.avoid h hhold a haold
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp hanew
      apply private_prime_preserved (hprime h hh).1 ?_ (havoidD h hh) ((hn n hnP).2.2.2 h hh)
      intro hd
      have heq : h = G := (Nat.dvd_prime hG).mp hd |>.resolve_left (by have := (hprime h hh).2; omega)
      exact (ne_of_lt (hGlarge h hh)) heq
  · intro a ha
    rw [extendState_points] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hF.lower a ha
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      have h2 : (2 : ℚ) ≤ (D * n : ℕ) := by exact_mod_cast hn2 n hnP
      exact h2.trans (hvalabove n hnP).le
  · rw [extendState_points, Finset.coe_union, Finset.coe_image]
    apply insert_primitive_block_original hF.original hP hD hc hfree hshift
    · intro a ha n hnP
      rw [block_shift_eq (by omega)]
      simpa only [Nat.cast_mul] using hsmall a ha n hnP
    · intro a ha n hnP
      exact (habove a ha n hnP).trans (hvalabove n hnP)
    · intro n hnP
      exact (Nat.cast_nonneg (D * n)).trans (hvalabove n hnP).le
  · intro a ha
    rw [extendState_points] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hF.tiny a ha
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      rw [← blockAtom_value, block_value_eq_perturbed (by omega)]
      exact perturbed_point_tiny (hn2 n hnP) (hn n hnP).2.2.1 hq

lemma state_mass_ne_top (F : ConstructionState) : F.mass ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro a ha
  exact ENNReal.ofReal_ne_top

lemma extendState_mass_gain (F : ConstructionState) (H G D : ℕ) (P : Finset ℕ)
    (hp : 2 < H * G) (hD : 1 ≤ D) (hn : ∀ n ∈ P, 2 * D ≤ n)
    (habove : ∀ a ∈ F.points, ∀ n ∈ P, a + 1 < (D * n : ℕ))
    (hw : (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n) :
    F.mass + (1 : ℝ≥0∞) / (24 * D) < (extendState F H G D P).mass := by
  obtain ⟨hc, hc2⟩ := blockScale_bounds hp
  have hdisj : Disjoint F.points (P.image (fun n : ℕ => blockScale H G * D * n)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hnew
    obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp hnew
    have hab := habove _ ha n hnP
    have hDq : (0 : ℚ) ≤ D := Nat.cast_nonneg D
    have hnq : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    push_cast at hab
    nlinarith [mul_nonneg hDq hnq]
  unfold ConstructionState.mass
  rw [extendState_points, Finset.sum_union hdisj]
  apply ENNReal.add_lt_add_left (state_mass_ne_top F)
  simpa only [totalWeight_finset] using block_weight_lower_bound P hc hc2 hD hn hw

end Apicella143

end

-- module Apicella143.InsertionExistence
noncomputable section
open scoped BigOperators ENNReal
namespace Apicella143

lemma labels_threshold (F : Finset ℚ) (H D : ℕ) (hD : 1 ≤ D) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      2 * D ≤ n ∧ 4 * H < D * n ∧ ∀ a ∈ F, a + 1 < (D * n : ℕ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((∑ a ∈ F, |a|) + 2 * D + 4 * H + 3 : ℚ)
  have hsum : (0 : ℚ) ≤ ∑ a ∈ F, |a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hN2 : 2 ≤ N := by
    have : (2 : ℚ) < N := by linarith [(show (0 : ℚ) ≤ D from Nat.cast_nonneg D), (show (0 : ℚ) ≤ H from Nat.cast_nonneg H)]
    exact_mod_cast this.le
  refine ⟨N, hN2, ?_⟩
  intro n hn
  have hn' : (N : ℚ) ≤ n := by exact_mod_cast hn
  have hmul : n ≤ D * n := by nlinarith
  have hmul' : (n : ℚ) ≤ (D * n : ℕ) := by exact_mod_cast hmul
  refine ⟨?_, ?_, ?_⟩
  · have : (2 : ℚ) * D ≤ n := by linarith
    exact_mod_cast this
  · have : (4 : ℚ) * H < (D * n : ℕ) := by linarith
    exact_mod_cast this
  · intro a ha
    have hs : |a| ≤ ∑ b ∈ F, |b| := Finset.single_le_sum (fun b _ => abs_nonneg b) ha
    linarith [le_abs_self a]

/-- One complete block insertion. Old-round points use the reset grid; current-round
points use their virtual roots. Every required parameter is constructed here. -/
lemma insert_block_exists (base F : ConstructionState) (hb : ValidState base) (hF : ValidState F)
    (D : ℕ) (hD : 48 ≤ D) (R : Finset ℕ)
    (hdiv : ∀ a ∈ base.atoms, a.N ∣ D)
    (hbaseprimes : base.primes ⊆ F.primes)
    (havoidD : ∀ h ∈ F.primes, ¬ h ∣ D)
    (hroots : ∀ p ∈ R, 2 * D ≤ p)
    (hcard : R.card ≤ D / 12)
    (hcover : ∀ a ∈ F.points, a ∈ base.points ∨
      ∃ p ∈ R, ∃ m : ℕ, a = ((p : ℚ) / (p - 1 : ℕ)) * D * m) :
    ∃ (F' : ConstructionState) (p : ℕ), ValidState F' ∧
      F.atoms ⊆ F'.atoms ∧ F.primes ⊆ F'.primes ∧
      (∀ h ∈ F'.primes, ¬ h ∣ D) ∧ 2 * D ≤ p ∧
      (∀ a ∈ F'.points, a ∈ base.points ∨
        ∃ r ∈ insert p R, ∃ m : ℕ, a = ((r : ℚ) / (r - 1 : ℕ)) * D * m) ∧
      F.mass + (1 : ℝ≥0∞) / (24 * D) < F'.mass := by
  classical
  obtain ⟨H, hH, hHD, hH2, _, hnew, hbudget⟩ := fresh_private_prime F hF D
  have hD1 : 1 ≤ D := by omega
  have hD0 : 0 < D := by omega
  have havD (h : ℕ) (hh : h ∈ insert H F.primes) : ¬ h ∣ D := by
    rcases Finset.mem_insert.mp hh with rfl | hh
    · exact Nat.not_dvd_of_pos_of_lt hD0 hHD
    · exact havoidD h hh
  obtain ⟨N, hN, hthreshold⟩ := labels_threshold F.points H D hD1
  obtain ⟨P, hP, hprim, hw⟩ := round_labels (insert H F.primes) R D N
    (by
      intro h hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact hH.pos
      · exact (hF.prime h hh).1.pos)
    hD0 (by intro p hp; have := hroots p hp; omega) hbudget hcard hN
  let U := D * P.sup id
  let B := F.points.sup Rat.den
  let Q := 2 * U ^ 13 + U * B + 2 * D + 2
  obtain ⟨G, hG, hGlarge, hQ⟩ := auxiliary_prime_exists H Q (by omega) (insert H F.primes)
  have hp : 2 < H * G := by nlinarith [hG.two_le]
  have hq : 2 * U ^ 13 ≤ H * G - 1 := by dsimp [Q] at hQ; omega
  have hpD : 2 * D ≤ H * G := by dsimp [Q] at hQ; omega
  have hn (n : ℕ) (hnP : n ∈ P) :
      2 * D ≤ n ∧ 4 * H < D * n ∧ D * n ≤ U ∧
        ∀ h ∈ insert H F.primes, ¬ h ∣ n := by
    obtain ⟨hn2, hn4, _⟩ := hthreshold n (hP n hnP).1
    exact ⟨hn2, hn4, Nat.mul_le_mul_left D (Finset.le_sup (f := id) hnP), (hP n hnP).2.1⟩
  have habove (a : ℚ) (ha : a ∈ F.points) (n : ℕ) (hnP : n ∈ P) : a + 1 < (D * n : ℕ) :=
    (hthreshold n (hP n hnP).1).2.2 a ha
  have hfree (n : ℕ) (hnP : n ∈ P) : RightFree (F.points : Set ℚ) D n := by
    intro a ha k hcoll
    rcases hcover a ha with haold | ⟨p, hpR, m, rfl⟩
    · exact state_grid_free base hb hdiv
        (fun h hh => havoidD h (hbaseprimes hh))
        (fun h hh => (hP n hnP).2.1 h (Finset.mem_insert_of_mem (hbaseprimes hh))) a haold k hcoll
    · have hp2 : 1 < p := by have := hroots p hpR; omega
      have hsep := root_not_bad_separated hp2 hD0 ((hP n hnP).2.2 p hpR) (k * m)
      have heq : (k : ℚ) * ((p : ℚ) / (p - 1 : ℕ) * D * m) - D * n =
          (p : ℚ) / (p - 1 : ℕ) * D * (k * m : ℤ) - D * n := by push_cast; ring
      rw [← heq] at hsep
      have hle := abs_le.mpr ⟨hcoll.1.le, hcoll.2⟩
      linarith
  have hsmall (a : ℚ) (ha : a ∈ F.points) (n : ℕ) (hnP : n ∈ P) :
      (D * n : ℚ) / (H * G - 1 : ℕ) < 1 / a.den := by
    have hden : a.den ≤ B := Finset.le_sup (f := Rat.den) ha
    have hmn := (hn n hnP).2.2.1
    have hprod : D * n * a.den < H * G - 1 := by
      have : D * n * a.den ≤ U * B := Nat.mul_le_mul hmn hden
      dsimp [Q] at hQ
      omega
    have hqpos : (0 : ℚ) < (H * G - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
    have hdenpos : (0 : ℚ) < a.den := Nat.cast_pos.mpr a.den_pos
    apply (div_lt_div_iff₀ hqpos hdenpos).mpr
    simpa only [one_mul, Nat.cast_mul] using (Nat.cast_lt (α := ℚ)).mpr hprod
  let F' := extendState F H G D P
  refine ⟨F', H * G, block_extension_valid F hF H G D U P hH hH2 hG hD1 hGlarge
    hnew hbudget havD hprim hn hfree habove hq hsmall, ?_, ?_, ?_, hpD, ?_, ?_⟩
  · exact Finset.subset_union_left
  · exact Finset.subset_insert _ _
  · exact havD
  · intro a ha
    rw [extendState_points] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases hcover a ha with h | ⟨r, hr, m, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, m, hm⟩
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      exact Or.inr ⟨H * G, Finset.mem_insert_self _ _, n, rfl⟩
  · exact extendState_mass_gain F H G D P hp hD1 (fun n hnP => (hn n hnP).1) habove hw

end Apicella143

end

-- module Apicella143.RoundExtension
noncomputable section
open scoped BigOperators ENNReal
namespace Apicella143

lemma round_gain_bound {D : ℕ} (hD : 48 ≤ D) :
    (1 : ℝ≥0∞) / 576 ≤ ((D / 12 : ℕ) : ℝ≥0∞) * (1 / (24 * D)) := by
  have hD0 : D ≠ 0 := by omega
  apply (ENNReal.toReal_le_toReal (by norm_num)
    (ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (by norm_num) (by simp [hD0])))).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hJ : (D : ℝ) / 24 ≤ ((D / 12 : ℕ) : ℝ) := by
    have hcast := Rat.cast_le (K := ℝ) |>.mpr (round_blocks_lower_bound hD)
    push_cast at hcast
    exact hcast
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  rw [mul_one_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 24 * D)).mpr
  nlinarith

/-- Finite induction inside one round, retaining every invariant and adding one
proved block gain at each step. -/
lemma round_prefix_exists (base : ConstructionState) (hb : ValidState base)
    (D : ℕ) (hD : 48 ≤ D) (hdiv : ∀ a ∈ base.atoms, a.N ∣ D)
    (havoidD : ∀ h ∈ base.primes, ¬ h ∣ D) (s : ℕ) (hs : s ≤ D / 12) :
    ∃ (F : ConstructionState) (R : Finset ℕ), ValidState F ∧
      base.atoms ⊆ F.atoms ∧ base.primes ⊆ F.primes ∧
      (∀ h ∈ F.primes, ¬ h ∣ D) ∧ (∀ p ∈ R, 2 * D ≤ p) ∧ R.card ≤ s ∧
      (∀ a ∈ F.points, a ∈ base.points ∨
        ∃ p ∈ R, ∃ m : ℕ, a = ((p : ℚ) / (p - 1 : ℕ)) * D * m) ∧
      base.mass + (s : ℝ≥0∞) * (1 / (24 * D)) ≤ F.mass := by
  induction s with
  | zero =>
    refine ⟨base, ∅, hb, Finset.Subset.refl _, Finset.Subset.refl _, havoidD,
      by simp, by simp, ?_, ?_⟩
    · intro a ha
      exact Or.inl ha
    · simp
  | succ s ih =>
    obtain ⟨F, R, hF, hba, hbp, hav, hr, hcard, hcover, hmass⟩ := ih (by omega)
    obtain ⟨F', p, hF', hfa, hfp, hav', hpD, hcover', hgain⟩ :=
      insert_block_exists base F hb hF D hD R hdiv hbp hav hr (by omega) hcover
    refine ⟨F', insert p R, hF', hba.trans hfa, hbp.trans hfp, hav', ?_, ?_, hcover', ?_⟩
    · intro r hrR
      rcases Finset.mem_insert.mp hrR with rfl | hrR
      · exact hpD
      · exact hr r hrR
    · exact (Finset.card_insert_le p R).trans (by omega)
    · calc
        base.mass + (s.succ : ℝ≥0∞) * (1 / (24 * D)) =
            (base.mass + (s : ℝ≥0∞) * (1 / (24 * D))) + (1 / (24 * D)) := by
          rw [Nat.cast_succ]
          ring
        _ ≤ F.mass + (1 / (24 * D)) := add_le_add_left hmass _
        _ ≤ F'.mass := hgain.le

/-- An entire round always exists, with a gain bounded uniformly away from zero. -/
lemma round_extension_exists (F : ConstructionState) (hF : ValidState F) :
    ∃ F' : ConstructionState, ValidState F' ∧ F.atoms ⊆ F'.atoms ∧
      F.primes ⊆ F'.primes ∧ F.mass + (1 : ℝ≥0∞) / 576 ≤ F'.mass := by
  obtain ⟨D, hD, hdiv, hav⟩ := state_grid_exists F hF
  obtain ⟨F', _, hF', hfa, hfp, _, _, _, _, hmass⟩ :=
    round_prefix_exists F hF D hD hdiv hav (D / 12) le_rfl
  exact ⟨F', hF', hfa, hfp, (add_le_add_right (round_gain_bound hD) F.mass).trans hmass⟩

end Apicella143

end

-- module Apicella143.LocalFiniteness
noncomputable section
namespace Apicella143

/-- The unit-distance condition at k = 1 already makes integer parts injective. -/
lemma original_floor_injOn {A : Set ℚ} (hA : Original A) : Set.InjOn Int.floor A := by
  intro a ha b hb hab
  by_contra hne
  have hdist := hA a ha b hb hne 1 (by omega)
  norm_num at hdist
  have hla := Int.floor_le a
  have hlb := Int.floor_le b
  have hua := Int.lt_floor_add_one a
  have hub := Int.lt_floor_add_one b
  rw [hab] at hla hua
  have hsmall : |a - b| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  linarith

/-- In the lower-bounded setting no separate growth assumption is needed for local finiteness. -/
lemma original_locallyFiniteAbove {A : Set ℚ} (hA : Original A)
    (hlower : ∀ a ∈ A, (2 : ℚ) ≤ a) : LocallyFiniteAbove A := by
  intro x
  have hmap : Set.MapsTo Int.floor (A ∩ Set.Iic x) (Set.Icc (2 : ℤ) ⌊x⌋) := by
    intro a ha
    constructor
    · simpa using Int.floor_mono (hlower a ha.1)
    · exact Int.floor_mono ha.2
  exact (Set.finite_Icc (2 : ℤ) ⌊x⌋).of_injOn hmap
    ((original_floor_injOn hA).mono Set.inter_subset_left)

end Apicella143

end

-- module Apicella143.Main
noncomputable section
open scoped BigOperators ENNReal
namespace Apicella143

/-- Classical choice is used only to select witnesses of the proved round-extension theorem. -/
def nextState (F : {F : ConstructionState // ValidState F}) :
    {F : ConstructionState // ValidState F} :=
  ⟨(round_extension_exists F.val F.property).choose,
    (round_extension_exists F.val F.property).choose_spec.1⟩

lemma nextState_properties (F : {F : ConstructionState // ValidState F}) :
    F.val.atoms ⊆ (nextState F).val.atoms ∧
      F.val.mass + (1 : ℝ≥0∞) / 576 ≤ (nextState F).val.mass := by
  exact ⟨(round_extension_exists F.val F.property).choose_spec.2.1,
    (round_extension_exists F.val F.property).choose_spec.2.2.2⟩

def stateSequence : ℕ → {F : ConstructionState // ValidState F}
  | 0 => ⟨emptyState, emptyState_valid⟩
  | n + 1 => nextState (stateSequence n)

def pointSequence (n : ℕ) : Set ℚ := ((stateSequence n).val.points : Set ℚ)

def constructedSet : Set ℚ := ⋃ n, pointSequence n

lemma pointSequence_monotone : Monotone pointSequence := by
  apply monotone_nat_of_le_succ
  intro n a ha
  change a ∈ (stateSequence (n + 1)).val.points
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_image.mpr
  exact ⟨b, (nextState_properties (stateSequence n)).1 hb, rfl⟩

lemma stateSequence_mass_lower (n : ℕ) :
    (n : ℝ≥0∞) / 576 ≤ (stateSequence n).val.mass := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (n.succ : ℝ≥0∞) / 576 = (n : ℝ≥0∞) / 576 + 1 / 576 := by
        rw [Nat.cast_succ]
        simp only [div_eq_mul_inv, add_mul, one_mul]
      _ ≤ (stateSequence n).val.mass + 1 / 576 := add_le_add_left ih _
      _ ≤ (stateSequence n.succ).val.mass := (nextState_properties (stateSequence n)).2

lemma constructedSet_original : Original constructedSet :=
  original_iUnion_of_monotone pointSequence_monotone (fun n => (stateSequence n).property.original)

lemma constructedSet_lower : ∀ a ∈ constructedSet, (2 : ℚ) ≤ a :=
  lower_bound_iUnion (fun n => (stateSequence n).property.lower)

lemma constructedSet_tiny : ∀ a ∈ constructedSet, TinyPositiveDisplacement a := by
  intro a ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  exact (stateSequence n).property.tiny a hn

lemma constructedSet_weight_diverges : totalWeight constructedSet = ⊤ := by
  apply totalWeight_iUnion_eq_top_of_unbounded
  intro n
  refine ⟨(n + 1) * 576, ?_⟩
  have hmass := stateSequence_mass_lower ((n + 1) * 576)
  have heq : (((n + 1) * 576 : ℕ) : ℝ≥0∞) / 576 = (n : ℝ≥0∞) + 1 := by
    push_cast
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  rw [heq] at hmass
  have hlt : (n : ℝ≥0∞) < (n : ℝ≥0∞) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (show (n : ℝ≥0∞) < ((n + 1 : ℕ) : ℝ≥0∞) by exact_mod_cast Nat.lt_succ_self n)
  change (n : ℝ≥0∞) < totalWeight ((stateSequence ((n + 1) * 576)).val.points : Set ℚ)
  rw [totalWeight_finset]
  exact hlt.trans_le hmass

/-- The exact requested existence theorem, with no unproved analytic or construction interface. -/
theorem mainConclusion_proved : MainConclusion := by
  exact ⟨constructedSet, rational_set_countable _, constructedSet_lower,
    constructedSet_original, constructedSet_weight_diverges⟩

/-- The stronger manuscript conclusion also includes local finiteness and the
specified twelfth-power positive displacement from the integer lattice. -/
theorem strongConclusion_proved : StrongConclusion := by
  exact ⟨constructedSet, rational_set_countable _, constructedSet_lower,
    constructedSet_original, constructedSet_weight_diverges,
    original_locallyFiniteAbove constructedSet_original constructedSet_lower,
    constructedSet_tiny⟩

end Apicella143

end

-- module Apicella143.RealConclusion
noncomputable section
open scoped ENNReal
namespace Apicella143

/-- The actual subset of the reals is the injective image of the rational construction. -/
def constructedRealSet : Set ℝ := (fun q : ℚ => (q : ℝ)) '' constructedSet

def constructedRealEquiv : constructedSet ≃ constructedRealSet :=
  Equiv.ofBijective (fun a => ⟨(a.val : ℝ), ⟨a.val, a.property, rfl⟩⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact Rat.cast_injective (congrArg Subtype.val hab),
    by
      intro a
      obtain ⟨q, hq, heq⟩ := a.property
      exact ⟨⟨q, hq⟩, Subtype.ext heq⟩⟩

lemma constructedRealSet_lower : ∀ a ∈ constructedRealSet, (2 : ℝ) ≤ a := by
  intro a ha
  obtain ⟨q, hq, rfl⟩ := ha
  change (2 : ℝ) ≤ (q : ℝ)
  exact_mod_cast constructedSet_lower q hq

lemma constructedRealSet_separated :
    ∀ a ∈ constructedRealSet, ∀ b ∈ constructedRealSet, a ≠ b →
      ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ |(k : ℝ) * a - b| := by
  intro a ha b hb hab k hk
  obtain ⟨q, hq, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hb
  have hqr : q ≠ r := fun h => hab (congrArg (fun x : ℚ => (x : ℝ)) h)
  exact (original_iff_real_inequalities constructedSet).mp constructedSet_original q hq r hr hqr k hk

lemma constructedRealSet_weight_diverges :
    (∑' a : constructedRealSet, ENNReal.ofReal (1 / (a.val * Real.log a.val))) = ⊤ := by
  rw [← constructedRealEquiv.tsum_eq (fun a : constructedRealSet =>
    ENNReal.ofReal (1 / (a.val * Real.log a.val)))]
  exact constructedSet_weight_diverges

lemma constructedRealSet_not_summable :
    ¬ Summable (fun a : constructedRealSet => 1 / (a.val * Real.log a.val)) := by
  intro hs
  have hn (a : constructedRealSet) : 0 ≤ 1 / (a.val * Real.log a.val) := by
    have ha := constructedRealSet_lower a a.property
    have hlog : 0 < Real.log a.val := Real.log_pos (by linarith)
    positivity
  have h := ENNReal.ofReal_tsum_of_nonneg hn hs
  rw [constructedRealSet_weight_diverges] at h
  exact ENNReal.ofReal_ne_top h

/-- A completely explicit real-domain formulation, including rationality, countability,
all ordered positive-integer multiplier inequalities, and divergence of the nonnegative sum. -/
theorem realConclusion_proved :
    ∃ A : Set ℝ, A.Countable ∧ A ⊆ Set.Ici 2 ∧
      (∀ a ∈ A, ∃ q : ℚ, a = (q : ℝ)) ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℝ) * a - b|) ∧
      (∑' a : A, ENNReal.ofReal (1 / (a.val * Real.log a.val))) = ⊤ ∧
      ¬ Summable (fun a : A => 1 / (a.val * Real.log a.val)) := by
  refine ⟨constructedRealSet, (rational_set_countable constructedSet).image _,
    constructedRealSet_lower, ?_, constructedRealSet_separated,
    constructedRealSet_weight_diverges, constructedRealSet_not_summable⟩
  intro a ha
  obtain ⟨q, _, rfl⟩ := ha
  exact ⟨q, rfl⟩

end Apicella143

end

/- Erdős Problem 143, part (ii), is false.

This is a formalization of a known result, ported from Mattia Apicella's Lean 4 development
github.com/mapice/erdos-143-candidate-disproof (commit 0f4b96940c97c7e0c36d17b584ec2bf1d842c02a,
Lean 4.24) to the pinned toolchain; it is cited on erdosproblems.com/143. That work constructs a
countable set of rationals A in [2, ∞), with |k a - b| ≥ 1 for all distinct a, b in A and every
integer k ≥ 1, such that the sum of 1/(a log a) over A diverges. -/

theorem OMA.disproof : ¬ (type_of% @Erdos143.erdos_143.parts.ii) := by
  intro h
  obtain ⟨A, hc, hlow, _, hsep, _, hns⟩ := Apicella143.realConclusion_proved
  have hinf : A.Infinite := by
    intro hfin
    apply hns
    have : Finite A := hfin.to_subtype
    exact Summable.of_finite
  apply hns
  refine h A ⟨fun x hx => lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hlow hx), hinf, hc, ?_⟩
  intro x hx y hy hxy k hk
  exact hsep x hx y hy hxy k hk
