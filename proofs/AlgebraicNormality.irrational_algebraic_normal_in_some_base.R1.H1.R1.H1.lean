import OMAReductions.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# Wall's Theorem for Rational Shifts

Proves `OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1.H1`:
if `b ≥ 2` and `x : ℝ` is normal in base `b`, then `x + s` is normal in base `b` for every
`s : ℚ`.

The proof is completely elementary:
1. Relate `digitSeq` blocks to `⌊b^k * Int.fract (b^i * x)⌋₊`.
2. Prove Pyatetskii-Shapiro's hot-spot criterion via a finite-sum Chebyshev/variance bound on
   non-overlapping `k`-blocks in `B^(r*k)`-strings.
3. Use pigeonhole to show `Int.fract (b^i * s)` is eventually periodic with preperiod `i₀` and
   period `P ≥ 1`.
4. For each residue class `t < P`, `b^(i₀ + t) * x` satisfies the hot-spot bound in base `b^P`
   with constant `P`, hence is normal in base `b^P`, hence equidistributed on all `[c, d) ⊆ [0, 1)`,
   hence invariant under constant rotation by `Int.fract (b^(i₀ + t) * s)`.
5. Average over the `P` residue classes to conclude `IsNormalInBase b (x + s)`.
-/

open Filter NormalNumber

namespace WallRationalShift

/- ### Part 1: Digit sequences and fractional parts -/

lemma fract_nat_mul_eq (n : ℕ) (x : ℝ) :
    Int.fract ((n : ℝ) * x) = Int.fract ((n : ℝ) * Int.fract x) := by
  have hx : (n : ℝ) * x = (n : ℝ) * Int.fract x + ((n : ℤ) * ⌊x⌋ : ℤ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hx, Int.fract_add_intCast]

lemma digitSeq_eq_floor_fract (b : ℕ) (hb : 0 < b) (x : ℝ) (m : ℕ) :
    digitSeq b x m = ⌊(b : ℝ) * Int.fract ((b : ℝ) ^ m * x)⌋₊ := by
  unfold digitSeq
  have h1 : Int.fract ((b : ℝ) ^ m * x) = Int.fract ((b : ℝ) ^ m * Int.fract x) := by
    simpa [Nat.cast_pow] using fract_nat_mul_eq (b ^ m) x
  rw [h1]
  set y : ℝ := (b : ℝ) ^ m * Int.fract x
  have hy_nonneg : 0 ≤ y := mul_nonneg (by positivity) (Int.fract_nonneg x)
  have hbm1 : (b : ℝ) ^ (m + 1) * Int.fract x = (b : ℝ) * y := by
    dsimp only [y]; rw [pow_succ']; ring
  rw [hbm1]
  have hfl_eq : ⌊y⌋ = (⌊y⌋₊ : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by exact_mod_cast Nat.floor_le hy_nonneg,
      by exact_mod_cast Nat.lt_floor_add_one y⟩
  have hy_eq : y = (⌊y⌋₊ : ℝ) + Int.fract y := by
    rw [Int.fract, hfl_eq]
    push_cast
    ring
  have hby : (b : ℝ) * y = (b : ℝ) * Int.fract y + ((b * ⌊y⌋₊ : ℕ) : ℝ) := by
    conv_lhs => rw [hy_eq]
    rw [mul_add, Nat.cast_mul, add_comm]
  have hfl : ⌊(b : ℝ) * y⌋₊ = b * ⌊y⌋₊ + ⌊(b : ℝ) * Int.fract y⌋₊ := by
    rw [hby, Nat.floor_add_natCast (mul_nonneg (by positivity) (Int.fract_nonneg y)), add_comm]
  have hlt : ⌊(b : ℝ) * Int.fract y⌋₊ < b := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) (Int.fract_nonneg y))]
    calc (b : ℝ) * Int.fract y < (b : ℝ) * 1 :=
          mul_lt_mul_of_pos_left (Int.fract_lt_one y) (by positivity)
      _ = b := mul_one _
  rw [hfl, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

lemma nat_eq_of_base_digits_eq (b : ℕ) (hb : 0 < b) :
    ∀ k a₁ a₂ : ℕ, a₁ < b ^ k → a₂ < b ^ k →
      (∀ j : Fin k, (a₁ / b ^ (k - 1 - j.1)) % b = (a₂ / b ^ (k - 1 - j.1)) % b) →
      a₁ = a₂ := by
  intro k
  induction k with
  | zero =>
    intro a₁ a₂ h1 h2 _
    simp at h1 h2
    omega
  | succ k ih =>
    intro a₁ a₂ h1 h2 hdig
    have hq : a₁ / b ^ k = a₂ / b ^ k := by
      have h0 := hdig ⟨0, Nat.zero_lt_succ k⟩
      simp only [Nat.add_sub_cancel, Nat.sub_zero] at h0
      have hq1 : a₁ / b ^ k < b := by
        rw [Nat.div_lt_iff_lt_mul (pow_pos hb k)]
        simpa [pow_succ'] using h1
      have hq2 : a₂ / b ^ k < b := by
        rw [Nat.div_lt_iff_lt_mul (pow_pos hb k)]
        simpa [pow_succ'] using h2
      rwa [Nat.mod_eq_of_lt hq1, Nat.mod_eq_of_lt hq2] at h0
    have hr : a₁ % b ^ k = a₂ % b ^ k := by
      apply ih (a₁ % b ^ k) (a₂ % b ^ k) (Nat.mod_lt _ (pow_pos hb k))
        (Nat.mod_lt _ (pow_pos hb k))
      intro j
      have hj := hdig j.succ
      simp only [Fin.val_succ] at hj
      have hexp : k + 1 - 1 - (j.1 + 1) = k - 1 - j.1 := by omega
      rw [hexp] at hj
      have hdvd : b ^ (k - 1 - j.1 + 1) ∣ b ^ k := by
        apply Nat.pow_dvd_pow
        omega
      have hmod (a : ℕ) : ((a % b ^ k) / b ^ (k - 1 - j.1)) % b =
          (a / b ^ (k - 1 - j.1)) % b := by
        have hdecomp : a = b ^ k * (a / b ^ k) + a % b ^ k := (Nat.div_add_mod a (b ^ k)).symm
        obtain ⟨c, hc⟩ := hdvd
        have hdiv : a / b ^ (k - 1 - j.1) =
            b * (c * (a / b ^ k)) + (a % b ^ k) / b ^ (k - 1 - j.1) := by
          have ha_eq : a = b ^ (k - 1 - j.1) * (b * (c * (a / b ^ k))) + a % b ^ k := by
            conv_lhs => rw [hdecomp]
            rw [hc, pow_succ']
            ring
          conv_lhs => rw [ha_eq]
          rw [Nat.mul_add_div (pow_pos hb (k - 1 - j.1))]
        rw [hdiv, Nat.mul_add_mod]
      rw [hmod a₁, hmod a₂]
      exact hj
    calc a₁ = b ^ k * (a₁ / b ^ k) + a₁ % b ^ k := (Nat.div_add_mod a₁ (b ^ k)).symm
      _ = b ^ k * (a₂ / b ^ k) + a₂ % b ^ k := by rw [hq, hr]
      _ = a₂ := Nat.div_add_mod a₂ (b ^ k)

lemma exists_code_of_word (b : ℕ) (hb : 0 < b) :
    ∀ (k : ℕ) (w : Fin k → ℕ), (∀ j, w j < b) →
      ∃ a < b ^ k, ∀ j : Fin k, (a / b ^ (k - 1 - j.1)) % b = w j := by
  intro k
  induction k with
  | zero =>
    intro w _
    exact ⟨0, by simp, fun j => Fin.elim0 j⟩
  | succ k ih =>
    intro w hw
    obtain ⟨a', ha'lt, ha'⟩ := ih (fun j : Fin k => w j.succ) (fun j => hw j.succ)
    refine ⟨w 0 * b ^ k + a', ?_, ?_⟩
    · have h0 : w 0 + 1 ≤ b := hw 0
      calc w 0 * b ^ k + a' < w 0 * b ^ k + b ^ k := by omega
        _ = (w 0 + 1) * b ^ k := by ring
        _ ≤ b * b ^ k := Nat.mul_le_mul_right _ h0
        _ = b ^ (k + 1) := by rw [pow_succ']
    · intro j
      refine Fin.cases ?_ ?_ j
      · simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
        rw [mul_comm (w 0), Nat.mul_add_div (pow_pos hb k),
            Nat.div_eq_of_lt ha'lt, add_zero, Nat.mod_eq_of_lt (hw 0)]
      · intro j'
        have hexp : k + 1 - 1 - (j'.1 + 1) = k - 1 - j'.1 := by omega
        simp only [Fin.val_succ, hexp]
        have hdvd : b ^ (k - 1 - j'.1 + 1) ∣ b ^ k := Nat.pow_dvd_pow b (by omega)
        obtain ⟨c, hc⟩ := hdvd
        have hdiv : (w 0 * b ^ k + a') / b ^ (k - 1 - j'.1) =
            b * (w 0 * c) + a' / b ^ (k - 1 - j'.1) := by
          rw [hc, pow_succ']
          have : w 0 * (b * b ^ (k - 1 - j'.1) * c) + a' =
              b ^ (k - 1 - j'.1) * (b * (w 0 * c)) + a' := by ring
          rw [this, Nat.mul_add_div (pow_pos hb _)]
        rw [hdiv, Nat.mul_add_mod]
        exact ha' j'

lemma floor_block_digit (b k : ℕ) (hb : 0 < b) (x : ℝ) (i : ℕ) (j : Fin k) :
    digitSeq b x (i + j.1) =
      (⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * x)⌋₊ / b ^ (k - 1 - j.1)) % b := by
  rw [digitSeq_eq_floor_fract b hb x (i + j.1)]
  set u : ℝ := Int.fract ((b : ℝ) ^ i * x)
  have hu0 : 0 ≤ u := Int.fract_nonneg _
  have hu1 : u < 1 := Int.fract_lt_one _
  have hfr : Int.fract ((b : ℝ) ^ (i + j.1) * x) = Int.fract ((b : ℝ) ^ j.1 * u) := by
    have : (b : ℝ) ^ (i + j.1) * x = (b : ℝ) ^ j.1 * ((b : ℝ) ^ i * x) := by
      rw [pow_add]; ring
    rw [this]
    simpa [Nat.cast_pow] using fract_nat_mul_eq (b ^ j.1) ((b : ℝ) ^ i * x)
  rw [hfr]
  have hdig : ⌊(b : ℝ) * Int.fract ((b : ℝ) ^ j.1 * u)⌋₊ =
      ⌊(b : ℝ) ^ (j.1 + 1) * u⌋₊ % b := by
    have := digitSeq_eq_floor_fract b hb u j.1
    unfold digitSeq at this
    rw [Int.fract_eq_self.mpr ⟨hu0, hu1⟩] at this
    exact this.symm
  rw [hdig]
  have hdiv : ⌊(b : ℝ) ^ (j.1 + 1) * u⌋₊ =
      ⌊(b : ℝ) ^ k * u⌋₊ / b ^ (k - 1 - j.1) := by
    have hexp : j.1 + 1 + (k - 1 - j.1) = k := by omega
    have hcast : ((b ^ (k - 1 - j.1) : ℕ) : ℝ) ≠ 0 := by positivity
    have heq : (b : ℝ) ^ (j.1 + 1) * u =
        ((b : ℝ) ^ k * u) / ((b ^ (k - 1 - j.1) : ℕ) : ℝ) := by
      rw [eq_div_iff hcast, Nat.cast_pow]
      calc (b : ℝ) ^ (j.1 + 1) * u * (b : ℝ) ^ (k - 1 - j.1)
          = (b : ℝ) ^ (j.1 + 1 + (k - 1 - j.1)) * u := by rw [pow_add]; ring
        _ = (b : ℝ) ^ k * u := by rw [hexp]
    rw [heq, Nat.floor_div_natCast]
  rw [hdiv]

lemma digitSeq_block_iff_floor_eq (b k : ℕ) (hb : 0 < b) (x : ℝ) (i : ℕ) (a : ℕ)
    (ha : a < b ^ k) :
    (∀ j : Fin k, digitSeq b x (i + j.1) = (a / b ^ (k - 1 - j.1)) % b) ↔
      ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * x)⌋₊ = a := by
  constructor
  · intro h
    have hlt : ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * x)⌋₊ < b ^ k := by
      rw [Nat.floor_lt (mul_nonneg (by positivity) (Int.fract_nonneg _))]
      rw [Nat.cast_pow]
      calc (b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * x) < (b : ℝ) ^ k * 1 :=
            mul_lt_mul_of_pos_left (Int.fract_lt_one _) (by positivity)
        _ = (b : ℝ) ^ k := mul_one _
    apply nat_eq_of_base_digits_eq b hb k _ a hlt ha
    intro j
    rw [← floor_block_digit b k hb x i j]
    exact h j
  · intro h j
    rw [floor_block_digit b k hb x i j, h]

lemma floor_mul_fract_lt (B : ℕ) (hB : 0 < B) (u : ℝ) :
    ⌊(B : ℝ) * Int.fract u⌋₊ < B := by
  rw [Nat.floor_lt (mul_nonneg (by positivity) (Int.fract_nonneg _))]
  calc (B : ℝ) * Int.fract u < (B : ℝ) * 1 :=
        mul_lt_mul_of_pos_left (Int.fract_lt_one _) (by positivity)
    _ = B := mul_one _

lemma floor_mul_fract_eq_iff (B : ℕ) (hB : 0 < B) (u : ℝ) (a : ℕ) :
    ⌊(B : ℝ) * Int.fract u⌋₊ = a ↔
      (a : ℝ) / B ≤ Int.fract u ∧ Int.fract u < ((a : ℝ) + 1) / B := by
  have hBp : (0 : ℝ) < B := by positivity
  rw [Nat.floor_eq_iff (mul_nonneg (by positivity) (Int.fract_nonneg _)),
      div_le_iff₀ hBp, lt_div_iff₀ hBp, mul_comm (Int.fract u)]

/- ### Part 2: Pyatetskii-Shapiro Hot-Spot Criterion -/

noncomputable def occ (B : ℕ) (y : ℝ) (L a M : ℕ) : ℕ :=
  ((Finset.range M).filter (fun m => ⌊(B : ℝ) ^ L * Int.fract ((B : ℝ) ^ m * y)⌋₊ = a)).card

lemma sum_indicator_sub_eq_zero (Q a : ℕ) (ha : a < Q) :
    ∑ c : Fin Q, ((if c.1 = a then (1 : ℝ) else 0) - 1 / (Q : ℝ)) = 0 := by
  have hQ0 : 0 < Q := by omega
  have hQp : (Q : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1' : ∑ c : Fin Q, (if c.1 = a then (1 : ℝ) else 0) = 1 := by
    trans ∑ c : Fin Q, (if c = ⟨a, ha⟩ then (1 : ℝ) else 0)
    · refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h : c.1 = a
      · have hc : c = ⟨a, ha⟩ := Fin.ext h
        simp [hc]
      · have hc : c ≠ ⟨a, ha⟩ := fun hc => h (congrArg Fin.val hc)
        simp [h, hc]
    · simp
  rw [h1']
  field_simp
  ring

lemma sum_pi_single_zero {r Q : ℕ} (f : Fin Q → ℝ) (hf : ∑ c : Fin Q, f c = 0)
    (g : Fin Q → ℝ) (j₁ j₂ : Fin r) (hne : j₁ ≠ j₂) :
    ∑ v : Fin r → Fin Q, f (v j₁) * g (v j₂) = 0 := by
  classical
  let e : (Fin r → Fin Q) ≃ Fin Q × ({ j : Fin r // j ≠ j₁ } → Fin Q) :=
    { toFun := fun v => (v j₁, fun j => v j.1)
      invFun := fun p j => if h : j = j₁ then p.1 else p.2 ⟨j, h⟩
      left_inv := fun v => by
        funext j
        by_cases h : j = j₁ <;> simp [h]
      right_inv := fun p => by
        refine Prod.ext (by simp) ?_
        funext j
        simp [j.2] }
  rw [← Equiv.sum_comp e.symm]
  rw [Fintype.sum_prod_type]
  have heval : ∀ (c : Fin Q) (w : { j : Fin r // j ≠ j₁ } → Fin Q),
      f (e.symm (c, w) j₁) * g (e.symm (c, w) j₂) = f c * g (w ⟨j₂, hne.symm⟩) := by
    intro c w
    simp [e, hne.symm]
  simp_rw [heval, ← Finset.mul_sum, ← Finset.sum_mul, hf, zero_mul]

lemma chebyshev_block_variance (Q r a : ℕ) (ha : a < Q) (δ : ℝ) (hδ : 0 < δ) :
    (((Finset.univ : Finset (Fin r → Fin Q)).filter (fun v =>
      δ < |(((Finset.univ : Finset (Fin r)).filter (fun j => (v j).1 = a)).card : ℝ) / r -
        1 / (Q : ℝ)|)).card : ℝ) * (δ * r) ^ 2 ≤ (r : ℝ) * (Q : ℝ) ^ r := by
  classical
  set p : ℝ := 1 / (Q : ℝ)
  let X : Fin r → (Fin r → Fin Q) → ℝ := fun j v => (if (v j).1 = a then (1 : ℝ) else 0) - p
  have hXsum (v : Fin r → Fin Q) :
      ∑ j : Fin r, X j v =
        (((Finset.univ : Finset (Fin r)).filter (fun j => (v j).1 = a)).card : ℝ) - r * p := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have htot : ∑ v : Fin r → Fin Q, (∑ j : Fin r, X j v) ^ 2 ≤ (r : ℝ) * (Q : ℝ) ^ r := by
    have hexp : ∀ v : Fin r → Fin Q,
        (∑ j : Fin r, X j v) ^ 2 = ∑ j₁ : Fin r, ∑ j₂ : Fin r, X j₁ v * X j₂ v := fun v => by
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hdiag : ∀ j₁ : Fin r,
        ∑ v : Fin r → Fin Q, ∑ j₂ : Fin r, X j₁ v * X j₂ v =
          ∑ v : Fin r → Fin Q, X j₁ v * X j₁ v := by
      intro j₁
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single j₁]
      · intro j₂ _ hne
        exact sum_pi_single_zero (fun c => (if c.1 = a then (1 : ℝ) else 0) - p)
          (sum_indicator_sub_eq_zero Q a ha)
          (fun c => (if c.1 = a then (1 : ℝ) else 0) - p) j₁ j₂ hne.symm
      · intro h; exact absurd (Finset.mem_univ j₁) h
    simp_rw [hdiag]
    have hbound : ∀ j₁ : Fin r,
        ∑ v : Fin r → Fin Q, X j₁ v * X j₁ v ≤ (Q : ℝ) ^ r := by
      intro j₁
      calc ∑ v : Fin r → Fin Q, X j₁ v * X j₁ v
          ≤ ∑ _v : Fin r → Fin Q, (1 : ℝ) := by
            refine Finset.sum_le_sum fun v _ => ?_
            have hp0 : 0 ≤ p := by positivity
            have hp1 : p ≤ 1 := by
              dsimp only [p]
              have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
              exact div_le_one_of_le₀ hQ1 (by positivity)
            dsimp only [X]
            split_ifs <;> nlinarith
        _ = (Q : ℝ) ^ r := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow]
    calc ∑ j₁ : Fin r, ∑ v : Fin r → Fin Q, X j₁ v * X j₁ v
        ≤ ∑ _j₁ : Fin r, (Q : ℝ) ^ r := Finset.sum_le_sum fun j₁ _ => hbound j₁
      _ = (r : ℝ) * (Q : ℝ) ^ r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  set Bad := (Finset.univ : Finset (Fin r → Fin Q)).filter (fun v =>
    δ < |(((Finset.univ : Finset (Fin r)).filter (fun j => (v j).1 = a)).card : ℝ) / r - p|)
  have hbad : (Bad.card : ℝ) * (δ * r) ^ 2 ≤ ∑ v ∈ Bad, (∑ j : Fin r, X j v) ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun v hv => ?_
    have hv' := (Finset.mem_filter.mp hv).2
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · have hrp : (0 : ℝ) < r := by positivity
      have hmul : δ * r < |∑ j : Fin r, X j v| := by
        rw [hXsum v]
        have heq : ((((Finset.univ : Finset (Fin r)).filter (fun j => (v j).1 = a)).card : ℝ) -
            r * p) = r * ((((Finset.univ : Finset (Fin r)).filter
            (fun j => (v j).1 = a)).card : ℝ) / r - p) := by field_simp
        rw [heq, abs_mul, abs_of_pos hrp, mul_comm δ]
        exact mul_lt_mul_of_pos_left hv' hrp
      have hsq : (δ * r) ^ 2 ≤ |∑ j : Fin r, X j v| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hmul.le 2
      simpa [sq_abs] using hsq
  calc (Bad.card : ℝ) * (δ * r) ^ 2
      ≤ ∑ v ∈ Bad, (∑ j : Fin r, X j v) ^ 2 := hbad
    _ ≤ ∑ v : Fin r → Fin Q, (∑ j : Fin r, X j v) ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg fun v => sq_nonneg _
    _ ≤ (r : ℝ) * (Q : ℝ) ^ r := htot

lemma shift_occ_diff (B : ℕ) (y : ℝ) (k a M d : ℕ) :
    |((Finset.range M).filter (fun m =>
        ⌊(B : ℝ) ^ k * Int.fract ((B : ℝ) ^ (m + d) * y)⌋₊ = a)).card -
      (occ B y k a M : ℝ)| ≤ (d : ℝ) := by
  let P : ℕ → Prop := fun m => ⌊(B : ℝ) ^ k * Int.fract ((B : ℝ) ^ m * y)⌋₊ = a
  classical
  have h1 : ((Finset.range M).filter (fun m => P (m + d))).card ≤
      ((Finset.range M).filter P).card + d := by
    have hsub : ((Finset.range M).filter (fun m => P (m + d))).image (· + d) ⊆
        ((Finset.range M).filter P) ∪ (Finset.Ico M (M + d)) := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have ⟨hmM, hPm⟩ := Finset.mem_filter.mp hm
      rw [Finset.mem_range] at hmM
      by_cases hlt : m + d < M
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hPm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    calc ((Finset.range M).filter (fun m => P (m + d))).card
        = (((Finset.range M).filter (fun m => P (m + d))).image (· + d)).card :=
          (Finset.card_image_of_injective _ (fun _ _ h => by omega)).symm
      _ ≤ (((Finset.range M).filter P) ∪ (Finset.Ico M (M + d))).card :=
          Finset.card_le_card hsub
      _ ≤ ((Finset.range M).filter P).card + (Finset.Ico M (M + d)).card :=
          Finset.card_union_le _ _
      _ = ((Finset.range M).filter P).card + d := by rw [Nat.card_Ico]; omega
  have h2 : ((Finset.range M).filter P).card ≤
      ((Finset.range M).filter (fun m => P (m + d))).card + d := by
    have hsub : (Finset.range M).filter P ⊆
        (((Finset.range M).filter (fun m => P (m + d))).image (· + d)) ∪ (Finset.range d) := by
      intro x hx
      have ⟨hxM, hPx⟩ := Finset.mem_filter.mp hx
      rw [Finset.mem_range] at hxM
      by_cases hlt : x < d
      · exact Finset.mem_union_right _ (Finset.mem_range.mpr hlt)
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x - d, ?_, by omega⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
          have : x - d + d = x := by omega
          rwa [this]⟩
    calc ((Finset.range M).filter P).card
        ≤ ((((Finset.range M).filter (fun m => P (m + d))).image (· + d)) ∪ (Finset.range d)).card :=
          Finset.card_le_card hsub
      _ ≤ (((Finset.range M).filter (fun m => P (m + d))).image (· + d)).card +
            (Finset.range d).card := Finset.card_union_le _ _
      _ = ((Finset.range M).filter (fun m => P (m + d))).card + d := by
          rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  rw [abs_le]
  have h1r : (((Finset.range M).filter (fun m => P (m + d))).card : ℝ) ≤
      (occ B y k a M : ℝ) + d := by exact_mod_cast h1
  have h2r : (occ B y k a M : ℝ) ≤
      (((Finset.range M).filter (fun m => P (m + d))).card : ℝ) + d := by exact_mod_cast h2
  constructor <;> linarith

lemma pyatetskii_shapiro (B : ℕ) (hB : 2 ≤ B) (y : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hhot : ∀ (L a : ℕ), a < B ^ L → ∀ ε > 0,
      ∀ᶠ M : ℕ in atTop, (occ B y L a M : ℝ) / M ≤ C / (B : ℝ) ^ L + ε) :
    ∀ (k a : ℕ), 1 ≤ k → a < B ^ k →
      Tendsto (fun M : ℕ => (occ B y k a M : ℝ) / M) atTop (nhds (1 / (B : ℝ) ^ k)) := by
  intro k a hk ha
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hBpos : 0 < B := by omega
  set Q : ℕ := B ^ k
  have hQpos : 0 < Q := pow_pos hBpos k
  set p : ℝ := 1 / (Q : ℝ)
  set δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  obtain ⟨r, hr⟩ := exists_nat_gt (max 1 ((C + 1) / (δ ^ 2 * δ)))
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
    exact_mod_cast this.le
  have hrpos : (0 : ℝ) < r := by positivity
  have hrbound : C / (δ ^ 2 * r) < δ := by
    have hgt : (C + 1) / (δ ^ 2 * δ) < r := lt_of_le_of_lt (le_max_right _ _) hr
    have h1 : C + 1 < r * (δ ^ 2 * δ) := (div_lt_iff₀ (by positivity)).mp hgt
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  classical
  let Bad : Finset (Fin r → Fin Q) := (Finset.univ : Finset (Fin r → Fin Q)).filter (fun v =>
    δ < |(((Finset.univ : Finset (Fin r)).filter (fun j => (v j).1 = a)).card : ℝ) / r - p|)
  have hBad_card : (Bad.card : ℝ) / (Q : ℝ) ^ r ≤ 1 / (δ ^ 2 * r) := by
    have hcheb := chebyshev_block_variance Q r a ha δ hδ
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  let encode : (Fin r → Fin Q) → ℕ := fun v =>
    Classical.choose (exists_code_of_word Q hQpos r (fun j => (v j).1) (fun j => (v j).2))
  have henc_lt : ∀ v : Fin r → Fin Q, encode v < Q ^ r := fun v =>
    (Classical.choose_spec (exists_code_of_word Q hQpos r (fun j => (v j).1) (fun j => (v j).2))).1
  have henc_dig : ∀ (v : Fin r → Fin Q) (j : Fin r),
      (encode v / Q ^ (r - 1 - j.1)) % Q = (v j).1 := fun v =>
    (Classical.choose_spec (exists_code_of_word Q hQpos r (fun j => (v j).1) (fun j => (v j).2))).2
  let blockVec : ℕ → Fin r → Fin Q := fun m j =>
    ⟨⌊(Q : ℝ) * Int.fract ((B : ℝ) ^ (m + j.1 * k) * y)⌋₊,
      floor_mul_fract_lt Q hQpos _⟩
  have hblock_code : ∀ (m : ℕ) (v : Fin r → Fin Q),
      blockVec m = v ↔ ⌊(B : ℝ) ^ (r * k) * Int.fract ((B : ℝ) ^ m * y)⌋₊ = encode v := by
    intro m v
    have hQr : (B : ℝ) ^ (r * k) = (Q : ℝ) ^ r := by
      dsimp only [Q]; rw [Nat.cast_pow, ← pow_mul, mul_comm]
    rw [hQr]
    have hstep : ∀ j : Fin r,
        (blockVec m j).1 =
          (⌊(Q : ℝ) ^ r * Int.fract ((B : ℝ) ^ m * y)⌋₊ / Q ^ (r - 1 - j.1)) % Q := by
      intro j
      dsimp only [blockVec]
      have hpow : (B : ℝ) ^ (m + j.1 * k) * y = (Q : ℝ) ^ j.1 * ((B : ℝ) ^ m * y) := by
        dsimp only [Q]; rw [pow_add, Nat.cast_pow, ← pow_mul, mul_comm j.1 k]; ring
      rw [hpow]
      have h1 := floor_block_digit Q r hQpos ((B : ℝ) ^ m * y) 0 j
      simp only [zero_add, pow_zero, one_mul] at h1
      rw [digitSeq_eq_floor_fract Q hQpos ((B : ℝ) ^ m * y) j.1] at h1
      exact h1
    constructor
    · intro hmv
      have hlt : ⌊(Q : ℝ) ^ r * Int.fract ((B : ℝ) ^ m * y)⌋₊ < Q ^ r := by
        simpa [Nat.cast_pow] using floor_mul_fract_lt (Q ^ r) (pow_pos hQpos r) ((B : ℝ) ^ m * y)
      apply nat_eq_of_base_digits_eq Q hQpos r _ (encode v) hlt (henc_lt v)
      intro j
      rw [← hstep j, hmv, henc_dig v j]
    · intro hcode
      funext j
      apply Fin.ext
      rw [hstep j, hcode, henc_dig v j]
  have hhot_bad : ∀ᶠ M : ℕ in atTop,
      (((Finset.range M).filter (fun m => blockVec m ∈ Bad)).card : ℝ) / M ≤
        C / (δ ^ 2 * r) + δ := by
    by_cases hBad0 : Bad.card = 0
    · filter_upwards [Filter.eventually_ge_atTop 1] with M hM
      have hEmpty : Bad = ∅ := Finset.card_eq_zero.mp hBad0
      simp only [hEmpty, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
        Nat.cast_zero, zero_div]
      positivity
    · have hBad_pos : (0 : ℝ) < Bad.card := by positivity
      have hall : ∀ v ∈ Bad, ∀ᶠ M : ℕ in atTop,
          (occ B y (r * k) (encode v) M : ℝ) / M ≤ C / (B : ℝ) ^ (r * k) + δ / Bad.card := by
        intro v _
        have hlt : encode v < B ^ (r * k) := by
          have := henc_lt v
          dsimp only [Q] at this
          rwa [← pow_mul, mul_comm] at this
        exact hhot (r * k) (encode v) hlt (δ / Bad.card) (by positivity)
      have hfin := (Finset.eventually_all Bad).mpr hall
      filter_upwards [hfin, Filter.eventually_ge_atTop 1] with M hM hM1
      have hcard_le : ((Finset.range M).filter (fun m => blockVec m ∈ Bad)).card ≤
          ∑ v ∈ Bad, occ B y (r * k) (encode v) M := by
        calc ((Finset.range M).filter (fun m => blockVec m ∈ Bad)).card
            ≤ (Bad.biUnion fun v => (Finset.range M).filter (fun m => blockVec m = v)).card := by
              apply Finset.card_le_card
              intro m hm
              have ⟨hmM, hmb⟩ := Finset.mem_filter.mp hm
              exact Finset.mem_biUnion.mpr ⟨blockVec m, hmb, Finset.mem_filter.mpr ⟨hmM, rfl⟩⟩
          _ ≤ ∑ v ∈ Bad, ((Finset.range M).filter (fun m => blockVec m = v)).card :=
              Finset.card_biUnion_le
          _ = ∑ v ∈ Bad, occ B y (r * k) (encode v) M := by
              refine Finset.sum_congr rfl fun v _ => ?_
              unfold occ
              congr 1
              ext m
              simp [hblock_code m v]
      have hMpos : (0 : ℝ) < M := by positivity
      calc (((Finset.range M).filter (fun m => blockVec m ∈ Bad)).card : ℝ) / M
          ≤ (∑ v ∈ Bad, (occ B y (r * k) (encode v) M : ℝ)) / M := by
            gcongr
            exact_mod_cast hcard_le
        _ = ∑ v ∈ Bad, (occ B y (r * k) (encode v) M : ℝ) / M := Finset.sum_div _ _ _
        _ ≤ ∑ _v ∈ Bad, (C / (B : ℝ) ^ (r * k) + δ / Bad.card) :=
            Finset.sum_le_sum fun v hv => hM v hv
        _ = (Bad.card : ℝ) * (C / (B : ℝ) ^ (r * k) + δ / Bad.card) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = C * ((Bad.card : ℝ) / (Q : ℝ) ^ r) + δ := by
            have hQr : (B : ℝ) ^ (r * k) = (Q : ℝ) ^ r := by
              dsimp only [Q]; rw [Nat.cast_pow, ← pow_mul, mul_comm]
            rw [hQr]
            field_simp
        _ ≤ C * (1 / (δ ^ 2 * r)) + δ := by gcongr
        _ = C / (δ ^ 2 * r) + δ := by ring
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp hhot_bad
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt ((r * k : ℝ) / δ)
  refine ⟨max (max M₀ M₁) 1, fun M hM => ?_⟩
  have hM_ge₀ : M₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM_ge₁ : M₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < M := by positivity
  have hbadM := hM₀ M hM_ge₀
  have hshiftM : (r * k : ℝ) / M < δ := by
    have : (r * k : ℝ) / δ < M := lt_of_lt_of_le hM₁ (by exact_mod_cast hM_ge₁)
    rw [div_lt_iff₀ hMpos]
    have h2 := (div_lt_iff₀ hδ).mp this
    linarith
  let freq : (Fin r → Fin Q) → ℝ := fun v =>
    (((Finset.univ : Finset (Fin r)).filter (fun j => (v j).1 = a)).card : ℝ) / r
  have havg_shift : |(∑ m ∈ Finset.range M, freq (blockVec m)) / M -
      (occ B y k a M : ℝ) / M| ≤ (r * k : ℝ) / M := by
    have hsum_eq : ∑ m ∈ Finset.range M, freq (blockVec m) =
        (∑ j : Fin r, (((Finset.range M).filter (fun m =>
          ⌊(B : ℝ) ^ k * Int.fract ((B : ℝ) ^ (m + j.1 * k) * y)⌋₊ = a)).card : ℝ)) / r := by
      dsimp only [freq, blockVec]
      rw [← Finset.sum_div]
      congr 1
      trans ∑ m ∈ Finset.range M, ∑ j : Fin r,
          (if ⌊(Q : ℝ) * Int.fract ((B : ℝ) ^ (m + j.1 * k) * y)⌋₊ = a then (1 : ℝ) else 0)
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_boole]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_boole]
        congr 2
        ext m
        simp [Q]
    rw [hsum_eq]
    have hrew : (∑ j : Fin r, (((Finset.range M).filter (fun m =>
        ⌊(B : ℝ) ^ k * Int.fract ((B : ℝ) ^ (m + j.1 * k) * y)⌋₊ = a)).card : ℝ)) / r / M -
        (occ B y k a M : ℝ) / M =
        (∑ j : Fin r, ((((Finset.range M).filter (fun m =>
          ⌊(B : ℝ) ^ k * Int.fract ((B : ℝ) ^ (m + j.1 * k) * y)⌋₊ = a)).card : ℝ) -
          (occ B y k a M : ℝ))) / (r * M) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, sub_div, div_div, mul_div_mul_left _ _ hrpos.ne']
    rw [hrew, abs_div, abs_of_pos (mul_pos hrpos hMpos)]
    have htri : |∑ j : Fin r, ((((Finset.range M).filter (fun m =>
        ⌊(B : ℝ) ^ k * Int.fract ((B : ℝ) ^ (m + j.1 * k) * y)⌋₊ = a)).card : ℝ) -
        (occ B y k a M : ℝ))| ≤ (r : ℝ) * ((r * k : ℝ)) := by
      calc |∑ j : Fin r, _|
          ≤ ∑ j : Fin r, |((((Finset.range M).filter (fun m =>
              ⌊(B : ℝ) ^ k * Int.fract ((B : ℝ) ^ (m + j.1 * k) * y)⌋₊ = a)).card : ℝ) -
              (occ B y k a M : ℝ))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin r, ((j.1 * k : ℕ) : ℝ) :=
            Finset.sum_le_sum fun j _ => shift_occ_diff B y k a M (j.1 * k)
        _ ≤ ∑ _j : Fin r, (r * k : ℝ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have : j.1 * k ≤ r * k := Nat.mul_le_mul_right k j.2.le
            exact_mod_cast this
        _ = (r : ℝ) * (r * k : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc |∑ j : Fin r, _| / (r * M)
        ≤ (r : ℝ) * (r * k : ℝ) / (r * M) := div_le_div_of_nonneg_right htri (by positivity)
      _ = (r * k : ℝ) / M := by field_simp
  have havg_p : |(∑ m ∈ Finset.range M, freq (blockVec m)) / M - p| ≤
      δ + (((Finset.range M).filter (fun m => blockVec m ∈ Bad)).card : ℝ) / M := by
    have hrew : (∑ m ∈ Finset.range M, freq (blockVec m)) / M - p =
        (∑ m ∈ Finset.range M, (freq (blockVec m) - p)) / M := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [hrew, abs_div, abs_of_pos hMpos]
    have hterm : ∀ m ∈ Finset.range M,
        |freq (blockVec m) - p| ≤ δ + if blockVec m ∈ Bad then (1 : ℝ) else 0 := by
      intro m _
      by_cases hmb : blockVec m ∈ Bad
      · simp only [hmb, ↓reduceIte]
        have hf0 : 0 ≤ freq (blockVec m) := by dsimp only [freq]; positivity
        have hf1 : freq (blockVec m) ≤ 1 := by
          dsimp only [freq]
          rw [div_le_one hrpos]
          have : ((Finset.univ : Finset (Fin r)).filter (fun j => (blockVec m j).1 = a)).card ≤ r := by
            calc _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_filter_le _ _
              _ = r := by simp
          exact_mod_cast this
        have hp0 : 0 ≤ p := by positivity
        have hp1 : p ≤ 1 := by
          dsimp only [p]
          have : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
          exact div_le_one_of_le₀ this (by positivity)
        rw [abs_le]
        constructor <;> linarith
      · simp only [hmb, ↓reduceIte, add_zero]
        have hnot : ¬ δ < |freq (blockVec m) - p| := by
          intro hlt
          exact hmb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        linarith
    calc |∑ m ∈ Finset.range M, (freq (blockVec m) - p)| / M
        ≤ (∑ m ∈ Finset.range M, |freq (blockVec m) - p|) / M :=
          div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hMpos.le
      _ ≤ (∑ m ∈ Finset.range M, (δ + if blockVec m ∈ Bad then (1 : ℝ) else 0)) / M :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum hterm) hMpos.le
      _ = δ + (((Finset.range M).filter (fun m => blockVec m ∈ Bad)).card : ℝ) / M := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.sum_boole, add_div]
          congr 1
          field_simp
  rw [Real.dist_eq]
  have hp_eq : 1 / (B : ℝ) ^ k = p := by dsimp only [p, Q]; rw [Nat.cast_pow]
  rw [hp_eq]
  have htri : |(occ B y k a M : ℝ) / M - p| ≤
      |(∑ m ∈ Finset.range M, freq (blockVec m)) / M - (occ B y k a M : ℝ) / M| +
      |(∑ m ∈ Finset.range M, freq (blockVec m)) / M - p| := by
    have : (occ B y k a M : ℝ) / M - p =
        -((∑ m ∈ Finset.range M, freq (blockVec m)) / M - (occ B y k a M : ℝ) / M) +
        ((∑ m ∈ Finset.range M, freq (blockVec m)) / M - p) := by ring
    rw [this]
    calc _ ≤ |-((∑ m ∈ Finset.range M, freq (blockVec m)) / M - (occ B y k a M : ℝ) / M)| +
            |(∑ m ∈ Finset.range M, freq (blockVec m)) / M - p| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hδ4 : 4 * δ = ε := by dsimp only [δ]; ring
  linarith

/- ### Part 3: Equidistribution on arbitrary intervals and rotation invariance -/

lemma equidist_Ico_of_base_normal (B : ℕ) (hB : 2 ≤ B) (y : ℝ)
    (hnorm : ∀ (L a : ℕ), 1 ≤ L → a < B ^ L →
      Tendsto (fun M : ℕ => (occ B y L a M : ℝ) / M) atTop (nhds (1 / (B : ℝ) ^ L)))
    (c d : ℝ) (hc0 : 0 ≤ c) (hcd : c ≤ d) (hd1 : d ≤ 1) :
    Tendsto (fun M : ℕ =>
      (((Finset.range M).filter (fun m =>
        c ≤ Int.fract ((B : ℝ) ^ m * y) ∧ Int.fract ((B : ℝ) ^ m * y) < d)).card : ℝ) / M)
      atTop (nhds (d - c)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hBpos : 0 < B := by omega
  have hB1 : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have hpow0 : Tendsto (fun L : ℕ => (2 : ℝ) / (B : ℝ) ^ L) atTop (nhds 0) := by
    have hinv : Tendsto (fun L : ℕ => ((B : ℝ)⁻¹) ^ L) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hB1)
    have h2 := hinv.const_mul 2
    simpa [div_eq_mul_inv, inv_pow] using h2
  obtain ⟨L0, hL0⟩ := (Metric.tendsto_atTop.mp hpow0) (ε / 2) (by positivity)
  let L' : ℕ := max L0 1
  have hL'1 : 1 ≤ L' := le_max_right _ _
  have hBL_err : (2 : ℝ) / (B : ℝ) ^ L' < ε / 2 := by
    have := hL0 L' (le_max_left _ _)
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at this
    exact this
  set Q : ℕ := B ^ L'
  have hQpos : 0 < Q := pow_pos hBpos L'
  have hQrpos : (0 : ℝ) < Q := by positivity
  let a₁ : ℕ := ⌊c * Q⌋₊
  let a₂ : ℕ := ⌊d * Q⌋₊
  have ha₁_le : (a₁ : ℝ) ≤ c * Q := Nat.floor_le (mul_nonneg hc0 hQrpos.le)
  have hc_lt : c * Q < (a₁ : ℝ) + 1 := Nat.lt_floor_add_one _
  have ha₂_le : (a₂ : ℝ) ≤ d * Q := Nat.floor_le (mul_nonneg (le_trans hc0 hcd) hQrpos.le)
  have hd_lt : d * Q < (a₂ : ℝ) + 1 := Nat.lt_floor_add_one _
  have ha₁_le_a₂ : a₁ ≤ a₂ := Nat.floor_mono (mul_le_mul_of_nonneg_right hcd hQrpos.le)
  have ha₂_le_Q : a₂ ≤ Q := by
    by_contra h
    push Not at h
    have h1 : ((Q + 1 : ℕ) : ℝ) ≤ (a₂ : ℝ) := by exact_mod_cast h
    have h2 : d * Q ≤ 1 * Q := mul_le_mul_of_nonneg_right hd1 hQrpos.le
    push_cast at h1
    linarith
  let S_in : Finset ℕ := Finset.Ico (a₁ + 1) a₂
  let S_out : Finset ℕ := (Finset.Ico a₁ (a₂ + 1)).filter (· < Q)
  have hSin_lt : ∀ a ∈ S_in, a < Q := fun a ha => by
    have := (Finset.mem_Ico.mp ha).2
    omega
  have hSout_lt : ∀ a ∈ S_out, a < Q := fun a ha => (Finset.mem_filter.mp ha).2
  have ht_in : Tendsto (fun M : ℕ =>
      (∑ a ∈ S_in, (occ B y L' a M : ℝ)) / M) atTop (nhds ((S_in.card : ℝ) / Q)) := by
    have hsum : Tendsto (fun M : ℕ => ∑ a ∈ S_in, (occ B y L' a M : ℝ) / M) atTop
        (nhds (∑ _a ∈ S_in, (1 : ℝ) / (B : ℝ) ^ L')) :=
      tendsto_finsetSum S_in fun a ha => hnorm L' a hL'1 (hSin_lt a ha)
    simp_rw [← Finset.sum_div] at hsum
    have hlim : (∑ _a ∈ S_in, (1 : ℝ)) / (B : ℝ) ^ L' = (S_in.card : ℝ) / Q := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]; dsimp only [Q]; rw [Nat.cast_pow]
    rwa [hlim] at hsum
  have ht_out : Tendsto (fun M : ℕ =>
      (∑ a ∈ S_out, (occ B y L' a M : ℝ)) / M) atTop (nhds ((S_out.card : ℝ) / Q)) := by
    have hsum : Tendsto (fun M : ℕ => ∑ a ∈ S_out, (occ B y L' a M : ℝ) / M) atTop
        (nhds (∑ _a ∈ S_out, (1 : ℝ) / (B : ℝ) ^ L')) :=
      tendsto_finsetSum S_out fun a ha => hnorm L' a hL'1 (hSout_lt a ha)
    simp_rw [← Finset.sum_div] at hsum
    have hlim : (∑ _a ∈ S_out, (1 : ℝ)) / (B : ℝ) ^ L' = (S_out.card : ℝ) / Q := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]; dsimp only [Q]; rw [Nat.cast_pow]
    rwa [hlim] at hsum
  obtain ⟨M₁, hM₁⟩ := (Metric.tendsto_atTop.mp ht_in) (ε / 2) (by positivity)
  obtain ⟨M₂, hM₂⟩ := (Metric.tendsto_atTop.mp ht_out) (ε / 2) (by positivity)
  refine ⟨max (max M₁ M₂) 1, fun M hM => ?_⟩
  have hM_ge₁ : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM_ge₂ : M₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMpos : (0 : ℝ) < M := by
    have : 1 ≤ M := le_trans (le_max_right _ _) hM
    positivity
  have hcard_in : ∑ a ∈ S_in, occ B y L' a M ≤
      ((Finset.range M).filter (fun m =>
        c ≤ Int.fract ((B : ℝ) ^ m * y) ∧ Int.fract ((B : ℝ) ^ m * y) < d)).card := by
    have hdisj : (S_in : Set ℕ).PairwiseDisjoint
        (fun a => (Finset.range M).filter (fun m => ⌊(B : ℝ) ^ L' * Int.fract ((B : ℝ) ^ m * y)⌋₊ = a)) := by
      intro a _ a' _ hne
      exact Finset.disjoint_left.mpr fun m hm1 hm2 =>
        hne ((Finset.mem_filter.mp hm1).2.symm.trans (Finset.mem_filter.mp hm2).2)
    unfold occ
    rw [← Finset.card_biUnion hdisj]
    apply Finset.card_le_card
    intro m hm
    obtain ⟨a, ha, hm'⟩ := Finset.mem_biUnion.mp hm
    have ⟨hmM, hfl⟩ := Finset.mem_filter.mp hm'
    have ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
    have hflQ : ⌊(Q : ℝ) * Int.fract ((B : ℝ) ^ m * y)⌋₊ = a := by simpa [Q] using hfl
    have ⟨hlo, hhi⟩ := (floor_mul_fract_eq_iff Q hQpos _ a).mp hflQ
    refine Finset.mem_filter.mpr ⟨hmM, ?_, ?_⟩
    · have : c ≤ (a : ℝ) / Q := by
        rw [le_div_iff₀ hQrpos]
        have : (a₁ : ℝ) + 1 ≤ a := by exact_mod_cast ha1
        linarith
      exact le_trans this hlo
    · have : ((a : ℝ) + 1) / Q ≤ d := by
        rw [div_le_iff₀ hQrpos]
        have : (a : ℝ) + 1 ≤ a₂ := by exact_mod_cast ha2
        linarith
      exact lt_of_lt_of_le hhi this
  have hcard_out : ((Finset.range M).filter (fun m =>
        c ≤ Int.fract ((B : ℝ) ^ m * y) ∧ Int.fract ((B : ℝ) ^ m * y) < d)).card ≤
      ∑ a ∈ S_out, occ B y L' a M := by
    have hdisj : (S_out : Set ℕ).PairwiseDisjoint
        (fun a => (Finset.range M).filter (fun m => ⌊(B : ℝ) ^ L' * Int.fract ((B : ℝ) ^ m * y)⌋₊ = a)) := by
      intro a _ a' _ hne
      exact Finset.disjoint_left.mpr fun m hm1 hm2 =>
        hne ((Finset.mem_filter.mp hm1).2.symm.trans (Finset.mem_filter.mp hm2).2)
    unfold occ
    rw [← Finset.card_biUnion hdisj]
    apply Finset.card_le_card
    intro m hm
    have ⟨hmM, hmc, hmd⟩ := Finset.mem_filter.mp hm
    set a := ⌊(Q : ℝ) * Int.fract ((B : ℝ) ^ m * y)⌋₊
    have haQ : a < Q := floor_mul_fract_lt Q hQpos _
    have ha1 : a₁ ≤ a := Nat.floor_mono (by
      rw [mul_comm c]; exact mul_le_mul_of_nonneg_left hmc hQrpos.le)
    have ha2 : a ≤ a₂ := Nat.floor_mono (by
      rw [mul_comm d]; exact mul_le_mul_of_nonneg_left hmd.le hQrpos.le)
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ha1, by omega⟩, haQ⟩,
      Finset.mem_filter.mpr ⟨hmM, by dsimp only [a, Q]; rw [Nat.cast_pow]⟩⟩
  have hSin_len : d - c - 2 / (B : ℝ) ^ L' ≤ (S_in.card : ℝ) / Q := by
    have hBL : (Q : ℝ) = (B : ℝ) ^ L' := by dsimp only [Q]; rw [Nat.cast_pow]
    rw [← hBL]
    rw [Nat.card_Ico]
    by_cases hle : a₁ + 1 ≤ a₂
    · have hcast : ((a₂ - (a₁ + 1) : ℕ) : ℝ) = (a₂ : ℝ) - (a₁ : ℝ) - 1 := by
        rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]; ring
      rw [hcast]
      have h1 : (d - c) * Q - 2 ≤ (a₂ : ℝ) - (a₁ : ℝ) - 1 := by linarith
      have hdiv : d - c - 2 / (Q : ℝ) = ((d - c) * Q - 2) / Q := by field_simp
      rw [hdiv]
      exact div_le_div_of_nonneg_right h1 hQrpos.le
    · have hsub0 : a₂ - (a₁ + 1) = 0 := by omega
      rw [hsub0, Nat.cast_zero, zero_div]
      have : (a₂ : ℝ) ≤ (a₁ : ℝ) := by exact_mod_cast (show a₂ ≤ a₁ by omega)
      have hdiff : (d - c) * Q < 2 := by linarith
      have : d - c < 2 / (Q : ℝ) := (lt_div_iff₀ hQrpos).mpr hdiff
      linarith
  have hSout_len : (S_out.card : ℝ) / Q ≤ d - c + 2 / (B : ℝ) ^ L' := by
    have hBL : (Q : ℝ) = (B : ℝ) ^ L' := by dsimp only [Q]; rw [Nat.cast_pow]
    rw [← hBL]
    have hcard_le : S_out.card ≤ a₂ + 1 - a₁ := by
      calc S_out.card ≤ (Finset.Ico a₁ (a₂ + 1)).card := Finset.card_filter_le _ _
        _ = a₂ + 1 - a₁ := Nat.card_Ico _ _
    have hcast : ((a₂ + 1 - a₁ : ℕ) : ℝ) = (a₂ : ℝ) + 1 - (a₁ : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hle : (S_out.card : ℝ) ≤ (a₂ : ℝ) + 1 - (a₁ : ℝ) := by
      rw [← hcast]; exact_mod_cast hcard_le
    have hnum : (a₂ : ℝ) + 1 - (a₁ : ℝ) ≤ (d - c) * Q + 2 := by linarith
    have hdiv : d - c + 2 / (Q : ℝ) = ((d - c) * Q + 2) / Q := by field_simp
    rw [hdiv]
    exact div_le_div_of_nonneg_right (le_trans hle hnum) hQrpos.le
  have hinM := hM₁ M hM_ge₁
  have houtM := hM₂ M hM_ge₂
  rw [Real.dist_eq] at hinM houtM ⊢
  have hinM' := abs_lt.mp hinM
  have houtM' := abs_lt.mp houtM
  have hloM : (∑ a ∈ S_in, (occ B y L' a M : ℝ)) / M ≤
      (((Finset.range M).filter (fun m =>
        c ≤ Int.fract ((B : ℝ) ^ m * y) ∧ Int.fract ((B : ℝ) ^ m * y) < d)).card : ℝ) / M := by
    apply div_le_div_of_nonneg_right _ hMpos.le
    exact_mod_cast hcard_in
  have hhiM : (((Finset.range M).filter (fun m =>
        c ≤ Int.fract ((B : ℝ) ^ m * y) ∧ Int.fract ((B : ℝ) ^ m * y) < d)).card : ℝ) / M ≤
      (∑ a ∈ S_out, (occ B y L' a M : ℝ)) / M := by
    apply div_le_div_of_nonneg_right _ hMpos.le
    exact_mod_cast hcard_out
  rw [abs_lt]
  constructor <;> linarith

lemma fract_add_mem_Ico_iff (u α c d : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hc0 : 0 ≤ c) (_hcd : c ≤ d) (hd1 : d ≤ 1) :
    (c ≤ Int.fract (u + α) ∧ Int.fract (u + α) < d) ↔
      (if α ≤ c then c - α ≤ u ∧ u < d - α
       else if d ≤ α then c + 1 - α ≤ u ∧ u < d + 1 - α
       else (0 ≤ u ∧ u < d - α) ∨ (c + 1 - α ≤ u ∧ u < 1)) := by
  have hfr : Int.fract (u + α) = if u + α < 1 then u + α else u + α - 1 := by
    split_ifs with h
    · exact Int.fract_eq_self.mpr ⟨by linarith, h⟩
    · have h1 : u + α = (u + α - 1) + 1 := by ring
      conv_lhs => rw [h1]
      rw [Int.fract_add_one]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [hfr]
  by_cases h1 : α ≤ c
  · simp only [h1, ↓reduceIte]
    by_cases hlt : u + α < 1
    · simp only [hlt, ↓reduceIte]; constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
    · simp only [hlt, ↓reduceIte]; constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
  · by_cases h2 : d ≤ α
    · simp only [h1, h2, ↓reduceIte]
      by_cases hlt : u + α < 1
      · simp only [hlt, ↓reduceIte]; constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
      · simp only [hlt, ↓reduceIte]; constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
    · simp only [h1, h2, ↓reduceIte]
      by_cases hlt : u + α < 1
      · simp only [hlt, ↓reduceIte]
        constructor
        · intro ⟨a, b⟩; left; constructor <;> linarith
        · rintro (⟨a, b⟩ | ⟨a, b⟩) <;> constructor <;> linarith
      · simp only [hlt, ↓reduceIte]
        constructor
        · intro ⟨a, b⟩; right; constructor <;> linarith
        · rintro (⟨a, b⟩ | ⟨a, b⟩) <;> constructor <;> linarith

lemma equidist_rotated_Ico (B : ℕ) (hB : 2 ≤ B) (y α : ℝ)
    (hnorm : ∀ (L a : ℕ), 1 ≤ L → a < B ^ L →
      Tendsto (fun M : ℕ => (occ B y L a M : ℝ) / M) atTop (nhds (1 / (B : ℝ) ^ L)))
    (c d : ℝ) (hc0 : 0 ≤ c) (hcd : c ≤ d) (hd1 : d ≤ 1) :
    Tendsto (fun M : ℕ =>
      (((Finset.range M).filter (fun m =>
        c ≤ Int.fract ((B : ℝ) ^ m * y + α) ∧ Int.fract ((B : ℝ) ^ m * y + α) < d)).card : ℝ) / M)
      atTop (nhds (d - c)) := by
  set α' : ℝ := Int.fract α
  have hα0 : 0 ≤ α' := Int.fract_nonneg α
  have hα1 : α' < 1 := Int.fract_lt_one α
  have hfr_eq : ∀ m : ℕ,
      Int.fract ((B : ℝ) ^ m * y + α) = Int.fract (Int.fract ((B : ℝ) ^ m * y) + α') := by
    intro m
    have : (B : ℝ) ^ m * y + α =
        (Int.fract ((B : ℝ) ^ m * y) + α') + (⌊(B : ℝ) ^ m * y⌋ + ⌊α⌋ : ℤ) := by
      dsimp only [α']; rw [Int.fract, Int.fract]; push_cast; ring
    rw [this, Int.fract_add_intCast]
  simp_rw [hfr_eq]
  by_cases h1 : α' ≤ c
  · have hfilt : ∀ M : ℕ,
        (Finset.range M).filter (fun m =>
          c ≤ Int.fract (Int.fract ((B : ℝ) ^ m * y) + α') ∧
          Int.fract (Int.fract ((B : ℝ) ^ m * y) + α') < d) =
        (Finset.range M).filter (fun m =>
          c - α' ≤ Int.fract ((B : ℝ) ^ m * y) ∧ Int.fract ((B : ℝ) ^ m * y) < d - α') := by
      intro M; ext m; simp only [Finset.mem_filter]
      refine and_congr_right fun _ => ?_
      rw [fract_add_mem_Ico_iff _ _ _ _ (Int.fract_nonneg _) (Int.fract_lt_one _) hα0 hα1 hc0 hcd hd1]
      simp [h1]
    simp_rw [hfilt]
    have ht := equidist_Ico_of_base_normal B hB y hnorm (c - α') (d - α')
      (by linarith) (by linarith) (by linarith)
    simpa [sub_sub_sub_cancel_right] using ht
  · by_cases h2 : d ≤ α'
    · have hfilt : ∀ M : ℕ,
          (Finset.range M).filter (fun m =>
            c ≤ Int.fract (Int.fract ((B : ℝ) ^ m * y) + α') ∧
            Int.fract (Int.fract ((B : ℝ) ^ m * y) + α') < d) =
          (Finset.range M).filter (fun m =>
            c + 1 - α' ≤ Int.fract ((B : ℝ) ^ m * y) ∧
            Int.fract ((B : ℝ) ^ m * y) < d + 1 - α') := by
        intro M; ext m; simp only [Finset.mem_filter]
        refine and_congr_right fun _ => ?_
        rw [fract_add_mem_Ico_iff _ _ _ _ (Int.fract_nonneg _) (Int.fract_lt_one _) hα0 hα1 hc0 hcd hd1]
        simp [h1, h2]
      simp_rw [hfilt]
      have ht := equidist_Ico_of_base_normal B hB y hnorm (c + 1 - α') (d + 1 - α')
        (by linarith) (by linarith) (by linarith)
      have hlen : d + 1 - α' - (c + 1 - α') = d - c := by ring
      rwa [hlen] at ht
    · have hfilt : ∀ M : ℕ,
          ((Finset.range M).filter (fun m =>
            c ≤ Int.fract (Int.fract ((B : ℝ) ^ m * y) + α') ∧
            Int.fract (Int.fract ((B : ℝ) ^ m * y) + α') < d)).card =
          ((Finset.range M).filter (fun m =>
            0 ≤ Int.fract ((B : ℝ) ^ m * y) ∧ Int.fract ((B : ℝ) ^ m * y) < d - α')).card +
          ((Finset.range M).filter (fun m =>
            c + 1 - α' ≤ Int.fract ((B : ℝ) ^ m * y) ∧
            Int.fract ((B : ℝ) ^ m * y) < 1)).card := by
        intro M
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext m; simp only [Finset.mem_filter, Finset.mem_union]
          rw [fract_add_mem_Ico_iff _ _ _ _ (Int.fract_nonneg _) (Int.fract_lt_one _) hα0 hα1 hc0 hcd hd1]
          simp only [h1, h2, ↓reduceIte]
          tauto
        · rw [Finset.disjoint_left]
          intro m hm1 hm2
          have hlt := (Finset.mem_filter.mp hm1).2.2
          have hge := (Finset.mem_filter.mp hm2).2.1
          linarith
      simp_rw [hfilt, Nat.cast_add, add_div]
      have ht1 := equidist_Ico_of_base_normal B hB y hnorm 0 (d - α')
        le_rfl (by linarith) (by linarith)
      have ht2 := equidist_Ico_of_base_normal B hB y hnorm (c + 1 - α') 1
        (by linarith) (by linarith) le_rfl
      have hsum := ht1.add ht2
      have hlen : d - α' - 0 + (1 - (c + 1 - α')) = d - c := by ring
      rwa [hlen] at hsum

/- ### Part 4: Periodic shift for rationals and averaging over residue classes -/

lemma exists_periodic_pow_rat (b : ℕ) (s : ℚ) :
    ∃ i₀ P : ℕ, 1 ≤ P ∧ ∀ m t : ℕ,
      ∃ z : ℤ, (b : ℝ) ^ (i₀ + m * P + t) * (s : ℝ) = (b : ℝ) ^ (i₀ + t) * (s : ℝ) + (z : ℝ) := by
  let q : ℕ := s.den
  have hq : 0 < q := s.pos
  let f : Fin (q + 1) → Fin q := fun i =>
    ⟨((b : ℤ) ^ i.1 * s.num % (q : ℤ)).toNat, by
      have hnn : 0 ≤ (b : ℤ) ^ i.1 * s.num % (q : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast hq.ne')
      have hlt : (b : ℤ) ^ i.1 * s.num % (q : ℤ) < (q : ℤ) :=
        Int.emod_lt_of_pos _ (by exact_mod_cast hq)
      omega⟩
  have hcard : Fintype.card (Fin q) < Fintype.card (Fin (q + 1)) := by simp
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hmod : ∀ u v : ℕ, u < v →
      ((b : ℤ) ^ u * s.num % (q : ℤ)) = ((b : ℤ) ^ v * s.num % (q : ℤ)) →
      ∃ i₀ P : ℕ, 1 ≤ P ∧ ∀ m t : ℕ,
        ∃ z : ℤ, (b : ℝ) ^ (i₀ + m * P + t) * (s : ℝ) =
          (b : ℝ) ^ (i₀ + t) * (s : ℝ) + (z : ℝ) := by
    intro u v huv hcong
    refine ⟨u, v - u, by omega, fun m t => ?_⟩
    have hstep : ∀ n : ℕ,
        ((b : ℤ) ^ (u + n * (v - u)) * s.num) % (q : ℤ) =
          ((b : ℤ) ^ u * s.num) % (q : ℤ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hexp : u + (n + 1) * (v - u) = (v - u) + (u + n * (v - u)) := by ring
        rw [hexp, pow_add, mul_assoc, Int.mul_emod, ih, ← Int.mul_emod, ← mul_assoc, ← pow_add]
        have hexp2 : v - u + u = v := by omega
        rw [hexp2, hcong]
    have hdvd : (q : ℤ) ∣ ((b : ℤ) ^ (u + m * (v - u) + t) * s.num -
        (b : ℤ) ^ (u + t) * s.num) := by
      have h1 : (q : ℤ) ∣ ((b : ℤ) ^ (u + m * (v - u)) * s.num - (b : ℤ) ^ u * s.num) := by
        have hq1 := Int.mul_ediv_add_emod ((b : ℤ) ^ (u + m * (v - u)) * s.num) (q : ℤ)
        have hq2 := Int.mul_ediv_add_emod ((b : ℤ) ^ u * s.num) (q : ℤ)
        refine ⟨((b : ℤ) ^ (u + m * (v - u)) * s.num) / (q : ℤ) -
          ((b : ℤ) ^ u * s.num) / (q : ℤ), ?_⟩
        linarith [hstep m]
      have h2 : (b : ℤ) ^ (u + m * (v - u) + t) * s.num - (b : ℤ) ^ (u + t) * s.num =
          (b : ℤ) ^ t * ((b : ℤ) ^ (u + m * (v - u)) * s.num - (b : ℤ) ^ u * s.num) := by
        rw [pow_add, pow_add]; ring
      rw [h2]
      exact dvd_mul_of_dvd_right h1 _
    obtain ⟨z, hz⟩ := hdvd
    refine ⟨z, ?_⟩
    have hqr : (q : ℝ) ≠ 0 := by positivity
    have hs_eq : (s : ℝ) = (s.num : ℝ) / (q : ℝ) := by
      rw [Rat.cast_def]
    rw [hs_eq]
    have hzr : (b : ℝ) ^ (u + m * (v - u) + t) * (s.num : ℝ) -
        (b : ℝ) ^ (u + t) * (s.num : ℝ) = (q : ℝ) * (z : ℝ) := by
      exact_mod_cast hz
    have hdiv : ((b : ℝ) ^ (u + m * (v - u) + t) * (s.num : ℝ) -
        (b : ℝ) ^ (u + t) * (s.num : ℝ)) / (q : ℝ) = (z : ℝ) := by
      rw [hzr]; field_simp
    linarith [show (b : ℝ) ^ (u + m * (v - u) + t) * ((s.num : ℝ) / (q : ℝ)) -
        (b : ℝ) ^ (u + t) * ((s.num : ℝ) / (q : ℝ)) = (z : ℝ) by
      have : (b : ℝ) ^ (u + m * (v - u) + t) * ((s.num : ℝ) / (q : ℝ)) -
          (b : ℝ) ^ (u + t) * ((s.num : ℝ) / (q : ℝ)) =
          ((b : ℝ) ^ (u + m * (v - u) + t) * (s.num : ℝ) -
            (b : ℝ) ^ (u + t) * (s.num : ℝ)) / (q : ℝ) := by ring
      rw [this, hdiv]]
  have hval : ((b : ℤ) ^ i.1 * s.num % (q : ℤ)) = ((b : ℤ) ^ j.1 * s.num % (q : ℤ)) := by
    have h1 := congrArg Fin.val heq
    dsimp only [f] at h1
    have hnn1 : 0 ≤ (b : ℤ) ^ i.1 * s.num % (q : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    have hnn2 : 0 ≤ (b : ℤ) ^ j.1 * s.num % (q : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    omega
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact hmod i.1 j.1 hlt hval
  · exact hmod j.1 i.1 hgt hval.symm

lemma occ_tendsto_of_isNormalInBase (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hx : IsNormalInBase b x) (L a : ℕ) (ha : a < b ^ L) :
    Tendsto (fun n : ℕ => (occ b x L a n : ℝ) / n) atTop (nhds (1 / (b : ℝ) ^ L)) := by
  have hb0 : 0 < b := by omega
  let w : Fin L → ℕ := fun j => (a / b ^ (L - 1 - j.1)) % b
  have hw : ∀ j : Fin L, w j < b := fun j => Nat.mod_lt _ hb0
  have hnorm := hx L w hw
  have hfilt : ∀ n : ℕ,
      (Finset.range n).filter (fun i => ∀ j : Fin L, digitSeq b x (i + j.1) = w j) =
      (Finset.range n).filter (fun i => ⌊(b : ℝ) ^ L * Int.fract ((b : ℝ) ^ i * x)⌋₊ = a) := by
    intro n; ext i; simp only [Finset.mem_filter]
    exact and_congr_right fun _ => digitSeq_block_iff_floor_eq b L hb0 x i a ha
  unfold occ
  simpa only [hfilt] using hnorm

lemma residue_class_hot_spot (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormalInBase b x)
    (s₀ P : ℕ) (hP : 1 ≤ P) :
    ∀ (L a : ℕ), a < (b ^ P) ^ L → ∀ ε > 0,
      ∀ᶠ M : ℕ in atTop,
        (occ (b ^ P) ((b : ℝ) ^ s₀ * x) L a M : ℝ) / M ≤ (P : ℝ) / ((b ^ P : ℕ) : ℝ) ^ L + ε := by
  intro L a ha ε hε
  have ha' : a < b ^ (P * L) := by rwa [← pow_mul] at ha
  have ht := occ_tendsto_of_isNormalInBase b hb x hx (P * L) a ha'
  have hsub : Tendsto (fun M : ℕ => s₀ + M * P) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun N => ⟨N, fun M hM => by
      calc N ≤ M := hM
        _ = M * 1 := (mul_one M).symm
        _ ≤ M * P := Nat.mul_le_mul_left M hP
        _ ≤ s₀ + M * P := Nat.le_add_left _ _⟩
  have hsubseq : Tendsto (fun M : ℕ => (occ b x (P * L) a (s₀ + M * P) : ℝ) / (s₀ + M * P))
      atTop (nhds (1 / (b : ℝ) ^ (P * L))) := by
    have := ht.comp hsub
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using this
  have hratio : Tendsto (fun M : ℕ => ((s₀ + M * P : ℕ) : ℝ) / M) atTop (nhds (P : ℝ)) := by
    have h0 : Tendsto (fun M : ℕ => (s₀ : ℝ) / M + P) atTop (nhds (0 + P)) :=
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add tendsto_const_nhds
    rw [zero_add] at h0
    refine h0.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    have hMpos : (M : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hprod : Tendsto (fun M : ℕ =>
      ((occ b x (P * L) a (s₀ + M * P) : ℝ) / (s₀ + M * P)) * (((s₀ + M * P : ℕ) : ℝ) / M))
      atTop (nhds ((1 / (b : ℝ) ^ (P * L)) * (P : ℝ))) :=
    hsubseq.mul hratio
  have hlim : (1 / (b : ℝ) ^ (P * L)) * (P : ℝ) = (P : ℝ) / ((b ^ P : ℕ) : ℝ) ^ L := by
    rw [Nat.cast_pow, ← pow_mul]; ring
  rw [hlim] at hprod
  have hev := (Metric.tendsto_atTop.mp hprod) ε hε
  filter_upwards [Filter.eventually_ge_atTop (max hev.choose 1)] with M hM
  have hM0 : hev.choose ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hdist := hev.choose_spec M hM0
  rw [Real.dist_eq] at hdist
  have hcard : occ (b ^ P) ((b : ℝ) ^ s₀ * x) L a M ≤ occ b x (P * L) a (s₀ + M * P) := by
    unfold occ
    have hinj : Function.Injective (fun m : ℕ => s₀ + m * P) := fun m₁ m₂ h =>
      Nat.eq_of_mul_eq_mul_right hP (Nat.add_left_cancel h)
    rw [← Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
    have ⟨hmM, hfl⟩ := Finset.mem_filter.mp hm
    rw [Finset.mem_range] at hmM
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by nlinarith), ?_⟩
    have hpow1 : ((b ^ P : ℕ) : ℝ) ^ L = (b : ℝ) ^ (P * L) := by
      rw [Nat.cast_pow, ← pow_mul]
    have hpow2 : ((b ^ P : ℕ) : ℝ) ^ m * ((b : ℝ) ^ s₀ * x) = (b : ℝ) ^ (s₀ + m * P) * x := by
      rw [Nat.cast_pow, ← pow_mul, pow_add, mul_comm m P]; ring
    rwa [hpow1, hpow2] at hfl
  have hMpos : (0 : ℝ) < M := by positivity
  have hden_pos : (0 : ℝ) < ((s₀ + M * P : ℕ) : ℝ) := by positivity
  have hle1 : (occ (b ^ P) ((b : ℝ) ^ s₀ * x) L a M : ℝ) / M ≤
      ((occ b x (P * L) a (s₀ + M * P) : ℝ) / (s₀ + M * P)) * (((s₀ + M * P : ℕ) : ℝ) / M) := by
    have hsimp : ((occ b x (P * L) a (s₀ + M * P) : ℝ) / ((s₀ + M * P : ℕ) : ℝ)) *
        (((s₀ + M * P : ℕ) : ℝ) / M) = (occ b x (P * L) a (s₀ + M * P) : ℝ) / M := by
      field_simp
    have hcast : ((s₀ + M * P : ℕ) : ℝ) = (s₀ : ℝ) + (M : ℝ) * (P : ℝ) := by push_cast; ring
    rw [← hcast, hsimp]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hMpos.le
  have hle2 := (abs_lt.mp hdist).2
  linarith

lemma tendsto_avg_residue_classes (f : ℕ → Prop) [DecidablePred f]
    (i₀ P : ℕ) (hP : 1 ≤ P) (L : ℝ)
    (hres : ∀ t : ℕ, t < P →
      Tendsto (fun M : ℕ =>
        (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ) / M)
        atTop (nhds L)) :
    Tendsto (fun n : ℕ => (((Finset.range n).filter f).card : ℝ) / n) atTop (nhds L) := by
  have hPpos : (0 : ℝ) < P := by positivity
  have hdiv : Tendsto (fun n : ℕ => (n - i₀) / P) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro M
    refine ⟨i₀ + M * P, fun n hn => ?_⟩
    rw [Nat.le_div_iff_mul_le hP]
    omega
  have hterm : ∀ t ∈ Finset.range P,
      Tendsto (fun n : ℕ =>
        (((Finset.range ((n - i₀) / P)).filter (fun m => f (i₀ + m * P + t))).card : ℝ) / n)
        atTop (nhds (L / P)) := by
    intro t ht
    have htP : t < P := Finset.mem_range.mp ht
    have h1 := (hres t htP).comp hdiv
    have h2 : Tendsto (fun n : ℕ => (((n - i₀) / P : ℕ) : ℝ) / n) atTop (nhds (1 / (P : ℝ))) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt ((i₀ + P : ℝ) / (P * ε))
      refine ⟨max N (i₀ + P), fun n hn => ?_⟩
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hniP : i₀ + P ≤ n := le_trans (le_max_right _ _) hn
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hdm : ((n - i₀) / P) * P ≤ n - i₀ := Nat.div_mul_le_self _ _
      have hdm2 : n - i₀ < ((n - i₀) / P + 1) * P := by
        have := Nat.div_add_mod (n - i₀) P
        have := Nat.mod_lt (n - i₀) hP
        nlinarith
      have hdmr : (((n - i₀) / P : ℕ) : ℝ) * P ≤ (n : ℝ) - i₀ := by
        have : ((n - i₀) / P) * P + i₀ ≤ n := by omega
        have : (((n - i₀) / P : ℕ) : ℝ) * P + i₀ ≤ n := by exact_mod_cast this
        linarith
      have hdmr2 : (n : ℝ) - i₀ < ((((n - i₀) / P : ℕ) : ℝ) + 1) * P := by
        have : n < ((n - i₀) / P + 1) * P + i₀ := by omega
        have : (n : ℝ) < ((((n - i₀) / P : ℕ) : ℝ) + 1) * P + i₀ := by exact_mod_cast this
        linarith
      rw [Real.dist_eq]
      have hdiff : (((n - i₀) / P : ℕ) : ℝ) / n - 1 / P =
          ((((n - i₀) / P : ℕ) : ℝ) * P - n) / (n * P) := by field_simp
      rw [hdiff, abs_div, abs_of_pos (mul_pos hnpos hPpos)]
      have habs : |(((n - i₀) / P : ℕ) : ℝ) * P - n| ≤ (i₀ : ℝ) + P := by
        rw [abs_le]; constructor <;> linarith
      have hbound : ((i₀ : ℝ) + P) / (n * P) < ε := by
        rw [div_lt_iff₀ (mul_pos hnpos hPpos)]
        have hgt : (i₀ + P : ℝ) / (P * ε) < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
        have := (div_lt_iff₀ (mul_pos hPpos hε)).mp hgt
        nlinarith
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right habs (mul_pos hnpos hPpos).le) hbound
    have hprod := h1.mul h2
    have hlim : L * (1 / (P : ℝ)) = L / P := by ring
    rw [hlim] at hprod
    refine hprod.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (i₀ + P)] with n hn
    have hqpos : 0 < (n - i₀) / P := Nat.div_pos (by omega) hP
    have hqr : (((n - i₀) / P : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp only [Function.comp_apply]
    field_simp
  have hsum : Tendsto (fun n : ℕ =>
      (∑ t ∈ Finset.range P,
        (((Finset.range ((n - i₀) / P)).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) / n)
      atTop (nhds L) := by
    have h := tendsto_finsetSum (Finset.range P) hterm
    simp_rw [← Finset.sum_div] at h
    have hlim : (∑ _t ∈ Finset.range P, L) / (P : ℝ) = L := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rwa [hlim] at h
  rw [Metric.tendsto_atTop] at hsum ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hsum (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((i₀ + P : ℝ) / (ε / 2))
  refine ⟨max (max N₁ N₂) (i₀ + P), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hniP : i₀ + P ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  set M := (n - i₀) / P
  have hdisj : (Finset.range P : Set ℕ).PairwiseDisjoint
      (fun t => ((Finset.range M).filter (fun m => f (i₀ + m * P + t))).image
        (fun m => i₀ + m * P + t)) := by
    intro t₁ ht₁ t₂ ht₂ hne
    exact Finset.disjoint_left.mpr fun x hx1 hx2 => by
      obtain ⟨m₁, _, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨m₂, _, hEq⟩ := Finset.mem_image.mp hx2
      have ht1 : t₁ < P := Finset.mem_range.mp ht₁
      have ht2 : t₂ < P := Finset.mem_range.mp ht₂
      have hmod := congrArg (· % P) (show m₁ * P + t₁ = m₂ * P + t₂ by omega)
      rw [Nat.mul_add_mod', Nat.mul_add_mod', Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt ht2] at hmod
      exact hne hmod
  have hcard_eq : ∑ t ∈ Finset.range P,
        ((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card =
      ((Finset.range P).biUnion (fun t =>
        ((Finset.range M).filter (fun m => f (i₀ + m * P + t))).image
          (fun m => i₀ + m * P + t))).card := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.card_image_of_injective _ (fun m₁ m₂ h => by
      have : m₁ * P = m₂ * P := by omega
      exact Nat.eq_of_mul_eq_mul_right hP this)]
  have hsub1 : (Finset.range P).biUnion (fun t =>
      ((Finset.range M).filter (fun m => f (i₀ + m * P + t))).image (fun m => i₀ + m * P + t)) ⊆
      (Finset.range n).filter f := by
    intro x hx
    obtain ⟨t, ht, hx'⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx'
    have ⟨hmM, hfm⟩ := Finset.mem_filter.mp hm
    have htP : t < P := Finset.mem_range.mp ht
    have hmM' : m < M := Finset.mem_range.mp hmM
    have hMP : M * P ≤ n - i₀ := Nat.div_mul_le_self _ _
    have hlt : i₀ + m * P + t < n := by
      have : m * P + t < M * P := by nlinarith
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hfm⟩
  have hsub2 : (Finset.range n).filter f ⊆
      ((Finset.range P).biUnion (fun t =>
        ((Finset.range M).filter (fun m => f (i₀ + m * P + t))).image (fun m => i₀ + m * P + t))) ∪
      (Finset.range i₀ ∪ Finset.Ico (i₀ + M * P) n) := by
    intro x hx
    have ⟨hxn, hfx⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_range] at hxn
    by_cases hxi : x < i₀
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_range.mpr hxi))
    · by_cases hxM : x < i₀ + M * P
      · refine Finset.mem_union_left _ ?_
        let m := (x - i₀) / P
        let t := (x - i₀) % P
        have htP : t < P := Nat.mod_lt _ hP
        have hx_eq : i₀ + m * P + t = x := by
          have hdm : P * m + t = x - i₀ := Nat.div_add_mod (x - i₀) P
          rw [mul_comm] at hdm
          omega
        have hmM : m < M := by
          dsimp only [m]
          rw [Nat.div_lt_iff_lt_mul hP]
          omega
        refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr htP,
          Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmM, ?_⟩, hx_eq⟩⟩
        rwa [hx_eq]
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hxn⟩))
  have hle_lo : ∑ t ∈ Finset.range P,
      ((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card ≤
      ((Finset.range n).filter f).card := by
    rw [hcard_eq]; exact Finset.card_le_card hsub1
  have hle_hi : ((Finset.range n).filter f).card ≤
      (∑ t ∈ Finset.range P,
        ((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card) + (i₀ + P) := by
    rw [hcard_eq]
    have hrem : n - (i₀ + M * P) ≤ P := by
      have h1 : P * M + (n - i₀) % P = n - i₀ := Nat.div_add_mod (n - i₀) P
      have h2 : (n - i₀) % P < P := Nat.mod_lt (n - i₀) hP
      rw [mul_comm] at h1
      omega
    calc ((Finset.range n).filter f).card
        ≤ _ := Finset.card_le_card hsub2
      _ ≤ _ + (Finset.range i₀ ∪ Finset.Ico (i₀ + M * P) n).card := Finset.card_union_le _ _
      _ ≤ _ + ((Finset.range i₀).card + (Finset.Ico (i₀ + M * P) n).card) := by
          gcongr; exact Finset.card_union_le _ _
      _ ≤ _ + (i₀ + P) := by
          rw [Finset.card_range, Nat.card_Ico]; omega
  have hdiff_le : |(((Finset.range n).filter f).card : ℝ) / n -
      (∑ t ∈ Finset.range P,
        (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) / n| ≤
      ((i₀ : ℝ) + P) / n := by
    have h1 : (∑ t ∈ Finset.range P,
        (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) ≤
        (((Finset.range n).filter f).card : ℝ) := by exact_mod_cast hle_lo
    have h2 : (((Finset.range n).filter f).card : ℝ) ≤
        (∑ t ∈ Finset.range P,
          (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) +
          ((i₀ : ℝ) + P) := by exact_mod_cast hle_hi
    rw [← sub_div, abs_div, abs_of_pos hnpos]
    apply div_le_div_of_nonneg_right _ hnpos.le
    rw [abs_le]; constructor <;> linarith
  have herr : ((i₀ : ℝ) + P) / n < ε / 2 := by
    rw [div_lt_iff₀ hnpos]
    have hgt : ((i₀ : ℝ) + P) / (ε / 2) < n := lt_of_lt_of_le hN₂ (by exact_mod_cast hn2)
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε / 2)).mp hgt
    linarith
  have hsum_n := hN₁ n hn1
  rw [Real.dist_eq] at hsum_n ⊢
  have htri : |(((Finset.range n).filter f).card : ℝ) / n - L| ≤
      |(((Finset.range n).filter f).card : ℝ) / n -
        (∑ t ∈ Finset.range P,
          (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) / n| +
      |(∑ t ∈ Finset.range P,
          (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) / n - L| := by
    have : (((Finset.range n).filter f).card : ℝ) / n - L =
        ((((Finset.range n).filter f).card : ℝ) / n -
          (∑ t ∈ Finset.range P,
            (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) / n) +
        ((∑ t ∈ Finset.range P,
            (((Finset.range M).filter (fun m => f (i₀ + m * P + t))).card : ℝ)) / n - L) := by ring
    rw [this]
    exact abs_add_le _ _
  linarith

end WallRationalShift

theorem OMA.solution :
    OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1.H1 := by
  intro b hb x s hx k w hw
  have hb0 : 0 < b := by omega
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hfilt : ∀ n : ℕ,
        (Finset.range n).filter (fun i => ∀ j : Fin 0, digitSeq b (x + (s : ℝ)) (i + j.1) = w j) =
        Finset.range n := fun n => by
      ext i; simp
    simp only [hfilt, Finset.card_range, pow_zero, div_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    exact (div_self this).symm
  · obtain ⟨a, ha, hwa⟩ := WallRationalShift.exists_code_of_word b hb0 k w hw
    have hiff : ∀ i : ℕ,
        (∀ j : Fin k, digitSeq b (x + (s : ℝ)) (i + j.1) = w j) ↔
        ((a : ℝ) / (b : ℝ) ^ k ≤ Int.fract ((b : ℝ) ^ i * (x + (s : ℝ))) ∧
          Int.fract ((b : ℝ) ^ i * (x + (s : ℝ))) < ((a : ℝ) + 1) / (b : ℝ) ^ k) := by
      intro i
      have h1 : (∀ j : Fin k, digitSeq b (x + (s : ℝ)) (i + j.1) = w j) ↔
          (∀ j : Fin k, digitSeq b (x + (s : ℝ)) (i + j.1) = (a / b ^ (k - 1 - j.1)) % b) :=
        forall_congr' fun j => by rw [hwa j]
      rw [h1, WallRationalShift.digitSeq_block_iff_floor_eq b k hb0 (x + (s : ℝ)) i a ha]
      have h2 := WallRationalShift.floor_mul_fract_eq_iff (b ^ k) (pow_pos hb0 k)
        ((b : ℝ) ^ i * (x + (s : ℝ))) a
      simpa [Nat.cast_pow] using h2
    have hfilt : ∀ n : ℕ,
        ((Finset.range n).filter (fun i =>
          ∀ j : Fin k, digitSeq b (x + (s : ℝ)) (i + j.1) = w j)).card =
        ((Finset.range n).filter (fun i =>
          (a : ℝ) / (b : ℝ) ^ k ≤ Int.fract ((b : ℝ) ^ i * (x + (s : ℝ))) ∧
          Int.fract ((b : ℝ) ^ i * (x + (s : ℝ))) < ((a : ℝ) + 1) / (b : ℝ) ^ k)).card := by
      intro n; congr 1; ext i; simp only [Finset.mem_filter]
      exact and_congr_right fun _ => hiff i
    simp_rw [hfilt]
    obtain ⟨i₀, P, hP, hper⟩ := WallRationalShift.exists_periodic_pow_rat b s
    let B : ℕ := b ^ P
    have hB : 2 ≤ B := le_trans hb (Nat.le_self_pow (by omega) b)
    have hca : (0 : ℝ) ≤ (a : ℝ) / (b : ℝ) ^ k := by positivity
    have hcd : (a : ℝ) / (b : ℝ) ^ k ≤ ((a : ℝ) + 1) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hd1 : ((a : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : a + 1 ≤ b ^ k := ha
      exact_mod_cast this
    have hlen : ((a : ℝ) + 1) / (b : ℝ) ^ k - (a : ℝ) / (b : ℝ) ^ k = 1 / (b : ℝ) ^ k := by ring
    rw [← hlen]
    classical
    apply WallRationalShift.tendsto_avg_residue_classes _ i₀ P hP _
    intro t _
    have hnorm_t : ∀ (L c : ℕ), 1 ≤ L → c < B ^ L →
        Tendsto (fun M : ℕ =>
          (WallRationalShift.occ B ((b : ℝ) ^ (i₀ + t) * x) L c M : ℝ) / M)
          atTop (nhds (1 / (B : ℝ) ^ L)) :=
      WallRationalShift.pyatetskii_shapiro B hB ((b : ℝ) ^ (i₀ + t) * x) (P : ℝ) (by positivity)
        (WallRationalShift.residue_class_hot_spot b hb x hx (i₀ + t) P hP)
    have hrot := WallRationalShift.equidist_rotated_Ico B hB
      ((b : ℝ) ^ (i₀ + t) * x) ((b : ℝ) ^ (i₀ + t) * (s : ℝ)) hnorm_t
      ((a : ℝ) / (b : ℝ) ^ k) (((a : ℝ) + 1) / (b : ℝ) ^ k) hca hcd hd1
    have heq_fr : ∀ m : ℕ,
        Int.fract ((b : ℝ) ^ (i₀ + m * P + t) * (x + (s : ℝ))) =
        Int.fract ((B : ℝ) ^ m * ((b : ℝ) ^ (i₀ + t) * x) + (b : ℝ) ^ (i₀ + t) * (s : ℝ)) := by
      intro m
      obtain ⟨z, hz⟩ := hper m t
      have hx_pow : (b : ℝ) ^ (i₀ + m * P + t) * x = (B : ℝ) ^ m * ((b : ℝ) ^ (i₀ + t) * x) := by
        dsimp only [B]; rw [Nat.cast_pow, ← pow_mul, pow_add, pow_add, pow_add, mul_comm P m]; ring
      have htot : (b : ℝ) ^ (i₀ + m * P + t) * (x + (s : ℝ)) =
          ((B : ℝ) ^ m * ((b : ℝ) ^ (i₀ + t) * x) + (b : ℝ) ^ (i₀ + t) * (s : ℝ)) + (z : ℝ) := by
        rw [mul_add, hx_pow, hz]; ring
      rw [htot, Int.fract_add_intCast]
    simpa only [heq_fr] using hrot
