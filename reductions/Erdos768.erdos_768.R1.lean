import FormalConjectures.ErdosProblems.«768»

-- Reduction Erdos768.erdos_768.R1 of Erdős Problem 768
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- The hypotheses are the three inputs of the argument in Eric Li, The Sylow Divisor Condition (arXiv:2606.24872,
-- an unrefereed preprint): the prime number theorem in logarithmic intervals, the lower bound and the upper bound.
-- Lean source of that argument: github.com/ericlisg/erdos768-lean (commit e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9, Apache-2.0).
-- The main theorem here only passes from the two bounds to the density statement.

open scoped Classical
open Filter Asymptotics

namespace OMA.R_Erdos768_erdos_768_R1

/-- The prime number theorem in logarithmic intervals (Lemma 2.8 of the paper). -/
def H1 : Prop :=
  ∀ u δ : ℕ → ℝ, Tendsto u atTop atTop → (∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) →
    Tendsto (fun n : ℕ =>
      (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter
        (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ) /
      ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n))) atTop (nhds 1)

/-- The lower bound, given Lemma 2.8. -/
def H2 : Prop :=
  (∀ u δ : ℕ → ℝ, Tendsto u atTop atTop → (∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) →
    Tendsto (fun n : ℕ =>
      (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter
        (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ) /
      ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n))) atTop (nhds 1)) →
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    x * Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) + ε) *
        (Real.sqrt (Real.log x) * Real.log (Real.log x))) ≤
      (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ =>
        ∀ p : ℕ, p.Prime → p ∣ n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1)).card : ℝ)

/-- The upper bound. -/
def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ =>
        ∀ p : ℕ, p.Prime → p ∣ n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1)).card : ℝ) ≤
      x * Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) - ε) *
        (Real.sqrt (Real.log x) * Real.log (Real.log x)))

lemma count_eq (N : ℕ) :
    (Erdos768.erdos768Count N : ℝ) =
      (((Finset.Icc 1 ⌊(N : ℝ)⌋₊).filter (fun n : ℕ =>
        ∀ p : ℕ, p.Prime → p ∣ n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1)).card : ℝ) := by
  rw [Nat.floor_natCast]
  unfold Erdos768.erdos768Count
  congr 2

lemma bound_lim (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) + ε) * Erdos768.erdos768Scale N) ≤
        Erdos768.erdos768Density N)
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Erdos768.erdos768Density N ≤
        Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) - ε) * Erdos768.erdos768Scale N)) :
    Tendsto (fun N : ℕ => -Real.log (Erdos768.erdos768Density N) / Erdos768.erdos768Scale N)
      atTop (nhds (1 / (2 * Real.sqrt (Real.log 2)))) := by
  set c := 1 / (2 * Real.sqrt (Real.log 2)) with hc
  have hS : ∀ᶠ N : ℕ in atTop, 0 < Erdos768.erdos768Scale N := by
    have h1 : ∀ᶠ N : ℕ in atTop, Real.exp 1 < (N : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    filter_upwards [h1] with N hN
    have h0 : 0 < (N : ℝ) := lt_trans (Real.exp_pos 1) hN
    have hl : 1 < Real.log (N : ℝ) := by
      rw [Real.lt_log_iff_exp_lt h0]; exact hN
    unfold Erdos768.erdos768Scale
    exact mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos hl)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [hS, hlow _ hε2, hup _ hε2] with N hSN hl hu
  have hdpos : 0 < Erdos768.erdos768Density N := lt_of_lt_of_le (Real.exp_pos _) hl
  have h1 := Real.log_le_log (Real.exp_pos _) hl
  have h2 := Real.log_le_log hdpos hu
  rw [Real.log_exp] at h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hSN]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hSN]; nlinarith

theorem main : H1 → H2 → H3 → type_of% @Erdos768.erdos_768 := by
  intro h1 h2 h3
  have hl := h2 h1
  have hc : 0 < 1 / (2 * Real.sqrt (Real.log 2)) :=
    by have := Real.log_pos (one_lt_two : (1 : ℝ) < 2); positivity
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) :=
    (eventually_gt_atTop 0).mono fun N h => by exact_mod_cast h
  have hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) + ε) * Erdos768.erdos768Scale N) ≤
        Erdos768.erdos768Density N := by
    intro ε hε
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (hl ε hε), hpos] with N hN hN0
    unfold Erdos768.erdos768Density Erdos768.erdos768Scale
    rw [count_eq, le_div_iff₀ hN0]
    linarith [hN, mul_comm (Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) + ε) *
        (Real.sqrt (Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ))))) (N : ℝ)]
  have hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Erdos768.erdos768Density N ≤
        Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) - ε) * Erdos768.erdos768Scale N) := by
    intro ε hε
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (h3 ε hε), hpos] with N hN hN0
    unfold Erdos768.erdos768Density Erdos768.erdos768Scale
    rw [count_eq, div_le_iff₀ hN0]
    linarith [hN, mul_comm (Real.exp (-(1 / (2 * Real.sqrt (Real.log 2)) - ε) *
        (Real.sqrt (Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ))))) (N : ℝ)]
  have hlim := bound_lim hlow hup
  refine ⟨1 / (2 * Real.sqrt (Real.log 2)), hc,
    fun N => -Real.log (Erdos768.erdos768Density N) / Erdos768.erdos768Scale N -
      1 / (2 * Real.sqrt (Real.log 2)), ?_, ?_⟩
  · rw [Asymptotics.isLittleO_one_iff]
    exact (tendsto_sub_nhds_zero_iff).2 hlim
  · have hS : ∀ᶠ N : ℕ in atTop, 0 < Erdos768.erdos768Scale N := by
      have h1 : ∀ᶠ N : ℕ in atTop, Real.exp 1 < (N : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
      filter_upwards [h1] with N hN
      have h0 : 0 < (N : ℝ) := lt_trans (Real.exp_pos 1) hN
      have hl : 1 < Real.log (N : ℝ) := by
        rw [Real.lt_log_iff_exp_lt h0]; exact hN
      unfold Erdos768.erdos768Scale
      exact mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos hl)
    filter_upwards [hS, hlow 1 one_pos] with N hSN hN
    have hdpos : 0 < Erdos768.erdos768Density N := lt_of_lt_of_le (Real.exp_pos _) hN
    have : -(1 / (2 * Real.sqrt (Real.log 2)) +
        (-Real.log (Erdos768.erdos768Density N) / Erdos768.erdos768Scale N -
          1 / (2 * Real.sqrt (Real.log 2)))) * Erdos768.erdos768Scale N =
        Real.log (Erdos768.erdos768Density N) := by
      field_simp
      ring
    rw [this, Real.exp_log hdpos]

end OMA.R_Erdos768_erdos_768_R1
