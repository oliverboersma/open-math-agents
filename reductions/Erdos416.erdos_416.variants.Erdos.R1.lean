import FormalConjectures.ErdosProblems.«416»

-- Reduction Erdos416.erdos_416.variants.Erdos.R1 of Erdős Problem 416 — Erdos
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Erdős's theorem `V(x) = x (log x)^(-1 + o(1))` splits into its two halves.

* `H1` (the lower bound, elementary): `V(x) ≥ π(x)` because `φ(p) = p - 1`, and Chebyshev's bound
  `π(x) ≫ x / log x` gives `V(x) ≥ x (log x)^(-1-ε)` for large `x`.
* `H2` (the upper bound, the real content of Erdős 1935): `V(x) ≤ x (log x)^(-1+ε)` for large `x`.

`main` takes `f(x) = log_{log x}(V(x)/x) + 1`, which makes the identity exact, and reads `f = o(1)`
off the two bounds.
-/

open Filter Asymptotics

namespace OMA.R_Erdos416_erdos_416_variants_Erdos_R1

/-- Lower bound: for every `ε > 0`, `V(x) ≥ x (log x)^(-1-ε)` for all large `x`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x * Real.log x ^ (-1 - ε) ≤ Erdos416.V x

/-- Upper bound (Erdős 1935): for every `ε > 0`, `V(x) ≤ x (log x)^(-1+ε)` for all large `x`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, Erdos416.V x ≤ x * Real.log x ^ (-1 + ε)

theorem main : H1 → H2 → type_of% @Erdos416.erdos_416.variants.Erdos := by
  intro h1 h2
  -- eventually `log x > 1`, `x > 0` and `V x > 0`
  have hlog : ∀ᶠ x : ℝ in atTop, 1 < Real.log x := by
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos 1])]
    exact hx
  have hbase : ∀ᶠ x : ℝ in atTop, 1 < Real.log x ∧ 0 < x ∧ 0 < Erdos416.V x / x := by
    filter_upwards [hlog, h1 1 one_pos, eventually_gt_atTop 0] with x hl hv hx
    refine ⟨hl, hx, div_pos (lt_of_lt_of_le ?_ hv) hx⟩
    exact mul_pos hx (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨fun x => Real.logb (Real.log x) (Erdos416.V x / x) + 1, ?_, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    filter_upwards [hbase, h1 c hc, h2 c hc] with x ⟨hl, hx, hv⟩ hlo hhi
    simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs, abs_le]
    have hb : 1 < Real.log x := hl
    constructor
    · -- `V/x ≥ (log x)^(-1-c)`
      have : (Real.log x) ^ (-1 - c) ≤ Erdos416.V x / x := by
        rw [le_div_iff₀ hx]; linarith [mul_comm x (Real.log x ^ (-1 - c))]
      have := (Real.logb_le_logb hb (Real.rpow_pos_of_pos (by linarith) _) hv).mpr this
      rw [Real.logb_rpow (by linarith) (by linarith)] at this
      linarith
    · have : Erdos416.V x / x ≤ (Real.log x) ^ (-1 + c) := by
        rw [div_le_iff₀ hx]; linarith [mul_comm x (Real.log x ^ (-1 + c))]
      have := (Real.logb_le_logb hb hv (Real.rpow_pos_of_pos (by linarith) _)).mpr this
      rw [Real.logb_rpow (by linarith) (by linarith)] at this
      linarith
  · filter_upwards [hbase] with x ⟨hl, hx, hv⟩
    have : -1 + (Real.logb (Real.log x) (Erdos416.V x / x) + 1) =
        Real.logb (Real.log x) (Erdos416.V x / x) := by ring
    rw [this, Real.rpow_logb (by linarith) (by linarith) hv]
    field_simp

end OMA.R_Erdos416_erdos_416_variants_Erdos_R1
