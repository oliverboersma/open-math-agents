import FormalConjectures.ErdosProblems.«1162»

-- Reduction Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1 of Erdős Problem 1162 — roney dougal tracey
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The asymptotic `log₂ f(n) ∼ n²/16` of Roney-Dougal and Tracey splits into its two halves.

* `H1` (the lower bound, elementary): with `k = ⌊n/2⌋` disjoint transpositions, `S_n` contains an
  elementary abelian 2-group `(ℤ/2)^k`, and the graphs of the linear maps `𝔽₂^a → 𝔽₂^b`
  (`a = ⌊k/2⌋`, `b = k - a`) give `2^(a·b)` distinct subgroups of it; `a·b ≥ n²/16 - n/2`.
* `H2` (the upper bound, the real content of [RoTr25]): `log₂ f(n) ≤ (1/16 + ε) n²` for large `n`.

`main` only does the asymptotic bookkeeping.
-/

open Filter Asymptotics

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1

/-- Lower bound: `S_n` has at least `2^(a·b)` subgroups, where `a = ⌊⌊n/2⌋/2⌋` and
`b = ⌊n/2⌋ - a`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ^ ((n / 2 / 2) * (n / 2 - n / 2 / 2)) ≤ Erdos1162.f n

/-- Upper bound (Roney-Dougal and Tracey 2025): for every `ε > 0`,
`log₂ f(n) ≤ (1/16 + ε) n²` for all large `n`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    Real.logb 2 (Erdos1162.f n : ℝ) ≤ (1 / 16 + ε) * (n : ℝ) ^ 2

lemma sq_le_ab (n : ℕ) : n ^ 2 ≤ 16 * ((n / 2 / 2) * (n / 2 - n / 2 / 2)) + 8 * n := by
  have h4 : n / 2 / 2 = n / 4 := by rw [Nat.div_div_eq_div_mul]
  have hb : n / 4 ≤ n / 2 - n / 4 := by omega
  rw [h4]
  have hn : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hab : (n / 4) * (n / 4) ≤ (n / 4) * (n / 2 - n / 4) := Nat.mul_le_mul_left _ hb
  set q := n / 4
  set r := n % 4
  have hr2 : r * r ≤ 3 * r := Nat.mul_le_mul_right _ (by omega)
  have hqr : q * r ≤ 3 * q := by
    have : r ≤ 3 := by omega
    calc q * r ≤ q * 3 := Nat.mul_le_mul_left _ this
      _ = 3 * q := by ring
  have key : n ^ 2 ≤ 16 * (q * q) + 8 * n := by
    rw [hn]
    ring_nf
    nlinarith
  calc n ^ 2 ≤ 16 * (q * q) + 8 * n := key
    _ ≤ 16 * (q * (n / 2 - q)) + 8 * n := by
        have := Nat.mul_le_mul_left 16 hab
        omega

theorem main : H1 → H2 → type_of% @Erdos1162.erdos_1162.variants.roney_dougal_tracey := by
  intro h1 h2
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  have hup := h2 (c / 16) (by positivity)
  filter_upwards [hup, eventually_ge_atTop ⌈8 / c⌉₊] with n hn hnc
  set m := (n / 2 / 2) * (n / 2 - n / 2 / 2) with hm
  have hpow : ((2 : ℝ) ^ (m : ℝ)) ≤ (Erdos1162.f n : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast h1 n
  have hlow : (m : ℝ) ≤ Real.logb 2 (Erdos1162.f n : ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast Erdos1162.f_pos n)).mpr hpow
  have hsq : ((n : ℝ) ^ 2) ≤ 16 * (m : ℝ) + 8 * n := by exact_mod_cast sq_le_ab n
  have hn8 : 8 / c ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnc)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h8 : 8 * (n : ℝ) ≤ c * (n : ℝ) ^ 2 := by
    have : 8 ≤ c * n := by
      rw [div_le_iff₀ hc] at hn8
      linarith
    nlinarith
  simp only [Pi.sub_apply]
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 16), Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1
