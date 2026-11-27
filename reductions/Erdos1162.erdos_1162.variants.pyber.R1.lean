import FormalConjectures.ErdosProblems.«1162»

-- Reduction Erdos1162.erdos_1162.variants.pyber.R1 of Erdős Problem 1162 — pyber
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Pyber's theorem `log f(n) ≍ n²` splits into its two halves.

* `H1` (the lower bound, elementary): with `k = ⌊n/2⌋` disjoint transpositions, `S_n` contains an
  elementary abelian 2-group `(ℤ/2)^k`, and the graphs of the linear maps `𝔽₂^a → 𝔽₂^b`
  (`a = ⌊k/2⌋`, `b = k - a`) give `2^(a·b)` distinct subgroups of it.
* `H2` (the upper bound, the real content of [Py93]): `log f(n) = O(n²)`.

`main` only does the asymptotic bookkeeping.
-/

open Filter Asymptotics

namespace OMA.R_Erdos1162_erdos_1162_variants_pyber_R1

/-- Lower bound: `S_n` has at least `2^(a·b)` subgroups, where `a = ⌊⌊n/2⌋/2⌋` and
`b = ⌊n/2⌋ - a`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ^ ((n / 2 / 2) * (n / 2 - n / 2 / 2)) ≤ Erdos1162.f n

/-- Upper bound (Pyber 1993): `log f(n) ≤ C n²` for all large `n`. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, Real.log (Erdos1162.f n : ℝ) ≤ C * (n : ℝ) ^ 2

lemma log_f_nonneg (n : ℕ) : 0 ≤ Real.log (Erdos1162.f n : ℝ) :=
  Real.log_nonneg (by exact_mod_cast Erdos1162.f_pos n)

lemma sq_le_ab (n : ℕ) (hn : 8 ≤ n) : n ^ 2 ≤ 64 * ((n / 2 / 2) * (n / 2 - n / 2 / 2)) := by
  have h4 : n / 2 / 2 = n / 4 := by rw [Nat.div_div_eq_div_mul]
  have hb : n / 4 ≤ n / 2 - n / 4 := by omega
  have ha : n ≤ 8 * (n / 4) := by omega
  rw [h4]
  calc n ^ 2 = n * n := by ring
    _ ≤ (8 * (n / 4)) * (8 * (n / 4)) := Nat.mul_le_mul ha ha
    _ = 64 * ((n / 4) * (n / 4)) := by ring
    _ ≤ 64 * ((n / 4) * (n / 2 - n / 4)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)

theorem main : H1 → H2 → type_of% @Erdos1162.erdos_1162.variants.pyber := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2
  refine ⟨?_, ?_⟩
  · refine IsBigO.of_bound C ?_
    filter_upwards [hC] with n hn
    rw [Real.norm_of_nonneg (log_f_nonneg n), Real.norm_of_nonneg (by positivity)]
    exact hn
  · refine IsBigO.of_bound (64 / Real.log 2) ?_
    filter_upwards [eventually_ge_atTop 8] with n hn
    rw [Real.norm_of_nonneg (log_f_nonneg n), Real.norm_of_nonneg (by positivity)]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set m := (n / 2 / 2) * (n / 2 - n / 2 / 2) with hm
    have hpow : ((2 : ℝ) ^ m) ≤ (Erdos1162.f n : ℝ) := by exact_mod_cast h1 n
    have hlog : (m : ℝ) * Real.log 2 ≤ Real.log (Erdos1162.f n : ℝ) := by
      have := Real.log_le_log (by positivity) hpow
      rwa [Real.log_pow] at this
    have hsq : ((n : ℝ) ^ 2) ≤ 64 * (m : ℝ) := by exact_mod_cast sq_le_ab n hn
    calc (n : ℝ) ^ 2 ≤ 64 * (m : ℝ) := hsq
      _ = 64 / Real.log 2 * ((m : ℝ) * Real.log 2) := by field_simp
      _ ≤ 64 / Real.log 2 * Real.log (Erdos1162.f n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)

end OMA.R_Erdos1162_erdos_1162_variants_pyber_R1
