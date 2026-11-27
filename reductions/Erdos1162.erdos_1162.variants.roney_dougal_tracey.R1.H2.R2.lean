import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1

-- Reduction Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2.R2 of step Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2
-- Credit: @tamoghnokandar

/-!
The upper bound `log₂ f(n) ≤ (1/16 + ε) n²` of Roney-Dougal and Tracey (arXiv:2503.05416),
split along the proof of their Theorem 1.

* `H1` is their Theorem 3 (Sections 3 to 7): `S_n` has at most `2^(n²/16 + γ n log₂ n)`
  nilpotent subgroups.
* `H2` is their Proposition 8.7 with `ε = 1/16` and the tautological property (Section 8, resting
  on their Theorem 7): any bound `2^(n²/16 + g(n))`, `g` non-decreasing, on the number of nilpotent
  subgroups of `S_n` transfers to all subgroups at the cost of a factor `2^(κ n^(3/2))`.
  Proposition 8.7 only needs the bound for nilpotent subgroups of products of transitive groups of
  bounded degree; those are nilpotent subgroups of `S_n`, so the premise used here is stronger.
  `n^(3/2)` is written `n * √n`.

`main` takes `g(n) = γ n log₂ n` and does the asymptotic bookkeeping.
-/

open Filter

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2

/-- Roney-Dougal and Tracey, Theorem 3: there is an absolute constant `γ ≥ 0` such that `S_n` has
at most `2^(n²/16 + γ n log₂ n)` nilpotent subgroups. -/
def H1 : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ ∀ n : ℕ,
    (Nat.card {H : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent H} : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + γ * n * Real.logb 2 n)

/-- Roney-Dougal and Tracey, Proposition 8.7 (with `ε = 1/16`): there is an absolute constant `κ`
such that, for every non-decreasing `g`, if `S_n` has at most `2^(n²/16 + g(n))` nilpotent
subgroups for all `n`, then it has at most `2^(n²/16 + g(n) + κ n^(3/2))` subgroups for all `n`. -/
def H2 : Prop :=
  ∃ κ : ℝ, ∀ g : ℕ → ℝ, Monotone g →
    (∀ n : ℕ, (Nat.card {H : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent H} : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + g n)) →
    ∀ n : ℕ, (Erdos1162.f n : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + g n + κ * ((n : ℝ) * Real.sqrt n))

lemma logb_two_natCast_nonneg (n : ℕ) : 0 ≤ Real.logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

lemma logb_two_le_four_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (n : ℝ) ≤ 4 * Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have h1 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt n) = Real.log n / 2 := Real.log_sqrt hn0.le
  have h3 : Real.log n ≤ 2 * Real.sqrt n := by linarith
  have h4 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h5 : 0 < Real.log 2 := by linarith
  unfold Real.logb
  rw [div_le_iff₀ h5]
  nlinarith

lemma mono_g (γ : ℝ) (hγ : 0 ≤ γ) :
    Monotone (fun n : ℕ => γ * n * Real.logb 2 (n : ℝ)) := by
  intro m n hmn
  simp only
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have := logb_two_natCast_nonneg n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    positivity
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast h
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hl : Real.logb 2 (m : ℝ) ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hm0 hmn'
    have hl0 := logb_two_natCast_nonneg m
    have h1 : γ * (m : ℝ) ≤ γ * n := mul_le_mul_of_nonneg_left hmn' hγ
    have h2 : 0 ≤ γ * (n : ℝ) := mul_nonneg hγ (Nat.cast_nonneg n)
    exact mul_le_mul h1 hl hl0 h2

theorem main : H1 → H2 → OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1.H2 := by
  rintro ⟨γ, hγ0, hγ⟩ ⟨κ, hκ⟩
  intro ε hε
  have hf := hκ (fun n : ℕ => γ * n * Real.logb 2 (n : ℝ)) (mono_g γ hγ0) hγ
  have hK0 : 0 ≤ 4 * γ + |κ| := by positivity
  filter_upwards [eventually_ge_atTop (⌈((4 * γ + |κ|) / ε) ^ 2⌉₊ + 1)] with n hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
  -- `K ≤ ε √n`
  have hceil : ((4 * γ + |κ|) / ε) ^ 2 ≤ (n : ℝ) := by
    have h1 : ((4 * γ + |κ|) / ε) ^ 2 ≤ (⌈((4 * γ + |κ|) / ε) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈((4 * γ + |κ|) / ε) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hKs : (4 * γ + |κ|) / ε ≤ Real.sqrt n := by
    have h1 : Real.sqrt (((4 * γ + |κ|) / ε) ^ 2) ≤ Real.sqrt n := Real.sqrt_le_sqrt hceil
    rw [Real.sqrt_sq (div_nonneg hK0 hε.le)] at h1
    exact h1
  have hK : 4 * γ + |κ| ≤ ε * Real.sqrt n := by
    rw [div_le_iff₀ hε] at hKs
    linarith
  -- take logarithms
  have hfpos : (0 : ℝ) < (Erdos1162.f n : ℝ) := by exact_mod_cast Erdos1162.f_pos n
  have hlog : Real.logb 2 (Erdos1162.f n : ℝ) ≤
      (n : ℝ) ^ 2 / 16 + γ * n * Real.logb 2 (n : ℝ) + κ * ((n : ℝ) * Real.sqrt n) := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hfpos (hf n)
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
  have hL : Real.logb 2 (n : ℝ) ≤ 4 * Real.sqrt n := logb_two_le_four_sqrt n hn1
  have hns : 0 ≤ (n : ℝ) * Real.sqrt n := mul_nonneg hn0 hs0
  have t1 : γ * n * Real.logb 2 (n : ℝ) ≤ 4 * γ * ((n : ℝ) * Real.sqrt n) := by
    have := mul_le_mul_of_nonneg_left hL (mul_nonneg hγ0 hn0)
    linarith
  have t2 : κ * ((n : ℝ) * Real.sqrt n) ≤ |κ| * ((n : ℝ) * Real.sqrt n) :=
    mul_le_mul_of_nonneg_right (le_abs_self κ) hns
  have t3 : (4 * γ + |κ|) * ((n : ℝ) * Real.sqrt n) ≤ ε * (n : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hK hns
    have h2 : ε * Real.sqrt n * ((n : ℝ) * Real.sqrt n) = ε * (n : ℝ) ^ 2 := by
      calc ε * Real.sqrt n * ((n : ℝ) * Real.sqrt n)
          = ε * (n : ℝ) * (Real.sqrt n * Real.sqrt n) := by ring
        _ = ε * (n : ℝ) ^ 2 := by rw [hss]; ring
    linarith
  nlinarith [t1, t2, t3, hlog]

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2
