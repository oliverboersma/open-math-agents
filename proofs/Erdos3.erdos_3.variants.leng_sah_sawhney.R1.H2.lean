import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1
import Mathlib

-- Step Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H2: hypothesis H2 of reduction Erdos3.erdos_3.variants.leng_sah_sawhney.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Each density increment lowers the gap by at least η, so following increments from s takes at
most g/η + 1 steps, where g = gap s. Induction gives level s ≤ A (1 + g)^(D+1). With
c = 1/(2(D+1)), max(level s, 0)^c ≤ A^c √(1+g) ≤ g + (A^(2c) + 1)/2 by AM-GM, which is the
claimed bound with K = exp((A^(2c) + 1)/2). -/

namespace Erdos3LSSStepH2

lemma level_bound (State : Type) (gap level : State → ℝ) (η C : ℝ) (D : ℕ) (hη : 0 < η)
    (hC : 0 < C) (hg : ∀ s, 0 ≤ gap s)
    (h : ∀ s, level s ≤ C * (1 + gap s) ^ D ∨ ∃ t, gap t ≤ gap s - η ∧
      level s ≤ level t + C * (1 + gap s) ^ D) :
    ∀ n : ℕ, ∀ s, gap s < (n + 1) * η → level s ≤ (n + 1) * (C * (1 + gap s) ^ D) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rcases h s with h1 | ⟨t, ht, -⟩
    · simpa using h1
    · have := hg t
      push_cast at hs
      linarith
  | succ n ih =>
    intro s hs
    have hX : 0 ≤ C * (1 + gap s) ^ D := by have := hg s; positivity
    rcases h s with h1 | ⟨t, ht, h2⟩
    · push_cast
      nlinarith
    · have htlt : gap t < (n + 1) * η := by push_cast at hs; linarith
      have h3 := ih t htlt
      have hmono : (1 + gap t) ^ D ≤ (1 + gap s) ^ D :=
        pow_le_pow_left₀ (by linarith [hg t]) (by linarith) D
      have h4 : (n + 1 : ℝ) * (C * (1 + gap t) ^ D) ≤ (n + 1) * (C * (1 + gap s) ^ D) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hmono hC.le
      push_cast
      linarith

theorem main : ∀ (State : Type) (gap level : State → ℝ) (η C : ℝ) (D : ℕ), 0 < η → 0 < C →
    (∀ s, 0 ≤ gap s) → (∀ s, level s ≤ C * (1 + gap s) ^ D ∨ ∃ t, gap t ≤ gap s - η ∧
      level s ≤ level t + C * (1 + gap s) ^ D) →
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ s, Real.exp (-gap s) ≤ K * Real.exp (-(max (level s) 0) ^ c) := by
  intro State gap level η C D hη hC hg h
  set A : ℝ := (1 / η + 1) * C with hA
  have hApos : 0 < A := by positivity
  set c : ℝ := 1 / (2 * ((D : ℝ) + 1)) with hc
  have hcpos : 0 < c := by positivity
  refine ⟨c, Real.exp ((A ^ (2 * c) + 1) / 2), hcpos, Real.exp_pos _, ?_⟩
  intro s
  set g := gap s with hgdef
  have hg0 : 0 ≤ g := hg s
  -- level s ≤ A (1 + g)^(D+1)
  have hlev : level s ≤ A * (1 + g) ^ (D + 1) := by
    set n := ⌊g / η⌋₊ with hn
    have hlt : g < (n + 1) * η := by
      have := Nat.lt_floor_add_one (g / η)
      rw [div_lt_iff₀ hη] at this
      push_cast at this ⊢
      linarith
    have hb := level_bound State gap level η C D hη hC hg h n s hlt
    have hnle : (n : ℝ) ≤ g / η := Nat.floor_le (div_nonneg hg0 hη.le)
    have hX : 0 ≤ C * (1 + g) ^ D := by positivity
    calc level s ≤ (n + 1) * (C * (1 + g) ^ D) := hb
      _ ≤ (g / η + 1) * (C * (1 + g) ^ D) := by
          apply mul_le_mul_of_nonneg_right _ hX; linarith
      _ ≤ ((1 / η + 1) * (1 + g)) * (C * (1 + g) ^ D) := by
          apply mul_le_mul_of_nonneg_right _ hX
          have h1 : 0 ≤ 1 / η := by positivity
          rw [show (1 / η + 1) * (1 + g) = 1 / η + g / η + 1 + g by ring]
          linarith
      _ = A * (1 + g) ^ (D + 1) := by rw [hA, pow_succ]; ring
  set L := max (level s) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  have hLle : L ≤ A * (1 + g) ^ (D + 1) := max_le hlev (by positivity)
  -- L^c ≤ A^c * sqrt(1+g)
  have hpow : L ^ c ≤ A ^ c * Real.sqrt (1 + g) := by
    calc L ^ c ≤ (A * (1 + g) ^ (D + 1)) ^ c := Real.rpow_le_rpow hL0 hLle hcpos.le
      _ = A ^ c * ((1 + g) ^ (D + 1)) ^ c := Real.mul_rpow hApos.le (by positivity)
      _ = A ^ c * Real.sqrt (1 + g) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]
          congr 1
          rw [hc]; push_cast; field_simp
  -- AM-GM
  have hsq : Real.sqrt (1 + g) ^ 2 = 1 + g := Real.sq_sqrt (by linarith)
  have hAc : (A ^ c) ^ 2 = A ^ (2 * c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hApos.le]; push_cast; ring_nf
  have hamgm : A ^ c * Real.sqrt (1 + g) ≤ g + (A ^ (2 * c) + 1) / 2 := by
    nlinarith [sq_nonneg (A ^ c - Real.sqrt (1 + g))]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Erdos3LSSStepH2

theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1.H2 := Erdos3LSSStepH2.main
