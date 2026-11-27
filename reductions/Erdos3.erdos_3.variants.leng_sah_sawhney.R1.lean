import FormalConjectures.ErdosProblems.«3»
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
The density increment argument of Leng, Sah and Sawhney, arXiv:2402.17995,
uses a multiplicative density gain that becomes a fixed decrease in the
logarithm of the reciprocal density. The
progression-length estimate bounds the loss in the iterated logarithm of the
interval length. The second hypothesis isolates the iteration of these estimates.
-/

namespace OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1

open Asymptotics Filter

/-- The density increment after rescaling the progression to an integer interval. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∃ D : ℕ,
      ∀ (N : ℕ) (A : Finset ℕ), 3 ≤ N → 0 < A.card →
        A ⊆ Finset.Icc 1 N → (A : Set ℕ).IsAPOfLengthFree k →
        let gap := Real.log ((N : ℝ) / A.card)
        let level := Real.log (Real.log (N : ℝ))
        level ≤ C * (1 + gap) ^ D ∨
          ∃ (M : ℕ) (B : Finset ℕ), 3 ≤ M ∧ 0 < B.card ∧
            B ⊆ Finset.Icc 1 M ∧ (B : Set ℕ).IsAPOfLengthFree k ∧
            Real.log ((M : ℝ) / B.card) ≤ gap - η ∧
            level ≤ Real.log (Real.log (M : ℝ)) + C * (1 + gap) ^ D

/-- A fixed decrease in the gap allows only linearly many steps. The accumulated
loss in the level is therefore at most polynomial in the initial gap. -/
def H2 : Prop :=
  ∀ (State : Type) (gap level : State → ℝ) (η C : ℝ) (D : ℕ),
    0 < η → 0 < C → (∀ s, 0 ≤ gap s) →
    (∀ s, level s ≤ C * (1 + gap s) ^ D ∨
      ∃ t, gap t ≤ gap s - η ∧ level s ≤ level t + C * (1 + gap s) ^ D) →
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ s, Real.exp (-gap s) ≤ K * Real.exp (-(max (level s) 0) ^ c)

theorem main : H1 → H2 → type_of% @Erdos3.erdos_3.variants.leng_sah_sawhney := by
  intro increment iteration k hk
  obtain ⟨η, C, hη, hC, D, advance⟩ := increment k hk
  let State := {p : ℕ × Finset ℕ // 3 ≤ p.1 ∧ 0 < p.2.card ∧
    p.2 ⊆ Finset.Icc 1 p.1 ∧ (p.2 : Set ℕ).IsAPOfLengthFree k}
  let gap (s : State) : ℝ := Real.log ((s.1.1 : ℝ) / s.1.2.card)
  let level (s : State) : ℝ := Real.log (Real.log (s.1.1 : ℝ))
  have gap_nonnegative (s : State) : 0 ≤ gap s := by
    have hcard : s.1.2.card ≤ s.1.1 := by
      simpa using Finset.card_le_card s.2.2.2.1
    have hpos : (0 : ℝ) < (s.1.2.card : ℝ) := by exact_mod_cast s.2.2.1
    exact Real.log_nonneg ((le_div_iff₀ hpos).mpr (by
      simpa only [one_mul] using (show (s.1.2.card : ℝ) ≤ s.1.1 by exact_mod_cast hcard)))
  have step (s : State) : level s ≤ C * (1 + gap s) ^ D ∨
      ∃ t, gap t ≤ gap s - η ∧ level s ≤ level t + C * (1 + gap s) ^ D := by
    obtain ⟨⟨N, A⟩, hN, hcard, hsubset, hfree⟩ := s
    rcases advance N A hN hcard hsubset hfree with small | next
    · exact Or.inl small
    · obtain ⟨M, B, hM, hB, hsub, hBfree, hg, hl⟩ := next
      exact Or.inr ⟨⟨(M, B), hM, hB, hsub, hBfree⟩, hg, hl⟩
  obtain ⟨c, K, hc, hK, bound⟩ :=
    iteration State gap level η C D hη hC gap_nonnegative step
  refine ⟨c, hc, isBigO_iff.mpr ⟨K, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).mpr (Real.exp_one_lt_three.le.trans (by exact_mod_cast hN))
  have hlevel : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hlog
  have hnonneg : 0 ≤ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c) := by positivity
  have hboundNonneg : 0 ≤ K * ((N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) :=
    mul_nonneg hK.le hnonneg
  have hmax : Erdos3.r k N ≤
      ⌊K * ((N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c))⌋₊ := by
    apply csSup_le'
    rintro _ ⟨A, hA, hfree, rfl⟩
    rw [Nat.le_floor_iff hboundNonneg]
    by_cases hApos : 0 < A.card
    · let s : State := ⟨(N, A), hN, hApos, hA, hfree⟩
      have hAreal : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hApos
      have hratio : Real.exp (-gap s) = (A.card : ℝ) / N := by
        change Real.exp (-Real.log ((N : ℝ) / A.card)) = _
        rw [Real.exp_neg, Real.exp_log (div_pos hNpos hAreal), inv_div]
      have h := bound s
      rw [hratio, show level s = Real.log (Real.log (N : ℝ)) from rfl,
        max_eq_left hlevel] at h
      calc
        (A.card : ℝ) ≤ (K * Real.exp (-Real.log (Real.log N) ^ c)) * N :=
          (div_le_iff₀ hNpos).mp h
        _ = _ := by ring
    · simpa [Nat.eq_zero_of_not_pos hApos] using hboundNonneg
  have hreal : (Erdos3.r k N : ℝ) ≤ K * ((N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) :=
    (show (Erdos3.r k N : ℝ) ≤ (⌊K * ((N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c))⌋₊ : ℕ)
      by exact_mod_cast hmax).trans (Nat.floor_le hboundNonneg)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg (Erdos3.r k N)), abs_of_nonneg hnonneg]
  exact hreal

end OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1
