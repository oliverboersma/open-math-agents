import FormalConjectures.ErdosProblems.«89»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1
open Filter Finset EuclideanGeometry Asymptotics
open scoped Classical

/-- Guth and Katz's incidence estimate for ordered pairs of nonzero equal-length segments. -/
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℝ², S.card = n →
  let P := S.offDiag
  (((P ×ˢ P).filter fun z ↦ dist z.1.1 z.1.2 = dist z.2.1 z.2.2).card : ℝ) ≤
    C * (n : ℝ)^3 * Real.log n

/-- The squared number of ordered segments is bounded by the number of distinct
lengths times the number of congruent ordered segment pairs. -/
def H2 : Prop := ∀ S : Finset ℝ², let P := S.offDiag
  P.card^2 ≤ distinctDistances S *
    ((P ×ˢ P).filter fun z ↦ dist z.1.1 z.1.2 = dist z.2.1 z.2.2).card

theorem main : H1 → H2 → type_of% @Erdos89.erdos_89.variants.n_dvd_log_n := by
  classical
  rintro ⟨C,hC,inc⟩ energy
  refine IsBigO.of_bound (4*C) ?_
  filter_upwards [inc,eventually_ge_atTop 2] with n hinc hn
  let v := {m : ℕ | ∃ S : Finset ℝ², S.card = n ∧ distinctDistances S = m}
  have nonempty : v.Nonempty := by
    obtain ⟨S,hS⟩ := Infinite.exists_subset_card_eq ℝ² n
    exact ⟨_,S,hS,rfl⟩
  obtain ⟨S,hS,hD⟩ := Nat.sInf_mem nonempty
  change distinctDistances S = minimalDistinctDistances ℝ² n at hD
  let P := S.offDiag
  let E := (P ×ˢ P).filter fun z ↦ dist z.1.1 z.1.2 = dist z.2.1 z.2.2
  have he : (P.card:ℝ)^2 ≤ (distinctDistances S : ℝ) * E.card := by exact_mod_cast energy S
  have upper := mul_le_mul_of_nonneg_left (hinc S hS) (Nat.cast_nonneg (distinctDistances S) : 0 ≤ (_ : ℝ))
  have he' : (P.card:ℝ)^2 ≤ (distinctDistances S : ℝ) * (C*(n:ℝ)^3*Real.log n) := he.trans upper
  have cardP : (P.card : ℝ) = (n : ℝ) * ((n : ℝ)-1) := by
    dsimp [P]
    rw [offDiag_card,hS,← Nat.mul_sub_one]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) hlog.le),
    ← hD, abs_of_nonneg (Nat.cast_nonneg (distinctDistances S) : (0:ℝ) ≤ _)]
  apply (div_le_iff₀ hlog).mpr
  have low : (n:ℝ)^2/2 ≤ (P.card:ℝ) := by rw [cardP]; nlinarith
  have quad := (pow_le_pow_left₀ (by positivity) low 2).trans he'
  apply le_of_mul_le_mul_left (a := (n:ℝ)^3) _ (by positivity)
  nlinarith only [quad]

end OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1
