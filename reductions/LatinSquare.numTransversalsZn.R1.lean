import FormalConjectures.Paper.LatinSquare
import Mathlib

-- Credit: @marcusbuffett. @MechaNuggan also noted the logarithmic rate and diagonal in the desk notes.
namespace OMA.R_LatinSquare_numTransversalsZn_R1
open LatinSquare Filter Set
open scoped Topology

/-- The logarithmic growth-rate conclusion of Eberhard, Manners and Mrazović. -/
def H1 : Prop := Tendsto (fun k : ℕ ↦ (1 : ℝ) / (2*k+1) *
  Real.log (z (2*k+1) / (2*k+1).factorial)) atTop (𝓝 (-1))

/-- The diagonal is a transversal in odd order, while negation is not. -/
def H2 : Prop := ∀ n : ℕ, 3 ≤ n → Odd n → 0 < z n ∧ z n < n.factorial

/-- A convergent sequence strictly inside the open unit interval, with interior
limit, has a uniform positive distance from both endpoints. -/
def H3 : Prop := ∀ (u : ℕ → ℝ) (x : ℝ), Tendsto u atTop (𝓝 x) → x ∈ Ioo 0 1 →
  (∀ n ≥ 1, u n ∈ Ioo 0 1) →
  ∃ a b : ℝ, 0 < a ∧ b < 1 ∧ a < b ∧ ∀ n ≥ 1, u n ∈ Icc a b

theorem main : H1 → H2 → H3 → type_of% @LatinSquare.numTransversalsZn := by
  intro rate strict uniform
  let u (k : ℕ) := ((z (2*k+1) : ℝ) / (2*k+1).factorial) ^ (((2*k+1 : ℕ) : ℝ)⁻¹)
  have bounds (k : ℕ) (hk : 1 ≤ k) : u k ∈ Ioo 0 1 := by
    have hodd : Odd (2*k+1) := ⟨k,rfl⟩
    obtain ⟨hp,hl⟩ := strict (2*k+1) (by omega) hodd
    have hr : (z (2*k+1) : ℝ) / (2*k+1).factorial < 1 := by
      apply (div_lt_one (by positivity)).mpr
      exact_mod_cast hl
    exact ⟨Real.rpow_pos_of_pos (by positivity) _,
      Real.rpow_lt_one (by positivity) hr (by positivity)⟩
  have rootRate : Tendsto u atTop (𝓝 (Real.exp (-1))) := by
    apply (Real.continuous_exp.continuousAt.tendsto.comp rate).congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hp := (strict (2*k+1) (by omega) ⟨k,rfl⟩).1
    dsimp [Function.comp_def,u]
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    push_cast
    ring
  obtain ⟨a,b,ha,hb,hab,hh⟩ := uniform u _ rootRate
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (by norm_num)⟩ bounds
  refine ⟨a,ha,b,hb,hab,?_⟩
  rintro n hn ⟨k,rfl⟩
  obtain ⟨hl,hu⟩ := hh k (by omega)
  have he : (u k) ^ (2*k+1) = (z (2*k+1) : ℝ) / (2*k+1).factorial :=
    Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have l := pow_le_pow_left₀ ha.le hl (2*k+1)
  have h := pow_le_pow_left₀ (ha.le.trans hl) hu (2*k+1)
  rw [he] at l h
  exact ⟨(le_div_iff₀ (by positivity)).mp l,(div_le_iff₀ (by positivity)).mp h⟩

end OMA.R_LatinSquare_numTransversalsZn_R1
