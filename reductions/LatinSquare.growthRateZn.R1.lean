import FormalConjectures.Paper.LatinSquare
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_LatinSquare_growthRateZn_R1
open LatinSquare Real Filter
open scoped Topology

/-- Eberhard–Manners–Mrazović's enumeration of transversals in odd cyclic groups. -/
def H1 : Prop := Tendsto (fun k : ℕ ↦ let n := 2*k+1; (z n : ℝ) / ((n.factorial : ℝ)^2 / (n : ℝ)^(n-1))) atTop (𝓝 (exp (-(1/2))))

/-- The logarithm of the factorial normalization, divided by the order, tends to minus one. -/
def H2 : Prop := Tendsto (fun n : ℕ ↦ (log (n.factorial : ℝ) -
  ((n : ℝ)-1)*log n) / n) atTop (𝓝 (-1))

theorem main : H1 → H2 → type_of% @LatinSquare.growthRateZn := by
  intro count stirling
  let n (k : ℕ) := 2*k+1
  let q (k : ℕ) := (z (n k) : ℝ) / (((n k).factorial : ℝ)^2 / (n k : ℝ)^(n k-1))
  have hn : Tendsto n atTop atTop := by
    refine tendsto_atTop.2 (fun m ↦ ?_)
    filter_upwards [eventually_ge_atTop m] with k hk
    dsimp [n]
    omega
  have hNr : Tendsto (fun k ↦ (n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hq : Tendsto q atTop (𝓝 (exp (-(1/2)))) := count
  have small := (hq.log (exp_pos _).ne').div_atTop hNr
  have sum := (stirling.comp hn).add small
  rw [add_zero] at sum
  apply sum.congr'
  filter_upwards [hq.eventually (lt_mem_nhds (exp_pos _))] with k hpos
  have hn1 : 1 ≤ n k := by dsimp [n]; omega
  have hnr : (0 : ℝ) < n k := by exact_mod_cast hn1
  have fpos : (0 : ℝ) < (n k).factorial := by positivity
  have zpos : (0 : ℝ) < z (n k) := by
    dsimp [q] at hpos
    exact (div_pos_iff_of_pos_right (by positivity)).mp hpos
  change (log ((n k).factorial : ℝ) - ((n k : ℝ)-1) * log (n k)) / (n k) +
    log (q k) / (n k) = 1 / (2 * (k : ℝ) + 1) * log ((z (n k) : ℝ) / (n k).factorial)
  have castN : (n k : ℝ) = 2*(k : ℝ)+1 := by simp [n]
  rw [← castN]
  simp (disch := positivity) only [q,Real.log_div,Real.log_pow, Nat.cast_sub hn1,
    Nat.cast_one,Nat.cast_ofNat]
  ring

end OMA.R_LatinSquare_growthRateZn_R1
