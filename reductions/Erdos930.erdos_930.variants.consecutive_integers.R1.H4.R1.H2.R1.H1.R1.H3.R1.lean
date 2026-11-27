import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1
import Mathlib

/-!
# An explicit upper bound for Chebyshev's theta

Below exp 40 the problem becomes a finite integer inequality about primorials.
It follows from Büthe's verified bound theta(x) < x - 0.05 sqrt(x) in this
range. Above exp 40, Table 14 of Broadbent, Kadiri, Lumley, Ng and Wilk
gives a relative upper error smaller than 1/40000000. Corollary 1.4 of
Fiori, Kadiri and Swidinsky gives the decaying relative error for psi,
with constants 9.22022, 3/2 and 0.8476836. Rounding the first and last
constants outwards suffices. The last step certifies the overlap of these
two estimates at explicit constants.
-/
namespace OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1
open Finset Real

/-- An integer certificate up to the first analytic threshold. -/
def H1 : Prop := ∀ n : ℕ, 5000000 ≤ n → n ≤ ⌊exp 40⌋₊ →
    primorial n * n^(n^2) ≤ (n+1)^(n^2)

/-- The one-sided error at the b=40 entry of the explicit Chebyshev table. -/
def H2 : Prop := ∀ x : ℝ, exp 40 ≤ x →
    Chebyshev.theta x - x ≤ x/40000000

/-- The explicit exponentially decreasing estimate for psi, rounded outwards. -/
def H3 : Prop := ∀ x : ℝ, exp 40 ≤ x →
    Chebyshev.psi x - x ≤ x * (10 * (sqrt (log x))^3 * exp (-(4/5)*sqrt (log x)))

/-- Comparison of the constant and exponentially decreasing relative errors. -/
def H4 : Prop := ∀ y : ℝ, 0 ≤ y →
    min (1/40000000:ℝ) (10*y^3*exp (-(4/5)*y)) * (5*y^4) ≤ 1

lemma primorial_bound (n : ℕ) (hn : 0 < n)
    (cert : primorial n*n^(n^2) ≤ (n+1)^(n^2)) :
    log (primorial n:ℝ) ≤ n := by
  have h : (0:ℝ) < n := by exact_mod_cast hn
  have pp : (0:ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have c : (primorial n:ℝ)*(n:ℝ)^(n^2) ≤ ((n:ℝ)+1)^(n^2) := by exact_mod_cast cert
  have f := log_le_log (by positivity) c
  rw [log_mul pp.ne' (pow_pos h _).ne', log_pow,log_pow] at f
  push_cast at f
  have g := log_le_sub_one_of_pos (show 0<((n:ℝ)+1)/n by positivity)
  rw [log_div (by positivity) h.ne'] at g
  have g' : log ((n:ℝ)+1)-log n ≤ 1/n := by
    calc _ ≤ ((n:ℝ)+1)/n-1 := g
         _ = _ := by field_simp;ring
  have eq : (n:ℝ)^2 * (1/n) = n := by field_simp
  nlinarith only [f,mul_le_mul_of_nonneg_left g' (sq_nonneg (n:ℝ)),eq]

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1.H3 := by
  intro cert table tail overlap x hx
  have xp : 0<x := by linarith
  have lp : 0<log x := log_pos (by linarith)
  by_cases hb : x < exp 40
  · have nlo : 5000000 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hh := primorial_bound ⌊x⌋₊ (by omega) (cert _ nlo (Nat.floor_le_floor hb.le))
    rw [Chebyshev.theta_eq_log_primorial]
    exact (hh.trans (Nat.floor_le xp.le)).trans (le_add_of_nonneg_right (by positivity))
  · let y := sqrt (log x)
    have yp : 0 < y := sqrt_pos.2 lp
    have ys : y^2=log x := sq_sqrt lp.le
    have y4 : y^4=(log x)^2 := by rw [←ys];ring
    let e := min (1/40000000:ℝ) (10*y^3*exp (-(4/5)*y))
    have bound : Chebyshev.theta x-x ≤ x*e := by
      rw [show x*e = min (x*(1/40000000)) (x*(10*y^3*exp (-(4/5)*y))) from mul_min_of_nonneg _ _ xp.le]
      exact le_min (by linarith [table x (le_of_not_gt hb)])
        ((sub_le_sub_right (Chebyshev.theta_le_psi x) x).trans (tail x (le_of_not_gt hb)))
    have he := overlap y yp.le
    change e*(5*y^4) ≤ 1 at he
    rw [y4] at he
    have scaled : x*e ≤ x/(5*(log x)^2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left he xp.le]
    linarith
end OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1_H3_R1
