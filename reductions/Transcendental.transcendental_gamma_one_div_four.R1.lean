import FormalConjectures.Wikipedia.Transcendental
import Mathlib

-- Reduction Transcendental.transcendental_gamma_one_div_four.R1: Gamma(1/4) is transcendental
-- Source: G. V. Chudnovsky, Algebraic independence of constants connected with the exponential
--   and the elliptic functions, Dokl. Akad. Nauk Ukrain. SSR Ser. A 8 (1976), 698-701; see also
--   M. Waldschmidt, Transcendence of periods: the state of the art, Pure Appl. Math. Q. 2 (2006).
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Transcendence of `Γ(1/4)` from Chudnovsky's theorem on periods

Chudnovsky's theorem (1976): if a Weierstrass elliptic function has algebraic invariants and
complex multiplication, then `π` and any nonzero period `ω` are algebraically independent over `ℚ`.
For the lemniscatic curve `y² = 1 - x⁴` (complex multiplication by `ℤ[i]`) the number
`∫₀¹ dx / √(1 - x⁴) = ϖ / 2 = 1.31102…`, half the lemniscate constant, is a nonzero algebraic
multiple of a period.

* `H1` (Chudnovsky, the deep input): `π` and `∫₀¹ dx / √(1 - x⁴)` are algebraically independent
  over `ℚ`, that is, `π` and the lemniscate constant are algebraically independent. This is the
  theorem in its original form, about periods; it does not mention the Gamma function.
* `H2` (Euler's Beta integral, elementary): `∫₀¹ dx / √(1 - x⁴) = Γ(1/4) Γ(1/2) / (4 Γ(3/4))`,
  by the substitution `t = x⁴`, which turns the integral into `B(1/4, 1/2) / 4`.

`main`: the reflection formula at `1/4` gives `Γ(1/4) Γ(3/4) = π √2`, hence
`π · (ϖ/2)² = Γ(1/4)⁴ / 32`. If `Γ(1/4)` were algebraic, the monomial `π · (ϖ/2)²` would be
algebraic, contradicting `H1`.
-/

namespace OMA.R_Transcendental_transcendental_gamma_one_div_four_R1

open Real

/-- Chudnovsky (1976): `π` and the lemniscate period `∫₀¹ dx / √(1 - x⁴)` are algebraically
independent over `ℚ`. -/
def H1 : Prop :=
  AlgebraicIndependent ℚ
    (fun b : Bool => if b then π else ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 4))

/-- Euler's Beta integral: `∫₀¹ dx / √(1 - x⁴) = B(1/4, 1/2) / 4 = Γ(1/4) Γ(1/2) / (4 Γ(3/4))`. -/
def H2 : Prop :=
  ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 4) =
    Real.Gamma (1 / 4) * Real.Gamma (1 / 2) / (4 * Real.Gamma (3 / 4))

/-- A monomial `x ^ m * y ^ n` with `0 < m` in two algebraically independent reals is
transcendental. -/
lemma monomial_ne {x y a : ℝ}
    (ind : AlgebraicIndependent ℚ (fun b : Bool => if b then x else y))
    (ha : IsAlgebraic ℚ a) (m n : ℕ) (hm : 0 < m) : x ^ m * y ^ n ≠ a := by
  intro h
  have indK : AlgebraicIndependent (algebraicClosure ℚ ℝ) (fun b : Bool => if b then x else y) :=
    ind.algebraicClosure
  let a' : algebraicClosure ℚ ℝ := ⟨a, mem_algebraicClosure_iff.mpr ha⟩
  have hp : MvPolynomial.aeval (fun b : Bool => if b then x else y)
      (MvPolynomial.X true ^ m * MvPolynomial.X false ^ n - MvPolynomial.C a' :
        MvPolynomial Bool (algebraicClosure ℚ ℝ)) = 0 := by
    have : algebraMap (algebraicClosure ℚ ℝ) ℝ a' = a := rfl
    simp [this, h]
  have p0 := indK.eq_zero_of_aeval_eq_zero _ hp
  have e0 := congrArg (MvPolynomial.eval (fun _ => (0 : algebraicClosure ℚ ℝ))) p0
  have e1 := congrArg (MvPolynomial.eval (fun _ => (1 : algebraicClosure ℚ ℝ))) p0
  simp [hm.ne'] at e0 e1
  rw [e0] at e1
  simp at e1

/-- The algebra behind `main`: reflection at `1/4` (`e3`) and the Beta evaluation (`e4`). -/
lemma period_identity {P I G T q w : ℝ} (hG : 0 < G) (_hT : 0 < T)
    (hq : 0 < q) (hw : 0 < w) (hw2 : w ^ 2 = 2) (hq2 : q ^ 2 = P)
    (e3 : G * T = P * w) (e4 : I = G * q / (4 * T)) : P * I ^ 2 = G ^ 4 / 32 := by
  subst hq2
  have hT' : T = q ^ 2 * w / G := by field_simp; linarith
  rw [e4, hT']
  field_simp
  linear_combination (-(16 : ℝ)) * hw2

theorem main : H1 → H2 → type_of% @Transcendental.transcendental_gamma_one_div_four := by
  intro h1 h2 hG
  have ha : IsAlgebraic ℚ (Real.Gamma (1 / 4) ^ 4 * algebraMap ℚ ℝ (1 / 32)) :=
    (hG.pow 4).mul (isAlgebraic_algebraMap _)
  have e3 := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show π * (1 / 4) = π / 4 by ring,
    Real.sin_pi_div_four] at e3
  have h2pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key := period_identity (P := π) (I := ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 4))
    (G := Real.Gamma (1 / 4)) (T := Real.Gamma (3 / 4)) (q := √π) (w := √2)
    (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))
    (Real.sqrt_pos.mpr Real.pi_pos) h2pos hs2 (Real.sq_sqrt Real.pi_pos.le)
    (by rw [e3]; field_simp; linarith [hs2])
    (by rw [h2, Real.Gamma_one_half_eq])
  refine monomial_ne h1 ha 1 2 one_pos ?_
  rw [pow_one, key]
  simp [div_eq_mul_inv]

end OMA.R_Transcendental_transcendental_gamma_one_div_four_R1
