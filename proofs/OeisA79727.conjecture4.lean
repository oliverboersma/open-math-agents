import FormalConjectures.OEIS.«79727»
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Vandermonde

/-! Reduction of Bala’s squarefree-product conjecture to a half-block congruence. -/

open scoped BigOperators

namespace OpenMath.A079727

private theorem prime_is_odd {p : ℕ} (hp : OeisA3625.A p) : Odd p := by
  apply hp.1.odd_of_ne_two
  intro h
  subst p
  norm_num [OeisA3625.A] at hp

private theorem odd_product (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    Odd (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp]
    exact (prime_is_odd (hS p (Finset.mem_insert_self p S))).mul
      (ih fun q hq => hS q (Finset.mem_insert_of_mem hq))

private theorem square_product_dvd (S : Finset ℕ) (x : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hlocal : ∀ p ∈ S, p ^ 2 ∣ x) :
    (∏ p ∈ S, p) ^ 2 ∣ x := by
  rw [← Finset.prod_pow]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp]
    have hp' := hS p (Finset.mem_insert_self p S)
    have hS' := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hc : (p ^ 2).Coprime (∏ q ∈ S, q ^ 2) := Nat.Coprime.prod_right fun q hq =>
      Nat.coprime_pow_primes 2 2 hp' (hS' q hq) (by
        intro h
        exact hp (h ▸ hq))
    exact hc.mul_dvd_of_dvd_of_dvd (hlocal p (Finset.mem_insert_self p S))
      (ih hS' fun q hq => hlocal q (Finset.mem_insert_of_mem hq))

private theorem sum_blocks (f : ℕ → ℕ) (p J : ℕ) :
    (∑ k ∈ Finset.range (p * J), f k) =
      ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range p, f (p * j + r) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]

private def term (k : ℕ) : ℕ := (Nat.choose (2 * k) k) ^ 3

private theorem carry_dvd {p : ℕ} (hp : OeisA3625.A p) (j r : ℕ)
    (hl : (p + 1) / 2 ≤ r) (hr : r < p) : p ^ 2 ∣ term (p * j + r) := by
  have : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨u, hu⟩ := prime_is_odd hp
  have hk : (p * j + r) % p = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have h2 : 2 * (p * j + r) % p = 2 * r - p := by
    have hflat : 2 * (p * j + r) = (2 * r - p) + p * (2 * j + 1) := by
      have hp' : p ≤ 2 * r := by omega
      calc
        2 * (p * j + r) = 2 * r + p * (2 * j) := by ring
        _ = (2 * r - p + p) + p * (2 * j) := by rw [Nat.sub_add_cancel hp']
        _ = (2 * r - p) + p * (2 * j + 1) := by ring
    rw [hflat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hb := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := 2 * (p * j + r)) (k := p * j + r)
  have hz : (2 * r - p).choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [hk, h2, hz, zero_mul] at hb
  have hd : p ∣ (2 * (p * j + r)).choose (p * j + r) := by
    apply Nat.dvd_of_mod_eq_zero
    simpa [Nat.ModEq] using hb
  obtain ⟨a, ha⟩ := hd
  unfold term
  refine ⟨p * a ^ 3, ?_⟩
  rw [ha]
  ring

/-- Reduces Bala's assertion to the initial half of each residue block. -/
theorem conjecture4_of_blocks
    (half : ∀ p, OeisA3625.A p → ∀ j,
      p ^ 2 ∣ ∑ r ∈ Finset.range ((p + 1) / 2), term (p * j + r))
    (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a ((∏ p ∈ S, p - 1) / 2) := by
  let N := ∏ p ∈ S, p
  change N ^ 2 ∣ OeisA79727.a ((N - 1) / 2)
  apply square_product_dvd _ _ (fun p hp => (hS p hp).1)
  intro p hp
  have hpA := hS p hp
  have hpodd := prime_is_odd hpA
  have hNodd : Odd N := odd_product S hS
  obtain ⟨q, hq⟩ : p ∣ N := Finset.dvd_prod_of_mem id hp
  rw [hq] at hNodd ⊢
  obtain ⟨J, hJ⟩ := (Nat.odd_mul.mp hNodd).2
  have hqsplit : p * q = p * J + p * J + p := by rw [hJ]; ring
  have hindex : (p * q - 1) / 2 + 1 = p * J + (p + 1) / 2 := by
    obtain ⟨i, hi⟩ := hpodd
    omega
  have hpbound : (p + 1) / 2 ≤ p := by omega
  have hfull (j : ℕ) : p ^ 2 ∣ ∑ r ∈ Finset.range p, term (p * j + r) := by
    conv =>
      arg 2
      arg 1
      rw [← Nat.add_sub_of_le hpbound]
    rw [Finset.sum_range_add]
    refine Nat.dvd_add (half p hpA j) (Finset.dvd_sum fun r hr => ?_)
    have hr' := Finset.mem_range.mp hr
    apply carry_dvd hpA j <;> omega
  change p ^ 2 ∣ ∑ k ∈ Finset.range ((p * q - 1) / 2 + 1), term k
  rw [hindex, Finset.sum_range_add, sum_blocks]
  exact Nat.dvd_add (Finset.dvd_sum fun j _ => hfull j) (half p hpA J)

/-- The half-block congruence for the exceptional prime three follows directly from Lucas. -/
theorem half_block_three (j : ℕ) :
    3 ^ 2 ∣ ∑ r ∈ Finset.range ((3 + 1) / 2), term (3 * j + r) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let x := (2 * (3 * j)).choose (3 * j)
  let y := (2 * (3 * j + 1)).choose (3 * j + 1)
  let z := (2 * j).choose j
  have hx : x ≡ z [MOD 3] := by
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := 3) (n := 2 * (3 * j)) (k := 3 * j)
    simpa [x, z, show (3 * j) % 3 = 0 by omega, show 2 * (3 * j) % 3 = 0 by omega,
      show 3 * j / 3 = j by omega, show 2 * (3 * j) / 3 = 2 * j by omega] using h
  have hy : y ≡ 2 * z [MOD 3] := by
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := 3) (n := 2 * (3 * j + 1)) (k := 3 * j + 1)
    simpa [y, z, show (3 * j + 1) % 3 = 1 by omega, show 2 * (3 * j + 1) % 3 = 2 by omega,
      show (3 * j + 1) / 3 = j by omega, show 2 * (3 * j + 1) / 3 = 2 * j by omega] using h
  have hz : z + 2 * z ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr ⟨z, by ring⟩
  obtain ⟨u, hu⟩ := Nat.modEq_zero_iff_dvd.mp ((hx.add hy).trans hz)
  have hmul : 9 ∣ 3 * x * y * (x + y) := ⟨x * y * u, by rw [hu]; ring⟩
  change 9 ∣ ∑ r ∈ Finset.range 2, term (3 * j + r)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
  change 9 ∣ x ^ 3 + y ^ 3
  apply (Nat.dvd_add_iff_left hmul).mpr
  calc
    9 ∣ (x + y) ^ 3 := ⟨3 * u ^ 3, by rw [hu]; ring⟩
    _ = x ^ 3 + y ^ 3 + 3 * x * y * (x + y) := by ring

end OpenMath.A079727

/- First-order expansion of central binomial coefficients along prime blocks. -/

open scoped BigOperators

namespace OpenMath.A079727

/-- A nonzero natural residue modulo p gives a unit modulo p squared. -/
theorem unit_of_residue {p a b : ℕ} (hp : p.Prime) (hb : 0 < b)
    (hbp : b < p) (h : a ≡ b [MOD p]) :
    IsUnit (a : ZMod (p ^ 2)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).2
  intro hdiv
  have hzero := (Nat.modEq_zero_iff_dvd.mpr hdiv)
  have hbdiv := Nat.modEq_zero_iff_dvd.mp (h.symm.trans hzero)
  exact (not_le_of_gt hbp) (Nat.le_of_dvd hb hbdiv)

theorem residue_shift (p j a : ℕ) : p * j + a ≡ a [MOD p] := by
  rw [Nat.ModEq, Nat.add_comm, Nat.add_mul_mod_self_left]

theorem shift_sq_zero (p j : ℕ) :
    ((p : ZMod (p ^ 2)) * j) ^ 2 = 0 := by
  rw [mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

end OpenMath.A079727

/- Algebraic certificates for the even and odd Clausen square cases.

The arguments use the Euler derivation θ=z·d/dz. The variables u0,u1,u2,u3
stand for successive θ derivatives. The two equations in each theorem
are a scaled Gauss equation and its θ derivative.
-/

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

/-- Scaled differential expression for the symmetric Clausen square. -/
def clausenOperator (r z h0 h1 h2 h3 : R) : R :=
  8 * (1 - z) * h3 + (12 * r * (1 - z) - 12) * h2 +
    (4 * (r - 1) ^ 2 - 6 * r ^ 2 * z) * h1 - r ^ 3 * z * h0

/-- Squaring a solution of the symmetric Gauss equation gives the Clausen equation. -/
theorem clausen_square (r z u0 u1 u2 u3 : R)
    (h0 : 16 * (1 - z) * u2 + (8 * r * (1 - z) - 8) * u1 - r ^ 2 * z * u0 = 0)
    (h1 : 16 * (1 - z) * u3 + (8 * r * (1 - z) - 8 - 16 * z) * u2 -
      (r ^ 2 + 8 * r) * z * u1 - r ^ 2 * z * u0 = 0) :
    clausenOperator r z (u0 ^ 2) (2 * u0 * u1)
      (2 * u1 ^ 2 + 2 * u0 * u2) (6 * u1 * u2 + 2 * u0 * u3) = 0 := by
  calc
    _ = (3 * u1 + (r - 1) * u0) *
          (16 * (1 - z) * u2 + (8 * r * (1 - z) - 8) * u1 - r ^ 2 * z * u0) +
        u0 * (16 * (1 - z) * u3 + (8 * r * (1 - z) - 8 - 16 * z) * u2 -
          (r ^ 2 + 8 * r) * z * u1 - r ^ 2 * z * u0) := by unfold clausenOperator; ring
    _ = _ := by simp only [h0, h1, mul_zero, add_zero]

/-- The Euler-transformed Gauss equation yields the same Clausen square
after multiplication by 1-z. -/
theorem clausen_square_euler (r z u0 u1 u2 u3 : R)
    (h0 : 16 * (1 - z) * u2 + (8 * r * (1 - z) - 8 - 16 * z) * u1 -
      (r + 2) ^ 2 * z * u0 = 0)
    (h1 : 16 * (1 - z) * u3 + (8 * r * (1 - z) - 8 - 32 * z) * u2 -
      ((r + 2) ^ 2 + 8 * (r + 2)) * z * u1 - (r + 2) ^ 2 * z * u0 = 0) :
    clausenOperator r z ((1 - z) * u0 ^ 2)
      (-z * u0 ^ 2 + 2 * (1 - z) * u0 * u1)
      (-z * u0 ^ 2 - 4 * z * u0 * u1 + (1 - z) * (2 * u1 ^ 2 + 2 * u0 * u2))
      (-z * u0 ^ 2 - 6 * z * u0 * u1 - 6 * z * (u1 ^ 2 + u0 * u2) +
        (1 - z) * (6 * u1 * u2 + 2 * u0 * u3)) = 0 := by
  calc
    _ = (3 * (1 - z) * u1 + (r * (1 - z) - 1 - z) * u0) *
          (16 * (1 - z) * u2 + (8 * r * (1 - z) - 8 - 16 * z) * u1 -
            (r + 2) ^ 2 * z * u0) +
        (1 - z) * u0 * (16 * (1 - z) * u3 + (8 * r * (1 - z) - 8 - 32 * z) * u2 -
          ((r + 2) ^ 2 + 8 * (r + 2)) * z * u1 - (r + 2) ^ 2 * z * u0) := by
      unfold clausenOperator
      ring
    _ = _ := by simp only [h0, h1, mul_zero, add_zero]

end OpenMath.A079727

/- The exact coefficient recurrences for the scaled Gauss and Clausen operators. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

/-- The Euler derivation on polynomials. -/
noncomputable def theta (P : R[X]) : R[X] := X * derivative P

theorem coeff_theta (P : R[X]) (n : ℕ) : (theta P).coeff n = (n : R) * P.coeff n := by
  cases n with
  | zero => simp [theta]
  | succ n =>
    rw [theta, coeff_X_mul, coeff_derivative]
    simp [mul_comm]

/-- Gauss operator for the upper parameter w/4 and lower parameter (r+1)/2. -/
noncomputable def gaussPolynomial (r w : R) (P : R[X]) : R[X] :=
  16 * (1 - X) * theta (theta P) +
    (C (8 * r - 8) - C (8 * w) * X) * theta P - C (w ^ 2) * X * P

/-- The scaled Gauss equation is exactly the hypergeometric ratio recurrence. -/
theorem coeff_gaussPolynomial (r w : R) (P : R[X]) (n : ℕ) :
    (gaussPolynomial r w P).coeff (n + 1) =
      8 * ((n : R) + 1) * (2 * (n : R) + r + 1) * P.coeff (n + 1) -
        (4 * (n : R) + w) ^ 2 * P.coeff n := by
  have h : gaussPolynomial r w P =
      C 16 * theta (theta P) - C 16 * (X * theta (theta P)) +
        C (8 * r - 8) * theta P - C (8 * w) * (X * theta P) - C (w ^ 2) * (X * P) := by
    simp only [gaussPolynomial, map_ofNat]
    ring
  rw [h]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_theta, Nat.cast_add, Nat.cast_one]
  ring

/-- Polynomial form of the scaled symmetric Clausen operator. -/
noncomputable def clausenPolynomial (r : R) (P : R[X]) : R[X] :=
  8 * (1 - X) * theta (theta (theta P)) +
    (C (12 * r - 12) - C (12 * r) * X) * theta (theta P) +
    (C (4 * (r - 1) ^ 2) - C (6 * r ^ 2) * X) * theta P -
    C (r ^ 3) * X * P

/-- The cubic hypergeometric recurrence follows by taking a coefficient. -/
theorem coeff_clausenPolynomial (r : R) (P : R[X]) (n : ℕ) :
    (clausenPolynomial r P).coeff (n + 1) =
      4 * ((n : R) + 1) * ((n : R) + r) * (2 * (n : R) + r + 1) * P.coeff (n + 1) -
        (2 * (n : R) + r) ^ 3 * P.coeff n := by
  have h : clausenPolynomial r P =
      C 8 * theta (theta (theta P)) - C 8 * (X * theta (theta (theta P))) +
        C (12 * r - 12) * theta (theta P) - C (12 * r) * (X * theta (theta P)) +
        C (4 * (r - 1) ^ 2) * theta P - C (6 * r ^ 2) * (X * theta P) -
        C (r ^ 3) * (X * P) := by
    simp only [clausenPolynomial, map_ofNat]
    ring
  rw [h]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_theta, Nat.cast_add, Nat.cast_one]
  ring

end OpenMath.A079727

/- Exact polynomial symmetric squares for the terminating Clausen cases. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

private theorem theta_add (P Q : R[X]) : theta (P + Q) = theta P + theta Q := by
  simp only [theta, derivative_add, mul_add]

private theorem theta_sub (P Q : R[X]) : theta (P - Q) = theta P - theta Q := by
  simp only [theta, derivative_sub, mul_sub]

private theorem theta_neg (P : R[X]) : theta (-P) = -theta P := by
  simp only [theta, derivative_neg, mul_neg]

private theorem theta_mul (P Q : R[X]) : theta (P * Q) = theta P * Q + P * theta Q := by
  simp only [theta, derivative_mul, mul_add]
  ring

private theorem theta_C (a : R) : theta (C a) = 0 := by simp [theta]
private theorem theta_X : theta (X : R[X]) = X := by simp [theta]
private theorem theta_zero : theta (0 : R[X]) = 0 := by simp [theta]
private theorem theta_one : theta (1 : R[X]) = 0 := by simp [theta]
private theorem theta_two : theta (2 : R[X]) = 0 := by simp [theta]
private theorem theta_four : theta (4 : R[X]) = 0 := by simp [theta]
private theorem theta_eight : theta (8 : R[X]) = 0 := by simp [theta]
private theorem theta_sixteen : theta (16 : R[X]) = 0 := by simp [theta]

private theorem theta_sq (P : R[X]) : theta (P ^ 2) = 2 * P * theta P := by
  rw [pow_two, theta_mul]
  ring

private theorem theta_sq_two (P : R[X]) :
    theta (theta (P ^ 2)) = 2 * theta P ^ 2 + 2 * P * theta (theta P) := by
  rw [theta_sq]
  simp only [theta_mul, theta_two]
  ring

private theorem theta_sq_three (P : R[X]) :
    theta (theta (theta (P ^ 2))) =
      6 * theta P * theta (theta P) + 2 * P * theta (theta (theta P)) := by
  rw [theta_sq_two]
  simp only [theta_add, theta_mul, theta_sq, theta_two]
  ring

private theorem theta_fsq (P : R[X]) :
    theta ((1 - X) * P ^ 2) = -X * P ^ 2 + 2 * (1 - X) * P * theta P := by
  simp only [theta_mul, theta_sub, theta_one, theta_X, theta_sq]
  ring

private theorem theta_fsq_two (P : R[X]) :
    theta (theta ((1 - X) * P ^ 2)) =
      -X * P ^ 2 - 4 * X * P * theta P +
        (1 - X) * (2 * theta P ^ 2 + 2 * P * theta (theta P)) := by
  rw [theta_fsq]
  simp only [theta_add, theta_mul, theta_sub, theta_neg, theta_one, theta_X,
    theta_sq, theta_two]
  ring

private theorem theta_fsq_three (P : R[X]) :
    theta (theta (theta ((1 - X) * P ^ 2))) =
      -X * P ^ 2 - 6 * X * P * theta P -
        6 * X * (theta P ^ 2 + P * theta (theta P)) +
        (1 - X) * (6 * theta P * theta (theta P) + 2 * P * theta (theta (theta P))) := by
  rw [theta_fsq_two]
  simp only [theta_add, theta_mul, theta_sub, theta_neg, theta_one, theta_X,
    theta_sq, theta_two, theta_four]
  ring

private theorem operator_matches (r : R) (P : R[X]) :
    clausenPolynomial r P = clausenOperator (C r) X P (theta P)
      (theta (theta P)) (theta (theta (theta P))) := by
  simp only [clausenPolynomial, clausenOperator, map_sub, map_mul, map_pow, map_one, map_ofNat]
  ring

private theorem gauss_derivative (r w : R) (P : R[X])
    (h : gaussPolynomial r w P = 0) :
    16 * (1 - X) * theta (theta (theta P)) +
      (C (8 * r - 8) - C (8 * w + 16) * X) * theta (theta P) -
      C (w ^ 2 + 8 * w) * X * theta P - C (w ^ 2) * X * P = 0 := by
  have h' := congrArg theta h
  simp only [gaussPolynomial, theta_add, theta_sub, theta_mul, theta_C, theta_zero, theta_X,
    theta_one, theta_eight, theta_sixteen, theta_sq,
    map_add, map_sub, map_mul, map_pow, map_ofNat] at h' ⊢
  linear_combination h'

/-- Gauss at parameter r/4 squares to the scaled Clausen polynomial equation. -/
theorem gauss_square_clausen (r : R) (P : R[X])
    (h : gaussPolynomial r r P = 0) : clausenPolynomial r (P ^ 2) = 0 := by
  have hd := gauss_derivative r r P h
  rw [operator_matches, theta_sq_three, theta_sq_two, theta_sq]
  apply clausen_square
  · simp only [gaussPolynomial, map_sub, map_mul, map_pow, map_ofNat] at h
    linear_combination h
  · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at hd
    linear_combination hd

/-- Gauss at parameter (r+2)/4 squares to the same Clausen equation
after the Euler factor 1-X. -/
theorem gauss_square_euler_clausen (r : R) (P : R[X])
    (h : gaussPolynomial r (r + 2) P = 0) :
    clausenPolynomial r ((1 - X) * P ^ 2) = 0 := by
  have hd := gauss_derivative r (r + 2) P h
  rw [operator_matches, theta_fsq_three, theta_fsq_two, theta_fsq]
  apply clausen_square_euler
  · simp only [gaussPolynomial, map_add, map_sub, map_mul, map_pow, map_ofNat] at h
    linear_combination h
  · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at hd
    linear_combination hd

end OpenMath.A079727

/- A truncating hypergeometric coefficient recurrence provides a Gauss polynomial. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

/-- Polynomial with the first d+1 coefficients of the given sequence. -/
noncomputable def truncateSeries (d : ℕ) (f : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range (d + 1), C (f j) * X ^ j

theorem coeff_truncateSeries (d : ℕ) (f : ℕ → R) (n : ℕ) :
    (truncateSeries d f).coeff n = if n ≤ d then f n else 0 := by
  rw [truncateSeries, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp

theorem natDegree_truncateSeries (d : ℕ) (f : ℕ → R) :
    (truncateSeries d f).natDegree ≤ d := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [coeff_truncateSeries, if_neg (by omega)]

private theorem coeff_gauss_zero (r w : R) (P : R[X]) :
    (gaussPolynomial r w P).coeff 0 = 0 := by
  have h : gaussPolynomial r w P =
      C 16 * theta (theta P) - C 16 * (X * theta (theta P)) +
        C (8 * r - 8) * theta P - C (8 * w) * (X * theta P) - C (w ^ 2) * (X * P) := by
    simp only [gaussPolynomial, map_ofNat]
    ring
  rw [h]
  simp [coeff_theta]

/-- The product coefficient must vanish at the cutoff, after which no
new coefficient is needed. -/
theorem gauss_of_truncating (d : ℕ) (f : ℕ → R) (r w : R)
    (hstep : ∀ n < d, 8 * ((n : R) + 1) * (2 * (n : R) + r + 1) * f (n + 1) =
      (4 * (n : R) + w) ^ 2 * f n)
    (hcut : (4 * (d : R) + w) ^ 2 = 0) :
    gaussPolynomial r w (truncateSeries d f) = 0 := by
  ext n
  cases n with
  | zero => simp [coeff_gauss_zero]
  | succ n =>
    simp only [coeff_gaussPolynomial, coeff_zero, coeff_truncateSeries]
    rcases lt_trichotomy n d with h | h | h
    · rw [if_pos (by omega), if_pos h.le, hstep n h, sub_self]
    · subst n
      rw [if_neg (by omega), if_pos le_rfl, hcut]
      simp
    · rw [if_neg (by omega), if_neg (by omega)]
      simp

/-- The corresponding Clausen solution has the untwisted square form. -/
theorem clausen_of_truncating_even (d : ℕ) (f : ℕ → R) (r : R)
    (hstep : ∀ n < d, 8 * ((n : R) + 1) * (2 * (n : R) + r + 1) * f (n + 1) =
      (4 * (n : R) + r) ^ 2 * f n)
    (hcut : (4 * (d : R) + r) ^ 2 = 0) :
    clausenPolynomial r ((truncateSeries d f) ^ 2) = 0 :=
  gauss_square_clausen r _ (gauss_of_truncating d f r r hstep hcut)

/-- The corresponding Clausen solution for the shifted numerator has
the additional Euler factor. -/
theorem clausen_of_truncating_odd (d : ℕ) (f : ℕ → R) (r : R)
    (hstep : ∀ n < d, 8 * ((n : R) + 1) * (2 * (n : R) + r + 1) * f (n + 1) =
      (4 * (n : R) + (r + 2)) ^ 2 * f n)
    (hcut : (4 * (d : R) + (r + 2)) ^ 2 = 0) :
    clausenPolynomial r ((1 - X) * (truncateSeries d f) ^ 2) = 0 :=
  gauss_square_euler_clausen r _ (gauss_of_truncating d f r (r + 2) hstep hcut)

end OpenMath.A079727

/- The local central-binomial cube recurrence compared to Clausen coefficients. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

/-- A cube block whose perturbation squares to zero is encoded coefficient by coefficient. -/
theorem cube_coeff_of_clausen (d : ℕ) (v : ℕ → R) (P : R[X]) (δ : R)
    (hδ : δ ^ 2 = 0) (hP : clausenPolynomial (1 + 2 * δ) P = 0) (hP0 : P.coeff 0 = 1)
    (hunit : ∀ n < d, IsUnit (8 * (δ + (n : R) + 1) ^ 3))
    (hstep : ∀ n < d, (δ + (n : R) + 1) * v (n + 1) =
      2 * (2 * (δ + (n : R)) + 1) * v n)
    (k : ℕ) (hk : k ≤ d) :
    v k ^ 3 = v 0 ^ 3 * (64 : R) ^ k * P.coeff k := by
  induction k with
  | zero => rw [hP0, pow_zero, mul_one, mul_one]
  | succ k ih =>
    have hk' : k < d := by omega
    have hden :
        4 * ((k : R) + 1) * ((k : R) + (1 + 2 * δ)) *
          (2 * (k : R) + (1 + 2 * δ) + 1) = 8 * (δ + (k : R) + 1) ^ 3 := by
      linear_combination -8 * (δ + (k : R) + 1) * hδ
    have hcf0 := congrArg (fun Q : R[X] => Q.coeff (k + 1)) hP
    rw [coeff_clausenPolynomial, coeff_zero, hden] at hcf0
    have hcf := sub_eq_zero.mp hcf0
    have hcube := congrArg (fun x : R => x ^ 3) (hstep k hk')
    apply (hunit k hk').mul_left_cancel
    calc
      _ = 8 * ((δ + (k : R) + 1) * v (k + 1)) ^ 3 := by ring
      _ = 64 * (2 * (k : R) + (1 + 2 * δ)) ^ 3 * v k ^ 3 := by
        rw [hcube]
        ring
      _ = _ := by
        rw [ih hk'.le, pow_succ]
        linear_combination -(64 * v 0 ^ 3 * (64 : R) ^ k) * hcf

/-- Evaluating the corresponding polynomial recovers the unnormalized cube sum. -/
theorem cube_sum_of_clausen (d : ℕ) (v : ℕ → R) (P : R[X]) (δ : R)
    (hδ : δ ^ 2 = 0) (hP : clausenPolynomial (1 + 2 * δ) P = 0) (hP0 : P.coeff 0 = 1)
    (hdeg : P.natDegree ≤ d)
    (hunit : ∀ n < d, IsUnit (8 * (δ + (n : R) + 1) ^ 3))
    (hstep : ∀ n < d, (δ + (n : R) + 1) * v (n + 1) =
      2 * (2 * (δ + (n : R)) + 1) * v n) :
    (∑ n ∈ Finset.range (d + 1), v n ^ 3) = v 0 ^ 3 * P.eval 64 := by
  rw [Polynomial.eval_eq_sum_range' (n := d + 1) (by omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [cube_coeff_of_clausen d v P δ hδ hP hP0 hunit hstep k
    (Finset.mem_range_succ_iff.mp hk)]
  ring

end OpenMath.A079727

/- Terminating Gauss coefficients for the shifted central-binomial cube sum. -/

open Polynomial

namespace OpenMath.A079727

abbrev RingP (p : ℕ) := ZMod (p ^ 2)

def shift (p j : ℕ) : RingP p := (p : RingP p) * j

def gaussDen (p j n : ℕ) : RingP p :=
  8 * ((n : RingP p) + 1) * (2 * (n : RingP p) + (1 + 2 * shift p j) + 1)

def gaussCoeff (p j : ℕ) (e : RingP p) : ℕ → RingP p
  | 0 => 1
  | n + 1 =>
    (4 * (n : RingP p) + (1 + 2 * shift p j + e)) ^ 2 *
      (gaussDen p j n)⁻¹ * gaussCoeff p j e n

private theorem shifted_unit {p : ℕ} (hp : p.Prime) (j n : ℕ) (hn : n + 1 < p) :
    IsUnit (shift p j + (n : RingP p) + 1) := by
  have h : IsUnit (↑(p * j + (n + 1)) : RingP p) :=
    unit_of_residue hp (by omega) hn (residue_shift p j (n + 1))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, shift, add_assoc] using h

private theorem unit_two {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    IsUnit (2 : RingP p) :=
  unit_of_residue hp (by decide) hp2 (Nat.ModEq.refl 2)

private theorem gaussDen_unit {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j n : ℕ)
    (hn : n + 1 < p) : IsUnit (gaussDen p j n) := by
  have he : gaussDen p j n =
      (2 : RingP p)^4 * (↑(n + 1) : RingP p) * (shift p j + (n : RingP p) + 1) := by
    unfold gaussDen
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [he]
  exact (((unit_two hp hp2).pow 4).mul
      (unit_of_residue hp (by omega) hn (.refl (n + 1)))).mul (shifted_unit hp j n hn)

/-- Multiply through by the unit denominator in the Gauss recurrence. -/
theorem gaussCoeff_step {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j : ℕ)
    (e : RingP p) (n : ℕ) (hn : n + 1 < p) :
    gaussDen p j n * gaussCoeff p j e (n + 1) =
      (4 * (n : RingP p) + (1 + 2 * shift p j + e)) ^ 2 * gaussCoeff p j e n := by
  have h := ZMod.mul_inv_of_unit _ (gaussDen_unit hp hp2 j n hn)
  rw [gaussCoeff]
  calc
    _ = (gaussDen p j n * (gaussDen p j n)⁻¹) *
        ((4 * (n : RingP p) + (1 + 2 * shift p j + e)) ^ 2 * gaussCoeff p j e n) := by ring
    _ = _ := by rw [h, one_mul]

private theorem gauss_cut {p : ℕ} (j e : ℕ) (he : 4 * (p / 4) + 1 + e = p) :
    (4 * ((p / 4 : ℕ) : RingP p) + (1 + 2 * shift p j + (e : RingP p))) ^ 2 = 0 := by
  have hcast := congrArg (fun n : ℕ => (n : RingP p)) he
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hcast
  have h :
      4 * ((p / 4 : ℕ) : RingP p) + (1 + 2 * shift p j + (e : RingP p)) =
        (p : RingP p) * (1 + 2 * (j : RingP p)) := by
    unfold shift
    linear_combination hcast
  rw [h, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

/-- The Gauss polynomial in the relevant branch. -/
noncomputable def primeGauss (p j : ℕ) (e : RingP p) : (RingP p)[X] :=
  truncateSeries (p / 4) (gaussCoeff p j e)

/-- The even or Euler-transformed square. -/
noncomputable def primeSquare (p j : ℕ) : (RingP p)[X] :=
  if p % 4 = 1 then primeGauss p j 0 ^ 2 else (1 - X) * primeGauss p j 2 ^ 2

private theorem gauss_coeff_zero (p j : ℕ) (e : RingP p) :
    (primeGauss p j e).coeff 0 = 1 := by
  rw [primeGauss, coeff_truncateSeries, if_pos (Nat.zero_le _), gaussCoeff]

private theorem primeSquare_eq_clausen {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j : ℕ) :
    clausenPolynomial (1 + 2 * shift p j) (primeSquare p j) = 0 := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr (by omega)
  unfold primeSquare primeGauss
  split
  next h =>
    apply clausen_of_truncating_even
    · intro n hn
      simpa only [gaussDen, add_zero] using gaussCoeff_step hp hp2 j 0 n (by omega)
    · simpa only [Nat.cast_zero, add_zero] using gauss_cut (p := p) j 0 (by omega)
  next h =>
    apply clausen_of_truncating_odd
    · intro n hn
      simpa only [gaussDen] using gaussCoeff_step hp hp2 j 2 n (by omega)
    · simpa only [Nat.cast_ofNat] using gauss_cut (p := p) j 2 (by omega)

private theorem primeSquare_const (p j : ℕ) : (primeSquare p j).coeff 0 = 1 := by
  unfold primeSquare
  split <;> simp [pow_two, mul_coeff_zero, gauss_coeff_zero]

private theorem square_degree_le (p j : ℕ) (e : RingP p) :
    (primeGauss p j e ^ 2).natDegree ≤ 2 * (p / 4) := by
  exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 (natDegree_truncateSeries _ _))

private theorem primeSquare_degree {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j : ℕ) :
    (primeSquare p j).natDegree ≤ p / 2 := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr (by omega)
  unfold primeSquare
  split
  next h =>
    have h' := square_degree_le p j 0
    omega
  next h =>
    have hx : ((1 - X : (RingP p)[X])).natDegree ≤ 1 := by
      have hh := natDegree_sub_le_of_le (by simp : (1 : (RingP p)[X]).natDegree ≤ 1)
          (natDegree_X_le : (X : (RingP p)[X]).natDegree ≤ 1)
      simpa only [max_self] using hh
    have hlo := natDegree_mul_le (p := (1 - X : (RingP p)[X])) (q := primeGauss p j 2 ^ 2)
    have hh := square_degree_le p j 2
    omega

private theorem centralBlock_step (p j n : ℕ) :
    (shift p j + (n : RingP p) + 1) * (Nat.centralBinom (p * j + (n + 1)) : RingP p) =
      2 * (2 * (shift p j + (n : RingP p)) + 1) * Nat.centralBinom (p * j + n) := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, shift, ← Nat.add_assoc] using
    congrArg (fun q : ℕ => (q : RingP p)) (Nat.succ_mul_centralBinom_succ (p * j + n))

/-- The shifted cube half-block is the evaluated square or Euler-transformed square. -/
theorem centralBlock_eq_primeSquare {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j : ℕ) :
    (∑ n ∈ Finset.range (p / 2 + 1), (Nat.centralBinom (p * j + n) : RingP p) ^ 3) =
      (Nat.centralBinom (p * j) : RingP p) ^ 3 * (primeSquare p j).eval 64 := by
  simpa only [add_zero] using cube_sum_of_clausen (p / 2)
    (fun n => (Nat.centralBinom (p * j + n) : RingP p)) (primeSquare p j) (shift p j)
    (shift_sq_zero p j) (primeSquare_eq_clausen hp hp2 j) (primeSquare_const p j)
    (primeSquare_degree hp hp2 j)
    (fun n hn => (show IsUnit (8 : RingP p) from (by
      rw [show (8 : RingP p) = 2 ^ 3 by ring]
      exact (unit_two hp hp2).pow 3)).mul ((shifted_unit hp j n (by omega)).pow 3))
    (fun n _ => centralBlock_step p j n)

end OpenMath.A079727

/- Reduction of every p² cube half-block to one polynomial value modulo p. -/

open Polynomial

namespace OpenMath.A079727

noncomputable def reducePrime (p : ℕ) : RingP p →+* ZMod p :=
  ZMod.castHom (show p ∣ p ^ 2 by exact ⟨p, by ring⟩) (ZMod p)

private theorem reduce_shift (p j : ℕ) : reducePrime p (shift p j) = 0 := by
  simp [shift, reducePrime]

private theorem cast_nat_ne_zero_of_lt {p k : ℕ} (hk : 0 < k) (hkp : k < p) :
    (k : ZMod p) ≠ 0 := by
  intro h
  exact (not_le_of_gt hkp) (Nat.le_of_dvd hk ((ZMod.natCast_eq_zero_iff k p).1 h))

/-- In the prime field, every shifted Gauss coefficient is a squared binomial coefficient. -/
theorem gaussCoeff_reduce_binomial {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j e : ℕ)
    (he : 4 * (p / 4) + 1 + e = p) (n : ℕ) (hn : n ≤ p / 4) :
    reducePrime p (gaussCoeff p j (e : RingP p) n) = (((p / 4).choose n : ℕ) : ZMod p)^2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  induction n with
  | zero => simp [gaussCoeff]
  | succ n ih =>
    have hn' : n ≤ p / 4 := by omega
    have hnp : n + 1 < p := by omega
    have hne : (↑(n + 1) : ZMod p) ≠ 0 :=
      cast_nat_ne_zero_of_lt (by omega) hnp
    have htwo : (2 : ZMod p) ≠ 0 := cast_nat_ne_zero_of_lt (by decide) hp2
    have hD : 16 * ((n : ZMod p) + 1) ^ 2 ≠ 0 := by
      rw [show (16 : ZMod p) = 2 ^ 4 by ring]
      exact mul_ne_zero (pow_ne_zero _ htwo) (pow_ne_zero _ (by
        simpa only [Nat.cast_add, Nat.cast_one] using hne))
    have he' : 4 * ((p / 4 : ℕ) : ZMod p) + 1 + (e : ZMod p) = 0 := by
      have hc := congrArg (fun k : ℕ => (k : ZMod p)) he
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_self] using hc
    have hw : 4 * (n : ZMod p) + (1 + (e : ZMod p)) =
        -4 * (((p / 4 : ℕ) : ZMod p) - (n : ZMod p)) := by
      linear_combination he'
    have hg := congrArg (reducePrime p) (gaussCoeff_step hp hp2 j (e : RingP p) n hnp)
    simp only [gaussDen, map_mul, map_pow, map_add, map_natCast, map_one, map_ofNat,
      reduce_shift, mul_zero, add_zero] at hg
    rw [ih hn', hw] at hg
    have hc : (((p / 4).choose (n + 1) : ℕ) : ZMod p) * ((n : ZMod p) + 1) =
        (((p / 4).choose n : ℕ) : ZMod p) * (((p / 4 : ℕ) : ZMod p) - (n : ZMod p)) := by
      have h := congrArg (fun k : ℕ => (k : ZMod p)) (Nat.choose_succ_right_eq (p / 4) n)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hn'] using h
    have hcs := congrArg (fun x : ZMod p => x ^ 2) hc
    apply mul_left_cancel₀ hD
    linear_combination hg - 16 * hcs

/-- Evaluate the common prime-field Gauss polynomial at 64. -/
noncomputable def binomialSquareEval (p : ℕ) : ZMod p :=
  ∑ n ∈ Finset.range (p / 4 + 1), (((p / 4).choose n : ℕ) : ZMod p)^2 * 64 ^ n

theorem reduce_primeGauss_eval {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j e : ℕ)
    (he : 4 * (p / 4) + 1 + e = p) :
    reducePrime p ((primeGauss p j (e : RingP p)).eval 64) = binomialSquareEval p := by
  simp only [primeGauss, truncateSeries, eval_finsetSum, eval_mul, eval_pow, eval_C, eval_X,
    map_sum, map_mul, map_pow, map_ofNat, binomialSquareEval]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [gaussCoeff_reduce_binomial hp hp2 j e he n (Finset.mem_range_succ_iff.mp hn)]

private theorem square_zero_of_reduced_zero {p : ℕ} (hp : p.Prime) (x : RingP p)
    (h : reducePrime p x = 0) : x ^ 2 = 0 := by
  let _ : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x] at h ⊢
  have hdiv : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 (by simpa only [map_natCast] using h)
  obtain ⟨u, hu⟩ := hdiv
  rw [hu, Nat.cast_mul, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

/-- One prime-field vanishing proves all shifted cube half-blocks modulo p². -/
theorem all_half_blocks_of_eval_zero {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (j : ℕ)
    (hzero : binomialSquareEval p = 0) :
    p ^ 2 ∣ ∑ n ∈ Finset.range (p / 2 + 1), Nat.centralBinom (p * j + n) ^ 3 := by
  apply (ZMod.natCast_eq_zero_iff _ _).1
  push_cast
  rw [centralBlock_eq_primeSquare hp hp2 j]
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr (by omega)
  have he : (primeSquare p j).eval 64 = 0 := by
    unfold primeSquare
    split
    next hp1 =>
      rw [eval_pow]
      apply square_zero_of_reduced_zero hp
      rw [show (0 : RingP p) = (0 : ℕ) by simp,
        reduce_primeGauss_eval hp hp2 j 0 (by omega), hzero]
    next hp1 =>
      rw [eval_mul, eval_pow]
      have hs : ((primeGauss p j 2).eval 64) ^ 2 = 0 := by
        apply square_zero_of_reduced_zero hp
        rw [show (2 : RingP p) = (2 : ℕ) by simp,
          reduce_primeGauss_eval hp hp2 j 2 (by omega), hzero]
      rw [hs, mul_zero]
  rw [he, mul_zero]

end OpenMath.A079727

/- Quadratic reciprocity for the prime classes in the A079727 conjecture. -/

namespace OpenMath.A079727

open ZMod

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem legendre_seven_of_pow_cube (a : ℤ) (ha : (a : ZMod 7) ≠ 0)
    (hpow : (a : ZMod 7) ^ 3 = -1) : legendreSym 7 a = -1 := by
  rcases legendreSym.eq_one_or_neg_one 7 ha with h | h
  · exfalso
    have hu := legendreSym.eq_pow 7 a
    rw [h, Int.cast_one, show 7 / 2 = 3 by decide, hpow] at hu
    exact (by decide : (1 : ZMod 7) ≠ -1) hu
  · exact h

theorem legendre_neg_seven {p : ℕ} [Fact p.Prime]
    (hclasses : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) : legendreSym p (-7) = -1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hpmod : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  have hs : legendreSym 7 (p : ℤ) = -1 := by
    rw [legendreSym.mod 7]
    change legendreSym 7 ((p : ℤ) % (7 : ℤ)) = -1
    rcases hclasses with h3 | h5 | h6
    · have hm : (p : ℤ) % 7 = 3 := by omega
      rw [hm]
      exact legendre_seven_of_pow_cube 3 (by decide) (by decide)
    · have hm : (p : ℤ) % 7 = 5 := by omega
      rw [hm]
      exact legendre_seven_of_pow_cube 5 (by decide) (by decide)
    · have hm : (p : ℤ) % 7 = 6 := by omega
      rw [hm]
      exact legendre_seven_of_pow_cube 6 (by decide) (by decide)
  have hqr : legendreSym p (7 : ℤ) =
      (-1) ^ (7 / 2 * (p / 2)) * legendreSym 7 (p : ℤ) :=
    legendreSym.quadratic_reciprocity' (p := 7) (q := p) (by decide) hp2
  rw [legendreSym.at_neg hp2, χ₄_eq_neg_one_pow hpmod, hqr, hs, ← mul_assoc,
    ← pow_add, show p / 2 + 7 / 2 * (p / 2) = 4 * (p / 2) by omega, pow_mul]
  norm_num

/-- Euler's criterion in the coefficient field, with no external character-sum axiom. -/
theorem neg_seven_pow_half {p : ℕ} (hp : p.Prime)
    (hclasses : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) :
    (-7 : ZMod p) ^ (p / 2) = -1 := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  have h := legendreSym.eq_pow p (-7)
  rw [legendre_neg_seven hclasses] at h
  simpa using h.symm

/-- If the square root changes sign under Frobenius, the twist factor
raised to the half-exponent differs from one by a unit. -/
theorem twist_factor_unit {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hodd : p % 2 = 1) (half d : R) (hhalf : 2 * half = 1)
    (hhalfp : half ^ p = half) (hdp : d ^ p = -d) (hd : IsUnit d) :
    IsUnit (((half * (1 + d)) ^ 2) ^ (p / 2) - 1) := by
  let μ := half * (1 + d)
  change IsUnit ((μ ^ 2) ^ (p / 2) - 1)
  have he : ((μ ^ 2) ^ (p / 2) - 1) * μ = -d := by
    rw [sub_mul, one_mul, ← pow_mul, ← pow_succ, show 2 * (p / 2) + 1 = p by omega]
    dsimp [μ]
    rw [mul_pow, hhalfp, add_pow_char, one_pow, hdp]
    linear_combination -d * hhalf
  exact isUnit_of_mul_isUnit_left (he ▸ hd.neg : IsUnit (((μ ^ 2) ^ (p / 2) - 1) * μ))

end OpenMath.A079727

/- The two local binomial identities in the 2-isogeny coefficient calculation. -/

namespace OpenMath.A079727

open ZMod

private theorem natCast_ne_zero_of_lt {p k : ℕ} (hk : 0 < k) (hkp : k < p) :
    (k : ZMod p) ≠ 0 := by
  intro h
  exact (not_le_of_gt hkp) (Nat.le_of_dvd hk ((ZMod.natCast_eq_zero_iff k p).1 h))

private theorem cast_choose_step (p n j : ℕ) :
    (((n.choose (j + 1)) : ℕ) : ZMod p) * (↑(j + 1) : ZMod p) =
      (n.choose j : ZMod p) * (↑(n - j) : ZMod p) := by
  simpa only [Nat.cast_mul] using
    congrArg (fun x : ℕ => (x : ZMod p)) (Nat.choose_succ_right_eq n j)

private theorem cast_choose_diag_step (p n j : ℕ) :
    (↑(n + 1) : ZMod p) * (n.choose j : ZMod p) =
      ((n + 1).choose (j + 1) : ZMod p) * (↑(j + 1) : ZMod p) := by
  simpa only [Nat.cast_mul] using
    congrArg (fun x : ℕ => (x : ZMod p)) (Nat.add_one_mul_choose_eq n j)

/-- Generalized negative-index binomial coefficients in characteristic p. -/
theorem cast_choose_complement {p : ℕ} [Fact p.Prime] (a j : ℕ) (haj : a + j < p) :
    ((p - 1 - a).choose j : ZMod p) = (-1) ^ j * ((a + j).choose j : ZMod p) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjp : j + 1 < p := by omega
    have hmul : (↑(j + 1) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by omega) hjp
    apply mul_right_cancel₀ hmul
    rw [cast_choose_step, ih (by omega), mul_assoc, ← Nat.add_assoc,
      mul_assoc ((-1 : ZMod p) ^ (j + 1)), ← cast_choose_diag_step, pow_succ]
    have hsub : (↑(p - 1 - a - j) : ZMod p) = -((a : ZMod p) + j + 1) := by
      rw [show p - 1 - a - j = p - (a + j + 1) by omega,
        Nat.cast_sub (by omega), ZMod.natCast_self]
      push_cast
      ring
    rw [hsub]
    push_cast
    ring

private theorem cast_central_step (p k : ℕ) :
    (↑(k + 1) : ZMod p) * (Nat.centralBinom (k + 1) : ZMod p) =
      2 * (2 * (k : ZMod p) + 1) * Nat.centralBinom k := by
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
    congrArg (fun x : ℕ => (x : ZMod p)) (Nat.succ_mul_centralBinom_succ k)

/-- The ordinary central binomial coefficient written as a half-index binomial modulo p. -/
theorem central_half_choose {p : ℕ} [Fact p.Prime] (hp : p % 2 = 1) (k : ℕ)
    (hk : k ≤ p / 2) :
    (-4 : ZMod p) ^ k * ((p / 2).choose k : ZMod p) = Nat.centralBinom k := by
  induction k with
  | zero => simp [Nat.centralBinom_zero]
  | succ k ih =>
    have hkp : k + 1 < p := by omega
    have hmul : (↑(k + 1) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by omega) hkp
    apply mul_right_cancel₀ hmul
    rw [mul_assoc, cast_choose_step, pow_succ, mul_comm (Nat.centralBinom (k + 1) : ZMod p),
      cast_central_step]
    have htwice : 2 * ((p / 2 : ℕ) : ZMod p) + 1 = 0 := by
      have hc : (↑(2 * (p / 2) + 1) : ZMod p) = 0 := by
        rw [show 2 * (p / 2) + 1 = p by omega, ZMod.natCast_self]
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hc
    have hsub : (-4 : ZMod p) * (↑(p / 2 - k) : ZMod p) = 2 * (2 * (k : ZMod p) + 1) := by
      rw [Nat.cast_sub (by omega)]
      linear_combination -2 * htwice
    calc
      _ = ((-4 : ZMod p) ^ k * ((p / 2).choose k : ZMod p)) *
          ((-4 : ZMod p) * (↑(p / 2 - k) : ZMod p)) := by ring
      _ = _ := by rw [ih (by omega), hsub, mul_comm]

end OpenMath.A079727

/- Translation and scaling of the characteristic-p coefficient of a cubic. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

noncomputable def hasseCoeff (p : ℕ) (P : R[X]) : R :=
  (P ^ (p / 2)).coeff (p - 1)

private theorem cast_high_choose_zero (p i : ℕ) [Fact p.Prime] [CharP R p]
    (hp : 3 < p) (hlo : p ≤ i) (hhi : i < 2 * p - 1) :
    (i.choose (p - 1) : R) = 0 := by
  have hm : i % p = i - p := by
    rw [Nat.mod_eq_sub_mod hlo, Nat.mod_eq_of_lt (by omega)]
  have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := i) (k := p - 1)
  rw [hm, Nat.mod_eq_of_lt (by omega : p - 1 < p),
    Nat.choose_eq_zero_of_lt (by omega : i - p < p - 1), zero_mul] at hc
  obtain ⟨k, hk⟩ := Nat.modEq_zero_iff_dvd.mp hc
  rw [hk, Nat.cast_mul, CharP.cast_eq_zero R p, zero_mul]

/-- Translation invariance; all higher coefficients have zero binomial multiplier in the field. -/
theorem hasse_translate (p : ℕ) [Fact p.Prime] [CharP R p] (hp : 3 < p)
    (P : R[X]) (hdeg : P.natDegree ≤ 3) (b : R) :
    hasseCoeff p (P.comp (X + C b)) = hasseCoeff p P := by
  unfold hasseCoeff
  rw [← pow_comp, comp_eq_sum_left, sum_def, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_add_C_pow]
  rw [Finset.sum_eq_single (p - 1)]
  · simp
  · intro i hi hne
    have hdegree : i ≤ 3 * (p / 2) := by
      have h := (le_natDegree_of_mem_supp i hi).trans
        (natDegree_pow_le.trans (Nat.mul_le_mul_left (p / 2) hdeg))
      simpa only [Nat.mul_comm (p / 2) 3] using h
    by_cases h : i < p - 1
    · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero, mul_zero]
    · have hlo : p ≤ i := by omega
      have hhi : i < 2 * p - 1 := by omega
      rw [cast_high_choose_zero p i hp hlo hhi, mul_zero, mul_zero]
  · intro hi
    rw [notMem_support_iff.mp hi, zero_mul]

/-- Substituting a scalar multiple of X multiplies each coefficient by a power. -/
theorem coeff_scale_X (P : R[X]) (l : R) (n : ℕ) :
    (P.comp (C l * X)).coeff n = l ^ n * P.coeff n := by
  rw [comp_eq_sum_left, sum_def, finsetSum_coeff]
  simp only [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single n]
  · simp [mul_comm]
  · intro i hi hne
    simp [Ne.symm hne]
  · intro h
    rw [notMem_support_iff.mp h]
    simp

/-- Comparing the cubic under a dilation compares Hasse coefficients. -/
theorem hasse_scale (p : ℕ) (hodd : p % 2 = 1) (P Q : R[X]) (l : R)
    (hl : IsUnit l) (hscale : Q.comp (C l * X) = C (l ^ 3) * P) :
    hasseCoeff p Q = l ^ (p / 2) * hasseCoeff p P := by
  have hp : p - 1 = 2 * (p / 2) := by omega
  have h := congrArg (hasseCoeff p) hscale
  unfold hasseCoeff at h ⊢
  rw [← pow_comp, coeff_scale_X, mul_pow, ← C_pow, coeff_C_mul] at h
  apply (hl.pow (p - 1)).mul_left_cancel
  rw [h, ← pow_mul, ← mul_assoc, ← pow_add]
  congr 2
  omega

end OpenMath.A079727

/- The modular coefficient equality behind the cubic's 2-isogeny. -/

namespace OpenMath.A079727

/-- The isogenous coefficient term equals the original coefficient term in the prime field. -/
theorem isogeny_choose_term {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1) (k : ℕ)
    (hk : 2 * k ≤ p / 2) :
    ((p / 2).choose k : ZMod p) * (-4) ^ k * (-1) ^ (p / 2 - 2 * k) *
        ((2 * (p / 2 - k)).choose (p / 2) : ZMod p) =
      ((p / 2).choose k : ZMod p) * ((p / 2 - k).choose k : ZMod p) := by
  let h := p / 2
  let t := h - 2 * k
  change (h.choose k : ZMod p) * (-4) ^ k * (-1) ^ t *
      ((2 * (h - k)).choose h : ZMod p) = (h.choose k : ZMod p) * ((h - k).choose k : ZMod p)
  have hs : h ≤ 2 * (h - k) := by omega
  have ht : 2 * (h - k) - h = t := by omega
  have hn : 2 * (h - k) = p - 1 - 2 * k := by omega
  have hsum : 2 * k + t = h := by omega
  have hcomp := cast_choose_complement (p := p) (2 * k) t (by omega)
  rw [hsum] at hcomp
  have heq :
      ((2 * (h - k)).choose h : ZMod p) = (-1) ^ t * (h.choose t : ZMod p) := by
    rw [← Nat.choose_symm hs, ht, hn]
    exact hcomp
  have hsign : (-1 : ZMod p) ^ t * (-1) ^ t = 1 := by rw [← mul_pow]; simp
  have hcentral := central_half_choose hodd k (by omega)
  have hchoose : (h.choose (2 * k) : ZMod p) * ((2 * k).choose k : ZMod p) =
      (h.choose k : ZMod p) * ((h - k).choose k : ZMod p) := by
    have hc := Nat.choose_mul (n := h) (k := 2 * k) (s := k) (by omega)
    rw [show 2 * k - k = k by omega] at hc
    simpa only [Nat.cast_mul] using congrArg (fun j : ℕ => (j : ZMod p)) hc
  calc
    _ = ((-4) ^ k * (h.choose k : ZMod p)) *
        (((-1 : ZMod p) ^ t * (-1) ^ t) * (h.choose t : ZMod p)) := by rw [heq]; ring
    _ = ((2 * k).choose k : ZMod p) * (h.choose (2 * k) : ZMod p) := by
      rw [hsign, one_mul, hcentral]
      unfold t
      rw [Nat.choose_symm hk, Nat.centralBinom_eq_two_mul_choose]
    _ = _ := by rw [mul_comm, hchoose]

/-- The same identity holds in any commutative ring of characteristic p. -/
theorem isogeny_choose_term_char {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (hodd : p % 2 = 1) (k : ℕ) (hk : 2 * k ≤ p / 2) :
    ((p / 2).choose k : R) * (-4) ^ k * (-1) ^ (p / 2 - 2 * k) *
        ((2 * (p / 2 - k)).choose (p / 2) : R) =
      ((p / 2).choose k : R) * ((p / 2 - k).choose k : R) := by
  simpa only [map_mul, map_pow, map_neg, map_one, map_ofNat, map_natCast] using
    congrArg (ZMod.castHom (dvd_refl p) R) (isogeny_choose_term hodd k hk)

end OpenMath.A079727

/- The characteristic-p coefficient invariant under the 2-isogeny parameter change. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

/-- A monic quadratic with prescribed lower coefficients. -/
noncomputable def quadratic (a b : R) : R[X] := X ^ 2 + C a * X + C b

private theorem coeff_add_C_block (P : R[X]) (b : R) (h n : ℕ) :
    ((P + C b) ^ h).coeff n =
      ∑ k ∈ Finset.range (h + 1), (h.choose k : R) * b ^ k * (P ^ (h - k)).coeff n := by
  rw [add_comm, add_pow, finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  have he : C b ^ k * P ^ (h - k) * ((h.choose k : ℕ) : R[X]) =
      C ((h.choose k : R) * b ^ k) * P ^ (h - k) := by
    simp only [map_mul, map_natCast, map_pow]
    ring
  rw [he, coeff_C_mul]

/-- The coefficient in the middle of the power of the original quadratic. -/
theorem coeff_quadratic_pow (a b : R) (h : ℕ) :
    (quadratic a b ^ h).coeff h =
      ∑ k ∈ Finset.range (h + 1), (h.choose k : R) * ((h - k).choose k : R) *
        a ^ (h - 2 * k) * b ^ k := by
  have he : quadratic a b = X * (X + C a) + C b := by unfold quadratic; ring
  rw [he, coeff_add_C_block]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range_succ_iff.mp hk
  rw [mul_pow, coeff_X_pow_mul', if_pos (Nat.sub_le _ _),
    show h - (h - k) = k by omega, coeff_X_add_C_pow,
    show h - k - k = h - 2 * k by omega]
  ring

/-- Expansion after the quadratic's coefficients change by the 2-isogeny map. -/
theorem coeff_isogenous_pow (a b : R) (h : ℕ) :
    (quadratic (-2 * a) (a ^ 2 - 4 * b) ^ h).coeff h =
      ∑ k ∈ Finset.range (h + 1), (h.choose k : R) * (-4 * b) ^ k *
        (-a) ^ (2 * (h - k) - h) * ((2 * (h - k)).choose h : R) := by
  have he : quadratic (-2 * a) (a ^ 2 - 4 * b) =
      (X + C (-a)) ^ 2 + C (-4 * b) := by
    simp only [quadratic, map_neg, map_mul, map_pow, map_sub, map_ofNat]
    ring
  rw [he, coeff_add_C_block]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← pow_mul, coeff_X_add_C_pow]
  ring

/-- In characteristic p, the 2-isogeny parameter change preserves the middle coefficient. -/
theorem coeff_isogeny (p : ℕ) [Fact p.Prime] [CharP R p] (hodd : p % 2 = 1)
    (a b : R) :
    (quadratic (-2 * a) (a ^ 2 - 4 * b) ^ (p / 2)).coeff (p / 2) =
      (quadratic a b ^ (p / 2)).coeff (p / 2) := by
  rw [coeff_isogenous_pow, coeff_quadratic_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : 2 * k ≤ p / 2
  · have hcoef := isogeny_choose_term_char (R := R) hodd k hk
    rw [show 2 * (p / 2 - k) - p / 2 = p / 2 - 2 * k by omega]
    rw [mul_pow]
    rw [show (-a) ^ (p / 2 - 2 * k) = (-1) ^ (p / 2 - 2 * k) * a ^ (p / 2 - 2 * k)
      by rw [← mul_pow, neg_one_mul]]
    linear_combination (a ^ (p / 2 - 2 * k) * b ^ k) * hcoef
  · have hp : Nat.Prime p := Fact.out
    have hpos : 0 < p / 2 := Nat.div_pos hp.two_le (by decide)
    have h1 : (2 * (p / 2 - k)).choose (p / 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (p / 2 - k).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [h1, h2, Nat.cast_zero, mul_zero, zero_mul]

/-- The coefficient of the cubic reduces to the middle coefficient of its quadratic factor. -/
theorem hasse_X_quadratic (p : ℕ) (hodd : p % 2 = 1) (a b : R) :
    hasseCoeff p (X * quadratic a b) = (quadratic a b ^ (p / 2)).coeff (p / 2) := by
  rw [hasseCoeff, mul_pow, show p - 1 = p / 2 + p / 2 by omega, coeff_X_pow_mul]

/-- The p-th characteristic coefficient is unchanged under the 2-isogeny parameters. -/
theorem hasse_isogeny (p : ℕ) [Fact p.Prime] [CharP R p] (hodd : p % 2 = 1)
    (a b : R) :
    hasseCoeff p (X * quadratic (-2 * a) (a ^ 2 - 4 * b)) =
      hasseCoeff p (X * quadratic a b) := by
  rw [hasse_X_quadratic p hodd, hasse_X_quadratic p hodd]
  exact coeff_isogeny p hodd a b

end OpenMath.A079727

/- The explicit translations and twist of X³+21X²+112X. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

/-- A monic short cubic. -/
noncomputable def shortCubic (a b : R) : R[X] := X ^ 3 + C a * X + C b

private theorem degree_X_quad (a b : R) : (X * quadratic a b).natDegree ≤ 3 := by
  have hX : (X : R[X]).natDegree ≤ 1 := natDegree_X_le
  have hX2 : (X ^ 2 : R[X]).natDegree ≤ 2 :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ hX)
  have hC (r : R) : (C r).natDegree = 0 := natDegree_C _
  have hAX : (C a * X).natDegree ≤ 1 := by
    exact natDegree_mul_le.trans (by rw [hC, zero_add]; exact hX)
  have hquad : (quadratic a b).natDegree ≤ 2 := by
    unfold quadratic
    exact natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le hX2 (by omega)) (by simp)
  exact natDegree_mul_le.trans (by omega)

private theorem comp_X_quad (a b u : R) :
    (X * quadratic a b).comp (X + C u) =
      X ^ 3 + C (3 * u + a) * X ^ 2 + C (3 * u ^ 2 + 2 * a * u + b) * X +
        C (u ^ 3 + a * u ^ 2 + b * u) := by
  simp only [quadratic, mul_comp, add_comp, pow_comp, C_comp, X_comp,
    map_add, map_mul, map_pow, map_ofNat]
  ring

private theorem scale_short (a b l : R) :
    (shortCubic (a * l ^ 2) (b * l ^ 3)).comp (C l * X) =
      C (l ^ 3) * shortCubic a b := by
  simp only [shortCubic, mul_comp, add_comp, pow_comp, C_comp, X_comp, map_mul, map_pow]
  ring

/-- The Hasse coefficient vanishes whenever the displayed quadratic root
is sent to its negative by Frobenius. -/
theorem cubic_hasse_zero (p : ℕ) [Fact p.Prime] [CharP R p]
    (hp : 3 < p) (hodd : p % 2 = 1)
    (half d : R) (hhalf : 2 * half = 1) (hhalfp : half ^ p = half)
    (hd : d ^ 2 = -7) (hdp : d ^ p = -d) (hdu : IsUnit d) :
    hasseCoeff p (X * quadratic (21 : R) 112) = 0 := by
  let P := X * quadratic (21 : R) 112
  let A := half * (-21 + 3 * d)
  let B := half * (-7 - 21 * d)
  let u := half * (-21 + d)
  let l := half * (d - 3)
  let v := d - 7
  let S := shortCubic (-35 : R) (-98)
  change hasseCoeff p P = 0
  have hu2 : IsUnit (2 : R) := isUnit_of_mul_isUnit_left (hhalf ▸ isUnit_one)
  have hh2 : 4 * half ^ 2 = 1 := by
    calc
      _ = (2 * half) ^ 2 := by ring
      _ = _ := by rw [hhalf, one_pow]
  have hu' : 2 * u = -21 + d := by
    unfold u
    linear_combination (-21 + d) * hhalf
  have hu_sq : 2 * u ^ 2 = 217 - 21 * d := by
    unfold u
    linear_combination (2 * half ^ 2) * hd + (217 - 21 * d) * hh2
  have hA : 3 * u + 21 = A := by
    unfold A u
    linear_combination -21 * hhalf
  have hB : 3 * u ^ 2 + 42 * u + 112 = B := by
    apply hu2.mul_left_cancel
    unfold B
    linear_combination 3 * hu_sq + 42 * hu' - (-7 - 21 * d) * hhalf
  have hroot : u ^ 2 + 21 * u + 112 = 0 := by
    apply hu2.mul_left_cancel
    linear_combination hu_sq + 21 * hu'
  have hfirst : P.comp (X + C u) = X * quadratic A B := by
    dsimp only [P]
    rw [comp_X_quad, hA, show (2 : R) * 21 = 42 by ring, hB]
    have h : u ^ 3 + 21 * u ^ 2 + 112 * u = 0 := by
      linear_combination u * hroot
    rw [h]
    simp only [quadratic, map_zero, add_zero]
    ring
  have hbase : P.comp (X + C (-7)) = S := by
    dsimp only [P]
    rw [comp_X_quad, show (3 : R) * (-7) + 21 = 0 by ring,
      show (3 : R) * (-7)^2 + 2*21*(-7) + 112 = -35 by ring,
      show (-7 : R)^3 + 21*(-7)^2 + 112*(-7) = -98 by ring]
    simp [S, shortCubic]
  have hA' : -2 * A = 21 - 3 * d := by
    unfold A
    linear_combination -(-21 + 3 * d) * hhalf
  have hAsq : 2 * A ^ 2 = 189 - 63 * d := by
    unfold A
    linear_combination (18 * half ^ 2) * hd + (189 - 63 * d) * hh2
  have hB' : 2 * (A ^ 2 - 4 * B) = 217 + 21 * d := by
    unfold B
    linear_combination hAsq - 4 * (-7 - 21 * d) * hhalf
  have hl2 : 2 * l ^ 2 = 1 - 3 * d := by
    unfold l
    linear_combination (2 * half ^ 2) * hd + (1 - 3 * d) * hh2
  have hl3 : 2 * l ^ 3 = 9 + 5 * d := by
    have hl2' : l ^ 2 = half * (1 - 3 * d) := by
      apply hu2.mul_left_cancel
      linear_combination hl2 - (1 - 3 * d) * hhalf
    rw [pow_succ, hl2']
    unfold l
    linear_combination (-6 * half ^ 2) * hd + (9 + 5 * d) * hh2
  have hzeroQuad : 3 * v + -2 * A = 0 := by rw [hA']; unfold v; ring
  have hv2 : v ^ 2 = 42 - 14 * d := by
    unfold v
    linear_combination hd
  have hv3 : v ^ 3 = 140 * d - 196 := by
    rw [pow_succ, hv2]
    unfold v
    linear_combination -14 * hd
  have hlin : 3 * v ^ 2 + 2 * (-2 * A) * v + (A ^ 2 - 4 * B) = -35 * l ^ 2 := by
    have h := congrArg (fun x : R => 4 * v * x) hzeroQuad
    apply hu2.mul_left_cancel
    linear_combination h + hB' + 35 * hl2 - 6 * hv2
  have hconst : v ^ 3 + (-2 * A) * v ^ 2 + (A ^ 2 - 4 * B) * v = -98 * l ^ 3 := by
    have h := congrArg (fun x : R => (2 * v ^ 2) * x) hzeroQuad
    apply hu2.mul_left_cancel
    unfold v at h ⊢
    unfold v at hv3
    linear_combination h + (d - 7) * hB' + 98 * hl3 - 4 * hv3 + 21 * hd
  let Q := X * quadratic (-2 * A) (A ^ 2 - 4 * B)
  let W := shortCubic (-35 * l ^ 2) (-98 * l ^ 3)
  have hshift : Q.comp (X + C v) = W := by
    dsimp only [Q]
    rw [comp_X_quad, hzeroQuad, hlin, hconst]
    simp only [W, shortCubic, map_zero, zero_mul, add_zero]
  have hiso := hasse_isogeny p hodd A B
  have hst := hasse_translate p hp P (degree_X_quad 21 112) u
  have hbas := hasse_translate p hp P (degree_X_quad 21 112) (-7)
  have hsh := hasse_translate p hp Q (degree_X_quad (-2 * A) (A ^ 2 - 4 * B)) v
  rw [hfirst] at hst
  rw [hbase] at hbas
  rw [hshift] at hsh
  have hlunit : IsUnit l := by
    have h : l * (half * (-d - 3)) = 4 := by
      unfold l
      linear_combination -half ^ 2 * hd + 4 * hh2
    have hfour : IsUnit (4 : R) := by
      rw [show (4 : R) = 2 ^ 2 by ring]
      exact hu2.pow 2
    exact isUnit_of_mul_isUnit_left (h.symm ▸ hfour)
  have hscale := hasse_scale p hodd S W l hlunit (scale_short (-35) (-98) l)
  have hsame : hasseCoeff p P = l ^ (p / 2) * hasseCoeff p P := by
    calc
      _ = hasseCoeff p (X * quadratic A B) := hst.symm
      _ = hasseCoeff p Q := hiso.symm
      _ = hasseCoeff p W := hsh.symm
      _ = _ := by rw [hscale, hbas]
  have hl_square : (half * (1 + d)) ^ 2 = l := by
    apply hu2.mul_left_cancel
    unfold l
    linear_combination 2 * half ^ 2 * hd + (d - 3) * hh2 - (d - 3) * hhalf
  have hun := twist_factor_unit p hodd half d hhalf hhalfp hdp hdu
  rw [hl_square] at hun
  apply hun.mul_left_cancel
  rw [sub_mul, one_mul, ← hsame, sub_self, mul_zero]

end OpenMath.A079727

/- The inert-prime Hasse vanishing in the actual finite coefficient field. -/

open Polynomial

namespace OpenMath.A079727

private abbrev CMAlgebra (p : ℕ) := QuadraticAlgebra (ZMod p) (-7) 0

/-- The Hasse coefficient of the cubic, over the prime field, vanishes in the inert classes. -/
theorem prime_hasse_vanishing {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hclasses : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) :
    (quadratic (21 : ZMod p) 112 ^ (p / 2)).coeff (p / 2) = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP (CMAlgebra p) p :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  let f := algebraMap (ZMod p) (CMAlgebra p)
  let d : CMAlgebra p := QuadraticAlgebra.omega
  let half : CMAlgebra p := f ((2 : ZMod p)⁻¹)
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr (by omega)
  have hd : d ^ 2 = f (-7) := by
    dsimp only [d]
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  have hd' : d ^ 2 = -7 := by simpa only [map_neg, map_ofNat, f] using hd
  have hpow : (d ^ 2) ^ (p / 2) = -1 := by
    rw [hd, ← map_pow, neg_seven_pow_half hp hclasses, map_neg, map_one]
  have hdp : d ^ p = -d := by
    calc
      _ = (d ^ 2) ^ (p / 2) * d := by rw [← pow_mul, ← pow_succ, show 2 * (p / 2) + 1 = p by omega]
      _ = _ := by rw [hpow, neg_one_mul]
  have hdu : IsUnit d := by
    have hU : IsUnit ((d ^ 2) ^ (p / 2)) := by rw [hpow]; exact isUnit_one.neg
    have hp0 : p / 2 ≠ 0 := by omega
    obtain ⟨q, hq⟩ : ∃ q : ℕ, p / 2 = q + 1 := ⟨p / 2 - 1, by omega⟩
    rw [hq, pow_succ'] at hU
    have hh : IsUnit (d ^ 2) := isUnit_of_mul_isUnit_left hU
    rw [pow_two] at hh
    exact isUnit_of_mul_isUnit_left hh
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).1 h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  have hhalf : 2 * half = 1 := by
    unfold half
    rw [← map_ofNat f, ← map_mul, mul_inv_cancel₀ htwo, map_one]
  have hhalfp : half ^ p = half := by
    unfold half
    rw [← map_pow, ZMod.pow_card]
  have h := cubic_hasse_zero p hp3 hodd half d hhalf hhalfp hd' hdp hdu
  rw [hasse_X_quadratic p hodd] at h
  apply QuadraticAlgebra.algebraMap_injective (a := (-7 : ZMod p)) (b := (0 : ZMod p))
  rw [map_zero]
  change f ((quadratic (21 : ZMod p) 112 ^ (p / 2)).coeff (p / 2)) = 0
  rw [← coeff_map, Polynomial.map_pow]
  have hmap21 : ((21 : (ZMod p)[X]).map f) = 21 := by
    change (C (21 : ZMod p)).map f = C (21 : CMAlgebra p)
    rw [Polynomial.map_C, map_ofNat]
  have hmap112 : ((112 : (ZMod p)[X]).map f) = 112 := by
    change (C (112 : ZMod p)).map f = C (112 : CMAlgebra p)
    rw [Polynomial.map_C, map_ofNat]
  have hm : (quadratic (21 : ZMod p) 112).map f = quadratic (21 : CMAlgebra p) 112 := by
    simp only [quadratic, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, map_ofNat, hmap21, hmap112]
  rw [hm]
  exact h

end OpenMath.A079727

/- The binomial convolution in the terminating Pfaff transformation. -/

namespace OpenMath.A079727

open scoped BigOperators

theorem pfaff_binomial_coeff (d n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (d.choose k) ^ 2 * (d - k).choose (n - k)) =
      d.choose n * (d + n).choose n := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn := Finset.mem_range_succ_iff.mp hk
  rw [Nat.choose_symm hkn]
  have h := Nat.choose_mul (n := d) (k := n) (s := k) hkn
  calc
    _ = d.choose k * (d.choose k * (d - k).choose (n - k)) := by ring
    _ = d.choose k * (d.choose n * n.choose k) := by rw [← h]
    _ = _ := by ring

end OpenMath.A079727

/- The terminating Pfaff transform as an exact polynomial identity. -/

open Polynomial

namespace OpenMath.A079727

variable {R : Type*} [CommRing R]

/-- The standard shifted Legendre polynomial over a coefficient ring. -/
noncomputable def legendreSeries (d : ℕ) : R[X] :=
  truncateSeries d (fun n => (-1 : R)^n * (d.choose n : R) * ((d + n).choose n : R))

private theorem coeff_one_sub_X_pow (m n : ℕ) :
    ((1 - X : R[X]) ^ m).coeff n = (-1 : R) ^ n * (m.choose n : R) := by
  have he : (1 - X : R[X]) = C (-1 : R) * X + 1 := by simp; ring
  rw [he, add_pow, finsetSum_coeff]
  simp only [one_pow, mul_one, mul_pow, ← C_pow, coeff_mul_natCast, coeff_C_mul_X_pow]
  by_cases hn : n ≤ m
  · simp [hn]
  · have hz : m.choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hn, hz]

private theorem coeff_pfaff_term (d k n : ℕ) :
    (C ((d.choose k : R)^2) * ((-X)^k * (1-X)^(d-k))).coeff n =
      if k ≤ n then (-1 : R)^n * (d.choose k : R)^2 * ((d-k).choose (n-k) : R) else 0 := by
  have hx : ((-X : R[X]) ^ k) = C ((-1 : R)^k) * X^k := by
    rw [map_pow, ← mul_pow]
    simp
  rw [hx]
  have hprod : C ((d.choose k : R)^2) * ((C ((-1 : R)^k) * X^k) * (1-X)^(d-k)) =
      C ((d.choose k : R)^2 * (-1 : R)^k) * (X^k * (1-X)^(d-k)) := by
    rw [map_mul]
    ring
  rw [hprod, coeff_C_mul, coeff_X_pow_mul']
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, coeff_one_sub_X_pow]
    have he : (-1 : R)^k * (-1 : R)^(n-k) = (-1 : R)^n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    calc
      _ = ((-1 : R)^k * (-1 : R)^(n-k)) * (d.choose k : R)^2 *
          ((d-k).choose (n-k) : R) := by ring
      _ = _ := by rw [he, if_pos hkn]
  · rw [if_neg hkn, if_neg hkn, mul_zero]

/-- After clearing denominators, Pfaff is the exact coefficient convolution. -/
theorem pfaff_polynomial (d : ℕ) :
    (∑ k ∈ Finset.range (d + 1),
      C ((d.choose k : R)^2) * ((-X)^k * (1-X)^(d-k))) = legendreSeries d := by
  ext n
  rw [finsetSum_coeff]
  simp_rw [coeff_pfaff_term]
  rw [← Finset.sum_filter]
  let t := fun k : ℕ => (-1 : R)^n * (d.choose k : R)^2 * ((d-k).choose (n-k) : R)
  have hs : (∑ k ∈ (Finset.range (d+1)).filter (· ≤ n), t k) =
      ∑ k ∈ Finset.range (n+1), t k := by
    rcases le_total n d with hnd | hdn
    · have he : (Finset.range (d+1)).filter (· ≤ n) = Finset.range (n+1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [he]
    · have he : (Finset.range (d+1)).filter (· ≤ n) = Finset.range (d+1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [he]
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro k hk hkd
        have h := Nat.choose_eq_zero_of_lt (n := d) (k := k) (by
          simp only [Finset.mem_range] at hkd; omega)
        simp [t, h]
  change (∑ k ∈ (Finset.range (d+1)).filter (· ≤ n), t k) = _
  rw [hs]
  unfold t
  simp only [mul_assoc, ← Finset.mul_sum, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_sum]
  rw [pfaff_binomial_coeff, Nat.cast_mul, legendreSeries, coeff_truncateSeries]
  by_cases hnd : n ≤ d
  · rw [if_pos hnd, mul_assoc]
  · simp [hnd, Nat.choose_eq_zero_of_lt (by omega : d < n)]

/-- Evaluating Pfaff where -x=y(1-x) gives the squared-binomial sum. -/
theorem eval_pfaff (d : ℕ) (x y : R) (hxy : -x = (1-x)*y) :
    (legendreSeries d).eval x =
      (1-x)^d * ∑ k ∈ Finset.range (d+1), (d.choose k : R)^2 * y^k := by
  rw [← pfaff_polynomial]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_neg, eval_X, eval_sub, eval_one, hxy,
    mul_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h := Finset.mem_range_succ_iff.mp hk
  calc
    _ = (1-x)^(k+(d-k)) * ((d.choose k : R)^2 * y^k) := by rw [pow_add]; ring
    _ = _ := by rw [Nat.add_sub_of_le h]

end OpenMath.A079727

/- The Legendre-coefficient ratio for a cubic in the prime field. -/

namespace OpenMath.A079727

private theorem central_choose_step (h k : ℕ) :
    (k + 1) ^ 2 * (h.choose (2 * (k + 1)) * Nat.centralBinom (k + 1)) =
      (h - 2 * k) * (h - (2 * k + 1)) * (h.choose (2 * k) * Nat.centralBinom k) := by
  have ha : (2 * k + 2) * h.choose (2 * k + 2) =
      h.choose (2 * k + 1) * (h - (2 * k + 1)) := by
    simpa only [mul_comm, Nat.add_assoc] using Nat.choose_succ_right_eq h (2 * k + 1)
  have hb : (2 * k + 1) * h.choose (2 * k + 1) = h.choose (2 * k) * (h - 2 * k) := by
    simpa only [mul_comm] using Nat.choose_succ_right_eq h (2 * k)
  rw [show 2 * (k + 1) = 2 * k + 2 by omega]
  calc
    _ = ((k + 1) * Nat.centralBinom (k + 1)) * ((k + 1) * h.choose (2 * k + 2)) := by ring
    _ = ((2 * k + 2) * h.choose (2 * k + 2)) * (2 * k + 1) * Nat.centralBinom k := by
      rw [Nat.succ_mul_centralBinom_succ]
      ring
    _ = ((2 * k + 1) * h.choose (2 * k + 1)) * (h - (2 * k + 1)) * Nat.centralBinom k := by
      rw [ha]
      ring
    _ = _ := by rw [hb]; ring

private theorem legendre_choose_step (d k : ℕ) :
    (k + 1) ^ 2 * (d.choose (k + 1) * (d + (k + 1)).choose (k + 1)) =
      (d - k) * (d + k + 1) * (d.choose k * (d + k).choose k) := by
  calc
    _ = (d.choose (k + 1) * (k + 1)) * ((d + k + 1).choose (k + 1) * (k + 1)) := by
      rw [Nat.add_assoc]
      ring
    _ = _ := by
      rw [Nat.choose_succ_right_eq, ← Nat.add_one_mul_choose_eq]
      ring

private theorem legendre_factor_match {p : ℕ} (hodd : p % 2 = 1) (k : ℕ) :
    (((p / 2 : ℕ) : ZMod p) - 2 * (k : ZMod p)) *
      (((p / 2 : ℕ) : ZMod p) - (2 * (k : ZMod p) + 1)) =
      -4 * (((p / 4 : ℕ) : ZMod p) - (k : ZMod p)) *
        (((p / 4 : ℕ) : ZMod p) + (k : ZMod p) + 1) := by
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with hr | hr
  · have hn : 4 * (p / 4) + 1 = p := by omega
    have hb : (4 : ZMod p) * ((p / 4 : ℕ) : ZMod p) + 1 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_self]
        using congrArg (fun n : ℕ => (n : ZMod p)) hn
    rw [show p / 2 = 2 * (p / 4) by omega, Nat.cast_mul, Nat.cast_ofNat]
    linear_combination 2 * (((p / 4 : ℕ) : ZMod p) - (k : ZMod p)) * hb
  · have hn : 4 * (p / 4) + 3 = p := by omega
    have hb : (4 : ZMod p) * ((p / 4 : ℕ) : ZMod p) + 3 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self]
        using congrArg (fun n : ℕ => (n : ZMod p)) hn
    rw [show p / 2 = 2 * (p / 4) + 1 by omega, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    linear_combination 2 * (((p / 4 : ℕ) : ZMod p) - (k : ZMod p)) * hb

/-- The cubic coefficient terms become the shifted Legendre polynomial terms modulo p. -/
theorem legendre_binomial_bridge {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1) (k : ℕ)
    (hk : k ≤ p / 4) :
    ((p / 2).choose (2 * k) : ZMod p) * (Nat.centralBinom k : ZMod p) =
      (-4 : ZMod p) ^ k * ((p / 4).choose k : ZMod p) * ((p / 4 + k).choose k : ZMod p) := by
  induction k with
  | zero => simp [Nat.centralBinom_zero]
  | succ k ih =>
    have hlt : ↑(k + 1) ≠ (0 : ZMod p) := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff (k + 1) p).1 h
      have hh := Nat.le_of_dvd (by omega : 0 < k + 1) hd
      omega
    have hne : ((k : ZMod p) + 1) ^ 2 ≠ 0 := pow_ne_zero _ (by
      simpa only [Nat.cast_add, Nat.cast_one] using hlt)
    apply mul_left_cancel₀ hne
    have hU := congrArg (fun n : ℕ => (n : ZMod p)) (central_choose_step (p / 2) k)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
      Nat.cast_sub (by omega : 2 * k ≤ p / 2),
      Nat.cast_sub (by omega : 2 * k + 1 ≤ p / 2)] at hU
    have hV := congrArg (fun n : ℕ => (n : ZMod p)) (legendre_choose_step (p / 4) k)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
      Nat.cast_sub (by omega : k ≤ p / 4)] at hV
    rw [hU, legendre_factor_match hodd k, ih (by omega), pow_succ]
    linear_combination ((-4 : ZMod p) ^ k * 4) * hV

end OpenMath.A079727

/- The prime-field evaluation of the square polynomial is zero at 64. -/

open Polynomial

namespace OpenMath.A079727

private theorem reduce_choice_mul (p h k : ℕ) :
    (h.choose k : ZMod p) * ((h - k).choose k : ZMod p) =
      (h.choose (2*k) : ZMod p) * (Nat.centralBinom k : ZMod p) := by
  have hh := Nat.choose_mul (n := h) (k := 2*k) (s := k) (by omega)
  rw [show 2*k-k = k by omega] at hh
  simpa only [Nat.cast_mul, Nat.centralBinom_eq_two_mul_choose] using
    (congrArg (fun n : ℕ => (n : ZMod p)) hh).symm

private theorem scalar_match {p : ℕ} [Fact p.Prime] (x : ZMod p)
    (hval : (21 : ZMod p)^2 * x = 448) (h k : ℕ) (hk : 2*k ≤ h) :
    (-4 : ZMod p)^k * (21 : ZMod p)^(h-2*k) * (112 : ZMod p)^k =
      (21 : ZMod p)^h * (-1 : ZMod p)^k * x^k := by
  have he : (-4 : ZMod p) * 112 = -1 * (21 : ZMod p)^2 * x := by
    linear_combination hval
  calc
    _ = (21 : ZMod p)^(h-2*k) * ((-4 : ZMod p) * 112)^k := by rw [mul_pow]; ring
    _ = ((21 : ZMod p)^(h-2*k) * (21 : ZMod p)^(2*k)) * ((-1 : ZMod p)^k*x^k) := by
      rw [he, mul_pow, mul_pow, ← pow_mul]
      ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hk]; ring

private theorem cubic_legendre_eval {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1)
    (x : ZMod p) (hx : (21 : ZMod p)^2 * x = 448) :
    (quadratic (21 : ZMod p) 112 ^ (p / 2)).coeff (p / 2) =
      (21 : ZMod p)^(p / 2) * (legendreSeries (p / 4)).eval x := by
  let h := p / 2
  let d := p / 4
  rw [coeff_quadratic_pow]
  let f := fun k : ℕ => (h.choose k : ZMod p) * ((h-k).choose k : ZMod p) *
    (21 : ZMod p)^(h-2*k) * (112 : ZMod p)^k
  change ∑ k ∈ Finset.range (h+1), f k = (21 : ZMod p)^h * (legendreSeries d).eval x
  have hsum : (∑ k ∈ Finset.range (d+1), f k) = ∑ k ∈ Finset.range (h+1), f k := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hin
    have hd : d < i := by simp only [Finset.mem_range] at hin; omega
    have hz : (h - i).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [f, hz]
  rw [← hsum]
  simp only [legendreSeries, truncateSeries, eval_finsetSum, eval_mul, eval_pow, eval_C, eval_X,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := Finset.mem_range_succ_iff.mp hk
  unfold f
  rw [reduce_choice_mul, legendre_binomial_bridge hodd k hk']
  have hs := scalar_match x hx h k (by omega)
  linear_combination ((d.choose k : ZMod p) * ((d+k).choose k : ZMod p)) * hs

private theorem cast_three_ne_zero {p : ℕ} (hp : 3 < p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff 3 p).mp h
  exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide) hd)

private theorem cast_seven_ne_zero {p : ℕ} (hp : p.Prime) (hne : p ≠ 7) : (7 : ZMod p) ≠ 0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff 7 p).mp h
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with hh | hh
  · exact hp.ne_one hh
  · exact hne hh

/-- All three inert congruence classes give zero for the squared-binomial polynomial. -/
theorem prime_square_eval_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hclasses : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) :
    binomialSquareEval p = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp7 : p ≠ 7 := by rintro rfl; omega
  have h3 := cast_three_ne_zero hp3
  have h7 := cast_seven_ne_zero hp hp7
  have h21 : (21 : ZMod p) ≠ 0 := by
    rw [show (21 : ZMod p) = 3 * 7 by ring]
    exact mul_ne_zero h3 h7
  have h63 : (63 : ZMod p) ≠ 0 := by
    rw [show (63 : ZMod p) = 3 ^ 2 * 7 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h7
  let x : ZMod p := 64 / 63
  have hx : x * 63 = 64 := div_mul_cancel₀ _ h63
  have hxval : (21 : ZMod p)^2 * x = 448 := by linear_combination 7 * hx
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr (by omega)
  have hz := prime_hasse_vanishing hp hp3 hclasses
  rw [cubic_legendre_eval hodd x hxval] at hz
  have hz' := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ h21)
  have hxy : -x = (1-x) * 64 := by
    apply mul_right_cancel₀ h63
    linear_combination 63 * hx
  have hx1 : 1 - x ≠ 0 := by
    have hf : (1 - x) * 63 = -1 := by linear_combination -hx
    intro h
    rw [h, zero_mul] at hf
    exact (neg_ne_zero.mpr one_ne_zero) hf.symm
  rw [eval_pfaff _ x 64 hxy] at hz'
  exact (mul_eq_zero.mp hz').resolve_left (pow_ne_zero _ hx1)

end OpenMath.A079727

/- The exact squarefree-product theorem after the two block cases. -/

open scoped BigOperators

namespace OpenMath.A079727

theorem bala_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a ((∏ p ∈ S, p - 1) / 2) := by
  apply conjecture4_of_blocks _ S hS
  intro p hp j
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two hp.1).mpr (by
      intro h
      subst p
      have h := hp.2
      omega)
  have hh := hp.1.two_le
  by_cases hp3 : p = 3
  · subst p
    exact half_block_three j
  · have hp3' : 3 < p := by omega
    rw [show (p + 1) / 2 = p / 2 + 1 by omega]
    exact all_half_blocks_of_eval_zero hp.1 (by omega) j
      (prime_square_eval_zero hp.1 hp3' hp.2)

end OpenMath.A079727

theorem OMA.solution : type_of% @OeisA79727.conjecture4 := by
  exact OpenMath.A079727.bala_squarefree
