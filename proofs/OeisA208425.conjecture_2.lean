import FormalConjectures.OEIS.«208425»
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Choose.Lucas

/-!
# The A208425 prime-length binomial sum

For primes congruent to one modulo three, the exceptional term gives the
required binomial coefficient modulo the square of the prime. A finite-field
polynomial identity accounts for the remaining terms.
-/

namespace A208425Regular

open Polynomial

variable {p : ℕ}

abbrev F (p : ℕ) := ZMod p
abbrev P (p : ℕ) := Polynomial (F p)

noncomputable def yy : P p := 1 - X

noncomputable def uu : P p := X * yy

noncomputable def dd (r : ℕ) (g : P p) : P p :=
  uu * derivative g - C (r : F p) * (1 - 2 * X) * g

theorem cast_ne_zero_of_pos_lt {j : ℕ} (hj : 0 < j) (hjp : j < p) : (j : F p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact fun h => (Nat.le_of_dvd hj h).not_gt hjp

theorem cast_difference_ne_zero {i r : ℕ} (hr : r < p) (hi : i < p + r) (hir : i ≠ r) :
    (i : F p) - (r : F p) ≠ 0 := by
  rcases lt_or_gt_of_ne hir with h | h
  · have hh := cast_ne_zero_of_pos_lt (p := p) (j := r - i) (by omega) (by omega)
    rw [Nat.cast_sub h.le] at hh
    rwa [sub_ne_zero, ne_comm, ← sub_ne_zero] at hh
  · have hh := cast_ne_zero_of_pos_lt (p := p) (j := i - r) (by omega) (by omega)
    rwa [Nat.cast_sub h.le] at hh

theorem derivative_const_of_lt [Fact p.Prime] {g : P p} (hg : g.natDegree < p)
    (hd : g.derivative = 0) : g = C (g.coeff 0) := by
  ext i
  cases i with
  | zero => simp
  | succ i =>
    rw [coeff_C_succ]
    by_cases h : i + 1 ≤ g.natDegree
    · have hh := congrArg (fun q : P p => q.coeff i) hd
      simp only [coeff_derivative, coeff_zero] at hh
      rcases mul_eq_zero.mp hh with hz | hz
      · exact hz
      · exact (cast_ne_zero_of_pos_lt (p := p) (j := i + 1) (by omega) (by omega) (by simpa using hz)).elim
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem d_u : derivative (uu : P p) = 1 - 2 * X := by
  simp [uu, yy, derivative_mul]
  ring

theorem d_y : derivative (yy : P p) = -1 := by simp [yy]

theorem u_derivative_pow (k : ℕ) :
    (uu : P p) * derivative (uu ^ k) = C (k : F p) * derivative uu * uu ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, derivative_mul, mul_add, ← mul_assoc, ih, Nat.cast_succ, map_add, map_one]
    ring

theorem dd_const_mul_upow (r k : ℕ) (z : F p) :
    dd r (C z * uu ^ k) = C (z * ((k : F p) - (r : F p))) * (1 - 2 * X) * uu ^ k := by
  unfold dd
  rw [derivative_mul, derivative_C, zero_mul, zero_add]
  rw [show (uu : P p) * (C z * derivative (uu ^ k)) =
      C z * (uu * derivative (uu ^ k)) by ring, u_derivative_pow, d_u]
  simp only [map_mul, map_sub]
  ring

theorem dd_sub (r : ℕ) (g h : P p) :
    dd r (g - h) = dd r g - dd r h := by
  simp [dd, derivative_sub, mul_sub]
  ring

theorem dd_form (r : ℕ) (g : P p) :
    dd r g = X * derivative g - X * (X * derivative g) - C (r : F p) * g +
      C (2 * (r : F p)) * (X * g) := by
  simp [dd, uu, yy, map_mul, C_ofNat]
  ring

theorem dd_coeff_zero (r : ℕ) (g : P p) : (dd r g).coeff 0 = -(r : F p) * g.coeff 0 := by
  rw [dd_form]
  simp

theorem dd_coeff_succ (r k : ℕ) (g : P p) :
    (dd r g).coeff (k + 1) =
      ((k + 1 : F p) - (r : F p)) * g.coeff (k + 1) +
        (2 * (r : F p) - (k : F p)) * g.coeff k := by
  rw [dd_form]
  simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_derivative]
  cases k with
  | zero =>
    simp
    ring
  | succ k =>
    simp only [coeff_X_mul, coeff_derivative, Nat.cast_succ]
    ring

theorem u_pow_coeff (r : ℕ) : ((uu : P p) ^ r).coeff r = 1 := by
  rw [uu, mul_pow]
  calc
    (X ^ r * (yy : P p) ^ r).coeff r = ((yy : P p) ^ r).coeff 0 :=
      by simpa only [zero_add] using coeff_X_pow_mul ((yy : P p) ^ r) r 0
    _ = 1 := by simp [yy, coeff_zero_eq_eval_zero]

theorem u_pow_degree_le (r : ℕ) : ((uu : P p) ^ r).natDegree ≤ 2 * r := by
  have h1 : (yy : P p).natDegree ≤ 1 := by
    unfold yy
    exact (natDegree_sub_le _ _).trans (by simpa using (natDegree_X_le : (X : P p).natDegree ≤ 1))
  have h2 : (uu : P p).natDegree ≤ 2 := by
    unfold uu
    have hx : (X : P p).natDegree ≤ 1 := natDegree_X_le
    exact natDegree_mul_le.trans (by omega)
  exact natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left r h2)

theorem dd_kernel [Fact p.Prime] {r : ℕ} (hr : r < p) {g : P p} (hg : g.natDegree < p + r)
    (hd : dd r g = 0) : g = C (g.coeff r) * uu ^ r := by
  let q := g - C (g.coeff r) * uu ^ r
  have hq_deg : q.natDegree < p + r := by
    have hb : (C (g.coeff r) * (uu : P p) ^ r).natDegree ≤ 2 * r :=
      le_trans (natDegree_C_mul_le _ _) (u_pow_degree_le r)
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (by omega)
  have hq_r : q.coeff r = 0 := by simp [q, u_pow_coeff]
  have hq_der : dd r q = 0 := by
    simp [q, dd_sub, hd, dd_const_mul_upow]
  have hz (i : ℕ) (hi : i < p + r) : q.coeff i = 0 := by
    induction i with
    | zero =>
      by_cases h : r = 0
      · simpa [h] using hq_r
      · have h0 := congrArg (fun t : P p => t.coeff 0) hq_der
        rw [dd_coeff_zero, coeff_zero] at h0
        exact (mul_eq_zero.mp h0).resolve_left
          (neg_ne_zero.mpr (cast_ne_zero_of_pos_lt (by omega) hr))
    | succ i ih =>
      by_cases h : i + 1 = r
      · simpa [h] using hq_r
      · have h0 := congrArg (fun t : P p => t.coeff (i+1)) hq_der
        rw [dd_coeff_succ, ih (by omega), mul_zero, add_zero, coeff_zero] at h0
        exact (mul_eq_zero.mp h0).resolve_left (by simpa using cast_difference_ne_zero (p := p) hr hi h)
  have hq_zero : q = 0 := by
    ext i
    rw [coeff_zero]
    by_cases h : i < p + r
    · exact hz i h
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact sub_eq_zero.mp hq_zero

end A208425Regular

namespace A208425Regular

open Polynomial
open scoped BigOperators

variable {p : ℕ}

noncomputable def bsum (r : ℕ) : P p :=
  ∑ k ∈ Finset.range (r + 1), C (((r + k).choose r : ℕ) : F p) * X ^ k

theorem coeff_bsum (r n : ℕ) :
    (bsum (p := p) r).coeff n = if n ≤ r then ((r + n).choose r : F p) else 0 := by
  classical
  simp only [bsum, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

theorem bsum_deg (r : ℕ) : (bsum (p := p) r).natDegree ≤ r := by
  unfold bsum
  exact natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hk)

theorem coeff_x_derivative (g : P p) (n : ℕ) :
    (X * derivative g).coeff n = (n : F p) * g.coeff n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul, coeff_derivative, mul_comm]
    norm_cast

theorem bsum_deriv (r : ℕ) :
    (yy : P p) * derivative (bsum r) - C ((r + 1 : ℕ) : F p) * bsum r =
      -C (((2*r+1 : ℕ) : F p) * ((2*r).choose r : F p)) * X ^ r := by
  ext n
  rw [yy, sub_mul, one_mul]
  simp only [coeff_sub, coeff_derivative, coeff_x_derivative, coeff_C_mul,
    neg_mul, coeff_neg, coeff_X_pow, coeff_bsum]
  rcases lt_trichotomy n r with h | heq | h
  · simp [h.le, (by omega : n+1 ≤ r), h.ne]
    have hnat := Nat.choose_mul_succ_eq (r+n) r
    rw [show r+n+1-r=n+1 by omega] at hnat
    have hcast := congrArg (fun j : ℕ => (j : F p)) hnat
    push_cast at hcast ⊢
    have hcast' : ((r+n).choose r : F p) * ((r : F p) + (n : F p) + 1) =
        ((r+(n+1)).choose r : F p) * ((n : F p) + 1) := by
      simpa [Nat.add_assoc] using hcast
    linear_combination -hcast'
  · subst n
    simp [show ¬r+1 ≤ r by omega, show r+r=2*r by omega]
    ring
  · simp [h.not_ge, h.not_gt, h.ne']

noncomputable def betaPoly (r : ℕ) : P p :=
  yy ^ (r + 1) * bsum r

theorem beta_deriv (r : ℕ) :
    derivative (betaPoly (p := p) r) =
      -C (((2*r+1 : ℕ) : F p) * ((2*r).choose r : F p)) * uu ^ r := by
  unfold betaPoly
  calc
    derivative (yy ^ (r + 1) * bsum r : P p) =
      yy ^ r * (yy * derivative (bsum r) - C ((r+1 : ℕ) : F p) * bsum r) := by
        rw [derivative_mul, derivative_pow_succ, d_y, pow_succ]
        simp only [Nat.cast_succ, map_add, map_one]
        ring
    _ = _ := by rw [bsum_deriv, uu, mul_pow]; ring

theorem ydeg_le : (yy : P p).natDegree ≤ 1 := by
  unfold yy
  exact (natDegree_sub_le _ _).trans (by simpa using (natDegree_X_le : (X : P p).natDegree ≤ 1))

theorem beta_deg (r : ℕ) : (betaPoly (p := p) r).natDegree ≤ 2*r+1 := by
  unfold betaPoly
  have hpw : ((yy : P p)^(r+1)).natDegree ≤ r+1 := natDegree_pow_le.trans (by
    simpa using Nat.mul_le_mul_left (r+1) (ydeg_le (p := p)))
  exact natDegree_mul_le.trans (by have hb := bsum_deg (p := p) r; omega)

theorem u_comp_y : (uu : P p).comp yy = uu := by
  simp [uu, yy, mul_comp, sub_comp]
  ring

theorem y_one_minus : (yy : P p).comp yy = X := by
  simp [yy, sub_comp]

theorem beta_reflected_sum [Fact p.Prime] (r : ℕ) (hr : 2*r+1 < p) :
    betaPoly (p := p) r + (betaPoly r).comp yy = 1 := by
  let g := betaPoly (p := p) r + (betaPoly r).comp yy
  have hdegree : g.natDegree < p := by
    have h := beta_deg (p := p) r
    have hc : ((betaPoly (p := p) r).comp yy).natDegree ≤ 2*r+1 :=
      natDegree_comp_le.trans (by
        have hx := ydeg_le (p := p)
        exact (Nat.mul_le_mul h hx).trans (by simp))
    exact (natDegree_add_le _ _).trans_lt (by omega)
  have hd : g.derivative = 0 := by
    change derivative (betaPoly (p := p) r + (betaPoly r).comp (1 - X)) = 0
    rw [derivative_add, derivative_comp_one_sub_X, beta_deriv]
    rw [show (1-X : P p) = yy by rfl]
    simp [mul_comp, pow_comp, u_comp_y]
  have he : g.coeff 0 = 1 := by
    have ha : eval 0 (bsum (p := p) r) = 1 := by
      rw [← coeff_zero_eq_eval_zero, coeff_bsum]
      simp
    simp [g, betaPoly, yy, coeff_zero_eq_eval_zero, ha]
  simpa [g, he] using derivative_const_of_lt hdegree hd

end A208425Regular

namespace A208425Regular

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem factorial_cast_ne_zero {n : ℕ} (hn : n < p) : (n.factorial : F p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial]
  omega

theorem choose_cast_ne_zero {n k : ℕ} (hk : k ≤ n) (hn : n < p) : (n.choose k : F p) ≠ 0 := by
  intro hz
  have h := congrArg (fun t : ℕ => (t : F p)) (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [Nat.cast_mul, hz, zero_mul] at h
  exact factorial_cast_ne_zero (p := p) hn h.symm

theorem choose_factorial_prod (n k : ℕ) :
    (n.choose k : F p) * (k.factorial : F p) =
      ∏ i ∈ Finset.range k, ((n : F p) - (i : F p)) := by
  by_cases hk : k ≤ n
  · have h := congrArg (fun t : ℕ => (t : F p)) (Nat.descFactorial_eq_factorial_mul_choose n k)
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_mul, mul_comm] at h
    rw [← h]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (by have hh := Finset.mem_range.mp hi; omega)]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    exact (Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : n < k)) (sub_self _)).symm

theorem reflect_small_choose (r j : ℕ) (hrel : 3*r+1 = p) (hj : j < r) :
    ((2*r).choose (j+1) : F p) =
      (-1 : F p)^(j+1) * ((r+j+1).choose (j+1) : F p) := by
  have hf := factorial_cast_ne_zero (p := p) (n := j+1) (by omega)
  apply (mul_right_cancel₀ hf)
  rw [choose_factorial_prod, mul_assoc, choose_factorial_prod]
  rw [← Finset.prod_range_reflect (fun i : ℕ => ((r+j+1 : ℕ) : F p) - (i : F p)) (j+1)]
  rw [show (-1 : F p)^(j+1) = ∏ _ ∈ Finset.range (j+1), (-1 : F p) by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show j+1-1-i = j-i by omega, Nat.cast_sub (by omega : i ≤ j)]
  have hpz : ((3*r+1 : ℕ) : F p) = 0 := by rw [hrel, ZMod.natCast_self]
  push_cast at hpz ⊢
  linear_combination hpz

theorem derivative_coefficient_reflect (r j : ℕ) (hrel : 3*r+1 = p) (hj : j < r) :
    (-1 : F p)^j * ((2*r).choose (r+j+1) : F p) =
      -((2*r-j-1).choose r : F p) := by
  have hc := choose_cast_ne_zero (p := p) (n := r+j+1) (k := j+1) (by omega) (by omega)
  have hnat := Nat.choose_mul (n := 2*r) (k := r+j+1) (s := j+1) (by omega)
  rw [show r+j+1-(j+1)=r by omega, show 2*r-(j+1)=2*r-j-1 by omega] at hnat
  have he := congrArg (fun t : ℕ => (t : F p)) hnat
  push_cast at he
  rw [reflect_small_choose r j hrel hj, mul_assoc, mul_comm (((r+j+1).choose (j+1) : ℕ) : F p),
    ← mul_assoc] at he
  have hq := mul_right_cancel₀ hc he
  rw [hq, ← mul_assoc, ← pow_add, show j+(j+1)=2*j+1 by omega, pow_succ, pow_mul]
  norm_num

theorem central_choose_cast (m k : ℕ) (hrel : 2*m+1 = p) (hk : k ≤ m) :
    ((2*k).choose k : F p) = (-4 : F p)^k * (m.choose k : F p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hnext := cast_ne_zero_of_pos_lt (p := p) (j := k+1) (by omega) (by omega)
    apply (mul_left_cancel₀ hnext)
    have hnat := Nat.succ_mul_centralBinom_succ k
    simp only [Nat.centralBinom_eq_two_mul_choose] at hnat
    have hm := congrArg (fun t : ℕ => (t : F p)) hnat
    push_cast at hm ⊢
    rw [hm, ih (by omega), pow_succ]
    have hchoose' : (m-k) * m.choose k = (k+1) * m.choose (k+1) := by
      have h := Nat.choose_mul (n := m) (k := k+1) (s := k) (by omega)
      rw [show k+1-k = 1 by omega, Nat.choose_one_right] at h
      simpa [Nat.choose_succ_self_right, mul_comm] using h.symm
    have hh := congrArg (fun t : ℕ => (t : F p)) hchoose'
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : k ≤ m), Nat.cast_succ] at hh
    have hpz : ((2*m+1 : ℕ) : F p) = 0 := by rw [hrel, ZMod.natCast_self]
    push_cast at hpz
    linear_combination (-4 * (-4 : F p)^k) * hh + (2 * (-4 : F p)^k * (m.choose k : F p)) * hpz

end A208425Regular

namespace A208425Regular

open Polynomial

theorem choose_column_sum (n k : ℕ) :
    ∑ j ∈ Finset.range (n+1), j.choose k = (n+1).choose (k+1) := by
  rw [← Nat.sum_Icc_choose n k]
  symm
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr (by have h := Finset.mem_Icc.mp hi; omega)
  · intro i hi hnot
    exact Nat.choose_eq_zero_of_lt (by
      have hi' := Finset.mem_range.mp hi
      simp only [Finset.mem_Icc, not_and] at hnot
      omega)

theorem choose_reverse_convolution (n a b : ℕ) :
    (∑ j ∈ Finset.range (n+1), j.choose a * (n-j).choose b) =
      (n+1).choose (a+b+1) := by
  induction n generalizing b with
  | zero =>
    cases a <;> cases b <;> simp [Nat.choose]
  | succ n ih =>
    cases b with
    | zero => simp [choose_column_sum]
    | succ b =>
      rw [show n.succ + 1 = (n+1)+1 by rfl, Finset.sum_range_succ]
      simp only [Nat.sub_self, Nat.choose_zero_succ, mul_zero, add_zero]
      have h : (∑ j ∈ Finset.range (n+1), j.choose a * ((n+1)-j).choose (b+1)) =
          ∑ j ∈ Finset.range (n+1), (j.choose a * (n-j).choose b +
            j.choose a * (n-j).choose (b+1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hle := Finset.mem_range.mp hj
        rw [show n+1-j = (n-j)+1 by omega, Nat.choose_succ_succ, mul_add]
      rw [h, Finset.sum_add_distrib, ih, ih]
      simpa [Nat.add_assoc] using (Nat.choose_succ_succ (n+1) (a+b+1)).symm

variable {p : ℕ}

theorem coeff_one_sub_pow {R : Type*} [CommRing R] (s j : ℕ) :
    (((1-X : Polynomial R)^s).coeff j) = (-1 : R)^j * (s.choose j : R) := by
  have h : (1-X : Polynomial R) = C (-1 : R) * (X + C (-1 : R)) := by
    simp [sub_eq_add_neg, add_comm]
  rw [h, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  by_cases hj : j ≤ s
  · have hsign : (-1 : R)^s * (-1)^(s-j)=(-1)^j := by
      rw [← pow_add, show s+(s-j)=j+2*(s-j) by omega, pow_add, pow_mul]
      norm_num
    linear_combination (s.choose j : R) * hsign
  · simp [Nat.choose_eq_zero_of_lt (by omega : s < j)]


theorem coeff_y_pow (s j : ℕ) :
    (((yy : P p)^s).coeff j) = (-1 : F p)^j * (s.choose j : F p) :=
  coeff_one_sub_pow s j

variable [Fact p.Prime]

noncomputable def logpoly : P p :=
  ∑ j ∈ Finset.range (p-1), C (((j+1 : ℕ) : F p)⁻¹) * X^(j+1)

noncomputable def wpoly (r : ℕ) : P p :=
  ∑ s ∈ Finset.range r, C (((2*r-s-1).choose r : F p) / (((s+1 : ℕ) : F p))) * X^(s+1)

theorem wpoly_deg (r : ℕ) : (wpoly (p := p) r).natDegree ≤ r := by
  unfold wpoly
  exact natDegree_sum_le_of_forall_le _ _ fun j hj =>
    (natDegree_C_mul_X_pow_le _ _).trans (by simpa using Finset.mem_range.mp hj)

theorem wpoly_eval_zero (r : ℕ) : (wpoly (p := p) r).eval 0 = 0 := by
  simp [wpoly, eval_finsetSum]

theorem wpoly_deriv (r : ℕ) (hr : r < p) :
    derivative (wpoly (p := p) r) =
      ∑ s ∈ Finset.range r, C ((2*r-s-1).choose r : F p) * X^s := by
  unfold wpoly
  rw [derivative_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hcast := cast_ne_zero_of_pos_lt (p := p) (j := s+1)
    (by omega) (by have hh := Finset.mem_range.mp hs; omega)
  rw [derivative_C_mul_X_pow]
  simp only [Nat.add_sub_cancel]
  rw [div_mul_cancel₀ _ hcast]

theorem wpoly_deriv_reflect (r : ℕ) (hrel : 3*r+1=p) :
    (derivative (wpoly (p := p) r)).comp yy = -derivative (wpoly r) := by
  rw [wpoly_deriv r (by omega)]
  ext j
  simp only [sum_comp, mul_comp, C_comp, X_comp, pow_comp, finsetSum_coeff,
    coeff_C_mul, coeff_y_pow, coeff_neg, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hj : j < r
  · rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hj)]
    have hseq : (∑ s ∈ Finset.range r, ((2*r-s-1).choose r : F p) *
          ((-1 : F p)^j * (s.choose j : F p))) =
          (-1 : F p)^j * ((2*r).choose (r+j+1) : F p) := by
      simp_rw [mul_left_comm _ ((-1 : F p)^j), ← Nat.cast_mul]
      rw [← Finset.mul_sum, ← Nat.cast_sum]
      congr 2
      have hsub : Finset.range r ⊆ Finset.range (2*r-1+1) :=
        Finset.range_subset_range.mpr (by omega)
      have hsum := Finset.sum_subset hsub (f := fun s : ℕ =>
        (2*r-1-s).choose r * s.choose j) (by
          intro s hs hr
          have hge : r ≤ s := by
            simpa [Finset.mem_range] using hr
          rw [Nat.choose_eq_zero_of_lt (by omega : 2*r-1-s < r), zero_mul])
      calc
        _ = ∑ s ∈ Finset.range r, (2*r-1-s).choose r * s.choose j := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [show 2*r-s-1=2*r-1-s by omega]
        _ = ∑ s ∈ Finset.range (2*r-1+1), (2*r-1-s).choose r * s.choose j := hsum
        _ = (2*r).choose (r+j+1) := by
          simp_rw [mul_comm]
          rw [choose_reverse_convolution]
          rw [show r*2-1+1=r*2 by omega, show j+r+1=r+j+1 by omega]
    rw [hseq]
    exact derivative_coefficient_reflect r j hrel hj
  · rw [Finset.sum_ite_eq, if_neg (by simpa [Finset.mem_range] using hj), neg_zero]
    apply Finset.sum_eq_zero
    intro s hs
    have hz : s.choose j = 0 := Nat.choose_eq_zero_of_lt (by
      have h := Finset.mem_range.mp hs; omega)
    simp [hz]

theorem wpoly_reflect (r : ℕ) (hrel : 3*r+1=p) :
    (wpoly (p := p) r).comp yy = wpoly r := by
  let g := (wpoly (p := p) r).comp yy - wpoly r
  have hd : g.derivative = 0 := by
    change derivative ((wpoly (p := p) r).comp (1-X) - wpoly r) = 0
    rw [derivative_sub, derivative_comp_one_sub_X]
    change -((derivative (wpoly (p := p) r)).comp yy) - derivative (wpoly r) = 0
    rw [wpoly_deriv_reflect _ hrel]
    simp
  have hdeg : g.natDegree < p := by
    have hw := wpoly_deg (p := p) r
    have hy := ydeg_le (p := p)
    have hc : ((wpoly (p := p) r).comp yy).natDegree ≤ r :=
      natDegree_comp_le.trans ((Nat.mul_le_mul hw hy).trans (by simp))
    exact (natDegree_sub_le _ _).trans_lt (by omega)
  have hc := derivative_const_of_lt hdeg hd
  have h2 : (2 : F p) ≠ 0 := cast_ne_zero_of_pos_lt (p := p) (j := 2) (by omega) (by
    have hp := (Fact.out : p.Prime).two_le
    omega)
  have hhalf : (1 : F p) - 1/2 = 1/2 := by field_simp; ring
  have h0 : g.eval (1/2) = g.coeff 0 := by
    calc
      _ = (C (g.coeff 0)).eval (1/2) := congrArg (fun f : P p => f.eval (1/2)) hc
      _ = _ := eval_C
  have hz : g.eval (1/2) = 0 := by
    have hy : (yy : P p).eval (1/2) = 1/2 := by
      rw [yy, eval_sub, eval_one, eval_X, hhalf]
    change ((wpoly (p := p) r).comp yy - wpoly r).eval (1/2) = 0
    rw [eval_sub, eval_comp, hy, sub_self]
  rw [hz] at h0
  rw [← sub_eq_zero]
  change g = 0
  rw [hc, ← h0, C_0]

end A208425Regular

namespace A208425Regular

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem logpoly_deriv :
    derivative (logpoly (p := p)) = ∑ j ∈ Finset.range (p-1), (X : P p)^j := by
  unfold logpoly
  rw [derivative_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp := Finset.mem_range.mp hj
  have hjn := cast_ne_zero_of_pos_lt (p := p) (j := j+1) (by omega) (by omega)
  rw [derivative_C_mul_X_pow]
  simp only [Nat.add_sub_cancel, inv_mul_cancel₀ hjn, map_one, one_mul]

theorem logpoly_u_deriv :
    (uu : P p) * derivative logpoly = X - X^p := by
  have h := geom_sum_mul_neg (X : P p) (p-1)
  rw [logpoly_deriv, uu, yy, mul_assoc, mul_comm (1-X), h, mul_sub, mul_one, ← pow_succ']
  rw [show p-1+1=p by have hh := (Fact.out : p.Prime).pos; omega]

theorem y_pow_char :
    (yy : P p)^p = 1 - X^p := by
  unfold yy
  rw [sub_pow_char, one_pow]

theorem dd_sum {ι : Type*} (s : Finset ι) (r : ℕ) (f : ι → P p) :
    dd r (∑ i ∈ s, f i) = ∑ i ∈ s, dd r (f i) := by
  simp [dd, Finset.mul_sum, Finset.sum_sub_distrib]

theorem dd_add (r : ℕ) (f g : P p) : dd r (f + g) = dd r f + dd r g := by
  simp [dd, derivative_add, mul_add]
  ring

theorem dd_mul (r : ℕ) (f g : P p) :
    dd r (f * g) = uu * derivative f * g + f * dd r g := by
  simp [dd, derivative_mul]
  ring

theorem dd_u_mul (r : ℕ) (f : P p) :
    dd r (uu^r * f) = uu^(r+1) * derivative f := by
  rw [mul_comm, dd_mul, ← one_mul ((uu : P p)^r), ← C_1, dd_const_mul_upow]
  simp [pow_succ]
  ring

theorem dd_x_y (r a b : ℕ) :
    dd r (X^a * (yy : P p)^b) =
      C ((a : F p)-(r : F p)) * X^a * yy^(b+1) -
      C ((b : F p)-(r : F p)) * X^(a+1) * yy^b := by
  have hx : (X : P p) * derivative (X^a) = C (a : F p) * X^a := by
    cases a with
    | zero => simp
    | succ a =>
      rw [derivative_X_pow_succ, pow_succ']
      simp only [Nat.cast_succ]
      ring
  have hy : (yy : P p) * derivative (yy^b) = -C (b : F p) * yy^b := by
    cases b with
    | zero => simp
    | succ b =>
      rw [derivative_pow_succ, d_y, pow_succ']
      simp only [Nat.cast_succ]
      ring
  unfold dd
  rw [derivative_mul]
  have hc : (uu : P p) * (derivative (X^a) * yy^b + X^a * derivative (yy^b)) =
      (X*derivative (X^a))*yy^(b+1) + X^(a+1)*(yy*derivative (yy^b)) := by
    simp [uu, pow_succ]
    ring
  rw [hc, hx, hy]
  simp only [map_sub, pow_succ]
  have hd' : (1 - 2*X : P p) = yy - X := by unfold yy; ring
  rw [hd']
  ring

theorem beta_partition (r : ℕ) (hr : 2*r+1 < p) :
    (∑ l ∈ Finset.range (r+1), C ((2*r-l).choose r : F p) *
      (X^(r-l) * yy^(r+1) + X^(r+1) * yy^(r-l)) : P p) = 1 := by
  rw [← Finset.sum_range_reflect]
  have h := beta_reflected_sum (p := p) r hr
  simp only [betaPoly, bsum, mul_comp, pow_comp, y_one_minus, sum_comp, C_comp, X_comp] at h
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlr := Finset.mem_range.mp hl
  rw [show r+1-1-l = r-l by omega, show 2*r-(r-l)=r+l by omega,
    show r-(r-l)=l by omega]
  ring

noncomputable def ppoly (r m : ℕ) : P p :=
  ∑ k ∈ Finset.range (m+1),
    C (((2*k).choose k : F p) / ((k : F p)-(r : F p))) * uu^k

theorem binomial_series (m : ℕ) (hm : 2*m+1=p) :
    (∑ k ∈ Finset.range (m+1), C ((2*k).choose k : F p) * uu^k : P p) = (1-4*uu)^m := by
  rw [show (1-4*uu : P p)=(-4*uu)+1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [central_choose_cast m k hm (by have h := Finset.mem_range.mp hk; omega)]
  rw [show (-4 : P p) = (-1)*4 by ring, mul_pow]
  simp only [map_mul, map_pow, map_neg, C_ofNat, C_eq_natCast, one_pow, mul_one]
  ring

theorem dd_ppoly (r m : ℕ) (hrm : r ≤ m) (hm : 2*m+1=p) :
    dd r (ppoly r m : P p) =
      1 - 2*X^p - C ((2*r).choose r : F p) * (1-2*X) * uu^r := by
  unfold ppoly
  rw [dd_sum]
  simp_rw [dd_const_mul_upow, div_mul_eq_mul_div]
  have hh : (∑ k ∈ Finset.range (m+1),
      C ((((2*k).choose k : F p) * ((k : F p)-r)) / ((k : F p)-r)) *
        (1-2*X) * uu^k : P p) =
      ∑ k ∈ Finset.range (m+1),
        (C ((2*k).choose k : F p) * (1-2*X) * uu^k -
          if k=r then C ((2*r).choose r : F p) * (1-2*X) * uu^r else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkr : k = r
    · subst k
      simp
    · have h := cast_difference_ne_zero (p := p) (i := k) (r := r) (by omega)
        (by have h := Finset.mem_range.mp hk; omega) hkr
      rw [mul_div_cancel_right₀ _ h]
      simp [hkr]
  rw [hh, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hg : (∑ k ∈ Finset.range (m+1),
      C ((2*k).choose k : F p) * (1-2*X) * uu^k : P p) =
      (1-2*X) * (1-4*uu)^m := by
    rw [← binomial_series m hm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hg]
  have hpw : (1-2*X : P p) * (1-4*uu)^m = 1-2*X^p := by
    rw [show (1-4*uu : P p) = (1-2*X)^2 by simp [uu,yy]; ring, ← pow_mul, ← pow_succ', hm]
    rw [sub_pow_char, one_pow, mul_pow]
    have h2 : (2 : P p)^p = 2 := by
      rw [show (2 : P p) = 1+1 by norm_num, add_pow_char, one_pow]
    rw [h2]
  rw [hpw]

noncomputable def epiece (r l : ℕ) : P p :=
  -C (((2*r-l).choose r : F p) / (l : F p)) *
    ((1-2*X^p)*X^(r-l)*yy^r + (1-2*yy^p)*yy^(r-l)*X^r)

noncomputable def epoly (r : ℕ) : P p :=
  uu^r * (C (2*((2*r).choose r : F p)) * logpoly) +
    ∑ l ∈ Finset.Icc 1 r, epiece r l

theorem dd_epiece (r l : ℕ) (hpos : 0 < l) (hlr : l ≤ r) (hrp : r < p) :
    dd r (epiece r l) =
      C ((2*r-l).choose r : F p) * (1-2*X^p) *
        (X^(r-l)*yy^(r+1)+X^(r+1)*yy^(r-l)) := by
  have hl : (l : F p) ≠ 0 := cast_ne_zero_of_pos_lt hpos (by omega)
  unfold epiece
  have hx : derivative (1-2*X^p : P p) = 0 := by
    simp [derivative_X_pow]
  have hy : derivative (1-2*(yy : P p)^p) = 0 := by
    simp [derivative_pow]
  rw [dd_mul, derivative_neg, derivative_C, neg_zero, mul_zero, zero_mul, zero_add, dd_add]
  rw [show (1-2*X^p : P p)*X^(r-l)*yy^r=(1-2*X^p)*(X^(r-l)*yy^r) by ring,
    show (1-2*yy^p : P p)*yy^(r-l)*X^r=(1-2*yy^p)*(X^r*yy^(r-l)) by ring]
  rw [dd_mul r (1-2*X^p), dd_mul r (1-2*yy^p)]
  simp only [hx, hy, mul_zero, zero_mul, zero_add]
  rw [dd_x_y, dd_x_y, y_pow_char, Nat.cast_sub hlr]
  simp only [sub_self, map_zero, zero_mul, sub_zero, zero_sub]
  rw [show (r : F p)-l-r = -l by ring, C_neg]
  have hmul : C (((2*r-l).choose r : F p) / (l : F p)) * C ((l : ℕ) : F p) =
      C ((2*r-l).choose r : F p) := by rw [← C_mul, div_mul_cancel₀ _ hl]
  linear_combination ((1-2*X^p)*(X^(r-l)*yy^(r+1)+X^(r+1)*yy^(r-l))) * hmul

end A208425Regular

namespace A208425Regular

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem dd_kernel_wide {r : ℕ} (hr : 2*r < p) {g : P p}
    (hg : g.natDegree < p + 2*r) (hd : dd r g = 0) :
    g = C (g.coeff r) * uu^r := by
  by_cases hz : g = 0
  · simp [hz]
  have hh := congrArg (fun t : P p => t.coeff (g.natDegree+1)) hd
  rw [dd_coeff_succ, coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < g.natDegree+1),
    mul_zero, zero_add, coeff_zero, ← leadingCoeff] at hh
  have hgdeg : g.natDegree = 2*r := by
    by_contra hne
    have hne' := cast_difference_ne_zero (p := p) (i := g.natDegree) (r := 2*r) hr hg hne
    have hne'' : 2*(r : F p)-(g.natDegree : F p) ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ← sub_ne_zero]
      simpa using hne'
    exact hne'' ((mul_eq_zero.mp hh).resolve_right (leadingCoeff_ne_zero.mpr hz))
  exact dd_kernel (by omega) (by omega) hd

theorem dd_epoly (r : ℕ) (hr : 2*r+1 < p) :
    dd r (epoly r : P p) =
      1-2*X^p-C ((2*r).choose r : F p)*(1-2*X)*uu^r := by
  unfold epoly
  rw [dd_add, dd_u_mul, derivative_C_mul, dd_sum]
  have hg : (uu : P p)^(r+1) * (C (2*((2*r).choose r : F p))*derivative logpoly) =
      C (2*((2*r).choose r : F p))*uu^r*(X-X^p) := by
    rw [← logpoly_u_deriv, pow_succ]
    ring
  rw [hg]
  have hs : (∑ l ∈ Finset.Icc 1 r, dd r (epiece r l) : P p) =
      (1-2*X^p) * (∑ l ∈ Finset.Icc 1 r, C ((2*r-l).choose r : F p) *
        (X^(r-l)*yy^(r+1)+X^(r+1)*yy^(r-l))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have h := Finset.mem_Icc.mp hl
    rw [dd_epiece r l (by omega) h.2 (by omega)]
    ring
  rw [hs]
  have hp := beta_partition (p := p) r hr
  have hset : Finset.range (r+1) = insert 0 (Finset.Icc 1 r) := by
    ext i
    simp [Finset.mem_range]
    omega
  rw [hset, Finset.sum_insert (by simp)] at hp
  have h0 : (C ((2*r-0).choose r : F p) *
      (X^(r-0)*yy^(r+1)+X^(r+1)*yy^(r-0)) : P p) = C ((2*r).choose r : F p)*uu^r := by
    simp only [Nat.sub_zero, uu, mul_pow, pow_succ]
    have h : (yy : P p) + X = 1 := by simp [yy]
    linear_combination (C ((2*r).choose r : F p) * X^r * yy^r) * h
  rw [h0] at hp
  rw [show (∑ l ∈ Finset.Icc 1 r, C ((2*r-l).choose r : F p) *
        (X^(r-l)*yy^(r+1)+X^(r+1)*yy^(r-l)) : P p) = 1 - C ((2*r).choose r : F p)*uu^r
      by linear_combination hp]
  simp only [map_mul, C_ofNat]
  ring

theorem u_degree : (uu : P p).natDegree = 2 := by
  apply le_antisymm
  · simpa using (u_pow_degree_le (p := p) 1)
  · apply le_natDegree_of_ne_zero
    rw [uu, yy, mul_sub, mul_one, coeff_sub, coeff_X_mul]
    simp [coeff_X]

theorem u_pow_degree (r : ℕ) : ((uu : P p)^r).natDegree = 2*r := by
  have hU : (uu : P p) ≠ 0 := by
    intro hz
    have hd := u_degree (p := p)
    rw [hz, natDegree_zero] at hd
    omega
  rw [natDegree_pow' (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hU)), u_degree]
  exact Nat.mul_comm _ _

theorem logpoly_degree : (logpoly (p := p)).natDegree < p := by
  unfold logpoly
  have h : (∑ j ∈ Finset.range (p-1), C (((j+1 : ℕ) : F p)⁻¹) *
        X^(j+1) : P p).natDegree ≤ p-1 := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_X_pow_le _ _).trans (by
      have hh := Finset.mem_range.mp hj
      omega)
  have hp := (Fact.out : p.Prime).pos
  omega

theorem ppoly_degree (r m : ℕ) : (ppoly (p := p) r m).natDegree ≤ 2*m := by
  unfold ppoly
  exact natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_le _ _).trans ((u_pow_degree_le k).trans
      (by have hh := Finset.mem_range.mp hk; omega))

noncomputable def elow (r : ℕ) : P p :=
  ∑ l ∈ Finset.Icc 1 r, -C (((2*r-l).choose r : F p) / (l : F p)) *
    (X^(r-l)*yy^r + yy^(r-l)*X^r)

noncomputable def ehigh (r : ℕ) : P p :=
  C (2*((2*r).choose r : F p))*logpoly +
    ∑ l ∈ Finset.Icc 1 r, C (2*(((2*r-l).choose r : F p) / (l : F p))) *
      (X^(p-l)+yy^(p-l))

theorem esplit (r : ℕ) (hr : r < p) :
    epoly (p := p) r = uu^r * ehigh r + elow r := by
  unfold epoly ehigh elow
  rw [mul_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlr := (Finset.mem_Icc.mp hl).2
  unfold epiece
  simp [uu, mul_pow, C_mul, C_ofNat]
  have hxp : (X : P p)^p * X^(r-l) = X^r * X^(p-l) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hyp : (yy : P p)^p * yy^(r-l) = yy^r * yy^(p-l) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  linear_combination
    2 * C (((2*r-l).choose r : F p) / (l : F p)) * (yy : P p)^r * hxp +
    2 * C (((2*r-l).choose r : F p) / (l : F p)) * (X : P p)^r * hyp

noncomputable def plow (r : ℕ) : P p :=
  ∑ k ∈ Finset.range r,
    C (((2*k).choose k : F p) / ((k : F p)-(r : F p))) * uu^k

noncomputable def phigh (r m : ℕ) : P p :=
  ∑ k ∈ Finset.Icc (r+1) m,
    C (((2*k).choose k : F p) / ((k : F p)-(r : F p))) * uu^(k-r)

theorem psplit (r m : ℕ) (hrm : r ≤ m) :
    ppoly (p := p) r m = uu^r * phigh r m + plow r := by
  unfold ppoly phigh plow
  have hset : Finset.range (m+1) =
      Finset.range r ∪ insert r (Finset.Icc (r+1) m) := by
    ext k
    simp [Finset.mem_range]
    omega
  have hd : Disjoint (Finset.range r) (insert r (Finset.Icc (r+1) m)) := by
    rw [Finset.disjoint_left]
    intro k hk h
    simp [Finset.mem_range] at hk
    simp at h
    omega
  rw [hset, Finset.sum_union hd, Finset.sum_insert (by simp), add_comm, Finset.mul_sum]
  simp only [sub_self, div_zero, map_zero, zero_mul, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have h := Finset.mem_Icc.mp hk
  have hu : (uu : P p)^k = uu^r * uu^(k-r) := by
    rw [← pow_add, show r+(k-r)=k by omega]
  rw [hu]
  ring

theorem low_degree (r : ℕ) (hr : 0 < r) :
    (plow (p := p) r).natDegree < 2*r ∧ (elow (p := p) r).natDegree < 2*r := by
  constructor
  · have h : (plow (p := p) r).natDegree ≤ 2*r-1 := by
      unfold plow
      apply natDegree_sum_le_of_forall_le
      intro k hk
      exact (natDegree_C_mul_le _ _).trans ((u_pow_degree_le k).trans (by
        have hh := Finset.mem_range.mp hk
        omega))
    omega
  · have h : (elow (p := p) r).natDegree ≤ 2*r-1 := by
      unfold elow
      apply natDegree_sum_le_of_forall_le
      intro l hl
      have hh := Finset.mem_Icc.mp hl
      have hx (k : ℕ) : ((X : P p)^k).natDegree ≤ k :=
        natDegree_pow_le.trans (by have h := (natDegree_X_le : (X : P p).natDegree ≤ 1); simp_all)
      have hy (k : ℕ) : ((yy : P p)^k).natDegree ≤ k :=
        natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left k (ydeg_le (p := p)))
      rw [neg_mul, natDegree_neg]
      refine (natDegree_C_mul_le _ _).trans ?_
      have hleft := (natDegree_mul_le (p := (X : P p)^(r-l)) (q := yy^r)).trans
        (Nat.add_le_add (hx _) (hy _))
      have hright := (natDegree_mul_le (p := (yy : P p)^(r-l)) (q := X^r)).trans
        (Nat.add_le_add (hy _) (hx _))
      exact (natDegree_add_le _ _).trans (by omega)
    omega

theorem high_eval_zero (r m : ℕ) (hrel : 3*r+1=p) :
    (phigh (p := p) r m).eval 0 = 0 ∧ (ehigh (p := p) r).eval 0 = 0 := by
  constructor
  · unfold phigh
    rw [eval_finsetSum]
    apply Finset.sum_eq_zero
    intro k hk
    have h := Finset.mem_Icc.mp hk
    simp [uu, yy, zero_pow (show k-r≠0 by omega)]
  · unfold ehigh
    simp only [eval_add, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X, yy,
      eval_sub, eval_one, sub_zero, one_pow]
    have hlog : (logpoly (p := p)).eval 0 = 0 := by simp [logpoly, eval_finsetSum]
    rw [hlog, mul_zero, zero_add]
    have hb : (∑ l ∈ Finset.Icc 1 r, 2*(((2*r-l).choose r : F p) / (l : F p))*(0^(p-l)+1)) =
        2*(wpoly (p := p) r).eval 1 := by
      unfold wpoly
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
      rw [Finset.mul_sum, show Finset.Icc 1 r=Finset.Ico 1 (r+1) by ext j; simp,
        Finset.sum_Ico_eq_sum_range]
      simp only [show r+1-1=r by omega]
      apply Finset.sum_congr rfl
      intro j hj
      have hjr := Finset.mem_range.mp hj
      rw [show 1+j=j+1 by omega, show 2*r-(j+1)=2*r-j-1 by omega]
      simp [zero_pow (show p-(j+1)≠0 by omega)]
    rw [hb]
    have hm := congrArg (fun f : P p => f.eval 0) (wpoly_reflect (p := p) r hrel)
    simp [yy, wpoly_eval_zero] at hm
    rw [hm, mul_zero]

end A208425Regular

namespace A208425Regular

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem ehigh_degree (r : ℕ) : (ehigh (p := p) r).natDegree < p := by
  have hp := (Fact.out : p.Prime).pos
  unfold ehigh
  have hlog : (C (2*((2*r).choose r : F p))*logpoly).natDegree ≤ p-1 :=
    (natDegree_C_mul_le _ _).trans (by have h := logpoly_degree (p := p); omega)
  have hs : (∑ l ∈ Finset.Icc 1 r, C (2*(((2*r-l).choose r : F p) / (l : F p))) *
        (X^(p-l)+yy^(p-l))).natDegree ≤ p-1 := by
    apply natDegree_sum_le_of_forall_le
    intro l hl
    have hh := Finset.mem_Icc.mp hl
    refine (natDegree_C_mul_le _ _).trans ?_
    have hx : ((X : P p)^(p-l)).natDegree ≤ p-l := by simp
    have hy : ((yy : P p)^(p-l)).natDegree ≤ p-l := natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left (p-l) (ydeg_le (p := p)))
    exact (natDegree_add_le _ _).trans (by omega)
  exact (natDegree_add_le _ _).trans_lt (by omega)

theorem pp_eq_ep (r m : ℕ) (hr : 0 < r) (hrel : 3*r+1=p) (hm : 2*m+1=p) :
    (ppoly r m : P p) = epoly r := by
  have hrm : r ≤ m := by omega
  have h6 : 2*r+1 < p := by omega
  have hE : (epoly (p := p) r).natDegree < p+2*r := by
    rw [esplit r (by omega)]
    have hmul := natDegree_mul_le (p := (uu : P p)^r) (q := ehigh r)
    have h0 := ehigh_degree (p := p) r
    have h1 := u_pow_degree (p := p) r
    have h2 := (low_degree (p := p) r hr).2
    exact (natDegree_add_le _ _).trans_lt (by omega)
  have hP := ppoly_degree (p := p) r m
  let g := (ppoly r m : P p)-epoly r
  have hg : g.natDegree < p+2*r := (natDegree_sub_le _ _).trans_lt (by omega)
  have hD : dd r g = 0 := by
    simp [g, dd_sub, dd_ppoly r m hrm hm, dd_epoly r h6]
  have hker := dd_kernel_wide (p := p) (r := r) (by omega) hg hD
  let c := g.coeff r
  let H := phigh (p := p) r m - ehigh r - C c
  have hmove : uu^r * H = elow r - (plow r : P p) := by
    change ppoly r m - epoly r = C c * uu^r at hker
    rw [psplit r m hrm, esplit r (by omega)] at hker
    unfold H
    linear_combination hker
  have hH : H = 0 := by
    by_contra hH
    have hu : ((uu : P p)^r) ≠ 0 := by
      intro hz
      have hh := u_pow_degree (p := p) r
      rw [hz, natDegree_zero] at hh
      omega
    have hl := (low_degree (p := p) r hr).1
    have he := (low_degree (p := p) r hr).2
    have hdeg := congrArg (fun f : P p => f.natDegree) hmove
    rw [natDegree_mul hu hH, u_pow_degree] at hdeg
    have hsub := natDegree_sub_le (elow (p := p) r) (plow r)
    omega
  have hc : c=0 := by
    have he := congrArg (fun f : P p => f.eval 0) hH
    have hzero := high_eval_zero (p := p) r m hrel
    simp [H, hzero.1, hzero.2] at he
    exact he
  apply sub_eq_zero.1
  change g=0
  change g=C c*uu^r at hker
  rw [hker,hc,C_0,zero_mul]

end A208425Regular

namespace A208425Regular

open Polynomial

variable {p : ℕ} [Fact p.Prime]

noncomputable def phiSix (p : ℕ) : P p := X^2-X+1

abbrev SixthQuot (p : ℕ) := AdjoinRoot (phiSix p)

noncomputable def qm : P p →+* SixthQuot p := AdjoinRoot.mk (phiSix p)

theorem qm_u : qm (p := p) uu = 1 := by
  have hz : AdjoinRoot.mk (phiSix p) (phiSix p) = 0 := AdjoinRoot.mk_self
  change qm (p := p) (phiSix p) = 0 at hz
  have he : (phiSix p)=1-uu := by simp [phiSix,uu,yy]; ring
  have hb : qm (p := p) (1-uu) = 0 :=
    (congrArg (qm (p := p)) he).symm.trans hz
  rw [map_sub, map_one, sub_eq_zero] at hb
  exact hb.symm

theorem qm_x_y : qm (p := p) X * qm yy = 1 := by
  rw [← map_mul]
  exact qm_u

theorem qm_x_add_y : qm (p := p) X + qm yy = 1 := by
  rw [← map_add, show (X+yy : P p)=1 by simp [yy], map_one]

theorem qm_pow (h6 : 6 ∣ p-1) :
    qm (p := p) (X^p)=qm X ∧ qm (p := p) (yy^p)=qm yy := by
  let x := qm (p := p) X
  let y := qm (p := p) yy
  have hxy : x*y=1 := qm_x_y
  have hs : x+y=1 := qm_x_add_y
  have hx2 : x^2 - x + 1 = 0 := by
    linear_combination x*hs - hxy
  have hy2 : y^2 - y + 1 = 0 := by
    linear_combination y*hs - hxy
  have hx3 : x^3 = -1 := by linear_combination (x+1)*hx2
  have hy3 : y^3 = -1 := by linear_combination (y+1)*hy2
  have hx6 : x^6=1 := by rw [show (6:ℕ)=3*2 by decide, pow_mul,hx3]; ring
  have hy6 : y^6=1 := by rw [show (6:ℕ)=3*2 by decide, pow_mul,hy3]; ring
  rcases h6 with ⟨t,ht⟩
  have hp := (Fact.out : p.Prime).pos
  have hp' : p=6*t+1 := by omega
  simp only [map_pow]
  change x^p=x ∧ y^p=y
  have H (z : SixthQuot p) (hz : z^6=1) : z^p=z := by
    calc
      z^p = z^(6*t+1) := congrArg (fun n : ℕ => z^n) hp'
      _ = z := by rw [pow_succ,pow_mul,hz,one_pow,one_mul]
  exact ⟨H x hx6,H y hy6⟩

theorem qm_epoly (r : ℕ) (hrel : 3*r+1=p) (h6 : 6 ∣ p-1) (hL : phiSix p ∣ logpoly) :
    qm (epoly (p := p) r) = 0 := by
  have hl := AdjoinRoot.mk_eq_zero.mpr hL
  change qm (p := p) logpoly = 0 at hl
  unfold epoly
  simp only [map_add, map_mul, hl, mul_zero, zero_add, map_sum]
  have hp := qm_pow (p := p) h6
  have hg (l : ℕ) (hlr : l ≤ r) :
      qm (epiece (p := p) r l) =
        -qm (C (((2*r-l).choose r : F p)/(l : F p))) *
          ((1-2*qm X)*(qm yy)^l + (1-2*qm yy)*(qm X)^l) := by
    unfold epiece
    have hx : qm (p := p) (X^(r-l)*yy^r) = (qm yy)^l := by
      have hh : (X^(r-l)*yy^r : P p) = uu^(r-l)*yy^l := by
        rw [uu, mul_pow, show (yy : P p)^r = yy^(r-l)*yy^l by
          rw [←pow_add]; congr 1; omega]
        ring
      rw [hh,map_mul,map_pow,qm_u,one_pow,one_mul]
      exact map_pow _ _ _
    have hy : qm (p := p) (yy^(r-l)*X^r) = (qm X)^l := by
      have hh : (yy^(r-l)*X^r : P p) = uu^(r-l)*X^l := by
        rw [uu, mul_pow, show (X : P p)^r = X^(r-l)*X^l by
          rw [←pow_add]; congr 1; omega]
        ring
      rw [hh,map_mul,map_pow,qm_u,one_pow,one_mul]
      exact map_pow _ _ _
    rw [show (1-2*X^p : P p)*X^(r-l)*yy^r=(1-2*X^p)*(X^(r-l)*yy^r) by ring,
      show (1-2*yy^p : P p)*yy^(r-l)*X^r=(1-2*yy^p)*(yy^(r-l)*X^r) by ring]
    have h2 : qm (2 : P p) = 2 := by
      rw [show (2 : P p)=1+1 by norm_num, map_add, map_one]
      norm_num
    simp [hx,hy,hp.1,hp.2,h2]
  have heq : (∑ l ∈ Finset.Icc 1 r, qm (epiece (p := p) r l)) =
      -(1-2*qm X)*(qm ((wpoly r).comp yy)) -(1-2*qm yy)*qm (wpoly r) := by
    unfold wpoly
    simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, map_sum, map_mul, map_pow]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      show Finset.Icc 1 r=Finset.Ico 1 (r+1) by ext j; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [show r+1-1=r by omega]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show 1+j=j+1 by omega, hg _ (by omega), show 2*r-(j+1)=2*r-j-1 by omega]
    ring
  rw [heq, wpoly_reflect r hrel]
  linear_combination 2*qm ((wpoly (p := p) r)) * qm_x_add_y (p := p)

theorem regular_sum_zero_from_log (r m : ℕ) (hrel : 3*r+1=p) (hm : 2*m+1=p)
    (hL : phiSix p ∣ logpoly) :
    (∑ k ∈ (Finset.range (m+1)).erase r,
      ((2*k).choose k : F p) / ((k : F p)-(r : F p))) = 0 := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h6 : 6 ∣ p-1 := ⟨r/2, by rcases hodd with ⟨t, ht⟩; omega⟩
  have hP := pp_eq_ep (p := p) r m (by omega) hrel hm
  have hq := congrArg (qm (p := p)) hP
  rw [qm_epoly r hrel h6 hL] at hq
  unfold ppoly at hq
  simp only [map_sum, map_mul, map_pow, qm_u, one_pow, mul_one] at hq
  have hh : qm (p := p)
      (C (∑ k ∈ Finset.range (m+1), ((2*k).choose k : F p)/((k : F p)-(r : F p)))) = 0 := by
    simpa [map_sum] using hq
  have hmonic : (phiSix p).Monic := by
    have hy : (yy : P p).natDegree < 2 := by
      have h := ydeg_le (p := p)
      omega
    have hd : (yy : P p).degree < ((2 : ℕ) : WithBot ℕ) :=
      degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hy)
    rw [show phiSix p = X^2+yy by simp [phiSix, yy]; ring]
    exact monic_X_pow_add hd
  have hdeg : (phiSix p).natDegree = 2 := by
    apply le_antisymm
    · exact (natDegree_add_le _ _).trans (by
        have h : (X^2-X : P p).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
        simpa using h)
    · exact le_natDegree_of_ne_zero (by simp [phiSix, coeff_X_pow, coeff_X, coeff_one])
  have hs : (∑ k ∈ Finset.range (m+1), ((2*k).choose k : F p)/((k : F p)-(r : F p))) = 0 := by
    by_contra hb
    have hne : C (∑ k ∈ Finset.range (m+1), ((2*k).choose k : F p)/((k : F p)-(r : F p))) ≠ 0 :=
      C_ne_zero.mpr hb
    have hsmall :
        (C (∑ k ∈ Finset.range (m+1), ((2*k).choose k : F p)/((k : F p)-(r : F p)))).natDegree <
          (phiSix p).natDegree := by rw [natDegree_C,hdeg]; decide
    exact (AdjoinRoot.mk_ne_zero_of_natDegree_lt hmonic hne hsmall) hh
  rw [← Finset.sum_erase_add (Finset.range (m+1)) _ (Finset.mem_range.mpr (by omega : r < m+1))] at hs
  simpa using hs

end A208425Regular

namespace A208425Regular

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem log_reflect (hp2 : 2<p) : (logpoly (p := p)).comp yy = logpoly := by
  let f := logpoly (p := p)
  let g := f.comp yy - f
  have hU : (uu : P p) ≠ 0 := by
    intro hz
    have h := u_degree (p := p)
    rw [hz, natDegree_zero] at h
    omega
  have hd : g.derivative = 0 := by
    change derivative (f.comp (1-X)-f) = 0
    rw [derivative_sub, derivative_comp_one_sub_X]
    change -f.derivative.comp yy - f.derivative = 0
    apply mul_left_cancel₀ hU
    rw [mul_zero, mul_sub, mul_neg, logpoly_u_deriv]
    have h := congrArg (fun q : P p => q.comp yy) (logpoly_u_deriv (p := p))
    simp only [mul_comp, u_comp_y, sub_comp, X_comp, pow_comp] at h
    change (uu : P p) * f.derivative.comp yy = _ at h
    rw [h,y_pow_char]
    unfold yy
    ring
  have hf : f.natDegree < p := logpoly_degree
  have hc : (f.comp yy).natDegree ≤ f.natDegree :=
    natDegree_comp_le.trans (by
      simpa using Nat.mul_le_mul_left f.natDegree (ydeg_le (p := p)))
  have hdeg : g.natDegree < p := (natDegree_sub_le _ _).trans_lt (by omega)
  have he := derivative_const_of_lt hdeg hd
  have h2 : (2 : F p) ≠ 0 := cast_ne_zero_of_pos_lt (j := 2) (by omega) hp2
  have hy : (yy : P p).eval (1/2) = 1/2 := by
    rw [yy, eval_sub, eval_one, eval_X]
    field_simp
    ring
  have hz : g.coeff 0 = 0 := by
    calc
      _ = (C (g.coeff 0)).eval (1/2) := eval_C.symm
      _ = g.eval (1/2) := congrArg (fun q : P p => q.eval (1/2)) he.symm
      _ = 0 := by
        change (f.comp yy - f).eval (1/2) = 0
        rw [eval_sub, eval_comp, hy, sub_self]
  have hh : g=0 := by rw [he,hz,C_0]
  exact sub_eq_zero.mp hh

theorem qm_log_inversion (x y : SixthQuot p) (hxy : x*y=1) :
    x^p * (∑ j ∈ Finset.range (p-1), qm (C (((j+1 : ℕ) : F p)⁻¹))*y^(j+1)) =
    -(∑ j ∈ Finset.range (p-1), qm (C (((j+1 : ℕ) : F p)⁻¹))*x^(j+1)) := by
  rw [Finset.mul_sum,← Finset.sum_neg_distrib]
  have hpow (j : ℕ) (hj : j ≤ p) : x^p * y^j=x^(p-j) := by
    calc
      x^p*y^j=(x^(p-j)*x^j)*y^j := by rw [←pow_add, Nat.sub_add_cancel hj]
      _ = x^(p-j)*(x*y)^j := by rw [mul_pow]; ring
      _ = _ := by rw [hxy,one_pow,mul_one]
  have hsum :
      (∑ j ∈ Finset.range (p-1), x^p * (qm (C (((j+1 : ℕ) : F p)⁻¹))*y^(j+1))) =
      ∑ j ∈ Finset.range (p-1), qm (C (((j+1 : ℕ) : F p)⁻¹))*x^(p-(j+1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hle := Finset.mem_range.mp hj
    rw [mul_left_comm, hpow (j+1) (by omega)]
  rw [hsum]
  nth_rw 1 [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hle := Finset.mem_range.mp hj
  rw [show p-1-1-j+1 = p-(j+1) by omega,
    show p-(p-(j+1))=j+1 by omega, Nat.cast_sub (by omega : j+1 ≤ p),
    ZMod.natCast_self, zero_sub, inv_neg, map_neg, map_neg, neg_mul]

theorem qm_log_zero (hp3 : 3<p) (h6 : 6 ∣ p-1) :
    qm (p := p) logpoly = 0 := by
  let x := qm (p := p) X
  let y := qm (p := p) yy
  have hxy : x*y=1 := qm_x_y
  have hs : x+y=1 := qm_x_add_y
  have hlog := qm_log_inversion x y hxy
  have hx : qm (p := p) logpoly =
      ∑ j ∈ Finset.range (p-1), qm (C (((j+1 : ℕ) : F p)⁻¹))*x^(j+1) := by
    simp only [logpoly,map_sum,map_mul,map_pow,x]
  have hy : qm (p := p) (logpoly.comp yy) =
      ∑ j ∈ Finset.range (p-1), qm (C (((j+1 : ℕ) : F p)⁻¹))*y^(j+1) := by
    simp only [logpoly,sum_comp,mul_comp,C_comp,pow_comp,X_comp,map_sum,map_mul,map_pow,y]
  rw [← hx, ← hy, log_reflect (by omega)] at hlog
  have hxp : x^p=x := by
    change (qm (p := p) X)^p=qm X
    rw [← map_pow, (qm_pow (p := p) h6).1]
  rw [hxp] at hlog
  have hh : (x+1)*qm (p := p) logpoly=0 := by linear_combination hlog
  have hthree : (y+1)*(x+1)=3 := by linear_combination hxy + hs
  have hh' := congrArg (fun t : SixthQuot p => (y+1)*t) hh
  rw [←mul_assoc,hthree,mul_zero] at hh'
  have hn3 : (3 : F p) ≠ 0 := cast_ne_zero_of_pos_lt (j := 3) (by omega) hp3
  have hc3 : qm (p := p) (C (3 : F p)) = 3 := by
    rw [C_ofNat, show (3 : P p)=1+1+1 by norm_num, map_add,map_add,map_one]
    norm_num
  have hunit : qm (p := p) (C ((3 : F p)⁻¹))*3=1 := by
    rw [←hc3, ←map_mul, ←C_mul, inv_mul_cancel₀ hn3, C_1,map_one]
  have hh'' := congrArg (fun t : SixthQuot p => qm (C ((3 : F p)⁻¹))*t) hh'
  rw [←mul_assoc,hunit,one_mul,mul_zero] at hh''
  exact hh''

theorem regular_sum_zero (r m : ℕ) (hrel : 3*r+1=p) (hm : 2*m+1=p) :
    (∑ k ∈ (Finset.range (m+1)).erase r,
      ((2*k).choose k : F p) / ((k : F p)-(r : F p))) = 0 := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h6 : 6 ∣ p-1 := ⟨r/2, by rcases hodd with ⟨t, ht⟩; omega⟩
  have h := qm_log_zero (p := p) (by omega) h6
  exact regular_sum_zero_from_log r m hrel hm (AdjoinRoot.mk_eq_zero.mp h)

end A208425Regular

namespace A208425Reduction

open Finset

def summand (n k : ℕ) : ℕ :=
  n.choose k * (n - k).choose k * (n + k).choose k

def coefficient (p k : ℕ) : ℕ :=
  (3 * k).choose k * (2 * k).choose k * (p + k).choose (3 * k + 1)

theorem summand_rewrite (n k : ℕ) :
    summand n k = (3 * k).choose k * (2 * k).choose k * (n + k).choose (3 * k) := by
  have h1 := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
  have h2 := Nat.choose_mul (n := n + k) (k := 3 * k) (s := k) (by omega)
  rw [show 2 * k - k = k by omega] at h1
  rw [show n + k - k = n by omega, show 3 * k - k = 2 * k by omega] at h2
  unfold summand
  rw [← h1]
  calc
    _ = ((n + k).choose k * n.choose (2 * k)) * (2 * k).choose k := by ring
    _ = _ := by rw [← h2]; ring

private theorem sum_choose (p k : ℕ) :
    (∑ i ∈ range p, i.choose k) = p.choose (k + 1) := by
  induction p with
  | zero => simp
  | succ p ih => rw [sum_range_succ, ih, Nat.choose_succ_succ, add_comm]

theorem shifted_hockey (p k : ℕ) :
    (∑ n ∈ range p, (n + k).choose (3 * k)) = (p + k).choose (3 * k + 1) := by
  have hz : (∑ i ∈ range k, i.choose (3 * k)) = 0 :=
    sum_eq_zero fun i hi => Nat.choose_eq_zero_of_lt (by
      have hi' := mem_range.mp hi
      omega)
  rw [add_comm p k, ← sum_choose, sum_range_add, hz, zero_add]
  exact sum_congr rfl fun n _ => by rw [add_comm]

theorem whole_sum (p : ℕ) (hp : 0 < p) :
    (∑ n ∈ range p, ∑ k ∈ range (n + 1), summand n k) =
      ∑ k ∈ range ((p - 1) / 2 + 1), coefficient p k := by
  trans ∑ n ∈ range p, ∑ k ∈ range p, summand n k
  · apply sum_congr rfl
    intro n hn
    have hn' := mem_range.mp hn
    apply sum_subset (range_mono (by omega))
    intro k _ hk
    have hk' : n < k := by simpa using hk
    simp [summand, Nat.choose_eq_zero_of_lt hk']
  simp_rw [summand_rewrite]
  rw [sum_comm]
  simp_rw [← mul_sum, shifted_hockey]
  change (∑ k ∈ range p, coefficient p k) = _
  symm
  apply sum_subset (range_mono (by omega))
  intro k _ hk
  have hk' : (p - 1) / 2 < k := by simpa using hk
  simp [coefficient, Nat.choose_eq_zero_of_lt (show p + k < 3 * k + 1 by omega)]

theorem scaled_coefficient (p k : ℕ) (hp : 0 < p) :
    (3 * k + 1) * coefficient p k =
      p * (p + k).choose k * (p - 1).choose (2 * k) * (2 * k).choose k := by
  have h1 : (p + k).choose (3 * k + 1) * (3 * k + 1) =
      (p + k - 1).choose (3 * k) * (p + k) := by
    rw [Nat.choose_succ_right_eq]
    simpa only [show p + k - 1 + 1 = p + k by omega] using
      (Nat.choose_mul_succ_eq (p + k - 1) (3 * k)).symm
  have h2 := Nat.choose_mul (n := p + k - 1) (k := 3 * k) (s := k) (by omega)
  rw [show p + k - 1 - k = p - 1 by omega, show 3 * k - k = 2 * k by omega] at h2
  have h3 := Nat.choose_mul_succ_eq (p + k - 1) k
  rw [show p + k - 1 + 1 = p + k by omega, show p + k - k = p by omega] at h3
  unfold coefficient
  calc
    _ = ((p + k).choose (3 * k + 1) * (3 * k + 1)) *
        (3 * k).choose k * (2 * k).choose k := by ring
    _ = ((p + k - 1).choose (3 * k) * (3 * k).choose k) *
        (p + k) * (2 * k).choose k := by rw [h1]; ring
    _ = ((p + k - 1).choose k * (p + k)) *
        (p - 1).choose (2 * k) * (2 * k).choose k := by rw [h2]; ring
    _ = _ := by rw [h3]; ring

private theorem choose_plus_prime (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    ((p + k).choose k : ZMod p) = 1 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := p + k) (k := k) (p := p)
  have hmod : (p + k) % p = k := by
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hk]
  have hm : (p + k).choose k ≡ 1 [MOD p] := by
    simpa only [hmod, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk, Nat.choose_self,
      Nat.choose_zero_right, Nat.mul_one] using h
  simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ 1 p).2 hm

private theorem choose_prime_minus_one (p j : ℕ) [Fact p.Prime] (hj : j < p) :
    ((p - 1).choose j : ZMod p) = (-1 : ZMod p)^j := by
  have hp : p.Prime := Fact.out
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.choose_succ_right_eq (p - 1) j
    have hcast : ((p - 1).choose (j + 1) : ZMod p) * ((j : ZMod p) + 1) =
        ((p - 1).choose j : ZMod p) * (-((j : ZMod p) + 1)) := by
      have aux := congrArg (fun n : ℕ => (n : ZMod p)) h
      rw [show p - 1 - j = p - (j + 1) by omega] at aux
      push_cast [Nat.cast_sub (show j + 1 ≤ p by omega)] at aux
      simpa only [ZMod.natCast_self, zero_sub] using aux
    have hnz : ((j : ZMod p) + 1) ≠ 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add, ne_eq, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) hj
    apply mul_right_cancel₀ hnz
    rw [hcast, ih (by omega), pow_succ]
    ring

private theorem scaled_factor (p r k : ℕ) [Fact p.Prime] (hr : p = 3 * r + 1) :
    ((3 * k + 1 : ℕ) : ZMod p) = 3 * ((k : ZMod p) - (r : ZMod p)) := by
  have aux : (3 : ZMod p) * (r : ZMod p) + 1 = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hr
    push_cast at h
    rwa [ZMod.natCast_self, eq_comm] at h
  push_cast
  linear_combination aux

theorem regular_division (p r k : ℕ) [Fact p.Prime] (hr : p = 3 * r + 1)
    (hk : 2 * k < p) (hkr : k ≠ r) :
    p ∣ coefficient p k ∧
      ((coefficient p k / p : ℕ) : ZMod p) =
        ((2 * k).choose k : ZMod p) / (3 * ((k : ZMod p) - (r : ZMod p))) := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  have hscaled := scaled_coefficient p k hp.pos
  have hfacet : (3 * ((k : ZMod p) - (r : ZMod p))) ≠ 0 := by
    apply mul_ne_zero
    · change ((3 : ℕ) : ZMod p) ≠ 0
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    · rw [sub_ne_zero, ne_eq, ZMod.natCast_eq_natCast_iff',
        Nat.mod_eq_of_lt (show k < p by omega), Nat.mod_eq_of_lt (show r < p by omega)]
      exact hkr
  have hcoeff : (coefficient p k : ZMod p) = 0 := by
    have eq := congrArg (fun n : ℕ => (n : ZMod p)) hscaled
    rw [Nat.cast_mul, scaled_factor p r k hr] at eq
    push_cast at eq
    simp only [ZMod.natCast_self, zero_mul] at eq
    exact (mul_eq_zero.mp eq).resolve_left hfacet
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 hcoeff
  refine ⟨hdvd, ?_⟩
  have hquot : (3 * k + 1) * (coefficient p k / p) =
      (p + k).choose k * (p - 1).choose (2 * k) * (2 * k).choose k := by
    apply Nat.mul_left_cancel hp.pos
    calc
      p * ((3*k+1) * (coefficient p k / p)) = (3*k+1) * coefficient p k := by
        rw [← mul_assoc, mul_comm p (3*k+1), mul_assoc, Nat.mul_div_cancel' hdvd]
      _ = _ := by rw [hscaled]; ring
  have hz := congrArg (fun n : ℕ => (n : ZMod p)) hquot
  rw [Nat.cast_mul, scaled_factor p r k hr] at hz
  push_cast at hz
  rw [choose_plus_prime p k (by omega), choose_prime_minus_one p (2*k) hk,
    pow_mul, neg_one_sq, one_pow, one_mul, one_mul] at hz
  exact (eq_div_iff hfacet).2 (by simpa only [mul_comm] using hz)

private theorem paired_factorial (p r : ℕ) [Fact p.Prime] (hr : r < p) (he : Even r) :
    (p + r).choose r * (p - 1).choose r ≡ 1 [MOD p^2] := by
  have hp : p.Prime := Fact.out
  have hc : Nat.Coprime (p^2) (r.factorial^2) :=
    (hp.coprime_factorial_of_lt hr).pow 2 2
  apply Nat.ModEq.cancel_right_of_coprime hc
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  have hprod : (p + r).choose r * (p - 1).choose r * r.factorial^2 =
      ∏ i ∈ range r, (p + 1 + i) * (p - 1 - i) := by
    rw [prod_mul_distrib, ← Nat.ascFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
      Nat.ascFactorial_eq_factorial_mul_choose', Nat.descFactorial_eq_factorial_mul_choose,
      show p + 1 + r - 1 = p + r by omega]
    ring
  rw [hprod, one_mul, Nat.cast_prod]
  have hpzero : ((p : ZMod (p^2))^2) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  calc
    _ = ∏ i ∈ range r, (-1 : ZMod (p^2)) * ((i : ZMod (p^2)) + 1)^2 := by
      apply prod_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [show p - 1 - i = p - (i + 1) by omega]
      push_cast [Nat.cast_sub (show i + 1 ≤ p by omega)]
      linear_combination hpzero
    _ = (-1 : ZMod (p^2))^r * ∏ i ∈ range r, ((i : ZMod (p^2)) + 1)^2 := by
      rw [prod_mul_distrib, prod_const, card_range]
    _ = ((r.factorial^2 : ℕ) : ZMod (p^2)) := by
      rw [he.neg_one_pow, one_mul, prod_pow, Nat.factorial_eq_prod_range_add_one]
      push_cast
      rfl

theorem singular_coefficient (p r : ℕ) [Fact p.Prime] (hr : p = 3*r + 1) :
    coefficient p r ≡ (2*r).choose r [MOD p^2] := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  have hodd := hp.odd_of_ne_two (by omega)
  obtain ⟨u, hu⟩ := hodd
  have he : Even r := ⟨r / 2, by omega⟩
  have hsc := scaled_coefficient p r hp.pos
  rw [← hr] at hsc
  have hprod : coefficient p r =
      (p + r).choose r * (p - 1).choose (2*r) * (2*r).choose r := by
    apply Nat.mul_left_cancel hp.pos
    rw [hsc]
    ring
  have hsym : (p - 1).choose (2*r) = (p - 1).choose r := by
    rw [← Nat.choose_symm (show 2*r ≤ p - 1 by omega),
      show p - 1 - 2*r = r by omega]
  rw [hprod, hsym]
  simpa only [one_mul] using (paired_factorial p r (by omega) he).mul_right ((2*r).choose r)

theorem reduction_to_field_sum (p r : ℕ) [Fact p.Prime] (hr : p = 3 * r + 1)
    (hfield : (∑ k ∈ (range ((p - 1) / 2 + 1)).erase r,
      ((2 * k).choose k : ZMod p) / ((k : ZMod p) - (r : ZMod p))) = 0) :
    (∑ n ∈ range p, ∑ k ∈ range (n + 1), summand n k)
      ≡ (2 * r).choose r [MOD p^2] := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  let S := range ((p - 1) / 2 + 1)
  have hrS : r ∈ S := mem_range.mpr (by omega)
  have facts (k : ℕ) (hk : k ∈ S.erase r) :=
    regular_division p r k hr
      (by have h := mem_range.mp (mem_erase.mp hk).2; omega) (mem_erase.mp hk).1
  have hthree : (3 : ZMod p) ≠ 0 := by
    change ((3 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hsum : (3 : ZMod p) * ((∑ k ∈ S.erase r, coefficient p k / p : ℕ) : ZMod p)
      = 0 := by
    rw [Nat.cast_sum, mul_sum]
    change (∑ k ∈ S.erase r, _) = _
    rw [← hfield]
    apply sum_congr rfl
    intro k hk
    have hkS := mem_range.mp (mem_erase.mp hk).2
    have hkr : (k : ZMod p) - (r : ZMod p) ≠ 0 := by
      rw [sub_ne_zero, ne_eq, ZMod.natCast_eq_natCast_iff',
        Nat.mod_eq_of_lt (show k < p by omega), Nat.mod_eq_of_lt (show r < p by omega)]
      exact (mem_erase.mp hk).1
    rw [(facts k hk).2]
    field_simp
  have hz := (mul_eq_zero.mp hsum).resolve_left hthree
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 hz
  have hsplit : (∑ k ∈ S.erase r, coefficient p k) =
      p * ∑ k ∈ S.erase r, coefficient p k / p := by
    rw [mul_sum]
    exact sum_congr rfl fun k hk => (Nat.mul_div_cancel' (facts k hk).1).symm
  have h0 : (∑ k ∈ S.erase r, coefficient p k) ≡ 0 [MOD p^2] := by
    rw [Nat.modEq_zero_iff_dvd, hsplit, pow_two]
    exact Nat.mul_dvd_mul_left p hdvd
  rw [whole_sum p hp.pos]
  change (∑ k ∈ S, coefficient p k) ≡ (2 * r).choose r [MOD p^2]
  rw [← sum_erase_add S (coefficient p) hrS]
  simpa only [zero_add] using h0.add (singular_coefficient p r hr)

end A208425Reduction

/- The checked interface from the finite-field identity to the exact pinned statement. -/

namespace A208425Reduction

open Finset

theorem original_from_field
    (hField : ∀ (p r : ℕ) [Fact p.Prime], p = 3*r+1 →
      (∑ k ∈ (range ((p-1)/2+1)).erase r,
        ((2*k).choose k : ZMod p) / ((k : ZMod p) - (r : ZMod p))) = 0) :
    type_of% @OeisA208425.conjecture_2 := by
  intro p hp hpmod
  let : Fact p.Prime := ⟨hp⟩
  let r := (p - 1) / 3
  have hp2 := hp.two_le
  have hr : p = 3 * r + 1 := by dsimp [r]; omega
  have hindex : 2 * (p - 1) / 3 = 2 * r := by dsimp [r]; omega
  rw [hindex]
  change (∑ n ∈ range p, ∑ k ∈ range (n + 1), summand n k) ≡
    (2 * r).choose r [MOD p^2]
  exact reduction_to_field_sum p r hr (hField p r hr)

end A208425Reduction

theorem OMA.solution : type_of% @OeisA208425.conjecture_2 := by
  apply A208425Reduction.original_from_field
  intro p r hp hr
  have hp2 := hp.out.two_le
  have hodd := hp.out.odd_of_ne_two (by omega)
  have hpm : 2 * ((p - 1) / 2) + 1 = p := by
    obtain ⟨j, hj⟩ := hodd
    omega
  exact A208425Regular.regular_sum_zero r ((p - 1) / 2) hr.symm hpm
