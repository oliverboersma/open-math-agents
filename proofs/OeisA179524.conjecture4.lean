import FormalConjectures.OEIS.«179524»
import Mathlib

-- Credit: @TaifengYi

/-! # Weighted divisibility for OEIS A179524 -/

section

open Finset
namespace SunQ

noncomputable def plus (q : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ range n, (1 + q ^ (i+1))

noncomputable def geom (q : ℂ) (n : ℕ) : ℂ := ∑ i ∈ range n, q^i

/-- A Laurent polynomial model for an integer q-number. -/
noncomputable def qnum (q : ℂ) : ℤ → ℂ
  | .ofNat n => geom q n
  | .negSucc n => -(q^(n+1))⁻¹ * geom q (n+1)

/-- Twice the half-integer parameter is supplied as an integer. -/
noncomputable def weight (q : ℂ) (v : ℤ) : ℂ :=
  (qnum q (3*v+1) - q^(2*v+1) * qnum q (2*v+1) / (1+q^(v+1))^2) / (1+q)

noncomputable def amp (q : ℂ) (j : ℕ) : ℂ :=
  -8 * (-1)^j * q^(j^2+4*j) * (plus q (2*j))^3 / (plus q j)^4 *
    weight q (-1-2*(j:ℤ))

noncomputable def lift (g : ℂ → ℕ → ℕ → ℂ) (q : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ range n, amp q j * (g q (2*j) j)^2 * ∑ k ∈ range n, q^k * (g q k (2*j))^2

end SunQ

end

section

/- Clearing denominators at odd-order roots of unity. -/

open Finset Polynomial
namespace SunQ

def OddRoot (z : ℂ) := ∃ d : ℕ, Odd d ∧ z^d = 1

theorem root_one : OddRoot 1 := ⟨1, by decide, by simp⟩

theorem root_ne_zero {z : ℂ} (hz : OddRoot z) : z ≠ 0 := by
  obtain ⟨d, hd, hp⟩ := hz
  obtain ⟨k, rfl⟩ := hd
  exact fun h => by simp_all

theorem root_zpow {z : ℂ} (hz : OddRoot z) (e : ℤ) : OddRoot (z^e) := by
  obtain ⟨d, hd, hp⟩ := hz
  exact ⟨d, hd, by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp, one_zpow]⟩

theorem root_plus_ne_zero {z : ℂ} (hz : OddRoot z) : 1 + z ≠ 0 := by
  obtain ⟨d, hd, hp⟩ := hz
  intro hf
  rw [show z = -1 by linear_combination hf, hd.neg_pow, one_pow] at hp
  norm_num at hp

/-- Common denominator for values on odd-order roots, including evaluation at one. -/
def Clear (f : ℂ → ℂ) : Prop :=
  ∃ P D : ℤ[X], ∃ e : ℕ, D.eval 1 = 2^e ∧
    ∀ z, OddRoot z → aeval z D ≠ 0 ∧ aeval z P = f z * aeval z D

theorem Clear.poly (P : ℤ[X]) : Clear (fun z : ℂ => aeval z P) :=
  ⟨P, 1, 0, by simp, by simp⟩

theorem Clear.const (c : ℤ) : Clear (fun _ : ℂ => (c : ℂ)) := by
  simpa using Clear.poly (C c)

theorem Clear.x : Clear (fun z : ℂ => z) := by simpa using Clear.poly X

theorem Clear.congr {f g : ℂ → ℂ} (hf : Clear f) (h : ∀ z, OddRoot z → f z = g z) :
    Clear g := by
  obtain ⟨P,D,e,he,hh⟩ := hf
  exact ⟨P,D,e,he, fun z hz => (h z hz) ▸ hh z hz⟩

theorem Clear.add {f g : ℂ → ℂ} (hf : Clear f) (hg : Clear g) :
    Clear (fun z => f z + g z) := by
  obtain ⟨P,D,e,he,H⟩ := hf
  obtain ⟨R,B,k,hk,K⟩ := hg
  refine ⟨P*B+R*D, D*B,e+k, by simp [he,hk,pow_add], ?_⟩
  intro z hz
  obtain ⟨h₁,h₂⟩ := H z hz
  obtain ⟨h₃,h₄⟩ := K z hz
  simp only [map_mul, map_add, h₂,h₄]
  exact ⟨mul_ne_zero h₁ h₃, by ring⟩

theorem Clear.mul {f g : ℂ → ℂ} (hf : Clear f) (hg : Clear g) :
    Clear (fun z => f z * g z) := by
  obtain ⟨P,D,e,he,H⟩ := hf
  obtain ⟨R,B,k,hk,K⟩ := hg
  refine ⟨P*R, D*B,e+k, by simp [he,hk,pow_add], ?_⟩
  intro z hz
  obtain ⟨h₁,h₂⟩ := H z hz
  obtain ⟨h₃,h₄⟩ := K z hz
  simp only [map_mul, h₂,h₄]
  exact ⟨mul_ne_zero h₁ h₃, by ring⟩

theorem Clear.pow {f : ℂ → ℂ} (hf : Clear f) (k : ℕ) : Clear (fun z => f z ^ k) := by
  induction k with
  | zero => simpa using Clear.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem Clear.neg {f : ℂ → ℂ} (hf : Clear f) : Clear (fun z => -f z) := by
  simpa using (Clear.const (-1)).mul hf

theorem Clear.sub {f g : ℂ → ℂ} (hf : Clear f) (hg : Clear g) :
    Clear (fun z => f z - g z) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem eval_at_one (B : ℤ[X]) : aeval (1 : ℂ) B = ((B.eval 1 : ℤ) : ℂ) := by
  simp only [aeval_def]
  simpa only [map_one, eq_intCast] using (eval₂_hom (algebraMap ℤ ℂ) (p := B) 1)

theorem Clear.inv {f : ℂ → ℂ} (hf : Clear f) {k : ℕ} (h1 : f 1 = 2^k)
    (hn : ∀ z, OddRoot z → f z ≠ 0) : Clear (fun z => (f z)⁻¹) := by
  obtain ⟨P,D,e,he,H⟩ := hf
  refine ⟨D,P,k+e,?_,?_⟩
  · have hP := (H 1 root_one).2
    rw [eval_at_one, eval_at_one, h1, he] at hP
    rw [pow_add]
    exact_mod_cast hP
  · intro z hz
    obtain ⟨hD,hP⟩ := H z hz
    rw [hP]
    exact ⟨mul_ne_zero (hn z hz) hD, by rw [← mul_assoc, inv_mul_cancel₀ (hn z hz), one_mul]⟩

theorem Clear.sum {f : ℕ → ℂ → ℂ} (h : ∀ k, Clear (f k)) (n : ℕ) :
    Clear (fun z => ∑ k ∈ range n, f k z) := by
  induction n with
  | zero => simpa using Clear.const 0
  | succ n ih => simpa only [sum_range_succ] using ih.add (h n)

theorem Clear.prod {f : ℕ → ℂ → ℂ} (h : ∀ k, Clear (f k)) (n : ℕ) :
    Clear (fun z => ∏ k ∈ range n, f k z) := by
  induction n with
  | zero => simpa using Clear.const 1
  | succ n ih => simpa only [prod_range_succ] using ih.mul (h n)

theorem clear_zpow (i : ℤ) : Clear (fun z => z^i) := by
  cases i with
  | ofNat k => simpa using Clear.x.pow k
  | negSucc k =>
    simpa using (Clear.x.pow (k+1)).inv (k := 0) (by simp) (fun z hz => pow_ne_zero _ (root_ne_zero hz))

theorem clear_qnum (i : ℤ) : Clear (fun z => qnum z i) := by
  have hgeom (k : ℕ) : Clear (fun z => geom z k) := Clear.sum (fun j => Clear.x.pow j) k
  cases i with
  | ofNat k => exact hgeom k
  | negSucc k =>
    apply Clear.mul _ (hgeom (k+1))
    exact ((Clear.x.pow (k+1)).inv (k := 0) (by simp) (fun z hz => pow_ne_zero _ (root_ne_zero hz))).neg

theorem clear_weight (v : ℤ) : Clear (fun z => weight z v) := by
  have hplus (e : ℤ) : Clear (fun z : ℂ => 1 + z^e) := by simpa using (Clear.const 1).add (clear_zpow e)
  have hinv (e : ℤ) : Clear (fun z : ℂ => (1 + z^e)⁻¹) :=
    (hplus e).inv (k := 1) (by norm_num) (fun z hz => root_plus_ne_zero (root_zpow hz e))
  have h := ((clear_qnum (3*v+1)).sub (((clear_zpow (2*v+1)).mul (clear_qnum (2*v+1))).mul
    ((hinv (v+1)).pow 2))).mul (hinv 1)
  simpa [weight, div_eq_mul_inv] using h

theorem plus_at_one (k : ℕ) : plus 1 k = 2^k := by norm_num [plus]

theorem plus_ne_zero {z : ℂ} (hz : OddRoot z) (n : ℕ) : plus z n ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro i _
  exact root_plus_ne_zero (by simpa only [zpow_natCast] using root_zpow hz ((i+1 : ℕ) : ℤ))

theorem clear_amp (j : ℕ) : Clear (fun z => amp z j) := by
  have hplus (n : ℕ) : Clear (fun z => plus z n) :=
    Clear.prod (fun i => by simpa using (Clear.const 1).add (Clear.x.pow (i+1))) n
  have hi := (hplus j).inv (plus_at_one j) (fun z hz => plus_ne_zero hz j)
  have hc := (((((Clear.const (-8)).mul ((Clear.const (-1)).pow j)).mul
    (Clear.x.pow (j^2+4*j))).mul ((hplus (2*j)).pow 3)).mul (hi.pow 4)).mul
    (clear_weight (-1-2*(j:ℤ)))
  simpa [amp, div_eq_mul_inv] using hc

theorem clear_lift {g : ℂ → ℕ → ℕ → ℂ} (hg : ∀ n k, Clear (fun z => g z n k)) (n : ℕ) :
    Clear (fun z => lift g z n) :=
  Clear.sum (fun j => ((clear_amp j).mul ((hg (2*j) j).pow 2)).mul
    (Clear.sum (fun k => (Clear.x.pow k).mul ((hg k (2*j)).pow 2)) n)) n

end SunQ

end

section

/- Gaussian binomial coefficients, with their finite product and factorial formulas. -/

namespace SunQ

open Finset Polynomial

noncomputable def gb (Q : ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gb Q n (k + 1) + Q ^ (n - k) * gb Q n k

@[simp] theorem gb_zero (Q : ℂ) (n : ℕ) : gb Q n 0 = 1 := by cases n <;> rfl

theorem gb_zero_of_lt (Q : ℂ) {n k : ℕ} (h : n < k) : gb Q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [gb]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => simp [gb, ih (show n < k+1 by omega), ih (show n < k by omega)]

@[simp] theorem gb_self (Q : ℂ) (n : ℕ) : gb Q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gb, gb_zero_of_lt Q (Nat.lt_succ_self n), ih]

noncomputable def fac (Q : ℂ) (k : ℕ) : ℂ := ∏ i ∈ range k, (1-Q^(i+1))

@[simp] theorem fac_zero (Q : ℂ) : fac Q 0 = 1 := by simp [fac]
theorem fac_succ (Q : ℂ) (k : ℕ) : fac Q (k+1) = fac Q k * (1-Q^(k+1)) := by
  simp [fac, prod_range_succ]

theorem gb_mul_fac (Q : ℂ) {n k : ℕ} (hk : k ≤ n) :
    gb Q n k * fac Q k * fac Q (n-k) = fac Q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases h : k = n
      · subst k; simp
      have h₀ : k ≤ n := by omega
      have h₁ : k+1 ≤ n := by omega
      have hF : fac Q (n-k) = fac Q (n-(k+1)) * (1-Q^(n-k)) := by
        have e : n-k = n-(k+1)+1 := by omega
        rw [e, fac_succ]
      have he : n-k + (k+1) = n+1 := by omega
      simp only [Nat.succ_sub_succ_eq_sub, gb, add_mul]
      calc
        _ = (gb Q n (k+1) * fac Q (k+1) * fac Q (n-(k+1))) * (1-Q^(n-k)) +
            Q^(n-k) * (gb Q n k * fac Q k * fac Q (n-k)) * (1-Q^(k+1)) := by
              nth_rw 1 [hF]
              nth_rw 2 [fac_succ Q k]
              ring
        _ = _ := by rw [ih h₁, ih h₀, fac_succ, ← he, pow_add]; ring

theorem gb_one (n k : ℕ) : gb 1 n k = (n.choose k : ℂ) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gb]
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [gb, Nat.choose_succ_succ, ih, add_comm]

theorem gaussianProduct_coeff (Q : ℂ) (n k : ℕ) :
    (∏ i ∈ range n, (1 + C (Q^i) * X : ℂ[X])).coeff k = Q^(k.choose 2) * gb Q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gb, coeff_one]
  | succ n ih =>
    rw [prod_range_succ, mul_add, mul_one, ← mul_assoc, coeff_add]
    cases k with
    | zero => rw [coeff_mul_X_zero, ih]; simp
    | succ k =>
      rw [coeff_mul_X, coeff_mul_C, ih, ih, Nat.choose_succ_succ, Nat.choose_one_right, gb]
      by_cases hk : k ≤ n
      · have hpow : Q^n = Q^k * Q^(n-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
        rw [pow_add, hpow]
        ring
      · have h₁ : n < k := by omega
        rw [gb_zero_of_lt Q h₁, gb_zero_of_lt Q (show n < k+1 by omega)]
        ring

theorem fac_ne_zero {Q : ℂ} {n d : ℕ} (hQ : IsPrimitiveRoot Q d) (hn : n < d) :
    fac Q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  exact (hQ.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero i)
    (lt_of_le_of_lt (Finset.mem_range.mp hi) hn)).symm
end SunQ

end

section

/- # Reduction of Sun's weighted sum and divisibility by its full 2-primary part -/

open Finset

namespace SunReduction

def coefficient (j : ℕ) : ℤ := (-4 : ℤ)^j * ((2*j).choose j : ℤ)^2

def reduced (n : ℕ) : ℤ :=
  ∑ j ∈ range n, (20 * (j : ℤ) + 7) * coefficient j *
    ∑ k ∈ range n, (k.choose (2*j) : ℤ)^2

theorem row (n k : ℕ) (hk : k < n) :
    OeisA179524.a k = ∑ j ∈ range n, coefficient j * (k.choose (2*j) : ℤ)^2 := by
  unfold OeisA179524.a
  calc
    _ = ∑ j ∈ range (k+1), coefficient j * (k.choose (2*j) : ℤ)^2 := by
      apply sum_congr rfl
      intro j _
      have h := Nat.choose_mul (n := k) (k := 2*j) (s := j) (by omega)
      rw [show 2*j-j=j by omega] at h
      have H : (k.choose (2*j) : ℤ) * ((2*j).choose j : ℤ) =
          (k.choose j : ℤ) * ((k-j).choose j : ℤ) := by exact_mod_cast h
      unfold coefficient
      linear_combination -((-4 : ℤ)^j) * ((k.choose (2*j) : ℤ) * ((2*j).choose j : ℤ) +
        (k.choose j : ℤ) * ((k-j).choose j : ℤ)) * H
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro j _ hj
      simp only [mem_range, not_lt] at hj
      simp [Nat.choose_eq_zero_of_lt (show k < 2*j by omega)]

theorem telescope (n m : ℕ) :
    ∑ k ∈ range n, (2*(k : ℤ) - m + 1) * (k.choose m : ℤ)^2 =
      ((m : ℤ)+1) * (n.choose (m+1) : ℤ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.choose_succ_succ, Nat.cast_add]
    by_cases h : m ≤ n
    · have H : (n.choose (m+1) : ℤ) * ((m : ℤ)+1) =
          (n.choose m : ℤ) * ((n : ℤ)-m) := by
        exact_mod_cast (show (n.choose (m+1) : ℤ) * ((m+1 : ℕ) : ℤ) =
          (n.choose m : ℤ) * ((n : ℤ)-m) by
            rw [← Nat.cast_sub h]
            exact_mod_cast Nat.choose_succ_right_eq n m)
      linear_combination -2 * (n.choose m : ℤ) * H
    · simp [Nat.choose_eq_zero_of_lt (show n < m by omega)]

theorem dvd_telescope (n m : ℕ) : (n : ℤ) ∣
    ∑ k ∈ range n, (2*(k : ℤ) - m + 1) * (k.choose m : ℤ)^2 := by
  rw [telescope]
  cases n with
  | zero => simp
  | succ n =>
    use (n.choose m : ℤ) * ((n+1).choose (m+1) : ℤ)
    have h : ((n : ℤ)+1) * (n.choose m : ℤ) =
        ((n+1).choose (m+1) : ℤ) * ((m : ℤ)+1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n m
    push_cast
    linear_combination -((n+1).choose (m+1) : ℤ) * h

theorem weight_reduction (n : ℕ) : (n : ℤ) ∣
    (∑ k ∈ range n, (20 * (k : ℤ) + 17) * OeisA179524.a k) - reduced n := by
  have expand : (∑ k ∈ range n, (20 * (k : ℤ) + 17) * OeisA179524.a k) =
      ∑ j ∈ range n, ∑ k ∈ range n, (20*(k : ℤ)+17) * coefficient j *
        (k.choose (2*j) : ℤ)^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    rw [row n k (mem_range.mp hk), mul_sum]
    simp [mul_assoc]
  rw [expand, reduced, ← sum_sub_distrib]
  apply dvd_sum
  intro j _
  have h : (∑ k ∈ range n, (20*(k : ℤ)+17) * coefficient j * (k.choose (2*j) : ℤ)^2) -
        (20*(j : ℤ)+7) * coefficient j * (∑ k ∈ range n, (k.choose (2*j) : ℤ)^2) =
      (10 * coefficient j) * ∑ k ∈ range n,
        (2*(k : ℤ) - (2*j : ℕ) + 1) * (k.choose (2*j) : ℤ)^2 := by
    rw [mul_sum, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro k _
    push_cast
    ring
  rw [h]
  exact dvd_mul_of_dvd_right (dvd_telescope n (2*j)) _

theorem solution_iff : (type_of% @OeisA179524.conjecture4) ↔
    ∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ reduced n := by
  constructor
  · intro h n hn
    have hd := dvd_sub (h n hn) (weight_reduction n)
    simpa using hd
  · intro h n hn
    have hd := dvd_add (weight_reduction n) (h n hn)
    simpa using hd

open Polynomial

private theorem two_pow_dvd_binomial_power {R : Type*} [CommRing R] (x : R) (r : ℕ) :
    (2 : R)^(r+1) ∣ (1 + 2*x)^(2^r) - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨b, hb⟩ := ih
    have he : (1+2*x)^(2^r) = 1 + 2^(r+1)*b := by linear_combination hb
    use b*(1+2^r*b)
    rw [Nat.pow_succ 2 r, pow_mul, he]
    rw [pow_succ (2 : R) (r+1), pow_succ (2 : R) r]
    ring

private theorem weighted_choose_coeff (n m : ℕ) :
    ((1+2*X : ℤ[X])^n).coeff m = (n.choose m : ℤ)*2^m := by
  have e := Polynomial.comp_C_mul_X_coeff (p := (1+X : ℤ[X])^n) (r := 2) (n := m)
  simpa only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.one_comp, Polynomial.X_comp,
    map_ofNat, Polynomial.coeff_one_add_X_pow] using e

theorem weighted_choose_period (r k m d : ℕ) (hd : 2^r ∣ d) :
    (2 : ℤ)^(r+1) ∣
      (((k+d).choose m : ℤ) - (k.choose m : ℤ))*2^m := by
  let F : ℤ[X] := 1+2*X
  have h : (2 : ℤ[X])^(r+1) ∣ F^d-1 :=
    (two_pow_dvd_binomial_power (X : ℤ[X]) r).trans (dvd_pow_sub_one_of_dvd hd)
  have h' : (2 : ℤ[X])^(r+1) ∣ F^(k+d)-F^k := by
    rw [show F^(k+d)-F^k = F^k*(F^d-1) by rw [pow_add]; ring]
    exact dvd_mul_of_dvd_right h _
  obtain ⟨b, hb⟩ := h'
  use b.coeff m
  have hc : (2 : ℤ[X])^(r+1) = C ((2 : ℤ)^(r+1)) := by simp
  rw [hc] at hb
  have e := congrArg (fun p : ℤ[X] => p.coeff m) hb
  simpa only [F, coeff_sub, weighted_choose_coeff, coeff_C_mul, sub_mul] using e

private theorem row_period (j r k d : ℕ) (hd : 2^r ∣ d) :
    (2 : ℤ)^(r+1) ∣ coefficient j * ((k+d).choose (2*j) : ℤ)^2 -
      coefficient j * (k.choose (2*j) : ℤ)^2 := by
  obtain ⟨b, hb⟩ := weighted_choose_period r k (2*j) d hd
  use b * (-1 : ℤ)^j * ((2*j).choose j : ℤ)^2 *
    (((k+d).choose (2*j) : ℤ)+(k.choose (2*j) : ℤ))
  unfold coefficient
  rw [show (-4 : ℤ) = (-1) * 2^2 by decide, mul_pow, ← pow_mul]
  linear_combination (-1 : ℤ)^j * ((2*j).choose j : ℤ)^2 *
    (((k+d).choose (2*j) : ℤ)+(k.choose (2*j) : ℤ)) * hb

private theorem prefix_dvd (f : ℕ → ℤ)
    (hper : ∀ r k d : ℕ, 2^r ∣ d → (2 : ℤ)^(r+1) ∣ f (k+d)-f k)
    (r t : ℕ) : (2 : ℤ)^r ∣ ∑ k ∈ range (2^r*t), f k := by
  induction r with
  | zero => simp
  | succ r ih =>
    let M := 2^r*t
    obtain ⟨u, hu⟩ := ih
    have hd : (2 : ℤ)^(r+1) ∣ ∑ k ∈ range M, (f (M+k)-f k) := by
      apply dvd_sum
      intro k _
      rw [Nat.add_comm M k]
      exact hper r k M (dvd_mul_right _ _)
    obtain ⟨v, hv⟩ := hd
    rw [sum_sub_distrib] at hv
    use u+v
    have he : 2^(r+1)*t = M+M := by dsimp [M]; ring
    rw [he, sum_range_add]
    change (∑ k ∈ range M, f k) = (2 : ℤ)^r*u at hu
    rw [pow_succ] at hv ⊢
    linear_combination 2*hu+hv

theorem two_primary (n r : ℕ) (hr : 2^r ∣ n) : (2 : ℤ)^r ∣
    ∑ k ∈ range n, (20*(k : ℤ)+17) * OeisA179524.a k := by
  have hn : (2 : ℤ)^r ∣ (n : ℤ) := by exact_mod_cast hr
  have hR : (2 : ℤ)^r ∣ reduced n := by
    apply dvd_sum
    intro j _
    rw [mul_assoc, mul_sum]
    apply dvd_mul_of_dvd_right
    obtain ⟨t, ht⟩ := hr
    rw [ht]
    exact prefix_dvd _ (row_period j) r t
  have h := dvd_add (hn.trans (weight_reduction n)) hR
  simpa using h

end SunReduction

end

section

/- Evaluation of the lifted sum at one. -/

open Finset
namespace SunQ

theorem qnum_one (v : ℤ) : qnum 1 v = (v : ℂ) := by
  cases v <;> simp [qnum, geom, Int.cast_negSucc]

theorem weight_one (v : ℤ) : weight 1 v = (10*(v:ℂ)+3)/8 := by
  simp only [weight, qnum_one, one_zpow, Int.cast_add, Int.cast_one, Int.cast_mul,
    one_mul, Int.cast_ofNat]
  ring

theorem amp_one (j : ℕ) : amp 1 j = (20*(j:ℂ)+7) * (-4)^j := by
  have hp (k : ℕ) : plus 1 k = 2^k := by norm_num [plus]
  have ha : (-4:ℂ) = (-1)*2^2 := by norm_num
  have hh : (-4:ℂ)^j = (-1)^j*(2^j)^2 := by
    rw [ha, mul_pow, ← pow_mul, Nat.mul_comm 2 j, pow_mul]
  rw [amp, hp, hp, weight_one, hh, Nat.mul_comm 2 j, pow_mul]
  push_cast
  simp only [one_pow, mul_one]
  field_simp
  ring

theorem lift_one (n : ℕ) : lift gb 1 n = (SunReduction.reduced n : ℂ) := by
  unfold lift SunReduction.reduced SunReduction.coefficient
  push_cast
  simp only [amp_one, gb_one, one_pow, one_mul]
  apply sum_congr rfl
  intro j _
  ring

end SunQ

end

section

namespace SunQ
open Finset Polynomial

theorem plus_period {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d) :
    plus q d = 2 := by
  have dh : 0 < d := by obtain ⟨t, rfl⟩ := hd; omega
  have H := X_pow_sub_C_eq_prod hq dh (hd.neg_pow q)
  have H1 := congrArg (Polynomial.eval (1 : ℂ)) H
  simpa [plus, eval_prod, pow_succ, hq.pow_eq_one, one_add_one_eq_two] using H1.symm

theorem plus_blocks {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a b : ℕ) : plus q (a*d+b) = 2^a * plus q b := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Nat.add_assoc, ih]
    have h : plus q (d+b) = plus q d * plus q b := by
      unfold plus
      rw [prod_range_add]
      simp only [Nat.add_assoc, pow_add q d, hq.pow_eq_one, one_mul]
    rw [h, plus_period hd hq, pow_succ, mul_assoc]

theorem qnum_mul_sub (q : ℂ) (hq : q ≠ 0) (v : ℤ) :
    qnum q v * (q-1) = q^v-1 := by
  cases v with
  | ofNat n => simpa [qnum, geom] using geom_sum_mul q n
  | negSucc n =>
    simp only [qnum, geom, zpow_negSucc]
    rw [mul_assoc, geom_sum_mul]
    have hn : q ^ (n+1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring

theorem weight_shift {d : ℕ} (hd : 1 < d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (v k : ℤ) : weight q (v + (d : ℤ)*k) = weight q v := by
  have h0 := hq.ne_zero (by omega)
  have h1 := hq.sub_one_ne_zero hd
  have qp (x i : ℤ) : q^(x+(d:ℤ)*i) = q^x := by
    rw [zpow_add₀ h0, zpow_mul, zpow_natCast, hq.pow_eq_one, one_zpow, mul_one]
  have qn (x i : ℤ) : qnum q (x+(d:ℤ)*i) = qnum q x := by
    apply mul_right_cancel₀ h1
    rw [qnum_mul_sub q h0, qnum_mul_sub q h0, qp]
  unfold weight
  rw [show 3*(v+(d:ℤ)*k)+1 = (3*v+1)+(d:ℤ)*(3*k) by ring, qn,
      show 2*(v+(d:ℤ)*k)+1 = (2*v+1)+(d:ℤ)*(2*k) by ring, qp, qn,
      show v+(d:ℤ)*k+1 = (v+1)+(d:ℤ)*k by ring, qp]

theorem amp_blocks {d : ℕ} (hd : Odd d) (hd1 : 1 < d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a b : ℕ) : amp q (a*d+b) = (-4)^a * amp q b := by
  have hs : (-1 : ℂ)^(a*d+b) = (-1)^a * (-1)^b := by
    rw [pow_add, Nat.mul_comm a d, pow_mul, hd.neg_one_pow]
  have phase : q^((a*d+b)^2+4*(a*d+b)) = q^(b^2+4*b) := by
    rw [show (a*d+b)^2+4*(a*d+b)=d*(a^2*d+2*a*b+4*a)+(b^2+4*b) by ring,
      pow_add, pow_mul, hq.pow_eq_one, one_pow, one_mul]
  have w : weight q (-1-2*((a*d+b:ℕ):ℤ)) = weight q (-1-2*(b:ℤ)) := by
    push_cast
    rw [show -1-2*((a:ℤ)*d+b) = (-1-2*(b:ℤ))+(d:ℤ)*(-2*a) by ring, weight_shift hd1 hq]
  unfold amp
  rw [hs, phase, w, show 2*(a*d+b)=(2*a)*d+2*b by ring, plus_blocks hd hq,
    plus_blocks hd hq, Nat.mul_comm 2 a, pow_mul]
  have hsign : (-4 : ℂ)^a = (-1)^a * (2^a)^2 := by
    rw [← pow_mul, Nat.mul_comm a 2, pow_mul, ← mul_pow]
    norm_num
  rw [hsign]
  by_cases H : plus q b = 0
  · simp [H]
  · field_simp [H]
    <;> ring

end SunQ

end

section

open Polynomial Finset
namespace OMA.Sun

noncomputable def gaussianProduct (q : ℂ) (n : ℕ) : ℂ[X] :=
  ∏ i ∈ range n, (1 + C (q ^ i) * X)

noncomputable def gaussian (q : ℂ) (n k : ℕ) : ℂ :=
  (gaussianProduct q n).coeff k / q ^ (k.choose 2)

theorem gaussian_period {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d) :
    gaussianProduct q d = 1 + X ^ d := by
  have dh : 0 < d := by obtain ⟨t, rfl⟩ := hd; omega
  have hroot : IsPrimitiveRoot (C q : ℂ[X]) d := hq.map_of_injective C_injective
  have H := X_pow_sub_C_eq_prod hroot dh (hd.neg_pow (X : ℂ[X]))
  have H1 := congrArg (Polynomial.eval (1 : ℂ[X])) H
  simpa [gaussianProduct, eval_prod, ← map_pow] using H1.symm

theorem gaussian_blocks {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a b : ℕ) :
    gaussianProduct q (a*d+b) = (1+X^d)^a * gaussianProduct q b := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Nat.add_assoc, ih]
    have h : gaussianProduct q (d+b) = gaussianProduct q d * gaussianProduct q b := by
      simp only [gaussianProduct, prod_range_add, pow_add, hq.pow_eq_one, one_mul]
    rw [h, gaussian_period hd hq, pow_succ, mul_assoc]

theorem gaussianProduct_degree (q : ℂ) (n : ℕ) : (gaussianProduct q n).natDegree ≤ n := by
  unfold gaussianProduct
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ range n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      apply natDegree_add_le_of_degree_le (by simp)
      exact (natDegree_mul_le ..).trans (by simp)
    _ = _ := by simp

private theorem block_coeff {d b : ℕ} (hb : b < d) {q : ℂ} (a c e : ℕ) (he : e < d) :
    (((1+X^d)^a * gaussianProduct q b).coeff (c*d+e)) =
      (a.choose c : ℂ) * (gaussianProduct q b).coeff e := by
  induction a generalizing c with
  | zero =>
    cases c with
    | zero => simp
    | succ c =>
      rw [pow_zero, one_mul, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
      apply coeff_eq_zero_of_natDegree_lt
      have := gaussianProduct_degree q b
      rw [Nat.succ_mul]
      omega
  | succ a ih =>
    rw [pow_succ', add_mul, one_mul, add_mul, mul_assoc, coeff_add]
    cases c with
    | zero =>
      simpa [coeff_X_pow_mul', he.not_ge] using ih 0
    | succ c =>
      have hi : (c+1)*d+e=(c*d+e)+d := by ring
      rw [ih, hi, coeff_X_pow_mul, ih, Nat.choose_succ_succ, Nat.cast_add]
      ring

private theorem phase_period {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a e : ℕ) : q ^ ((a*d+e).choose 2) = q ^ (e.choose 2) := by
  have step (b : ℕ) : q ^ ((d+b).choose 2) = q ^ (b.choose 2) := by
    induction b with
    | zero =>
      simp only [Nat.add_zero, Nat.choose_eq_zero_of_lt (by decide : 0 < 2), pow_zero]
      obtain ⟨t, ht⟩ := hd
      have h : d.choose 2 = d*t := by
        rw [Nat.choose_two_right, ht]
        simp only [Nat.add_sub_cancel]; rw [show (2*t+1)*(2*t) = ((2*t+1)*t)*2 by ring, Nat.mul_div_cancel _ (by decide : 0 < 2)]
      rw [h, pow_mul, hq.pow_eq_one, one_pow]
    | succ b ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ (d+b) 1, Nat.choose_succ_succ b 1,
        Nat.choose_one_right, Nat.choose_one_right, pow_add, pow_add, ih, pow_add, hq.pow_eq_one, one_mul]
  induction a generalizing e with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, Nat.add_assoc, ih, step]

theorem gaussian_lucas {d : ℕ} (hd : Odd d) {q : ℂ} (hq : IsPrimitiveRoot q d)
    (a b c e : ℕ) (hb : b < d) (he : e < d) :
    gaussian q (a*d+b) (c*d+e) = (a.choose c : ℂ) * gaussian q b e := by
  simp only [gaussian, gaussian_blocks hd hq, block_coeff hb _ _ _ he, phase_period hd hq]
  ring

end OMA.Sun

end

section

/- The q-Lucas factorization for the recursive Gaussian coefficients. -/

namespace SunQ

theorem gb_eq_gaussian {Q : ℂ} (hQ : Q ≠ 0) (n k : ℕ) :
    gb Q n k = OMA.Sun.gaussian Q n k := by
  unfold OMA.Sun.gaussian OMA.Sun.gaussianProduct
  rw [gaussianProduct_coeff, eq_div_iff (pow_ne_zero _ hQ), mul_comm]

theorem gb_lucas {d : ℕ} (hd : Odd d) {Q : ℂ} (hQ : IsPrimitiveRoot Q d)
    (a b c e : ℕ) (hb : b < d) (he : e < d) :
    gb Q (a*d+b) (c*d+e) = (a.choose c : ℂ) * gb Q b e := by
  have h : Q ≠ 0 := hQ.ne_zero (by omega)
  simpa only [gb_eq_gaussian h] using OMA.Sun.gaussian_lucas hd hQ a b c e hb he

end SunQ

end

section

/- Reduction of the lifted sum at every multiple of an odd primitive root order. -/

open Finset
namespace SunQ

private theorem sum_blocks (m d : ℕ) (f : ℕ → ℂ) :
    ∑ i ∈ range (m*d), f i = ∑ a ∈ range m, ∑ b ∈ range d, f (a*d+b) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

private noncomputable def term (g : ℂ → ℕ → ℕ → ℂ) (q : ℂ) (j k : ℕ) : ℂ :=
  amp q j * (g q (2*j) j)^2 * (q^k * (g q k (2*j))^2)

private theorem lift_eq_sum (g : ℂ → ℕ → ℕ → ℂ) (q : ℂ) (n : ℕ) :
    lift g q n = ∑ j ∈ range n, ∑ k ∈ range n, term g q j k := by
  simp [lift, term, mul_sum]

private theorem term_blocks (g : ℂ → ℕ → ℕ → ℂ) {d : ℕ} {q : ℂ} (hq : IsPrimitiveRoot q d)
    (lucas : ∀ a b c e, b < d → e < d →
      g q (a*d+b) (c*d+e) = (a.choose c : ℂ) * g q b e)
    (tri : ∀ {n k}, n < k → g q n k = 0)
    (ampB : ∀ a b, amp q (a*d+b) = (-4)^a * amp q b)
    (J s K b : ℕ) (hs : s < d) (hb : b < d) :
    term g q (J*d+s) (K*d+b) =
      ((-4 : ℂ)^J * ((2*J).choose J : ℂ)^2 * (K.choose (2*J) : ℂ)^2) * term g q s b := by
  unfold term
  by_cases h : 2*s < d
  · rw [show 2*(J*d+s) = (2*J)*d+2*s by ring, lucas _ _ _ _ h hs,
      lucas _ _ _ _ hb h, ampB, pow_add, Nat.mul_comm K d, pow_mul, hq.pow_eq_one, one_pow, one_mul]
    ring
  · have r : 2*s-d < d := by omega
    have hzero : g q (2*s-d) s = 0 := tri (by omega)
    have hc : g q (2*s) s = 0 := by
      have hl := lucas 1 (2*s-d) 0 s r hs
      simpa only [one_mul, Nat.add_sub_of_le (by omega : d ≤ 2*s), zero_mul, zero_add, hzero, mul_zero] using hl
    have hzero' : g q (2*(J*d+s)) (J*d+s) = 0 := by
      rw [show 2*(J*d+s) = (2*J+1)*d+(2*s-d) by rw [add_mul, one_mul, Nat.add_assoc, Nat.add_sub_of_le (by omega : d ≤ 2*s)]; ring,
        lucas _ _ _ _ r hs, hzero, mul_zero]
    simp only [hzero', hc, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]

/-- A full period of zero implies vanishing at every multiple of the root order. -/
theorem lift_vanish_multiple (g : ℂ → ℕ → ℕ → ℂ) {d : ℕ} {q : ℂ} (hq : IsPrimitiveRoot q d)
    (lucas : ∀ a b c e, b < d → e < d →
      g q (a*d+b) (c*d+e) = (a.choose c : ℂ) * g q b e)
    (tri : ∀ {n k}, n < k → g q n k = 0)
    (ampB : ∀ a b, amp q (a*d+b) = (-4)^a * amp q b)
    (vanish : lift g q d = 0) (n : ℕ) (hn : d ∣ n) : lift g q n = 0 := by
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.mul_comm d m, lift_eq_sum, sum_blocks]
  apply sum_eq_zero
  intro J _
  simp_rw [sum_blocks m d]
  rw [sum_comm]
  apply sum_eq_zero
  intro K _
  calc
    _ = ∑ s ∈ range d, ∑ b ∈ range d,
          ((-4 : ℂ)^J * ((2*J).choose J : ℂ)^2 * (K.choose (2*J) : ℂ)^2) * term g q s b := by
      apply sum_congr rfl; intro s hs
      apply sum_congr rfl; intro b hb
      exact term_blocks g hq lucas tri ampB J s K b (mem_range.mp hs) (mem_range.mp hb)
    _ = 0 := by simp_rw [← mul_sum]; rw [← lift_eq_sum, vanish, mul_zero]

theorem gb_vanish_multiple {d : ℕ} (hd : Odd d) (hd1 : 1 < d)
    {q : ℂ} (hq : IsPrimitiveRoot q d) (vanish : lift gb q d = 0)
    {n : ℕ} (hn : d ∣ n) : lift gb q n = 0 :=
  lift_vanish_multiple gb hq (gb_lucas hd hq) (gb_zero_of_lt q) (amp_blocks hd hd1 hq)
    vanish n hn

end SunQ

end

section

namespace OMA.Sun
open Polynomial Finset

/-- Specialization at 1 of a polynomial vanishing at the nontrivial roots of unity. -/
theorem divisor_of_cyclotomic_vanishing {m : ℕ} (hm : 0 < m) (P : ℤ[X])
    (vanish : ∀ d, d ∣ m → 1 < d → ∀ z : ℂ, IsPrimitiveRoot z d → aeval z P = 0) :
    (m : ℤ) ∣ P.eval 1 := by
  classical
  let t := m.divisors.erase 1
  have spec {d : ℕ} (hd : d ∈ t) : d ∣ m ∧ 1 < d := by
    obtain ⟨hn, hd⟩ := Finset.mem_erase.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    exact ⟨(Nat.mem_divisors.mp hd).1, by omega⟩
  have hp : (∏ d ∈ t, cyclotomic d ℤ) ∣ P := by
    refine Finset.prod_dvd_of_isRelPrime ?_ ?_
    · intro d hd e he hne
      have hd' := cyclotomic.irreducible (Nat.zero_lt_of_lt (spec hd).2)
      have he' := cyclotomic.irreducible (Nat.zero_lt_of_lt (spec he).2)
      apply hd'.isRelPrime_iff_not_dvd.mpr
      intro hdiv
      exact hne <| cyclotomic_injective <| eq_of_monic_of_associated
        (cyclotomic.monic _ ℤ) (cyclotomic.monic _ ℤ) (hd'.associated_of_dvd he' hdiv)
    · intro d hd
      obtain ⟨hdm, hd1⟩ := spec hd
      have hpos : 0 < d := by omega
      have hz := Complex.isPrimitiveRoot_exp d hpos.ne'
      rw [cyclotomic_eq_minpoly hz hpos]
      exact minpoly.isIntegrallyClosed_dvd (hz.isIntegral hpos) (vanish d hdm hd1 _ hz)
  change (∏ d ∈ m.divisors.erase 1, cyclotomic d ℤ) ∣ P at hp
  rw [prod_cyclotomic_eq_geom_sum hm] at hp
  obtain ⟨Q, hQ⟩ := hp
  refine ⟨Q.eval 1, ?_⟩
  rw [hQ, eval_mul, eval_finsetSum]
  simp

/-- Denominator clearing is harmless at an odd modulus if the specialized denominator
is a power of two. Multiplicities of primes dividing the modulus are included. -/
theorem odd_divisor_of_cleared_vanishing {m e : ℕ} (hm : Odd m) (P : ℤ[X]) (T : ℤ)
    (specialize : P.eval 1 = (2 : ℤ)^e * T)
    (vanish : ∀ d, d ∣ m → 1 < d → ∀ z : ℂ, IsPrimitiveRoot z d → aeval z P = 0) :
    (m : ℤ) ∣ T := by
  have hp : 0 < m := by obtain ⟨k, rfl⟩ := hm; omega
  have H := divisor_of_cyclotomic_vanishing hp P vanish
  rw [specialize] at H
  have hc : IsCoprime (m : ℤ) ((2 : ℤ)^e) := by
    exact_mod_cast (hm.coprime_two_right.pow_right e).isCoprime
  exact hc.dvd_of_dvd_mul_left H

end OMA.Sun

end

section

/- Divisibility of the integer sequence from single-period vanishing. -/

open Finset Polynomial
namespace SunQ

theorem clear_gb (n k : ℕ) : Clear (fun z => gb z n k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simpa [gb] using Clear.const 1
    | succ k => simpa [gb] using Clear.const 0
  | succ n ih =>
    cases k with
    | zero => simpa [gb] using Clear.const 1
    | succ k => exact (ih (k+1)).add ((Clear.x.pow (n-k)).mul (ih k))

theorem from_period_vanishing
    (period : ∀ {d : ℕ}, Odd d → 1 < d → ∀ {q : ℂ}, IsPrimitiveRoot q d → lift gb q d = 0) :
    type_of% @OeisA179524.conjecture4 := by
  intro n hn
  obtain ⟨k,m,hm,heq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have hmD : m ∣ n := heq ▸ dvd_mul_left _ _
  have hkD : 2^k ∣ n := heq ▸ dvd_mul_right _ _
  obtain ⟨P,D,e,hD,hP⟩ := clear_lift clear_gb n
  change ∀ z, OddRoot z → aeval z D ≠ 0 ∧ aeval z P = lift gb z n * aeval z D at hP
  have h1 := (hP 1 root_one).2
  rw [eval_at_one, eval_at_one, lift_one, hD, mul_comm] at h1
  have hodd : (m : ℤ) ∣ SunReduction.reduced n := by
    refine OMA.Sun.odd_divisor_of_cleared_vanishing hm P _ (e := e) (by exact_mod_cast h1) ?_
    intro d hdm hd q hq
    have ho := hm.of_dvd_nat hdm
    have hzero := gb_vanish_multiple ho hd hq (period ho hd hq) (hdm.trans hmD)
    rw [(hP q ⟨d, ho, hq.pow_eq_one⟩).2, hzero, zero_mul]
  have hmZ : (m : ℤ) ∣ (n : ℤ) := by exact_mod_cast hmD
  have hmS := dvd_add (hmZ.trans (SunReduction.weight_reduction n)) hodd
  rw [sub_add_cancel] at hmS
  have hcop : IsCoprime ((2 : ℤ)^k) (m : ℤ) := by
    exact_mod_cast (hm.coprime_two_right.symm.pow_left k).isCoprime
  have h := hcop.mul_dvd (SunReduction.two_primary n k hkD) hmS
  have hz : (n : ℤ) = (2 : ℤ)^k * (m : ℤ) := by exact_mod_cast heq
  rwa [← hz] at h

end SunQ

end

section

/- # Gaussian convolution and reflection at a primitive root -/

namespace SunQ

open Finset

private noncomputable def hgb (Q : ℂ) (b i : ℕ) := gb Q (b+i) b

private theorem hgb_succ (Q : ℂ) (b i : ℕ) :
    hgb Q (b+1) (i+1) = hgb Q (b+1) i + Q^(i+1)*hgb Q b (i+1) := by
  unfold hgb
  rw [show b+1+(i+1) = (b+(i+1))+1 by omega, gb,
    show b+(i+1)-b = i+1 by omega, show b+1+i = b+(i+1) by omega]

private noncomputable def conv (Q : ℂ) (r s N : ℕ) : ℂ :=
  ∑ i ∈ range (N+1), Q^((s+1)*i) * hgb Q r i * hgb Q s (N-i)

private theorem conv_zero (Q : ℂ) (r s : ℕ) : conv Q r s 0 = 1 := by
  simp [conv, hgb]

private theorem conv_first (Q : ℂ) (r N : ℕ) :
    conv Q r 0 (N+1) = conv Q r 0 N + Q^(N+1)*hgb Q r (N+1) := by
  simp [conv, hgb, sum_range_succ, gb_zero]

private theorem conv_succ (Q : ℂ) (r s N : ℕ) :
    conv Q r (s+1) (N+1) =
      conv Q r (s+1) N + Q^(N+1)*conv Q r s (N+1) := by
  unfold conv
  rw [sum_range_succ (n := N+1), sum_range_succ (n := N+1) (f := fun i =>
    Q^((s+1)*i) * hgb Q r i * hgb Q s (N+1-i)), mul_add (Q^(N+1)), mul_sum]
  simp only [Nat.sub_self, hgb, add_zero, gb_self, mul_one]
  rw [← add_assoc (∑ i ∈ range (N+1), _)]
  apply congrArg₂ (· + ·)
  · rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range_succ_iff.mp hi
    have step := hgb_succ Q s (N-i)
    unfold hgb at step
    rw [show N+1-i = N-i+1 by omega, step,
      show (s+1+1)*i = (s+1)*i+i by ring, pow_add]
    have e : Q^i*Q^(N-i+1) = Q^(N+1) := by rw [← pow_add]; congr 1; omega
    linear_combination Q^((s+1)*i) * gb Q (r+i) r * gb Q (s+(N-i+1)) s * e
  · rw [show (s+1+1)*(N+1) = (N+1)+(s+1)*(N+1) by ring, pow_add]
    ring

theorem gaussian_convolution (Q : ℂ) (r s N : ℕ) :
    (∑ i ∈ range (N+1), Q^((s+1)*i) * gb Q (r+i) r * gb Q (s+(N-i)) s) =
      gb Q (r+s+1+N) (r+s+1) := by
  change conv Q r s N = hgb Q (r+s+1) N
  induction s generalizing N with
  | zero =>
    induction N with
    | zero => simp [conv_zero, hgb]
    | succ N ih => rw [conv_first, ih]; simpa only [Nat.add_zero] using (hgb_succ Q r N).symm
  | succ s ih =>
    induction N with
    | zero => simp [conv_zero, hgb]
    | succ N ihN =>
      rw [conv_succ, ihN, ih, show r+(s+1)+1 = (r+s+1)+1 by omega]
      exact (hgb_succ Q (r+s+1) N).symm

private theorem gb_step_bottom {Q : ℂ} {d k b : ℕ} (hq : IsPrimitiveRoot Q d)
    (hk : k < d) (hb : b < k) :
    gb Q k (b+1) * (1-Q^(b+1)) = gb Q k b * (1-Q^(k-b)) := by
  have l := gb_mul_fac Q (n := k) (k := b+1) (by omega)
  have r := gb_mul_fac Q (n := k) (k := b) (by omega)
  have ef : fac Q (k-b) = fac Q (k-(b+1)) * (1-Q^(k-b)) := by
    rw [show k-b = (k-(b+1))+1 by omega, fac_succ]
  rw [fac_succ Q b] at l
  rw [ef] at r
  apply mul_right_cancel₀ (mul_ne_zero (fac_ne_zero (n := b) hq (by omega))
    (fac_ne_zero (n := k-(b+1)) hq (by omega)))
  linear_combination l-r

private theorem gb_step_both {Q : ℂ} {d x b : ℕ} (hq : IsPrimitiveRoot Q d)
    (hx : x < d) (hb : b ≤ x) :
    gb Q (x+1) (b+1) * (1-Q^(b+1)) = gb Q x b * (1-Q^(x+1)) := by
  have l := gb_mul_fac Q (n := x+1) (k := b+1) (by omega)
  have r := gb_mul_fac Q hb
  simp only [Nat.succ_sub_succ_eq_sub, fac_succ] at l
  apply mul_right_cancel₀ (mul_ne_zero (fac_ne_zero (n := b) hq (by omega))
    (fac_ne_zero (n := x-b) hq (by omega)))
  linear_combination l-(1-Q^(x+1))*r

theorem gb_reflect {Q : ℂ} {d k : ℕ} (hq : IsPrimitiveRoot Q d) (hk : k < d)
    (b : ℕ) (hb : b ≤ k) :
    gb Q (d-1+b-k) b * Q^(b*k) = (-1)^b * Q^(b.choose 2) * gb Q k b := by
  induction b with
  | zero => simp
  | succ b ih =>
    let x := d-1+b-k
    have hbk : b < k := by omega
    have hstep := gb_step_both (x := x) (b := b) hq (by dsimp [x]; omega) (by dsimp [x]; omega)
    have hlow := gb_step_bottom hq hk hbk
    have e : Q^(x+1)*Q^(k-b) = 1 := by
      rw [← pow_add, show x+1+(k-b) = d by dsimp [x]; omega, hq.pow_eq_one]
    have er : (1-Q^(x+1))*Q^(k-b) = -(1-Q^(k-b)) := by linear_combination -e
    have ep : Q^((b+1)*k) = Q^(b*k)*Q^b*Q^(k-b) := by
      rw [← pow_add, ← pow_add, Nat.add_mul, one_mul]
      congr 1
      omega
    have ec : (b+1).choose 2 = b.choose 2+b := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
    rw [show d-1+(b+1)-k = x+1 by dsimp [x]; omega, ec, pow_add Q, pow_succ (-1 : ℂ) b]
    apply mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm (hq.pow_ne_one_of_pos_of_lt
      (l := b+1) (by omega) (by omega))))
    calc
      _ = (gb Q x b*Q^(b*k))*Q^b*((1-Q^(x+1))*Q^(k-b)) := by
        rw [ep]
        linear_combination Q^(b*k)*Q^b*Q^(k-b)*hstep
      _ = _ := by
        rw [er, show gb Q x b*Q^(b*k) = _ from ih (by omega)]
        linear_combination (-1 : ℂ)^b * Q^(b.choose 2) * Q^b * hlow

theorem primitive_sum_square {Q : ℂ} {d : ℕ} (hq : IsPrimitiveRoot Q d)
    (j : ℕ) (hj : 2*j < d) :
    (∑ k ∈ range d, Q^k*(gb Q k (2*j))^2) = Q^(j*(2*j+3))*gb Q (d+2*j) (4*j+1) := by
  let b := 2*j
  let N := d-1-b
  let E := j*(2*j+3)
  have hb : b < d := hj
  have hq0 : Q ≠ 0 := hq.ne_zero (by omega)
  have hsign : (-1 : ℂ)^b = 1 := by simp [b, pow_mul]
  have hc : b.choose 2 + E = b*b+b := by
    dsimp [b,E]
    rw [Nat.choose_two_right, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
    cases j with
    | zero => decide
    | succ j =>
      rw [show 2*(j+1)-1=2*j+1 by omega]
      ring
  have front : ∑ k ∈ range b, Q^k*(gb Q k b)^2 = 0 := by
    apply sum_eq_zero
    intro k hk
    simp [gb_zero_of_lt Q (mem_range.mp hk)]
  change (∑ k ∈ range d, Q^k*(gb Q k b)^2) = Q^E*_
  calc
    _ = ∑ i ∈ range (N+1), Q^(b+i)*(gb Q (b+i) b)^2 := by
      conv_lhs => rw [show d = b+(N+1) by dsimp [N]; omega]
      rw [sum_range_add, front, zero_add]
    _ = Q^E * ∑ i ∈ range (N+1), Q^((b+1)*i)*gb Q (b+i) b*gb Q (b+(N-i)) b := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range_succ_iff.mp hi
      have hh := gb_reflect hq (k := b+i) (by dsimp [N] at hi'; omega) b (by omega)
      have ei : d-1+b-(b+i) = b+(N-i) := by dsimp [N] at *; omega
      rw [hsign, one_mul, ei] at hh
      have ep : Q^(b*(b+i))*Q^(b+i) = Q^(b.choose 2)*Q^E*Q^((b+1)*i) := by
        rw [← pow_add, ← pow_add, ← pow_add, hc]
        congr 1
        ring
      apply mul_left_cancel₀ (pow_ne_zero (b.choose 2) hq0)
      calc
        _ = (gb Q (b+(N-i)) b * Q^(b*(b+i))) * Q^(b+i) * gb Q (b+i) b := by rw [hh]; ring
        _ = _ := by
          linear_combination gb Q (b+(N-i)) b * gb Q (b+i) b * ep
    _ = _ := by
      rw [gaussian_convolution, show b+b+1+N = d+2*j by dsimp [b,N] at *; omega,
        show b+b+1 = 4*j+1 by dsimp [b]; omega]

end SunQ

end

section

/- Finite product reversals for the root-of-unity argument. -/
open Finset

namespace SunReflect

noncomputable def factors (Q ε : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ range n, (1 + ε*Q^(i+1))

noncomputable def stride (Q ε X : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ range n, (1 + ε*X*Q^i)

theorem factors_succ (Q ε : ℂ) (n : ℕ) :
    factors Q ε (n+1) = factors Q ε n * (1+ε*Q^(n+1)) := by
  simp [factors, prod_range_succ]

theorem stride_succ (Q ε X : ℂ) (n : ℕ) :
    stride Q ε X (n+1) = stride Q ε X n * (1+ε*X*Q^n) := by
  simp [stride, prod_range_succ]

theorem reverse_factors (Q ε X : ℂ) (hε : ε*ε=1) {H : ℕ} (hX : Q^H*X=1)
    (t : ℕ) (ht : t ≤ H) :
    factors Q ε H * (X^t * Q^(t.choose 2)) =
      factors Q ε (H-t) * ε^t * stride Q ε X t := by
  induction t with
  | zero => simp [stride]
  | succ t ih =>
    have ht' : t ≤ H := by omega
    have hh : H-t = (H-(t+1))+1 := by omega
    have hpow : Q^(H-t)*(X*Q^t)=1 := by
      rw [mul_comm X, ← mul_assoc, ← pow_add, Nat.sub_add_cancel ht', hX]
    have hfactor : (1+ε*Q^(H-t))*(X*Q^t)= ε*(1+ε*X*Q^t) := by
      calc
        _ = X*Q^t + ε*(Q^(H-t)*(X*Q^t)) := by ring
        _ = ε*(1+ε*X*Q^t) := by rw [hpow]; linear_combination -(X*Q^t)*(hε)
    calc
      _ = (factors Q ε H * (X^t*Q^(t.choose 2)))*(X*Q^t) := by
        rw [Nat.choose_succ_succ t 1, Nat.choose_one_right, pow_add, pow_succ X]; ring
      _ = (factors Q ε (H-(t+1))*(1+ε*Q^(H-t)))* ε^t*stride Q ε X t*(X*Q^t) := by
        rw [ih ht', hh, factors_succ]
      _ = factors Q ε (H-(t+1))* ε^(t+1)* stride Q ε X (t+1) := by
        rw [stride_succ, pow_succ]
        linear_combination (factors Q ε (H-(t+1))*ε^t*stride Q ε X t)*hfactor

theorem stride_self (Q ε : ℂ) (n : ℕ) : stride Q ε Q n = factors Q ε n := by
  unfold stride factors
  apply prod_congr rfl
  intro i _
  rw [pow_succ]
  ring

theorem twice_choose_two (n : ℕ) : 2*n.choose 2 + n = n*n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]; nlinarith

theorem even_triangle (t : ℕ) : 2*t + (2*t).choose 2 = t*(2*t+1) := by
  have h := twice_choose_two (2*t)
  nlinarith

theorem reverse_even (Q ε : ℂ) (hε : ε*ε=1) {H : ℕ} (hp : Q^(H+1)=1)
    (t : ℕ) (ht : 2*t ≤ H) :
    factors Q ε H * Q^(t*(2*t+1)) =
      factors Q ε (H-2*t)*factors Q ε (2*t) := by
  have h := reverse_factors Q ε Q hε (by simpa [pow_succ] using hp : Q^H*Q=1) (2*t) ht
  rw [← pow_add, even_triangle, stride_self, pow_mul ε, pow_two, hε, one_pow, mul_one] at h
  exact h

theorem reverse_half (q ε : ℂ) (hε : ε*ε=1) {H : ℕ} (hp : (q^2)^H*q=1)
    (t : ℕ) (ht : t ≤ H) :
    factors (q^2) ε H * q^(t*t) =
      factors (q^2) ε (H-t) * ε^t * stride (q^2) ε q t := by
  have h := reverse_factors (q^2) ε q hε hp t ht
  rwa [← pow_mul, ← pow_add, Nat.add_comm t, twice_choose_two] at h

theorem split_factors (q ε : ℂ) (t : ℕ) :
    factors q ε (2*t) = factors (q^2) ε t * stride (q^2) ε q t := by
  induction t with
  | zero => simp [factors, stride]
  | succ t ih =>
    rw [show 2*(t+1)=2*t+1+1 by omega, factors_succ, factors_succ, ih,
      factors_succ, stride_succ, ← pow_mul, ← pow_mul,
      show 2*(t+1)=2*t+1+1 by omega, pow_succ q (2*t)]
    ring

theorem square_factors (q : ℂ) (t : ℕ) :
    factors q (-1) t * factors q 1 t = factors (q^2) (-1) t := by
  induction t with
  | zero => simp [factors]
  | succ t ih =>
    rw [factors_succ, factors_succ, factors_succ, ← pow_mul, Nat.mul_comm 2, pow_mul]
    simp only [neg_one_mul, one_mul]
    linear_combination (1-(q^(t+1))^2)*ih

end SunReflect

end

section

/- Gaussian and plus-factor reversals at a root of odd order. -/

namespace SunReflect
open SunQ Finset

theorem neg_fac (Q : ℂ) (n : ℕ) : factors Q (-1) n = fac Q n := by
  simp [factors, fac, sub_eq_add_neg]
theorem pos_plus (Q : ℂ) (n : ℕ) : factors Q 1 n = plus Q n := by
  simp [factors, plus]

theorem square_fac (Q : ℂ) (n : ℕ) : fac Q n * plus Q n = fac (Q^2) n := by
  simpa only [neg_fac,pos_plus] using square_factors Q n

theorem fac_nz {Q : ℂ} {d n : ℕ} (hQ : IsPrimitiveRoot Q d) (hn : n < d) : fac Q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' := mem_range.mp hi
  exact sub_ne_zero.mpr (hQ.pow_ne_one_of_pos_of_lt (by omega) (by omega : i+1<d)).symm

theorem plus_nz {Q : ℂ} {d : ℕ} (hQ : IsPrimitiveRoot Q d) (hd : Odd d) (n : ℕ) : plus Q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi hzero
  have H : Q^(i+1) = -1 := by linear_combination hzero
  have E := congrArg (fun w : ℂ => w^d) H
  change (Q^(i+1))^d = (-1:ℂ)^d at E
  rw [← pow_mul, Nat.mul_comm (i+1) d, pow_mul, hQ.pow_eq_one, one_pow, hd.neg_one_pow] at E
  norm_num at E

theorem fac_square_nz {Q : ℂ} {d n : ℕ} (hQ : IsPrimitiveRoot Q d)
    (hd : Odd d) (hn : n < d) : fac (Q^2) n ≠ 0 := by
  rw [← square_fac]
  exact mul_ne_zero (fac_nz hQ hn) (plus_nz hQ hd _)

theorem gb_quot {Q : ℂ} {d n k : ℕ} (hQ : IsPrimitiveRoot Q d)
    (hn : n < d) (hk : k ≤ n) :
    gb Q n k = fac Q n / (fac Q k * fac Q (n-k)) := by
  apply (eq_div_iff <| mul_ne_zero (fac_nz hQ (by omega)) (fac_nz hQ (by omega))).mpr
  rw [← mul_assoc, gb_mul_fac Q hk]

theorem reflect_fac {Q : ℂ} {H : ℕ} (hQ : IsPrimitiveRoot Q (H+1)) (t : ℕ) (ht : 2*t ≤ H) :
    fac Q (H-2*t) = fac Q H * Q^(t*(2*t+1)) / fac Q (2*t) := by
  apply (eq_div_iff (fac_nz hQ (by omega))).mpr
  simpa only [neg_fac] using (reverse_even Q (-1) (by norm_num) hQ.pow_eq_one t ht).symm

theorem reflect_plus {Q : ℂ} {H : ℕ} (hQ : IsPrimitiveRoot Q (H+1)) (hd : Odd (H+1))
    (t : ℕ) (ht : 2*t ≤ H) :
    plus Q (H-2*t) = plus Q H * Q^(t*(2*t+1)) / plus Q (2*t) := by
  apply (eq_div_iff (plus_nz hQ hd _)).mpr
  simpa only [pos_plus] using (reverse_even Q 1 (by norm_num) hQ.pow_eq_one t ht).symm

theorem reflect_row {Q : ℂ} {H : ℕ} (hQ : IsPrimitiveRoot Q (H+1)) (t : ℕ) (ht : 4*t ≤ H) :
    gb Q (H-2*t) (2*t) = gb Q (4*t) (2*t) / Q^(6*t^2+t) := by
  have f2 := fac_nz hQ (show 2*t<H+1 by omega)
  have f4 := fac_nz hQ (show 4*t<H+1 by omega)
  have fH := fac_nz hQ (show H<H+1 by omega)
  have q0 := hQ.ne_zero (by omega)
  rw [gb_quot hQ (by omega) (by omega), gb_quot hQ (by omega) (by omega),
    show H-2*t-2*t = H-4*t by omega, show 4*t-2*t=2*t by omega,
    reflect_fac hQ t (by omega), show 4*t=2*(2*t) by omega, reflect_fac hQ (2*t) (by omega)]
  have phase : Q^(t*(2*t+1)) * Q^(6*t^2+t) = Q^((2*t)*(2*(2*t)+1)) := by
    rw [← pow_add]; congr 1; ring
  field_simp [q0, f2, f4, fH]
  linear_combination phase * (fac Q H * fac Q (2*(2*t)))

noncomputable def normalized (Q : ℂ) (t : ℕ) : ℂ := gb Q (2*t) t / (plus Q t)^2

theorem normalized_eq {Q : ℂ} {d t : ℕ} (hQ : IsPrimitiveRoot Q d) (ht : 2*t<d) :
    normalized Q t = fac Q (2*t) / fac (Q^2) t ^ 2 := by
  rw [normalized, gb_quot hQ ht (by omega), show 2*t-t=t by omega, ← square_fac]
  ring

theorem normalized_reflect {Q : ℂ} {h t : ℕ} (hQ : IsPrimitiveRoot Q (2*h+1))
    (ht : t≤h) :
    normalized Q (h-t) = normalized Q h * Q^t * normalized Q t := by
  have hodd : Odd (2*h+1) := ⟨h,rfl⟩
  have hQ0 := hQ.ne_zero (by omega)
  have hp : (Q^2)^h * Q = 1 := by rw [← pow_mul, ← pow_succ, hQ.pow_eq_one]
  have rev := reverse_half Q (-1) (by norm_num) hp t ht
  simp only [neg_fac] at rev
  have sqrev := congrArg (fun x : ℂ => x^2) rev
  change (fac (Q^2) h*Q^(t*t))^2 = (fac (Q^2) (h-t)*(-1)^t*stride (Q^2) (-1) Q t)^2 at sqrev
  have sign : ((-1:ℂ)^t)^2=1 := by rw [← pow_mul, Nat.mul_comm t 2, pow_mul]; norm_num
  simp only [mul_pow,sign,mul_one] at sqrev
  have split := split_factors Q (-1) t
  simp only [neg_fac] at split
  have ft : fac (Q^2) t ≠ 0 := fac_square_nz hQ hodd (by omega)
  have fh : fac (Q^2) h ≠ 0 := fac_square_nz hQ hodd (by omega)
  have fj : fac (Q^2) (h-t) ≠ 0 := fac_square_nz hQ hodd (by omega)
  have f2 : fac Q (2*t) ≠ 0 := fac_nz hQ (by omega)
  have hs : stride (Q^2) (-1) Q t = fac Q (2*t)/fac (Q^2) t := by
    apply (eq_div_iff ft).mpr
    rw [mul_comm, ← split]
  rw [hs, div_pow] at sqrev
  have ratio : (fac (Q^2) (h-t))^2 =
      (fac (Q^2) h)^2 * (Q^(t*t))^2 * (fac (Q^2) t)^2 / (fac Q (2*t))^2 := by
    field_simp [ft, f2] at sqrev ⊢
    linear_combination -sqrev
  rw [normalized_eq hQ (by omega), normalized_eq hQ (by omega), normalized_eq hQ (by omega), ratio,
    show 2*(h-t)=2*h-2*t by omega, reflect_fac hQ t (by omega)]
  have phase : Q^(t*(2*t+1)) = (Q^(t*t))^2 * Q^t := by rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [phase]
  field_simp [ft, fh, fj, f2, hQ0]

end SunReflect

end

section

/- The reflected expansion of the lifted sum at a primitive odd-order root. -/

namespace SunReflect
open SunQ Finset

noncomputable def gaussianTerm (Q : ℂ) (t : ℕ) : ℂ :=
  (-1)^t * Q^(3*t^2) * (normalized Q t)^2 * gb Q (4*t) (2*t) /
    (plus Q (2*t))^3 * weight Q (2*(t:ℤ))

noncomputable def factor (Q : ℂ) (h : ℕ) : ℂ :=
  -8 * (-1)^h * Q^(3*h^2+7*h) * (plus Q (2*h))^3 * (normalized Q h)^2

theorem low_row {Q : ℂ} {h j t : ℕ} (hq : IsPrimitiveRoot Q (2*h+1)) (hjt : j+t=h)
    (ht : 2*t ≤ h) :
    gb Q ((2*h+1)+2*j) (4*j+1) = gb Q (4*t) (2*t) / Q^(6*t^2+t) := by
  have odd : Odd (2*h+1) := ⟨h,rfl⟩
  have H := gb_lucas odd hq 1 (2*j) 1 (2*h-4*t) (by omega) (by omega)
  simp only [one_mul, Nat.choose_self, Nat.cast_one] at H
  rw [show 4*j+1 = 2*h+1+(2*h-4*t) by omega, H, ← reflect_row hq t (by omega)]
  have n : 2*j = 2*h-2*t := by omega
  rw [n, gb_quot hq (by omega) (by omega), gb_quot hq (by omega) (by omega),
    show 2*h-2*t-(2*h-4*t)=2*t by omega, show 2*h-2*t-2*t=2*h-4*t by omega]
  rw [mul_comm (fac Q (2*h-4*t))]

theorem high_row {Q : ℂ} {h j t : ℕ} (hq : IsPrimitiveRoot Q (2*h+1)) (hjt : j+t=h)
    (ht : h<2*t) : gb Q ((2*h+1)+2*j) (4*j+1) = 0 := by
  have odd : Odd (2*h+1) := ⟨h,rfl⟩
  have H := gb_lucas odd hq 1 (2*j) 0 (4*j+1) (by omega) (by omega)
  simpa [gb_zero_of_lt Q (show 2*j < 4*j+1 by omega)] using H

private theorem phase_reflect {Q : ℂ} {h j t : ℕ} (hq : IsPrimitiveRoot Q (2*h+1)) (hjt : j+t=h) :
    Q^(3*j^2+7*j) * (Q^(t*(2*t+1)))^3 * (Q^t)^2 =
      Q^(3*h^2+7*h) * Q^(3*t^2) * Q^(6*t^2+t) := by
  simp only [← pow_mul, ← pow_add]
  have e : (3*j^2+7*j+t*(2*t+1)*3+t*2)+(2*h+1)*(3*t) =
    (3*h^2+7*h+3*t^2)+(6*t^2+t) := by rw [← hjt]; ring
  rw [← e, pow_add Q _ ((2*h+1)*(3*t)), pow_mul Q (2*h+1), hq.pow_eq_one, one_pow, mul_one]

theorem reflect_term {Q : ℂ} {h j t : ℕ} (hq : IsPrimitiveRoot Q (2*h+1))
    (hh : 0<h) (hjt : j+t=h) (ht : 2*t≤h) :
    amp Q j * (gb Q (2*j) j)^2 * (Q^(j*(2*j+3)) * gb Q ((2*h+1)+2*j) (4*j+1)) =
      factor Q h * gaussianTerm Q t := by
  have hQ0 := hq.ne_zero (by omega)
  have odd : Odd (2*h+1) := ⟨h,rfl⟩
  have phase := phase_reflect hq hjt
  have hj : j=h-t := by omega
  have plusR := reflect_plus hq odd t (by omega)
  rw [show 2*h-2*t = 2*j by omega] at plusR
  have normR := normalized_reflect hq (show t≤h by omega)
  rw [← hj] at normR
  have sgn : (-1:ℂ)^j = (-1)^h*(-1)^t := by
    rw [← hjt, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
  have wgt : weight Q (-1-2*(j:ℤ)) = weight Q (2*(t:ℤ)) := by
    rw [show -1-2*(j:ℤ) = 2*(t:ℤ)+((2*h+1:ℕ):ℤ)*(-1) by push_cast; omega,
      weight_shift (by omega) hq]
  calc
    _ = -8*(-1)^j*Q^(3*j^2+7*j)*(plus Q (2*j))^3*(normalized Q j)^2*
          (gb Q (4*t) (2*t) / Q^(6*t^2+t)) * weight Q (2*(t:ℤ)) := by
      rw [low_row hq hjt ht, amp, wgt, normalized,
        show 3*j^2+7*j = j^2+4*j+j*(2*j+3) by ring, pow_add]
      ring
    _ = _ := by
      rw [normR, plusR, sgn, factor, gaussianTerm]
      field_simp [hQ0, plus_nz hq odd (2*t)]
      apply congrArg Neg.neg
      linear_combination (norm := ring)
        ((plus Q (2*h))^3*(normalized Q h)^2*(normalized Q t)^2*
          gb Q (4*t) (2*t)*weight Q (2*(t:ℤ)))*phase

theorem reflected_vanishing {Q : ℂ} {h : ℕ} (hq : IsPrimitiveRoot Q (2*h+1)) (hh : 0<h)
    (rows : ∀ j, 2*j < 2*h+1 →
      (∑ k ∈ range (2*h+1), Q^k * (gb Q k (2*j))^2) =
        Q^(j*(2*j+3))*gb Q ((2*h+1)+2*j) (4*j+1))
    (vanish : (∑ t ∈ range (h/2+1), gaussianTerm Q t)=0) : lift gb Q (2*h+1)=0 := by
  classical
  let f (j : ℕ) := amp Q j * (gb Q (2*j) j)^2 *
    ∑ k ∈ range (2*h+1), Q^k * (gb Q k (2*j))^2
  change (∑ j ∈ range (2*h+1), f j)=0
  have H₁ : (∑ j ∈ range (h+1), f j) = ∑ j ∈ range (2*h+1), f j := by
    apply sum_subset (range_mono (by omega))
    intro j hj hnj
    simp only [mem_range] at hj hnj
    have H : (∑ k ∈ range (2*h+1), Q^k * (gb Q k (2*j))^2)=0 := by
      apply sum_eq_zero; intro k hk
      have := mem_range.mp hk
      simp [gb_zero_of_lt Q (show k<2*j by omega)]
    simp [f,H]
  rw [← H₁, ← sum_range_reflect f (h+1)]
  simp only [Nat.add_sub_cancel] 
  have H₂ : (∑ t ∈ range (h/2+1), f (h-t)) = ∑ t ∈ range (h+1), f (h-t) := by
    apply sum_subset (range_mono (by omega))
    intro t ht hnt
    simp only [mem_range] at ht hnt
    simp only [f, rows (h-t) (by omega), high_row hq (by omega : h-t+t=h) (by omega), mul_zero]
  rw [← H₂]
  calc
    _ = ∑ t ∈ range (h/2+1), factor Q h * gaussianTerm Q t := by
      apply sum_congr rfl
      intro t ht
      have ht' := mem_range.mp ht
      simpa only [f, rows (h-t) (by omega)] using
        reflect_term hq hh (by omega : h-t+t=h) (by omega)
    _ = 0 := by rw [← mul_sum, vanish, mul_zero]

end SunReflect

end

section

/- A denominator-cleared q-WZ certificate for the terminating sum used in A179524. -/

namespace SunCertificate

variable {R : Type*} [CommRing R]

/-- Numerator of the weight with denominator `(1+q*x)*(1-b*q*x^2)`. -/
def weightNumerator (q b x : R) : R :=
  (1-x)*(1+q*x)*(1-b*q*x^2) + x*(1-b*q^2*x^3)*(1-b*x^2)

/-- The contiguous relation between the parameters `b` and `b*q²`, after
clearing the three binomial denominators. The telescoping multiplier of the
kernel at `b` is `b*(1-x)^2*(1+x)/(1-b)`. -/
theorem qWZPolynomial (q b x : R) :
    (1-b)*weightNumerator q b x*(1-b*q^3*x^2) -
      (1-b*x)*(1-b*x^2)*weightNumerator q (b*q^2) x =
    -b*q^3*x^3*(1-q*x)*(1-b*x)*(1-b*x^2)*(1-b*q^2*x^2) -
      b*(1-x)^2*(1+x)*(1+q*x)*(1-b*q*x^2)*(1-b*q^3*x^2) := by
  unfold weightNumerator
  ring

def poch (u a : R) (t : ℕ) : R := ∏ i ∈ Finset.range t, (1-a*u^i)

theorem poch_succ (u a : R) (t : ℕ) : poch u a (t+1) = poch u a t*(1-a*u^t) :=
  Finset.prod_range_succ _ _

theorem poch_shift (u a : R) (t : ℕ) :
    (1-a)*poch u (a*u) t = (1-a*u^t)*poch u a t := by
  induction t with
  | zero => simp [poch]
  | succ t ih =>
    rw [poch_succ, poch_succ, ← mul_assoc, ih, pow_succ]
    ring

def num (q b : R) (t : ℕ) : R := (-1)^t*q^(3*t*t)*
  poch (q^2) q t^2*poch (q^2) b t*poch (q^2) b (2*t)

def den (q b : R) (t : ℕ) : R :=
  poch (q^2) (q^2) t*poch (q^2) (q^2) (2*t)*poch (q^2) (b*q) (2*t)

theorem num_shift (q b : R) (t : ℕ) : let x := (q^2)^t;
    (1-b)^2*num q (b*q^2) t = num q b t*(1-b*x)*(1-b*x^2) := by
  dsimp [num]
  have h₁ := poch_shift (q^2) b t
  have h₂ := poch_shift (q^2) b (2*t)
  rw [Nat.mul_comm 2 t, pow_mul] at h₂
  rw [Nat.mul_comm 2 t]
  linear_combination (norm := ring)
    (-1)^t*q^(3*t*t)*poch (q^2) q t^2 *
      ((1-b)*poch (q^2) (b*q^2) (t*2)*h₁ + (1-b*(q^2)^t)*poch (q^2) b t*h₂)

theorem den_shift (q b : R) (t : ℕ) : let x := (q^2)^t;
    (1-b*q)*den q (b*q^2) t = (1-b*q*x^2)*den q b t := by
  dsimp [den]
  have h := poch_shift (q^2) (b*q) (2*t)
  rw [Nat.mul_comm 2 t, pow_mul] at h
  rw [Nat.mul_comm 2 t, show b*q^2*q = b*q*q^2 by ring]
  linear_combination (norm := ring) poch (q^2) (q^2) t * poch (q^2) (q^2) (t*2) * h

theorem poch_two_succ (u a : R) (t : ℕ) :
    poch u a (2*(t+1)) = poch u a (2*t)*(1-a*(u^t)^2)*(1-a*u*(u^t)^2) := by
  rw [show 2*(t+1)=2*t+1+1 by omega, poch_succ, poch_succ, pow_succ,
    Nat.mul_comm 2 t, pow_mul]
  ring

theorem num_succ (q b : R) (t : ℕ) : let x := (q^2)^t; num q b (t+1) =
    num q b t*(-q^3*x^3)*(1-q*x)^2*(1-b*x)*(1-b*x^2)*(1-b*q^2*x^2) := by
  dsimp [num]
  rw [show 3*(t+1)*(t+1) = 3*t*t + 2*t*3 + 3 by ring, pow_add q _ 3, pow_add q (3*t*t) (2*t*3), pow_mul q (2*t) 3,
    pow_mul q 2 t, pow_succ (-1 : R), poch_succ, poch_succ, poch_two_succ]
  ring

theorem den_succ (q b : R) (t : ℕ) : let x := (q^2)^t; den q b (t+1) =
    den q b t*(1-q^2*x)*(1-q^2*x^2)*(1-q^4*x^2)*(1-b*q*x^2)*(1-b*q^3*x^2) := by
  dsimp [den]
  rw [poch_succ, poch_two_succ, poch_two_succ]
  ring

end SunCertificate

end

section

/- Finite telescoping for the polynomial contiguous relation. -/

namespace SunCertificate

variable {K : Type*} [Field K]

def kernel (q b : K) (t : ℕ) := num q b t / den q b t

def bracket (q b x : K) := weightNumerator q b x / ((1+q*x)*(1-b*q*x^2))

def flux (q b : K) (t : ℕ) :=
  let x := (q^2)^t
  b*(1-x)^2*(1+x)/(1-b)*kernel q b t

def term (q b : K) (t : ℕ) := kernel q b t * bracket q b ((q^2)^t)

private theorem ratio {n d n' d' a c l m : K} (hd : d ≠ 0) (hd' : d' ≠ 0)
    (ha : a ≠ 0) (hm : m ≠ 0) (h₁ : a*n'=n*c) (h₂ : l*d'=m*d) :
    n'/d' = n/d*(c*l)/(a*m) := by
  field_simp [hd,hd',ha,hm]
  linear_combination (norm := ring) d*m*h₁ - n*c*h₂

set_option maxHeartbeats 1500000 in
theorem contiguous (q b : K) (t : ℕ) (hd : den q b t ≠ 0)
    (hd' : den q (b*q^2) t ≠ 0) (hds : den q b (t+1) ≠ 0)
    (hb : 1-b ≠ 0) (hc : 1-b*q ≠ 0) :
    term q b t - ((1-b)/(1-b*q))*term q (b*q^2) t =
      flux q b (t+1) - flux q b t := by
  let x := (q^2)^t
  have n₁ := num_shift q b t
  have d₁ := den_shift q b t
  have n₂ := num_succ q b t
  have d₂ := den_succ q b t
  dsimp only at n₁ d₁ n₂ d₂
  change den q b (t+1) = den q b t*(1-q^2*x)*(1-q^2*x^2)*(1-q^4*x^2)*(1-b*q*x^2)*(1-b*q^3*x^2) at d₂
  have hnz : den q b t*(1-q^2*x)*(1-q^2*x^2)*(1-q^4*x^2)*(1-b*q*x^2)*(1-b*q^3*x^2) ≠ 0 :=
    d₂ ▸ hds
  simp only [mul_ne_zero_iff] at hnz
  obtain ⟨⟨⟨⟨⟨_,h₁⟩,h₂⟩,h₃⟩,hy⟩,hz⟩ := hnz
  have hx : 1+q*x ≠ 0 := by
    intro hh
    apply h₂
    linear_combination (norm := ring) (1-q*x)*hh
  have hx' : 1-q*x ≠ 0 := by
    intro hh
    apply h₂
    linear_combination (norm := ring) (1+q*x)*hh
  have hx₂ : 1+q^2*x ≠ 0 := by
    intro hh
    apply h₃
    linear_combination (norm := ring) (1-q^2*x)*hh
  have r₁ : kernel q (b*q^2) t = kernel q b t *
      ((1-b*x)*(1-b*x^2)*(1-b*q)) / ((1-b)^2*(1-b*q*x^2)) := by
    apply ratio hd hd' (pow_ne_zero 2 hb) hy _ d₁
    simpa only [mul_assoc] using n₁
  have r₂ : kernel q b (t+1) = kernel q b t *
      ((-q^3*x^3)*(1-q*x)*(1-b*x)*(1-b*x^2)*(1-b*q^2*x^2)) /
      ((1-q^2*x)^2*(1+q^2*x)*(1+q*x)*(1-b*q*x^2)*(1-b*q^3*x^2)) := by
    unfold kernel
    rw [n₂,d₂]
    change num q b t*(-q^3*x^3)*(1-q*x)^2*(1-b*x)*(1-b*x^2)*(1-b*q^2*x^2) / _ = _
    rw [show 1-q^2*x^2 = (1-q*x)*(1+q*x) by ring,
      show 1-q^4*x^2 = (1-q^2*x)*(1+q^2*x) by ring]
    field_simp [hd,h₁,hx',hx,hx₂,hy,hz]
    <;> ring
  unfold term bracket flux
  change kernel q b t * (weightNumerator q b x / ((1+q*x)*(1-b*q*x^2))) -
      ((1-b)/(1-b*q))*(kernel q (b*q^2) t*(weightNumerator q (b*q^2) x / ((1+q*x)*(1-b*q^2*q*x^2)))) =
    b*(1-(q^2)^(t+1))^2*(1+(q^2)^(t+1))/(1-b)*kernel q b (t+1) -
      b*(1-x)^2*(1+x)/(1-b)*kernel q b t
  rw [r₁,r₂,pow_succ (q^2) t, show b*q^2*q*x^2 = b*q^3*x^2 by ring]
  change _ = b*(1-x*q^2)^2*(1+x*q^2)/(1-b)*_ - _
  rw [mul_comm x (q^2)]
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  field_simp [hx,hy,hz,h₁,hx₂,hb,hc]
  unfold weightNumerator
  ring

end SunCertificate

end

section

/- The finite terminating sum at a primitive root of odd order. -/

open Finset
namespace SunCertificate

private def par (q : ℂ) (h k : ℕ) := q^(2*h+1-2*k)

private theorem evenFactor {q : ℂ} {h i : ℕ} (hq : IsPrimitiveRoot q (2*h+1))
    (hi : 0 < i) (hj : i < 2*h+1) : 1-q^(2*i) ≠ 0 := by
  intro hh
  have hd := hq.dvd_of_pow_eq_one (2*i) (sub_eq_zero.mp hh).symm
  have cop : (2*h+1).Coprime 2 := by
    exact Nat.coprime_two_right.mpr ⟨h, by omega⟩
  exact (not_lt.mpr (Nat.le_of_dvd hi (cop.dvd_of_dvd_mul_left hd))) hj

private theorem denRoot {q : ℂ} {h k t : ℕ} (hq : IsPrimitiveRoot q (2*h+1))
    (hk : k ≤ h) (_ht : 2*t < 2*h+1) (hj : h-k+2*t < 2*h+1) :
    den q (par q h k) t ≠ 0 := by
  have hu (s : ℕ) (hs : s ≤ 2*t) : poch (q^2) (q^2) s ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have := Finset.mem_range.mp hi
    rw [← pow_succ' (q^2), ← pow_mul]
    exact evenFactor hq (by omega) (by omega)
  apply mul_ne_zero (mul_ne_zero (hu t (by omega)) (hu (2*t) (le_refl _)))
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have := Finset.mem_range.mp hi
  change 1-(q^(2*h+1-2*k)*q)*(q^2)^i ≠ 0
  rw [← pow_succ, ← pow_mul, ← pow_add,
    show (2*h+1-2*k+1)+2*i = 2*(h-k+1+i) by omega]
  exact evenFactor hq (by omega) (by omega)

private theorem par_succ {q : ℂ} {h k : ℕ} (hk : k+1 ≤ h) :
    par q h (k+1)*q^2 = par q h k := by
  unfold par
  rw [← pow_add, show 2*h+1-2*(k+1)+2 = 2*h+1-2*k by omega]

private theorem kernel_outside {q : ℂ} {h k t : ℕ} (hq : IsPrimitiveRoot q (2*h+1))
    (hk : k ≤ h) (ht : k < 2*t) : kernel q (par q h k) t = 0 := by
  have hf : poch (q^2) (par q h k) (2*t) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr ht)
    change 1 - q^(2*h+1-2*k)*(q^2)^k = 0
    rw [← pow_mul, ← pow_add, show 2*h+1-2*k+2*k = 2*h+1 by omega, hq.pow_eq_one, sub_self]
  simp [kernel, num, hf]

private theorem contiguousRoot {q : ℂ} {h k : ℕ} (hq : IsPrimitiveRoot q (2*h+1))
    (hk : k+1 ≤ h) (t : ℕ) :
    term q (par q h (k+1)) t - ((1-par q h (k+1))/(1-par q h (k+1)*q))*term q (par q h k) t =
      flux q (par q h (k+1)) (t+1) - flux q (par q h (k+1)) t := by
  by_cases ht : 2*t ≤ k+1
  · rw [← par_succ (q:=q) hk]
    apply contiguous
    · exact denRoot hq hk (by omega) (by omega)
    · rw [par_succ hk]
      exact denRoot hq (by omega) (by omega) (by omega)
    · exact denRoot hq hk (by omega) (by omega)
    · exact sub_ne_zero.mpr (Ne.symm <| hq.pow_ne_one_of_pos_of_lt (by omega) (by omega))
    · unfold par
      rw [← pow_succ, show 2*h+1-2*(k+1)+1 = 2*(h-k) by omega]
      exact evenFactor hq (by omega) (by omega)
  · simp [term, flux, kernel_outside hq hk (by omega : k+1 < 2*t),
      kernel_outside hq (by omega : k ≤ h) (by omega : k < 2*t),
      kernel_outside hq hk (by omega : k+1 < 2*(t+1))]

private theorem telescope (f : ℕ → ℂ) (n : ℕ) :
    ∑ t ∈ range n, (f (t+1)-f t) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

theorem terminating {q : ℂ} {h k : ℕ} (hq : IsPrimitiveRoot q (2*h+1)) (hk : k ≤ h) :
    ∑ t ∈ range (h/2+1), term q (par q h k) t = 0 := by
  induction k with
  | zero =>
    apply sum_eq_zero
    intro t ht
    rcases t with _|t
    · simp [term, bracket, weightNumerator, par, hq.pow_eq_one]
    · simp [term, kernel_outside hq (by omega : 0 ≤ h) (by omega : 0 < 2*(t+1))]
  | succ k ih =>
    have recurrence := sum_congr (s₁ := range (h/2+1)) rfl (fun t _ => contiguousRoot hq hk t)
    rw [sum_sub_distrib, ← mul_sum, ih (by omega), mul_zero, sub_zero, telescope] at recurrence
    simpa [flux, kernel_outside hq hk (by omega : k+1 < 2*(h/2+1))] using recurrence

theorem terminatingFinal {q : ℂ} {h : ℕ} (hq : IsPrimitiveRoot q (2*h+1)) :
    ∑ t ∈ range (h/2+1), term q q t = 0 := by
  have eq : par q h h = q := by unfold par; rw [show 2*h+1-2*h=1 by omega, pow_one]
  simpa only [eq] using terminating hq (le_refl h)

end SunCertificate

end

section

/- The terminating q-WZ summands specialize to the reflected Gaussian row. -/

namespace SunCertificate
open SunQ SunReflect

private theorem poch_even (Q : ℂ) (n : ℕ) : poch (Q^2) (Q^2) n = fac (Q^2) n := by
  unfold poch fac
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_succ]
  ring

private theorem poch_odd {Q : ℂ} {d : ℕ} (hQ : IsPrimitiveRoot Q d) (hd : Odd d)
    {n : ℕ} (hn : n < d) : poch (Q^2) Q n = fac Q (2*n)/fac (Q^2) n := by
  have h := split_factors Q (-1) n
  simp only [neg_fac] at h
  have H : poch (Q^2) Q n = stride (Q^2) (-1) Q n := by
    simp only [poch, stride, neg_mul, one_mul, sub_eq_add_neg]
  rw [H, eq_div_iff (fac_square_nz hQ hd hn), mul_comm, ← h]

theorem kernel_at_root {Q : ℂ} {d t : ℕ} (hQ : IsPrimitiveRoot Q d) (hd : Odd d)
    (ht : 4*t < d) :
    num Q Q t / den Q Q t =
      (-1)^t * Q^(3*t^2) * (normalized Q t)^2 * gb Q (4*t) (2*t) / (plus Q (2*t))^3 := by
  have h₁ : t < d := by omega
  have h₂ : 2*t < d := by omega
  have f₁ := fac_nz hQ h₁
  have f₂ := fac_nz hQ h₂
  have p₁ := plus_nz hQ hd t
  have p₂ := plus_nz hQ hd (2*t)
  unfold num den
  rw [show Q*Q=Q^2 by ring, poch_odd hQ hd h₁, poch_odd hQ hd h₂,
    show 2*(2*t)=4*t by omega, poch_even, poch_even, normalized_eq hQ h₂,
    gb_quot hQ ht (show 2*t ≤ 4*t by omega), show 4*t-2*t=2*t by omega,
    ← square_fac, ← square_fac, show 3*t*t=3*t^2 by ring]
  field_simp [f₁, f₂, p₁, p₂]

private theorem one_add_pow_ne_zero {Q : ℂ} {d : ℕ} (hQ : IsPrimitiveRoot Q d) (hd : Odd d)
    (n : ℕ) : 1 + Q^n ≠ 0 := by
  intro hh
  have h : Q^n = -1 := by linear_combination hh
  have H := congrArg (fun z : ℂ => z^d) h
  change (Q^n)^d = (-1:ℂ)^d at H
  rw [← pow_mul, Nat.mul_comm, pow_mul, hQ.pow_eq_one, one_pow, hd.neg_one_pow] at H
  norm_num at H
private theorem weight_in_x {Q : ℂ} {d t : ℕ} (hQ : IsPrimitiveRoot Q d) (hodd : Odd d) (hd : 1 < d) :
    (1-Q^2)*weight Q (2*(t:ℤ)) =
      1-Q*((Q^2)^t)^3 - Q*((Q^2)^t)^2*(1-Q*((Q^2)^t)^2)/(1+Q*((Q^2)^t))^2 := by
  let x := (Q^2)^t
  have h₀ := hQ.ne_zero (by omega)
  have h₁ := hQ.sub_one_ne_zero hd
  have E (m : ℕ) : Q^(m*(2*(t:ℤ))+1) = Q*x^m := by
    have e : (m:ℤ)*(2*(t:ℤ))+1 = ((m*(2*t)+1 : ℕ):ℤ) := by push_cast; ring
    rw [e, zpow_natCast, pow_succ, Nat.mul_comm m, pow_mul, pow_mul]
    ring
  have N (m : ℕ) : qnum Q (m*(2*(t:ℤ))+1) = (1-Q*x^m)/(1-Q) := by
    have H := qnum_mul_sub Q h₀ (m*(2*(t:ℤ))+1)
    rw [E] at H
    apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h₁)))).mpr
    linear_combination -H
  have E₁ : Q ^ (2 * (t:ℤ) + 1) = Q*x := by simpa using E 1
  unfold weight
  have N₃ := N 3
  have N₂ := N 2
  have E₂ := E 2
  norm_num only [Nat.cast_ofNat] at N₃ N₂ E₂
  rw [N₃,N₂,E₂,E₁]
  change (1-Q^2)*(((1-Q*x^3)/(1-Q) - Q*x^2*((1-Q*x^2)/(1-Q))/(1+Q*x)^2)/(1+Q)) =
    1-Q*x^3-Q*x^2*(1-Q*x^2)/(1+Q*x)^2
  have h : 1+Q ≠ 0 := by simpa using one_add_pow_ne_zero hQ hodd 1
  have H : 1-Q ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h₁))
  rw [show 1-Q^2=(1-Q)*(1+Q) by ring]
  field_simp [h,H]

theorem bracket_at_root {Q : ℂ} {d t : ℕ} (hQ : IsPrimitiveRoot Q d) (hodd : Odd d) (hd : 1 < d)
    (ht : 4*t < d) :
    weightNumerator Q Q ((Q^2)^t) / ((1+Q*(Q^2)^t)*(1-Q*Q*((Q^2)^t)^2)) =
       (1-Q^2)*weight Q (2*(t:ℤ)) := by
  let x := (Q^2)^t
  rw [weight_in_x hQ hodd hd]
  change weightNumerator Q Q x / ((1+Q*x)*(1-Q*Q*x^2)) =
    1-Q*x^3-Q*x^2*(1-Q*x^2)/(1+Q*x)^2
  have H : Q*x=Q^(2*t+1) := by dsimp [x]; rw [pow_succ Q (2*t), pow_mul]; ring
  have hm : 1-Q*x ≠ 0 := by
    rw [H]
    exact sub_ne_zero.mpr (hQ.pow_ne_one_of_pos_of_lt (by omega) (by omega)).symm
  have hp : 1+Q*x ≠ 0 := by rw [H]; exact one_add_pow_ne_zero hQ hodd _
  have hden : 1-Q*Q*x^2 ≠ 0 := by rw [show 1-Q*Q*x^2=(1-Q*x)*(1+Q*x) by ring]; exact mul_ne_zero hm hp
  rw [sub_div' (pow_ne_zero 2 hp)]
  apply (div_eq_div_iff (mul_ne_zero hp hden) (pow_ne_zero 2 hp)).mpr
  unfold weightNumerator
  ring

end SunCertificate

end

section

/- Vanishing of the normalized reflected row by finite telescoping. -/
namespace SunCertificate
open SunQ SunReflect Finset

theorem normalized_vanish {Q : ℂ} {h : ℕ} (hQ : IsPrimitiveRoot Q (2*h+1)) (hh : 0 < h) :
    ∑ t ∈ range (h/2+1), (-1)^t * Q^(3*t^2) * (normalized Q t)^2 *
      gb Q (4*t) (2*t) / (plus Q (2*t))^3 * weight Q (2*(t:ℤ)) = 0 := by
  have hs := terminatingFinal hQ
  have hodd : Odd (2*h+1) := ⟨h, rfl⟩
  have hd : 1 < 2*h+1 := by omega
  have H : (1-Q^2) * (∑ t ∈ range (h/2+1), (-1)^t * Q^(3*t^2) * (normalized Q t)^2 *
      gb Q (4*t) (2*t) / (plus Q (2*t))^3 * weight Q (2*(t:ℤ))) = 0 := by
    rw [← hs, mul_sum]
    apply sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    have ht4 : 4*t < 2*h+1 := by omega
    unfold term kernel bracket
    rw [kernel_at_root hQ hodd ht4, bracket_at_root hQ hodd hd ht4]
    ring
  exact (mul_eq_zero.mp H).resolve_left (sub_ne_zero.mpr
    (hQ.pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0) (by omega)).symm)

end SunCertificate

end

section

/- # Vanishing of the full Gaussian lift on a primitive odd-order period -/

namespace SunQ

open Finset SunCertificate SunReflect

theorem primitive_block {d : ℕ} (hd : Odd d) (hd1 : 1 < d) {Q : ℂ}
    (hq : IsPrimitiveRoot Q d) : lift gb Q d = 0 := by
  obtain ⟨h, rfl⟩ := hd
  have hh : 0 < h := by omega
  exact reflected_vanishing hq hh (primitive_sum_square hq) (normalized_vanish hq hh)

end SunQ

end

section

theorem OMA.solution : type_of% @OeisA179524.conjecture4 := by
  exact SunQ.from_period_vanishing SunQ.primitive_block

end
