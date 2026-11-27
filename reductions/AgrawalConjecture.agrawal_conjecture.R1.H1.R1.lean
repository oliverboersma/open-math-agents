import OMAReductions.R_AgrawalConjecture_agrawal_conjecture_R1
import Mathlib

/-! # Least-prime-factor bounds for the prime-modulus step of Agrawal's conjecture

Let q be the least prime factor of n and F = (X-1)^n - (X^n-1). Over ZMod n, F is
nonzero for composite n and has degree at most n-q. Since its derivative vanishes,
every monic separable factor occurs with multiplicity at least q. The integers
from one through q-1 are units, so differentiating and cancelling raises its
multiplicity one level at a time.

This bounds (p+1)q by n. For odd n the additional coprime factor X also occurs
with multiplicity at least q, giving (p+2)q ≤ n. Both remaining steps ask for a
local obstruction to the simple polynomial congruence in these smaller ranges.
-/

open Polynomial Finset

namespace OMA.R_AgrawalConjecture_agrawal_conjecture_R1_H1_R1

lemma intermediate_coeff (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (((X - 1 : (ZMod n)[X]) ^ n - (X ^ n - 1)).coeff k) =
      (-1 : ZMod n) ^ (n-k) * (n.choose k : ZMod n) := by
  rw [show (X - 1 : (ZMod n)[X]) = X + C (-1) by simp [sub_eq_add_neg]]
  rw [coeff_sub, coeff_X_add_C_pow]
  simp [coeff_X_pow, coeff_one, Nat.ne_of_lt hkn, Nat.ne_of_gt hk]

/-- An identically vanishing difference would force n to divide every intermediate binomial coefficient. -/
lemma difference_ne_zero {n : ℕ} (hn : 1 < n) (hc : ¬n.Prime) :
    (X - 1 : (ZMod n)[X]) ^ n - (X ^ n - 1) ≠ 0 := by
  intro hz
  have hd : n ∣ (Icc 1 (n-1)).gcd n.choose := by
    apply dvd_gcd_iff.mpr
    intro k hk
    obtain ⟨hk,hk'⟩ := mem_Icc.mp hk
    have h := congrArg (fun f : (ZMod n)[X] => f.coeff k) hz
    change ((X - 1 : (ZMod n)[X]) ^ n - (X ^ n - 1)).coeff k = 0 at h
    rw [intermediate_coeff n k (by omega) (by omega)] at h
    have hu : IsUnit ((-1 : ZMod n) ^ (n-k)) := (isUnit_one.neg).pow _
    exact (ZMod.natCast_eq_zero_iff _ _).mp (hu.mul_right_eq_zero.mp h)
  by_cases h : IsPrimePow n
  · rw [Choose.gcd_choose_eq_minFac_of_isPrimePow h] at hd
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have he := le_antisymm (Nat.le_of_dvd hp.pos hd) (Nat.minFac_le (by omega))
    exact hc (he ▸ hp)
  · rw [Choose.gcd_choose_eq_one_of_not_isPrimePow hn h, Nat.dvd_one] at hd
    omega

/-- Indices smaller than the least prime factor are units modulo n. -/
lemma choose_dvd {n j : ℕ} (hn : 0 < n) (hj : 0 < j) (hsmall : j < n.minFac) :
    n ∣ n.choose j := by
  have e := Nat.add_one_mul_choose_eq (n-1) (j-1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hj] at e
  exact (Nat.coprime_of_lt_minFac hj.ne' hsmall).dvd_of_dvd_mul_right
    ⟨_,e.symm⟩

lemma degree_bound {n : ℕ} (hn : 1 < n) :
    ((X - 1 : (ZMod n)[X]) ^ n - (X ^ n - 1)).natDegree ≤ n - n.minFac := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hk0 : 0 < k := by omega
  by_cases hkn : k < n
  · rw [intermediate_coeff n k hk0 hkn]
    have hbin := choose_dvd (n := n) (j := n-k) (by omega) (by omega) (by omega)
    rw [Nat.choose_symm (by omega : k ≤ n)] at hbin
    simp [(ZMod.natCast_eq_zero_iff _ _).mpr hbin]
  · rw [show (X - 1 : (ZMod n)[X]) = X + C (-1) by simp [sub_eq_add_neg]]
    rw [coeff_sub, coeff_X_add_C_pow]
    rcases eq_or_lt_of_le (Nat.le_of_not_gt hkn) with rfl | lt
    · simp [coeff_X_pow, coeff_one, hk0.ne']
    · simp [coeff_X_pow, coeff_one, lt.ne', hk0.ne', Nat.choose_eq_zero_of_lt lt]

/-- Cancel the differentiated factor one power at a time while the multiplicity is a unit. -/
lemma raise_multiplicity {R : Type*} [CommRing R] {g f : R[X]}
    (mon : g.Monic) (sep : g.Separable) (stationary : derivative f = 0)
    {q : ℕ} (units : ∀ k : ℕ, 0 < k → k < q → IsUnit (k : R))
    (one : g ∣ f) : g ^ q ∣ f := by
  suffices all : ∀ j : ℕ, j ≤ q → g ^ j ∣ f from all q le_rfl
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
    intro h
    cases k with
    | zero => simpa using one
    | succ m =>
      obtain ⟨u,eq⟩ := ih (by omega)
      have hu := (units (m+1) (by omega) (by omega)).map (C : R →+* R[X])
      have d := stationary
      rw [eq, derivative_mul, derivative_pow, Nat.add_sub_cancel] at d
      have cancel : C ((m+1 : ℕ) : R) * derivative g * u + g * derivative u = 0 := by
        apply (mon.pow m).mul_right_eq_zero_iff.mp
        linear_combination (norm := ring_nf) d
      have dvd' : g ∣ C ((m+1 : ℕ) : R) * (derivative g * u) := by
        refine ⟨-derivative u, ?_⟩
        linear_combination cancel
      obtain ⟨v,hv⟩ := sep.dvd_of_dvd_mul_left (hu.dvd_mul_left.mp dvd')
      exact ⟨v, by rw [eq,hv,pow_succ g (m+1),mul_assoc]⟩

lemma necessary_range {n p : ℕ} (hn : 1 < n) (hc : ¬n.Prime) (hp : p.Prime) (cop : n.Coprime p)
    (h : (X ^ p - 1 : (ZMod n)[X]) ^ 2 ∣ (X - 1)^n - (X^n - 1)) :
    p * n.minFac + n.minFac ≤ n := by
  let _ : Fact (1 < n) := ⟨hn⟩
  have mon : (X ^ p - 1 : (ZMod n)[X]).Monic := by simpa using monic_X_pow_sub_C (1 : ZMod n) hp.ne_zero
  have sep : (X ^ p - 1 : (ZMod n)[X]).Separable := by
    simpa using separable_X_pow_sub_C_unit (n := p) (1 : (ZMod n)ˣ) ((ZMod.isUnit_iff_coprime p n).2 cop.symm)
  have d : derivative ((X - 1 : (ZMod n)[X])^n - (X^n - 1)) = 0 := by simp [derivative_pow]
  have dvd := raise_multiplicity mon sep d (q := n.minFac)
    (fun k hk hkn => (ZMod.isUnit_iff_coprime k n).2 (Nat.coprime_of_lt_minFac hk.ne' hkn).symm)
    ((dvd_pow_self _ (by decide : 2 ≠ 0)).trans h)
  obtain ⟨u,e⟩ := dvd
  have nonz := difference_ne_zero hn hc
  have hune : u ≠ 0 := fun h0 => nonz (by simpa [h0] using e)
  have b := degree_bound hn
  rw [e, (mon.pow _).natDegree_mul' hune, mon.natDegree_pow,
    show (X ^ p - 1 : (ZMod n)[X]).natDegree = p by
      simpa using (natDegree_X_pow_sub_C (n := p) (r := (1 : ZMod n)))] at b
  rw [Nat.mul_comm n.minFac p] at b
  have := Nat.minFac_le (by omega : 0 < n)
  omega

lemma necessary_range_odd {n p : ℕ} (hn : 1 < n) (hc : ¬n.Prime) (hp : p.Prime)
    (cop : n.Coprime p) (odd : Odd n)
    (h : (X ^ p - 1 : (ZMod n)[X]) ^ 2 ∣ (X - 1)^n - (X^n - 1)) :
    (p + 2) * n.minFac ≤ n := by
  let _ : Fact (1 < n) := ⟨hn⟩
  let f : (ZMod n)[X] := (X - 1)^n - (X^n - 1)
  let g : (ZMod n)[X] := X ^ p - 1
  have mon : g.Monic := by simpa [g] using monic_X_pow_sub_C (1 : ZMod n) hp.ne_zero
  have sep : g.Separable := by
    simpa [g] using separable_X_pow_sub_C_unit (n := p) (1 : (ZMod n)ˣ)
      ((ZMod.isUnit_iff_coprime p n).2 cop.symm)
  have sd : derivative f = 0 := by simp [f,derivative_pow]
  have units (k : ℕ) (hk : 0 < k) (hkn : k < n.minFac) : IsUnit (k : ZMod n) :=
    (ZMod.isUnit_iff_coprime k n).2 (Nat.coprime_of_lt_minFac hk.ne' hkn).symm
  have hx : X ∣ f := by
    apply X_dvd_iff.mpr
    rw [coeff_zero_eq_eval_zero]
    simp [f, show n ≠ 0 by omega, odd.neg_one_pow]
  have hg : g ∣ f := (dvd_pow_self _ (by decide : 2 ≠ 0)).trans h
  have cp : IsCoprime (X : (ZMod n)[X]) g := by
    refine ⟨X ^ (p-1), -1, ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel hp.pos]
    simp [g]
  have both := (cp.pow).mul_dvd (raise_multiplicity monic_X separable_X sd units hx)
    (raise_multiplicity mon sep sd units hg)
  obtain ⟨u,e⟩ := both
  have ne : f ≠ 0 := difference_ne_zero hn hc
  have un : u ≠ 0 := fun hz => ne (by simpa [hz] using e)
  have b : f.natDegree ≤ n - n.minFac := degree_bound hn
  have gd : g.natDegree = p := by simpa [g] using (natDegree_X_pow_sub_C (n := p) (r := (1 : ZMod n)))
  rw [e, ((monic_X.pow _).mul (mon.pow _)).natDegree_mul' un,
    (monic_X.pow _).natDegree_mul (mon.pow _), mon.natDegree_pow, gd, natDegree_X_pow] at b
  have := Nat.minFac_le (by omega : 0 < n)
  rw [Nat.add_mul, Nat.mul_comm p]
  omega


/-- For even n in the remaining range, find a prime-power factor of n on
which the univariate congruence already fails. -/
def H1 : Prop :=
  ∀ n p : ℕ, 1 < n → ¬ n.Prime → Even n → p.Prime → 5 ≤ p → n.Coprime p →
    (p + 1) * n.minFac ≤ n → ¬ p ∣ n ^ 2 - 1 →
    ∃ m : ℕ, IsPrimePow m ∧ m ∣ n ∧
      ¬ (X ^ p - 1 : (ZMod m)[X]) ∣ (X - 1) ^ n - (X ^ n - 1)

/-- For odd n the root at zero removes a further minFac(n) degrees. -/
def H2 : Prop :=
  ∀ n p : ℕ, 1 < n → ¬ n.Prime → Odd n → p.Prime → 5 ≤ p → n.Coprime p →
    (p + 2) * n.minFac ≤ n → ¬ p ∣ n ^ 2 - 1 →
    ∃ m : ℕ, IsPrimePow m ∧ m ∣ n ∧
      ¬ (X ^ p - 1 : (ZMod m)[X]) ∣ (X - 1) ^ n - (X ^ n - 1)

lemma small_primes {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (hcop : n.Coprime p)
    (hsmall : p < 5) : p ∣ n ^ 2 - 1 := by
  have non : n % p ≠ 0 := fun h => hp.coprime_iff_not_dvd.mp hcop.symm (Nat.dvd_of_mod_eq_zero h)
  have lt := Nat.mod_lt n hp.pos
  apply (Nat.modEq_iff_dvd' (show 1 ≤ n ^ 2 by nlinarith)).mp
  change 1 % p = n ^ 2 % p
  rw [Nat.pow_mod]
  have h2 := hp.two_le
  have ne4 : p ≠ 4 := by rintro rfl; exact (by decide : ¬Nat.Prime 4) hp
  rcases (show p = 2 ∨ p = 3 by omega) with rfl | rfl
  · have e : n % 2 = 1 := by omega
    norm_num [e]
  · rcases (show n % 3 = 1 ∨ n % 3 = 2 by omega) with e | e <;> norm_num [e]

theorem main : H1 → H2 → OMA.R_AgrawalConjecture_agrawal_conjecture_R1.H1 := by
  intro evenCase oddCase n p hn hc hp hcop
  dsimp only
  intro hpoly
  by_contra bad
  have large : 5 ≤ p := by
    by_contra! small
    exact bad (small_primes hn hp hcop small)
  have test : ∃ m : ℕ, IsPrimePow m ∧ m ∣ n ∧
      ¬ (X ^ p - 1 : (ZMod m)[X]) ∣ (X - 1) ^ n - (X ^ n - 1) := by
    rcases Nat.even_or_odd n with he | ho
    · apply evenCase n p hn hc he hp large hcop _ bad
      simpa [Nat.add_mul] using necessary_range hn hc hp hcop hpoly
    · exact oddCase n p hn hc ho hp large hcop (necessary_range_odd hn hc hp hcop ho hpoly) bad
  obtain ⟨m, _, hmn, fail⟩ := test
  apply fail
  have div : (X ^ p - 1 : (ZMod n)[X]) ∣ (X - 1) ^ n - (X ^ n - 1) :=
    (dvd_pow_self _ (by decide : 2 ≠ 0)).trans hpoly
  simpa using Polynomial.map_dvd (ZMod.castHom hmn (ZMod m)) div

end OMA.R_AgrawalConjecture_agrawal_conjecture_R1_H1_R1
