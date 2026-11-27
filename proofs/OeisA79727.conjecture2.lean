import FormalConjectures.OEIS.«79727»

/-!
# Proof of OeisA79727.conjecture2

Proves Peter Bala's 2024 conjecture that for every prime `p` in OEIS A003625
(`p % 7 ∈ {3, 5, 6}`), `a(p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3]`, where
`a(n) = ∑ k ∈ range (n + 1), (Nat.choose (2 * k) k) ^ 3`.

Method:
1. Block expansion of `a(p * (p - 1))` modulo `p ^ 3` into `A_0^2 + 6*p*S_1*A_1 + p^2*S_2*B_2`.
2. Explicit degree-2 CM endomorphism in `PowerSeries (Quad7 (ZMod p))` showing the Hasse
   invariant of the supersingular elliptic curve `y^2 = (x + 21) * (x^2 + 7)` vanishes.
3. Exact 2-isogeny and pure integer 3rd-order ODE for `P_m(1 + 2t)^2` lifting `A_0 ≡ 0 (mod p)`
   to `A_0 ≡ 0 (mod p ^ 2)`.
4. Symmetric square Picard-Fuchs ODE and Wronskian evaluation at `z = 64` establishing
   `S_1 ≡ 0`, `A_1 ≡ 0`, and `S_2 * B_2 ≡ 1 (mod p)`.

Credit: Daniel Whorlow (@draonbioetl)
-/

open scoped BigOperators
open Finset Polynomial


-- Credit: Daniel Whorlow (@draonbioetl)


namespace OMA_A79727

private lemma prod_Icc_eq_factorial (n : ℕ) :
    ∏ j ∈ Finset.Icc 1 n, j = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
          ext x; simp [Finset.mem_Icc]; omega,
        Finset.prod_insert (by simp), ih, Nat.factorial_succ]

private lemma a3625_props {p : ℕ} (hp : OeisA3625.A p) (h3 : p ≠ 3) :
    p.Prime ∧ 5 ≤ p ∧ p ≠ 7 ∧ Odd p ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) := by
  rcases hp with ⟨hpr, hmod⟩
  have h2 : p ≠ 2 := by intro h; subst h; omega
  have h5 : 5 ≤ p := by
    have := hpr.two_le
    by_contra hlt
    interval_cases p <;> simp_all [Nat.Prime]
  have h7 : p ≠ 7 := by intro h; subst h; omega
  exact ⟨hpr, h5, h7, hpr.odd_of_ne_two h2, hmod⟩

private lemma leg7_356 :
    @legendreSym 7 ⟨by decide⟩ 3 = -1 ∧
    @legendreSym 7 ⟨by decide⟩ 5 = -1 ∧
    @legendreSym 7 ⟨by decide⟩ 6 = -1 := by
  decide

private lemma neg_seven_pow_half_eq_neg_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hmod : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) :
    ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp7 : p ≠ 7 := by intro h; subst h; omega
  have hhalf : (p - 1) / 2 = p / 2 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2); omega
  rw [hhalf]
  have hleg := legendreSym.eq_pow p (-7 : ℤ)
  have hcast : ((-7 : ℤ) : ZMod p) = (-7 : ZMod p) := by norm_num
  rw [hcast] at hleg
  rw [← hleg]
  have hmul : legendreSym p (-7 : ℤ) = legendreSym p (-1 : ℤ) * legendreSym p (7 : ℤ) := by
    rw [show (-7 : ℤ) = (-1) * 7 by norm_num, legendreSym.mul]
  rw [hmul]
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hqr := legendreSym.quadratic_reciprocity hp2 (by decide : 7 ≠ 2) hp7
  have hneg1 : legendreSym p (-1 : ℤ) = (-1 : ℤ) ^ (p / 2) := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_mod_four]
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h4 with h | h
    · have hev : Even (p / 2) := ⟨p / 4, by omega⟩
      simp [h, hev.neg_one_pow]
    · have hodd2 : Odd (p / 2) := ⟨p / 4, by omega⟩
      simp [h, hodd2.neg_one_pow]
  have h7p : legendreSym 7 (p : ℤ) = -1 := by
    have hmod_eq : (p : ℤ) % 7 = ((p % 7 : ℕ) : ℤ) := by omega
    rw [legendreSym.mod, Nat.cast_ofNat, hmod_eq]
    rcases hmod with h | h | h
    · rw [h, Nat.cast_ofNat]; exact leg7_356.1
    · rw [h, Nat.cast_ofNat]; exact leg7_356.2.1
    · rw [h, Nat.cast_ofNat]; exact leg7_356.2.2
  have hpow : (-1 : ℤ) ^ (p / 2 * (7 / 2)) = (-1 : ℤ) ^ (p / 2) := by
    have : 7 / 2 = 3 := rfl
    rw [this, mul_comm, pow_mul]
    norm_num
  rw [hpow, h7p, Nat.cast_ofNat] at hqr
  have hval : legendreSym p (-1 : ℤ) * legendreSym p (7 : ℤ) = -1 := by
    rw [hneg1]
    have hsq : ((-1 : ℤ) ^ (p / 2)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hqr3 : legendreSym p 7 = -((-1 : ℤ) ^ (p / 2)) := by linarith
    rw [hqr3]
    calc (-1 : ℤ) ^ (p / 2) * -((-1 : ℤ) ^ (p / 2)) = -(((-1 : ℤ) ^ (p / 2)) ^ 2) := by ring
      _ = -1 := by rw [hsq]
  rw [hval]
  norm_num

private lemma sum_inv_sq_zmod_p {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod p)⁻¹) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hfull : ∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod p)⁻¹) ^ 2 =
      ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
    simp only [inv_zero, zero_pow two_ne_zero, add_zero]
    refine Finset.sum_bij (fun j _ => (j : ZMod p)) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h0
      have hdvd : p ∣ j := (ZMod.natCast_eq_zero_iff j p).mp h0
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · intro a ha b hb hab
      rw [Finset.mem_Icc] at ha hb
      have h1 : a % p = b % p := by
        simpa [ZMod.val_natCast] using congrArg ZMod.val hab
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
      exact h1
    · intro x hx
      rw [Finset.mem_erase] at hx
      refine ⟨x.val, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ZMod.natCast_zmod_val x⟩
      · have : x.val ≠ 0 := fun h => hx.1 (by rw [← ZMod.natCast_zmod_val x, h]; simp)
        omega
      · have := x.val_lt; omega
    · intro _ _; rfl
  rw [hfull]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd
    omega
  have hbij : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, ((2 * x)⁻¹) ^ 2 :=
    (Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2ne) (fun y : ZMod p => (y⁻¹) ^ 2)).symm
  have hscale : ∑ x : ZMod p, ((2 * x)⁻¹) ^ 2 = ((2 : ZMod p)⁻¹) ^ 2 * ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_inv, mul_pow]
  have heq : (1 - ((2 : ZMod p)⁻¹) ^ 2) * ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    have := hbij.trans hscale
    linear_combination this
  have h1ne : (1 - ((2 : ZMod p)⁻¹) ^ 2 : ZMod p) ≠ 0 := by
    intro h
    have h4 : (4 : ZMod p) = 1 := by
      have hinv : ((2 : ZMod p)⁻¹) ^ 2 = 1 := (sub_eq_zero.mp h).symm
      calc (4 : ZMod p) = (2 : ZMod p) ^ 2 * 1 := by ring
        _ = (2 : ZMod p) ^ 2 * ((2 : ZMod p)⁻¹) ^ 2 := by rw [hinv]
        _ = ((2 : ZMod p) * (2 : ZMod p)⁻¹) ^ 2 := by rw [← mul_pow]
        _ = 1 := by rw [mul_inv_cancel₀ h2ne, one_pow]
    have h3 : (3 : ZMod p) = 0 := by linear_combination h4
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h3)
    have := Nat.le_of_dvd (by decide) hdvd
    omega
  exact (mul_eq_zero.mp heq).resolve_left h1ne

private lemma isUnit_natCast_zmod_pow {p k j : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) (hjp : j < p) :
    IsUnit (j : ZMod (p ^ k)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hcop : Nat.Coprime j p := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjp)).symm
  exact hcop.pow_right k

private lemma natCast_mul_inv_eq_one {p k j : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) (hjp : j < p) :
    (j : ZMod (p ^ k)) * (j : ZMod (p ^ k))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_natCast_zmod_pow hp hj1 hjp)

private lemma two_mul_inv_eq_one {p k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 : ZMod (p ^ k)) * (2 : ZMod (p ^ k))⁻¹ = 1 := by
  simpa using natCast_mul_inv_eq_one (p := p) (k := k) (j := 2) hp (by decide) (by omega)

private lemma sum_inv_zmod_p_sq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ j ∈ Finset.Icc 1 (p - 1), (j : ZMod (p ^ 2))⁻¹ = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  set H : ZMod (p ^ 2) := ∑ j ∈ Finset.Icc 1 (p - 1), (j : ZMod (p ^ 2))⁻¹
  have hrev : H = ∑ j ∈ Finset.Icc 1 (p - 1), ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ := by
    refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; rw [Finset.mem_Icc] at hj ⊢; omega
    · intro a ha b hb hab; rw [Finset.mem_Icc] at ha hb; omega
    · intro j hj; rw [Finset.mem_Icc] at hj
      exact ⟨p - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro a ha; rw [Finset.mem_Icc] at ha; congr 2; omega
  have h2H : 2 * H = -(p : ZMod (p ^ 2)) * ∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod (p ^ 2))⁻¹) ^ 2 := by
    have hadd : 2 * H = ∑ j ∈ Finset.Icc 1 (p - 1),
        ((j : ZMod (p ^ 2))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) := by
      rw [two_mul, Finset.sum_add_distrib]
      conv_lhs => rhs; rw [hrev]
    rw [hadd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hju := natCast_mul_inv_eq_one (k := 2) hp hj.1 (by omega)
    have hpu := natCast_mul_inv_eq_one (k := 2) hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
    have hsum_jp : (j : ZMod (p ^ 2)) + ((p - j : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
    have hp2_zero : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
      rw [← Nat.cast_mul, ← sq]; exact ZMod.natCast_self (p ^ 2)
    have hpair : (j : ZMod (p ^ 2))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ =
        (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹ * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ := by
      have h1 : (j : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2)) *
          ((j : ZMod (p ^ 2))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) = (p : ZMod (p ^ 2)) := by
        calc (j : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2)) *
              ((j : ZMod (p ^ 2))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 2))⁻¹)
            = ((j : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹) * ((p - j : ℕ) : ZMod (p ^ 2)) +
              (j : ZMod (p ^ 2)) * (((p - j : ℕ) : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) := by ring
          _ = ((p - j : ℕ) : ZMod (p ^ 2)) + (j : ZMod (p ^ 2)) := by rw [hju, hpu]; ring
          _ = (p : ZMod (p ^ 2)) := by rw [add_comm, hsum_jp]
      calc (j : ZMod (p ^ 2))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 2))⁻¹
          = ((j : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹) *
            (((p - j : ℕ) : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) *
            ((j : ZMod (p ^ 2))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) := by rw [hju, hpu]; ring
        _ = (j : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2)) *
            ((j : ZMod (p ^ 2))⁻¹ + ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) *
            (j : ZMod (p ^ 2))⁻¹ * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ := by ring
        _ = (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹ * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ := by rw [h1]
    have hp_neg : (p : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ =
        -(p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹ := by
      have hmul : (p : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2)) =
          -(p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)) := by
        have : ((p - j : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - (j : ZMod (p ^ 2)) := by
          linear_combination hsum_jp
        rw [this, mul_sub, hp2_zero]; ring
      have hmul2 : (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)) =
          -(p : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2)) := by linear_combination hmul
      calc (p : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹
          = (p : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ *
            ((j : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹) := by rw [hju, mul_one]
        _ = ((p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))) *
            ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ * (j : ZMod (p ^ 2))⁻¹ := by ring
        _ = (-(p : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))) *
            ((p - j : ℕ) : ZMod (p ^ 2))⁻¹ * (j : ZMod (p ^ 2))⁻¹ := by rw [hmul2]
        _ = -(p : ZMod (p ^ 2)) * (((p - j : ℕ) : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) *
            (j : ZMod (p ^ 2))⁻¹ := by ring
        _ = -(p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹ := by rw [hpu, mul_one]
    rw [hpair]
    calc (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹ * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹
        = ((p : ZMod (p ^ 2)) * ((p - j : ℕ) : ZMod (p ^ 2))⁻¹) * (j : ZMod (p ^ 2))⁻¹ := by ring
      _ = (-(p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹) * (j : ZMod (p ^ 2))⁻¹ := by rw [hp_neg]
      _ = -(p : ZMod (p ^ 2)) * ((j : ZMod (p ^ 2))⁻¹) ^ 2 := by ring
  set S2 : ZMod (p ^ 2) := ∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod (p ^ 2))⁻¹) ^ 2
  have hcast_S2 : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) S2 = 0 := by
    simp only [S2, map_sum, map_pow]
    have hterm : ∀ j ∈ Finset.Icc 1 (p - 1),
        ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) ((j : ZMod (p ^ 2))⁻¹) = (j : ZMod p)⁻¹ := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have : Fact p.Prime := ⟨hp⟩
      have hju := natCast_mul_inv_eq_one (k := 2) hp hj.1 (by omega)
      have h1 := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) hju
      simp only [map_mul, map_natCast, map_one] at h1
      have hjne : (j : ZMod p) ≠ 0 := by
        intro h0
        have hdvd := (ZMod.natCast_eq_zero_iff j p).mp h0
        have := Nat.le_of_dvd (by omega) hdvd; omega
      exact mul_left_cancel₀ hjne (by rw [h1, mul_inv_cancel₀ hjne])
    rw [Finset.sum_congr rfl fun j hj => by rw [hterm j hj]]
    exact sum_inv_sq_zmod_p hp h5
  have hpS2 : (p : ZMod (p ^ 2)) * S2 = 0 := by
    have hdvd : p ∣ S2.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      rw [← ZMod.natCast_zmod_val S2] at hcast_S2
      simpa using hcast_S2
    rcases hdvd with ⟨t, ht⟩
    have hS2eq : S2 = (p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2)) := by
      rw [← ZMod.natCast_zmod_val S2, ht, Nat.cast_mul]
    rw [hS2eq, ← mul_assoc, ← Nat.cast_mul, ← sq, ZMod.natCast_self, zero_mul]
  have h2H0 : (2 : ZMod (p ^ 2)) * H = 0 := by
    rw [h2H, neg_mul, hpS2, neg_zero]
  have h2u := two_mul_inv_eq_one (p := p) (k := 2) hp h5
  calc H = ((2 : ZMod (p ^ 2)) * (2 : ZMod (p ^ 2))⁻¹) * H := by rw [h2u, one_mul]
    _ = (2 : ZMod (p ^ 2))⁻¹ * ((2 : ZMod (p ^ 2)) * H) := by ring
    _ = 0 := by rw [h2H0, mul_zero]

private lemma prod_one_add_cubed_zero {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (x twoInv : R) (hx3 : x ^ 3 = 0) (h2 : 2 * twoInv = 1) (c : ι → R) :
    ∏ j ∈ s, (1 + x * c j) =
      1 + x * (∑ j ∈ s, c j) + x ^ 2 * twoInv * ((∑ j ∈ s, c j) ^ 2 - ∑ j ∈ s, (c j) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    set S1 := ∑ j ∈ s, c j
    set S2 := ∑ j ∈ s, (c j) ^ 2
    linear_combination
      (twoInv * c a * (S1 ^ 2 - S2)) * hx3 - (x ^ 2 * c a * S1) * h2

private lemma prod_block_eq_factorial {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (u : ℕ) :
    ∏ j ∈ Finset.Icc 1 (p - 1), ((u * p + j : ℕ) : ZMod (p ^ 3)) =
      ((p - 1).factorial : ZMod (p ^ 3)) := by
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hp3_zero : ((u * p : ℕ) : ZMod (p ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow, mul_pow, mul_comm (u ^ 3), Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have h2u := two_mul_inv_eq_one (p := p) (k := 3) hp h5
  have hfac : ∏ j ∈ Finset.Icc 1 (p - 1), (j : ZMod (p ^ 3)) = ((p - 1).factorial : ZMod (p ^ 3)) := by
    rw [← Nat.cast_prod, prod_Icc_eq_factorial]
  have hsplit : ∏ j ∈ Finset.Icc 1 (p - 1), ((u * p + j : ℕ) : ZMod (p ^ 3)) =
      (∏ j ∈ Finset.Icc 1 (p - 1), (j : ZMod (p ^ 3))) *
      (∏ j ∈ Finset.Icc 1 (p - 1), (1 + ((u * p : ℕ) : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hju := natCast_mul_inv_eq_one (k := 3) hp hj.1 (by omega)
    push_cast
    calc (u : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) + (j : ZMod (p ^ 3))
        = (j : ZMod (p ^ 3)) + (u : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) *
            ((j : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹) := by rw [hju, mul_one]; ring
      _ = (j : ZMod (p ^ 3)) * (1 + (u : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹) := by ring
  rw [hsplit, hfac, prod_one_add_cubed_zero _ _ _ hp3_zero h2u]
  set H1 : ZMod (p ^ 3) := ∑ j ∈ Finset.Icc 1 (p - 1), (j : ZMod (p ^ 3))⁻¹
  set H2 : ZMod (p ^ 3) := ∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod (p ^ 3))⁻¹) ^ 2
  have hpH1 : (p : ZMod (p ^ 3)) * H1 = 0 := by
    have hdvd2 : p ^ 2 ∣ p ^ 3 := ⟨p, by ring⟩
    have hcast : ZMod.castHom hdvd2 (ZMod (p ^ 2)) H1 = 0 := by
      simp only [H1, map_sum]
      have hterm : ∀ j ∈ Finset.Icc 1 (p - 1),
          ZMod.castHom hdvd2 (ZMod (p ^ 2)) ((j : ZMod (p ^ 3))⁻¹) = (j : ZMod (p ^ 2))⁻¹ := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        have hju3 := natCast_mul_inv_eq_one (k := 3) hp hj.1 (by omega)
        have hju2 := natCast_mul_inv_eq_one (k := 2) hp hj.1 (by omega)
        have h1 := congrArg (ZMod.castHom hdvd2 (ZMod (p ^ 2))) hju3
        simp only [map_mul, map_natCast, map_one] at h1
        calc ZMod.castHom hdvd2 (ZMod (p ^ 2)) ((j : ZMod (p ^ 3))⁻¹)
            = ((j : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹) *
              ZMod.castHom hdvd2 (ZMod (p ^ 2)) ((j : ZMod (p ^ 3))⁻¹) := by rw [hju2, one_mul]
          _ = (j : ZMod (p ^ 2))⁻¹ * ((j : ZMod (p ^ 2)) *
              ZMod.castHom hdvd2 (ZMod (p ^ 2)) ((j : ZMod (p ^ 3))⁻¹)) := by ring
          _ = (j : ZMod (p ^ 2))⁻¹ := by rw [h1, mul_one]
      rw [Finset.sum_congr rfl hterm]
      exact sum_inv_zmod_p_sq hp h5
    have hdvd : p ^ 2 ∣ H1.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      rw [← ZMod.natCast_zmod_val H1] at hcast
      simpa using hcast
    rcases hdvd with ⟨t, ht⟩
    have hH1eq : H1 = ((p ^ 2 : ℕ) : ZMod (p ^ 3)) * (t : ZMod (p ^ 3)) := by
      rw [← ZMod.natCast_zmod_val H1, ht, Nat.cast_mul]
    rw [hH1eq, ← mul_assoc, ← Nat.cast_mul, show p * p ^ 2 = p ^ 3 by ring, ZMod.natCast_self, zero_mul]
  have hp2H2 : (p : ZMod (p ^ 3)) ^ 2 * H2 = 0 := by
    have hdvd1 : p ∣ p ^ 3 := dvd_pow_self p (by decide)
    have hcast : ZMod.castHom hdvd1 (ZMod p) H2 = 0 := by
      simp only [H2, map_sum, map_pow]
      have hterm : ∀ j ∈ Finset.Icc 1 (p - 1),
          ZMod.castHom hdvd1 (ZMod p) ((j : ZMod (p ^ 3))⁻¹) = (j : ZMod p)⁻¹ := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        have : Fact p.Prime := ⟨hp⟩
        have hju3 := natCast_mul_inv_eq_one (k := 3) hp hj.1 (by omega)
        have h1 := congrArg (ZMod.castHom hdvd1 (ZMod p)) hju3
        simp only [map_mul, map_natCast, map_one] at h1
        have hjne : (j : ZMod p) ≠ 0 := by
          intro h0
          have hdvd := (ZMod.natCast_eq_zero_iff j p).mp h0
          have := Nat.le_of_dvd (by omega) hdvd; omega
        exact mul_left_cancel₀ hjne (by rw [h1, mul_inv_cancel₀ hjne])
      rw [Finset.sum_congr rfl fun j hj => by rw [hterm j hj]]
      exact sum_inv_sq_zmod_p hp h5
    have hdvd : p ∣ H2.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      rw [← ZMod.natCast_zmod_val H2] at hcast
      simpa using hcast
    rcases hdvd with ⟨t, ht⟩
    have hH2eq : H2 = (p : ZMod (p ^ 3)) * (t : ZMod (p ^ 3)) := by
      rw [← ZMod.natCast_zmod_val H2, ht, Nat.cast_mul]
    rw [hH2eq, ← mul_assoc, ← pow_succ, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have hx1 : ((u * p : ℕ) : ZMod (p ^ 3)) * H1 = 0 := by
    rw [Nat.cast_mul, mul_assoc, hpH1, mul_zero]
  have hx2 : ((u * p : ℕ) : ZMod (p ^ 3)) ^ 2 * (H1 ^ 2 - H2) = 0 := by
    have h1 : ((u * p : ℕ) : ZMod (p ^ 3)) ^ 2 * H1 ^ 2 = 0 := by
      rw [← mul_pow, hx1, zero_pow two_ne_zero]
    have h2 : ((u * p : ℕ) : ZMod (p ^ 3)) ^ 2 * H2 = 0 := by
      rw [Nat.cast_mul, mul_pow, mul_assoc, hp2H2, mul_zero]
    rw [mul_sub, h1, h2, sub_zero]
  have hRHS : (1 : ZMod (p ^ 3)) + ((u * p : ℕ) : ZMod (p ^ 3)) * H1 +
      ((u * p : ℕ) : ZMod (p ^ 3)) ^ 2 * (2 : ZMod (p ^ 3))⁻¹ * (H1 ^ 2 - H2) = 1 := by
    calc (1 : ZMod (p ^ 3)) + ((u * p : ℕ) : ZMod (p ^ 3)) * H1 +
          ((u * p : ℕ) : ZMod (p ^ 3)) ^ 2 * (2 : ZMod (p ^ 3))⁻¹ * (H1 ^ 2 - H2)
        = 1 + ((u * p : ℕ) : ZMod (p ^ 3)) * H1 +
          (2 : ZMod (p ^ 3))⁻¹ * (((u * p : ℕ) : ZMod (p ^ 3)) ^ 2 * (H1 ^ 2 - H2)) := by ring
      _ = 1 := by rw [hx1, hx2]; ring
  rw [hRHS, mul_one]

private lemma factorial_split_nat (p : ℕ) (hp : 1 ≤ p) :
    ∀ n s : ℕ, (n * p + s).factorial =
      p ^ n * n.factorial *
        (∏ u ∈ Finset.range n, ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) *
        (∏ j ∈ Finset.Icc 1 s, (n * p + j)) := by
  intro n s
  induction s with
  | zero =>
    simp only [add_zero, Finset.Icc_eq_empty (by decide : ¬ 1 ≤ 0), Finset.prod_empty, mul_one]
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : ((n + 1) * p).factorial =
          (n * p).factorial * (∏ j ∈ Finset.Icc 1 (p - 1), (n * p + j)) * ((n + 1) * p) := by
        have hprod : ∀ t : ℕ, (n * p + t).factorial =
            (n * p).factorial * ∏ j ∈ Finset.Icc 1 t, (n * p + j) := by
          intro t
          induction t with
          | zero => simp
          | succ t iht =>
            rw [Nat.add_succ, Nat.factorial_succ, iht,
              show Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) by
                ext x; simp [Finset.mem_Icc]; omega,
              Finset.prod_insert (by simp)]
            ring
        have h1 := hprod (p - 1)
        have h2 : (n + 1) * p = (n * p + (p - 1)) + 1 := by
          have : p = (p - 1) + 1 := by omega
          calc (n + 1) * p = n * p + p := by ring
            _ = n * p + ((p - 1) + 1) := by rw [← this]
            _ = n * p + (p - 1) + 1 := by ring
        rw [h2, Nat.factorial_succ, h1]
        ring
      rw [hstep, ih, Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
      ring
  | succ s ih =>
    rw [Nat.add_succ, Nat.factorial_succ, ih,
      show Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) by
        ext x; simp [Finset.mem_Icc]; omega,
      Finset.prod_insert (by simp)]
    ring

private lemma choose_dvd_of_mod_gt_half {p k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hgt : (p - 1) / 2 < k % p) :
    p ∣ Nat.choose (2 * k) k := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hrlt : k % p < p := Nat.mod_lt k hp.pos
  have h2r : (2 * k) % p = 2 * (k % p) - p := by
    have h1 : (2 * k) % p = (2 * (k % p)) % p := by
      rw [Nat.mul_mod, show 2 % p = 2 from Nat.mod_eq_of_lt (by omega)]
    rw [h1, Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * k) (k := k) (p := p)
  rw [h2r, Nat.choose_eq_zero_of_lt (by omega : 2 * (k % p) - p < k % p), zero_mul] at hluc
  exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hluc)

private lemma choose_dvd_of_div_gt_half {p k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hgt : (p - 1) / 2 < k / p) (hlt : k / p < p) :
    p ∣ Nat.choose (2 * k) k := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hrm : (p - 1) / 2 < k % p
  · exact choose_dvd_of_mod_gt_half hp h5 hrm
  · have hrm' : k % p ≤ (p - 1) / 2 := Nat.le_of_not_lt hrm
    have h2r_lt : 2 * (k % p) < p := by omega
    have hdiv : (2 * k) / p = 2 * (k / p) := by
      have hk := Nat.div_add_mod k p
      have h2k : 2 * k = p * (2 * (k / p)) + 2 * (k % p) := by linarith
      rw [h2k, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt h2r_lt, add_zero]
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * k) (k := k) (p := p)
    rw [hdiv] at hluc
    have hq_dvd : p ∣ Nat.choose (2 * (k / p)) (k / p) := by
      have hmodq : (k / p) % p = k / p := Nat.mod_eq_of_lt hlt
      exact choose_dvd_of_mod_gt_half hp h5 (by rw [hmodq]; exact hgt)
    have h0 : Nat.choose ((2 * k) % p) (k % p) * Nat.choose (2 * (k / p)) (k / p) ≡ 0 [MOD p] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_right hq_dvd _
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hluc.trans h0)

private def H1 (p k : ℕ) : ZMod (p ^ 3) :=
  ∑ j ∈ Finset.Icc 1 k, (j : ZMod (p ^ 3))⁻¹

private def H2 (p k : ℕ) : ZMod (p ^ 3) :=
  ∑ j ∈ Finset.Icc 1 k, ((j : ZMod (p ^ 3))⁻¹) ^ 2

private lemma choose_block_cube_zmod_p3 {p q r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    ((Nat.choose (2 * (q * p + r)) (q * p + r) : ℕ) : ZMod (p ^ 3)) ^ 3 =
      ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3 *
      ((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 *
      (1 + 6 * (q : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) * (H1 p (2 * r) - H1 p r) +
        (q : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 *
          (18 * (H1 p (2 * r) - H1 p r) ^ 2 - 6 * H2 p (2 * r) + 3 * H2 p r)) := by
  have h1p : 1 ≤ p := by omega
  have h2r_lt : 2 * r < p := by omega
  have hnat_main : Nat.choose (2 * (q * p + r)) (q * p + r) * ((q * p + r).factorial) ^ 2 =
      (2 * (q * p + r)).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show q * p + r ≤ 2 * (q * p + r) by omega)
    rw [show 2 * (q * p + r) - (q * p + r) = q * p + r by omega] at h1
    linarith [sq ((q * p + r).factorial)]
  have hnat_q : Nat.choose (2 * q) q * (q.factorial) ^ 2 = (2 * q).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show q ≤ 2 * q by omega)
    rw [show 2 * q - q = q by omega] at h1
    linarith [sq q.factorial]
  have hnat_r : Nat.choose (2 * r) r * (r.factorial) ^ 2 = (2 * r).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
    rw [show 2 * r - r = r by omega] at h1
    linarith [sq r.factorial]
  have hfac_num := factorial_split_nat p h1p (2 * q) (2 * r)
  have hfac_den := factorial_split_nat p h1p q r
  rw [show 2 * q * p + 2 * r = 2 * (q * p + r) by ring] at hfac_num
  have hcancel :
      Nat.choose (2 * (q * p + r)) (q * p + r) *
        (q.factorial) ^ 2 *
        (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) ^ 2 *
        (∏ j ∈ Finset.Icc 1 r, (q * p + j)) ^ 2 =
      (2 * q).factorial *
        (∏ u ∈ Finset.range (2 * q), ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) *
        (∏ j ∈ Finset.Icc 1 (2 * r), (2 * q * p + j)) := by
    apply Nat.mul_left_cancel (pow_pos hp.pos (2 * q))
    have hsq_p : (p ^ q) ^ 2 = p ^ (2 * q) := by rw [← pow_mul, mul_comm]
    calc p ^ (2 * q) * (Nat.choose (2 * (q * p + r)) (q * p + r) * (q.factorial) ^ 2 *
            (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) ^ 2 *
            (∏ j ∈ Finset.Icc 1 r, (q * p + j)) ^ 2)
        = Nat.choose (2 * (q * p + r)) (q * p + r) *
            (p ^ q * q.factorial *
              (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) *
              (∏ j ∈ Finset.Icc 1 r, (q * p + j))) ^ 2 := by rw [← hsq_p]; ring
      _ = Nat.choose (2 * (q * p + r)) (q * p + r) * ((q * p + r).factorial) ^ 2 := by rw [← hfac_den]
      _ = (2 * (q * p + r)).factorial := hnat_main
      _ = p ^ (2 * q) * ((2 * q).factorial *
            (∏ u ∈ Finset.range (2 * q), ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) *
            (∏ j ∈ Finset.Icc 1 (2 * r), (2 * q * p + j))) := by rw [hfac_num]; ring
  have hcancel2 :
      Nat.choose (2 * (q * p + r)) (q * p + r) *
        (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) ^ 2 *
        (∏ j ∈ Finset.Icc 1 r, (q * p + j)) ^ 2 =
      Nat.choose (2 * q) q *
        (∏ u ∈ Finset.range (2 * q), ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) *
        (∏ j ∈ Finset.Icc 1 (2 * r), (2 * q * p + j)) := by
    apply Nat.mul_left_cancel (pow_pos (Nat.factorial_pos q) 2)
    calc (q.factorial) ^ 2 * (Nat.choose (2 * (q * p + r)) (q * p + r) *
            (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) ^ 2 *
            (∏ j ∈ Finset.Icc 1 r, (q * p + j)) ^ 2)
        = Nat.choose (2 * (q * p + r)) (q * p + r) * (q.factorial) ^ 2 *
            (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) ^ 2 *
            (∏ j ∈ Finset.Icc 1 r, (q * p + j)) ^ 2 := by ring
      _ = (2 * q).factorial *
            (∏ u ∈ Finset.range (2 * q), ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) *
            (∏ j ∈ Finset.Icc 1 (2 * r), (2 * q * p + j)) := hcancel
      _ = (q.factorial) ^ 2 * (Nat.choose (2 * q) q *
            (∏ u ∈ Finset.range (2 * q), ∏ j ∈ Finset.Icc 1 (p - 1), (u * p + j)) *
            (∏ j ∈ Finset.Icc 1 (2 * r), (2 * q * p + j))) := by rw [← hnat_q]; ring
  have hcast :
      ((Nat.choose (2 * (q * p + r)) (q * p + r) : ℕ) : ZMod (p ^ 3)) *
        (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), ((u * p + j : ℕ) : ZMod (p ^ 3))) ^ 2 *
        (∏ j ∈ Finset.Icc 1 r, ((q * p + j : ℕ) : ZMod (p ^ 3))) ^ 2 =
      ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) *
        (∏ u ∈ Finset.range (2 * q), ∏ j ∈ Finset.Icc 1 (p - 1), ((u * p + j : ℕ) : ZMod (p ^ 3))) *
        (∏ j ∈ Finset.Icc 1 (2 * r), ((2 * q * p + j : ℕ) : ZMod (p ^ 3))) := by
    have h0 := congrArg (fun n : ℕ => (n : ZMod (p ^ 3))) hcancel2
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using h0
  have hblk_q : (∏ u ∈ Finset.range q, ∏ j ∈ Finset.Icc 1 (p - 1), ((u * p + j : ℕ) : ZMod (p ^ 3))) =
      ((p - 1).factorial : ZMod (p ^ 3)) ^ q := by
    rw [Finset.prod_congr rfl fun u _ => prod_block_eq_factorial hp h5 u, Finset.prod_const, Finset.card_range]
  have hblk_2q : (∏ u ∈ Finset.range (2 * q), ∏ j ∈ Finset.Icc 1 (p - 1), ((u * p + j : ℕ) : ZMod (p ^ 3))) =
      ((p - 1).factorial : ZMod (p ^ 3)) ^ (2 * q) := by
    rw [Finset.prod_congr rfl fun u _ => prod_block_eq_factorial hp h5 u, Finset.prod_const, Finset.card_range]
  rw [hblk_q, hblk_2q, ← pow_mul, mul_comm q 2] at hcast
  have hpart : ∀ (m s : ℕ), s < p →
      (∏ j ∈ Finset.Icc 1 s, ((m * p + j : ℕ) : ZMod (p ^ 3))) =
      (s.factorial : ZMod (p ^ 3)) * (1 + ((m * p : ℕ) : ZMod (p ^ 3)) * H1 p s +
        ((m * p : ℕ) : ZMod (p ^ 3)) ^ 2 * (2 : ZMod (p ^ 3))⁻¹ * (H1 p s ^ 2 - H2 p s)) := by
    intro m s hsp
    have hm3 : ((m * p : ℕ) : ZMod (p ^ 3)) ^ 3 = 0 := by
      rw [← Nat.cast_pow, mul_pow, mul_comm (m ^ 3), Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have h2u := two_mul_inv_eq_one (p := p) (k := 3) hp h5
    have hfs : ∏ j ∈ Finset.Icc 1 s, (j : ZMod (p ^ 3)) = (s.factorial : ZMod (p ^ 3)) := by
      rw [← Nat.cast_prod, prod_Icc_eq_factorial]
    have hs1 : ∏ j ∈ Finset.Icc 1 s, ((m * p + j : ℕ) : ZMod (p ^ 3)) =
        (∏ j ∈ Finset.Icc 1 s, (j : ZMod (p ^ 3))) *
        (∏ j ∈ Finset.Icc 1 s, (1 + ((m * p : ℕ) : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have hju := natCast_mul_inv_eq_one (k := 3) hp hj.1 (by omega)
      rw [Nat.cast_add]
      calc ((m * p : ℕ) : ZMod (p ^ 3)) + (j : ZMod (p ^ 3))
          = (j : ZMod (p ^ 3)) + ((m * p : ℕ) : ZMod (p ^ 3)) *
              ((j : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹) := by rw [hju, mul_one]; ring
        _ = (j : ZMod (p ^ 3)) * (1 + ((m * p : ℕ) : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹) := by ring
    rw [hs1, hfs, prod_one_add_cubed_zero _ _ _ hm3 h2u]
    rfl
  rw [hpart q r (by omega), hpart (2 * q) (2 * r) h2r_lt] at hcast
  have hrR : ((2 * r).factorial : ZMod (p ^ 3)) =
      (Nat.choose (2 * r) r : ZMod (p ^ 3)) * (r.factorial : ZMod (p ^ 3)) ^ 2 := by
    rw [← hnat_r, Nat.cast_mul, Nat.cast_pow]
  rw [hrR] at hcast
  have hunit_fac : ∀ s < p, IsUnit (s.factorial : ZMod (p ^ 3)) := by
    intro s hsp
    rw [ZMod.isUnit_iff_coprime]
    have : Nat.Coprime s.factorial p :=
      (hp.coprime_iff_not_dvd.mpr fun hd => by
        have := hp.dvd_factorial.mp hd; omega).symm
    exact this.pow_right 3
  have hu_r := (hunit_fac r (by omega)).pow 2
  have hu_p := (hunit_fac (p - 1) (by omega)).pow (2 * q)
  set U : ZMod (p ^ 3) :=
    ((p - 1).factorial : ZMod (p ^ 3)) ^ (2 * q) * (r.factorial : ZMod (p ^ 3)) ^ 2
  have hU : IsUnit U := hu_p.mul hu_r
  set x : ZMod (p ^ 3) := (q : ZMod (p ^ 3)) * (p : ZMod (p ^ 3))
  have hx3 : x ^ 3 = 0 := by
    have : x = ((q * p : ℕ) : ZMod (p ^ 3)) := by push_cast; rfl
    rw [this, ← Nat.cast_pow, mul_pow, mul_comm (q ^ 3), Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have h2u := two_mul_inv_eq_one (p := p) (k := 3) hp h5
  set E1 : ZMod (p ^ 3) := 1 + x * H1 p r + x ^ 2 * (2 : ZMod (p ^ 3))⁻¹ * (H1 p r ^ 2 - H2 p r)
  set E2 : ZMod (p ^ 3) := 1 + (2 * x) * H1 p (2 * r) +
    (2 * x) ^ 2 * (2 : ZMod (p ^ 3))⁻¹ * (H1 p (2 * r) ^ 2 - H2 p (2 * r))
  have hE1_eq : 1 + ((q * p : ℕ) : ZMod (p ^ 3)) * H1 p r +
      ((q * p : ℕ) : ZMod (p ^ 3)) ^ 2 * (2 : ZMod (p ^ 3))⁻¹ * (H1 p r ^ 2 - H2 p r) = E1 := by
    simp only [E1, x, Nat.cast_mul]
  have hE2_eq : 1 + ((2 * q * p : ℕ) : ZMod (p ^ 3)) * H1 p (2 * r) +
      ((2 * q * p : ℕ) : ZMod (p ^ 3)) ^ 2 * (2 : ZMod (p ^ 3))⁻¹ * (H1 p (2 * r) ^ 2 - H2 p (2 * r)) = E2 := by
    simp only [E2, x, Nat.cast_mul, Nat.cast_ofNat]; ring
  rw [hE1_eq, hE2_eq] at hcast
  have hmid : (Nat.choose (2 * (q * p + r)) (q * p + r) : ZMod (p ^ 3)) * E1 ^ 2 =
      (Nat.choose (2 * q) q : ZMod (p ^ 3)) * (Nat.choose (2 * r) r : ZMod (p ^ 3)) * E2 := by
    apply hU.mul_right_cancel
    linear_combination hcast
  set F1 : ZMod (p ^ 3) := 1 - 2 * x * H1 p r + x ^ 2 * (2 * H1 p r ^ 2 + H2 p r)
  have hE1_sq : E1 ^ 2 = 1 + 2 * x * H1 p r + x ^ 2 * (2 * H1 p r ^ 2 - H2 p r) := by
    simp only [E1]
    set a := H1 p r
    set b := H2 p r
    linear_combination
      (x ^ 2 * (a ^ 2 - b)) * h2u +
      (2 * a * (2 : ZMod (p ^ 3))⁻¹ * (a ^ 2 - b) + x * (2 : ZMod (p ^ 3))⁻¹ ^ 2 * (a ^ 2 - b) ^ 2) * hx3
  have hE1F1 : E1 ^ 2 * F1 = 1 := by
    rw [hE1_sq]
    simp only [F1]
    set a := H1 p r
    set b := H2 p r
    linear_combination
      (2 * a * (2 * a ^ 2 + b) - 2 * a * (2 * a ^ 2 - b) +
        x * (2 * a ^ 2 - b) * (2 * a ^ 2 + b)) * hx3
  have hsingle : (Nat.choose (2 * (q * p + r)) (q * p + r) : ZMod (p ^ 3)) =
      (Nat.choose (2 * q) q : ZMod (p ^ 3)) * (Nat.choose (2 * r) r : ZMod (p ^ 3)) * (E2 * F1) := by
    calc (Nat.choose (2 * (q * p + r)) (q * p + r) : ZMod (p ^ 3))
        = (Nat.choose (2 * (q * p + r)) (q * p + r) : ZMod (p ^ 3)) * (E1 ^ 2 * F1) := by rw [hE1F1, mul_one]
      _ = ((Nat.choose (2 * (q * p + r)) (q * p + r) : ZMod (p ^ 3)) * E1 ^ 2) * F1 := by ring
      _ = (Nat.choose (2 * q) q : ZMod (p ^ 3)) * (Nat.choose (2 * r) r : ZMod (p ^ 3)) * (E2 * F1) := by
            rw [hmid]; ring
  rw [hsingle, mul_pow, mul_pow]
  congr 1
  set d1 : ZMod (p ^ 3) := H1 p (2 * r) - H1 p r
  have hE2_simp : E2 = 1 + 2 * x * H1 p (2 * r) + 2 * x ^ 2 * (H1 p (2 * r) ^ 2 - H2 p (2 * r)) := by
    simp only [E2]
    linear_combination (2 * x ^ 2 * (H1 p (2 * r) ^ 2 - H2 p (2 * r))) * h2u
  have hE2F1 : E2 * F1 = 1 + 2 * x * d1 + x ^ 2 * (2 * d1 ^ 2 - 2 * H2 p (2 * r) + H2 p r) := by
    rw [hE2_simp]
    simp only [F1, d1]
    set a1 := H1 p r
    set a2 := H1 p (2 * r)
    set b1 := H2 p r
    set b2 := H2 p (2 * r)
    linear_combination
      (2 * a2 * (2 * a1 ^ 2 + b1) - 4 * a1 * (a2 ^ 2 - b2) +
        2 * x * (a2 ^ 2 - b2) * (2 * a1 ^ 2 + b1)) * hx3
  rw [hE2F1]
  set c2 : ZMod (p ^ 3) := 2 * d1 ^ 2 - 2 * H2 p (2 * r) + H2 p r
  have hcube : (1 + 2 * x * d1 + x ^ 2 * c2) ^ 3 = 1 + 6 * x * d1 + x ^ 2 * (12 * d1 ^ 2 + 3 * c2) := by
    linear_combination
      (8 * d1 ^ 3 + 12 * d1 * c2 + 12 * x * d1 ^ 2 * c2 + 3 * x * c2 ^ 2 +
        6 * x ^ 2 * d1 * c2 ^ 2 + x ^ 3 * c2 ^ 3) * hx3
  rw [hcube]
  simp only [c2, x]
  ring

private lemma a_p_mul_p_sub_one_eq_block_sum {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (OeisA79727.a (p * (p - 1)) : ZMod (p ^ 3)) =
      (∑ q ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3) ^ 2 +
      6 * (p : ZMod (p ^ 3)) *
        (∑ q ∈ Finset.range ((p - 1) / 2 + 1), (q : ZMod (p ^ 3)) * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3) *
        (∑ r ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 * (H1 p (2 * r) - H1 p r)) +
      (p : ZMod (p ^ 3)) ^ 2 *
        (∑ q ∈ Finset.range ((p - 1) / 2 + 1), (q : ZMod (p ^ 3)) ^ 2 * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3) *
        (∑ r ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 *
          (18 * (H1 p (2 * r) - H1 p r) ^ 2 - 6 * H2 p (2 * r) + 3 * H2 p r)) := by
  set m := (p - 1) / 2
  have hp_sub : p * (p - 1) + p = p * p := by
    rw [Nat.mul_sub_left_distrib, mul_one, Nat.sub_add_cancel (by nlinarith)]
  have h1 : (OeisA79727.a (p * (p - 1)) : ZMod (p ^ 3)) =
      ∑ k ∈ Finset.range (p * (p - 1) + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 3)) ^ 3 := by
    unfold OeisA79727.a
    simp only [Nat.cast_sum, Nat.cast_pow]
  rw [h1]
  set S_img : Finset ℕ := (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).image (fun qr => qr.1 * p + qr.2)
  have hsub_img : S_img ⊆ Finset.range (p * (p - 1) + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨⟨q, r⟩, hqr, rfl⟩
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqr
    rw [Finset.mem_range]
    have hq_le : q ≤ p - 2 := by omega
    have hqp : q * p ≤ (p - 2) * p := Nat.mul_le_mul_right p hq_le
    have hpp : (p - 2) * p + p = p * (p - 1) := by
      have : p - 1 = (p - 2) + 1 := by omega
      rw [this, Nat.mul_add, mul_one, mul_comm]
    dsimp only
    omega
  have hzero_out : ∀ k ∈ Finset.range (p * (p - 1) + 1), k ∉ S_img →
      ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 3)) ^ 3 = 0 := by
    intro k hk hnot
    rw [Finset.mem_range] at hk
    have hklt : k / p < p := Nat.div_lt_of_lt_mul (by omega)
    have hdvd : p ∣ Nat.choose (2 * k) k := by
      by_cases hrm : m < k % p
      · exact choose_dvd_of_mod_gt_half hp h5 hrm
      · have hrm' : k % p ≤ m := Nat.le_of_not_lt hrm
        have hqm : m < k / p := by
          by_contra hle
          have hle' : k / p ≤ m := Nat.le_of_not_lt hle
          apply hnot
          refine Finset.mem_image.mpr ⟨(k / p, k % p),
            Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_⟩
          simpa [mul_comm] using Nat.div_add_mod k p
        exact choose_dvd_of_div_gt_half hp h5 hqm hklt
    have hdvd3 : p ^ 3 ∣ (Nat.choose (2 * k) k) ^ 3 := pow_dvd_pow_of_dvd hdvd 3
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hdvd3
  have hinj : Set.InjOn (fun qr : ℕ × ℕ => qr.1 * p + qr.2)
      ↑(Finset.range (m + 1) ×ˢ Finset.range (m + 1)) := by
    intro a ha b hb hab
    dsimp only at hab
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at ha hb
    have hda : (a.1 * p + a.2) / p = a.1 := by
      rw [mul_comm, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega), add_zero]
    have hdb : (b.1 * p + b.2) / p = b.1 := by
      rw [mul_comm, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega), add_zero]
    have hq : a.1 = b.1 := by rw [← hda, ← hdb, hab]
    have hr : a.2 = b.2 := by nlinarith
    exact Prod.ext hq hr
  have hdrop : ∑ k ∈ Finset.range (p * (p - 1) + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 3)) ^ 3 =
      ∑ q ∈ Finset.range (m + 1), ∑ r ∈ Finset.range (m + 1),
        ((Nat.choose (2 * (q * p + r)) (q * p + r) : ℕ) : ZMod (p ^ 3)) ^ 3 := by
    rw [← Finset.sum_subset hsub_img hzero_out, Finset.sum_image hinj, Finset.sum_product]
  rw [hdrop]
  have hsub : ∀ q ∈ Finset.range (m + 1), ∀ r ∈ Finset.range (m + 1),
      ((Nat.choose (2 * (q * p + r)) (q * p + r) : ℕ) : ZMod (p ^ 3)) ^ 3 =
      ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3 * ((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 +
      6 * (p : ZMod (p ^ 3)) * ((q : ZMod (p ^ 3)) * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3) *
        (((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 * (H1 p (2 * r) - H1 p r)) +
      (p : ZMod (p ^ 3)) ^ 2 * ((q : ZMod (p ^ 3)) ^ 2 * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3) *
        (((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 *
          (18 * (H1 p (2 * r) - H1 p r) ^ 2 - 6 * H2 p (2 * r) + 3 * H2 p r)) := by
    intro q hq r hr
    rw [Finset.mem_range] at hq hr
    rw [choose_block_cube_zmod_p3 hp h5 (by omega)]
    ring
  calc ∑ q ∈ Finset.range (m + 1), ∑ r ∈ Finset.range (m + 1),
        ((Nat.choose (2 * (q * p + r)) (q * p + r) : ℕ) : ZMod (p ^ 3)) ^ 3
      = ∑ q ∈ Finset.range (m + 1), ∑ r ∈ Finset.range (m + 1),
          (((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3 * ((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 +
           6 * (p : ZMod (p ^ 3)) * ((q : ZMod (p ^ 3)) * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3) *
             (((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 * (H1 p (2 * r) - H1 p r)) +
           (p : ZMod (p ^ 3)) ^ 2 * ((q : ZMod (p ^ 3)) ^ 2 * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3) *
             (((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 *
               (18 * (H1 p (2 * r) - H1 p r) ^ 2 - 6 * H2 p (2 * r) + 3 * H2 p r))) := by
        refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun r hr => hsub q hq r hr
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sq]

end OMA_A79727


-- Complete Part 2 (hasse_inv_eq_zero)


namespace OMA_A79727_P2

private structure Quad7 (R : Type*) where
  re : R
  im : R

private lemma Quad7.ext {R : Type*} {a b : Quad7 R} (h1 : a.re = b.re) (h2 : a.im = b.im) : a = b := by
  cases a; cases b; congr

private instance {R : Type*} [Zero R] : Zero (Quad7 R) := ⟨⟨0, 0⟩⟩
private instance {R : Type*} [One R] [Zero R] : One (Quad7 R) := ⟨⟨1, 0⟩⟩
private instance {R : Type*} [Add R] : Add (Quad7 R) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
private instance {R : Type*} [Neg R] : Neg (Quad7 R) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
private instance {R : Type*} [Sub R] : Sub (Quad7 R) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
private instance {R : Type*} [CommRing R] : Mul (Quad7 R) :=
  ⟨fun x y => ⟨x.re * y.re - 7 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
private instance {R : Type*} [NatCast R] [Zero R] : NatCast (Quad7 R) := ⟨fun n => ⟨n, 0⟩⟩
private instance {R : Type*} [IntCast R] [Zero R] : IntCast (Quad7 R) := ⟨fun z => ⟨z, 0⟩⟩

@[simp] private lemma Quad7.zero_re {R : Type*} [Zero R] : (0 : Quad7 R).re = 0 := rfl
@[simp] private lemma Quad7.zero_im {R : Type*} [Zero R] : (0 : Quad7 R).im = 0 := rfl
@[simp] private lemma Quad7.one_re {R : Type*} [One R] [Zero R] : (1 : Quad7 R).re = 1 := rfl
@[simp] private lemma Quad7.one_im {R : Type*} [One R] [Zero R] : (1 : Quad7 R).im = 0 := rfl
@[simp] private lemma Quad7.add_re {R : Type*} [Add R] (x y : Quad7 R) : (x + y).re = x.re + y.re := rfl
@[simp] private lemma Quad7.add_im {R : Type*} [Add R] (x y : Quad7 R) : (x + y).im = x.im + y.im := rfl
@[simp] private lemma Quad7.neg_re {R : Type*} [Neg R] (x : Quad7 R) : (-x).re = -x.re := rfl
@[simp] private lemma Quad7.neg_im {R : Type*} [Neg R] (x : Quad7 R) : (-x).im = -x.im := rfl
@[simp] private lemma Quad7.sub_re {R : Type*} [Sub R] (x y : Quad7 R) : (x - y).re = x.re - y.re := rfl
@[simp] private lemma Quad7.sub_im {R : Type*} [Sub R] (x y : Quad7 R) : (x - y).im = x.im - y.im := rfl
@[simp] private lemma Quad7.mul_re {R : Type*} [CommRing R] (x y : Quad7 R) :
    (x * y).re = x.re * y.re - 7 * x.im * y.im := rfl
@[simp] private lemma Quad7.mul_im {R : Type*} [CommRing R] (x y : Quad7 R) :
    (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] private lemma Quad7.natCast_re {R : Type*} [NatCast R] [Zero R] (n : ℕ) : (n : Quad7 R).re = n := rfl
@[simp] private lemma Quad7.natCast_im {R : Type*} [NatCast R] [Zero R] (n : ℕ) : (n : Quad7 R).im = 0 := rfl
@[simp] private lemma Quad7.intCast_re {R : Type*} [IntCast R] [Zero R] (z : ℤ) : (z : Quad7 R).re = z := rfl
@[simp] private lemma Quad7.intCast_im {R : Type*} [IntCast R] [Zero R] (z : ℤ) : (z : Quad7 R).im = 0 := rfl

private instance {R : Type*} [CommRing R] : CommRing (Quad7 R) where
  add_assoc a b c := by apply Quad7.ext <;> simp [add_assoc]
  zero_add a := by apply Quad7.ext <;> simp
  add_zero a := by apply Quad7.ext <;> simp
  add_comm a b := by apply Quad7.ext <;> simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply Quad7.ext <;> simp
  sub_eq_add_neg a b := by apply Quad7.ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by apply Quad7.ext <;> simp <;> ring
  one_mul a := by apply Quad7.ext <;> simp
  mul_one a := by apply Quad7.ext <;> simp
  left_distrib a b c := by apply Quad7.ext <;> simp <;> ring
  right_distrib a b c := by apply Quad7.ext <;> simp <;> ring
  zero_mul a := by apply Quad7.ext <;> simp
  mul_zero a := by apply Quad7.ext <;> simp
  mul_comm a b := by apply Quad7.ext <;> simp <;> ring
  natCast_zero := by apply Quad7.ext <;> simp
  natCast_succ n := by apply Quad7.ext <;> simp
  intCast_ofNat n := by apply Quad7.ext <;> simp
  intCast_negSucc n := by apply Quad7.ext <;> simp [Int.cast_negSucc]

@[simp] private lemma Quad7.ofNat_re {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Quad7 R).re = OfNat.ofNat n := rfl
@[simp] private lemma Quad7.ofNat_im {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Quad7 R).im = 0 := rfl

private def Quad7.emb {R : Type*} [CommRing R] : R →+* Quad7 R where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_mul' a b := by apply Quad7.ext <;> simp
  map_zero' := rfl
  map_add' a b := by apply Quad7.ext <;> simp

private def Quad7.w {R : Type*} [CommRing R] : Quad7 R := ⟨0, 1⟩

private lemma Quad7.w_sq {R : Type*} [CommRing R] :
    (Quad7.w : Quad7 R) ^ 2 = Quad7.emb (-7) := by
  apply Quad7.ext <;> simp [Quad7.w, Quad7.emb, sq]

private lemma Quad7.charP {p : ℕ} {R : Type*} [CommRing R] [CharP R p] :
    CharP (Quad7 R) p := by
  refine ⟨fun n => ?_⟩
  constructor
  · intro h
    have hre : (n : R) = 0 := congrArg Quad7.re h
    exact (CharP.cast_eq_zero_iff R p n).mp hre
  · intro h
    apply Quad7.ext
    · exact (CharP.cast_eq_zero_iff R p n).mpr h
    · rfl

private lemma Quad7.norm_ne_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1)
    {x : Quad7 (ZMod p)} (hx : x ≠ 0) :
    x.re ^ 2 + 7 * x.im ^ 2 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  intro h0
  by_cases him : x.im = 0
  · rw [him, zero_pow two_ne_zero, mul_zero, add_zero] at h0
    have hre : x.re = 0 := sq_eq_zero_iff.mp h0
    exact hx (by apply Quad7.ext <;> assumption)
  · have hsq : (x.re * x.im⁻¹) ^ 2 = -7 := by
      have : x.re ^ 2 = -7 * x.im ^ 2 := by linear_combination h0
      rw [mul_pow, this, mul_assoc, ← mul_pow, mul_inv_cancel₀ him, one_pow, mul_one]
    have hpow : ((-7 : ZMod p) ^ ((p - 1) / 2)) = 1 := by
      have hodd : 2 * ((p - 1) / 2) = p - 1 := by
        have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
      rw [← hsq, ← pow_mul, hodd]
      have hne : x.re * x.im⁻¹ ≠ 0 := by
        intro hz
        rw [hz, zero_pow two_ne_zero] at hsq
        rw [← hsq, zero_pow (by omega : (p - 1) / 2 ≠ 0)] at hleg
        exact zero_ne_one (by linear_combination -hleg)
      exact ZMod.pow_card_sub_one_eq_one hne
    rw [hleg] at hpow
    have h2 : (2 : ZMod p) = 0 := by linear_combination -hpow
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
    have := Nat.le_of_dvd (by decide) hdvd; omega

private lemma Quad7.isUnit_of_ne_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1)
    {x : Quad7 (ZMod p)} (hx : x ≠ 0) : IsUnit x := by
  have : Fact p.Prime := ⟨hp⟩
  set N := x.re ^ 2 + 7 * x.im ^ 2
  have hN : N ≠ 0 := Quad7.norm_ne_zero hp h5 hleg hx
  refine isUnit_iff_exists_inv.mpr ⟨⟨x.re * N⁻¹, -x.im * N⁻¹⟩, ?_⟩
  apply Quad7.ext
  · simp only [Quad7.mul_re, Quad7.one_re]
    calc x.re * (x.re * N⁻¹) - 7 * x.im * (-x.im * N⁻¹)
        = (x.re ^ 2 + 7 * x.im ^ 2) * N⁻¹ := by ring
      _ = N * N⁻¹ := rfl
      _ = 1 := mul_inv_cancel₀ hN
  · simp only [Quad7.mul_im, Quad7.one_im]
    ring

private lemma Quad7.mul_eq_zero_iff {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1)
    {x y : Quad7 (ZMod p)} (hxy : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    rcases (Quad7.isUnit_of_ne_zero hp h5 hleg hx).exists_left_inv with ⟨u, hu⟩
    calc y = (u * x) * y := by rw [hu, one_mul]
      _ = u * (x * y) := by rw [mul_assoc]
      _ = 0 := by rw [hxy, mul_zero]

private lemma powerSeries_charP {K : Type*} [CommRing K] {p : ℕ} [CharP K p] :
    CharP (PowerSeries K) p := by
  refine ⟨fun n => ?_⟩
  constructor
  · intro h
    have h0 := congrArg PowerSeries.constantCoeff h
    simp only [map_natCast, map_zero] at h0
    exact (CharP.cast_eq_zero_iff K p n).mp h0
  · intro h
    rw [← map_natCast (PowerSeries.C (R := K)) n, (CharP.cast_eq_zero_iff K p n).mpr h, map_zero]

private lemma powerSeries_coeff_pow_p_shift {K : Type*} [CommRing K] {p : ℕ} [CharP K p] (hp : p.Prime)
    (h5 : 5 ≤ p) (G : PowerSeries K) (F : PowerSeries K) :
    PowerSeries.coeff (p - 1) (PowerSeries.X ^ ((p - 1) / 2) * (1 + PowerSeries.X * G) ^ p * F) =
      PowerSeries.coeff ((p - 1) / 2) F := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (PowerSeries K) p := powerSeries_charP
  have h1 : (1 + PowerSeries.X * G) ^ p = 1 + (PowerSeries.X * G) ^ p := by
    rw [add_pow_char, one_pow]
  rw [h1, mul_pow, mul_add, add_mul, map_add, mul_one]
  have hzero : PowerSeries.coeff (p - 1)
      (PowerSeries.X ^ ((p - 1) / 2) * (PowerSeries.X ^ p * G ^ p) * F) = 0 := by
    have hre : PowerSeries.X ^ ((p - 1) / 2) * (PowerSeries.X ^ p * G ^ p) * F =
        PowerSeries.X ^ p * (PowerSeries.X ^ ((p - 1) / 2) * G ^ p * F) := by ring
    rw [hre, PowerSeries.coeff_X_pow_mul']
    exact if_neg (by omega)
  rw [hzero, add_zero, PowerSeries.coeff_X_pow_mul']
  have hodd : 2 * ((p - 1) / 2) = p - 1 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  rw [if_pos (by omega)]
  have hsub : p - 1 - (p - 1) / 2 = (p - 1) / 2 := by omega
  rw [hsub]

private lemma powerSeries_deriv_residue_zero {K : Type*} [CommRing K] {p : ℕ}
    (r : ℕ) (hr1 : 1 ≤ r) (hrp : r < p) (H : PowerSeries K) :
    PowerSeries.coeff (p - 1)
      (PowerSeries.X ^ (p - r - 1) * (PowerSeries.X * PowerSeries.derivative K H - (r : PowerSeries K) * H)) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
  have hidx : p - 1 - (p - r - 1) = r := by omega
  rw [hidx, map_sub]
  rw [show PowerSeries.X * PowerSeries.derivative K H =
        PowerSeries.X ^ 1 * PowerSeries.derivative K H by rw [pow_one],
      PowerSeries.coeff_X_pow_mul', if_pos (by omega), PowerSeries.coeff_derivative]
  have hpred : r - 1 + 1 = r := by omega
  rw [hpred]
  have hcast : PowerSeries.coeff r ((r : PowerSeries K) * H) = (r : K) * PowerSeries.coeff r H := by
    rw [← map_natCast (PowerSeries.C (R := K)) r, PowerSeries.coeff_C_mul]
  rw [hcast, Nat.cast_sub hr1, Nat.cast_one]
  ring

private lemma powerSeries_key_deriv_ident {K : Type*} [CommRing K]
    (W W_inv V V' : PowerSeries K) (hW_mul : W * W_inv = 1)
    (hV : V = PowerSeries.X * W) (hV' : V' = PowerSeries.derivative K V)
    (p m k r : ℕ) (hmk : m + k = p - r - 1) (hp_eq : p = (m + k) + (r + 1)) (hr1 : 1 ≤ r) :
    (r : PowerSeries K) * (V' * W_inv ^ p * V ^ (m + k)) =
      -(PowerSeries.X ^ (p - r - 1) *
        (PowerSeries.X * PowerSeries.derivative K (W_inv ^ r) - (r : PowerSeries K) * W_inv ^ r)) := by
  subst hV'
  subst hV
  have hderiv_Winv : PowerSeries.derivative K W_inv = - PowerSeries.derivative K W * W_inv ^ 2 := by
    have hd := congrArg (PowerSeries.derivative K) hW_mul
    rw [Derivation.leibniz, Derivation.map_one_eq_zero] at hd
    simp only [smul_eq_mul] at hd
    calc PowerSeries.derivative K W_inv
        = (W * W_inv) * PowerSeries.derivative K W_inv := by rw [hW_mul, one_mul]
      _ = W_inv * (W * PowerSeries.derivative K W_inv) := by ring
      _ = W_inv * (-(PowerSeries.derivative K W * W_inv)) := by congr 1; linear_combination hd
      _ = -PowerSeries.derivative K W * W_inv ^ 2 := by ring
  have hd_pow : PowerSeries.derivative K (W_inv ^ r) =
      (r : PowerSeries K) * W_inv ^ (r - 1) * (-PowerSeries.derivative K W * W_inv ^ 2) := by
    rw [PowerSeries.derivative_pow, hderiv_Winv]
  have hdV : PowerSeries.derivative K (PowerSeries.X * W) = W + PowerSeries.X * PowerSeries.derivative K W := by
    simp only [Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, mul_one]; ring
  have hWcancel : W_inv ^ p * W ^ (m + k) = W_inv ^ (r + 1) := by
    rw [hp_eq, pow_add]
    calc W_inv ^ (m + k) * W_inv ^ (r + 1) * W ^ (m + k)
        = (W * W_inv) ^ (m + k) * W_inv ^ (r + 1) := by rw [mul_pow]; ring
      _ = W_inv ^ (r + 1) := by rw [hW_mul, one_pow, one_mul]
  have hWcancel2 : W_inv ^ (r + 1) * W = W_inv ^ r := by
    rw [pow_succ]
    calc W_inv ^ r * W_inv * W = W_inv ^ r * (W * W_inv) := by ring
      _ = W_inv ^ r := by rw [hW_mul, mul_one]
  have hWcancel3 : W_inv ^ (r - 1) * W_inv ^ 2 = W_inv ^ (r + 1) := by
    rw [← pow_add, show r - 1 + 2 = r + 1 by omega]
  have hXpow : (PowerSeries.X * W) ^ (m + k) = PowerSeries.X ^ (p - r - 1) * W ^ (m + k) := by
    rw [mul_pow, hmk]
  rw [hd_pow, hdV, hXpow]
  calc (r : PowerSeries K) *
        ((W + PowerSeries.X * PowerSeries.derivative K W) * W_inv ^ p *
          (PowerSeries.X ^ (p - r - 1) * W ^ (m + k)))
      = (r : PowerSeries K) * PowerSeries.X ^ (p - r - 1) *
        ((W + PowerSeries.X * PowerSeries.derivative K W) * (W_inv ^ p * W ^ (m + k))) := by ring
    _ = (r : PowerSeries K) * PowerSeries.X ^ (p - r - 1) *
        (W_inv ^ (r + 1) * W + PowerSeries.X * PowerSeries.derivative K W * W_inv ^ (r + 1)) := by
          rw [hWcancel]; ring
    _ = (r : PowerSeries K) * PowerSeries.X ^ (p - r - 1) *
        (W_inv ^ r + PowerSeries.X * PowerSeries.derivative K W * (W_inv ^ (r - 1) * W_inv ^ 2)) := by
          rw [hWcancel2, hWcancel3]
    _ = -(PowerSeries.X ^ (p - r - 1) *
        (PowerSeries.X * ((r : PowerSeries K) * W_inv ^ (r - 1) *
          (-PowerSeries.derivative K W * W_inv ^ 2)) - (r : PowerSeries K) * W_inv ^ r)) := by ring

private noncomputable def revPoly {R : Type*} [CommRing R] (d : ℕ) (P : Polynomial R) : Polynomial R :=
  ∑ k ∈ Finset.range (d + 1), C (P.coeff (d - k)) * Polynomial.X ^ k

private lemma revPoly_coeff {R : Type*} [CommRing R] (d : ℕ) (P : Polynomial R) (k : ℕ) :
    (revPoly d P).coeff k = if k ≤ d then P.coeff (d - k) else 0 := by
  simp only [revPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h1 h2
  · rfl
  · rw [Finset.mem_range] at h1; omega
  · rw [Finset.mem_range] at h1; omega
  · rfl

private lemma revPoly_mul {R : Type*} [CommRing R] (d1 d2 : ℕ) (P Q : Polynomial R)
    (hP : P.natDegree ≤ d1) (hQ : Q.natDegree ≤ d2) :
    revPoly (d1 + d2) (P * Q) = revPoly d1 P * revPoly d2 Q := by
  ext k
  rw [revPoly_coeff]
  by_cases hk : k ≤ d1 + d2
  · rw [if_pos hk, Polynomial.coeff_mul, Polynomial.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => P.coeff a * Q.coeff b)]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (revPoly d1 P).coeff i * (revPoly d2 Q).coeff j)]
    simp_rw [revPoly_coeff]
    have hL : ∑ a ∈ Finset.range (d1 + d2 - k + 1), P.coeff a * Q.coeff (d1 + d2 - k - a) =
        ∑ a ∈ (Finset.range (d1 + d2 - k + 1)).filter (fun a => a ≤ d1 ∧ d1 + d2 - k - a ≤ d2),
          P.coeff a * Q.coeff (d1 + d2 - k - a) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun a ha hnot => ?_
      rw [Finset.mem_filter] at hnot
      have hfail : ¬(a ≤ d1 ∧ d1 + d2 - k - a ≤ d2) := fun h => hnot ⟨ha, h⟩
      by_cases ha1 : a ≤ d1
      · have hgt : d2 < d1 + d2 - k - a := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), mul_zero]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (by omega), zero_mul]
    have hR : ∑ i ∈ Finset.range (k + 1),
          (if i ≤ d1 then P.coeff (d1 - i) else 0) * (if k - i ≤ d2 then Q.coeff (d2 - (k - i)) else 0) =
        ∑ i ∈ (Finset.range (k + 1)).filter (fun i => i ≤ d1 ∧ k - i ≤ d2),
          P.coeff (d1 - i) * Q.coeff (d2 - (k - i)) := by
      have hsub : ∑ i ∈ Finset.range (k + 1),
            (if i ≤ d1 then P.coeff (d1 - i) else 0) * (if k - i ≤ d2 then Q.coeff (d2 - (k - i)) else 0) =
          ∑ i ∈ (Finset.range (k + 1)).filter (fun i => i ≤ d1 ∧ k - i ≤ d2),
            (if i ≤ d1 then P.coeff (d1 - i) else 0) * (if k - i ≤ d2 then Q.coeff (d2 - (k - i)) else 0) := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hnot => ?_
        rw [Finset.mem_filter] at hnot
        have hfail : ¬(i ≤ d1 ∧ k - i ≤ d2) := fun h => hnot ⟨hi, h⟩
        by_cases h1 : i ≤ d1
        · have h2 : ¬(k - i ≤ d2) := fun h => hfail ⟨h1, h⟩
          rw [if_pos h1, if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
      rw [hsub]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [if_pos hi.2.1, if_pos hi.2.2]
    rw [hL, hR]
    refine Finset.sum_bij (fun a _ => d1 - a) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha ⊢
      omega
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      omega
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨d1 - i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩, by omega⟩
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      congr 2 <;> omega
  · rw [if_neg hk, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (revPoly d1 P).coeff i * (revPoly d2 Q).coeff j)]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [revPoly_coeff, revPoly_coeff]
    by_cases h1 : i ≤ d1
    · rw [if_pos h1, if_neg (by omega), mul_zero]
    · rw [if_neg h1, zero_mul]

private lemma revPoly_pow {R : Type*} [CommRing R] (d : ℕ) (P : Polynomial R) (hP : P.natDegree ≤ d) :
    ∀ n : ℕ, revPoly (n * d) (P ^ n) = (revPoly d P) ^ n := by
  intro n
  induction n with
  | zero =>
    ext k
    rw [zero_mul, pow_zero, pow_zero, revPoly_coeff, Polynomial.coeff_one, Polynomial.coeff_one]
    split_ifs <;> first | rfl | omega
  | succ n ih =>
    rw [Nat.succ_mul, pow_succ, pow_succ, revPoly_mul (n * d) d (P ^ n) P
      ((Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left n hP)) hP, ih]

private lemma endo_ring_ident {R : Type*} [CommRing R]
    (X0 W0 W_num W_den dW_num dW_den c2_v : R)
    (hWnum : W_num = 8 * (1 - W0 * X0))
    (hWden : W_den = (-3 + W0) + (-70 + 10 * W0) * X0 + (-203 - 63 * W0) * X0 ^ 2)
    (hdWnum : dW_num = 8 * (1 - 2 * W0 * X0))
    (hdWden : dW_den = (-70 + 10 * W0) + 2 * (-203 - 63 * W0) * X0)
    (hc2 : c2_v = -3 + W0)
    (hrel : W0 ^ 2 + 7 = 0) :
    8 * ((X0 * W_num) * (W_den + 21 * (X0 * W_num)) * (W_den ^ 2 + 7 * (X0 * W_num) ^ 2)) =
    c2_v * X0 * (dW_num * W_den - X0 * W_num * dW_den) ^ 2 *
      ((1 + 21 * X0) * (1 + 7 * X0 ^ 2)) := by
  subst hWnum hWden hdWnum hdWden hc2
  linear_combination
    (-940800 * W0 ^ 3 * X0 ^ 8 - 421120 * W0 ^ 3 * X0 ^ 7 - 189952 * W0 ^ 3 * X0 ^ 6 -
     61952 * W0 ^ 3 * X0 ^ 5 - 7936 * W0 ^ 3 * X0 ^ 4 - 256 * W0 ^ 3 * X0 ^ 3 +
     93148608 * W0 ^ 2 * X0 ^ 8 - 12865664 * W0 ^ 2 * X0 ^ 7 + 4990272 * W0 ^ 2 * X0 ^ 6 +
     1682688 * W0 ^ 2 * X0 ^ 5 + 130112 * W0 ^ 2 * X0 ^ 4 + 7040 * W0 ^ 2 * X0 ^ 3 +
     192 * W0 ^ 2 * X0 ^ 2 + 238818944 * W0 * X0 ^ 8 - 101129728 * W0 * X0 ^ 7 -
     28941696 * W0 * X0 ^ 6 - 7440384 * W0 * X0 ^ 5 - 1188992 * W0 * X0 ^ 4 -
     68096 * W0 * X0 ^ 3 - 1152 * W0 * X0 ^ 2 + 166154688 * X0 ^ 8 -
     68571776 * X0 ^ 7 + 3001152 * X0 ^ 6 + 13043968 * X0 ^ 5 +
     3658816 * X0 ^ 4 + 147840 * X0 ^ 3 + 1728 * X0 ^ 2) * hrel

private lemma lam_pow_half_ne_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1)
    (u_8 : (Quad7 (ZMod p))ˣ) (hu_8 : (u_8 : Quad7 (ZMod p)) = 8) :
    ((⟨-3, 1⟩ : Quad7 (ZMod p)) * (u_8⁻¹ : (Quad7 (ZMod p))ˣ)) ^ ((p - 1) / 2) ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set K := Quad7 (ZMod p)
  have : CharP K p := Quad7.charP
  set m := (p - 1) / 2
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  set w : K := Quad7.w
  have hw2 : w ^ 2 = Quad7.emb (-7) := Quad7.w_sq
  set c2 : K := ⟨-3, 1⟩
  set lam : K := c2 * (u_8⁻¹ : Kˣ)
  have hlam_sq : lam = (⟨1, 1⟩ * (u_8⁻¹ : Kˣ) * 2) ^ 2 := by
    have h1w : (⟨1, 1⟩ : K) ^ 2 = 2 * c2 := by apply Quad7.ext <;> simp [K, c2, sq] <;> ring
    have h4 : (2 : K) ^ 2 = 4 := by norm_num
    calc lam = c2 * (u_8⁻¹ : Kˣ) := rfl
      _ = c2 * (u_8⁻¹ : Kˣ) * ((u_8 : K) * (u_8⁻¹ : Kˣ)) := by rw [Units.mul_inv, mul_one]
      _ = (2 * c2) * (u_8⁻¹ : Kˣ) ^ 2 * 4 := by rw [hu_8]; ring
      _ = (⟨1, 1⟩ : K) ^ 2 * (u_8⁻¹ : Kˣ) ^ 2 * 2 ^ 2 := by rw [h1w, h4]
      _ = (⟨1, 1⟩ * (u_8⁻¹ : Kˣ) * 2) ^ 2 := by ring
  change lam ^ m ≠ 1
  rw [hlam_sq, ← pow_mul, h2m]
  intro h1
  have hmul_p : (⟨1, 1⟩ * (u_8⁻¹ : Kˣ) * 2 : K) ^ p = ⟨1, 1⟩ * (u_8⁻¹ : Kˣ) * 2 := by
    rw [show (⟨1, 1⟩ * (u_8⁻¹ : Kˣ) * 2 : K) ^ p =
          (⟨1, 1⟩ * (u_8⁻¹ : Kˣ) * 2 : K) ^ (p - 1) * (⟨1, 1⟩ * (u_8⁻¹ : Kˣ) * 2 : K) by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)],
      h1, one_mul]
  have h2p : (2 : K) ^ p = 2 := by
    have : (2 : K) = Quad7.emb (2 : ZMod p) := rfl
    rw [this, ← map_pow, ZMod.pow_card]
  have h8p : ((u_8⁻¹ : Kˣ) : K) ^ p = ((u_8⁻¹ : Kˣ) : K) := by
    have h8_emb : (u_8 : K) ^ p = (u_8 : K) := by
      rw [hu_8]
      have : (8 : K) = Quad7.emb (8 : ZMod p) := rfl
      rw [this, ← map_pow, ZMod.pow_card]
    calc ((u_8⁻¹ : Kˣ) : K) ^ p = ((u_8⁻¹ : Kˣ) : K) ^ p * ((u_8 : K) ^ p * ((u_8⁻¹ : Kˣ) : K)) := by
          rw [h8_emb, Units.mul_inv, mul_one]
      _ = (((u_8⁻¹ : Kˣ) : K) * (u_8 : K)) ^ p * ((u_8⁻¹ : Kˣ) : K) := by rw [mul_pow]; ring
      _ = ((u_8⁻¹ : Kˣ) : K) := by rw [Units.inv_mul, one_pow, one_mul]
  have hwp : w ^ p = -w := by
    rw [show w ^ p = (w ^ 2) ^ m * w by rw [← pow_mul, ← pow_succ]; congr 1; omega,
      hw2, ← map_pow, hleg]
    apply Quad7.ext <;> simp [K, w, Quad7.w, Quad7.emb]
  have h1wp : (⟨1, 1⟩ : K) ^ p = ⟨1, -1⟩ := by
    have h1w_eq : (⟨1, 1⟩ : K) = 1 + w := by apply Quad7.ext <;> simp [K, w, Quad7.w]
    rw [h1w_eq, add_pow_char, one_pow, hwp]
    apply Quad7.ext <;> simp [K, w, Quad7.w]
  rw [mul_pow, mul_pow, h1wp, h8p, h2p] at hmul_p
  have h2_ne : (2 : K) ≠ 0 := by
    intro hz; have hre : (2 : ZMod p) = 0 := congrArg Quad7.re hz
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hre)
    have := Nat.le_of_dvd (by decide) hdvd; omega
  have hdiff : ((⟨1, -1⟩ : K) - ⟨1, 1⟩) * ((u_8⁻¹ : Kˣ) * 2) = 0 := by linear_combination hmul_p
  have hu_ne : ((u_8⁻¹ : Kˣ) * 2 : K) ≠ 0 := by
    intro hz
    rcases Quad7.mul_eq_zero_iff hp h5 hleg hz with h | h
    · have h1 : (1 : K) = 0 := by rw [← Units.inv_mul u_8, h, zero_mul]
      exact one_ne_zero (congrArg Quad7.re h1)
    · exact h2_ne h
  have h0 := (Quad7.mul_eq_zero_iff hp h5 hleg hdiff).resolve_right hu_ne
  have him : (-2 : ZMod p) = 0 := by
    have h1 := congrArg Quad7.im h0
    simp only [Quad7.sub_im, Quad7.zero_im] at h1
    linear_combination h1
  have h2z : (2 : ZMod p) = 0 := by linear_combination -him
  have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2z)
  have := Nat.le_of_dvd (by decide) hdvd; omega

private lemma endo_exists {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1) :
    ∃ (W W_inv : PowerSeries (Quad7 (ZMod p))) (lam : Quad7 (ZMod p)),
      W * W_inv = 1 ∧
      (PowerSeries.X * W) * Polynomial.aeval (PowerSeries.X * W)
        ((1 + C (21 : Quad7 (ZMod p)) * Polynomial.X) * (1 + C (7 : Quad7 (ZMod p)) * Polynomial.X ^ 2)) =
      PowerSeries.C lam * PowerSeries.X * (PowerSeries.derivative (Quad7 (ZMod p)) (PowerSeries.X * W)) ^ 2 *
        Polynomial.aeval PowerSeries.X
          ((1 + C (21 : Quad7 (ZMod p)) * Polynomial.X) * (1 + C (7 : Quad7 (ZMod p)) * Polynomial.X ^ 2)) ∧
      lam ^ ((p - 1) / 2) ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set K := Quad7 (ZMod p)
  have : CharP K p := Quad7.charP
  set m := (p - 1) / 2
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  set w : K := Quad7.w
  have hw2 : w ^ 2 = Quad7.emb (-7) := Quad7.w_sq
  set fT : Polynomial K := (1 + C (21 : K) * Polynomial.X) * (1 + C (7 : K) * Polynomial.X ^ 2)
  set c2 : K := ⟨-3, 1⟩
  set c1 : K := ⟨-70, 10⟩
  set c0 : K := ⟨-203, -63⟩
  have hc2_ne : c2 ≠ 0 := by
    intro h
    have him : (1 : ZMod p) = 0 := congrArg Quad7.im h
    exact one_ne_zero him
  have h8_ne : (8 : K) ≠ 0 := by
    intro h
    have hre : (8 : ZMod p) = 0 := congrArg Quad7.re h
    have hdvd := (ZMod.natCast_eq_zero_iff 8 p).mp (by simpa using hre)
    have h2dvd : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using hdvd)
    have := Nat.le_of_dvd (by decide) h2dvd; omega
  obtain ⟨u_c2, hu_c2⟩ := Quad7.isUnit_of_ne_zero hp h5 hleg hc2_ne
  obtain ⟨u_8, hu_8⟩ := Quad7.isUnit_of_ne_zero hp h5 hleg h8_ne
  set W_num : PowerSeries K := PowerSeries.C (8 : K) * (1 - PowerSeries.C w * PowerSeries.X)
  set W_den : PowerSeries K :=
    PowerSeries.C c2 + PowerSeries.C c1 * PowerSeries.X + PowerSeries.C c0 * PowerSeries.X ^ 2
  have hWden_c0 : PowerSeries.constantCoeff W_den = (u_c2 : K) := by
    simp [W_den, hu_c2]
  set W_den_inv : PowerSeries K := PowerSeries.invOfUnit W_den u_c2
  have hWden_mul : W_den * W_den_inv = 1 := PowerSeries.mul_invOfUnit W_den u_c2 hWden_c0
  set W : PowerSeries K := W_num * W_den_inv
  have hW_c0 : PowerSeries.constantCoeff W = (u_8 * u_c2⁻¹ : Kˣ) := by
    simp [W, W_num, W_den_inv, hu_8, PowerSeries.constantCoeff_invOfUnit]
  set W_inv : PowerSeries K := PowerSeries.invOfUnit W (u_8 * u_c2⁻¹)
  have hW_mul : W * W_inv = 1 := PowerSeries.mul_invOfUnit W (u_8 * u_c2⁻¹) hW_c0
  set V : PowerSeries K := PowerSeries.X * W
  have hVW : V * W_den = PowerSeries.X * W_num := by
    calc V * W_den = PowerSeries.X * W_num * (W_den * W_den_inv) := by simp only [V, W]; ring
      _ = PowerSeries.X * W_num := by rw [hWden_mul, mul_one]
  set V' : PowerSeries K := PowerSeries.derivative K V
  have hV'_eq : V' * W_den ^ 2 =
      PowerSeries.derivative K (PowerSeries.X * W_num) * W_den -
      PowerSeries.X * W_num * PowerSeries.derivative K W_den := by
    have hd := congrArg (PowerSeries.derivative K) hVW
    rw [Derivation.leibniz] at hd
    calc V' * W_den ^ 2
        = (V' * W_den) * W_den := by ring
      _ = (PowerSeries.derivative K (PowerSeries.X * W_num) - V * PowerSeries.derivative K W_den) * W_den := by
            congr 1; linear_combination hd
      _ = PowerSeries.derivative K (PowerSeries.X * W_num) * W_den -
            (V * W_den) * PowerSeries.derivative K W_den := by ring
      _ = PowerSeries.derivative K (PowerSeries.X * W_num) * W_den -
            PowerSeries.X * W_num * PowerSeries.derivative K W_den := by rw [hVW]
  set lam : K := c2 * (u_8⁻¹ : Kˣ)
  have hlam_8 : (8 : K) * lam = c2 := by
    simp only [lam]
    calc (8 : K) * (c2 * (u_8⁻¹ : Kˣ)) = c2 * ((u_8 : K) * (u_8⁻¹ : Kˣ)) := by rw [hu_8]; ring
      _ = c2 := by rw [Units.mul_inv, mul_one]
  have h_endo : V * Polynomial.aeval V fT =
      PowerSeries.C lam * PowerSeries.X * V' ^ 2 * Polynomial.aeval PowerSeries.X fT := by
    have hclear : PowerSeries.C (8 : K) * W_den ^ 4 * (V * Polynomial.aeval V fT) =
        PowerSeries.C (8 : K) * W_den ^ 4 *
          (PowerSeries.C lam * PowerSeries.X * V' ^ 2 * Polynomial.aeval PowerSeries.X fT) := by
      have hLHS : W_den ^ 4 * (V * Polynomial.aeval V fT) =
          (PowerSeries.X * W_num) *
            (W_den + PowerSeries.C (21 : K) * (PowerSeries.X * W_num)) *
            (W_den ^ 2 + PowerSeries.C (7 : K) * (PowerSeries.X * W_num) ^ 2) := by
        simp only [fT, map_mul, map_add, map_one, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        calc W_den ^ 4 * (V * ((1 + PowerSeries.C (21 : K) * V) * (1 + PowerSeries.C (7 : K) * V ^ 2)))
            = (V * W_den) * (W_den + PowerSeries.C (21 : K) * (V * W_den)) *
              (W_den ^ 2 + PowerSeries.C (7 : K) * (V * W_den) ^ 2) := by ring
          _ = _ := by rw [hVW]
      have hRHS : PowerSeries.C (8 : K) * W_den ^ 4 *
            (PowerSeries.C lam * PowerSeries.X * V' ^ 2 * Polynomial.aeval PowerSeries.X fT) =
          PowerSeries.C c2 * PowerSeries.X * (V' * W_den ^ 2) ^ 2 *
            ((1 + PowerSeries.C (21 : K) * PowerSeries.X) * (1 + PowerSeries.C (7 : K) * PowerSeries.X ^ 2)) := by
        simp only [fT, map_mul, map_add, map_one, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        have hC8 : PowerSeries.C (8 : K) * PowerSeries.C lam = PowerSeries.C c2 := by
          rw [← map_mul, hlam_8]
        calc PowerSeries.C (8 : K) * W_den ^ 4 *
              (PowerSeries.C lam * PowerSeries.X * V' ^ 2 *
                ((1 + PowerSeries.C (21 : K) * PowerSeries.X) * (1 + PowerSeries.C (7 : K) * PowerSeries.X ^ 2)))
            = (PowerSeries.C (8 : K) * PowerSeries.C lam) * PowerSeries.X * (V' * W_den ^ 2) ^ 2 *
              ((1 + PowerSeries.C (21 : K) * PowerSeries.X) * (1 + PowerSeries.C (7 : K) * PowerSeries.X ^ 2)) := by ring
          _ = _ := by rw [hC8]
      rw [mul_assoc, hLHS, hRHS, hV'_eq]
      have hd1 : PowerSeries.derivative K (PowerSeries.X * W_num) =
          PowerSeries.C (8 : K) * (1 - PowerSeries.C (2 * w) * PowerSeries.X) := by
        have h1 : PowerSeries.X * W_num =
            PowerSeries.C (8 : K) * PowerSeries.X - PowerSeries.C (8 * w) * PowerSeries.X ^ 2 := by
          simp only [W_num, map_mul]; ring
        rw [h1, map_sub, Derivation.leibniz, Derivation.leibniz,
          PowerSeries.derivative_C, PowerSeries.derivative_C, PowerSeries.derivative_X,
          PowerSeries.derivative_pow, PowerSeries.derivative_X]
        simp only [smul_eq_mul, mul_zero, add_zero, mul_one, Nat.cast_ofNat, map_mul, map_ofNat]
        ring
      have hd2 : PowerSeries.derivative K W_den =
          PowerSeries.C c1 + PowerSeries.C (2 * c0) * PowerSeries.X := by
        simp only [W_den, map_add, Derivation.leibniz,
          PowerSeries.derivative_C, PowerSeries.derivative_X, PowerSeries.derivative_pow]
        simp only [smul_eq_mul, mul_zero, add_zero, mul_one, Nat.cast_ofNat, map_mul, map_ofNat]
        ring
      have hc2_w : c2 = -3 + w := by apply Quad7.ext <;> simp [K, c2, w, Quad7.w]
      have hc1_w : c1 = -70 + 10 * w := by apply Quad7.ext <;> simp [K, c1, w, Quad7.w]
      have hc0_w : c0 = -203 - 63 * w := by apply Quad7.ext <;> simp [K, c0, w, Quad7.w]
      have hCw2 : PowerSeries.C w ^ 2 = (-7 : PowerSeries K) := by
        rw [← map_pow, hw2, show Quad7.emb (-7 : ZMod p) = (-7 : K) by apply Quad7.ext <;> simp [K, Quad7.emb],
          map_neg, map_ofNat]
      have hCc2 : PowerSeries.C c2 = (-3 : PowerSeries K) + PowerSeries.C w := by
        rw [hc2_w, map_add, map_neg, map_ofNat]
      have hCc1 : PowerSeries.C c1 = (-70 : PowerSeries K) + 10 * PowerSeries.C w := by
        rw [hc1_w, map_add, map_neg, map_mul, map_ofNat, map_ofNat]
      have hCc0 : PowerSeries.C c0 = (-203 : PowerSeries K) - 63 * PowerSeries.C w := by
        rw [hc0_w, map_sub, map_neg, map_mul, map_ofNat, map_ofNat]
      have hC2c0 : PowerSeries.C (2 * c0) = (2 : PowerSeries K) * PowerSeries.C c0 := by
        rw [map_mul, map_ofNat]
      have hC2w : PowerSeries.C (2 * w) = (2 : PowerSeries K) * PowerSeries.C w := by
        rw [map_mul, map_ofNat]
      have hWnum_eq : W_num = 8 * (1 - PowerSeries.C w * PowerSeries.X) := by
        simp only [W_num, map_ofNat]
      have hWden_eq : W_den = (-3 + PowerSeries.C w) + (-70 + 10 * PowerSeries.C w) * PowerSeries.X +
          (-203 - 63 * PowerSeries.C w) * PowerSeries.X ^ 2 := by
        simp only [W_den, hCc2, hCc1, hCc0]
      have hd1_eq : PowerSeries.derivative K (PowerSeries.X * W_num) =
          8 * (1 - 2 * PowerSeries.C w * PowerSeries.X) := by
        rw [hd1, hC2w]; simp only [map_ofNat]
      have hd2_eq : PowerSeries.derivative K W_den =
          (-70 + 10 * PowerSeries.C w) + 2 * (-203 - 63 * PowerSeries.C w) * PowerSeries.X := by
        rw [hd2, hC2c0, hCc1, hCc0]
      have hrel : (PowerSeries.C w : PowerSeries K) ^ 2 + 7 = 0 := by linear_combination hCw2
      simp only [map_ofNat]
      exact endo_ring_ident PowerSeries.X (PowerSeries.C w) W_num W_den
        (PowerSeries.derivative K (PowerSeries.X * W_num)) (PowerSeries.derivative K W_den)
        (PowerSeries.C c2) hWnum_eq hWden_eq hd1_eq hd2_eq hCc2 hrel
    have h8c : PowerSeries.C ((u_8⁻¹ : Kˣ) : K) * PowerSeries.C (8 : K) = 1 := by
      rw [← map_mul, ← hu_8, Units.inv_mul, map_one]
    calc V * Polynomial.aeval V fT
        = (PowerSeries.C ((u_8⁻¹ : Kˣ) : K) * PowerSeries.C (8 : K)) *
          (W_den * W_den_inv) ^ 4 * (V * Polynomial.aeval V fT) := by
            rw [h8c, hWden_mul, one_pow, mul_one, one_mul]
      _ = (PowerSeries.C ((u_8⁻¹ : Kˣ) : K) * W_den_inv ^ 4) *
          (PowerSeries.C (8 : K) * W_den ^ 4 * (V * Polynomial.aeval V fT)) := by ring
      _ = (PowerSeries.C ((u_8⁻¹ : Kˣ) : K) * W_den_inv ^ 4) *
          (PowerSeries.C (8 : K) * W_den ^ 4 *
            (PowerSeries.C lam * PowerSeries.X * V' ^ 2 * Polynomial.aeval PowerSeries.X fT)) := by rw [hclear]
      _ = (PowerSeries.C ((u_8⁻¹ : Kˣ) : K) * PowerSeries.C (8 : K)) *
          (W_den * W_den_inv) ^ 4 *
          (PowerSeries.C lam * PowerSeries.X * V' ^ 2 * Polynomial.aeval PowerSeries.X fT) := by ring
      _ = PowerSeries.C lam * PowerSeries.X * V' ^ 2 * Polynomial.aeval PowerSeries.X fT := by
            rw [h8c, hWden_mul, one_pow, mul_one, one_mul]
  exact ⟨W, W_inv, lam, hW_mul, h_endo, lam_pow_half_ne_one hp h5 hleg u_8 hu_8⟩

private lemma hasse_inv_eq_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1) :
    (((Polynomial.X + C 21) * (Polynomial.X ^ 2 + C 7) : Polynomial (ZMod p)) ^ ((p - 1) / 2)).coeff (p - 1) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set K := Quad7 (ZMod p)
  have : CharP K p := Quad7.charP
  have : CharP (PowerSeries K) p := powerSeries_charP
  set m := (p - 1) / 2
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  set fT : Polynomial K := (1 + C (21 : K) * Polynomial.X) * (1 + C (7 : K) * Polynomial.X ^ 2)
  set Hp : ZMod p := (((Polynomial.X + C 21) * (Polynomial.X ^ 2 + C 7) : Polynomial (ZMod p)) ^ m).coeff (p - 1)
  have hHp_eq : (fT ^ m).coeff m = Quad7.emb Hp := by
    set g0 : Polynomial (ZMod p) := (Polynomial.X + C 21) * (Polynomial.X ^ 2 + C 7)
    set g1 : Polynomial (ZMod p) := (1 + C 21 * Polynomial.X) * (1 + C 7 * Polynomial.X ^ 2)
    have hfT_map : fT = g1.map Quad7.emb := by
      simp [fT, g1, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_X, map_ofNat]
    rw [hfT_map, ← Polynomial.map_pow, Polynomial.coeff_map]
    congr 1
    have hg0_exp : g0 = Polynomial.X ^ 3 + C 21 * Polynomial.X ^ 2 + C 7 * Polynomial.X + C 147 := by
      have h147 : C (21 : ZMod p) * C 7 = C 147 := by rw [← map_mul]; norm_num
      simp only [g0]; linear_combination h147
    have hg1_exp : g1 = C 147 * Polynomial.X ^ 3 + C 7 * Polynomial.X ^ 2 + C 21 * Polynomial.X + 1 := by
      have h147 : C (21 : ZMod p) * C 7 = C 147 := by rw [← map_mul]; norm_num
      simp only [g1]; linear_combination Polynomial.X ^ 3 * h147
    have hdeg_g0 : g0.natDegree ≤ 3 := by rw [hg0_exp]; compute_degree!
    have hrev_g0 : revPoly 3 g0 = g1 := by
      ext k
      rw [revPoly_coeff, hg0_exp, hg1_exp]
      by_cases hk : k ≤ 3
      · rw [if_pos hk]
        interval_cases k <;> simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_one]
      · rw [if_neg hk]
        simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one,
          show k ≠ 3 by omega, show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
    have hrev_pow := revPoly_pow 3 g0 hdeg_g0 m
    rw [hrev_g0] at hrev_pow
    rw [← hrev_pow, revPoly_coeff, if_pos (by omega), show m * 3 - m = p - 1 by omega]
  obtain ⟨W, W_inv, lam, hW_mul, h_endo, hlam_m_ne_one⟩ := endo_exists hp h5 hleg
  set V : PowerSeries K := PowerSeries.X * W
  set V' : PowerSeries K := PowerSeries.derivative K V
  have hpow := congrArg (fun S => V' * W_inv ^ p * S ^ m) h_endo
  have hpow_re :
      V' * W_inv ^ p * V ^ m * Polynomial.aeval V (fT ^ m) =
      PowerSeries.C (lam ^ m) * (PowerSeries.X ^ m * (V' * W_inv) ^ p * Polynomial.aeval PowerSeries.X (fT ^ m)) := by
    have h2m1 : 2 * m + 1 = p := by omega
    rw [map_pow (Polynomial.aeval V) fT m, map_pow (Polynomial.aeval PowerSeries.X) fT m]
    calc V' * W_inv ^ p * V ^ m * (Polynomial.aeval V fT) ^ m
        = V' * W_inv ^ p * (V * Polynomial.aeval V fT) ^ m := by
            rw [mul_pow V (Polynomial.aeval V fT) m]; ring
      _ = V' * W_inv ^ p * (PowerSeries.C lam * PowerSeries.X * V' ^ 2 * Polynomial.aeval PowerSeries.X fT) ^ m := hpow
      _ = PowerSeries.C lam ^ m * (PowerSeries.X ^ m * (V' ^ (2 * m + 1) * W_inv ^ p) *
            (Polynomial.aeval PowerSeries.X fT) ^ m) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
      _ = PowerSeries.C (lam ^ m) * (PowerSeries.X ^ m * (V' * W_inv) ^ p *
            (Polynomial.aeval PowerSeries.X fT) ^ m) := by
          rw [map_pow, h2m1, ← mul_pow]
  have hV'_W : V' * W_inv = 1 + PowerSeries.X * (PowerSeries.derivative K W * W_inv) := by
    have hdV : V' = W + PowerSeries.X * PowerSeries.derivative K W := by
      simp only [V', V, Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul, mul_one]
      ring
    rw [hdV, add_mul, hW_mul, mul_assoc]
  have hRHS_coeff :
      PowerSeries.coeff (p - 1)
        (PowerSeries.C (lam ^ m) * (PowerSeries.X ^ m * (V' * W_inv) ^ p * Polynomial.aeval PowerSeries.X (fT ^ m))) =
      lam ^ m * Quad7.emb Hp := by
    rw [PowerSeries.coeff_C_mul, hV'_W, powerSeries_coeff_pow_p_shift hp h5]
    have haeval_X : PowerSeries.coeff m (Polynomial.aeval PowerSeries.X (fT ^ m)) = (fT ^ m).coeff m := by
      rw [Polynomial.aeval_eq_sum_range]
      simp only [Algebra.smul_def, PowerSeries.algebraMap_eq, map_sum, PowerSeries.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · symm; apply Polynomial.coeff_eq_zero_of_natDegree_lt; rw [Finset.mem_range] at h; omega
    rw [haeval_X, hHp_eq]
  have hdeg_fTm : (fT ^ m).natDegree ≤ 3 * m := by
    have hdeg_fT : fT.natDegree ≤ 3 := by
      have h147 : C (21 : K) * C 7 = C 147 := by rw [← map_mul]; norm_num
      have : fT = C (147 : K) * Polynomial.X ^ 3 + C (7 : K) * Polynomial.X ^ 2 +
          C (21 : K) * Polynomial.X + 1 := by simp only [fT]; linear_combination Polynomial.X ^ 3 * h147
      rw [this]; compute_degree!
    calc (fT ^ m).natDegree ≤ m * fT.natDegree := Polynomial.natDegree_pow_le
      _ ≤ m * 3 := Nat.mul_le_mul_left m hdeg_fT
      _ = 3 * m := by ring
  have hLHS_coeff :
      PowerSeries.coeff (p - 1) (V' * W_inv ^ p * V ^ m * Polynomial.aeval V (fT ^ m)) = Quad7.emb Hp := by
    have haeval_sum : Polynomial.aeval V (fT ^ m) =
        ∑ k ∈ Finset.range (3 * m + 1), PowerSeries.C ((fT ^ m).coeff k) * V ^ k := by
      rw [Polynomial.aeval_eq_sum_range' (n := 3 * m + 1) (by omega)]
      simp only [Algebra.smul_def, PowerSeries.algebraMap_eq]
    rw [haeval_sum, Finset.mul_sum, map_sum]
    rw [Finset.sum_eq_single m]
    · have hterm_m : V' * W_inv ^ p * V ^ m * (PowerSeries.C ((fT ^ m).coeff m) * V ^ m) =
          PowerSeries.C ((fT ^ m).coeff m) * (PowerSeries.X ^ (p - 1) * (V' * W_inv)) := by
        have hVpow : V ^ m * V ^ m = PowerSeries.X ^ (p - 1) * W ^ (p - 1) := by
          rw [← pow_add, show m + m = p - 1 by omega, mul_pow PowerSeries.X W (p - 1)]
        have hWpow : W_inv ^ p * W ^ (p - 1) = W_inv := by
          have h1 : W_inv ^ p = W_inv ^ (p - 1) * W_inv := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega)]
          have h2 : W_inv ^ (p - 1) * W ^ (p - 1) = 1 := by
            rw [← mul_pow, mul_comm, hW_mul, one_pow]
          calc W_inv ^ p * W ^ (p - 1) = (W_inv ^ (p - 1) * W_inv) * W ^ (p - 1) := by rw [h1]
            _ = (W_inv ^ (p - 1) * W ^ (p - 1)) * W_inv := by ring
            _ = W_inv := by rw [h2, one_mul]
        calc V' * W_inv ^ p * V ^ m * (PowerSeries.C ((fT ^ m).coeff m) * V ^ m)
            = PowerSeries.C ((fT ^ m).coeff m) * (V' * W_inv ^ p * (V ^ m * V ^ m)) := by ring
          _ = PowerSeries.C ((fT ^ m).coeff m) * (PowerSeries.X ^ (p - 1) * (V' * (W_inv ^ p * W ^ (p - 1)))) := by
                rw [hVpow]; ring
          _ = PowerSeries.C ((fT ^ m).coeff m) * (PowerSeries.X ^ (p - 1) * (V' * W_inv)) := by rw [hWpow]
      rw [hterm_m, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
      rw [hV'_W]
      simp [hHp_eq]
    · intro k hk hne
      rw [Finset.mem_range] at hk
      rw [show V' * W_inv ^ p * V ^ m * (PowerSeries.C ((fT ^ m).coeff k) * V ^ k) =
            PowerSeries.C ((fT ^ m).coeff k) * (V' * W_inv ^ p * V ^ (m + k)) by rw [pow_add]; ring,
          PowerSeries.coeff_C_mul]
      suffices hz : PowerSeries.coeff (p - 1) (V' * W_inv ^ p * V ^ (m + k)) = 0 by rw [hz, mul_zero]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · set r := m - k
        have hr1 : 1 ≤ r := by omega
        have hrp : r < p := by omega
        have hr_ne : (r : K) ≠ 0 := by
          intro h0
          have hdvd := (CharP.cast_eq_zero_iff K p r).mp h0
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have hkey := powerSeries_key_deriv_ident W W_inv V V' hW_mul rfl rfl p m k r (by omega) (by omega) hr1
        have hc0 : PowerSeries.coeff (p - 1) ((r : PowerSeries K) * (V' * W_inv ^ p * V ^ (m + k))) = 0 := by
          rw [hkey, map_neg, powerSeries_deriv_residue_zero r hr1 hrp (W_inv ^ r), neg_zero]
        rw [← map_natCast (PowerSeries.C (R := K)) r, PowerSeries.coeff_C_mul] at hc0
        exact (Quad7.mul_eq_zero_iff hp h5 hleg hc0).resolve_left hr_ne
      · have hmk : p ≤ m + k := by omega
        have hdiv : V' * W_inv ^ p * V ^ (m + k) =
            PowerSeries.X ^ p * (V' * W_inv ^ p * PowerSeries.X ^ (m + k - p) * W ^ (m + k)) := by
          have hVpow : V ^ (m + k) = PowerSeries.X ^ (m + k) * W ^ (m + k) := mul_pow PowerSeries.X W (m + k)
          have hXpow : (PowerSeries.X : PowerSeries K) ^ (m + k) = PowerSeries.X ^ p * PowerSeries.X ^ (m + k - p) := by
            rw [← pow_add]; congr 1; omega
          rw [hVpow, hXpow]; ring
        rw [hdiv, PowerSeries.coeff_X_pow_mul']
        exact if_neg (by omega)
    · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
  have hmul0 : (1 - lam ^ m) * Quad7.emb Hp = 0 := by
    have := congrArg (PowerSeries.coeff (p - 1)) hpow_re
    rw [hLHS_coeff, hRHS_coeff] at this
    linear_combination this
  have hHp_emb : Quad7.emb Hp = 0 :=
    (Quad7.mul_eq_zero_iff hp h5 hleg hmul0).resolve_left (sub_ne_zero.mpr hlam_m_ne_one.symm)
  exact congrArg Quad7.re hHp_emb

end OMA_A79727_P2


-- Part 3: Proof that p^2 ∣ A_0 = ∑_{k=0}^m C(2k, k)^3 from H_p = 0!
-- Uses pure ℤ[t] 3rd-order ODE for P_m(1 + 2t)^2 = ∑ C(m+k, 2k) C(2k, k)^2 (t(t+1))^k.


namespace OMA_A79727_P3

private structure Quad7 (R : Type*) where
  re : R
  im : R

private lemma Quad7.ext {R : Type*} {a b : Quad7 R} (h1 : a.re = b.re) (h2 : a.im = b.im) : a = b := by
  cases a; cases b; congr

private instance {R : Type*} [Zero R] : Zero (Quad7 R) := ⟨⟨0, 0⟩⟩
private instance {R : Type*} [One R] [Zero R] : One (Quad7 R) := ⟨⟨1, 0⟩⟩
private instance {R : Type*} [Add R] : Add (Quad7 R) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
private instance {R : Type*} [Neg R] : Neg (Quad7 R) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
private instance {R : Type*} [Sub R] : Sub (Quad7 R) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
private instance {R : Type*} [CommRing R] : Mul (Quad7 R) :=
  ⟨fun x y => ⟨x.re * y.re - 7 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
private instance {R : Type*} [NatCast R] [Zero R] : NatCast (Quad7 R) := ⟨fun n => ⟨n, 0⟩⟩
private instance {R : Type*} [IntCast R] [Zero R] : IntCast (Quad7 R) := ⟨fun z => ⟨z, 0⟩⟩

@[simp] private lemma Quad7.zero_re {R : Type*} [Zero R] : (0 : Quad7 R).re = 0 := rfl
@[simp] private lemma Quad7.zero_im {R : Type*} [Zero R] : (0 : Quad7 R).im = 0 := rfl
@[simp] private lemma Quad7.one_re {R : Type*} [One R] [Zero R] : (1 : Quad7 R).re = 1 := rfl
@[simp] private lemma Quad7.one_im {R : Type*} [One R] [Zero R] : (1 : Quad7 R).im = 0 := rfl
@[simp] private lemma Quad7.add_re {R : Type*} [Add R] (x y : Quad7 R) : (x + y).re = x.re + y.re := rfl
@[simp] private lemma Quad7.add_im {R : Type*} [Add R] (x y : Quad7 R) : (x + y).im = x.im + y.im := rfl
@[simp] private lemma Quad7.neg_re {R : Type*} [Neg R] (x : Quad7 R) : (-x).re = -x.re := rfl
@[simp] private lemma Quad7.neg_im {R : Type*} [Neg R] (x : Quad7 R) : (-x).im = -x.im := rfl
@[simp] private lemma Quad7.sub_re {R : Type*} [Sub R] (x y : Quad7 R) : (x - y).re = x.re - y.re := rfl
@[simp] private lemma Quad7.sub_im {R : Type*} [Sub R] (x y : Quad7 R) : (x - y).im = x.im - y.im := rfl
@[simp] private lemma Quad7.mul_re {R : Type*} [CommRing R] (x y : Quad7 R) :
    (x * y).re = x.re * y.re - 7 * x.im * y.im := rfl
@[simp] private lemma Quad7.mul_im {R : Type*} [CommRing R] (x y : Quad7 R) :
    (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] private lemma Quad7.natCast_re {R : Type*} [NatCast R] [Zero R] (n : ℕ) : (n : Quad7 R).re = n := rfl
@[simp] private lemma Quad7.natCast_im {R : Type*} [NatCast R] [Zero R] (n : ℕ) : (n : Quad7 R).im = 0 := rfl
@[simp] private lemma Quad7.intCast_re {R : Type*} [IntCast R] [Zero R] (z : ℤ) : (z : Quad7 R).re = z := rfl
@[simp] private lemma Quad7.intCast_im {R : Type*} [IntCast R] [Zero R] (z : ℤ) : (z : Quad7 R).im = 0 := rfl

private instance {R : Type*} [CommRing R] : CommRing (Quad7 R) where
  add_assoc a b c := by apply Quad7.ext <;> simp [add_assoc]
  zero_add a := by apply Quad7.ext <;> simp
  add_zero a := by apply Quad7.ext <;> simp
  add_comm a b := by apply Quad7.ext <;> simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply Quad7.ext <;> simp
  sub_eq_add_neg a b := by apply Quad7.ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by apply Quad7.ext <;> simp <;> ring
  one_mul a := by apply Quad7.ext <;> simp
  mul_one a := by apply Quad7.ext <;> simp
  left_distrib a b c := by apply Quad7.ext <;> simp <;> ring
  right_distrib a b c := by apply Quad7.ext <;> simp <;> ring
  zero_mul a := by apply Quad7.ext <;> simp
  mul_zero a := by apply Quad7.ext <;> simp
  mul_comm a b := by apply Quad7.ext <;> simp <;> ring
  natCast_zero := by apply Quad7.ext <;> simp
  natCast_succ n := by apply Quad7.ext <;> simp
  intCast_ofNat n := by apply Quad7.ext <;> simp
  intCast_negSucc n := by apply Quad7.ext <;> simp [Int.cast_negSucc]

@[simp] private lemma Quad7.ofNat_re {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Quad7 R).re = OfNat.ofNat n := rfl
@[simp] private lemma Quad7.ofNat_im {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Quad7 R).im = 0 := rfl

private def Quad7.emb {R : Type*} [CommRing R] : R →+* Quad7 R where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_mul' a b := by apply Quad7.ext <;> simp
  map_zero' := rfl
  map_add' a b := by apply Quad7.ext <;> simp

private def Quad7.w {R : Type*} [CommRing R] : Quad7 R := ⟨0, 1⟩

private def Quad7.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Quad7 R →+* Quad7 S where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by apply Quad7.ext <;> simp
  map_mul' a b := by apply Quad7.ext <;> simp [map_mul, map_sub, map_add, map_ofNat]
  map_zero' := by apply Quad7.ext <;> simp
  map_add' a b := by apply Quad7.ext <;> simp [map_add]

-- Step 3A: Sum of polynomial values over ZMod p equals -coeff (p - 1) for deg < 2(p - 1).
private lemma sum_pow_zmod_p {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : k < 2 * (p - 1)) :
    ∑ x : ZMod p, x ^ k = if k = p - 1 then (-1 : ZMod p) else 0 := by
  have hp : p.Prime := Fact.out
  by_cases hk0 : k = 0
  · subst hk0
    have hne : (0 : ℕ) ≠ p - 1 := by have := hp.two_le; omega
    simp [hne]
  · have hsum_ne0 : ∑ x : ZMod p, x ^ k = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), zero_pow hk0, add_zero]
    rw [hsum_ne0]
    by_cases hkm : k = p - 1
    · subst hkm
      rw [if_pos rfl]
      have h1 : ∀ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ (p - 1) = 1 := by
        intro x hx
        exact ZMod.pow_card_sub_one_eq_one (Finset.mem_erase.mp hx).1
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one,
        Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
    · rw [if_neg hkm]
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
      have hgk : (g : ZMod p) ^ k ≠ 1 := by
        intro h1
        have hu : g ^ k = 1 := Units.ext (by simpa using h1)
        have hord : orderOf g = p - 1 := by
          rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
        have hdvd : p - 1 ∣ k := hord ▸ orderOf_dvd_of_pow_eq_one hu
        rcases hdvd with ⟨q, hq⟩
        have hq0 : q ≠ 0 := fun h => hk0 (by simp [hq, h])
        have hq1 : q ≠ 1 := fun h => hkm (by simp [hq, h])
        have : 2 ≤ q := by omega
        have : 2 * (p - 1) ≤ k := by nlinarith
        omega
      have hmul : (g : ZMod p) ^ k * ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k =
          ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun x _ => (g : ZMod p) * x) ?_ ?_ ?_ ?_
        · intro x hx
          rw [Finset.mem_erase] at hx ⊢
          exact ⟨mul_ne_zero g.ne_zero hx.1, Finset.mem_univ _⟩
        · intro a _ b _ hab
          exact mul_left_cancel₀ g.ne_zero hab
        · intro y hy
          rw [Finset.mem_erase] at hy
          refine ⟨(g⁻¹ : (ZMod p)ˣ) * y, Finset.mem_erase.mpr ⟨mul_ne_zero g⁻¹.ne_zero hy.1, Finset.mem_univ _⟩, ?_⟩
          calc (g : ZMod p) * ((g⁻¹ : (ZMod p)ˣ) * y)
              = ((g : ZMod p) * (g⁻¹ : (ZMod p)ˣ)) * y := by ring
            _ = y := by rw [Units.mul_inv, one_mul]
        · intro x _; rw [mul_pow]
      have hzero : ((g : ZMod p) ^ k - 1) * ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k = 0 := by
        linear_combination hmul
      exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hgk)

private lemma sum_eval_poly_eq_neg_coeff {p : ℕ} [Fact p.Prime]
    (g : Polynomial (ZMod p)) (hdeg : g.natDegree < 2 * (p - 1)) :
    ∑ x : ZMod p, g.eval x = -g.coeff (p - 1) := by
  have hp : p.Prime := Fact.out
  have h1 : ∀ x : ZMod p, g.eval x = ∑ k ∈ Finset.range (2 * (p - 1)), g.coeff k * x ^ k := by
    intro x
    rw [Polynomial.eval_eq_sum_range' hdeg]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ k ∈ Finset.range (2 * (p - 1)),
      ∑ x : ZMod p, g.coeff k * x ^ k =
        if k = p - 1 then -g.coeff (p - 1) else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← Finset.mul_sum, sum_pow_zmod_p k hk]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq']
  have hmem : p - 1 ∈ Finset.range (2 * (p - 1)) := by
    rw [Finset.mem_range]; have := hp.two_le; omega
  rw [if_pos hmem]

-- Step 3B: 2-isogeny bijection on ZMod p:
-- ∑ x, (x * (x^2 + 42*x - 7))^m = 2^m * ∑ s, ((s + 21) * (s^2 + 7))^m
private lemma two_isogeny_sum_eq {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1) :
    ∑ x : ZMod p, (x * (x ^ 2 + 42 * x - 7)) ^ ((p - 1) / 2) =
      (2 : ZMod p) ^ ((p - 1) / 2) * ∑ s : ZMod p, ((s + 21) * (s ^ 2 + 7)) ^ ((p - 1) / 2) := by
  have hp : p.Prime := Fact.out
  set m := (p - 1) / 2
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  have hm_pos : 0 < m := by omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd; omega
  have h7ne : (7 : ZMod p) ≠ 0 := by
    intro h0
    have h70 : (-7 : ZMod p) = 0 := by linear_combination -h0
    rw [h70, zero_pow (by omega)] at hleg
    exact zero_ne_one (by linear_combination -hleg)
  -- For any t : ZMod p, number of x ≠ 0 with x - 7 * x⁻¹ = t is 1 + (t^2 + 28)^m!
  -- Because x^2 - t*x - 7 = 0 <=> (2*x - t)^2 = t^2 + 28!
  -- And for x ≠ 0 with x - 7*x⁻¹ = t:
  --   x * (x^2 + 42*x - 7) = x^2 * (x - 7*x⁻¹ + 42) = x^2 * (t + 42)
  --   so (x * (x^2 + 42*x - 7))^m = (x^2)^m * (t + 42)^m = (t + 42)^m (since x^(p-1) = 1)!
  -- Sum over x ≠ 0 grouped by t = x - 7*x⁻¹:
  --   = ∑ t : ZMod p, (1 + (t^2 + 28)^m) * (t + 42)^m
  --   Wait: when t^2 + 28 = 0, there is 1 root (x = t/2), and 1 + 0^m = 1!
  --   When t^2 + 28 is a nonzero square, there are 2 roots, and 1 + 1 = 2!
  --   When t^2 + 28 is a nonsquare, there are 0 roots, and 1 + (-1) = 0!
  --   And ∑ t, (t + 42)^m = 0 (since m < p - 1), so ONLY ∑ t, ((t + 42) * (t^2 + 28))^m survives!
  --   Substitute t = 2*s: ((2*s + 42)*(4*s^2 + 28))^m = 8^m * ((s + 21)*(s^2 + 7))^m = 2^m * (4^m) * ...
  --   WAIT: 4^m = 2^(2m) = 2^(p-1) = 1! So 8^m = 2^m!!
  have hLHS_ne0 : ∑ x : ZMod p, (x * (x ^ 2 + 42 * x - 7)) ^ m =
      ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, (x - 7 * x⁻¹ + 42) ^ m := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), zero_mul, zero_pow (by omega), add_zero]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have hfac : x * (x ^ 2 + 42 * x - 7) = x ^ 2 * (x - 7 * x⁻¹ + 42) := by
      field_simp [hx0]; ring
    rw [hfac, mul_pow, ← pow_mul, h2m, ZMod.pow_card_sub_one_eq_one hx0, one_mul]
  rw [hLHS_ne0]
  -- Group by fiber t = x - 7 * x⁻¹
  have hfiber : ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, (x - 7 * x⁻¹ + 42) ^ m =
      ∑ t : ZMod p,
        (((Finset.univ : Finset (ZMod p)).erase 0).filter (fun x => x - 7 * x⁻¹ = t)).card *
          (t + 42) ^ m := by
    have h1 := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (ZMod p)).erase 0)
      (t := (Finset.univ : Finset (ZMod p)))
      (g := fun x => x - 7 * x⁻¹) (f := fun x => (x - 7 * x⁻¹ + 42) ^ m)
      (fun _ _ => Finset.mem_univ _)
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hfiber]
  -- Count roots of x - 7*x⁻¹ = t for each t: equals (1 + (t^2 + 28)^m) in ZMod p!
  have hcard : ∀ t : ZMod p,
      ((((Finset.univ : Finset (ZMod p)).erase 0).filter (fun x => x - 7 * x⁻¹ = t)).card : ZMod p) =
        1 + (t ^ 2 + 28) ^ m := by
    intro t
    set D : ZMod p := t ^ 2 + 28
    -- Bijection between {x ≠ 0 | x - 7*x⁻¹ = t} and {y : ZMod p | y^2 = D} via y = 2*x - t!
    have hbij : (((Finset.univ : Finset (ZMod p)).erase 0).filter (fun x => x - 7 * x⁻¹ = t)).card =
        ((Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = D)).card := by
      refine Finset.card_bij (fun x _ => 2 * x - t) ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_filter, Finset.mem_erase] at hx
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hmul : x * (x - 7 * x⁻¹) = x * t := congrArg (x * ·) hx.2
        have hx2 : x ^ 2 - 7 = x * t := by
          have : x * (x - 7 * x⁻¹) = x ^ 2 - 7 := by field_simp [hx.1.1]
          rw [← this, hmul]
        calc (2 * x - t) ^ 2 = 4 * (x ^ 2 - t * x) + t ^ 2 := by ring
          _ = 4 * 7 + t ^ 2 := by linear_combination 4 * hx2
          _ = D := by simp [D]; ring
      · intro a _ b _ hab
        have h2ab : 2 * (a - b) = 0 := by linear_combination hab
        exact sub_eq_zero.mp ((mul_eq_zero.mp h2ab).resolve_left h2ne)
      · intro y hy
        rw [Finset.mem_filter] at hy
        set x := (y + t) * (2 : ZMod p)⁻¹
        have h2x : 2 * x = y + t := by
          simp only [x]; rw [mul_comm, mul_assoc, inv_mul_cancel₀ h2ne, mul_one]
        have hx2 : x ^ 2 - t * x = 7 := by
          have h4 : 4 * (x ^ 2 - t * x) = 28 := by
            calc 4 * (x ^ 2 - t * x) = (2 * x - t) ^ 2 - t ^ 2 := by ring
              _ = y ^ 2 - t ^ 2 := by rw [h2x]; ring
              _ = (t ^ 2 + 28) - t ^ 2 := by rw [hy.2]
              _ = 28 := by ring
          have h4ne : (4 : ZMod p) ≠ 0 := by
            have : (4 : ZMod p) = 2 * 2 := by norm_num
            rw [this]; exact mul_ne_zero h2ne h2ne
          exact mul_left_cancel₀ h4ne (by linear_combination h4)
        have hx0 : x ≠ 0 := by
          intro hz; rw [hz] at hx2; simp at hx2; exact h7ne hx2.symm
        refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ _⟩, ?_⟩, ?_⟩
        · field_simp [hx0]; linear_combination hx2
        · rw [h2x]; ring
    rw [hbij]
    -- Now compute card {y : ZMod p | y^2 = D} in ZMod p!
    by_cases hD0 : D = 0
    · rw [hD0, zero_pow (by omega), add_zero]
      have hset : (Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = 0) = {0} := by
        ext y; simp [sq_eq_zero_iff]
      rw [hset, Finset.card_singleton, Nat.cast_one]
    · by_cases hsq : ∃ r : ZMod p, r ^ 2 = D
      · rcases hsq with ⟨r, hr⟩
        have hr0 : r ≠ 0 := fun hz => hD0 (by rw [← hr, hz, zero_pow two_ne_zero])
        have hrne : r ≠ -r := by
          intro h
          have h2r : 2 * r = 0 := by linear_combination h
          exact hr0 ((mul_eq_zero.mp h2r).resolve_left h2ne)
        have hset : (Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = D) = {r, -r} := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
          rw [← hr, sq_eq_sq_iff_eq_or_eq_neg]
        rw [hset, Finset.card_pair hrne, Nat.cast_ofNat]
        rw [← hr, ← pow_mul, h2m, ZMod.pow_card_sub_one_eq_one hr0]
        norm_num
      · have hset : (Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = D) = ∅ := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hy; exact hsq ⟨y, hy⟩
        rw [hset, Finset.card_empty, Nat.cast_zero]
        -- Since D ≠ 0 and D is not a square, D^m = -1!
        have hDm2 : (D ^ m) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, h2m, ZMod.pow_card_sub_one_eq_one hD0]
        have hDm_pm : D ^ m = 1 ∨ D ^ m = -1 := sq_eq_one_iff.mp hDm2
        rcases hDm_pm with h1 | hm1
        · exfalso
          -- If D^m = 1, then D is a square in (ZMod p)ˣ (cyclic of order 2m)!
          obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
          set uD : (ZMod p)ˣ := Units.mk0 D hD0
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg uD)
          have hord : orderOf g = 2 * m := by
            rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units, h2m]
          have hgkm : g ^ (k * (m : ℤ)) = 1 := by
            rw [zpow_mul, hk]
            exact Units.ext (by simpa [uD] using h1)
          have hdvd : (2 * m : ℤ) ∣ k * m := by
            have := orderOf_dvd_iff_zpow_eq_one.mpr hgkm
            rw [hord] at this
            simpa using this
          have h2dvd : (2 : ℤ) ∣ k := by
            rcases hdvd with ⟨q, hq⟩
            refine ⟨q, ?_⟩
            have hm_ne : (m : ℤ) ≠ 0 := by omega
            exact mul_right_cancel₀ hm_ne (by linarith)
          rcases h2dvd with ⟨j, rfl⟩
          apply hsq
          refine ⟨((g ^ j : (ZMod p)ˣ) : ZMod p), ?_⟩
          have : (g ^ j) ^ 2 = uD := by rw [← hk, ← zpow_natCast, ← zpow_mul]; congr 1; ring
          simpa [uD] using congrArg Units.val this
        · rw [hm1]; ring
  rw [Finset.sum_congr rfl fun t _ => by rw [hcard t]]
  have hsum_add : ∑ t : ZMod p, (1 + (t ^ 2 + 28) ^ m) * (t + 42) ^ m =
      (∑ t : ZMod p, (t + 42) ^ m) + ∑ t : ZMod p, (t ^ 2 + 28) ^ m * (t + 42) ^ m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => by ring
  rw [hsum_add]
  -- First sum ∑ t, (t + 42)^m = 0 since deg = m < p - 1
  have hsum1 : ∑ t : ZMod p, (t + 42) ^ m = 0 := by
    have hev : ∀ t : ZMod p, (t + 42) ^ m = ((Polynomial.X + C (42 : ZMod p)) ^ m).eval t := by
      intro t; simp
    simp_rw [hev]
    have hdeg : ((Polynomial.X + C (42 : ZMod p)) ^ m).natDegree < 2 * (p - 1) := by
      calc ((Polynomial.X + C (42 : ZMod p)) ^ m).natDegree
          ≤ m * (Polynomial.X + C (42 : ZMod p)).natDegree := Polynomial.natDegree_pow_le
        _ ≤ m * 1 := by gcongr; compute_degree!
        _ < 2 * (p - 1) := by omega
    rw [sum_eval_poly_eq_neg_coeff _ hdeg]
    have hlt : ((Polynomial.X + C (42 : ZMod p)) ^ m).natDegree < p - 1 := by
      calc ((Polynomial.X + C (42 : ZMod p)) ^ m).natDegree
          ≤ m * (Polynomial.X + C (42 : ZMod p)).natDegree := Polynomial.natDegree_pow_le
        _ ≤ m * 1 := by gcongr; compute_degree!
        _ < p - 1 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, neg_zero]
  rw [hsum1, zero_add]
  -- Reindex t = 2 * s:
  have hbij2 : ∑ t : ZMod p, (t ^ 2 + 28) ^ m * (t + 42) ^ m =
      ∑ s : ZMod p, ((2 * s) ^ 2 + 28) ^ m * (2 * s + 42) ^ m :=
    (Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2ne) (fun t => (t ^ 2 + 28) ^ m * (t + 42) ^ m)).symm
  rw [hbij2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h4m : (4 : ZMod p) ^ m = 1 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num, ← pow_mul, h2m, ZMod.pow_card_sub_one_eq_one h2ne]
  calc ((2 * s) ^ 2 + 28) ^ m * (2 * s + 42) ^ m
      = (4 * (s ^ 2 + 7)) ^ m * (2 * (s + 21)) ^ m := by congr 1 <;> congr 1 <;> ring
    _ = 4 ^ m * (s ^ 2 + 7) ^ m * (2 ^ m * (s + 21) ^ m) := by rw [mul_pow, mul_pow]
    _ = 2 ^ m * ((s + 21) ^ m * (s ^ 2 + 7) ^ m) := by rw [h4m]; ring
    _ = 2 ^ m * ((s + 21) * (s ^ 2 + 7)) ^ m := by rw [mul_pow]

-- Step 3C: From H_p = 0, deduce P_m(3w) = 0 in Quad7 (ZMod p),
-- where P_m(X) = ∑_{k=0}^m C(m, k) C(m+k, k) ((X - 1)/2)^k!
private noncomputable def legPoly (m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (m + 1), C ((Nat.choose m k * Nat.choose (m + k) k : ℕ) : ℤ) * Polynomial.X ^ k

private noncomputable def legSqR (m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (m + 1), C ((Nat.choose (m + k) (2 * k) * (Nat.choose (2 * k) k) ^ 2 : ℕ) : ℤ) * Polynomial.X ^ k

private lemma eval_legPoly_3w_eq_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1)
    (hHp : (((Polynomial.X + C 21) * (Polynomial.X ^ 2 + C 7) : Polynomial (ZMod p)) ^ ((p - 1) / 2)).coeff (p - 1) = 0) :
    (legPoly ((p - 1) / 2)).eval₂ (Int.castRingHom (Quad7 (ZMod p)))
      ((3 * (Quad7.w : Quad7 (ZMod p)) - 1) * Quad7.emb (2 : ZMod p)⁻¹) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set m := (p - 1) / 2
  have h2m : 2 * m = p - 1 := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd; omega
  have h7ne : (7 : ZMod p) ≠ 0 := by
    intro h0
    have h70 : (-7 : ZMod p) = 0 := by linear_combination -h0
    rw [h70, zero_pow (by omega)] at hleg
    exact zero_ne_one (by linear_combination -hleg)
  -- 1. Show [(x^2 + 42*x - 7)^m] coeff m = 0 in ZMod p
  have hcoeff_m : ((Polynomial.X ^ 2 + C (42 : ZMod p) * Polynomial.X - C 7) ^ m).coeff m = 0 := by
    set g : Polynomial (ZMod p) := (Polynomial.X * (Polynomial.X ^ 2 + C 42 * Polynomial.X - C 7)) ^ m
    set f : Polynomial (ZMod p) := ((Polynomial.X + C 21) * (Polynomial.X ^ 2 + C 7)) ^ m
    have hdeg_g : g.natDegree < 2 * (p - 1) := by
      have hd : (Polynomial.X * (Polynomial.X ^ 2 + C (42 : ZMod p) * Polynomial.X - C 7)).natDegree ≤ 3 := by
        have : Polynomial.X * (Polynomial.X ^ 2 + C (42 : ZMod p) * Polynomial.X - C 7) =
            Polynomial.X ^ 3 + C 42 * Polynomial.X ^ 2 - C 7 * Polynomial.X := by ring
        rw [this]; compute_degree!
      calc g.natDegree ≤ m * (Polynomial.X * (Polynomial.X ^ 2 + C (42 : ZMod p) * Polynomial.X - C 7)).natDegree :=
            Polynomial.natDegree_pow_le
        _ ≤ m * 3 := Nat.mul_le_mul_left m hd
        _ < 2 * (p - 1) := by omega
    have hdeg_f : f.natDegree < 2 * (p - 1) := by
      have hd : ((Polynomial.X + C (21 : ZMod p)) * (Polynomial.X ^ 2 + C 7)).natDegree ≤ 3 := by
        have h147 : C (21 : ZMod p) * C 7 = C 147 := by rw [← map_mul]; norm_num
        have : (Polynomial.X + C (21 : ZMod p)) * (Polynomial.X ^ 2 + C 7) =
            Polynomial.X ^ 3 + C 21 * Polynomial.X ^ 2 + C 7 * Polynomial.X + C 147 := by
          linear_combination h147
        rw [this]; compute_degree!
      calc f.natDegree ≤ m * ((Polynomial.X + C (21 : ZMod p)) * (Polynomial.X ^ 2 + C 7)).natDegree :=
            Polynomial.natDegree_pow_le
        _ ≤ m * 3 := Nat.mul_le_mul_left m hd
        _ < 2 * (p - 1) := by omega
    have hsg := sum_eval_poly_eq_neg_coeff g hdeg_g
    have hsf := sum_eval_poly_eq_neg_coeff f hdeg_f
    have hiso := two_isogeny_sum_eq h5 hleg
    have hg_ev : ∑ x : ZMod p, g.eval x = ∑ x : ZMod p, (x * (x ^ 2 + 42 * x - 7)) ^ m := by
      refine Finset.sum_congr rfl fun x _ => by simp [g]
    have hf_ev : ∑ s : ZMod p, f.eval s = ∑ s : ZMod p, ((s + 21) * (s ^ 2 + 7)) ^ m := by
      refine Finset.sum_congr rfl fun s _ => by simp [f]
    rw [← hg_ev, ← hf_ev, hsg, hsf] at hiso
    have hg0 : g.coeff (p - 1) = 0 := by
      rw [hHp, neg_zero, mul_zero] at hiso
      exact neg_eq_zero.mp hiso
    have hg_eq : g = Polynomial.X ^ m * (Polynomial.X ^ 2 + C 42 * Polynomial.X - C 7) ^ m := by
      simp only [g, mul_pow]
    rw [hg_eq, Polynomial.coeff_X_pow_mul'] at hg0
    rw [if_pos (by omega), show p - 1 - m = m by omega] at hg0
    exact hg0
  -- 2. Substitute X = w * U in Quad7 (ZMod p)[U]:
  --    (wU)^2 + 42*(wU) - 7 = -7 * (U^2 - 6*w*U + 1)
  set K := Quad7 (ZMod p)
  set w : K := Quad7.w
  have hw2 : w ^ 2 = -7 := by apply Quad7.ext <;> simp [K, w, Quad7.w, sq]
  have hcoeff_u : ((1 - C (6 * w) * Polynomial.X + Polynomial.X ^ 2 : Polynomial K) ^ m).coeff m = 0 := by
    have hmap : ((Polynomial.X ^ 2 + C (42 : ZMod p) * Polynomial.X - C 7 : Polynomial (ZMod p)) ^ m).map Quad7.emb =
        (Polynomial.X ^ 2 + C (42 : K) * Polynomial.X - C 7) ^ m := by
      simp [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, map_ofNat]
    have hcomp : ((Polynomial.X ^ 2 + C (42 : K) * Polynomial.X - C 7) ^ m).comp (C w * Polynomial.X) =
        C ((-7 : K) ^ m) * (1 - C (6 * w) * Polynomial.X + Polynomial.X ^ 2) ^ m := by
      rw [Polynomial.pow_comp]
      have h1 : (Polynomial.X ^ 2 + C (42 : K) * Polynomial.X - C 7).comp (C w * Polynomial.X) =
          C (-7 : K) * (1 - C (6 * w) * Polynomial.X + Polynomial.X ^ 2) := by
        simp only [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
          Polynomial.C_comp, Polynomial.X_comp]
        rw [mul_pow, ← map_pow, hw2]
        have h42 : C (42 : K) * C w = C (-7 : K) * (-C (6 * w)) := by
          rw [← map_neg, ← map_mul, ← map_mul]; congr 1; ring
        have hC7 : C (-7 : K) = -C (7 : K) := map_neg C (7 : K)
        linear_combination Polynomial.X * h42 - hC7
      rw [h1, mul_pow, map_pow]
    have hcm_comp : (((Polynomial.X ^ 2 + C (42 : K) * Polynomial.X - C 7) ^ m).comp (C w * Polynomial.X)).coeff m =
        w ^ m * ((Polynomial.X ^ 2 + C (42 : K) * Polynomial.X - C 7) ^ m).coeff m := by
      set Q : Polynomial K := (Polynomial.X ^ 2 + C (42 : K) * Polynomial.X - C 7) ^ m
      rw [Polynomial.comp_C_mul_X_coeff]
      ring
    have hQ0 : ((Polynomial.X ^ 2 + C (42 : K) * Polynomial.X - C 7) ^ m).coeff m = 0 := by
      rw [← hmap, Polynomial.coeff_map, hcoeff_m, map_zero]
    have hprod0 : (-7 : K) ^ m * ((1 - C (6 * w) * Polynomial.X + Polynomial.X ^ 2 : Polynomial K) ^ m).coeff m = 0 := by
      have h := congrArg (fun P => P.coeff m) hcomp
      rw [hcm_comp, hQ0, mul_zero, Polynomial.coeff_C_mul] at h
      exact h.symm
    have hm7 : (-7 : K) ^ m = -1 := by
      have : (-7 : K) = Quad7.emb (-7 : ZMod p) := by apply Quad7.ext <;> simp [K, Quad7.emb]
      rw [this, ← map_pow, hleg]
      apply Quad7.ext <;> simp [K, Quad7.emb]
    rw [hm7, neg_one_mul, neg_eq_zero] at hprod0
    exact hprod0
  -- 3. Binomial expansion of (1 - 6*w*X + X^2)^m = ((1 - X)^2 - 4 * t * X)^m where t = (3*w - 1) * 2⁻¹!
  set t : K := (3 * w - 1) * Quad7.emb (2 : ZMod p)⁻¹
  have h4t : 4 * t = 6 * w - 2 := by
    have h2inv : (2 : K) * Quad7.emb (2 : ZMod p)⁻¹ = 1 := by
      have : (2 : K) = Quad7.emb (2 : ZMod p) := rfl
      rw [this, ← map_mul, mul_inv_cancel₀ h2ne, map_one]
    calc 4 * t = (6 * w - 2) * ((2 : K) * Quad7.emb (2 : ZMod p)⁻¹) := by simp only [t]; ring
      _ = 6 * w - 2 := by rw [h2inv, mul_one]
  have hbin : (1 - C (6 * w) * Polynomial.X + Polynomial.X ^ 2 : Polynomial K) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        C ((Nat.choose m k : K) * (-4 * t) ^ k) * (Polynomial.X ^ k * (1 - Polynomial.X) ^ (2 * (m - k))) := by
    have hrew : (1 - C (6 * w) * Polynomial.X + Polynomial.X ^ 2 : Polynomial K) =
        (C (-4 * t) * Polynomial.X) + (1 - Polynomial.X) ^ 2 := by
      have hC4t : C (4 * t) = C (6 * w - 2) := congrArg C h4t
      rw [map_sub, map_ofNat] at hC4t
      have : C (-4 * t) = -C (4 * t) := by rw [neg_mul, map_neg]
      rw [this, hC4t]; ring
    rw [hrew, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm 2]
    have : C ((Nat.choose m k : K)) = (Nat.choose m k : Polynomial K) := by rw [map_natCast]
    rw [map_mul, this]; ring
  -- Extract coeff m of hbin:
  have hcoeff_bin :
      ((1 - C (6 * w) * Polynomial.X + Polynomial.X ^ 2 : Polynomial K) ^ m).coeff m =
      ∑ k ∈ Finset.range (m + 1),
        (Nat.choose m k : K) * (-4 * t) ^ k * ((-1 : K) ^ (m - k) * (Nat.choose (2 * (m - k)) (m - k) : K)) := by
    rw [hbin, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', if_pos (by omega)]
    congr 1
    -- coeff (m - k) of (1 - X)^(2*(m - k)) = (-1)^(m - k) * C(2*(m - k), m - k)
    set d := m - k
    have h1x : (1 - Polynomial.X : Polynomial K) ^ (2 * d) =
        ∑ j ∈ Finset.range (2 * d + 1), C ((-1 : K) ^ j * (Nat.choose (2 * d) j : K)) * Polynomial.X ^ j := by
      rw [sub_eq_add_neg, add_comm, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_pow, mul_one, show (-Polynomial.X : Polynomial K) = C (-1 : K) * Polynomial.X by simp,
        mul_pow, ← map_pow, map_mul, map_natCast]
      ring
    rw [h1x, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]
  have hcong : ∀ k ≤ m,
      ((-4 : ZMod p) ^ k * (-1 : ZMod p) ^ (m - k) * (Nat.choose (2 * (m - k)) (m - k) : ZMod p)) =
        (Nat.choose (m + k) k : ZMod p) := by
    intro k hk
    induction k with
    | zero =>
      simp only [pow_zero, one_mul, Nat.sub_zero, add_zero, Nat.choose_zero_right, Nat.cast_one]
      have hcp : ∀ j ≤ p - 1, (Nat.choose (p - 1) j : ZMod p) = (-1 : ZMod p) ^ j := by
        intro j hj
        induction j with
        | zero => simp
        | succ j ih =>
          have hcast : ((j + 1 : ℕ) : ZMod p) * (Nat.choose (p - 1) (j + 1) : ZMod p) =
              ((p - 1 - j : ℕ) : ZMod p) * (Nat.choose (p - 1) j : ZMod p) := by
            have h1 : (j + 1) * Nat.choose (p - 1) (j + 1) = (p - 1 - j) * Nat.choose (p - 1) j := by
              have h2 := Nat.choose_succ_right_eq (p - 1) j
              linarith
            rw [← Nat.cast_mul, h1, Nat.cast_mul]
          have hpj : ((p - 1 - j : ℕ) : ZMod p) = -((j + 1 : ℕ) : ZMod p) := by
            have hle : j + 1 ≤ p := by omega
            rw [show p - 1 - j = p - (j + 1) by omega, Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
          rw [hpj, ih (by omega)] at hcast
          have hjne : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
            intro h0
            have hdvd := (ZMod.natCast_eq_zero_iff (j + 1) p).mp h0
            have := Nat.le_of_dvd (by omega) hdvd; omega
          apply mul_left_cancel₀ hjne
          rw [hcast, pow_succ]; ring
      rw [h2m, hcp m (by omega), ← mul_pow]
      norm_num
    | succ k ih =>
      set d := m - (k + 1)
      have hd1 : m - k = d + 1 := by omega
      have hA : (d + 1) * Nat.choose (2 * (d + 1)) (d + 1) = 2 * (2 * d + 1) * Nat.choose (2 * d) d := by
        have hc1 := Nat.choose_mul_factorial_mul_factorial (show d + 1 ≤ 2 * d + 2 by omega)
        have hc0 := Nat.choose_mul_factorial_mul_factorial (show d ≤ 2 * d by omega)
        rw [show 2 * d + 2 - (d + 1) = d + 1 by omega] at hc1
        rw [show 2 * d - d = d by omega] at hc0
        rw [show 2 * (d + 1) = 2 * d + 2 by omega]
        apply Nat.mul_right_cancel (mul_pos (Nat.factorial_pos (d + 1)) (Nat.factorial_pos d))
        have hf2 : (2 * d + 2).factorial = (2 * d + 2) * (2 * d + 1) * (2 * d).factorial := by
          rw [show 2 * d + 2 = (2 * d + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
        have hfd : (d + 1).factorial = (d + 1) * d.factorial := Nat.factorial_succ d
        calc (d + 1) * Nat.choose (2 * d + 2) (d + 1) * ((d + 1).factorial * d.factorial)
            = Nat.choose (2 * d + 2) (d + 1) * (d + 1).factorial * (d + 1).factorial := by rw [hfd]; ring
          _ = (2 * d + 2).factorial := hc1
          _ = (2 * d + 2) * (2 * d + 1) * (Nat.choose (2 * d) d * d.factorial * d.factorial) := by rw [hf2, ← hc0]
          _ = 2 * (2 * d + 1) * Nat.choose (2 * d) d * ((d + 1).factorial * d.factorial) := by rw [hfd]; ring
      have hB : (k + 1) * Nat.choose (m + (k + 1)) (k + 1) = (m + k + 1) * Nat.choose (m + k) k := by
        rw [show m + (k + 1) = m + k + 1 by omega]
        have := Nat.add_one_mul_choose_eq (m + k) k; linarith
      have hAc : ((d + 1 : ℕ) : ZMod p) * (Nat.choose (2 * (d + 1)) (d + 1) : ZMod p) =
          2 * ((2 * d + 1 : ℕ) : ZMod p) * (Nat.choose (2 * d) d : ZMod p) := by
        have := congrArg (fun n : ℕ => (n : ZMod p)) hA
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using this
      have hBc : ((k + 1 : ℕ) : ZMod p) * (Nat.choose (m + (k + 1)) (k + 1) : ZMod p) =
          ((m + k + 1 : ℕ) : ZMod p) * (Nat.choose (m + k) k : ZMod p) := by
        have := congrArg (fun n : ℕ => (n : ZMod p)) hB
        simpa only [Nat.cast_mul] using this
      have hrel_mod : 2 * ((2 * d + 1 : ℕ) : ZMod p) * ((m + k + 1 : ℕ) : ZMod p) =
          4 * ((d + 1 : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p) := by
        have h2m1 : (2 * (m : ZMod p) + 1) = 0 := by
          have h1 : ((2 * m + 1 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) := congrArg Nat.cast (by omega)
          rw [ZMod.natCast_self] at h1
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h1
        have hd_cast : ((d : ℕ) : ZMod p) = (m : ZMod p) - (k : ZMod p) - 1 := by
          have h1 : d + (k + 1) = m := by omega
          have h2 := congrArg (fun n : ℕ => (n : ZMod p)) h1
          push_cast at h2; linear_combination h2
        push_cast
        rw [hd_cast]
        linear_combination (2 * (m : ZMod p) - 2 * (k : ZMod p) - 2) * h2m1
      have hne_fac : (2 : ZMod p) * ((2 * d + 1 : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
        apply mul_ne_zero (mul_ne_zero h2ne ?_) ?_
        · intro h0; have hdvd := (ZMod.natCast_eq_zero_iff (2 * d + 1) p).mp h0
          have := Nat.le_of_dvd (by omega) hdvd; omega
        · intro h0; have hdvd := (ZMod.natCast_eq_zero_iff (k + 1) p).mp h0
          have := Nat.le_of_dvd (by omega) hdvd; omega
      apply mul_left_cancel₀ hne_fac
      have ih' := ih (by omega)
      rw [hd1, pow_succ (-1 : ZMod p)] at ih'
      rw [pow_succ (-4 : ZMod p)]
      calc (2 : ZMod p) * ((2 * d + 1 : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p) *
            ((-4 : ZMod p) ^ k * (-4) * (-1 : ZMod p) ^ d * (Nat.choose (2 * d) d : ZMod p))
          = 4 * ((k + 1 : ℕ) : ZMod p) * (-4 : ZMod p) ^ k * ((-1 : ZMod p) ^ d * (-1)) *
              (2 * ((2 * d + 1 : ℕ) : ZMod p) * (Nat.choose (2 * d) d : ZMod p)) := by ring
        _ = 4 * ((d + 1 : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p) *
              ((-4 : ZMod p) ^ k * ((-1 : ZMod p) ^ d * (-1)) * (Nat.choose (2 * (d + 1)) (d + 1) : ZMod p)) := by
              rw [← hAc]; ring
        _ = 4 * ((d + 1 : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p) * (Nat.choose (m + k) k : ZMod p) := by rw [ih']
        _ = 2 * ((2 * d + 1 : ℕ) : ZMod p) * (((m + k + 1 : ℕ) : ZMod p) * (Nat.choose (m + k) k : ZMod p)) := by
              rw [← hrel_mod]; ring
        _ = 2 * ((2 * d + 1 : ℕ) : ZMod p) *
              (((k + 1 : ℕ) : ZMod p) * (Nat.choose (m + (k + 1)) (k + 1) : ZMod p)) := by rw [← hBc]
        _ = 2 * ((2 * d + 1 : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p) * (Nat.choose (m + (k + 1)) (k + 1) : ZMod p) := by ring
  -- Combine hcoeff_u, hcoeff_bin, hcong to get eval₂ (legPoly m) t = 0!
  rw [← hcoeff_u, hcoeff_bin]
  simp only [legPoly, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hck := congrArg Quad7.emb (hcong k (by omega))
  simp only [map_mul, map_pow, map_neg, map_natCast, map_one, map_ofNat] at hck
  have hint_c : (Int.castRingHom K) ((Nat.choose m k * Nat.choose (m + k) k : ℕ) : ℤ) =
      (Nat.choose m k : K) * (Nat.choose (m + k) k : K) := by
    rw [map_natCast, Nat.cast_mul]
  rw [hint_c]
  calc (Nat.choose m k : K) * (Nat.choose (m + k) k : K) * t ^ k
      = (Nat.choose m k : K) * ((-4 : K) ^ k * (-1 : K) ^ (m - k) * (Nat.choose (2 * (m - k)) (m - k) : K)) * t ^ k := by
          rw [← hck]
    _ = (Nat.choose m k : K) * (-4 * t) ^ k * ((-1 : K) ^ (m - k) * (Nat.choose (2 * (m - k)) (m - k) : K)) := by
          rw [mul_pow (-4 : K) t k]; ring

-- Step 3D: Pure ℤ[t] 3rd-order ODE proving legPoly(m)^2 = (legSqR m).comp (X * (X + 1))!
private noncomputable def Mt (m : ℕ) (Q : Polynomial ℤ) : Polynomial ℤ :=
  let t := (Polynomial.X : Polynomial ℤ)
  let Q1 := Polynomial.derivative Q
  let Q2 := Polynomial.derivative Q1
  let Q3 := Polynomial.derivative Q2
  let M : Polynomial ℤ := C ((m * (m + 1) : ℕ) : ℤ)
  t ^ 2 * (t + 1) ^ 2 * Q3 +
    3 * t * (t + 1) * (2 * t + 1) * Q2 +
    (6 * t ^ 2 + 6 * t + 1 - 4 * M * t * (t + 1)) * Q1 -
    2 * M * (2 * t + 1) * Q

private lemma Mt_unique_zero (m : ℕ) (D : Polynomial ℤ) (h0 : D.coeff 0 = 0) (hM : Mt m D = 0) :
    D = 0 := by
  by_contra hne
  set r := D.natTrailingDegree
  have hr_ne : D.coeff r ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hne
  have hr_pos : 1 ≤ r := by
    by_contra hlt
    have hr0 : r = 0 := by omega
    rw [hr0] at hr_ne
    exact hr_ne h0
  have hlt_zero : ∀ j < r, D.coeff j = 0 := fun j hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
  have hc := congrArg (fun P => P.coeff (r - 1)) hM
  rw [Polynomial.coeff_zero] at hc
  -- Compute (Mt m D).coeff (r - 1) = (r : ℤ)^3 * D.coeff r!
  have hterm : (Mt m D).coeff (r - 1) = (r : ℤ) ^ 3 * D.coeff r := by
    have hD1 : (Polynomial.derivative D).coeff (r - 1) = (r : ℤ) * D.coeff r := by
      rw [Polynomial.coeff_derivative, show r - 1 + 1 = r by omega, Nat.cast_sub hr_pos, Nat.cast_one]
      ring
    have hD_lt : ∀ j < r, D.coeff j = 0 := hlt_zero
    have hD1_lt : ∀ j < r - 1, (Polynomial.derivative D).coeff j = 0 := by
      intro j hj; rw [Polynomial.coeff_derivative, hD_lt (j + 1) (by omega), zero_mul]
    have hD2_lt : ∀ j < r - 2, (Polynomial.derivative (Polynomial.derivative D)).coeff j = 0 := by
      intro j hj; rw [Polynomial.coeff_derivative, hD1_lt (j + 1) (by omega), zero_mul]
    have hMt_exp : Mt m D =
        (Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4) *
          Polynomial.derivative (Polynomial.derivative (Polynomial.derivative D)) +
        (3 * Polynomial.X + 9 * Polynomial.X ^ 2 + 6 * Polynomial.X ^ 3) *
          Polynomial.derivative (Polynomial.derivative D) +
        (1 + C (6 - 4 * ((m * (m + 1) : ℕ) : ℤ)) * Polynomial.X +
          C (6 - 4 * ((m * (m + 1) : ℕ) : ℤ)) * Polynomial.X ^ 2) * Polynomial.derivative D -
        (C (2 * ((m * (m + 1) : ℕ) : ℤ)) + C (4 * ((m * (m + 1) : ℕ) : ℤ)) * Polynomial.X) * D := by
      simp only [Mt, map_sub, map_mul, map_ofNat]
      ring
    rw [hMt_exp]
    simp only [add_mul, mul_assoc, one_mul, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_ofNat_mul]
    have hX4 : (Polynomial.X ^ 4 * Polynomial.derivative (Polynomial.derivative (Polynomial.derivative D))).coeff (r - 1) = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · rw [Polynomial.coeff_derivative, hD2_lt (r - 1 - 4 + 1) (by omega), zero_mul]
      · rfl
    have hX3_3 : (Polynomial.X ^ 3 * Polynomial.derivative (Polynomial.derivative (Polynomial.derivative D))).coeff (r - 1) = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · rw [Polynomial.coeff_derivative, hD2_lt (r - 1 - 3 + 1) (by omega), zero_mul]
      · rfl
    have hX2_3 : (Polynomial.X ^ 2 * Polynomial.derivative (Polynomial.derivative (Polynomial.derivative D))).coeff (r - 1) =
        ((r : ℤ) * (r - 1) * (r - 2)) * D.coeff r := by
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
        rw [show r - 1 - 2 + 1 + 1 + 1 = r by omega,
            show r - 1 - 2 + 1 + 1 = r - 1 by omega,
            show r - 1 - 2 + 1 = r - 2 by omega,
            show r - 1 - 2 = r - 3 by omega]
        simp only [Nat.cast_sub (by omega : 3 ≤ r), Nat.cast_sub (by omega : 2 ≤ r),
          Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_ofNat, Nat.cast_one]
        ring
      · have : r = 1 ∨ r = 2 := by omega
        rcases this with hr1 | hr2
        · rw [hr1]; norm_num
        · rw [hr2]; norm_num
    have hX3_2 : (Polynomial.X ^ 3 * Polynomial.derivative (Polynomial.derivative D)).coeff (r - 1) = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · exact hD2_lt (r - 1 - 3) (by omega)
      · rfl
    have hX2_2 : (Polynomial.X ^ 2 * Polynomial.derivative (Polynomial.derivative D)).coeff (r - 1) = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · exact hD2_lt (r - 1 - 2) (by omega)
      · rfl
    have hX1_2 : (Polynomial.X * Polynomial.derivative (Polynomial.derivative D)).coeff (r - 1) =
        ((r : ℤ) * (r - 1)) * D.coeff r := by
      rw [show Polynomial.X * Polynomial.derivative (Polynomial.derivative D) =
        Polynomial.X ^ 1 * Polynomial.derivative (Polynomial.derivative D) by rw [pow_one],
        Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative,
            show r - 1 - 1 + 1 + 1 = r by omega,
            show r - 1 - 1 + 1 = r - 1 by omega,
            show r - 1 - 1 = r - 2 by omega]
        simp only [Nat.cast_sub (by omega : 2 ≤ r), Nat.cast_sub (by omega : 1 ≤ r),
          Nat.cast_ofNat, Nat.cast_one]
        ring
      · have hr1 : r = 1 := by omega
        rw [hr1]; norm_num
    have hX2_1 : (Polynomial.X ^ 2 * Polynomial.derivative D).coeff (r - 1) = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · exact hD1_lt (r - 1 - 2) (by omega)
      · rfl
    have hX1_1 : (Polynomial.X * Polynomial.derivative D).coeff (r - 1) = 0 := by
      rw [show Polynomial.X * Polynomial.derivative D = Polynomial.X ^ 1 * Polynomial.derivative D by rw [pow_one],
        Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · exact hD1_lt (r - 1 - 1) (by omega)
      · rfl
    have hX1_0 : (Polynomial.X * D).coeff (r - 1) = 0 := by
      rw [show Polynomial.X * D = Polynomial.X ^ 1 * D by rw [pow_one], Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · exact hD_lt (r - 1 - 1) (by omega)
      · rfl
    have hX0_0 : D.coeff (r - 1) = 0 := hD_lt (r - 1) (by omega)
    rw [hX4, hX3_3, hX2_3, hX3_2, hX2_2, hX1_2, hX2_1, hX1_1, hD1, hX1_0, hX0_0]
    ring
  rw [hterm] at hc
  have hr3 : (r : ℤ) ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  exact hr_ne ((mul_eq_zero.mp hc).resolve_left hr3)

private lemma legPoly_sq_eq_legSqR (m : ℕ) :
    (legPoly m) ^ 2 = (legSqR m).comp (Polynomial.X * (Polynomial.X + 1)) := by
  apply sub_eq_zero.mp
  apply Mt_unique_zero m
  · have hP0 : (legPoly m).coeff 0 = 1 := by
      simp [legPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    have hR0 : ((legSqR m).comp (Polynomial.X * (Polynomial.X + 1))).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, zero_mul,
        legSqR, Polynomial.eval_finsetSum, Polynomial.eval_C, Polynomial.eval_pow]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk0; rw [zero_pow hk0, mul_zero]
      · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    rw [Polynomial.coeff_sub, sq, Polynomial.mul_coeff_zero, hP0, hR0]; ring
  · have hMt_sub : ∀ A B : Polynomial ℤ, Mt m (A - B) = Mt m A - Mt m B := by
      intro A B; simp only [Mt, map_sub]; ring
    rw [hMt_sub]
    have hE_P : Polynomial.X * (Polynomial.X + 1) * Polynomial.derivative (Polynomial.derivative (legPoly m)) +
        (2 * Polynomial.X + 1) * Polynomial.derivative (legPoly m) -
        C ((m * (m + 1) : ℕ) : ℤ) * legPoly m = 0 := by
      ext k
      rw [Polynomial.coeff_zero]
      have hcP : ∀ j : ℕ, (legPoly m).coeff j =
          if j ≤ m then ((Nat.choose m j * Nat.choose (m + j) j : ℕ) : ℤ) else 0 := by
        intro j
        simp only [legPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_ite_eq]
        split_ifs with h1 h2
        · rfl
        · rw [Finset.mem_range] at h1; omega
        · rw [Finset.mem_range] at h1; omega
        · rfl
      have hLHS_k :
          (Polynomial.X * (Polynomial.X + 1) * Polynomial.derivative (Polynomial.derivative (legPoly m)) +
            (2 * Polynomial.X + 1) * Polynomial.derivative (legPoly m) -
            C ((m * (m + 1) : ℕ) : ℤ) * legPoly m).coeff k =
          ((k + 1 : ℤ) ^ 2) * (legPoly m).coeff (k + 1) +
            ((k : ℤ) * (k + 1) - ((m * (m + 1) : ℕ) : ℤ)) * (legPoly m).coeff k := by
        have hre : Polynomial.X * (Polynomial.X + 1) * Polynomial.derivative (Polynomial.derivative (legPoly m)) +
            (2 * Polynomial.X + 1) * Polynomial.derivative (legPoly m) -
            C ((m * (m + 1) : ℕ) : ℤ) * legPoly m =
            Polynomial.X ^ 2 * Polynomial.derivative (Polynomial.derivative (legPoly m)) +
            Polynomial.X * Polynomial.derivative (Polynomial.derivative (legPoly m)) +
            2 * (Polynomial.X * Polynomial.derivative (legPoly m)) +
            Polynomial.derivative (legPoly m) -
            C ((m * (m + 1) : ℕ) : ℤ) * legPoly m := by ring
        rw [hre]
        simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
          Polynomial.coeff_C_mul]
        cases k with
        | zero =>
          simp [Polynomial.coeff_derivative]; ring
        | succ k =>
          rw [show (Polynomial.X : Polynomial ℤ) * Polynomial.derivative (Polynomial.derivative (legPoly m)) =
                Polynomial.X ^ 1 * Polynomial.derivative (Polynomial.derivative (legPoly m)) by rw [pow_one],
              show (Polynomial.X : Polynomial ℤ) * Polynomial.derivative (legPoly m) =
                Polynomial.X ^ 1 * Polynomial.derivative (legPoly m) by rw [pow_one],
              Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
          rw [if_pos (by omega : 1 ≤ k + 1), if_pos (by omega : 1 ≤ k + 1)]
          split_ifs with h2
          · simp only [Polynomial.coeff_derivative, show k + 1 - 2 + 1 + 1 = k + 1 by omega,
              show k + 1 - 1 + 1 + 1 = k + 2 by omega, show k + 1 - 1 + 1 = k + 1 by omega]
            push_cast [show 1 ≤ k by omega]
            ring
          · have hk0 : k = 0 := by omega
            subst hk0
            simp only [Polynomial.coeff_derivative]
            push_cast
            ring
      rw [hLHS_k, hcP (k + 1), hcP k]
      by_cases hkm : k + 1 ≤ m
      · rw [if_pos hkm, if_pos (by omega)]
        have h1 : (k + 1) * Nat.choose m (k + 1) = (m - k) * Nat.choose m k := by
          have := Nat.choose_succ_right_eq m k; linarith
        have h2 : (k + 1) * Nat.choose (m + k + 1) (k + 1) = (m + k + 1) * Nat.choose (m + k) k := by
          have := Nat.add_one_mul_choose_eq (m + k) k; linarith
        have hnat : (k + 1) ^ 2 * (Nat.choose m (k + 1) * Nat.choose (m + (k + 1)) (k + 1)) =
            (m - k) * (m + k + 1) * (Nat.choose m k * Nat.choose (m + k) k) := by
          rw [show m + (k + 1) = m + k + 1 by omega]
          calc (k + 1) ^ 2 * (Nat.choose m (k + 1) * Nat.choose (m + k + 1) (k + 1))
              = ((k + 1) * Nat.choose m (k + 1)) * ((k + 1) * Nat.choose (m + k + 1) (k + 1)) := by ring
            _ = ((m - k) * Nat.choose m k) * ((m + k + 1) * Nat.choose (m + k) k) := by rw [h1, h2]
            _ = _ := by ring
        have hint : ((k + 1 : ℤ) ^ 2) * ((Nat.choose m (k + 1) * Nat.choose (m + (k + 1)) (k + 1) : ℕ) : ℤ) =
            ((m : ℤ) - k) * ((m : ℤ) + k + 1) * ((Nat.choose m k * Nat.choose (m + k) k : ℕ) : ℤ) := by
          have h0 := congrArg (fun n : ℕ => (n : ℤ)) hnat
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
            Nat.cast_sub (show k ≤ m by omega)] at h0 ⊢
          exact h0
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hint ⊢
        linear_combination hint
      · rw [if_neg hkm]
        by_cases hkeq : k = m
        · subst hkeq; rw [if_pos le_rfl]; push_cast; ring
        · rw [if_neg (by omega)]; ring
    have hMt_P2 : Mt m ((legPoly m) ^ 2) = 0 := by
      set P := legPoly m
      have hdE := congrArg Polynomial.derivative hE_P
      rw [map_zero] at hdE
      simp only [Mt, sq, Polynomial.derivative_mul, Polynomial.derivative_add,
        Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X,
        Polynomial.derivative_one, Polynomial.derivative_ofNat] at hdE ⊢
      linear_combination
        (2 * Polynomial.X * (Polynomial.X + 1) * P) * hdE +
        (6 * Polynomial.X * (Polynomial.X + 1) * Polynomial.derivative P + 2 * (2 * Polynomial.X + 1) * P) * hE_P
    have hLz_R :
        let R := legSqR m
        let R1 := Polynomial.derivative R
        let R2 := Polynomial.derivative R1
        let R3 := Polynomial.derivative R2
        let Z := (Polynomial.X : Polynomial ℤ)
        let M : Polynomial ℤ := C ((m * (m + 1) : ℕ) : ℤ)
        Z ^ 2 * (4 * Z + 1) * R3 + 3 * Z * (6 * Z + 1) * R2 + (12 * Z + 1 - 4 * M * Z) * R1 - 2 * M * R = 0 := by
      dsimp only
      ext k
      rw [Polynomial.coeff_zero]
      have hcR : ∀ j : ℕ, (legSqR m).coeff j =
          if j ≤ m then ((Nat.choose (m + j) (2 * j) * (Nat.choose (2 * j) j) ^ 2 : ℕ) : ℤ) else 0 := by
        intro j
        simp only [legSqR, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_ite_eq]
        split_ifs with h1 h2
        · rfl
        · rw [Finset.mem_range] at h1; omega
        · rw [Finset.mem_range] at h1; omega
        · rfl
      have hLHS_k :
          (Polynomial.X ^ 2 * (4 * Polynomial.X + 1) * Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (legSqR m))) +
            3 * Polynomial.X * (6 * Polynomial.X + 1) * Polynomial.derivative (Polynomial.derivative (legSqR m)) +
            (12 * Polynomial.X + 1 - 4 * C ((m * (m + 1) : ℕ) : ℤ) * Polynomial.X) * Polynomial.derivative (legSqR m) -
            2 * C ((m * (m + 1) : ℕ) : ℤ) * legSqR m).coeff k =
          ((k + 1 : ℤ) ^ 3) * (legSqR m).coeff (k + 1) +
            2 * (2 * (k : ℤ) + 1) * ((k : ℤ) * (k + 1) - ((m * (m + 1) : ℕ) : ℤ)) * (legSqR m).coeff k := by
        set R := legSqR m
        have hre :
            Polynomial.X ^ 2 * (4 * Polynomial.X + 1) * Polynomial.derivative (Polynomial.derivative (Polynomial.derivative R)) +
            3 * Polynomial.X * (6 * Polynomial.X + 1) * Polynomial.derivative (Polynomial.derivative R) +
            (12 * Polynomial.X + 1 - 4 * C ((m * (m + 1) : ℕ) : ℤ) * Polynomial.X) * Polynomial.derivative R -
            2 * C ((m * (m + 1) : ℕ) : ℤ) * R =
            4 * (Polynomial.X ^ 3 * Polynomial.derivative (Polynomial.derivative (Polynomial.derivative R))) +
            Polynomial.X ^ 2 * Polynomial.derivative (Polynomial.derivative (Polynomial.derivative R)) +
            18 * (Polynomial.X ^ 2 * Polynomial.derivative (Polynomial.derivative R)) +
            3 * (Polynomial.X * Polynomial.derivative (Polynomial.derivative R)) +
            C (12 - 4 * ((m * (m + 1) : ℕ) : ℤ)) * (Polynomial.X * Polynomial.derivative R) +
            Polynomial.derivative R -
            C (2 * ((m * (m + 1) : ℕ) : ℤ)) * R := by
          simp only [map_sub, map_mul, map_ofNat]; ring
        rw [hre]
        simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
          Polynomial.coeff_C_mul]
        cases k with
        | zero => simp [Polynomial.coeff_derivative]; ring
        | succ k =>
          rw [show Polynomial.X * Polynomial.derivative (Polynomial.derivative R) =
                Polynomial.X ^ 1 * Polynomial.derivative (Polynomial.derivative R) by rw [pow_one],
              show Polynomial.X * Polynomial.derivative R =
                Polynomial.X ^ 1 * Polynomial.derivative R by rw [pow_one],
              Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul',
              Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
          rw [if_pos (by omega : 1 ≤ k + 1), if_pos (by omega : 1 ≤ k + 1)]
          split_ifs with h3 h2
          · simp only [Polynomial.coeff_derivative,
              show k + 1 - 3 + 1 + 1 + 1 = k + 1 by omega,
              show k + 1 - 2 + 1 + 1 + 1 = k + 2 by omega,
              show k + 1 - 2 + 1 + 1 = k + 1 by omega,
              show k + 1 - 1 + 1 + 1 = k + 2 by omega,
              show k + 1 - 1 + 1 = k + 1 by omega]
            push_cast [show 2 ≤ k by omega, show 1 ≤ k by omega]
            ring
          · omega
          · have hk1 : k = 1 := by omega
            subst hk1; simp only [Polynomial.coeff_derivative]; push_cast; ring
          · have hk0 : k = 0 := by omega
            subst hk0; simp only [Polynomial.coeff_derivative]; push_cast; ring
      rw [hLHS_k, hcR (k + 1), hcR k]
      by_cases hkm : k + 1 ≤ m
      · rw [if_pos hkm, if_pos (by omega)]
        have hfac : (k + 1) ^ 3 * (Nat.choose (m + (k + 1)) (2 * (k + 1)) * (Nat.choose (2 * (k + 1)) (k + 1)) ^ 2) =
            2 * (2 * k + 1) * (m - k) * (m + k + 1) * (Nat.choose (m + k) (2 * k) * (Nat.choose (2 * k) k) ^ 2) := by
          have hA : (k + 1) * Nat.choose (2 * k + 2) (k + 1) = 2 * (2 * k + 1) * Nat.choose (2 * k) k := by
            have hc1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * k + 2 by omega)
            have hc0 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
            rw [show 2 * k + 2 - (k + 1) = k + 1 by omega] at hc1
            rw [show 2 * k - k = k by omega] at hc0
            have hpos : 0 < (k + 1).factorial * k.factorial := mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
            apply Nat.mul_right_cancel hpos
            have hf2 : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
              rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
            have hfk : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
            calc (k + 1) * Nat.choose (2 * k + 2) (k + 1) * ((k + 1).factorial * k.factorial)
                = Nat.choose (2 * k + 2) (k + 1) * (k + 1).factorial * (k + 1).factorial := by rw [hfk]; ring
              _ = (2 * k + 2).factorial := hc1
              _ = (2 * k + 2) * (2 * k + 1) * (Nat.choose (2 * k) k * k.factorial * k.factorial) := by rw [hf2, ← hc0]
              _ = 2 * (2 * k + 1) * Nat.choose (2 * k) k * ((k + 1).factorial * k.factorial) := by rw [hfk]; ring
          have hB : (2 * k + 2) * (2 * k + 1) * Nat.choose (m + k + 1) (2 * k + 2) =
              (m + k + 1) * (m - k) * Nat.choose (m + k) (2 * k) := by
            have hc1 := Nat.choose_mul_factorial_mul_factorial (show 2 * k + 2 ≤ m + k + 1 by omega)
            have hc0 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ m + k by omega)
            rw [show m + k + 1 - (2 * k + 2) = m - k - 1 by omega] at hc1
            rw [show m + k - 2 * k = m - k by omega] at hc0
            have hpos : 0 < (2 * k).factorial * (m - k - 1).factorial :=
              mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
            apply Nat.mul_right_cancel hpos
            have hf2k : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
              rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
            have hfmk : (m - k).factorial = (m - k) * (m - k - 1).factorial := by
              conv_lhs => rw [show m - k = (m - k - 1) + 1 by omega]
              rw [Nat.factorial_succ]; congr 1; omega
            have hfmk1 : (m + k + 1).factorial = (m + k + 1) * (m + k).factorial := Nat.factorial_succ _
            calc (2 * k + 2) * (2 * k + 1) * Nat.choose (m + k + 1) (2 * k + 2) * ((2 * k).factorial * (m - k - 1).factorial)
                = Nat.choose (m + k + 1) (2 * k + 2) * (2 * k + 2).factorial * (m - k - 1).factorial := by rw [hf2k]; ring
              _ = (m + k + 1).factorial := hc1
              _ = (m + k + 1) * (Nat.choose (m + k) (2 * k) * (2 * k).factorial * (m - k).factorial) := by rw [hfmk1, ← hc0]
              _ = (m + k + 1) * (m - k) * Nat.choose (m + k) (2 * k) * ((2 * k).factorial * (m - k - 1).factorial) := by
                    rw [hfmk]; ring
          rw [show m + (k + 1) = m + k + 1 by omega, show 2 * (k + 1) = 2 * k + 2 by omega]
          have hpos2 : 0 < 2 * (2 * k + 1) := by omega
          apply Nat.mul_left_cancel hpos2
          calc 2 * (2 * k + 1) * ((k + 1) ^ 3 * (Nat.choose (m + k + 1) (2 * k + 2) * Nat.choose (2 * k + 2) (k + 1) ^ 2))
              = ((2 * k + 2) * (2 * k + 1) * Nat.choose (m + k + 1) (2 * k + 2)) *
                ((k + 1) * Nat.choose (2 * k + 2) (k + 1)) ^ 2 := by ring
            _ = ((m + k + 1) * (m - k) * Nat.choose (m + k) (2 * k)) *
                (2 * (2 * k + 1) * Nat.choose (2 * k) k) ^ 2 := by rw [hB, hA]
            _ = 2 * (2 * k + 1) * (2 * (2 * k + 1) * (m - k) * (m + k + 1) *
                (Nat.choose (m + k) (2 * k) * Nat.choose (2 * k) k ^ 2)) := by ring
        have hint : ((k + 1 : ℤ) ^ 3) *
            ((Nat.choose (m + (k + 1)) (2 * (k + 1)) * (Nat.choose (2 * (k + 1)) (k + 1)) ^ 2 : ℕ) : ℤ) =
            2 * (2 * (k : ℤ) + 1) * ((m : ℤ) - k) * ((m : ℤ) + k + 1) *
            ((Nat.choose (m + k) (2 * k) * (Nat.choose (2 * k) k) ^ 2 : ℕ) : ℤ) := by
          have h0 := congrArg (fun n : ℕ => (n : ℤ)) hfac
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
            Nat.cast_sub (show k ≤ m by omega)] at h0 ⊢
          exact h0
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hint ⊢
        linear_combination hint
      · rw [if_neg hkm]
        by_cases hkeq : k = m
        · subst hkeq; rw [if_pos le_rfl]; push_cast; ring
        · rw [if_neg (by omega)]; ring
    have hMt_R : Mt m ((legSqR m).comp (Polynomial.X * (Polynomial.X + 1))) = 0 := by
      set R := legSqR m
      set Z : Polynomial ℤ := Polynomial.X * (Polynomial.X + 1)
      have hdZ : Polynomial.derivative Z = 2 * Polynomial.X + 1 := by
        simp only [Z, Polynomial.derivative_mul, Polynomial.derivative_add,
          Polynomial.derivative_X, Polynomial.derivative_one]
        ring
      have hdZ2 : Polynomial.derivative (2 * Polynomial.X + 1 : Polynomial ℤ) = 2 := by
        simp [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          Polynomial.derivative_X, Polynomial.derivative_one]
      have h1 : Polynomial.derivative (R.comp Z) = (2 * Polynomial.X + 1) * (Polynomial.derivative R).comp Z := by
        rw [Polynomial.derivative_comp, hdZ, mul_comm]
      have h2 : Polynomial.derivative (Polynomial.derivative (R.comp Z)) =
          2 * (Polynomial.derivative R).comp Z + (2 * Polynomial.X + 1) ^ 2 * (Polynomial.derivative (Polynomial.derivative R)).comp Z := by
        rw [h1, Polynomial.derivative_mul, hdZ2, Polynomial.derivative_comp, hdZ]; ring
      have h3 : Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (R.comp Z))) =
          6 * (2 * Polynomial.X + 1) * (Polynomial.derivative (Polynomial.derivative R)).comp Z +
          (2 * Polynomial.X + 1) ^ 3 * (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative R))).comp Z := by
        rw [h2, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_mul,
          Polynomial.derivative_ofNat, Polynomial.derivative_pow, hdZ2,
          Polynomial.derivative_comp, Polynomial.derivative_comp, hdZ]
        simp only [zero_mul, zero_add, Nat.cast_ofNat, pow_one, map_ofNat]
        ring
      have hcomp0 := congrArg (fun P => P.comp Z) hLz_R
      rw [Polynomial.zero_comp] at hcomp0
      simp only [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.ofNat_comp, Polynomial.one_comp, Polynomial.C_comp, Polynomial.X_comp] at hcomp0
      dsimp only [Mt]
      rw [h3, h2, h1]
      linear_combination (2 * Polynomial.X + 1) * hcomp0
    rw [hMt_P2, hMt_R, sub_self]

-- Step 3E: Elementary congruence C(m + k, 2k) * (-16)^k ≡ C(2k, k) (mod p^2) for k ≤ m!
private lemma choose_leg_cong_mod_p_sq {p k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hk : k ≤ (p - 1) / 2) :
    (Nat.choose ((p - 1) / 2 + k) (2 * k) : ZMod (p ^ 2)) * (-16 : ZMod (p ^ 2)) ^ k =
      (Nat.choose (2 * k) k : ZMod (p ^ 2)) := by
  set m := (p - 1) / 2
  have h2m : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  -- Prove by induction on k!
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    -- Step ratio:
    --   (2k+2)*(2k+1) * C(m+k+1, 2k+2) = (m+k+1)*(m-k) * C(m+k, 2k)
    --   (k+1) * C(2k+2, k+1) = 2*(2k+1) * C(2k, k)
    -- And 4 * (m + k + 1) * (m - k) = (2m + 1)^2 - (2k + 1)^2 = p^2 - (2k + 1)^2 ≡ -(2k + 1)^2 (mod p^2)!
    -- So in ZMod (p^2):
    --   (2k+2)*(2k+1) * C(m+k+1, 2k+2) * (-16)^(k+1)
    --   = (-4) * (4*(m+k+1)*(m-k)) * C(m+k, 2k) * (-16)^k
    --   = (-4) * (-(2k+1)^2) * C(2k, k)
    --   = 4 * (2k+1)^2 * C(2k, k)
    --   = 2*(2k+1) * (k+1) * C(2k+2, k+1)
    --   = (2k+2)*(2k+1) * C(2k+2, k+1)!
    -- Cancel the unit (2k+2)*(2k+1) in ZMod (p^2) since 2k+2 ≤ 2m < p!
    have hA : (k + 1) * Nat.choose (2 * k + 2) (k + 1) = 2 * (2 * k + 1) * Nat.choose (2 * k) k := by
      have hc1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * k + 2 by omega)
      have hc0 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
      rw [show 2 * k + 2 - (k + 1) = k + 1 by omega] at hc1
      rw [show 2 * k - k = k by omega] at hc0
      apply Nat.mul_right_cancel (mul_pos (Nat.factorial_pos (k + 1)) (Nat.factorial_pos k))
      have hf2 : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
      have hfk : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
      calc (k + 1) * Nat.choose (2 * k + 2) (k + 1) * ((k + 1).factorial * k.factorial)
          = Nat.choose (2 * k + 2) (k + 1) * (k + 1).factorial * (k + 1).factorial := by rw [hfk]; ring
        _ = (2 * k + 2).factorial := hc1
        _ = (2 * k + 2) * (2 * k + 1) * (Nat.choose (2 * k) k * k.factorial * k.factorial) := by rw [hf2, ← hc0]
        _ = 2 * (2 * k + 1) * Nat.choose (2 * k) k * ((k + 1).factorial * k.factorial) := by rw [hfk]; ring
    have hB : (2 * k + 2) * (2 * k + 1) * Nat.choose (m + k + 1) (2 * k + 2) =
        (m + k + 1) * (m - k) * Nat.choose (m + k) (2 * k) := by
      have hc1 := Nat.choose_mul_factorial_mul_factorial (show 2 * k + 2 ≤ m + k + 1 by omega)
      have hc0 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ m + k by omega)
      rw [show m + k + 1 - (2 * k + 2) = m - k - 1 by omega] at hc1
      rw [show m + k - 2 * k = m - k by omega] at hc0
      apply Nat.mul_right_cancel (mul_pos (Nat.factorial_pos (2 * k)) (Nat.factorial_pos (m - k - 1)))
      have hf2k : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
      have hfmk : (m - k).factorial = (m - k) * (m - k - 1).factorial := by
        conv_lhs => rw [show m - k = (m - k - 1) + 1 by omega]
        rw [Nat.factorial_succ]; congr 1; omega
      have hfmk1 : (m + k + 1).factorial = (m + k + 1) * (m + k).factorial := Nat.factorial_succ _
      calc (2 * k + 2) * (2 * k + 1) * Nat.choose (m + k + 1) (2 * k + 2) * ((2 * k).factorial * (m - k - 1).factorial)
          = Nat.choose (m + k + 1) (2 * k + 2) * (2 * k + 2).factorial * (m - k - 1).factorial := by rw [hf2k]; ring
        _ = (m + k + 1).factorial := hc1
        _ = (m + k + 1) * (Nat.choose (m + k) (2 * k) * (2 * k).factorial * (m - k).factorial) := by rw [hfmk1, ← hc0]
        _ = (m + k + 1) * (m - k) * Nat.choose (m + k) (2 * k) * ((2 * k).factorial * (m - k - 1).factorial) := by
              rw [hfmk]; ring
    have h4prod : (4 * ((m + k + 1 : ℕ) : ZMod (p ^ 2)) * ((m - k : ℕ) : ZMod (p ^ 2))) =
        -(((2 * k + 1 : ℕ) : ZMod (p ^ 2)) ^ 2) := by
      have hnat : 4 * (m + k + 1) * (m - k) + (2 * k + 1) ^ 2 = p ^ 2 := by
        have hle : k ≤ m := by omega
        zify [hle]
        have : (p : ℤ) = 2 * m + 1 := by omega
        rw [this]; ring
      have hc := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) hnat
      rw [ZMod.natCast_self] at hc
      push_cast at hc ⊢
      linear_combination hc
    have hunit : IsUnit (((2 * k + 2) * (2 * k + 1) : ℕ) : ZMod (p ^ 2)) := by
      rw [ZMod.isUnit_iff_coprime]
      have hc1 : Nat.Coprime (2 * k + 2) p :=
        (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
      have hc2 : Nat.Coprime (2 * k + 1) p :=
        (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
      exact (hc1.mul_left hc2).pow_right 2
    apply hunit.mul_left_cancel
    have hBc : (((2 * k + 2) * (2 * k + 1) : ℕ) : ZMod (p ^ 2)) * (Nat.choose (m + k + 1) (2 * k + 2) : ZMod (p ^ 2)) =
        ((m + k + 1 : ℕ) : ZMod (p ^ 2)) * ((m - k : ℕ) : ZMod (p ^ 2)) * (Nat.choose (m + k) (2 * k) : ZMod (p ^ 2)) := by
      have := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) hB
      simpa only [Nat.cast_mul] using this
    have hAc : ((k + 1 : ℕ) : ZMod (p ^ 2)) * (Nat.choose (2 * k + 2) (k + 1) : ZMod (p ^ 2)) =
        (2 : ZMod (p ^ 2)) * ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) * (Nat.choose (2 * k) k : ZMod (p ^ 2)) := by
      have := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) hA
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using this
    rw [show m + (k + 1) = m + k + 1 by omega, show 2 * (k + 1) = 2 * k + 2 by omega, pow_succ (-16 : ZMod (p ^ 2))]
    calc (((2 * k + 2) * (2 * k + 1) : ℕ) : ZMod (p ^ 2)) *
          ((Nat.choose (m + k + 1) (2 * k + 2) : ZMod (p ^ 2)) * ((-16 : ZMod (p ^ 2)) ^ k * (-16)))
        = ((((2 * k + 2) * (2 * k + 1) : ℕ) : ZMod (p ^ 2)) * (Nat.choose (m + k + 1) (2 * k + 2) : ZMod (p ^ 2))) *
            ((-16 : ZMod (p ^ 2)) ^ k * (-16)) := by ring
      _ = (-4 : ZMod (p ^ 2)) * (4 * ((m + k + 1 : ℕ) : ZMod (p ^ 2)) * ((m - k : ℕ) : ZMod (p ^ 2))) *
            ((Nat.choose (m + k) (2 * k) : ZMod (p ^ 2)) * (-16 : ZMod (p ^ 2)) ^ k) := by rw [hBc]; ring
      _ = 4 * ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) ^ 2 * (Nat.choose (2 * k) k : ZMod (p ^ 2)) := by
            rw [h4prod, ih']; ring
      _ = 2 * ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) *
            (2 * ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) * (Nat.choose (2 * k) k : ZMod (p ^ 2))) := by ring
      _ = 2 * ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) *
            (((k + 1 : ℕ) : ZMod (p ^ 2)) * (Nat.choose (2 * k + 2) (k + 1) : ZMod (p ^ 2))) := by rw [← hAc]
      _ = (((2 * k + 2) * (2 * k + 1) : ℕ) : ZMod (p ^ 2)) * (Nat.choose (2 * k + 2) (k + 1) : ZMod (p ^ 2)) := by
            push_cast; ring

-- Step 3F: Final theorem of Part 3: A_0 = 0 in ZMod (p^2)!
private lemma A0_eq_zero_zmod_p_sq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hleg : ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1)
    (hHp : (((Polynomial.X + C 21) * (Polynomial.X ^ 2 + C 7) : Polynomial (ZMod p)) ^ ((p - 1) / 2)).coeff (p - 1) = 0) :
    ∑ k ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3 = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  set m := (p - 1) / 2
  have h2u : (2 : ZMod (p ^ 2)) * (2 : ZMod (p ^ 2))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    change IsUnit ((2 : ℕ) : ZMod (p ^ 2))
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).symm.pow_right 2
  set t : Quad7 (ZMod (p ^ 2)) := (3 * (Quad7.w : Quad7 (ZMod (p ^ 2))) - 1) * Quad7.emb (2 : ZMod (p ^ 2))⁻¹
  set v : Quad7 (ZMod (p ^ 2)) := (legPoly m).eval₂ (Int.castRingHom (Quad7 (ZMod (p ^ 2)))) t
  -- 1. Project v to Quad7 (ZMod p): equals 0!
  set proj : Quad7 (ZMod (p ^ 2)) →+* Quad7 (ZMod p) := Quad7.map (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))
  have hproj_2inv : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) ((2 : ZMod (p ^ 2))⁻¹) = (2 : ZMod p)⁻¹ := by
    have : Fact p.Prime := ⟨hp⟩
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
      have := Nat.le_of_dvd (by decide) hdvd; omega
    have h1 := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) h2u
    simp only [map_mul, map_ofNat, map_one] at h1
    exact mul_left_cancel₀ h2ne (by rw [h1, mul_inv_cancel₀ h2ne])
  have hproj_t : proj t = (3 * (Quad7.w : Quad7 (ZMod p)) - 1) * Quad7.emb (2 : ZMod p)⁻¹ := by
    have hpw : proj Quad7.w = Quad7.w := by apply Quad7.ext <;> simp [proj, Quad7.map, Quad7.w]
    have hp2 : proj (Quad7.emb (2 : ZMod (p ^ 2))⁻¹) = Quad7.emb (2 : ZMod p)⁻¹ := by
      apply Quad7.ext
      · exact hproj_2inv
      · simp [proj, Quad7.map, Quad7.emb]
    simp only [t, map_mul, map_sub, map_ofNat, map_one, hpw, hp2]
  have hproj_v : proj v = 0 := by
    have h1 : proj v = (legPoly m).eval₂ (proj.comp (Int.castRingHom (Quad7 (ZMod (p ^ 2))))) (proj t) := by
      simp only [v, Polynomial.hom_eval₂]
    have h2 : proj.comp (Int.castRingHom (Quad7 (ZMod (p ^ 2)))) = Int.castRingHom (Quad7 (ZMod p)) :=
      RingHom.ext_int _ _
    rw [h1, h2, hproj_t]
    exact eval_legPoly_3w_eq_zero hp h5 hleg hHp
  -- 2. Since proj v = 0, both v.re and v.im are divisible by p, so v^2 = 0 in Quad7 (ZMod (p^2))!
  have hv_sq : v ^ 2 = 0 := by
    have hre0 : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) v.re = 0 := congrArg Quad7.re hproj_v
    have him0 : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) v.im = 0 := congrArg Quad7.im hproj_v
    have hdvd_re : p ∣ v.re.val := by
      rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_zmod_val v.re] at *
      simpa using hre0
    have hdvd_im : p ∣ v.im.val := by
      rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_zmod_val v.im] at *
      simpa using him0
    rcases hdvd_re with ⟨a, ha⟩
    rcases hdvd_im with ⟨b, hb⟩
    have hvre : v.re = (p : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) := by
      rw [← ZMod.natCast_zmod_val v.re, ha, Nat.cast_mul]
    have hvim : v.im = (p : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) := by
      rw [← ZMod.natCast_zmod_val v.im, hb, Nat.cast_mul]
    have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
      rw [← Nat.cast_mul, ← sq, ZMod.natCast_self]
    apply Quad7.ext
    · simp only [sq, Quad7.mul_re, Quad7.zero_re, hvre, hvim]
      linear_combination (a * a - 7 * b * b) * hp2
    · simp only [sq, Quad7.mul_im, Quad7.zero_im, hvre, hvim]
      linear_combination (2 * a * b) * hp2
  -- 3. Evaluate legPoly_sq_eq_legSqR at t:
  have ht_mul : t * (t + 1) = Quad7.emb (-16 : ZMod (p ^ 2)) := by
    have h2e : (2 : Quad7 (ZMod (p ^ 2))) * Quad7.emb (2 : ZMod (p ^ 2))⁻¹ = 1 := by
      apply Quad7.ext <;> simp [Quad7.emb, h2u]
    have hw2 : (Quad7.w : Quad7 (ZMod (p ^ 2))) ^ 2 = -7 := by apply Quad7.ext <;> simp [Quad7.w, sq]
    have h4t : 4 * (t * (t + 1)) = -64 := by
      have h2t : 2 * t = 3 * Quad7.w - 1 := by
        calc 2 * t = (3 * Quad7.w - 1) * ((2 : Quad7 (ZMod (p ^ 2))) * Quad7.emb (2 : ZMod (p ^ 2))⁻¹) := by
              simp only [t]; ring
          _ = 3 * Quad7.w - 1 := by rw [h2e, mul_one]
      calc 4 * (t * (t + 1)) = (2 * t) * (2 * t + 2) := by ring
        _ = (3 * Quad7.w - 1) * (3 * Quad7.w + 1) := by rw [h2t]; ring
        _ = 9 * (Quad7.w : Quad7 (ZMod (p ^ 2))) ^ 2 - 1 := by ring
        _ = -64 := by rw [hw2]; ring
    have h4u : (4 : Quad7 (ZMod (p ^ 2))) * (Quad7.emb (2 : ZMod (p ^ 2))⁻¹) ^ 2 = 1 := by
      calc (4 : Quad7 (ZMod (p ^ 2))) * (Quad7.emb (2 : ZMod (p ^ 2))⁻¹) ^ 2
          = ((2 : Quad7 (ZMod (p ^ 2))) * Quad7.emb (2 : ZMod (p ^ 2))⁻¹) ^ 2 := by ring
        _ = 1 := by rw [h2e, one_pow]
    calc t * (t + 1) = (4 * (Quad7.emb (2 : ZMod (p ^ 2))⁻¹) ^ 2) * (t * (t + 1)) := by rw [h4u, one_mul]
      _ = (Quad7.emb (2 : ZMod (p ^ 2))⁻¹) ^ 2 * (4 * (t * (t + 1))) := by ring
      _ = (Quad7.emb (2 : ZMod (p ^ 2))⁻¹) ^ 2 * (-64) := by rw [h4t]
      _ = -16 * (4 * (Quad7.emb (2 : ZMod (p ^ 2))⁻¹) ^ 2) := by ring
      _ = -16 := by rw [h4u, mul_one]
      _ = Quad7.emb (-16 : ZMod (p ^ 2)) := by apply Quad7.ext <;> simp [Quad7.emb]
  have heval_sq := congrArg (Polynomial.eval₂ (Int.castRingHom (Quad7 (ZMod (p ^ 2)))) t) (legPoly_sq_eq_legSqR m)
  rw [Polynomial.eval₂_pow, Polynomial.eval₂_comp] at heval_sq
  have hXt : (Polynomial.X * (Polynomial.X + 1)).eval₂ (Int.castRingHom (Quad7 (ZMod (p ^ 2)))) t = t * (t + 1) := by
    simp
  rw [hXt, ht_mul] at heval_sq
  have hR_zero : (legSqR m).eval₂ (Int.castRingHom (Quad7 (ZMod (p ^ 2)))) (Quad7.emb (-16 : ZMod (p ^ 2))) = 0 := by
    rw [← heval_sq]; exact hv_sq
  have hR_re := congrArg Quad7.re hR_zero
  simp only [legSqR, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow] at hR_re
  have hsum_re : (∑ k ∈ Finset.range (m + 1),
      (Int.castRingHom (Quad7 (ZMod (p ^ 2)))) ((Nat.choose (m + k) (2 * k) * (Nat.choose (2 * k) k) ^ 2 : ℕ) : ℤ) *
      (Quad7.emb (-16 : ZMod (p ^ 2))) ^ k).re =
      ∑ k ∈ Finset.range (m + 1),
        (Nat.choose (m + k) (2 * k) : ZMod (p ^ 2)) * (-16 : ZMod (p ^ 2)) ^ k *
        (Nat.choose (2 * k) k : ZMod (p ^ 2)) ^ 2 := by
    have hrew : ∀ k : ℕ,
        (Int.castRingHom (Quad7 (ZMod (p ^ 2)))) ((Nat.choose (m + k) (2 * k) * (Nat.choose (2 * k) k) ^ 2 : ℕ) : ℤ) *
        (Quad7.emb (-16 : ZMod (p ^ 2))) ^ k =
        Quad7.emb ((Nat.choose (m + k) (2 * k) : ZMod (p ^ 2)) * (-16 : ZMod (p ^ 2)) ^ k *
          (Nat.choose (2 * k) k : ZMod (p ^ 2)) ^ 2) := by
      intro k
      rw [map_natCast]
      simp only [map_mul, map_pow, map_natCast, Nat.cast_mul, Nat.cast_pow]
      ring
    simp_rw [hrew]
    rw [← map_sum]
    rfl
  rw [hsum_re, Quad7.zero_re] at hR_re
  rw [← hR_re]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [choose_leg_cong_mod_p_sq hp h5 (by omega)]
  ring

end OMA_A79727_P3


-- Part 4: Complete unified 2nd-order ODE -> 3rd-order ODE + Wronskian proof of
-- S_1 = 0, A_1 = 0, and S_2 * B_2 = 1 in ZMod p!


namespace OMA_A79727_P4

-- Theta operator θ(P) = X * P' on Polynomial R
private noncomputable def theta {R : Type*} [CommRing R] (P : Polynomial R) : Polynomial R :=
  Polynomial.X * Polynomial.derivative P

private lemma theta_add {R : Type*} [CommRing R] (P Q : Polynomial R) :
    theta (P + Q) = theta P + theta Q := by
  simp only [theta, map_add, mul_add]

private lemma theta_sub {R : Type*} [CommRing R] (P Q : Polynomial R) :
    theta (P - Q) = theta P - theta Q := by
  simp only [theta, map_sub, mul_sub]

private lemma theta_neg {R : Type*} [CommRing R] (P : Polynomial R) :
    theta (-P) = -theta P := by
  simp only [theta, map_neg, mul_neg]

private lemma theta_mul {R : Type*} [CommRing R] (P Q : Polynomial R) :
    theta (P * Q) = theta P * Q + P * theta Q := by
  simp only [theta, Polynomial.derivative_mul]; ring

private lemma theta_C_mul {R : Type*} [CommRing R] (c : R) (P : Polynomial R) :
    theta (C c * P) = C c * theta P := by
  simp only [theta, Polynomial.derivative_C_mul]; ring

private lemma theta_C {R : Type*} [CommRing R] (c : R) :
    theta (C c) = 0 := by
  simp only [theta, Polynomial.derivative_C, mul_zero]

private lemma theta_X {R : Type*} [CommRing R] :
    theta (Polynomial.X : Polynomial R) = Polynomial.X := by
  simp only [theta, Polynomial.derivative_X, mul_one]

private lemma theta_zero {R : Type*} [CommRing R] :
    theta (0 : Polynomial R) = 0 := by
  simpa using theta_C (0 : R)

private lemma theta_one {R : Type*} [CommRing R] :
    theta (1 : Polynomial R) = 0 := by
  simpa using theta_C (1 : R)

private lemma theta_ofNat {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    theta (OfNat.ofNat n : Polynomial R) = 0 := by
  have : (OfNat.ofNat n : Polynomial R) = C (OfNat.ofNat n : R) := rfl
  rw [this, theta_C]

private lemma theta_ofNat_mul {R : Type*} [CommRing R] (n : ℕ) [n.AtLeastTwo] (P : Polynomial R) :
    theta (OfNat.ofNat n * P) = OfNat.ofNat n * theta P := by
  have : (OfNat.ofNat n : Polynomial R) = C (OfNat.ofNat n : R) := rfl
  rw [this, theta_C_mul]

private lemma theta_coeff {R : Type*} [CommRing R] (P : Polynomial R) (k : ℕ) :
    (theta P).coeff k = (k : R) * P.coeff k := by
  cases k with
  | zero => simp [theta]
  | succ k =>
    simp only [theta, Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

private lemma theta_natDegree_le {R : Type*} [CommRing R] (P : Polynomial R) :
    (theta P).natDegree ≤ P.natDegree := by
  unfold theta
  by_cases h0 : Polynomial.derivative P = 0
  · simp [h0]
  · calc (Polynomial.X * Polynomial.derivative P).natDegree
        ≤ Polynomial.X.natDegree + (Polynomial.derivative P).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + (P.natDegree - 1) := by
          gcongr
          · exact Polynomial.natDegree_X_le
          · exact Polynomial.natDegree_derivative_le P
      _ ≤ P.natDegree := by
          have : 1 ≤ P.natDegree := by
            by_contra hlt
            have hdeg0 : P.natDegree = 0 := by omega
            have hP := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
            rw [hP, Polynomial.derivative_C] at h0
            exact h0 rfl
          omega

-- 3rd-order Picard-Fuchs operator L3(Y) = 8 θ^3 Y - X (8 θ^3 Y + 12 θ^2 Y + 6 θ Y + Y)
private noncomputable def L3 {R : Type*} [CommRing R] (Y : Polynomial R) : Polynomial R :=
  8 * theta (theta (theta Y)) -
    Polynomial.X * (8 * theta (theta (theta Y)) + 12 * theta (theta Y) + 6 * theta Y + Y)

private lemma L3_sub {R : Type*} [CommRing R] (Y Z : Polynomial R) :
    L3 (Y - Z) = L3 Y - L3 Z := by
  simp only [L3, theta_sub]; ring

private lemma L3_coeff {R : Type*} [CommRing R] (Y : Polynomial R) (k : ℕ) :
    (L3 Y).coeff (k + 1) =
      8 * ((k + 1 : R) ^ 3) * Y.coeff (k + 1) - (2 * (k : R) + 1) ^ 3 * Y.coeff k := by
  simp only [L3, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X_mul, theta_coeff]
  push_cast
  ring

private lemma L3_coeff_zero {R : Type*} [CommRing R] (Y : Polynomial R) :
    (L3 Y).coeff 0 = 0 := by
  simp [L3, theta_coeff]

private lemma L3_unique_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (D : Polynomial (ZMod p)) (hdeg : D.natDegree < p) (h0 : D.coeff 0 = 0) (hL : L3 D = 0) :
    D = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h8 : (8 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff 8 p).mp (by simpa using hz)
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using hdvd)
    have := Nat.le_of_dvd (by decide) h2; omega
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hkp : k < p
  · induction k with
    | zero => exact h0
    | succ k ih =>
      have hk_prev : D.coeff k = 0 := ih (by omega)
      have hc := congrArg (fun P => P.coeff (k + 1)) hL
      rw [L3_coeff, Polynomial.coeff_zero, hk_prev, mul_zero, sub_zero] at hc
      have hne : (8 : ZMod p) * ((k + 1 : ZMod p) ^ 3) ≠ 0 := by
        apply mul_ne_zero h8
        apply pow_ne_zero 3
        intro hz
        have hdvd := (ZMod.natCast_eq_zero_iff (k + 1) p).mp (by simpa using hz)
        have := Nat.le_of_dvd (by omega) hdvd; omega
      exact (mul_eq_zero.mp hc).resolve_left hne
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

-- Auxiliary operators for the inhomogeneous 3rd-order ODEs of R1 and R2:
private noncomputable def op1 {R : Type*} [CommRing R] (Y : Polynomial R) : Polynomial R :=
  24 * (1 - Polynomial.X) * theta (theta Y) - 24 * Polynomial.X * theta Y - 6 * Polynomial.X * Y

private noncomputable def op2 {R : Type*} [CommRing R] (Y : Polynomial R) : Polynomial R :=
  24 * (1 - Polynomial.X) * theta Y - 12 * Polynomial.X * Y

-- Pure ring identities: symmetric square of 2nd-order Gauss ODE (both cases a = 1/4 and a = 3/4)!
private lemma sym_sq_ode_mod4_eq1 {R : Type*} [CommRing R]
    (g0 h1 : Polynomial R)
    (hg0 : 16 * (1 - Polynomial.X) * theta (theta g0) - 8 * Polynomial.X * theta g0 - Polynomial.X * g0 = 0)
    (hh1 : 16 * (1 - Polynomial.X) * theta (theta h1) - 8 * Polynomial.X * theta h1 - Polynomial.X * h1 +
      16 * (1 - Polynomial.X) * theta g0 - 4 * Polynomial.X * g0 = 0) :
    L3 (g0 * g0) = 0 ∧
    L3 (2 * g0 * h1) + op1 (g0 * g0) = 0 ∧
    L3 (2 * h1 * h1) + op1 (2 * g0 * h1) + op2 (g0 * g0) = 0 := by
  have ht2 : theta (2 : Polynomial R) = 0 := theta_ofNat 2
  have ht4 : theta (4 : Polynomial R) = 0 := theta_ofNat 4
  have ht8 : theta (8 : Polynomial R) = 0 := theta_ofNat 8
  have ht16 : theta (16 : Polynomial R) = 0 := theta_ofNat 16
  have d_hg0 := congrArg theta hg0
  have d_hh1 := congrArg theta hh1
  rw [theta_zero] at d_hg0 d_hh1
  simp only [theta_add, theta_sub, theta_mul, ht2, ht4, ht8, ht16, theta_X, theta_one, theta_zero] at d_hg0 d_hh1
  refine ⟨?_, ?_, ?_⟩
  · unfold L3
    simp only [theta_mul, theta_add, theta_sub, ht2, theta_zero]
    linear_combination g0 * d_hg0 + (3 * theta g0) * hg0
  · unfold L3 op1
    simp only [theta_mul, theta_add, theta_sub, ht2, theta_zero]
    linear_combination h1 * d_hg0 + g0 * d_hh1 + (2 * g0 + 3 * theta h1) * hg0 + (3 * theta g0) * hh1
  · unfold L3 op1 op2
    simp only [theta_mul, theta_add, theta_sub, ht2, theta_zero]
    linear_combination (2 * h1) * d_hh1 + h1 * hg0 + (3 * (g0 + 2 * theta h1)) * hh1

private lemma sym_sq_ode_mod4_eq3 {R : Type*} [CommRing R]
    (g0 h1 : Polynomial R)
    (hg0 : 16 * (1 - Polynomial.X) * theta (theta g0) - 24 * Polynomial.X * theta g0 - 9 * Polynomial.X * g0 = 0)
    (hh1 : 16 * (1 - Polynomial.X) * theta (theta h1) - 24 * Polynomial.X * theta h1 - 9 * Polynomial.X * h1 +
      16 * (1 - Polynomial.X) * theta g0 - 12 * Polynomial.X * g0 = 0) :
    L3 ((1 - Polynomial.X) * g0 * g0) = 0 ∧
    L3 (2 * (1 - Polynomial.X) * g0 * h1) + op1 ((1 - Polynomial.X) * g0 * g0) = 0 ∧
    L3 (2 * (1 - Polynomial.X) * h1 * h1) + op1 (2 * (1 - Polynomial.X) * g0 * h1) +
      op2 ((1 - Polynomial.X) * g0 * g0) = 0 := by
  have ht2 : theta (2 : Polynomial R) = 0 := theta_ofNat 2
  have ht9 : theta (9 : Polynomial R) = 0 := theta_ofNat 9
  have ht12 : theta (12 : Polynomial R) = 0 := theta_ofNat 12
  have ht16 : theta (16 : Polynomial R) = 0 := theta_ofNat 16
  have ht24 : theta (24 : Polynomial R) = 0 := theta_ofNat 24
  have d_hg0 := congrArg theta hg0
  have d_hh1 := congrArg theta hh1
  rw [theta_zero] at d_hg0 d_hh1
  simp only [theta_add, theta_sub, theta_mul, ht2, ht9, ht12, ht16, ht24, theta_X, theta_one, theta_zero] at d_hg0 d_hh1
  refine ⟨?_, ?_, ?_⟩
  · unfold L3
    simp only [theta_mul, theta_add, theta_sub, ht2, theta_X, theta_one, theta_zero]
    linear_combination
      ((1 - Polynomial.X) * g0) * d_hg0 +
      (-2 * Polynomial.X * g0 + 3 * (1 - Polynomial.X) * theta g0) * hg0
  · unfold L3 op1
    simp only [theta_mul, theta_add, theta_sub, ht2, theta_X, theta_one, theta_zero]
    linear_combination
      ((1 - Polynomial.X) * h1) * d_hg0 +
      ((1 - Polynomial.X) * g0) * d_hh1 +
      (2 * (1 - Polynomial.X) * g0 - 2 * Polynomial.X * h1 + 3 * (1 - Polynomial.X) * theta h1) * hg0 +
      (-2 * Polynomial.X * g0 + 3 * (1 - Polynomial.X) * theta g0) * hh1
  · unfold L3 op1 op2
    simp only [theta_mul, theta_add, theta_sub, ht2, theta_X, theta_one, theta_zero]
    linear_combination
      (2 * (1 - Polynomial.X) * h1) * d_hh1 +
      ((1 - Polynomial.X) * h1) * hg0 +
      (3 * (1 - Polynomial.X) * g0 - 4 * Polynomial.X * h1 + 6 * (1 - Polynomial.X) * theta h1) * hh1

-- Wronskian 1-line identity for both a_num = 1 and a_num = 3!
private lemma wronskian_ode {R : Type*} [CommRing R]
    (a_num : ℕ) (g0 h1 : Polynomial R)
    (hg0 : 16 * (1 - Polynomial.X) * theta (theta g0) -
      C (8 * (a_num : R)) * Polynomial.X * theta g0 - C ((a_num : R) ^ 2) * Polynomial.X * g0 = 0)
    (hh1 : 16 * (1 - Polynomial.X) * theta (theta h1) -
      C (8 * (a_num : R)) * Polynomial.X * theta h1 - C ((a_num : R) ^ 2) * Polynomial.X * h1 +
      16 * (1 - Polynomial.X) * theta g0 - C (4 * (a_num : R)) * Polynomial.X * g0 = 0) :
    let W := g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0
    8 * (1 - Polynomial.X) * theta W - C (4 * (a_num : R)) * Polynomial.X * W = 0 := by
  dsimp only
  have ht2 : theta (2 : Polynomial R) = 0 := theta_ofNat 2
  simp only [theta_add, theta_sub, theta_mul, ht2, theta_zero]
  have h8a : C (8 * (a_num : R)) = 2 * C (4 * (a_num : R)) := by
    rw [show (8 * (a_num : R)) = 2 * (4 * (a_num : R)) by ring, map_mul, map_ofNat]
  rw [h8a] at hg0 hh1
  linear_combination g0 * hh1 - h1 * hg0

-- Exact Wronskian formula in (ZMod p)[X]: W^2 = (1 - X)^(p - a_num) for a_num ∈ {1, 3}!
private lemma wronskian_sq_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (a_num : ℕ) (ha_num : a_num = 1 ∨ a_num = 3)
    (W : Polynomial (ZMod p))
    (hW_deg : W.natDegree ≤ (p - a_num) / 2)
    (hW_c0 : W.coeff 0 = 1)
    (hW_ode : 8 * (1 - Polynomial.X) * theta W - C (4 * (a_num : ZMod p)) * Polynomial.X * W = 0) :
    W ^ 2 = (1 - Polynomial.X) ^ (p - a_num) := by
  have : Fact p.Prime := ⟨hp⟩
  -- Let F = (1 - X)^a_num * W^2. Notice deg F ≤ a_num + (p - a_num) = p!
  -- Wait: F' = 0 ==> F = c_0 + c_p * X^p!
  -- Wait: what is F.coeff 0? 1! And what is F.eval 1? 0!
  -- So 1 + c_p * 1^p = 0 ==> c_p = -1 ==> F = 1 - X^p = (1 - X)^p!
  -- Cancel (1 - X)^a_num (domain!) ==> W^2 = (1 - X)^(p - a_num)!!
  have h8ne : (8 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff 8 p).mp (by simpa using hz)
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using hdvd)
    have := Nat.le_of_dvd (by decide) h2; omega
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff 4 p).mp (by simpa using hz)
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hdvd)
    have := Nat.le_of_dvd (by decide) h2; omega
  set F : Polynomial (ZMod p) := (1 - Polynomial.X) ^ a_num * W ^ 2
  have hderiv_1x : Polynomial.derivative (1 - Polynomial.X : Polynomial (ZMod p)) = -1 := by
    simp [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_X]
  have hF'_zero : Polynomial.derivative F = 0 := by
    have hX_F' : 4 * Polynomial.X * Polynomial.derivative F = 0 := by
      have hdF : Polynomial.derivative F =
          (1 - Polynomial.X) ^ (a_num - 1) * W *
            (2 * (1 - Polynomial.X) * Polynomial.derivative W - C (a_num : ZMod p) * W) := by
        simp only [F, Polynomial.derivative_mul, Polynomial.derivative_pow, hderiv_1x,
          Nat.cast_ofNat, map_ofNat]
        have ha1 : a_num = (a_num - 1) + 1 := by omega
        conv_lhs => rhs; rw [ha1, pow_succ]
        ring
      rw [hdF]
      have hmid : 4 * Polynomial.X * (2 * (1 - Polynomial.X) * Polynomial.derivative W - C (a_num : ZMod p) * W) = 0 := by
        have : 4 * Polynomial.X * (2 * (1 - Polynomial.X) * Polynomial.derivative W - C (a_num : ZMod p) * W) =
            8 * (1 - Polynomial.X) * theta W - C (4 * (a_num : ZMod p)) * Polynomial.X * W := by
          simp only [theta, map_mul, map_ofNat]; ring
        rw [this, hW_ode]
      calc 4 * Polynomial.X * ((1 - Polynomial.X) ^ (a_num - 1) * W *
            (2 * (1 - Polynomial.X) * Polynomial.derivative W - C (a_num : ZMod p) * W))
          = (1 - Polynomial.X) ^ (a_num - 1) * W *
            (4 * Polynomial.X * (2 * (1 - Polynomial.X) * Polynomial.derivative W - C (a_num : ZMod p) * W)) := by ring
        _ = 0 := by rw [hmid, mul_zero]
    have h4X_ne : (4 * Polynomial.X : Polynomial (ZMod p)) ≠ 0 := by
      apply mul_ne_zero _ Polynomial.X_ne_zero
      rw [← map_ofNat (Polynomial.C (R := ZMod p)) 4]
      exact Polynomial.C_ne_zero.mpr h4ne
    exact (mul_eq_zero.mp hX_F').resolve_left h4X_ne
  -- Since F' = 0 and deg F ≤ p, F.coeff k = 0 for all 1 ≤ k < p and all k > p!
  have hF_deg : F.natDegree ≤ p := by
    have h1x_deg : ((1 - Polynomial.X : Polynomial (ZMod p)) ^ a_num).natDegree ≤ a_num := by
      calc ((1 - Polynomial.X : Polynomial (ZMod p)) ^ a_num).natDegree
          ≤ a_num * (1 - Polynomial.X : Polynomial (ZMod p)).natDegree := Polynomial.natDegree_pow_le
        _ ≤ a_num * 1 := by gcongr; compute_degree!
        _ = a_num := mul_one _
    have hW2_deg : (W ^ 2).natDegree ≤ p - a_num := by
      calc (W ^ 2).natDegree ≤ 2 * W.natDegree := Polynomial.natDegree_pow_le
        _ ≤ 2 * ((p - a_num) / 2) := Nat.mul_le_mul_left 2 hW_deg
        _ ≤ p - a_num := by omega
    calc F.natDegree ≤ ((1 - Polynomial.X : Polynomial (ZMod p)) ^ a_num).natDegree + (W ^ 2).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ a_num + (p - a_num) := Nat.add_le_add h1x_deg hW2_deg
      _ = p := by omega
  have hF_form : F = 1 + C (F.coeff p) * Polynomial.X ^ p := by
    ext k
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [if_pos rfl, if_neg (show (0 : ℕ) ≠ p by omega), add_zero]
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp [F, ← Polynomial.coeff_zero_eq_eval_zero, hW_c0]
    · by_cases hkp : k = p
      · rw [hkp]; simp [show p ≠ 0 by omega]
      · simp only [if_neg hk0, if_neg (Ne.symm hk0), if_neg hkp, if_neg (Ne.symm hkp), add_zero]
        by_cases hlt : k < p
        · have hc := congrArg (fun P => P.coeff (k - 1)) hF'_zero
          rw [Polynomial.coeff_zero, Polynomial.coeff_derivative, show k - 1 + 1 = k by omega,
            Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hc
          have hkne : (k : ZMod p) ≠ 0 := by
            intro h0
            have hdvd := (ZMod.natCast_eq_zero_iff k p).mp h0
            have := Nat.le_of_dvd (by omega) hdvd; omega
          have hc' : F.coeff k * (k : ZMod p) = 0 := by linear_combination hc
          exact (mul_eq_zero.mp hc').resolve_right hkne
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF_deg (by omega))
  -- Evaluate F at 1: F.eval 1 = 0 since a_num ≥ 1, so 1 + F.coeff p = 0 => F.coeff p = -1!
  have hFeval1 : F.eval 1 = 0 := by
    simp [F, zero_pow (show a_num ≠ 0 by omega)]
  have hFcp : F.coeff p = -1 := by
    have h1 := congrArg (Polynomial.eval 1) hF_form
    rw [hFeval1] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one] at h1
    linear_combination -h1
  rw [hFcp, map_neg, map_one] at hF_form
  -- F = 1 - X^p = (1 - X)^p in characteristic p!
  have hFp : F = (1 - Polynomial.X) ^ p := by
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    rw [hF_form, sub_eq_add_neg, add_pow_char, one_pow, hodd.neg_pow]
    ring
  have hcancel : (1 - Polynomial.X : Polynomial (ZMod p)) ^ a_num * W ^ 2 =
      (1 - Polynomial.X) ^ a_num * (1 - Polynomial.X) ^ (p - a_num) := by
    rw [← pow_add, show a_num + (p - a_num) = p by omega]
    exact hFp
  have h1x_ne : (1 - Polynomial.X : Polynomial (ZMod p)) ^ a_num ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp at this
  exact mul_left_cancel₀ h1x_ne hcancel

-- Define the three generating polynomials R0, R1, R2 in (ZMod p)[X] and prove they satisfy L3 / op1 / op2!
private def H1p (p k : ℕ) : ZMod p :=
  ∑ j ∈ Finset.Icc 1 k, (j : ZMod p)⁻¹

private def H2p (p k : ℕ) : ZMod p :=
  ∑ j ∈ Finset.Icc 1 k, ((j : ZMod p)⁻¹) ^ 2

private lemma H1p_succ (p k : ℕ) : H1p p (k + 1) = H1p p k + ((k + 1 : ℕ) : ZMod p)⁻¹ := by
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext x; simp [Finset.mem_Icc]; omega
  have hnot : k + 1 ∉ Finset.Icc 1 k := by simp [Finset.mem_Icc]
  rw [H1p, hins, Finset.sum_insert hnot, ← H1p, add_comm]

private lemma H2p_succ (p k : ℕ) : H2p p (k + 1) = H2p p k + (((k + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext x; simp [Finset.mem_Icc]; omega
  have hnot : k + 1 ∉ Finset.Icc 1 k := by simp [Finset.mem_Icc]
  rw [H2p, hins, Finset.sum_insert hnot, ← H2p, add_comm]

private noncomputable def polyR0 (p : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.range ((p - 1) / 2 + 1),
    C (((Nat.choose (2 * k) k : ZMod p) ^ 3) * ((64 : ZMod p)⁻¹) ^ k) * Polynomial.X ^ k

private noncomputable def polyR1 (p : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.range ((p - 1) / 2 + 1),
    C (((Nat.choose (2 * k) k : ZMod p) ^ 3) * (6 * (H1p p (2 * k) - H1p p k)) * ((64 : ZMod p)⁻¹) ^ k) *
      Polynomial.X ^ k

private noncomputable def polyR2 (p : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.range ((p - 1) / 2 + 1),
    C (((Nat.choose (2 * k) k : ZMod p) ^ 3) *
      (18 * (H1p p (2 * k) - H1p p k) ^ 2 - 6 * H2p p (2 * k) + 3 * H2p p k) * ((64 : ZMod p)⁻¹) ^ k) *
      Polynomial.X ^ k

private lemma polyR_odes {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    L3 (polyR0 p) = 0 ∧
    L3 (polyR1 p) + op1 (polyR0 p) = 0 ∧
    L3 (polyR2 p) + op1 (polyR1 p) + op2 (polyR0 p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set m := (p - 1) / 2
  have h2m1 : 2 * m + 1 = p := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega)); omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0; have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd; omega
  have h64ne : (64 : ZMod p) ≠ 0 := by
    have : (64 : ZMod p) = 2 ^ 6 := by norm_num
    rw [this]; exact pow_ne_zero 6 h2ne
  -- Helper: coefficient formulas for R0, R1, R2
  set c0 : ℕ → ZMod p := fun k => ((Nat.choose (2 * k) k : ZMod p) ^ 3) * ((64 : ZMod p)⁻¹) ^ k
  set d1 : ℕ → ZMod p := fun k => 6 * (H1p p (2 * k) - H1p p k)
  set d2 : ℕ → ZMod p := fun k => 18 * (H1p p (2 * k) - H1p p k) ^ 2 - 6 * H2p p (2 * k) + 3 * H2p p k
  have hcR0 : ∀ k, (polyR0 p).coeff k = if k ≤ m then c0 k else 0 := by
    intro k; simp only [polyR0, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]; split_ifs with h1 h2
    · rfl
    · rw [Finset.mem_range] at h1; omega
    · rw [Finset.mem_range] at h1; omega
    · rfl
  have hcR1 : ∀ k, (polyR1 p).coeff k = if k ≤ m then c0 k * d1 k else 0 := by
    intro k; simp only [polyR1, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]; split_ifs with h1 h2
    · simp only [c0, d1]; ring
    · rw [Finset.mem_range] at h1; omega
    · rw [Finset.mem_range] at h1; omega
    · rfl
  have hcR2 : ∀ k, (polyR2 p).coeff k = if k ≤ m then c0 k * d2 k else 0 := by
    intro k; simp only [polyR2, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]; split_ifs with h1 h2
    · simp only [c0, d2]; ring
    · rw [Finset.mem_range] at h1; omega
    · rw [Finset.mem_range] at h1; omega
    · rfl
  -- Recurrence for c0: 8*(k+1)^3 * c0 (k+1) = (2k+1)^3 * c0 k!
  have hc0_rec : ∀ k : ℕ, 8 * ((k + 1 : ZMod p) ^ 3) * c0 (k + 1) = (2 * (k : ZMod p) + 1) ^ 3 * c0 k := by
    intro k
    have hA : (k + 1) * Nat.choose (2 * (k + 1)) (k + 1) = 2 * (2 * k + 1) * Nat.choose (2 * k) k := by
      have hc1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * k + 2 by omega)
      have hc0 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
      rw [show 2 * k + 2 - (k + 1) = k + 1 by omega] at hc1
      rw [show 2 * k - k = k by omega] at hc0
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      apply Nat.mul_right_cancel (mul_pos (Nat.factorial_pos (k + 1)) (Nat.factorial_pos k))
      have hf2 : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
      have hfk : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
      calc (k + 1) * Nat.choose (2 * k + 2) (k + 1) * ((k + 1).factorial * k.factorial)
          = Nat.choose (2 * k + 2) (k + 1) * (k + 1).factorial * (k + 1).factorial := by rw [hfk]; ring
        _ = (2 * k + 2).factorial := hc1
        _ = (2 * k + 2) * (2 * k + 1) * (Nat.choose (2 * k) k * k.factorial * k.factorial) := by rw [hf2, ← hc0]
        _ = 2 * (2 * k + 1) * Nat.choose (2 * k) k * ((k + 1).factorial * k.factorial) := by rw [hfk]; ring
    have hAc : (k + 1 : ZMod p) * (Nat.choose (2 * (k + 1)) (k + 1) : ZMod p) =
        2 * (2 * (k : ZMod p) + 1) * (Nat.choose (2 * k) k : ZMod p) := by
      have := congrArg (fun n : ℕ => (n : ZMod p)) hA
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using this
    dsimp only [c0]
    rw [pow_succ ((64 : ZMod p)⁻¹)]
    calc 8 * (k + 1 : ZMod p) ^ 3 * ((Nat.choose (2 * (k + 1)) (k + 1) : ZMod p) ^ 3 * ((64 : ZMod p)⁻¹ ^ k * (64 : ZMod p)⁻¹))
        = 8 * ((k + 1 : ZMod p) * (Nat.choose (2 * (k + 1)) (k + 1) : ZMod p)) ^ 3 * (64 : ZMod p)⁻¹ ^ k * (64 : ZMod p)⁻¹ := by
            rw [mul_pow]; ring
      _ = 8 * (2 * (2 * (k : ZMod p) + 1) * (Nat.choose (2 * k) k : ZMod p)) ^ 3 * (64 : ZMod p)⁻¹ ^ k * (64 : ZMod p)⁻¹ := by
            rw [hAc]
      _ = (64 * (64 : ZMod p)⁻¹) * ((2 * (k : ZMod p) + 1) ^ 3 * ((Nat.choose (2 * k) k : ZMod p) ^ 3 * (64 : ZMod p)⁻¹ ^ k)) := by
            ring
      _ = (2 * (k : ZMod p) + 1) ^ 3 * ((Nat.choose (2 * k) k : ZMod p) ^ 3 * (64 : ZMod p)⁻¹ ^ k) := by
            rw [mul_inv_cancel₀ h64ne, one_mul]
  -- Steps for d1 and d2 when k < m (so 2k+1 and k+1 are nonzero in ZMod p):
  have hd1_step : ∀ k < m,
      d1 (k + 1) - d1 k = 6 * ((2 * (k : ZMod p) + 1)⁻¹) - 3 * ((k + 1 : ZMod p)⁻¹) := by
    intro k hk
    have h2k2 : (2 * (k + 1) : ℕ) = (2 * k + 1) + 1 := by omega
    simp only [d1, h2k2, H1p_succ]
    have h2ne_k : (2 * (k : ZMod p) + 2) = 2 * ((k : ZMod p) + 1) := by ring
    have hinv2 : (((2 * k + 1 + 1 : ℕ) : ZMod p))⁻¹ = (2 : ZMod p)⁻¹ * ((k + 1 : ZMod p))⁻¹ := by
      rw [show ((2 * k + 1 + 1 : ℕ) : ZMod p) = 2 * ((k : ZMod p) + 1) by push_cast; ring, mul_inv]
    have hinv2_6 : 6 * (2 : ZMod p)⁻¹ = (3 : ZMod p) := by
      apply mul_left_cancel₀ h2ne
      calc (2 : ZMod p) * (6 * (2 : ZMod p)⁻¹) = 6 * (2 * (2 : ZMod p)⁻¹) := by ring
        _ = 6 := by rw [mul_inv_cancel₀ h2ne, mul_one]
        _ = 2 * 3 := by norm_num
    rw [hinv2]
    push_cast
    linear_combination ((k + 1 : ZMod p)⁻¹) * hinv2_6
  have hd2_step : ∀ k < m,
      d2 (k + 1) - d2 k =
        (6 * ((2 * (k : ZMod p) + 1)⁻¹) - 3 * ((k + 1 : ZMod p)⁻¹)) * d1 k +
        12 * (((2 * (k : ZMod p) + 1)⁻¹) ^ 2) - 18 * ((2 * (k : ZMod p) + 1)⁻¹) * ((k + 1 : ZMod p)⁻¹) +
        6 * (((k + 1 : ZMod p)⁻¹) ^ 2) := by
    intro k hk
    have h2k2 : (2 * (k + 1) : ℕ) = (2 * k + 1) + 1 := by omega
    have hinv2 : (((2 * k + 1 + 1 : ℕ) : ZMod p))⁻¹ = (2 : ZMod p)⁻¹ * ((k + 1 : ZMod p))⁻¹ := by
      rw [show ((2 * k + 1 + 1 : ℕ) : ZMod p) = 2 * ((k : ZMod p) + 1) by push_cast; ring, mul_inv]
    have h2inv_sq : (2 : ZMod p)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2ne
    set a := ((2 * (k : ZMod p) + 1)⁻¹)
    set b := ((k + 1 : ZMod p)⁻¹)
    set u := H1p p (2 * k) - H1p p k
    have hdu : H1p p (2 * (k + 1)) - H1p p (k + 1) = u + a - (2 : ZMod p)⁻¹ * b := by
      simp only [h2k2, H1p_succ, hinv2, u, a, b]
      push_cast
      linear_combination b * h2inv_sq
    have hdH2 : -6 * H2p p (2 * (k + 1)) + 3 * H2p p (k + 1) - (-6 * H2p p (2 * k) + 3 * H2p p k) =
        -6 * a ^ 2 + 3 * (1 - 2 * ((2 : ZMod p)⁻¹) ^ 2) * b ^ 2 := by
      simp only [h2k2, H2p_succ, hinv2, a, b]
      push_cast
      ring
    have hhalf_sq : 4 * ((2 : ZMod p)⁻¹) ^ 2 = 1 := by
      calc 4 * ((2 : ZMod p)⁻¹) ^ 2 = ((2 : ZMod p)⁻¹ * 2) ^ 2 := by ring
        _ = 1 := by rw [h2inv_sq, one_pow]
    simp only [d2, d1, hdu]
    have : 18 * (u + a - (2 : ZMod p)⁻¹ * b) ^ 2 - 6 * H2p p (2 * (k + 1)) + 3 * H2p p (k + 1) -
        (18 * u ^ 2 - 6 * H2p p (2 * k) + 3 * H2p p k) =
        18 * ((u + a - (2 : ZMod p)⁻¹ * b) ^ 2 - u ^ 2) +
        (-6 * H2p p (2 * (k + 1)) + 3 * H2p p (k + 1) - (-6 * H2p p (2 * k) + 3 * H2p p k)) := by ring
    rw [this, hdH2]
    linear_combination (-18 * u * b - 18 * a * b) * h2inv_sq + (3 * b ^ 2) * hhalf_sq
  -- Coeff formulas for op1 and op2:
  have hop1_coeff : ∀ (Y : Polynomial (ZMod p)) (k : ℕ),
      (op1 Y).coeff (k + 1) =
        24 * ((k + 1 : ZMod p) ^ 2) * Y.coeff (k + 1) -
        6 * (2 * (k : ZMod p) + 1) ^ 2 * Y.coeff k := by
    intro Y k
    have hre : op1 Y = 24 * theta (theta Y) - 24 * (Polynomial.X * theta (theta Y)) -
        24 * (Polynomial.X * theta Y) - 6 * (Polynomial.X * Y) := by simp only [op1]; ring
    rw [hre]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_mul, theta_coeff]
    push_cast; ring
  have hop2_coeff : ∀ (Y : Polynomial (ZMod p)) (k : ℕ),
      (op2 Y).coeff (k + 1) =
        24 * (k + 1 : ZMod p) * Y.coeff (k + 1) -
        12 * (2 * (k : ZMod p) + 1) * Y.coeff k := by
    intro Y k
    have hre : op2 Y = 24 * theta Y - 24 * (Polynomial.X * theta Y) - 12 * (Polynomial.X * Y) := by
      simp only [op2]; ring
    rw [hre]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_mul, theta_coeff]
    push_cast; ring
  -- Also (2*m + 1 : ZMod p) = 0!
  have h2m1_zero : (2 * (m : ZMod p) + 1) = 0 := by
    have : (2 * (m : ZMod p) + 1) = ((2 * m + 1 : ℕ) : ZMod p) := by push_cast; rfl
    rw [this, h2m1, ZMod.natCast_self]
  refine ⟨?_, ?_, ?_⟩
  · -- L3 (polyR0 p) = 0
    ext n
    rw [Polynomial.coeff_zero]
    cases n with
    | zero => exact L3_coeff_zero _
    | succ k =>
      rw [L3_coeff, hcR0 (k + 1), hcR0 k]
      by_cases hkm : k < m
      · rw [if_pos (by omega), if_pos (by omega), hc0_rec k, sub_self]
      · by_cases hkeq : k = m
        · subst hkeq; rw [if_neg (by omega), if_pos le_rfl, h2m1_zero]; ring
        · rw [if_neg (by omega), if_neg (by omega)]; ring
  · -- L3 (polyR1 p) + op1 (polyR0 p) = 0
    ext n
    rw [Polynomial.coeff_zero, Polynomial.coeff_add]
    cases n with
    | zero => simp [L3, op1, theta_coeff]
    | succ k =>
      rw [L3_coeff, hop1_coeff, hcR1 (k + 1), hcR1 k, hcR0 (k + 1), hcR0 k]
      by_cases hkm : k < m
      · simp only [if_pos (show k + 1 ≤ m by omega), if_pos (show k ≤ m by omega)]
        have hk1_ne : (k + 1 : ZMod p) ≠ 0 := by
          intro h0; have hdvd := (ZMod.natCast_eq_zero_iff (k + 1) p).mp (by simpa using h0)
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have h2k1_ne : (2 * (k : ZMod p) + 1) ≠ 0 := by
          intro h0
          have hdvd := (ZMod.natCast_eq_zero_iff (2 * k + 1) p).mp (by simpa [Nat.cast_add, Nat.cast_mul] using h0)
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have hd1k := hd1_step k hkm
        have hrec := hc0_rec k
        have hinv1 : (k + 1 : ZMod p) * (k + 1 : ZMod p)⁻¹ - 1 = 0 := by rw [mul_inv_cancel₀ hk1_ne, sub_self]
        have hinv2 : (2 * (k : ZMod p) + 1) * (2 * (k : ZMod p) + 1)⁻¹ - 1 = 0 := by rw [mul_inv_cancel₀ h2k1_ne, sub_self]
        linear_combination
          (d1 k + 6 * (2 * (k : ZMod p) + 1)⁻¹) * hrec +
          (8 * (k + 1 : ZMod p) ^ 3 * c0 (k + 1)) * hd1k +
          (6 * (2 * (k : ZMod p) + 1) ^ 2 * c0 k) * hinv2 -
          (24 * (k + 1 : ZMod p) ^ 2 * c0 (k + 1)) * hinv1
      · by_cases hkeq : k = m
        · rw [hkeq]; simp only [if_neg (show ¬ m + 1 ≤ m by omega), if_pos le_rfl, h2m1_zero]; ring
        · simp only [if_neg (show ¬ k + 1 ≤ m by omega), if_neg (show ¬ k ≤ m by omega)]; ring
  · -- L3 (polyR2 p) + op1 (polyR1 p) + op2 (polyR0 p) = 0
    ext n
    rw [Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_add]
    cases n with
    | zero => simp [L3, op1, op2, theta_coeff]
    | succ k =>
      rw [L3_coeff, hop1_coeff, hop2_coeff, hcR2 (k + 1), hcR2 k, hcR1 (k + 1), hcR1 k, hcR0 (k + 1), hcR0 k]
      by_cases hkm : k < m
      · simp only [if_pos (show k + 1 ≤ m by omega), if_pos (show k ≤ m by omega)]
        have hk1_ne : (k + 1 : ZMod p) ≠ 0 := by
          intro h0; have hdvd := (ZMod.natCast_eq_zero_iff (k + 1) p).mp (by simpa using h0)
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have h2k1_ne : (2 * (k : ZMod p) + 1) ≠ 0 := by
          intro h0
          have hdvd := (ZMod.natCast_eq_zero_iff (2 * k + 1) p).mp (by simpa [Nat.cast_add, Nat.cast_mul] using h0)
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have hd1k := hd1_step k hkm
        have hd2k := hd2_step k hkm
        have hrec := hc0_rec k
        have hinv1 : (k + 1 : ZMod p) * (k + 1 : ZMod p)⁻¹ - 1 = 0 := by rw [mul_inv_cancel₀ hk1_ne, sub_self]
        have hinv2 : (2 * (k : ZMod p) + 1) * (2 * (k : ZMod p) + 1)⁻¹ - 1 = 0 := by rw [mul_inv_cancel₀ h2k1_ne, sub_self]
        set a := (2 * (k : ZMod p) + 1)⁻¹
        set b := (k + 1 : ZMod p)⁻¹
        -- Express everything in terms of c0 k via hrec!
        have hc0_next : 8 * (k + 1 : ZMod p) ^ 3 * c0 (k + 1) = (2 * (k : ZMod p) + 1) ^ 3 * c0 k := hrec
        have hc0_2 : 24 * (k + 1 : ZMod p) ^ 2 * c0 (k + 1) = 3 * b * (2 * (k : ZMod p) + 1) ^ 3 * c0 k := by
          linear_combination (3 * b) * hc0_next - (24 * (k + 1 : ZMod p) ^ 2 * c0 (k + 1)) * hinv1
        have hc0_1 : 24 * (k + 1 : ZMod p) * c0 (k + 1) = 3 * b ^ 2 * (2 * (k : ZMod p) + 1) ^ 3 * c0 k := by
          linear_combination (3 * b ^ 2) * hc0_next - (24 * (k + 1 : ZMod p) * c0 (k + 1) * ((k + 1 : ZMod p) * b + 1)) * hinv1
        have hA1 : (2 * (k : ZMod p) + 1) ^ 3 * a = (2 * (k : ZMod p) + 1) ^ 2 := by
          linear_combination ((2 * (k : ZMod p) + 1) ^ 2) * hinv2
        have hA2 : (2 * (k : ZMod p) + 1) ^ 3 * a ^ 2 = (2 * (k : ZMod p) + 1) := by
          linear_combination ((2 * (k : ZMod p) + 1) * ((2 * (k : ZMod p) + 1) * a + 1)) * hinv2
        calc 8 * (k + 1 : ZMod p) ^ 3 * (c0 (k + 1) * d2 (k + 1)) - (2 * (k : ZMod p) + 1) ^ 3 * (c0 k * d2 k) +
              (24 * (k + 1 : ZMod p) ^ 2 * (c0 (k + 1) * d1 (k + 1)) - 6 * (2 * (k : ZMod p) + 1) ^ 2 * (c0 k * d1 k)) +
              (24 * (k + 1 : ZMod p) * c0 (k + 1) - 12 * (2 * (k : ZMod p) + 1) * c0 k)
            = (8 * (k + 1 : ZMod p) ^ 3 * c0 (k + 1)) * d2 (k + 1) - (2 * (k : ZMod p) + 1) ^ 3 * c0 k * d2 k +
              ((24 * (k + 1 : ZMod p) ^ 2 * c0 (k + 1)) * d1 (k + 1) - 6 * (2 * (k : ZMod p) + 1) ^ 2 * c0 k * d1 k) +
              ((24 * (k + 1 : ZMod p) * c0 (k + 1)) - 12 * (2 * (k : ZMod p) + 1) * c0 k) := by ring
          _ = (2 * (k : ZMod p) + 1) ^ 3 * c0 k * (d2 (k + 1) - d2 k) +
              3 * b * (2 * (k : ZMod p) + 1) ^ 3 * c0 k * (d1 (k + 1) - d1 k) +
              (3 * b * (2 * (k : ZMod p) + 1) ^ 3 - 6 * (2 * (k : ZMod p) + 1) ^ 2) * c0 k * d1 k +
              (3 * b ^ 2 * (2 * (k : ZMod p) + 1) ^ 3 - 12 * (2 * (k : ZMod p) + 1)) * c0 k := by
                rw [hc0_next, hc0_2, hc0_1]; ring
          _ = (2 * (k : ZMod p) + 1) ^ 3 * c0 k *
                ((6 * a - 3 * b) * d1 k + 12 * a ^ 2 - 18 * a * b + 6 * b ^ 2) +
              3 * b * (2 * (k : ZMod p) + 1) ^ 3 * c0 k * (6 * a - 3 * b) +
              (3 * b * (2 * (k : ZMod p) + 1) ^ 3 - 6 * (2 * (k : ZMod p) + 1) ^ 2) * c0 k * d1 k +
              (3 * b ^ 2 * (2 * (k : ZMod p) + 1) ^ 3 - 12 * (2 * (k : ZMod p) + 1)) * c0 k := by
                rw [hd2k, hd1k]
          _ = 0 := by
                linear_combination (6 * c0 k * d1 k) * hA1 + (12 * c0 k) * hA2
      · by_cases hkeq : k = m
        · rw [hkeq]; simp only [if_neg (show ¬ m + 1 ≤ m by omega), if_pos le_rfl, h2m1_zero]; ring
        · simp only [if_neg (show ¬ k + 1 ≤ m by omega), if_neg (show ¬ k ≤ m by omega)]; ring

-- Construct g0 and h1 explicitly in (ZMod p)[X] for a_num ∈ {1, 3} with p % 4 = a_num!
private def pochCoeff (p a_num : ℕ) : ℕ → ZMod p
  | 0 => 1
  | k + 1 => pochCoeff p a_num k * ((4 * (k : ZMod p) + (a_num : ZMod p)) * (4 * ((k : ZMod p) + 1))⁻¹) ^ 2

private def logHarm (p a_num : ℕ) : ℕ → ZMod p
  | 0 => 0
  | k + 1 => logHarm p a_num k + (4 * ((4 * (k : ZMod p) + (a_num : ZMod p))⁻¹) - ((k : ZMod p) + 1)⁻¹)

private noncomputable def polyG0 (p a_num d : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.range (d + 1), C (pochCoeff p a_num k) * Polynomial.X ^ k

private noncomputable def polyH1 (p a_num d : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.range (d + 1), C (pochCoeff p a_num k * logHarm p a_num k) * Polynomial.X ^ k

private lemma polyG0_H1_odes {p a_num d : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpa : 4 * d + a_num = p) (ha_num : a_num = 1 ∨ a_num = 3) :
    let g0 := polyG0 p a_num d
    let h1 := polyH1 p a_num d
    16 * (1 - Polynomial.X) * theta (theta g0) -
      C (8 * (a_num : ZMod p)) * Polynomial.X * theta g0 - C ((a_num : ZMod p) ^ 2) * Polynomial.X * g0 = 0 ∧
    16 * (1 - Polynomial.X) * theta (theta h1) -
      C (8 * (a_num : ZMod p)) * Polynomial.X * theta h1 - C ((a_num : ZMod p) ^ 2) * Polynomial.X * h1 +
      16 * (1 - Polynomial.X) * theta g0 - C (4 * (a_num : ZMod p)) * Polynomial.X * g0 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set g0 := polyG0 p a_num d
  set h1 := polyH1 p a_num d
  have hc_g0 : ∀ k, g0.coeff k = if k ≤ d then pochCoeff p a_num k else 0 := by
    intro k; simp only [g0, polyG0, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]; split_ifs with h1 h2
    · rfl
    · rw [Finset.mem_range] at h1; omega
    · rw [Finset.mem_range] at h1; omega
    · rfl
  have hc_h1 : ∀ k, h1.coeff k = if k ≤ d then pochCoeff p a_num k * logHarm p a_num k else 0 := by
    intro k; simp only [h1, polyH1, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]; split_ifs with h1 h2
    · rfl
    · rw [Finset.mem_range] at h1; omega
    · rw [Finset.mem_range] at h1; omega
    · rfl
  have h4ne : (4 : ZMod p) ≠ 0 := by
    intro hz; have hdvd := (ZMod.natCast_eq_zero_iff 4 p).mp (by simpa using hz)
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hdvd)
    have := Nat.le_of_dvd (by decide) h2; omega
  have h4da : 4 * (d : ZMod p) + (a_num : ZMod p) = 0 := by
    have : 4 * (d : ZMod p) + (a_num : ZMod p) = ((4 * d + a_num : ℕ) : ZMod p) := by push_cast; rfl
    rw [this, hpa, ZMod.natCast_self]
  have hrec : ∀ k < d,
      16 * ((k + 1 : ZMod p) ^ 2) * pochCoeff p a_num (k + 1) =
        (4 * (k : ZMod p) + (a_num : ZMod p)) ^ 2 * pochCoeff p a_num k := by
    intro k hk
    have h4k_ne : (4 * ((k : ZMod p) + 1)) ≠ 0 := by
      apply mul_ne_zero h4ne
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff (k + 1) p).mp (by simpa [Nat.cast_add, Nat.cast_one] using h0)
      have := Nat.le_of_dvd (by omega) hdvd; omega
    simp only [pochCoeff]
    calc 16 * (k + 1 : ZMod p) ^ 2 *
          (pochCoeff p a_num k * ((4 * (k : ZMod p) + (a_num : ZMod p)) * (4 * ((k : ZMod p) + 1))⁻¹) ^ 2)
        = (4 * ((k : ZMod p) + 1) * (4 * ((k : ZMod p) + 1))⁻¹) ^ 2 *
          ((4 * (k : ZMod p) + (a_num : ZMod p)) ^ 2 * pochCoeff p a_num k) := by rw [mul_pow, mul_pow]; ring
      _ = (4 * (k : ZMod p) + (a_num : ZMod p)) ^ 2 * pochCoeff p a_num k := by
            rw [mul_inv_cancel₀ h4k_ne, one_pow, one_mul]
  constructor
  · have hre : 16 * (1 - Polynomial.X) * theta (theta g0) -
        C (8 * (a_num : ZMod p)) * Polynomial.X * theta g0 - C ((a_num : ZMod p) ^ 2) * Polynomial.X * g0 =
        16 * theta (theta g0) - 16 * (Polynomial.X * theta (theta g0)) -
        C (8 * (a_num : ZMod p)) * (Polynomial.X * theta g0) - C ((a_num : ZMod p) ^ 2) * (Polynomial.X * g0) := by ring
    rw [hre]
    ext n
    rw [Polynomial.coeff_zero]
    cases n with
    | zero => simp [theta_coeff]
    | succ k =>
      simp only [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, theta_coeff]
      rw [hc_g0 (k + 1), hc_g0 k]
      by_cases hkd : k < d
      · rw [if_pos (by omega), if_pos (by omega)]
        push_cast
        linear_combination hrec k hkd
      · by_cases hkeq : k = d
        · rw [hkeq]; simp only [if_neg (show ¬ d + 1 ≤ d by omega), if_pos le_rfl]
          linear_combination -(4 * (d : ZMod p) + (a_num : ZMod p)) * pochCoeff p a_num d * h4da
        · simp only [if_neg (show ¬ k + 1 ≤ d by omega), if_neg (show ¬ k ≤ d by omega)]; ring
  · have hre : 16 * (1 - Polynomial.X) * theta (theta h1) -
        C (8 * (a_num : ZMod p)) * Polynomial.X * theta h1 - C ((a_num : ZMod p) ^ 2) * Polynomial.X * h1 +
        16 * (1 - Polynomial.X) * theta g0 - C (4 * (a_num : ZMod p)) * Polynomial.X * g0 =
        16 * theta (theta h1) - 16 * (Polynomial.X * theta (theta h1)) -
        C (8 * (a_num : ZMod p)) * (Polynomial.X * theta h1) - C ((a_num : ZMod p) ^ 2) * (Polynomial.X * h1) +
        16 * theta g0 - 16 * (Polynomial.X * theta g0) - C (4 * (a_num : ZMod p)) * (Polynomial.X * g0) := by ring
    rw [hre]
    ext n
    rw [Polynomial.coeff_zero]
    cases n with
    | zero => simp [theta_coeff]
    | succ k =>
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, theta_coeff]
      rw [hc_h1 (k + 1), hc_h1 k, hc_g0 (k + 1), hc_g0 k]
      by_cases hkd : k < d
      · simp only [if_pos (show k + 1 ≤ d by omega), if_pos (show k ≤ d by omega)]
        have hk1_ne : ((k : ZMod p) + 1) ≠ 0 := by
          intro h0
          have hdvd := (ZMod.natCast_eq_zero_iff (k + 1) p).mp (by simpa [Nat.cast_add, Nat.cast_one] using h0)
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have h4ka_ne : (4 * (k : ZMod p) + (a_num : ZMod p)) ≠ 0 := by
          intro h0
          have hdvd := (ZMod.natCast_eq_zero_iff (4 * k + a_num) p).mp (by simpa [Nat.cast_add, Nat.cast_mul] using h0)
          have := Nat.le_of_dvd (by omega) hdvd; omega
        have hinv1 : ((k : ZMod p) + 1) * ((k : ZMod p) + 1)⁻¹ - 1 = 0 := by rw [mul_inv_cancel₀ hk1_ne, sub_self]
        have hinv2 : (4 * (k : ZMod p) + (a_num : ZMod p)) * (4 * (k : ZMod p) + (a_num : ZMod p))⁻¹ - 1 = 0 := by
          rw [mul_inv_cancel₀ h4ka_ne, sub_self]
        have hr := hrec k hkd
        simp only [logHarm]
        push_cast
        linear_combination
          (logHarm p a_num k + 4 * (4 * (k : ZMod p) + (a_num : ZMod p))⁻¹) * hr +
          (4 * (4 * (k : ZMod p) + (a_num : ZMod p)) * pochCoeff p a_num k) * hinv2 -
          (16 * ((k : ZMod p) + 1) * pochCoeff p a_num (k + 1)) * hinv1
      · by_cases hkeq : k = d
        · rw [hkeq]; simp only [if_neg (show ¬ d + 1 ≤ d by omega), if_pos le_rfl]
          linear_combination
            -(4 * (d : ZMod p) + (a_num : ZMod p)) * pochCoeff p a_num d * logHarm p a_num d * h4da -
            (4 * pochCoeff p a_num d) * h4da
        · simp only [if_neg (show ¬ k + 1 ≤ d by omega), if_neg (show ¬ k ≤ d by omega)]; ring

-- Final Part 4 theorem: given A_0 = 0 in ZMod p, prove S_1 = 0, A_1 = 0, and S_2 * B_2 = 1 in ZMod p!
private lemma part4_main {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7)
    (hA0 : ∑ k ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod p) ^ 3 = 0) :
    (∑ q ∈ Finset.range ((p - 1) / 2 + 1), (q : ZMod p) * ((Nat.choose (2 * q) q : ℕ) : ZMod p) ^ 3) = 0 ∧
    (∑ r ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod p) ^ 3 * (H1p p (2 * r) - H1p p r)) = 0 ∧
    (∑ q ∈ Finset.range ((p - 1) / 2 + 1), (q : ZMod p) ^ 2 * ((Nat.choose (2 * q) q : ℕ) : ZMod p) ^ 3) *
    (∑ r ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod p) ^ 3 *
      (18 * (H1p p (2 * r) - H1p p r) ^ 2 - 6 * H2p p (2 * r) + 3 * H2p p r)) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set m := (p - 1) / 2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0; have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd; omega
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h0; have hdvd := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd; omega
  have h6ne : (6 : ZMod p) ≠ 0 := by
    have : (6 : ZMod p) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2ne h3ne
  have h64ne : (64 : ZMod p) ≠ 0 := by
    have : (64 : ZMod p) = 2 ^ 6 := by norm_num
    rw [this]; exact pow_ne_zero 6 h2ne
  have h63ne : (-63 : ZMod p) ≠ 0 := by
    intro h0
    have h63 : (63 : ZMod p) = 0 := by linear_combination -h0
    have hdvd := (ZMod.natCast_eq_zero_iff 63 p).mp (by simpa using h63)
    have h63f : 63 = 3 * (3 * 7) := by norm_num
    rw [h63f] at hdvd
    rcases hp.dvd_mul.mp hdvd with h3 | h21
    · have := Nat.le_of_dvd (by decide) h3; omega
    · rcases hp.dvd_mul.mp h21 with h3 | h7d
      · have := Nat.le_of_dvd (by decide) h3; omega
      · have := Nat.le_of_dvd (by decide) h7d
        have : p = 7 := by interval_cases p <;> simp_all [Nat.Prime]
        exact h7 this
  -- Relate the sums to evaluations of polyR0, theta polyR0, theta (theta polyR0), polyR1, polyR2 at 64!
  have h64_cancel : ∀ k : ℕ, ((64 : ZMod p)⁻¹) ^ k * (64 : ZMod p) ^ k = 1 := fun k => by
    rw [← mul_pow, inv_mul_cancel₀ h64ne, one_pow]
  have hev_R0 : (polyR0 p).eval 64 =
      ∑ k ∈ Finset.range (m + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod p) ^ 3 := by
    simp only [polyR0, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine Finset.sum_congr rfl fun k _ => by rw [mul_assoc, h64_cancel, mul_one]
  have hnatDeg_sum_le : ∀ {n : ℕ} (f : ℕ → ZMod p),
      (∑ k ∈ Finset.range (n + 1), C (f k) * Polynomial.X ^ k).natDegree ≤ n := by
    intro n f
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    rw [Finset.mem_range] at hk
    calc (C (f k) * Polynomial.X ^ k).natDegree
        ≤ (C (f k)).natDegree + (Polynomial.X ^ k).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + k := Nat.add_le_add (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le k)
      _ ≤ n := by omega
  have hev_tR0 : (theta (polyR0 p)).eval 64 =
      ∑ k ∈ Finset.range (m + 1), (k : ZMod p) * ((Nat.choose (2 * k) k : ℕ) : ZMod p) ^ 3 := by
    rw [Polynomial.eval_eq_sum_range' (n := m + 1) (by
      calc (theta (polyR0 p)).natDegree ≤ (polyR0 p).natDegree := theta_natDegree_le _
        _ ≤ m := hnatDeg_sum_le _
        _ < m + 1 := by omega)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [theta_coeff]
    have hc : (polyR0 p).coeff k = ((Nat.choose (2 * k) k : ZMod p) ^ 3) * ((64 : ZMod p)⁻¹) ^ k := by
      simp only [polyR0, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk)]
    rw [hc]; calc (k : ZMod p) * (((Nat.choose (2 * k) k : ZMod p) ^ 3) * (64 : ZMod p)⁻¹ ^ k) * 64 ^ k
        = (k : ZMod p) * ((Nat.choose (2 * k) k : ZMod p) ^ 3) * ((64 : ZMod p)⁻¹ ^ k * 64 ^ k) := by ring
      _ = (k : ZMod p) * ((Nat.choose (2 * k) k : ZMod p) ^ 3) := by rw [h64_cancel, mul_one]
  have hev_t2R0 : (theta (theta (polyR0 p))).eval 64 =
      ∑ k ∈ Finset.range (m + 1), (k : ZMod p) ^ 2 * ((Nat.choose (2 * k) k : ℕ) : ZMod p) ^ 3 := by
    rw [Polynomial.eval_eq_sum_range' (n := m + 1) (by
      calc (theta (theta (polyR0 p))).natDegree ≤ (theta (polyR0 p)).natDegree := theta_natDegree_le _
        _ ≤ (polyR0 p).natDegree := theta_natDegree_le _
        _ ≤ m := hnatDeg_sum_le _
        _ < m + 1 := by omega)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [theta_coeff, theta_coeff]
    have hc : (polyR0 p).coeff k = ((Nat.choose (2 * k) k : ZMod p) ^ 3) * ((64 : ZMod p)⁻¹) ^ k := by
      simp only [polyR0, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk)]
    rw [hc]
    calc (k : ZMod p) * ((k : ZMod p) * (((Nat.choose (2 * k) k : ZMod p) ^ 3) * (64 : ZMod p)⁻¹ ^ k)) * 64 ^ k
        = (k : ZMod p) ^ 2 * ((Nat.choose (2 * k) k : ZMod p) ^ 3) * ((64 : ZMod p)⁻¹ ^ k * 64 ^ k) := by ring
      _ = (k : ZMod p) ^ 2 * ((Nat.choose (2 * k) k : ZMod p) ^ 3) := by rw [h64_cancel, mul_one]
  have hev_R1 : (polyR1 p).eval 64 =
      6 * ∑ k ∈ Finset.range (m + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod p) ^ 3 * (H1p p (2 * k) - H1p p k) := by
    simp only [polyR1, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc ((Nat.choose (2 * k) k : ZMod p) ^ 3) * (6 * (H1p p (2 * k) - H1p p k)) * (64 : ZMod p)⁻¹ ^ k * 64 ^ k
        = 6 * (((Nat.choose (2 * k) k : ZMod p) ^ 3) * (H1p p (2 * k) - H1p p k)) * ((64 : ZMod p)⁻¹ ^ k * 64 ^ k) := by ring
      _ = 6 * (((Nat.choose (2 * k) k : ZMod p) ^ 3) * (H1p p (2 * k) - H1p p k)) := by rw [h64_cancel, mul_one]
  have hev_R2 : (polyR2 p).eval 64 =
      ∑ k ∈ Finset.range (m + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod p) ^ 3 *
        (18 * (H1p p (2 * k) - H1p p k) ^ 2 - 6 * H2p p (2 * k) + 3 * H2p p k) := by
    simp only [polyR2, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine Finset.sum_congr rfl fun k _ => by rw [mul_assoc, h64_cancel, mul_one]
  -- Degree bounds on polyR0, polyR1, polyR2: all ≤ m!
  have hdeg_R0 : (polyR0 p).natDegree ≤ m := hnatDeg_sum_le _
  have hdeg_R1 : (polyR1 p).natDegree ≤ m := hnatDeg_sum_le _
  have hdeg_R2 : (polyR2 p).natDegree ≤ m := hnatDeg_sum_le _
  have hc0_R0 : (polyR0 p).coeff 0 = 1 := by simp [polyR0]
  have hc0_R1 : (polyR1 p).coeff 0 = 0 := by simp [polyR1, H1p]
  have hc0_R2 : (polyR2 p).coeff 0 = 0 := by simp [polyR2, H1p, H2p]
  obtain ⟨hLR0, hLR1, hLR2⟩ := polyR_odes hp h5
  -- Now split on p % 4 = 1 vs p % 4 = 3!
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hfinish : ∀ (a_num : ℕ) (mult g0 h1 : Polynomial (ZMod p)),
      (a_num = 1 ∧ mult = 1 ∨ a_num = 3 ∧ mult = 1 - Polynomial.X) →
      polyR0 p = mult * g0 * g0 →
      polyR1 p = 2 * mult * g0 * h1 →
      polyR2 p = 2 * mult * h1 * h1 →
      (g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0) ^ 2 = (1 - Polynomial.X) ^ (p - a_num) →
      (∑ q ∈ Finset.range (m + 1), (q : ZMod p) * ((Nat.choose (2 * q) q : ℕ) : ZMod p) ^ 3) = 0 ∧
      (∑ r ∈ Finset.range (m + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod p) ^ 3 * (H1p p (2 * r) - H1p p r)) = 0 ∧
      (∑ q ∈ Finset.range (m + 1), (q : ZMod p) ^ 2 * ((Nat.choose (2 * q) q : ℕ) : ZMod p) ^ 3) *
      (∑ r ∈ Finset.range (m + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod p) ^ 3 *
        (18 * (H1p p (2 * r) - H1p p r) ^ 2 - 6 * H2p p (2 * r) + 3 * H2p p r)) = 1 := by
    intro a_num mult g0 h1 hcase hR0eq hR1eq hR2eq hWsq
    have hmult_ne : mult.eval 64 ≠ 0 := by
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simp
      · simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
        rw [show (1 - 64 : ZMod p) = -63 by ring]
        exact h63ne
    have hg0_64 : g0.eval 64 = 0 := by
      have h0 : (polyR0 p).eval 64 = 0 := by rw [hev_R0, hA0]
      rw [hR0eq, Polynomial.eval_mul, Polynomial.eval_mul] at h0
      have hsq0 : g0.eval 64 * g0.eval 64 = 0 :=
        (mul_eq_zero.mp (by rw [← mul_assoc]; exact h0)).resolve_left hmult_ne
      exact mul_self_eq_zero.mp hsq0
    -- 1. S1 = (theta R0).eval 64 = 0!
    have hS1 : (theta (polyR0 p)).eval 64 = 0 := by
      rw [hR0eq]
      simp only [theta_mul, Polynomial.eval_add, Polynomial.eval_mul, hg0_64]
      ring
    -- 2. 6 * A1 = R1.eval 64 = 0 => A1 = 0!
    have hA1 : ∑ r ∈ Finset.range (m + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod p) ^ 3 * (H1p p (2 * r) - H1p p r) = 0 := by
      have h0 : (polyR1 p).eval 64 = 0 := by
        rw [hR1eq]
        simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, hg0_64]
        ring
      rw [hev_R1] at h0
      exact (mul_eq_zero.mp h0).resolve_left h6ne
    -- 3. (theta^2 R0).eval 64 * R2.eval 64 = 1!
    have hS2 : (theta (theta (polyR0 p))).eval 64 = 2 * mult.eval 64 * ((theta g0).eval 64) ^ 2 := by
      rw [hR0eq]
      simp only [theta_mul, theta_add, Polynomial.eval_add, Polynomial.eval_mul, hg0_64]
      ring
    have hB2 : (polyR2 p).eval 64 = 2 * mult.eval 64 * (h1.eval 64) ^ 2 := by
      rw [hR2eq]
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
      ring
    have hW64 : ((g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0) ^ 2).eval 64 =
        4 * (h1.eval 64) ^ 2 * ((theta g0).eval 64) ^ 2 := by
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat, hg0_64]
      ring
    have hWval := congrArg (Polynomial.eval 64) hWsq
    rw [hW64] at hWval
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X] at hWval
    have h1sub64 : (1 - 64 : ZMod p) = -63 := by ring
    rw [h1sub64] at hWval
    have hprod : (theta (theta (polyR0 p))).eval 64 * (polyR2 p).eval 64 = 1 := by
      rw [hS2, hB2]
      have hmult_sq : (mult.eval 64) ^ 2 = (-63 : ZMod p) ^ (a_num - 1) := by
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp
        · simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
          rw [h1sub64]
      calc 2 * mult.eval 64 * (theta g0).eval 64 ^ 2 * (2 * mult.eval 64 * h1.eval 64 ^ 2)
          = (mult.eval 64) ^ 2 * (4 * (h1.eval 64) ^ 2 * ((theta g0).eval 64) ^ 2) := by ring
        _ = (-63 : ZMod p) ^ (a_num - 1) * (-63 : ZMod p) ^ (p - a_num) := by rw [hmult_sq, hWval]
        _ = (-63 : ZMod p) ^ (p - 1) := by
              rw [← pow_add, show (a_num - 1) + (p - a_num) = p - 1 by rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega]
        _ = 1 := ZMod.pow_card_sub_one_eq_one h63ne
    exact ⟨by rw [← hev_tR0]; exact hS1, hA1, by rw [← hev_t2R0, ← hev_R2]; exact hprod⟩
  -- Execute both cases p % 4 = 1 and p % 4 = 3!
  rcases hmod4 with h41 | h43
  · -- Case p % 4 = 1: a_num = 1, d = (p - 1) / 4, mult = 1
    set d := (p - 1) / 4
    have hpa : 4 * d + 1 = p := by omega
    set g0 := polyG0 p 1 d
    set h1 := polyH1 p 1 d
    have hdeg_g0 : g0.natDegree ≤ d := hnatDeg_sum_le _
    have hdeg_h1 : h1.natDegree ≤ d := hnatDeg_sum_le _
    have hc0_g0 : g0.coeff 0 = 1 := by simp [g0, polyG0, pochCoeff]
    have hc0_h1 : h1.coeff 0 = 0 := by simp [h1, polyH1, logHarm]
    obtain ⟨hg0_raw, hh1_raw⟩ := polyG0_H1_odes hp h5 hpa (Or.inl rfl)
    have hg0_eq : 16 * (1 - Polynomial.X) * theta (theta g0) - 8 * Polynomial.X * theta g0 - Polynomial.X * g0 = 0 := by
      simpa only [Nat.cast_one, mul_one, one_pow, map_one, one_mul, map_ofNat] using hg0_raw
    have hh1_eq : 16 * (1 - Polynomial.X) * theta (theta h1) - 8 * Polynomial.X * theta h1 - Polynomial.X * h1 +
        16 * (1 - Polynomial.X) * theta g0 - 4 * Polynomial.X * g0 = 0 := by
      simpa only [Nat.cast_one, mul_one, one_pow, map_one, one_mul, map_ofNat] using hh1_raw
    obtain ⟨hL0, hL1, hL2⟩ := sym_sq_ode_mod4_eq1 g0 h1 hg0_eq hh1_eq
    have hR0eq : polyR0 p = 1 * g0 * g0 := by
      rw [one_mul]; apply sub_eq_zero.mp
      apply L3_unique_zero hp h5
      · calc (polyR0 p - g0 * g0).natDegree ≤ max (polyR0 p).natDegree (g0 * g0).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ max m (d + d) := by gcongr; exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add hdeg_g0 hdeg_g0)
          _ < p := by omega
      · rw [Polynomial.coeff_sub, hc0_R0, Polynomial.mul_coeff_zero, hc0_g0]; ring
      · rw [L3_sub, hLR0, hL0, sub_self]
    have hR1eq : polyR1 p = 2 * 1 * g0 * h1 := by
      rw [mul_one]; apply sub_eq_zero.mp
      apply L3_unique_zero hp h5
      · calc (polyR1 p - 2 * g0 * h1).natDegree ≤ max (polyR1 p).natDegree (2 * g0 * h1).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ max m (d + d) := by
              gcongr
              calc (2 * g0 * h1).natDegree ≤ (2 * g0).natDegree + h1.natDegree := Polynomial.natDegree_mul_le
                _ ≤ (2 : Polynomial (ZMod p)).natDegree + g0.natDegree + h1.natDegree := by gcongr; exact Polynomial.natDegree_mul_le
                _ ≤ 0 + d + d := by simp [Polynomial.natDegree_ofNat]; omega
                _ = d + d := by omega
          _ < p := by omega
      · rw [Polynomial.coeff_sub, hc0_R1, Polynomial.mul_coeff_zero, hc0_h1]; ring
      · rw [L3_sub]; rw [hR0eq, one_mul] at hLR1; linear_combination hLR1 - hL1
    have hR2eq : polyR2 p = 2 * 1 * h1 * h1 := by
      rw [mul_one]; apply sub_eq_zero.mp
      apply L3_unique_zero hp h5
      · calc (polyR2 p - 2 * h1 * h1).natDegree ≤ max (polyR2 p).natDegree (2 * h1 * h1).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ max m (d + d) := by
              gcongr
              calc (2 * h1 * h1).natDegree ≤ (2 * h1).natDegree + h1.natDegree := Polynomial.natDegree_mul_le
                _ ≤ (2 : Polynomial (ZMod p)).natDegree + h1.natDegree + h1.natDegree := by gcongr; exact Polynomial.natDegree_mul_le
                _ ≤ 0 + d + d := by simp [Polynomial.natDegree_ofNat]; omega
                _ = d + d := by omega
          _ < p := by omega
      · rw [Polynomial.coeff_sub, hc0_R2, Polynomial.mul_coeff_zero, hc0_h1]; ring
      · rw [L3_sub]; rw [hR0eq, one_mul, hR1eq, mul_one] at hLR2; linear_combination hLR2 - hL2
    have hWode := wronskian_ode 1 g0 h1 hg0_raw hh1_raw
    have hWdeg : (g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0).natDegree ≤ (p - 1) / 2 := by
      have hd1 : (g0 * g0).natDegree ≤ 2 * d := (Polynomial.natDegree_mul_le).trans (by omega)
      have hd2 : (2 * g0 * theta h1).natDegree ≤ 2 * d := by
        calc (2 * g0 * theta h1).natDegree ≤ (2 * g0).natDegree + (theta h1).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (2 : Polynomial (ZMod p)).natDegree + g0.natDegree + h1.natDegree := by
              gcongr; exact Polynomial.natDegree_mul_le; exact theta_natDegree_le _
          _ ≤ 2 * d := by simp [Polynomial.natDegree_ofNat]; omega
      have hd3 : (2 * h1 * theta g0).natDegree ≤ 2 * d := by
        calc (2 * h1 * theta g0).natDegree ≤ (2 * h1).natDegree + (theta g0).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (2 : Polynomial (ZMod p)).natDegree + h1.natDegree + g0.natDegree := by
              gcongr; exact Polynomial.natDegree_mul_le; exact theta_natDegree_le _
          _ ≤ 2 * d := by simp [Polynomial.natDegree_ofNat]; omega
      calc (g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0).natDegree
          ≤ max (g0 * g0 + 2 * g0 * theta h1).natDegree (2 * h1 * theta g0).natDegree := Polynomial.natDegree_sub_le _ _
        _ ≤ max (max (g0 * g0).natDegree (2 * g0 * theta h1).natDegree) (2 * h1 * theta g0).natDegree := by
            gcongr; exact Polynomial.natDegree_add_le _ _
        _ ≤ (p - 1) / 2 := by omega
    have hWc0 : (g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0).coeff 0 = 1 := by
      simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.mul_coeff_zero, theta_coeff, hc0_g0, hc0_h1]
    have hWsq := wronskian_sq_eq hp h5 1 (Or.inl rfl) _ hWdeg hWc0 hWode
    exact hfinish 1 1 g0 h1 (Or.inl ⟨rfl, rfl⟩) hR0eq hR1eq hR2eq hWsq
  · -- Case p % 4 = 3: a_num = 3, d = (p - 3) / 4, mult = 1 - X
    set d := (p - 3) / 4
    have hpa : 4 * d + 3 = p := by omega
    set g0 := polyG0 p 3 d
    set h1 := polyH1 p 3 d
    have hdeg_g0 : g0.natDegree ≤ d := hnatDeg_sum_le _
    have hdeg_h1 : h1.natDegree ≤ d := hnatDeg_sum_le _
    have hc0_g0 : g0.coeff 0 = 1 := by simp [g0, polyG0, pochCoeff]
    have hc0_h1 : h1.coeff 0 = 0 := by simp [h1, polyH1, logHarm]
    have h1x_deg : (1 - Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 1 := by compute_degree!
    obtain ⟨hg0_raw, hh1_raw⟩ := polyG0_H1_odes hp h5 hpa (Or.inr rfl)
    have hC24 : C (8 * ((3 : ℕ) : ZMod p)) = (24 : Polynomial (ZMod p)) := by
      rw [Nat.cast_ofNat, show (8 * (3 : ZMod p)) = 24 by norm_num, map_ofNat]
    have hC9 : C (((3 : ℕ) : ZMod p) ^ 2) = (9 : Polynomial (ZMod p)) := by
      rw [Nat.cast_ofNat, show ((3 : ZMod p) ^ 2) = 9 by norm_num, map_ofNat]
    have hC12 : C (4 * ((3 : ℕ) : ZMod p)) = (12 : Polynomial (ZMod p)) := by
      rw [Nat.cast_ofNat, show (4 * (3 : ZMod p)) = 12 by norm_num, map_ofNat]
    have hg0_eq : 16 * (1 - Polynomial.X) * theta (theta g0) - 24 * Polynomial.X * theta g0 - 9 * Polynomial.X * g0 = 0 := by
      simpa only [hC24, hC9] using hg0_raw
    have hh1_eq : 16 * (1 - Polynomial.X) * theta (theta h1) - 24 * Polynomial.X * theta h1 - 9 * Polynomial.X * h1 +
        16 * (1 - Polynomial.X) * theta g0 - 12 * Polynomial.X * g0 = 0 := by
      simpa only [hC24, hC9, hC12] using hh1_raw
    obtain ⟨hL0, hL1, hL2⟩ := sym_sq_ode_mod4_eq3 g0 h1 hg0_eq hh1_eq
    have hR0eq : polyR0 p = (1 - Polynomial.X) * g0 * g0 := by
      apply sub_eq_zero.mp
      apply L3_unique_zero hp h5
      · calc (polyR0 p - (1 - Polynomial.X) * g0 * g0).natDegree
            ≤ max (polyR0 p).natDegree ((1 - Polynomial.X) * g0 * g0).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ max m (1 + d + d) := by
              gcongr
              calc ((1 - Polynomial.X) * g0 * g0).natDegree ≤ ((1 - Polynomial.X) * g0).natDegree + g0.natDegree := Polynomial.natDegree_mul_le
                _ ≤ (1 - Polynomial.X : Polynomial (ZMod p)).natDegree + g0.natDegree + g0.natDegree := by gcongr; exact Polynomial.natDegree_mul_le
                _ ≤ 1 + d + d := by omega
          _ < p := by omega
      · rw [Polynomial.coeff_sub, hc0_R0, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero, hc0_g0]
        simp
      · rw [L3_sub, hLR0, hL0, sub_self]
    have hR1eq : polyR1 p = 2 * (1 - Polynomial.X) * g0 * h1 := by
      apply sub_eq_zero.mp
      apply L3_unique_zero hp h5
      · calc (polyR1 p - 2 * (1 - Polynomial.X) * g0 * h1).natDegree
            ≤ max (polyR1 p).natDegree (2 * (1 - Polynomial.X) * g0 * h1).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ max m (1 + d + d) := by
              gcongr
              calc (2 * (1 - Polynomial.X) * g0 * h1).natDegree ≤ (2 * (1 - Polynomial.X) * g0).natDegree + h1.natDegree := Polynomial.natDegree_mul_le
                _ ≤ (2 * (1 - Polynomial.X : Polynomial (ZMod p))).natDegree + g0.natDegree + h1.natDegree := by gcongr; exact Polynomial.natDegree_mul_le
                _ ≤ (2 : Polynomial (ZMod p)).natDegree + (1 - Polynomial.X : Polynomial (ZMod p)).natDegree + g0.natDegree + h1.natDegree := by gcongr; exact Polynomial.natDegree_mul_le
                _ ≤ 1 + d + d := by simp [Polynomial.natDegree_ofNat]; omega
          _ < p := by omega
      · rw [Polynomial.coeff_sub, hc0_R1, Polynomial.mul_coeff_zero, hc0_h1]; ring
      · rw [L3_sub]; rw [hR0eq] at hLR1; linear_combination hLR1 - hL1
    have hR2eq : polyR2 p = 2 * (1 - Polynomial.X) * h1 * h1 := by
      apply sub_eq_zero.mp
      apply L3_unique_zero hp h5
      · calc (polyR2 p - 2 * (1 - Polynomial.X) * h1 * h1).natDegree
            ≤ max (polyR2 p).natDegree (2 * (1 - Polynomial.X) * h1 * h1).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ max m (1 + d + d) := by
              gcongr
              calc (2 * (1 - Polynomial.X) * h1 * h1).natDegree ≤ (2 * (1 - Polynomial.X) * h1).natDegree + h1.natDegree := Polynomial.natDegree_mul_le
                _ ≤ (2 * (1 - Polynomial.X : Polynomial (ZMod p))).natDegree + h1.natDegree + h1.natDegree := by gcongr; exact Polynomial.natDegree_mul_le
                _ ≤ (2 : Polynomial (ZMod p)).natDegree + (1 - Polynomial.X : Polynomial (ZMod p)).natDegree + h1.natDegree + h1.natDegree := by gcongr; exact Polynomial.natDegree_mul_le
                _ ≤ 1 + d + d := by simp [Polynomial.natDegree_ofNat]; omega
          _ < p := by omega
      · rw [Polynomial.coeff_sub, hc0_R2, Polynomial.mul_coeff_zero, hc0_h1]; ring
      · rw [L3_sub]; rw [hR0eq, hR1eq] at hLR2; linear_combination hLR2 - hL2
    have hWode := wronskian_ode 3 g0 h1 hg0_raw hh1_raw
    have hWdeg : (g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0).natDegree ≤ (p - 3) / 2 := by
      have hd1 : (g0 * g0).natDegree ≤ 2 * d := (Polynomial.natDegree_mul_le).trans (by omega)
      have hd2 : (2 * g0 * theta h1).natDegree ≤ 2 * d := by
        calc (2 * g0 * theta h1).natDegree ≤ (2 * g0).natDegree + (theta h1).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (2 : Polynomial (ZMod p)).natDegree + g0.natDegree + h1.natDegree := by
              gcongr; exact Polynomial.natDegree_mul_le; exact theta_natDegree_le _
          _ ≤ 2 * d := by simp [Polynomial.natDegree_ofNat]; omega
      have hd3 : (2 * h1 * theta g0).natDegree ≤ 2 * d := by
        calc (2 * h1 * theta g0).natDegree ≤ (2 * h1).natDegree + (theta g0).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (2 : Polynomial (ZMod p)).natDegree + h1.natDegree + g0.natDegree := by
              gcongr; exact Polynomial.natDegree_mul_le; exact theta_natDegree_le _
          _ ≤ 2 * d := by simp [Polynomial.natDegree_ofNat]; omega
      calc (g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0).natDegree
          ≤ max (g0 * g0 + 2 * g0 * theta h1).natDegree (2 * h1 * theta g0).natDegree := Polynomial.natDegree_sub_le _ _
        _ ≤ max (max (g0 * g0).natDegree (2 * g0 * theta h1).natDegree) (2 * h1 * theta g0).natDegree := by
            gcongr; exact Polynomial.natDegree_add_le _ _
        _ ≤ (p - 3) / 2 := by omega
    have hWc0 : (g0 * g0 + 2 * g0 * theta h1 - 2 * h1 * theta g0).coeff 0 = 1 := by
      simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.mul_coeff_zero, theta_coeff, hc0_g0, hc0_h1]
    have hWsq := wronskian_sq_eq hp h5 3 (Or.inr rfl) _ hWdeg hWc0 hWode
    exact hfinish 3 (1 - Polynomial.X) g0 h1 (Or.inr ⟨rfl, rfl⟩) hR0eq hR1eq hR2eq hWsq

end OMA_A79727_P4


namespace OMA_A79727_Glue

private lemma cast_inv_p3_to_p {p j : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) (hjp : j < p) :
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p) ((j : ZMod (p ^ 3))⁻¹) =
      (j : ZMod p)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hju : (j : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    rw [ZMod.isUnit_iff_coprime]
    exact ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjp)).symm).pow_right 3
  have h1 := congrArg (ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)) hju
  simp only [map_mul, map_natCast, map_one] at h1
  have hjne : (j : ZMod p) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.natCast_eq_zero_iff j p).mp h0
    have := Nat.le_of_dvd (by omega) hdvd; omega
  exact mul_left_cancel₀ hjne (by rw [h1, mul_inv_cancel₀ hjne])

private lemma cast_H1_p3_to_p {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p) (OMA_A79727.H1 p k) =
      OMA_A79727_P4.H1p p k := by
  simp only [OMA_A79727.H1, OMA_A79727_P4.H1p, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  exact cast_inv_p3_to_p hp hj.1 (by omega)

private lemma cast_H2_p3_to_p {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p) (OMA_A79727.H2 p k) =
      OMA_A79727_P4.H2p p k := by
  simp only [OMA_A79727.H2, OMA_A79727_P4.H2p, map_sum, map_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [cast_inv_p3_to_p hp hj.1 (by omega)]

private lemma eq_mul_of_castHom_eq_zero {p k d : ℕ} (hp : p.Prime) (hd : d ∣ p ^ k)
    (x : ZMod (p ^ k)) (hx : ZMod.castHom hd (ZMod d) x = 0) :
    ∃ t : ZMod (p ^ k), x = (d : ZMod (p ^ k)) * t := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hdvd : d ∣ x.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h1 : ZMod.castHom hd (ZMod d) ((x.val : ℕ) : ZMod (p ^ k)) = (x.val : ZMod d) := map_natCast _ _
    rw [ZMod.natCast_zmod_val] at h1
    rw [← h1, hx]
  rcases hdvd with ⟨u, hu⟩
  refine ⟨(u : ZMod (p ^ k)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hu, Nat.cast_mul]

private lemma conj2_zmod_ge_5 {p : ℕ} (hp : OeisA3625.A p) (h3 : p ≠ 3) :
    (OeisA79727.a (p * (p - 1)) : ZMod (p ^ 3)) = ((p ^ 2 : ℕ) : ZMod (p ^ 3)) := by
  obtain ⟨hpr, h5, h7, _, hmod⟩ := OMA_A79727.a3625_props hp h3
  have hleg := OMA_A79727.neg_seven_pow_half_eq_neg_one hpr h5 hmod
  have hHp := OMA_A79727_P2.hasse_inv_eq_zero hpr h5 hleg
  have hA0_p2 := OMA_A79727_P3.A0_eq_zero_zmod_p_sq hpr h5 hleg hHp
  have hA0_p : ∑ k ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod p) ^ 3 = 0 := by
    have h := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) hA0_p2
    simpa only [map_sum, map_pow, map_natCast, map_zero] using h
  obtain ⟨hS1_p, hA1_p, hSB_p⟩ := OMA_A79727_P4.part4_main hpr h5 h7 hA0_p
  set m := (p - 1) / 2
  set A0_3 : ZMod (p ^ 3) := ∑ q ∈ Finset.range (m + 1), ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3
  set S1_3 : ZMod (p ^ 3) := ∑ q ∈ Finset.range (m + 1), (q : ZMod (p ^ 3)) * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3
  set A1_3 : ZMod (p ^ 3) := ∑ r ∈ Finset.range (m + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 *
      (OMA_A79727.H1 p (2 * r) - OMA_A79727.H1 p r)
  set S2_3 : ZMod (p ^ 3) := ∑ q ∈ Finset.range (m + 1), (q : ZMod (p ^ 3)) ^ 2 * ((Nat.choose (2 * q) q : ℕ) : ZMod (p ^ 3)) ^ 3
  set B2_3 : ZMod (p ^ 3) := ∑ r ∈ Finset.range (m + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod (p ^ 3)) ^ 3 *
      (18 * (OMA_A79727.H1 p (2 * r) - OMA_A79727.H1 p r) ^ 2 - 6 * OMA_A79727.H2 p (2 * r) + 3 * OMA_A79727.H2 p r)
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hdvd23 : p ^ 2 ∣ p ^ 3 := ⟨p, by ring⟩
  have hdvd13 : p ∣ p ^ 3 := dvd_pow_self p (by decide : 3 ≠ 0)
  have hA0_sq : A0_3 ^ 2 = 0 := by
    have hc : ZMod.castHom hdvd23 (ZMod (p ^ 2)) A0_3 = 0 := by
      simp only [A0_3, map_sum, map_pow, map_natCast]
      exact hA0_p2
    obtain ⟨t0, ht0⟩ := eq_mul_of_castHom_eq_zero hpr hdvd23 A0_3 hc
    rw [ht0, Nat.cast_pow]
    linear_combination (p : ZMod (p ^ 3)) * t0 ^ 2 * hp3
  have hS1A1 : 6 * (p : ZMod (p ^ 3)) * S1_3 * A1_3 = 0 := by
    have hcS1 : ZMod.castHom hdvd13 (ZMod p) S1_3 = 0 := by
      simp only [S1_3, map_sum, map_mul, map_pow, map_natCast]
      exact hS1_p
    have hcA1 : ZMod.castHom hdvd13 (ZMod p) A1_3 = 0 := by
      simp only [A1_3, map_sum, map_mul, map_pow, map_sub, map_natCast]
      rw [Finset.sum_congr rfl fun r hr => ?_]
      · exact hA1_p
      · rw [Finset.mem_range] at hr
        rw [cast_H1_p3_to_p hpr (by omega), cast_H1_p3_to_p hpr (by omega)]
    obtain ⟨t1, ht1⟩ := eq_mul_of_castHom_eq_zero hpr hdvd13 S1_3 hcS1
    obtain ⟨t2, ht2⟩ := eq_mul_of_castHom_eq_zero hpr hdvd13 A1_3 hcA1
    rw [ht1, ht2]
    linear_combination 6 * t1 * t2 * hp3
  have hS2B2 : (p : ZMod (p ^ 3)) ^ 2 * S2_3 * B2_3 = (p : ZMod (p ^ 3)) ^ 2 := by
    have hcS2 : ZMod.castHom hdvd13 (ZMod p) S2_3 =
        ∑ q ∈ Finset.range (m + 1), (q : ZMod p) ^ 2 * ((Nat.choose (2 * q) q : ℕ) : ZMod p) ^ 3 := by
      simp only [S2_3, map_sum, map_mul, map_pow, map_natCast]
    have hcB2 : ZMod.castHom hdvd13 (ZMod p) B2_3 =
        ∑ r ∈ Finset.range (m + 1), ((Nat.choose (2 * r) r : ℕ) : ZMod p) ^ 3 *
          (18 * (OMA_A79727_P4.H1p p (2 * r) - OMA_A79727_P4.H1p p r) ^ 2 -
            6 * OMA_A79727_P4.H2p p (2 * r) + 3 * OMA_A79727_P4.H2p p r) := by
      simp only [B2_3, map_sum, map_mul, map_pow, map_add, map_sub, map_natCast, map_ofNat]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_range] at hr
      rw [cast_H1_p3_to_p hpr (by omega), cast_H1_p3_to_p hpr (by omega),
          cast_H2_p3_to_p hpr (by omega), cast_H2_p3_to_p hpr (by omega)]
    have hcSB : ZMod.castHom hdvd13 (ZMod p) (S2_3 * B2_3 - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hcS2, hcB2, hSB_p, sub_self]
    obtain ⟨t3, ht3⟩ := eq_mul_of_castHom_eq_zero hpr hdvd13 (S2_3 * B2_3 - 1) hcSB
    linear_combination (p : ZMod (p ^ 3)) ^ 2 * ht3 + t3 * hp3
  have hblk := OMA_A79727.a_p_mul_p_sub_one_eq_block_sum hpr h5
  change (OeisA79727.a (p * (p - 1)) : ZMod (p ^ 3)) =
    A0_3 ^ 2 + 6 * (p : ZMod (p ^ 3)) * S1_3 * A1_3 + (p : ZMod (p ^ 3)) ^ 2 * S2_3 * B2_3 at hblk
  rw [hblk, hA0_sq, hS1A1, hS2B2, zero_add, zero_add, Nat.cast_pow]

end OMA_A79727_Glue


theorem OMA.solution : type_of% @OeisA79727.conjecture2 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3
    decide
  · exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (OMA_A79727_Glue.conj2_zmod_ge_5 hp h3)
