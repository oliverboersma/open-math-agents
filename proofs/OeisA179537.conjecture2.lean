import FormalConjectures.OEIS.«179537»

/-!
# Proof of OeisA179537.conjecture2

Proves Zhi-Wei Sun's 2010 conjecture that for every prime `p ≠ 7` with `(p / 7) = -1`,
`∑ k ∈ range p, (-1) ^ k * a(k) ≡ 0 [ZMOD p ^ 2]`, where
`a(n) = ∑ k ∈ range (n + 1), C(n, k) ^ 2 * C(n - k, k) ^ 2 * (-16) ^ k`.

Method:
1. Elementary 1-variable power-series identity and involution `u = -X / (1 + X)` in
   `PowerSeries (ZMod p)` and `v = 2X / (1 - X)` in `PowerSeries (ZMod (p ^ 2))` showing
   `(-16) ^ k * ∑ n < p, (-1) ^ n * C(n, 2k) ^ 2 ≡ C(2k, k) (mod p ^ 2)` for all `2k < p`,
   which reduces `∑ n < p, (-1) ^ n * a(n)` to `∑ k ≤ (p - 1) / 2, C(2k, k) ^ 3 (mod p ^ 2)`.
2. Explicit degree-2 CM endomorphism in `PowerSeries (Quad7 (ZMod p))` showing the Hasse
   invariant of the supersingular elliptic curve `y ^ 2 = (x + 21) * (x ^ 2 + 7)` vanishes.
3. Exact 2-isogeny and pure integer 3rd-order ODE for `P_m(1 + 2t) ^ 2` proving
   `∑ k ≤ (p - 1) / 2, C(2k, k) ^ 3 ≡ 0 (mod p ^ 2)`.

Credit: Daniel Whorlow (@draonbioetl)
-/

-- Credit: Daniel Whorlow (@draonbioetl)

section OMA_A179537_P23

open scoped BigOperators
open Finset Polynomial

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

end OMA_A179537_P23

namespace OMA_A179537_Red

open scoped BigOperators

private lemma choose_mul_choose_sub (n k : ℕ) :
    n.choose k * (n - k).choose k = n.choose (2 * k) * (2 * k).choose k := by
  by_cases h : 2 * k ≤ n
  · have h1 := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
    rw [show 2 * k - k = k by omega] at h1
    exact h1.symm
  · have h1 : n.choose (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, zero_mul]
    by_cases hk : k ≤ n
    · have h2 : (n - k).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h2, mul_zero]
    · have h2 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h2, zero_mul]

private lemma sum_a_swap {p : ℕ} (hp : 3 ≤ p) :
    ((∑ n ∈ Finset.range p, (-1 : ℤ) ^ n * OeisA179537.a n : ℤ) : ZMod (p ^ 2)) =
    ∑ k ∈ Finset.range ((p - 1) / 2 + 1),
      (-16 : ZMod (p ^ 2)) ^ k * ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 2 *
      (∑ n ∈ Finset.range p, (-1 : ZMod (p ^ 2)) ^ n * ((Nat.choose n (2 * k) : ℕ) : ZMod (p ^ 2)) ^ 2) := by
  have hcast : ((∑ n ∈ Finset.range p, (-1 : ℤ) ^ n * OeisA179537.a n : ℤ) : ZMod (p ^ 2)) =
      ∑ n ∈ Finset.range p, (-1 : ZMod (p ^ 2)) ^ n *
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.choose n k : ℕ) : ZMod (p ^ 2)) ^ 2 *
          ((Nat.choose (n - k) k : ℕ) : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k := by
    simp only [OeisA179537.a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, Int.cast_ofNat]
  rw [hcast]
  have hrew : ∀ n ∈ Finset.range p,
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.choose n k : ℕ) : ZMod (p ^ 2)) ^ 2 *
        ((Nat.choose (n - k) k : ℕ) : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k =
      ∑ k ∈ Finset.range ((p - 1) / 2 + 1),
        ((Nat.choose n (2 * k) : ℕ) : ZMod (p ^ 2)) ^ 2 *
        ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hterm : ∀ k : ℕ,
        ((Nat.choose n k : ℕ) : ZMod (p ^ 2)) ^ 2 *
        ((Nat.choose (n - k) k : ℕ) : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k =
        ((Nat.choose n (2 * k) : ℕ) : ZMod (p ^ 2)) ^ 2 *
        ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k := by
      intro k
      have hmul := choose_mul_choose_sub n k
      have hsq : ((Nat.choose n k * (n - k).choose k : ℕ) : ZMod (p ^ 2)) ^ 2 =
          ((Nat.choose n (2 * k) * (2 * k).choose k : ℕ) : ZMod (p ^ 2)) ^ 2 := by
        rw [hmul]
      simp only [Nat.cast_mul, mul_pow] at hsq
      rw [hsq]
    simp_rw [hterm]
    trans (∑ k ∈ Finset.range p,
        ((Nat.choose n (2 * k) : ℕ) : ZMod (p ^ 2)) ^ 2 *
        ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 2 * (-16 : ZMod (p ^ 2)) ^ k)
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ hk
      rw [Finset.mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ hk
      rw [Finset.mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [Finset.sum_congr rfl fun n hn => by rw [hrew n hn]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

private noncomputable def Qpoly {R : Type*} [CommRing R] (p r : ℕ) : PowerSeries R :=
  ∑ n ∈ Finset.range p,
    PowerSeries.C ((-1 : R) ^ n * (Nat.choose n r : R)) * (1 + PowerSeries.X) ^ n

private lemma coeff_one_add_X_pow {R : Type*} [CommRing R] (n r : ℕ) :
    PowerSeries.coeff r ((1 + PowerSeries.X : PowerSeries R) ^ n) = (Nat.choose n r : R) := by
  rw [add_comm, add_pow, map_sum]
  rw [Finset.sum_eq_single r]
  · simp only [one_pow, mul_one, ← map_natCast PowerSeries.C, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_X_pow_self, one_mul]
  · intro b _ hbr
    simp only [one_pow, mul_one, ← map_natCast PowerSeries.C, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_X_pow, if_neg (Ne.symm hbr), zero_mul]
  · intro hr
    rw [Finset.mem_range] at hr
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma coeff_Qpoly {R : Type*} [CommRing R] (p r : ℕ) :
    PowerSeries.coeff r (Qpoly (R := R) p r) =
    ∑ n ∈ Finset.range p, (-1 : R) ^ n * (Nat.choose n r : R) ^ 2 := by
  unfold Qpoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_C_mul, coeff_one_add_X_pow]
  ring

private lemma Qpoly_base {R : Type*} [CommRing R] {p : ℕ} (hodd : Odd p) :
    (2 + PowerSeries.X) * Qpoly (R := R) p 0 = 1 + (1 + PowerSeries.X) ^ p := by
  unfold Qpoly
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
  have h2 : (2 + PowerSeries.X : PowerSeries R) = 1 + (1 + PowerSeries.X) := by ring
  rw [h2, add_mul, one_mul, Finset.mul_sum]
  have hstep : ∑ n ∈ Finset.range p,
        (1 + PowerSeries.X) * (PowerSeries.C ((-1 : R) ^ n) * (1 + PowerSeries.X) ^ n) =
      -(∑ n ∈ Finset.range p,
        PowerSeries.C ((-1 : R) ^ (n + 1)) * (1 + PowerSeries.X) ^ (n + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pow_succ, pow_succ, map_mul, map_neg, map_one]
    ring
  rw [hstep, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_sub' (fun n => PowerSeries.C ((-1 : R) ^ n) * (1 + PowerSeries.X) ^ n) p]
  rw [pow_zero, pow_zero, map_one, mul_one, hodd.neg_one_pow, map_neg, map_one]
  ring

private lemma Qpoly_step {R : Type*} [CommRing R] {p : ℕ} (hodd : Odd p) (b : ℕ) :
    (2 + PowerSeries.X) * Qpoly (R := R) p (b + 1) +
    (1 + PowerSeries.X) * Qpoly (R := R) p b =
    PowerSeries.C (Nat.choose p (b + 1) : R) * (1 + PowerSeries.X) ^ p := by
  unfold Qpoly
  have h2 : (2 + PowerSeries.X : PowerSeries R) = 1 + (1 + PowerSeries.X) := by ring
  rw [h2, add_mul, one_mul, Finset.mul_sum, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  have hcomb : ∑ n ∈ Finset.range p,
        ((1 + PowerSeries.X) * (PowerSeries.C ((-1 : R) ^ n * (Nat.choose n (b + 1) : R)) * (1 + PowerSeries.X) ^ n) +
         (1 + PowerSeries.X) * (PowerSeries.C ((-1 : R) ^ n * (Nat.choose n b : R)) * (1 + PowerSeries.X) ^ n)) =
      -(∑ n ∈ Finset.range p,
        PowerSeries.C ((-1 : R) ^ (n + 1) * (Nat.choose (n + 1) (b + 1) : R)) * (1 + PowerSeries.X) ^ (n + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ, pow_succ]
    simp only [map_mul, map_add, map_neg, map_one]
    ring
  rw [hcomb, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_sub' (fun n => PowerSeries.C ((-1 : R) ^ n * (Nat.choose n (b + 1) : R)) * (1 + PowerSeries.X) ^ n) p]
  rw [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, map_zero, zero_mul, zero_sub,
    hodd.neg_one_pow, map_mul, map_neg, map_one]
  ring

private lemma Qpoly_closed {R : Type*} [CommRing R] {p : ℕ} (hodd : Odd p) (r : ℕ) :
    (2 + PowerSeries.X) ^ (r + 1) * Qpoly (R := R) p r =
    (-1 : PowerSeries R) ^ r * (1 + PowerSeries.X) ^ r * (1 + (1 + PowerSeries.X) ^ p) +
    (1 + PowerSeries.X) ^ p * ∑ j ∈ Finset.Icc 1 r,
      (-1 : PowerSeries R) ^ (r - j) * PowerSeries.C (Nat.choose p j : R) *
      (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j := by
  induction r with
  | zero =>
    simp [Qpoly_base hodd]
  | succ r ih =>
    have hstep := Qpoly_step (R := R) hodd r
    have hmul : (2 + PowerSeries.X) ^ (r + 2) * Qpoly (R := R) p (r + 1) =
        (2 + PowerSeries.X) ^ (r + 1) *
          (PowerSeries.C (Nat.choose p (r + 1) : R) * (1 + PowerSeries.X) ^ p) -
        (1 + PowerSeries.X) * ((2 + PowerSeries.X) ^ (r + 1) * Qpoly (R := R) p r) := by
      linear_combination (2 + PowerSeries.X) ^ (r + 1) * hstep
    rw [hmul, ih]
    have hIcc : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hsub : ∑ j ∈ Finset.Icc 1 r,
        (-1 : PowerSeries R) ^ (r + 1 - j) * PowerSeries.C (Nat.choose p j : R) *
        (1 + PowerSeries.X) ^ (r + 1 - j) * (2 + PowerSeries.X) ^ j =
      -(1 + PowerSeries.X) * ∑ j ∈ Finset.Icc 1 r,
        (-1 : PowerSeries R) ^ (r - j) * PowerSeries.C (Nat.choose p j : R) *
        (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have hexp : r + 1 - j = (r - j) + 1 := by omega
      rw [hexp, pow_succ, pow_succ]
      ring
    rw [hsub]
    simp only [Nat.sub_self, pow_zero, one_mul]
    rw [pow_succ (-1 : PowerSeries R), pow_succ (1 + PowerSeries.X)]
    ring

private lemma coeff_X_pow_mul_eq_zero {R : Type*} [CommRing R] {m d : ℕ} (h : d < m)
    (f : PowerSeries R) : PowerSeries.coeff d (PowerSeries.X ^ m * f) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  exact if_neg (by omega)

private lemma isUnit_two_zmod_pow {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (e : ℕ) :
    IsUnit (2 : ZMod (p ^ e)) := by
  have hcop : Nat.Coprime 2 (p ^ e) := by
    apply Nat.Coprime.pow_right
    have h2 : ¬ 2 ∣ p := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
      omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
  exact (ZMod.isUnit_iff_coprime 2 (p ^ e)).mpr hcop

private lemma isUnit_two_add_X {R : Type*} [CommRing R] (h2 : IsUnit (2 : R)) :
    IsUnit (2 + PowerSeries.X : PowerSeries R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simpa only [map_add, map_ofNat, PowerSeries.constantCoeff_X, add_zero] using h2

private lemma isUnit_one_add_X {R : Type*} [CommRing R] :
    IsUnit (1 + PowerSeries.X : PowerSeries R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

private lemma isUnit_one_sub_X {R : Type*} [CommRing R] :
    IsUnit (1 - PowerSeries.X : PowerSeries R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

private lemma choose_symm_nat {a b u : ℕ} (hua : u ≤ a) (hub : u ≤ b) :
    b.choose u * (a + b - u).choose b = a.choose u * (a + b - u).choose a := by
  have h1 := Nat.choose_mul (n := a + b - u) (k := b) (s := u) hub
  have h2 := Nat.choose_mul (n := a + b - u) (k := a) (s := u) hua
  have heq : a + b - u - u = (a - u) + (b - u) := by omega
  have h3 : (a + b - u - u).choose (b - u) = (a + b - u - u).choose (a - u) := by
    rw [heq, Nat.choose_symm_add]
  have ha : (a + b - u).choose b * b.choose u = (a + b - u).choose u * (a + b - u - u).choose (b - u) := h1
  have hb : (a + b - u).choose a * a.choose u = (a + b - u).choose u * (a + b - u - u).choose (a - u) := h2
  rw [mul_comm (b.choose u), mul_comm (a.choose u), ha, hb, h3]

private noncomputable def negBinomSeries {R : Type*} [CommRing R] (inv2 : R) (b : ℕ) : PowerSeries R :=
  PowerSeries.mk fun m => (-1 : R) ^ m * inv2 ^ (b + 1 + m) * (Nat.choose (b + m) b : R)

private lemma two_add_X_mul_negBinomSeries_zero {R : Type*} [CommRing R] {inv2 : R}
    (h2 : (2 : R) * inv2 = 1) :
    (2 + PowerSeries.X) * negBinomSeries inv2 0 = 1 := by
  ext m
  cases m with
  | zero =>
    simp only [add_mul, map_add, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_ofNat,
      PowerSeries.constantCoeff_X, zero_mul, add_zero, negBinomSeries, PowerSeries.constantCoeff_mk,
      pow_zero, one_mul, zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one, mul_one, map_one, h2]
  | succ m =>
    rw [add_mul, map_add, show (2 : PowerSeries R) = PowerSeries.C 2 from rfl,
      PowerSeries.coeff_C_mul, ← pow_one PowerSeries.X, PowerSeries.coeff_X_pow_mul',
      if_pos (by omega), show m + 1 - 1 = m by omega, PowerSeries.coeff_one]
    simp only [Nat.succ_ne_zero, ↓reduceIte, negBinomSeries, PowerSeries.coeff_mk,
      zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [pow_succ (-1 : R), show 1 + (m + 1) = (1 + m) + 1 by omega, pow_succ inv2 (1 + m)]
    calc 2 * ((-1 : R) ^ m * -1 * (inv2 ^ (1 + m) * inv2)) + (-1 : R) ^ m * inv2 ^ (1 + m)
        = (-1 : R) ^ m * inv2 ^ (1 + m) * (1 - (2 * inv2)) := by ring
      _ = 0 := by rw [h2]; ring

private lemma two_add_X_mul_negBinomSeries_succ {R : Type*} [CommRing R] {inv2 : R}
    (h2 : (2 : R) * inv2 = 1) (b : ℕ) :
    (2 + PowerSeries.X) * negBinomSeries inv2 (b + 1) = negBinomSeries inv2 b := by
  ext m
  cases m with
  | zero =>
    simp only [add_mul, map_add, show (2 : PowerSeries R) = PowerSeries.C 2 from rfl,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, add_zero, negBinomSeries,
      PowerSeries.coeff_mk, pow_zero, one_mul, add_zero, Nat.choose_self, Nat.cast_one, mul_one]
    rw [show b + 1 + 1 = (b + 1) + 1 by omega, pow_succ]
    calc 2 * (inv2 ^ (b + 1) * inv2) = (2 * inv2) * inv2 ^ (b + 1) := by ring
      _ = inv2 ^ (b + 1) := by rw [h2, one_mul]
  | succ m =>
    rw [add_mul, map_add, show (2 : PowerSeries R) = PowerSeries.C 2 from rfl,
      PowerSeries.coeff_C_mul, ← pow_one PowerSeries.X, PowerSeries.coeff_X_pow_mul',
      if_pos (by omega), show m + 1 - 1 = m by omega]
    simp only [negBinomSeries, PowerSeries.coeff_mk]
    have hpas : ((b + 1 + (m + 1)).choose (b + 1) : R) =
        ((b + (m + 1)).choose b : R) + ((b + 1 + m).choose (b + 1) : R) := by
      rw [show b + 1 + (m + 1) = (b + 1 + m) + 1 by omega, Nat.choose_succ_succ,
        show b + 1 + m = b + (m + 1) by omega, Nat.cast_add]
    rw [hpas]
    have he1 : b + 1 + 1 + (m + 1) = (b + 1 + (m + 1)) + 1 := by omega
    have he2 : b + 1 + 1 + m = b + 1 + (m + 1) := by omega
    rw [he1, he2, pow_succ inv2 (b + 1 + (m + 1)), pow_succ (-1 : R) m]
    linear_combination (-1 : R) ^ m * inv2 ^ (b + 1 + (m + 1)) *
      (-((b + (m + 1)).choose b : R) - ((b + 1 + m).choose (b + 1) : R)) * h2

private lemma negBinomSeries_eq_inv_pow {R : Type*} [CommRing R] {inv2 : R}
    (h2 : (2 : R) * inv2 = 1) (inv2X : PowerSeries R)
    (h2X : (2 + PowerSeries.X) * inv2X = 1) (b : ℕ) :
    negBinomSeries inv2 b = inv2X ^ (b + 1) := by
  induction b with
  | zero =>
    have h := two_add_X_mul_negBinomSeries_zero h2
    calc negBinomSeries inv2 0 = 1 * negBinomSeries inv2 0 := (one_mul _).symm
      _ = (inv2X * (2 + PowerSeries.X)) * negBinomSeries inv2 0 := by rw [mul_comm inv2X, h2X]
      _ = inv2X * ((2 + PowerSeries.X) * negBinomSeries inv2 0) := by ring
      _ = inv2X ^ 1 := by rw [h, mul_one, pow_one]
  | succ b ih =>
    have h := two_add_X_mul_negBinomSeries_succ h2 b
    calc negBinomSeries inv2 (b + 1) = 1 * negBinomSeries inv2 (b + 1) := (one_mul _).symm
      _ = (inv2X * (2 + PowerSeries.X)) * negBinomSeries inv2 (b + 1) := by rw [mul_comm inv2X, h2X]
      _ = inv2X * ((2 + PowerSeries.X) * negBinomSeries inv2 (b + 1)) := by ring
      _ = inv2X * negBinomSeries inv2 b := by rw [h]
      _ = inv2X ^ (b + 2) := by rw [ih, pow_succ']; ring

private lemma coeff_rat_symm {R : Type*} [CommRing R] {inv2 : R}
    (h2 : (2 : R) * inv2 = 1) (inv2X : PowerSeries R)
    (h2X : (2 + PowerSeries.X) * inv2X = 1) (a b : ℕ) :
    (-1 : R) ^ b * PowerSeries.coeff a ((1 + PowerSeries.X) ^ b * inv2X ^ (b + 1)) =
    (-1 : R) ^ a * PowerSeries.coeff b ((1 + PowerSeries.X) ^ a * inv2X ^ (a + 1)) := by
  have hform : ∀ x y : ℕ,
      (-1 : R) ^ y * PowerSeries.coeff x ((1 + PowerSeries.X) ^ y * inv2X ^ (y + 1)) =
      (-1 : R) ^ (x + y) * inv2 ^ (x + y + 1) *
        ∑ u ∈ Finset.range (min x y + 1),
          (-2 : R) ^ u * (Nat.choose y u : R) * (Nat.choose (x + y - u) y : R) := by
    intro x y
    rw [← negBinomSeries_eq_inv_pow h2 inv2X h2X y, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v =>
        PowerSeries.coeff u ((1 + PowerSeries.X : PowerSeries R) ^ y) *
        PowerSeries.coeff v (negBinomSeries inv2 y)) x]
    have hsub : ∑ u ∈ Finset.range (x + 1),
          PowerSeries.coeff u ((1 + PowerSeries.X : PowerSeries R) ^ y) *
          PowerSeries.coeff (x - u) (negBinomSeries inv2 y) =
        ∑ u ∈ Finset.range (min x y + 1),
          PowerSeries.coeff u ((1 + PowerSeries.X : PowerSeries R) ^ y) *
          PowerSeries.coeff (x - u) (negBinomSeries inv2 y) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro u hu hnot
      rw [Finset.mem_range] at hu hnot
      rw [coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    rw [hsub, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_range] at hu
    rw [coeff_one_add_X_pow, negBinomSeries, PowerSeries.coeff_mk]
    have he1 : y + (x - u) = x + y - u := by omega
    have he2 : y + 1 + (x - u) + u = x + y + 1 := by omega
    have h2u : (2 : R) ^ u * inv2 ^ u = 1 := by rw [← mul_pow, h2, one_pow]
    have hneg : (-1 : R) ^ (x + y) * (-1 : R) ^ u = (-1 : R) ^ y * (-1 : R) ^ (x - u) := by
      rw [← pow_add, ← pow_add]
      have : x + y + u = (y + (x - u)) + 2 * u := by omega
      rw [this, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
    have hinv : inv2 ^ (x + y + 1) * (2 : R) ^ u = inv2 ^ (y + 1 + (x - u)) := by
      rw [← he2, pow_add, mul_assoc, mul_comm (inv2 ^ u), h2u, mul_one]
    rw [he1]
    calc (-1 : R) ^ y * ((y.choose u : R) * ((-1 : R) ^ (x - u) * inv2 ^ (y + 1 + (x - u)) * ((x + y - u).choose y : R)))
        = ((-1 : R) ^ y * (-1 : R) ^ (x - u)) * inv2 ^ (y + 1 + (x - u)) * (y.choose u : R) * ((x + y - u).choose y : R) := by ring
      _ = ((-1 : R) ^ (x + y) * (-1 : R) ^ u) * (inv2 ^ (x + y + 1) * (2 : R) ^ u) * (y.choose u : R) * ((x + y - u).choose y : R) := by
          rw [← hneg, ← hinv]
      _ = (-1 : R) ^ (x + y) * inv2 ^ (x + y + 1) * (((-1 : R) * 2) ^ u * (y.choose u : R) * ((x + y - u).choose y : R)) := by
          rw [mul_pow]; ring
      _ = (-1 : R) ^ (x + y) * inv2 ^ (x + y + 1) * ((-2 : R) ^ u * (y.choose u : R) * ((x + y - u).choose y : R)) := by
          norm_num
  rw [hform a b, hform b a, add_comm b a, min_comm b a]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  have hsym := choose_symm_nat (a := a) (b := b) (u := u) (by omega) (by omega)
  have hcast : ((b.choose u * (a + b - u).choose b : ℕ) : R) =
      ((a.choose u * (a + b - u).choose a : ℕ) : R) := by rw [hsym]
  simp only [Nat.cast_mul] at hcast
  rw [mul_assoc, hcast, ← mul_assoc]

private lemma choose_p_sub_one_zmod {p : ℕ} (hp : p.Prime) :
    ∀ m < p, ((Nat.choose (p - 1) m : ℕ) : ZMod p) = (-1 : ZMod p) ^ m := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    have hpas : Nat.choose p (m + 1) = Nat.choose (p - 1) m + Nat.choose (p - 1) (m + 1) := by
      have h := Nat.choose_succ_succ (p - 1) m
      have hp1 : (p - 1).succ = p := by omega
      rw [hp1] at h
      exact h
    have hdvd : p ∣ Nat.choose p (m + 1) := hp.dvd_choose_self (by omega) (by omega)
    have hz : ((Nat.choose p (m + 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [hpas, Nat.cast_add, ih (by omega)] at hz
    rw [pow_succ]
    linear_combination hz

private lemma choose_div_p_zmod {p : ℕ} (hp : p.Prime) {i : ℕ} (hi1 : 1 ≤ i) (hip : i < p) :
    ((Nat.choose p i / p : ℕ) : ZMod p) = (-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hmul : i * Nat.choose p i = p * Nat.choose (p - 1) (i - 1) := by
    have h := Nat.choose_mul (n := p) (k := i) (s := 1) hi1
    simp only [Nat.choose_one_right] at h
    linarith
  have hdvd : p ∣ Nat.choose p i := hp.dvd_choose_self (by omega) hip
  have hdiv : i * (Nat.choose p i / p) = Nat.choose (p - 1) (i - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc p * (i * (Nat.choose p i / p))
        = i * (p * (Nat.choose p i / p)) := by ring
      _ = i * Nat.choose p i := by rw [Nat.mul_div_cancel' hdvd]
      _ = p * Nat.choose (p - 1) (i - 1) := hmul
  have hcast : (i : ZMod p) * ((Nat.choose p i / p : ℕ) : ZMod p) = (-1 : ZMod p) ^ (i - 1) := by
    rw [← Nat.cast_mul, hdiv, choose_p_sub_one_zmod hp (i - 1) (by omega)]
  have hi_ne : (i : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ i := (ZMod.natCast_eq_zero_iff i p).mp h
    have := Nat.le_of_dvd (by omega) hd
    omega
  calc ((Nat.choose p i / p : ℕ) : ZMod p)
      = (i : ZMod p)⁻¹ * ((i : ZMod p) * ((Nat.choose p i / p : ℕ) : ZMod p)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hi_ne, one_mul]
    _ = (-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹ := by rw [hcast, mul_comm]

private noncomputable def Alog {p : ℕ} (s : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  ∑ i ∈ Finset.Ico 1 p,
    PowerSeries.C ((-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹) * s ^ i

private lemma deriv_Alog {p : ℕ} (hp : p.Prime) (s : PowerSeries (ZMod p)) :
    PowerSeries.derivative (ZMod p) (Alog (p := p) s) =
    (∑ i ∈ Finset.Ico 1 p, PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * s ^ (i - 1)) *
      PowerSeries.derivative (ZMod p) s := by
  have : Fact p.Prime := ⟨hp⟩
  unfold Alog
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, PowerSeries.derivative_C, mul_zero, add_zero,
    PowerSeries.derivative_pow]
  have hi_ne : (i : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff i p).mp h
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hC : (i : PowerSeries (ZMod p)) = PowerSeries.C (i : ZMod p) := by simp
  rw [hC]
  calc PowerSeries.C ((-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹) *
        (PowerSeries.C (i : ZMod p) * s ^ (i - 1) * PowerSeries.derivative (ZMod p) s)
      = PowerSeries.C ((-1 : ZMod p) ^ (i - 1) * ((i : ZMod p)⁻¹ * (i : ZMod p))) *
          s ^ (i - 1) * PowerSeries.derivative (ZMod p) s := by
        simp only [map_mul]; ring
    _ = PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * s ^ (i - 1) * PowerSeries.derivative (ZMod p) s := by
        rw [inv_mul_cancel₀ hi_ne, mul_one]

private lemma one_add_mul_geom_alt {R : Type*} [CommRing R] (s : PowerSeries R) {p : ℕ}
    (hodd : Odd p) :
    (1 + s) * (∑ i ∈ Finset.Ico 1 p, PowerSeries.C ((-1 : R) ^ (i - 1)) * s ^ (i - 1)) =
    1 - s ^ (p - 1) := by
  have h1 : ∑ i ∈ Finset.Ico 1 p, PowerSeries.C ((-1 : R) ^ (i - 1)) * s ^ (i - 1) =
      ∑ j ∈ Finset.range (p - 1), PowerSeries.C ((-1 : R) ^ j) * s ^ j := by
    refine Finset.sum_nbij (fun i => i - 1) ?_ ?_ ?_ ?_
    · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; omega
    · intro i1 hi1 i2 hi2 h; rw [Finset.mem_coe, Finset.mem_Ico] at hi1 hi2; dsimp only at h; omega
    · intro j hj; rw [Finset.mem_coe, Finset.mem_range] at hj
      exact ⟨j + 1, by rw [Finset.mem_coe, Finset.mem_Ico]; omega, by dsimp only; omega⟩
    · intro i _; rfl
  rw [h1, add_mul, one_mul, Finset.mul_sum]
  have hstep : ∑ j ∈ Finset.range (p - 1), s * (PowerSeries.C ((-1 : R) ^ j) * s ^ j) =
      -(∑ j ∈ Finset.range (p - 1), PowerSeries.C ((-1 : R) ^ (j + 1)) * s ^ (j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ (-1 : R), pow_succ s, map_mul, map_neg, map_one]
    ring
  rw [hstep, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_sub' (fun j => PowerSeries.C ((-1 : R) ^ j) * s ^ j) (p - 1)]
  have hev : Even (p - 1) := by
    rcases hodd with ⟨m, rfl⟩
    exact ⟨m, by omega⟩
  rw [pow_zero, pow_zero, map_one, mul_one, hev.neg_one_pow, map_one, one_mul]

private lemma coeff_Alog_add_involution {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p)
    (inv1X : PowerSeries (ZMod p)) (h1X : (1 + PowerSeries.X) * inv1X = 1) :
    ∀ d < p, PowerSeries.coeff d
      (Alog (p := p) PowerSeries.X + Alog (p := p) (-PowerSeries.X * inv1X)) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  set u : PowerSeries (ZMod p) := -PowerSeries.X * inv1X
  have h1u : (1 + PowerSeries.X) * u = -PowerSeries.X := by
    calc (1 + PowerSeries.X) * (-PowerSeries.X * inv1X)
        = -PowerSeries.X * ((1 + PowerSeries.X) * inv1X) := by ring
      _ = -PowerSeries.X := by rw [h1X, mul_one]
  have h1_add_u : (1 + PowerSeries.X) * (1 + u) = 1 := by
    calc (1 + PowerSeries.X) * (1 + u) = 1 + PowerSeries.X + (1 + PowerSeries.X) * u := by ring
      _ = 1 + PowerSeries.X + (-PowerSeries.X) := by rw [h1u]
      _ = 1 := by ring
  have hdu : (1 + PowerSeries.X) ^ 2 * PowerSeries.derivative (ZMod p) u = -1 := by
    have hd := congrArg (PowerSeries.derivative (ZMod p)) h1u
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, PowerSeries.derivative_one,
      PowerSeries.derivative_X, zero_add, mul_one, map_neg, PowerSeries.derivative_X] at hd
    have hmul := congrArg (fun f => (1 + PowerSeries.X) * f) hd
    linear_combination hmul - h1u
  have hd_sum : (1 + PowerSeries.X) *
      PowerSeries.derivative (ZMod p) (Alog (p := p) PowerSeries.X + Alog (p := p) u) =
      u ^ (p - 1) - PowerSeries.X ^ (p - 1) := by
    rw [map_add, deriv_Alog hp PowerSeries.X, deriv_Alog hp u, PowerSeries.derivative_X, mul_one]
    have hA1 : (1 + PowerSeries.X) *
        (∑ i ∈ Finset.Ico 1 p, PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * PowerSeries.X ^ (i - 1)) =
        1 - PowerSeries.X ^ (p - 1) := one_add_mul_geom_alt PowerSeries.X hodd
    have hA2 : (1 + u) *
        (∑ i ∈ Finset.Ico 1 p, PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * u ^ (i - 1)) =
        1 - u ^ (p - 1) := one_add_mul_geom_alt u hodd
    have hA2' : (1 + PowerSeries.X) *
        ((∑ i ∈ Finset.Ico 1 p, PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * u ^ (i - 1)) *
          PowerSeries.derivative (ZMod p) u) = -(1 - u ^ (p - 1)) := by
      calc (1 + PowerSeries.X) *
            ((∑ i ∈ Finset.Ico 1 p, PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * u ^ (i - 1)) *
              PowerSeries.derivative (ZMod p) u)
          = ((1 + PowerSeries.X) * (1 + u)) *
              ((1 + PowerSeries.X) * ((∑ i ∈ Finset.Ico 1 p,
                PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * u ^ (i - 1)) *
                PowerSeries.derivative (ZMod p) u)) := by rw [h1_add_u, one_mul]
        _ = ((1 + u) * (∑ i ∈ Finset.Ico 1 p,
              PowerSeries.C ((-1 : ZMod p) ^ (i - 1)) * u ^ (i - 1))) *
              ((1 + PowerSeries.X) ^ 2 * PowerSeries.derivative (ZMod p) u) := by ring
        _ = (1 - u ^ (p - 1)) * (-1) := by rw [hA2, hdu]
        _ = -(1 - u ^ (p - 1)) := by ring
    rw [mul_add, hA1, hA2']
    ring
  have hd_eq : PowerSeries.derivative (ZMod p) (Alog (p := p) PowerSeries.X + Alog (p := p) u) =
      PowerSeries.X ^ (p - 1) * (((-inv1X) ^ (p - 1) - 1) * inv1X) := by
    have hu_pow : u ^ (p - 1) = PowerSeries.X ^ (p - 1) * (-inv1X) ^ (p - 1) := by
      rw [show u = PowerSeries.X * (-inv1X) by ring, mul_pow]
    calc PowerSeries.derivative (ZMod p) (Alog (p := p) PowerSeries.X + Alog (p := p) u)
        = (inv1X * (1 + PowerSeries.X)) *
            PowerSeries.derivative (ZMod p) (Alog (p := p) PowerSeries.X + Alog (p := p) u) := by
          rw [mul_comm inv1X, h1X, one_mul]
      _ = inv1X * (u ^ (p - 1) - PowerSeries.X ^ (p - 1)) := by rw [mul_assoc, hd_sum]
      _ = PowerSeries.X ^ (p - 1) * (((-inv1X) ^ (p - 1) - 1) * inv1X) := by rw [hu_pow]; ring
  intro d hd
  cases d with
  | zero =>
    have hA0 : ∀ s : PowerSeries (ZMod p), PowerSeries.constantCoeff s = 0 →
        PowerSeries.constantCoeff (Alog (p := p) s) = 0 := by
      intro s hs
      unfold Alog
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [map_mul, map_pow, hs, zero_pow (by omega), mul_zero]
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add,
      hA0 PowerSeries.X (by simp), hA0 u (by simp [u]), add_zero]
  | succ m =>
    have hder := PowerSeries.coeff_derivative (Alog (p := p) PowerSeries.X + Alog (p := p) u) m
    rw [hd_eq, coeff_X_pow_mul_eq_zero (by omega)] at hder
    have hm_ne : ((m : ZMod p) + 1) ≠ 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      intro h
      have hdiv := (ZMod.natCast_eq_zero_iff (m + 1) p).mp h
      have := Nat.le_of_dvd (by omega) hdiv
      omega
    exact (mul_eq_zero.mp (by rw [mul_comm]; exact hder.symm)).resolve_left hm_ne

private lemma poly_mul_trunc_sub_dvd {R : Type*} [CommRing R] (A B : Polynomial R)
    (F : PowerSeries R) (r : ℕ)
    (hAF : Polynomial.coeToPowerSeries.ringHom A * F = Polynomial.coeToPowerSeries.ringHom B) :
    Polynomial.X ^ (r + 1) ∣
      A * (∑ j ∈ Finset.range (r + 1), Polynomial.C (PowerSeries.coeff j F) * Polynomial.X ^ j) - B := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  set P : Polynomial R := ∑ j ∈ Finset.range (r + 1), Polynomial.C (PowerSeries.coeff j F) * Polynomial.X ^ j
  have hcoe : (A * P - B).coeff d =
      PowerSeries.coeff d (Polynomial.coeToPowerSeries.ringHom (A * P - B)) :=
    (Polynomial.coeff_coe (A * P - B) d).symm
  rw [hcoe, map_sub, map_mul, ← hAF, ← mul_sub, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v =>
      PowerSeries.coeff u (Polynomial.coeToPowerSeries.ringHom A) *
      PowerSeries.coeff v (Polynomial.coeToPowerSeries.ringHom P - F)) d]
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.mem_range] at hu
  have hPcoeff : PowerSeries.coeff (d - u) (Polynomial.coeToPowerSeries.ringHom P) = PowerSeries.coeff (d - u) F := by
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
    simp only [P, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single (d - u)]
    · simp
    · intro b _ hb; simp [hb.symm]
    · intro hnot; rw [Finset.mem_range] at hnot; omega
  rw [map_sub, hPcoeff, sub_self, mul_zero]

private lemma coeff_eval_trunc_mul_pow {R : Type*} [CommRing R] (c d : R) (r : ℕ) (hr : 1 ≤ r)
    (f : ℕ → R) (invW : PowerSeries R)
    (hW : (1 + PowerSeries.C d * PowerSeries.X) * invW = 1) :
    PowerSeries.coeff r
      ((∑ j ∈ Finset.range (r + 1),
          PowerSeries.C (f j) * (PowerSeries.C c * PowerSeries.X * invW) ^ j) *
        (1 + PowerSeries.C d * PowerSeries.X) ^ (r - 1)) =
    c ^ r * f r := by
  set W : PowerSeries R := 1 + PowerSeries.C d * PowerSeries.X
  rw [Finset.sum_mul, map_sum, Finset.sum_eq_single r]
  · have htop : (PowerSeries.C c * PowerSeries.X * invW) ^ r * W ^ (r - 1) =
        PowerSeries.C (c ^ r) * (PowerSeries.X ^ r * invW) := by
      rw [mul_pow, mul_pow, ← map_pow]
      have hexp : r = (r - 1) + 1 := by omega
      conv_lhs => rw [hexp, pow_succ invW]
      have hcanc : invW ^ (r - 1) * W ^ (r - 1) = 1 := by
        rw [← mul_pow, mul_comm, hW, one_pow]
      calc PowerSeries.C (c ^ (r - 1 + 1)) * PowerSeries.X ^ (r - 1 + 1) *
            (invW ^ (r - 1) * invW) * W ^ (r - 1)
          = PowerSeries.C (c ^ (r - 1 + 1)) * (PowerSeries.X ^ (r - 1 + 1) *
            ((invW ^ (r - 1) * W ^ (r - 1)) * invW)) := by ring
        _ = PowerSeries.C (c ^ (r - 1 + 1)) * (PowerSeries.X ^ (r - 1 + 1) * invW) := by
            rw [hcanc, one_mul]
        _ = PowerSeries.C (c ^ r) * (PowerSeries.X ^ r * invW) := by rw [← hexp]
    rw [mul_assoc, htop, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp only [le_refl, ↓reduceIte, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff]
    have hinv0 : PowerSeries.constantCoeff invW = 1 := by
      have h := congrArg PowerSeries.constantCoeff hW
      simpa only [W, map_mul, map_add, map_one, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
        mul_zero, add_zero, one_mul] using h
    rw [hinv0, mul_one, mul_comm]
  · intro j hj hjr
    rw [Finset.mem_range] at hj
    have hterm : (PowerSeries.C c * PowerSeries.X * invW) ^ j * W ^ (r - 1) =
        Polynomial.coeToPowerSeries.ringHom
          (Polynomial.C (c ^ j) * Polynomial.X ^ j *
            (1 + Polynomial.C d * Polynomial.X) ^ (r - 1 - j)) := by
      rw [mul_pow, mul_pow, ← map_pow]
      have hexp : r - 1 = j + (r - 1 - j) := by omega
      conv_lhs => rw [hexp, pow_add W]
      have hcanc : invW ^ j * W ^ j = 1 := by
        rw [← mul_pow, mul_comm, hW, one_pow]
      have hcoe : Polynomial.coeToPowerSeries.ringHom
            (Polynomial.C (c ^ j) * Polynomial.X ^ j *
              (1 + Polynomial.C d * Polynomial.X) ^ (r - 1 - j)) =
          PowerSeries.C (c ^ j) * PowerSeries.X ^ j * W ^ (r - 1 - j) := by
        simp only [map_mul, map_pow, map_add, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
          Polynomial.coe_C, Polynomial.coe_X, W]
      rw [hcoe]
      calc PowerSeries.C (c ^ j) * PowerSeries.X ^ j * invW ^ j * (W ^ j * W ^ (r - 1 - j))
          = PowerSeries.C (c ^ j) * PowerSeries.X ^ j * (invW ^ j * W ^ j) * W ^ (r - 1 - j) := by ring
        _ = PowerSeries.C (c ^ j) * PowerSeries.X ^ j * W ^ (r - 1 - j) := by rw [hcanc, mul_one]
    rw [mul_assoc, hterm, PowerSeries.coeff_C_mul, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeff_coe]
    have hdeg : (Polynomial.C (c ^ j) * Polynomial.X ^ j *
        (1 + Polynomial.C d * Polynomial.X) ^ (r - 1 - j)).natDegree < r := by
      have hd1 : (Polynomial.C (c ^ j) * Polynomial.X ^ j).natDegree ≤ j :=
        Polynomial.natDegree_C_mul_X_pow_le (c ^ j) j
      have hd2 : ((1 + Polynomial.C d * Polynomial.X) ^ (r - 1 - j)).natDegree ≤ r - 1 - j := by
        refine le_trans Polynomial.natDegree_pow_le ?_
        have h1x : (1 + Polynomial.C d * Polynomial.X).natDegree ≤ 1 := by
          refine le_trans (Polynomial.natDegree_add_le _ _) ?_
          simp only [Polynomial.natDegree_one, zero_le, max_eq_right]
          have hdX : (Polynomial.C d * Polynomial.X).natDegree ≤ 1 := by
            simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le d 1
          exact hdX
        exact le_trans (Nat.mul_le_mul_left _ h1x) (by omega)
      have hd3 := le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hd1 hd2)
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
  · intro hnot; rw [Finset.mem_range] at hnot; omega

private lemma coeff_termA_eq_zero {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p)
    (inv2X : PowerSeries (ZMod p)) (h2X : (2 + PowerSeries.X) * inv2X = 1)
    {k : ℕ} (hk : 2 * k < p) :
    PowerSeries.coeff (2 * k)
      (Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ (2 * k) * inv2X ^ (2 * k + 1)) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  cases k with
  | zero =>
    simp only [mul_zero, pow_zero, mul_one, zero_add, pow_one, PowerSeries.coeff_zero_eq_constantCoeff,
      map_mul]
    have hA0 : PowerSeries.constantCoeff (Alog (p := p) PowerSeries.X) = 0 := by
      unfold Alog
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      simp [zero_pow (show i ≠ 0 by omega)]
    rw [hA0, zero_mul]
  | succ k' =>
    set r := 2 * (k' + 1)
    obtain ⟨u1, hu1⟩ := isUnit_one_add_X (R := ZMod p)
    set inv1X : PowerSeries (ZMod p) := (u1⁻¹ : (PowerSeries (ZMod p))ˣ).val
    have h1X : (1 + PowerSeries.X) * inv1X = 1 := by
      rw [← hu1]
      change u1.val * (u1⁻¹ : (PowerSeries (ZMod p))ˣ).val = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    set u : PowerSeries (ZMod p) := -PowerSeries.X * inv1X
    set F : PowerSeries (ZMod p) := Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1)
    set Apoly : Polynomial (ZMod p) := ∑ i ∈ Finset.Ico 1 p,
      Polynomial.C ((-1 : ZMod p) ^ (i - 1) * (i : ZMod p)⁻¹) * Polynomial.X ^ i
    have hApoly_coe : Polynomial.coeToPowerSeries.ringHom Apoly = Alog (p := p) PowerSeries.X := by
      unfold Apoly Alog
      simp only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, Polynomial.coe_X]
    have hApoly_aeval : Polynomial.aeval u Apoly = Alog (p := p) u := by
      unfold Apoly Alog
      simp only [map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rfl
    have hAF : Polynomial.coeToPowerSeries.ringHom ((2 + Polynomial.X : Polynomial (ZMod p)) ^ (r + 1)) * F =
        Polynomial.coeToPowerSeries.ringHom (Apoly * (1 + Polynomial.X) ^ r) := by
      simp only [map_mul, map_pow, map_add, map_ofNat, map_one, hApoly_coe,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      calc (2 + PowerSeries.X) ^ (r + 1) *
            (Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1))
          = Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ r *
            ((2 + PowerSeries.X) * inv2X) ^ (r + 1) := by rw [mul_pow]; ring
        _ = Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ r := by rw [h2X, one_pow, mul_one]
    obtain ⟨Qrem, hQrem⟩ := poly_mul_trunc_sub_dvd _ _ F r hAF
    have haeval := congrArg (Polynomial.aeval u) hQrem
    simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_one, Polynomial.aeval_X,
      hApoly_aeval] at haeval
    set Paeval : PowerSeries (ZMod p) :=
      Polynomial.aeval u (∑ j ∈ Finset.range (r + 1), Polynomial.C (PowerSeries.coeff j F) * Polynomial.X ^ j)
    have h1_add_u : 1 + u = inv1X := by
      calc 1 + u = (1 + PowerSeries.X) * inv1X + (-PowerSeries.X * inv1X) := by rw [h1X]
        _ = inv1X := by ring
    have h2_add_u : 2 + u = (2 + PowerSeries.X) * inv1X := by
      calc 2 + u = 1 + (1 + u) := by ring
        _ = (1 + PowerSeries.X) * inv1X + inv1X := by rw [h1X, h1_add_u]
        _ = (2 + PowerSeries.X) * inv1X := by ring
    have hmul_id : Paeval * (1 + PowerSeries.X) ^ (r - 1) -
        Alog (p := p) u * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1) =
        PowerSeries.X ^ (r + 1) * ((-inv1X) ^ (r + 1) * Polynomial.aeval u Qrem *
          inv2X ^ (r + 1) * (1 + PowerSeries.X) ^ (2 * r)) := by
      have h1 : (2 + u) ^ (r + 1) * inv2X ^ (r + 1) * (1 + PowerSeries.X) ^ (2 * r) =
          (1 + PowerSeries.X) ^ (r - 1) := by
        rw [h2_add_u, mul_pow]
        have hexp : 2 * r = (r + 1) + (r - 1) := by omega
        rw [hexp, pow_add (1 + PowerSeries.X)]
        calc (2 + PowerSeries.X) ^ (r + 1) * inv1X ^ (r + 1) * inv2X ^ (r + 1) *
              ((1 + PowerSeries.X) ^ (r + 1) * (1 + PowerSeries.X) ^ (r - 1))
            = ((2 + PowerSeries.X) * inv2X) ^ (r + 1) *
              ((1 + PowerSeries.X) * inv1X) ^ (r + 1) * (1 + PowerSeries.X) ^ (r - 1) := by
              rw [mul_pow, mul_pow]; ring
          _ = (1 + PowerSeries.X) ^ (r - 1) := by rw [h2X, h1X, one_pow, one_mul, one_mul]
      have h2 : (1 + u) ^ r * (1 + PowerSeries.X) ^ (2 * r) = (1 + PowerSeries.X) ^ r := by
        rw [h1_add_u, show 2 * r = r + r by omega, pow_add (1 + PowerSeries.X)]
        calc inv1X ^ r * ((1 + PowerSeries.X) ^ r * (1 + PowerSeries.X) ^ r)
            = ((1 + PowerSeries.X) * inv1X) ^ r * (1 + PowerSeries.X) ^ r := by rw [mul_pow]; ring
          _ = (1 + PowerSeries.X) ^ r := by rw [h1X, one_pow, one_mul]
      have hu_pow : u ^ (r + 1) = PowerSeries.X ^ (r + 1) * (-inv1X) ^ (r + 1) := by
        rw [show u = PowerSeries.X * (-inv1X) by ring, mul_pow]
      have hsc := congrArg (fun x => x * inv2X ^ (r + 1) * (1 + PowerSeries.X) ^ (2 * r)) haeval
      calc Paeval * (1 + PowerSeries.X) ^ (r - 1) -
            Alog (p := p) u * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1)
          = ((2 + u) ^ (r + 1) * Paeval - Alog (p := p) u * (1 + u) ^ r) *
              inv2X ^ (r + 1) * (1 + PowerSeries.X) ^ (2 * r) := by
            rw [sub_mul, sub_mul]
            congr 1
            · rw [← h1]; ring
            · rw [← h2]; ring
        _ = u ^ (r + 1) * Polynomial.aeval u Qrem * inv2X ^ (r + 1) * (1 + PowerSeries.X) ^ (2 * r) := hsc
        _ = PowerSeries.X ^ (r + 1) * ((-inv1X) ^ (r + 1) * Polynomial.aeval u Qrem *
              inv2X ^ (r + 1) * (1 + PowerSeries.X) ^ (2 * r)) := by rw [hu_pow]; ring
    have hcoeff_eq : PowerSeries.coeff r (Paeval * (1 + PowerSeries.X) ^ (r - 1)) =
        PowerSeries.coeff r (Alog (p := p) u * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1)) := by
      have h := congrArg (PowerSeries.coeff r) hmul_id
      rw [map_sub, coeff_X_pow_mul_eq_zero (by omega)] at h
      exact sub_eq_zero.mp h
    have hLHS : PowerSeries.coeff r (Paeval * (1 + PowerSeries.X) ^ (r - 1)) = PowerSeries.coeff r F := by
      have haP : Paeval = ∑ j ∈ Finset.range (r + 1),
          PowerSeries.C (PowerSeries.coeff j F) * (PowerSeries.C (-1 : ZMod p) * PowerSeries.X * inv1X) ^ j := by
        unfold Paeval
        simp only [map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp [u]
      have h1X' : (1 + PowerSeries.C (1 : ZMod p) * PowerSeries.X) * inv1X = 1 := by
        simpa using h1X
      have hcalc := coeff_eval_trunc_mul_pow (-1 : ZMod p) (1 : ZMod p) r (by omega)
        (fun j => PowerSeries.coeff j F) inv1X h1X'
      have hrev : Even r := ⟨k' + 1, by omega⟩
      rw [hrev.neg_one_pow, one_mul] at hcalc
      rw [haP]
      simpa using hcalc
    have hRHS : PowerSeries.coeff r (Alog (p := p) u * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1)) =
        -PowerSeries.coeff r F := by
      have hadd0 : PowerSeries.coeff r
          ((Alog (p := p) PowerSeries.X + Alog (p := p) u) *
            ((1 + PowerSeries.X) ^ r * inv2X ^ (r + 1))) = 0 := by
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
            PowerSeries.coeff a (Alog (p := p) PowerSeries.X + Alog (p := p) u) *
            PowerSeries.coeff b ((1 + PowerSeries.X) ^ r * inv2X ^ (r + 1))) r]
        apply Finset.sum_eq_zero
        intro a ha
        rw [Finset.mem_range] at ha
        rw [coeff_Alog_add_involution hp h3 inv1X h1X a (by omega), zero_mul]
      rw [add_mul, map_add, ← mul_assoc, ← mul_assoc] at hadd0
      exact eq_neg_of_add_eq_zero_right hadd0
    have h2eq : (2 : ZMod p) * PowerSeries.coeff r F = 0 := by
      have h := hLHS.symm.trans (hcoeff_eq.trans hRHS)
      linear_combination h
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
      have := Nat.le_of_dvd (by decide) hd
      omega
    exact (mul_eq_zero.mp h2eq).resolve_left h2ne

private lemma coeff_two_rat_legendre {R : Type*} [CommRing R] (h2 : IsUnit (2 : R))
    (inv2X : PowerSeries R) (h2X : (2 + PowerSeries.X) * inv2X = 1) (k : ℕ) :
    (-16 : R) ^ k * PowerSeries.coeff (2 * k)
      (2 * (1 + PowerSeries.X) ^ (2 * k) * inv2X ^ (2 * k + 1)) = (Nat.choose (2 * k) k : R) := by
  cases k with
  | zero =>
    simp only [pow_zero, one_mul, mul_zero, zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_ofNat, map_one, mul_one]
    have h := congrArg PowerSeries.constantCoeff h2X
    simpa only [map_mul, map_add, map_ofNat, PowerSeries.constantCoeff_X, add_zero, map_one] using h
  | succ k' =>
    set r := 2 * (k' + 1)
    obtain ⟨u1, hu1⟩ := isUnit_one_sub_X (R := R)
    set inv1mX : PowerSeries R := (u1⁻¹ : (PowerSeries R)ˣ).val
    have h1mX : (1 - PowerSeries.X) * inv1mX = 1 := by
      rw [← hu1]
      change u1.val * (u1⁻¹ : (PowerSeries R)ˣ).val = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    set v : PowerSeries R := 2 * PowerSeries.X * inv1mX
    set H : PowerSeries R := 2 * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1)
    have hAF : Polynomial.coeToPowerSeries.ringHom ((2 + Polynomial.X : Polynomial R) ^ (r + 1)) * H =
        Polynomial.coeToPowerSeries.ringHom (2 * (1 + Polynomial.X) ^ r) := by
      simp only [map_mul, map_pow, map_add, map_ofNat, map_one,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      calc (2 + PowerSeries.X) ^ (r + 1) * (2 * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1))
          = 2 * (1 + PowerSeries.X) ^ r * ((2 + PowerSeries.X) * inv2X) ^ (r + 1) := by
            rw [mul_pow]; ring
        _ = 2 * (1 + PowerSeries.X) ^ r := by rw [h2X, one_pow, mul_one]
    obtain ⟨Qrem, hQrem⟩ := poly_mul_trunc_sub_dvd _ _ H r hAF
    have haeval := congrArg (Polynomial.aeval v) hQrem
    simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_one, Polynomial.aeval_X] at haeval
    set Paeval : PowerSeries R :=
      Polynomial.aeval v (∑ j ∈ Finset.range (r + 1), Polynomial.C (PowerSeries.coeff j H) * Polynomial.X ^ j)
    have h1_add_v : 1 + v = (1 + PowerSeries.X) * inv1mX := by
      calc 1 + v = (1 - PowerSeries.X) * inv1mX + 2 * PowerSeries.X * inv1mX := by rw [h1mX]
        _ = (1 + PowerSeries.X) * inv1mX := by ring
    have h2_add_v : 2 + v = 2 * inv1mX := by
      calc 2 + v = 2 * ((1 - PowerSeries.X) * inv1mX) + 2 * PowerSeries.X * inv1mX := by
            rw [h1mX, mul_one]
        _ = 2 * inv1mX := by ring
    have hmul_id : 2 ^ (r + 1) * (Paeval * (1 - PowerSeries.X) ^ (r - 1)) -
        2 * (1 - PowerSeries.X ^ 2) ^ r =
        PowerSeries.X ^ (r + 1) * ((2 * inv1mX) ^ (r + 1) * Polynomial.aeval v Qrem *
          (1 - PowerSeries.X) ^ (2 * r)) := by
      have h1 : (2 + v) ^ (r + 1) * (1 - PowerSeries.X) ^ (2 * r) =
          2 ^ (r + 1) * (1 - PowerSeries.X) ^ (r - 1) := by
        rw [h2_add_v, mul_pow]
        have hexp : 2 * r = (r + 1) + (r - 1) := by omega
        rw [hexp, pow_add (1 - PowerSeries.X)]
        calc 2 ^ (r + 1) * inv1mX ^ (r + 1) * ((1 - PowerSeries.X) ^ (r + 1) * (1 - PowerSeries.X) ^ (r - 1))
            = 2 ^ (r + 1) * ((1 - PowerSeries.X) * inv1mX) ^ (r + 1) * (1 - PowerSeries.X) ^ (r - 1) := by
              rw [mul_pow]; ring
          _ = 2 ^ (r + 1) * (1 - PowerSeries.X) ^ (r - 1) := by rw [h1mX, one_pow, mul_one]
      have h2' : 2 * (1 + v) ^ r * (1 - PowerSeries.X) ^ (2 * r) = 2 * (1 - PowerSeries.X ^ 2) ^ r := by
        rw [h1_add_v, mul_pow]
        have hexp : 2 * r = r + r := by omega
        rw [hexp, pow_add (1 - PowerSeries.X)]
        calc 2 * ((1 + PowerSeries.X) ^ r * inv1mX ^ r) *
              ((1 - PowerSeries.X) ^ r * (1 - PowerSeries.X) ^ r)
            = 2 * ((1 - PowerSeries.X) * inv1mX) ^ r *
              ((1 + PowerSeries.X) * (1 - PowerSeries.X)) ^ r := by
              rw [mul_pow, mul_pow]; ring
          _ = 2 * (1 - PowerSeries.X ^ 2) ^ r := by
              rw [h1mX, one_pow, mul_one]
              congr 2; ring
      have hv_pow : v ^ (r + 1) = PowerSeries.X ^ (r + 1) * (2 * inv1mX) ^ (r + 1) := by
        rw [show v = PowerSeries.X * (2 * inv1mX) by ring, mul_pow]
      have hsc := congrArg (fun x => x * (1 - PowerSeries.X) ^ (2 * r)) haeval
      calc 2 ^ (r + 1) * (Paeval * (1 - PowerSeries.X) ^ (r - 1)) -
            2 * (1 - PowerSeries.X ^ 2) ^ r
          = ((2 + v) ^ (r + 1) * Paeval - 2 * (1 + v) ^ r) *
              (1 - PowerSeries.X) ^ (2 * r) := by
            rw [sub_mul]
            congr 1
            · calc 2 ^ (r + 1) * (Paeval * (1 - PowerSeries.X) ^ (r - 1))
                  = Paeval * (2 ^ (r + 1) * (1 - PowerSeries.X) ^ (r - 1)) := by ring
                _ = Paeval * ((2 + v) ^ (r + 1) * (1 - PowerSeries.X) ^ (2 * r)) := by rw [← h1]
                _ = (2 + v) ^ (r + 1) * Paeval * (1 - PowerSeries.X) ^ (2 * r) := by ring
            · exact h2'.symm
        _ = v ^ (r + 1) * Polynomial.aeval v Qrem * (1 - PowerSeries.X) ^ (2 * r) := hsc
        _ = PowerSeries.X ^ (r + 1) * ((2 * inv1mX) ^ (r + 1) * Polynomial.aeval v Qrem *
              (1 - PowerSeries.X) ^ (2 * r)) := by rw [hv_pow]; ring
    have hcoeff_eq : PowerSeries.coeff r (2 ^ (r + 1) * (Paeval * (1 - PowerSeries.X) ^ (r - 1))) =
        PowerSeries.coeff r (2 * (1 - PowerSeries.X ^ 2) ^ r) := by
      have h := congrArg (PowerSeries.coeff r) hmul_id
      rw [map_sub, coeff_X_pow_mul_eq_zero (by omega)] at h
      exact sub_eq_zero.mp h
    have hLHS : PowerSeries.coeff r (2 ^ (r + 1) * (Paeval * (1 - PowerSeries.X) ^ (r - 1))) =
        2 * (16 : R) ^ (k' + 1) * PowerSeries.coeff r H := by
      rw [show (2 : PowerSeries R) ^ (r + 1) = PowerSeries.C ((2 : R) ^ (r + 1)) by rw [map_pow]; rfl,
        PowerSeries.coeff_C_mul]
      have haP : Paeval = ∑ j ∈ Finset.range (r + 1),
          PowerSeries.C (PowerSeries.coeff j H) * (PowerSeries.C (2 : R) * PowerSeries.X * inv1mX) ^ j := by
        unfold Paeval
        simp only [map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
      have h1mX' : (1 + PowerSeries.C (-1 : R) * PowerSeries.X) * inv1mX = 1 := by
        simpa [sub_eq_add_neg] using h1mX
      have hcalc := coeff_eval_trunc_mul_pow (2 : R) (-1 : R) r (by omega)
        (fun j => PowerSeries.coeff j H) inv1mX h1mX'
      have hcalc' : PowerSeries.coeff r (Paeval * (1 - PowerSeries.X) ^ (r - 1)) =
          (2 : R) ^ r * PowerSeries.coeff r H := by
        rw [haP]
        simpa [sub_eq_add_neg] using hcalc
      rw [hcalc']
      have h16 : (2 : R) ^ (r + 1) * (2 : R) ^ r = 2 * (16 : R) ^ (k' + 1) := by
        have h16_eq : (16 : R) = (2 : R) ^ 4 := by norm_num
        rw [h16_eq, ← pow_mul, ← pow_add, ← pow_succ']
        congr 1; omega
      rw [← mul_assoc, h16]
    have hRHS : PowerSeries.coeff r (2 * (1 - PowerSeries.X ^ 2) ^ r) =
        2 * ((-1 : R) ^ (k' + 1) * (Nat.choose r (k' + 1) : R)) := by
      rw [show (2 : PowerSeries R) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul]
      congr 1
      rw [sub_eq_add_neg, add_comm, add_pow, map_sum]
      rw [Finset.sum_eq_single (k' + 1)]
      · have hnegpow : (-PowerSeries.X ^ 2 : PowerSeries R) ^ (k' + 1) =
            PowerSeries.C ((-1 : R) ^ (k' + 1)) * PowerSeries.X ^ r := by
          rw [show (-PowerSeries.X ^ 2 : PowerSeries R) = PowerSeries.C (-1 : R) * PowerSeries.X ^ 2 by simp,
            mul_pow, ← map_pow, ← pow_mul]
        rw [one_pow, mul_one, hnegpow, ← map_natCast PowerSeries.C, PowerSeries.coeff_mul_C,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_self, mul_one]
      · intro j hj hjk
        have hnegpow : (-PowerSeries.X ^ 2 : PowerSeries R) ^ j =
            PowerSeries.C ((-1 : R) ^ j) * PowerSeries.X ^ (2 * j) := by
          rw [show (-PowerSeries.X ^ 2 : PowerSeries R) = PowerSeries.C (-1 : R) * PowerSeries.X ^ 2 by simp,
            mul_pow, ← map_pow, ← pow_mul]
        rw [one_pow, mul_one, hnegpow, ← map_natCast PowerSeries.C, PowerSeries.coeff_mul_C,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
          if_neg (show r ≠ 2 * j by omega), mul_zero, zero_mul]
      · intro hnot; rw [Finset.mem_range] at hnot; omega
    rw [hLHS, hRHS] at hcoeff_eq
    rcases h2 with ⟨u2, hu2⟩
    have hcancel : (16 : R) ^ (k' + 1) * PowerSeries.coeff r H =
        (-1 : R) ^ (k' + 1) * (Nat.choose r (k' + 1) : R) := by
      have h := congrArg (fun x => (u2⁻¹ : Rˣ).val * x) hcoeff_eq
      have h2inv : (u2⁻¹ : Rˣ).val * (2 : R) = 1 := by
        rw [← hu2, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc (16 : R) ^ (k' + 1) * PowerSeries.coeff r H
          = ((u2⁻¹ : Rˣ).val * 2) * ((16 : R) ^ (k' + 1) * PowerSeries.coeff r H) := by rw [h2inv, one_mul]
        _ = (u2⁻¹ : Rˣ).val * (2 * (16 : R) ^ (k' + 1) * PowerSeries.coeff r H) := by ring
        _ = (u2⁻¹ : Rˣ).val * (2 * ((-1 : R) ^ (k' + 1) * (Nat.choose r (k' + 1) : R))) := h
        _ = ((u2⁻¹ : Rˣ).val * 2) * ((-1 : R) ^ (k' + 1) * (Nat.choose r (k' + 1) : R)) := by ring
        _ = (-1 : R) ^ (k' + 1) * (Nat.choose r (k' + 1) : R) := by rw [h2inv, one_mul]
    calc (-16 : R) ^ (k' + 1) * PowerSeries.coeff r H
        = (-1 : R) ^ (k' + 1) * ((16 : R) ^ (k' + 1) * PowerSeries.coeff r H) := by
          rw [show (-16 : R) = (-1 : R) * 16 by ring, mul_pow]; ring
      _ = (-1 : R) ^ (k' + 1) * ((-1 : R) ^ (k' + 1) * (Nat.choose r (k' + 1) : R)) := by rw [hcancel]
      _ = ((-1 : R) * (-1 : R)) ^ (k' + 1) * (Nat.choose r (k' + 1) : R) := by rw [mul_pow]; ring
      _ = (Nat.choose r (k' + 1) : R) := by norm_num

private lemma p_mul_eq_zero_of_cast_eq_zero {p : ℕ} (hp : p.Prime) (x : ZMod (p ^ 2))
    (hx : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) x = 0) :
    (p : ZMod (p ^ 2)) * x = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hval : (x.val : ZMod p) = 0 := by
    have h := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) (ZMod.natCast_zmod_val x)
    rw [map_natCast, hx] at h
    exact h
  have hdvd : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).mp hval
  rcases hdvd with ⟨q, hq⟩
  have hx' : x = (p : ZMod (p ^ 2)) * (q : ZMod (p ^ 2)) := by
    rw [← ZMod.natCast_zmod_val x, hq, Nat.cast_mul]
  rw [hx', ← mul_assoc, ← sq, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

private lemma alt_sum_choose_sq_zmod_p_sq {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p)
    {k : ℕ} (hk : 2 * k < p) :
    (-16 : ZMod (p ^ 2)) ^ k *
      (∑ n ∈ Finset.range p, (-1 : ZMod (p ^ 2)) ^ n * ((Nat.choose n (2 * k) : ℕ) : ZMod (p ^ 2)) ^ 2) =
    ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  set r := 2 * k
  have hrev : Even r := ⟨k, by omega⟩
  have h2_p2 : IsUnit (2 : ZMod (p ^ 2)) := isUnit_two_zmod_pow hp h3 2
  obtain ⟨u2X, hu2X⟩ := isUnit_two_add_X h2_p2
  set inv2X : PowerSeries (ZMod (p ^ 2)) := (u2X⁻¹ : (PowerSeries (ZMod (p ^ 2)))ˣ).val
  have h2X : (2 + PowerSeries.X) * inv2X = 1 := by
    rw [← hu2X]
    change u2X.val * (u2X⁻¹ : (PowerSeries (ZMod (p ^ 2)))ˣ).val = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set A_p2 : PowerSeries (ZMod (p ^ 2)) := ∑ i ∈ Finset.Ico 1 p,
    PowerSeries.C ((Nat.choose p i / p : ℕ) : ZMod (p ^ 2)) * PowerSeries.X ^ i
  have h1Xp : (1 + PowerSeries.X : PowerSeries (ZMod (p ^ 2))) ^ p =
      1 + PowerSeries.X ^ p + PowerSeries.C (p : ZMod (p ^ 2)) * A_p2 := by
    rw [add_comm, add_pow]
    have hsplit : Finset.range (p + 1) = insert 0 (insert p (Finset.Ico 1 p)) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      Nat.choose_self, one_mul]
    rw [Finset.mul_sum]
    have hmid : ∑ i ∈ Finset.Ico 1 p, PowerSeries.X ^ i * (Nat.choose p i : PowerSeries (ZMod (p ^ 2))) =
        ∑ i ∈ Finset.Ico 1 p, PowerSeries.C (p : ZMod (p ^ 2)) *
          (PowerSeries.C ((Nat.choose p i / p : ℕ) : ZMod (p ^ 2)) * PowerSeries.X ^ i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      have hdvd : p ∣ Nat.choose p i := hp.dvd_choose_self (by omega) hi.2
      have hmul : (Nat.choose p i : PowerSeries (ZMod (p ^ 2))) =
          PowerSeries.C (p : ZMod (p ^ 2)) * PowerSeries.C ((Nat.choose p i / p : ℕ) : ZMod (p ^ 2)) := by
        rw [← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
        simp
      rw [hmul]
      ring
    rw [hmid]
    ring
  have hp2_zero : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
    rw [← sq, ← Nat.cast_pow, ZMod.natCast_self]
  have hQ_eq : Qpoly (R := ZMod (p ^ 2)) p r =
      2 * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1) +
      PowerSeries.C (p : ZMod (p ^ 2)) *
        (A_p2 * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1) +
         ∑ j ∈ Finset.Icc 1 r,
           PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j * ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2))) *
           (1 + PowerSeries.X) ^ (r - j) * inv2X ^ (r + 1 - j)) +
      PowerSeries.X ^ p *
        ((1 + PowerSeries.X) ^ r * inv2X ^ (r + 1) +
         (∑ j ∈ Finset.Icc 1 r,
           (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
           (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1)) := by
    have hcl := congrArg (fun x => x * inv2X ^ (r + 1)) (Qpoly_closed (R := ZMod (p ^ 2)) hodd r)
    have hL : (2 + PowerSeries.X) ^ (r + 1) * Qpoly (R := ZMod (p ^ 2)) p r * inv2X ^ (r + 1) =
        Qpoly (R := ZMod (p ^ 2)) p r := by
      calc (2 + PowerSeries.X) ^ (r + 1) * Qpoly (R := ZMod (p ^ 2)) p r * inv2X ^ (r + 1)
          = ((2 + PowerSeries.X) * inv2X) ^ (r + 1) * Qpoly (R := ZMod (p ^ 2)) p r := by
            rw [mul_pow]; ring
        _ = Qpoly (R := ZMod (p ^ 2)) p r := by rw [h2X, one_pow, one_mul]
    rw [hL, hrev.neg_one_pow, one_mul, h1Xp] at hcl
    rw [hcl]
    have hsum_j :
        (1 + PowerSeries.X ^ p + PowerSeries.C (p : ZMod (p ^ 2)) * A_p2) *
          (∑ j ∈ Finset.Icc 1 r,
            (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
            (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1) =
        PowerSeries.C (p : ZMod (p ^ 2)) *
          (∑ j ∈ Finset.Icc 1 r,
            PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j * ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2))) *
            (1 + PowerSeries.X) ^ (r - j) * inv2X ^ (r + 1 - j)) +
        PowerSeries.X ^ p *
          ((∑ j ∈ Finset.Icc 1 r,
            (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
            (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1)) := by
      have hp_zero_term : PowerSeries.C (p : ZMod (p ^ 2)) * A_p2 *
          (∑ j ∈ Finset.Icc 1 r,
            (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
            (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_Icc] at hj
        have hdvd : p ∣ Nat.choose p j := hp.dvd_choose_self (by omega) (by omega)
        have hc : PowerSeries.C (p : ZMod (p ^ 2)) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) = 0 := by
          rw [← map_mul, ← Nat.mul_div_cancel' hdvd, Nat.cast_mul, ← mul_assoc, hp2_zero, zero_mul, map_zero]
        calc PowerSeries.C (p : ZMod (p ^ 2)) * A_p2 *
              ((-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j)
            = (PowerSeries.C (p : ZMod (p ^ 2)) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2))) *
              (A_p2 * (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) := by ring
          _ = 0 := by rw [hc, zero_mul]
      have h1_term : (∑ j ∈ Finset.Icc 1 r,
            (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
            (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1) =
          PowerSeries.C (p : ZMod (p ^ 2)) *
          (∑ j ∈ Finset.Icc 1 r,
            PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j * ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2))) *
            (1 + PowerSeries.X) ^ (r - j) * inv2X ^ (r + 1 - j)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        have hdvd : p ∣ Nat.choose p j := hp.dvd_choose_self (by omega) (by omega)
        have hneg : (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) =
            PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j) := by
          have h1 : (-1 : ZMod (p ^ 2)) ^ (r - j) = (-1 : ZMod (p ^ 2)) ^ j := by
            have hev : Even (r - j + j) := by rw [Nat.sub_add_cancel hj.2]; exact hrev
            calc (-1 : ZMod (p ^ 2)) ^ (r - j)
                = (-1 : ZMod (p ^ 2)) ^ (r - j) * ((-1 : ZMod (p ^ 2)) ^ j * (-1 : ZMod (p ^ 2)) ^ j) := by
                  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
              _ = (-1 : ZMod (p ^ 2)) ^ (r - j + j) * (-1 : ZMod (p ^ 2)) ^ j := by rw [pow_add]; ring
              _ = (-1 : ZMod (p ^ 2)) ^ j := by rw [hev.neg_one_pow, one_mul]
          rw [← h1]
          simp
        have hch : PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) =
            PowerSeries.C (p : ZMod (p ^ 2)) * PowerSeries.C ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2)) := by
          rw [← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
        have hpow_canc : (2 + PowerSeries.X) ^ j * inv2X ^ (r + 1) = inv2X ^ (r + 1 - j) := by
          have hexp : r + 1 = j + (r + 1 - j) := by omega
          conv_lhs => rw [hexp, pow_add inv2X]
          calc (2 + PowerSeries.X) ^ j * (inv2X ^ j * inv2X ^ (r + 1 - j))
              = ((2 + PowerSeries.X) * inv2X) ^ j * inv2X ^ (r + 1 - j) := by rw [mul_pow]; ring
            _ = inv2X ^ (r + 1 - j) := by rw [h2X, one_pow, one_mul]
        rw [hneg, hch, map_mul]
        calc PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j) *
              (PowerSeries.C (p : ZMod (p ^ 2)) * PowerSeries.C ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2))) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j * inv2X ^ (r + 1)
            = PowerSeries.C (p : ZMod (p ^ 2)) *
              (PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j) * PowerSeries.C ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * ((2 + PowerSeries.X) ^ j * inv2X ^ (r + 1))) := by ring
          _ = PowerSeries.C (p : ZMod (p ^ 2)) *
              (PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j) * PowerSeries.C ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * inv2X ^ (r + 1 - j)) := by rw [hpow_canc]
      calc (1 + PowerSeries.X ^ p + PowerSeries.C (p : ZMod (p ^ 2)) * A_p2) *
            (∑ j ∈ Finset.Icc 1 r,
              (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1)
          = (1 + PowerSeries.X ^ p) * (∑ j ∈ Finset.Icc 1 r,
              (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1) +
            (PowerSeries.C (p : ZMod (p ^ 2)) * A_p2 * (∑ j ∈ Finset.Icc 1 r,
              (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j)) * inv2X ^ (r + 1) := by ring
        _ = (∑ j ∈ Finset.Icc 1 r,
              (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1) +
            PowerSeries.X ^ p * ((∑ j ∈ Finset.Icc 1 r,
              (-1 : PowerSeries (ZMod (p ^ 2))) ^ (r - j) * PowerSeries.C (Nat.choose p j : ZMod (p ^ 2)) *
              (1 + PowerSeries.X) ^ (r - j) * (2 + PowerSeries.X) ^ j) * inv2X ^ (r + 1)) := by
            rw [hp_zero_term, zero_mul, add_zero]; ring
        _ = _ := by rw [h1_term]
    rw [add_mul, hsum_j]
    ring
  have hQ_coeff := congrArg (PowerSeries.coeff r) hQ_eq
  rw [coeff_Qpoly, map_add, map_add, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq_zero hk, add_zero] at hQ_coeff
  set cast12 : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  set S_err : ZMod (p ^ 2) := PowerSeries.coeff r
    (A_p2 * (1 + PowerSeries.X) ^ r * inv2X ^ (r + 1) +
     ∑ j ∈ Finset.Icc 1 r,
       PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j * ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2))) *
       (1 + PowerSeries.X) ^ (r - j) * inv2X ^ (r + 1 - j))
  have hS_err_p : cast12 S_err = 0 := by
    set inv2Xp : PowerSeries (ZMod p) := PowerSeries.map cast12 inv2X
    have h2Xp : (2 + PowerSeries.X) * inv2Xp = 1 := by
      have h := congrArg (PowerSeries.map cast12) h2X
      simpa only [map_mul, map_add, map_ofNat, PowerSeries.map_X, map_one] using h
    have hA_map : PowerSeries.map cast12 A_p2 = Alog (p := p) PowerSeries.X := by
      unfold A_p2 Alog
      rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [map_mul, PowerSeries.map_C, map_natCast, choose_div_p_zmod hp hi.1 hi.2, map_pow,
        PowerSeries.map_X]
    have hcast_S : cast12 S_err =
        PowerSeries.coeff r (Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ r * inv2Xp ^ (r + 1)) +
        ∑ j ∈ Finset.Icc 1 r,
          (-1 : ZMod p) ^ j * ((Nat.choose p j / p : ℕ) : ZMod p) *
          PowerSeries.coeff r ((1 + PowerSeries.X) ^ (r - j) * inv2Xp ^ (r + 1 - j)) := by
      unfold S_err
      rw [← PowerSeries.coeff_map cast12 r, map_add, map_add]
      congr 1
      · congr 1
        rw [map_mul, map_mul, hA_map, map_pow, map_add, map_one, PowerSeries.map_X, map_pow]
      · rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hterm : PowerSeries.map cast12
            (PowerSeries.C ((-1 : ZMod (p ^ 2)) ^ j * ((Nat.choose p j / p : ℕ) : ZMod (p ^ 2))) *
              (1 + PowerSeries.X) ^ (r - j) * inv2X ^ (r + 1 - j)) =
            PowerSeries.C ((-1 : ZMod p) ^ j * ((Nat.choose p j / p : ℕ) : ZMod p)) *
              ((1 + PowerSeries.X) ^ (r - j) * inv2Xp ^ (r + 1 - j)) := by
          rw [map_mul, map_mul, PowerSeries.map_C, map_mul, map_pow, map_neg, map_one, map_natCast,
            map_pow, map_add, map_one, PowerSeries.map_X, map_pow, mul_assoc]
        rw [hterm, PowerSeries.coeff_C_mul]
    rw [hcast_S]
    have hTermA : PowerSeries.coeff r (Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ r * inv2Xp ^ (r + 1)) = 0 :=
      coeff_termA_eq_zero hp h3 inv2Xp h2Xp hk
    have hTermB : ∑ j ∈ Finset.Icc 1 r,
          (-1 : ZMod p) ^ j * ((Nat.choose p j / p : ℕ) : ZMod p) *
          PowerSeries.coeff r ((1 + PowerSeries.X) ^ (r - j) * inv2Xp ^ (r + 1 - j)) =
        PowerSeries.coeff r (Alog (p := p) PowerSeries.X * (1 + PowerSeries.X) ^ r * inv2Xp ^ (r + 1)) := by
      have h2inv_p : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
        have h2ne : (2 : ZMod p) ≠ 0 := by
          intro h
          have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
          have := Nat.le_of_dvd (by decide) hd
          omega
        exact mul_inv_cancel₀ h2ne
      have hsym_term : ∀ j ∈ Finset.Icc 1 r,
          (-1 : ZMod p) ^ j * PowerSeries.coeff r ((1 + PowerSeries.X) ^ (r - j) * inv2Xp ^ (r + 1 - j)) =
          PowerSeries.coeff (r - j) ((1 + PowerSeries.X) ^ r * inv2Xp ^ (r + 1)) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        have h := coeff_rat_symm h2inv_p inv2Xp h2Xp r (r - j)
        rw [hrev.neg_one_pow, one_mul] at h
        rw [show r + 1 - j = (r - j) + 1 by omega]
        have hneg : (-1 : ZMod p) ^ (r - j) = (-1 : ZMod p) ^ j := by
          have hev : Even (r - j + j) := by rw [Nat.sub_add_cancel hj.2]; exact hrev
          calc (-1 : ZMod p) ^ (r - j)
              = (-1 : ZMod p) ^ (r - j) * ((-1 : ZMod p) ^ j * (-1 : ZMod p) ^ j) := by
                rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
            _ = (-1 : ZMod p) ^ (r - j + j) * (-1 : ZMod p) ^ j := by rw [pow_add]; ring
            _ = (-1 : ZMod p) ^ j := by rw [hev.neg_one_pow, one_mul]
        rw [hneg] at h
        exact h
      have hB1 : ∑ j ∈ Finset.Icc 1 r,
            (-1 : ZMod p) ^ j * ((Nat.choose p j / p : ℕ) : ZMod p) *
            PowerSeries.coeff r ((1 + PowerSeries.X) ^ (r - j) * inv2Xp ^ (r + 1 - j)) =
          ∑ j ∈ Finset.Icc 1 r,
            ((Nat.choose p j / p : ℕ) : ZMod p) *
            PowerSeries.coeff (r - j) ((1 + PowerSeries.X) ^ r * inv2Xp ^ (r + 1)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← hsym_term j hj]; ring
      rw [hB1, mul_assoc]
      unfold Alog
      rw [Finset.sum_mul, map_sum]
      trans (∑ j ∈ Finset.Icc 1 r,
          PowerSeries.coeff r (PowerSeries.C ((-1 : ZMod p) ^ (j - 1) * (j : ZMod p)⁻¹) *
            PowerSeries.X ^ j * ((1 + PowerSeries.X) ^ r * inv2Xp ^ (r + 1))))
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
          if_pos hj.2, choose_div_p_zmod hp hj.1 (by omega)]
      · apply Finset.sum_subset
        · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_Ico]; omega
        · intro j hj hnot
          rw [Finset.mem_Ico] at hj; rw [Finset.mem_Icc] at hnot
          rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq_zero (by omega), mul_zero]
    rw [hTermB, hTermA, add_zero]
  have hpS : (p : ZMod (p ^ 2)) * S_err = 0 := p_mul_eq_zero_of_cast_eq_zero hp S_err hS_err_p
  rw [hpS, add_zero] at hQ_coeff
  rw [hQ_coeff]
  exact coeff_two_rat_legendre h2_p2 inv2X h2X k

theorem sum_a179537_eq_sum_choose_cube {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    ((∑ n ∈ Finset.range p, (-1 : ℤ) ^ n * OeisA179537.a n : ℤ) : ZMod (p ^ 2)) =
    ∑ k ∈ Finset.range ((p - 1) / 2 + 1), ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3 := by
  rw [sum_a_swap h3]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2k : 2 * k < p := by
    rcases hodd with ⟨m, rfl⟩
    omega
  have hterm := alt_sum_choose_sq_zmod_p_sq hp h3 h2k
  calc (-16 : ZMod (p ^ 2)) ^ k * ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 2 *
        (∑ n ∈ Finset.range p, (-1 : ZMod (p ^ 2)) ^ n * ((Nat.choose n (2 * k) : ℕ) : ZMod (p ^ 2)) ^ 2)
      = ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 2 *
        ((-16 : ZMod (p ^ 2)) ^ k *
          (∑ n ∈ Finset.range p, (-1 : ZMod (p ^ 2)) ^ n * ((Nat.choose n (2 * k) : ℕ) : ZMod (p ^ 2)) ^ 2)) := by ring
    _ = ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 2 * ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) := by
        rw [hterm]
    _ = ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3 := by ring

end OMA_A179537_Red

namespace OMA_A179537_Glue

private lemma neg_seven_pow_half_of_leg {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hp7 : p ≠ 7)
    (h_leg : letI : Fact (Nat.Prime 7) := ⟨by decide⟩; legendreSym 7 (p : ℤ) = -1) :
    ((-7 : ZMod p) ^ ((p - 1) / 2)) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
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
  have h7p : legendreSym 7 (p : ℤ) = -1 := h_leg
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

end OMA_A179537_Glue

theorem OMA.solution : type_of% @OeisA179537.conjecture2 := by
  intro p hp_fact hp7 h_leg
  have hpr : p.Prime := hp_fact.out
  by_cases h2 : p = 2
  · subst h2
    exfalso
    revert h_leg
    decide
  by_cases h3 : p = 3
  · subst h3
    decide
  have h4 : p ≠ 4 := fun h => by subst h; exact absurd hpr (by decide)
  have h5 : 5 ≤ p := by have := hpr.two_le; omega
  have hleg := OMA_A179537_Glue.neg_seven_pow_half_of_leg hpr h5 hp7 h_leg
  have hHp := OMA_A79727_P2.hasse_inv_eq_zero hpr h5 hleg
  have hA0 := OMA_A79727_P3.A0_eq_zero_zmod_p_sq hpr h5 hleg hHp
  have hred := OMA_A179537_Red.sum_a179537_eq_sum_choose_cube hpr (by omega)
  have hzero : ((∑ k ∈ Finset.range p, (-1 : ℤ) ^ k * OeisA179537.a k : ℤ) : ZMod (p ^ 2)) = 0 := by
    rw [hred, hA0]
  rw [Int.modEq_zero_iff_dvd]
  have hdvd : ((p ^ 2 : ℕ) : ℤ) ∣ ∑ k ∈ Finset.range p, (-1 : ℤ) ^ k * OeisA179537.a k :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  simpa only [Nat.cast_pow] using hdvd
