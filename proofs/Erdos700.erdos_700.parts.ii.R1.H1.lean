import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1
import Mathlib

-- Step Erdos700.erdos_700.parts.ii.R1.H1: hypothesis H1 of reduction Erdos700.erdos_700.parts.ii.R1
-- Credit: @ivillar
-- H1 := ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → p < q → q < r → q - p < r - q →     2 * (r - p) ^ 2 < p → Erdos700.f (p * q * r) ^ 2 > p * q * r  /-- There are arbitrarily large prime triples `p < q < r` with increasing gaps and `2 (r - p)^2 < p`. -/
-- Proof: by Lucas's theorem, a prime l of n = p q r fails to divide C(n, k) only if l divides k and
-- the base-l digits of k stay below those of n. For two primes at once this forces k = x y j, and
-- an explicit digit computation (using q - p < r - q and 2 (r - p)^2 < p) rules out every j.
-- So at least two of p, q, r divide C(n, k), hence gcd(n, C(n, k)) >= p q and f(n)^2 > n.


namespace OMA.E700H1

/-- One step of Lucas's theorem: if `l` does not divide `C(N, K)`, the last base-`l` digit of `K`
is at most that of `N`, and `l` does not divide the binomial of the remaining digits. -/
theorem digit {l N K N1 N0 K1 K0 : ℕ} (hl : l.Prime) (hN : N = N1 * l + N0)
    (hK : K = K1 * l + K0) (hN0 : N0 < l) (hK0 : K0 < l) (h : ¬ l ∣ N.choose K) :
    K0 ≤ N0 ∧ ¬ l ∣ N1.choose K1 := by
  have := Fact.mk hl
  have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := K) (p := l)
  have e1 : N % l = N0 := by
    rw [hN, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hN0]
  have e2 : N / l = N1 := by
    rw [hN, Nat.add_comm, Nat.add_mul_div_right _ _ hl.pos, Nat.div_eq_of_lt hN0, zero_add]
  have e3 : K % l = K0 := by
    rw [hK, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK0]
  have e4 : K / l = K1 := by
    rw [hK, Nat.add_comm, Nat.add_mul_div_right _ _ hl.pos, Nat.div_eq_of_lt hK0, zero_add]
  rw [e1, e2, e3, e4] at hc
  constructor
  · by_contra hlt
    rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hlt), zero_mul] at hc
    exact h (Nat.modEq_zero_iff_dvd.mp hc)
  · intro hd
    apply h
    exact Nat.modEq_zero_iff_dvd.mp
      (hc.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hd _)))

/-- A top digit: `K0 < l` and `l ∤ C(1 * l + N0, K0)` give `K0 ≤ N0`. -/
theorem digit1 {l N0 K0 : ℕ} (hl : l.Prime) (hN0 : N0 < l) (hK0 : K0 < l)
    (h : ¬ l ∣ (1 * l + N0).choose K0) : K0 ≤ N0 :=
  (digit hl rfl (show K0 = 0 * l + K0 by ring) hN0 hK0 h).1

theorem split {l M k : ℕ} (hl : l.Prime) (h : ¬ l ∣ (M * l).choose k) :
    l ∣ k ∧ ¬ l ∣ M.choose (k / l) := by
  have := digit hl (N := M * l) (K := k) (N1 := M) (N0 := 0) (K1 := k / l) (K0 := k % l)
    (by ring) (Nat.div_add_mod' k l).symm hl.pos (Nat.mod_lt _ hl.pos) h
  exact ⟨Nat.dvd_of_mod_eq_zero (by omega), this.2⟩

/-! ### Arithmetic contradictions -/

theorem arA {a s t j b p : ℕ} (ha : 0 < a) (hst : a * j = s * p + t) (ht : t ≤ a * b)
    (hjs : j + s ≤ a + b) (hbj : b < j) (hab : a < b) (hp : 2 * (b * b) < p) : False := by
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    have : a * j ≤ a * b := by linarith
    have := Nat.le_of_mul_le_mul_left this ha
    omega
  · have h1 : p ≤ s * p := Nat.le_mul_of_pos_left p hs0
    have h2 : a * j ≤ a * (a + b) := Nat.mul_le_mul_left a (by omega)
    have h3 : a * a ≤ b * b := Nat.mul_le_mul hab.le hab.le
    have h4 : a * b ≤ b * b := Nat.mul_le_mul_right b hab.le
    nlinarith

theorem arB {a s t j b p : ℕ} (hst : a * j = s * p + t) (ht : t ≤ a * b) (hsa : s < a)
    (hjs : p ≤ j + s) (hab : a ≤ b) (hp : 2 * (b * b) < p) : False := by
  have h3 : a * p ≤ a * (j + s) := Nat.mul_le_mul_left a hjs
  have h4 : (s + 1) * p ≤ a * p := Nat.mul_le_mul_right p hsa
  have h5 : a * s ≤ a * b := Nat.mul_le_mul_left a (by omega)
  have h6 : a * b ≤ b * b := Nat.mul_le_mul_right b hab
  nlinarith

theorem quotLt {a j p s t : ℕ} (ha : 0 < a) (hst : a * j = s * p + t) (hj : j < p) :
    s < a := by
  by_contra hh
  have : a * p ≤ s * p := Nat.mul_le_mul_right p (not_lt.mp hh)
  have : a * j < a * p := Nat.mul_lt_mul_of_pos_left hj ha
  nlinarith

/-! ### The three pairs -/

/-- The pair `p, q = p + a`: `k = p q j` with `0 < j < r`. -/
theorem casePQ (p a b j : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (ha : 0 < a)
    (hab : 2 * a < b) (hs : 2 * (b * b) < p) (hj1 : 1 ≤ j) (hj2 : j < p + b)
    (h1 : ¬ p ∣ ((p + a) * (p + b)).choose ((p + a) * j))
    (h2 : ¬ (p + a) ∣ (p * (p + b)).choose (p * j)) : False := by
  have hab' : a < b := by omega
  have hab2 : a * b < b * b := Nat.mul_lt_mul_of_pos_right hab' (by omega)
  have hbb : b ≤ b * b := Nat.le_mul_self b
  obtain ⟨e, rfl⟩ : ∃ e, b = 2 * a + 1 + e := ⟨b - (2 * a + 1), by omega⟩
  have hle : a * (a + 1 + e) ≤ p + a := by nlinarith
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hle
  have hPR : p * (p + (2 * a + 1 + e)) = (p + a + e) * (p + a) + u := by linarith
  have hu_lt : u < p + a := by nlinarith [Nat.mul_pos ha (show 0 < a + 1 + e by omega)]
  have hPR2 : p + a + e = 1 * (p + a) + e := by ring
  have he_lt : e < p + a := by omega
  have hQR : (p + a) * (p + (2 * a + 1 + e)) =
      (1 * p + (a + (2 * a + 1 + e))) * p + a * (2 * a + 1 + e) := by ring
  have hab_lt : a + (2 * a + 1 + e) < p := by omega
  have hab2' : a * (2 * a + 1 + e) < p := by omega
  rcases Nat.lt_or_ge j p with hjp | hjp
  · rcases Nat.lt_or_ge (2 * a + 1 + e) j with hbj | hbj
    · -- `b < j < p`
      obtain ⟨s, t, hst, ht⟩ : ∃ s t, a * j = s * p + t ∧ t < p :=
        ⟨a * j / p, a * j % p, (Nat.div_add_mod' _ _).symm, Nat.mod_lt _ hp.pos⟩
      have hK : (p + a) * j = (j + s) * p + t := by linarith
      obtain ⟨d1, d2⟩ := digit hp hQR hK hab2' ht h1
      have hsa : s < a := quotLt ha hst hjp
      rcases Nat.lt_or_ge (j + s) p with hjs | hjs
      · have := digit1 hp hab_lt hjs d2
        exact arA ha hst d1 this hbj hab' hs
      · exact arB hst d1 hsa hjs hab'.le hs
    · -- `j ≤ b`
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hle2 : a * (j' + 1) ≤ p + a := by
        have : a * (j' + 1) ≤ a * (2 * a + 1 + e) := Nat.mul_le_mul_left a hbj
        omega
      obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hle2
      have hK : p * (j' + 1) = j' * (p + a) + w := by linarith
      have hw_lt : w < p + a := by nlinarith [Nat.mul_pos ha (show 0 < j' + 1 by omega)]
      obtain ⟨d1, d2⟩ := digit hq hPR hK hu_lt hw_lt h2
      rw [hPR2] at d2
      have d3 := digit1 (K0 := j') hq he_lt (by omega) d2
      have : a * (j' + 1) ≤ a * (e + 1) := Nat.mul_le_mul_left a (by omega)
      nlinarith [Nat.mul_pos ha ha]
  · -- `p ≤ j < r`
    obtain ⟨c, rfl⟩ : ∃ c, j = p + c := ⟨j - p, by omega⟩
    rcases Nat.lt_or_ge a c with hac | hac
    · obtain ⟨g, rfl⟩ : ∃ g, c = a + g + 1 := ⟨c - a - 1, by omega⟩
      have hle3 : a * (g + 1) ≤ p + a := by
        have : a * (g + 1) ≤ a * (2 * a + 1 + e) := Nat.mul_le_mul_left a (by omega)
        omega
      obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hle3
      have hK : p * (p + (a + g + 1)) = (p + g) * (p + a) + v := by linarith
      have hv_lt : v < p + a := by nlinarith [Nat.mul_pos ha (show 0 < g + 1 by omega)]
      obtain ⟨d1, -⟩ := digit hq hPR hK hu_lt hv_lt h2
      have : a * (a + 1 + e) ≤ a * (g + 1) := by omega
      have := Nat.le_of_mul_le_mul_left this ha
      omega
    · obtain ⟨g, rfl⟩ : ∃ g, a = c + g := ⟨a - c, by omega⟩
      obtain ⟨h, rfl⟩ : ∃ h, p = g + h := ⟨p - g, by omega⟩
      have hK : (g + h) * (g + h + c) = h * (g + h + (c + g)) + (c + g) * g := by ring
      have hK0 : (c + g) * g < g + h + (c + g) := by
        have : (c + g) * g ≤ (c + g) * (c + g) := Nat.mul_le_mul_left _ (by omega)
        nlinarith
      obtain ⟨-, d2⟩ := digit hq hPR hK hu_lt hK0 h2
      rw [hPR2] at d2
      have := digit1 (K0 := h) hq he_lt (by omega) d2
      nlinarith

/-- The pair `p, r = p + b`: `k = p r j` with `0 < j < q`. -/
theorem casePR (p a b j : ℕ) (hp : p.Prime) (hr : (p + b).Prime) (ha : 0 < a)
    (hab : 2 * a < b) (hs : 2 * (b * b) < p) (hj1 : 1 ≤ j) (hj2 : j < p + a)
    (h1 : ¬ p ∣ ((p + a) * (p + b)).choose ((p + b) * j))
    (h2 : ¬ (p + b) ∣ (p * (p + a)).choose (p * j)) : False := by
  have hab' : a < b := by omega
  have hab2 : a * b < b * b := Nat.mul_lt_mul_of_pos_right hab' (by omega)
  have hbb : b ≤ b * b := Nat.le_mul_self b
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, p = d + m := ⟨p - d, by omega⟩
  have hPQ : p * (p + a) = m * (p + (a + d)) + (a + d) * d := by subst hm; ring
  have hbd_lt : (a + d) * d < p + (a + d) := by
    have : (a + d) * d ≤ (a + d) * (a + d) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hQR : (p + a) * (p + (a + d)) = (1 * p + (a + (a + d))) * p + a * (a + d) := by ring
  have hab_lt : a + (a + d) < p := by omega
  have hab2' : a * (a + d) < p := by omega
  rcases Nat.lt_or_ge j p with hjp | hjp
  · obtain ⟨s, t, hst, ht⟩ : ∃ s t, (a + d) * j = s * p + t ∧ t < p :=
      ⟨(a + d) * j / p, (a + d) * j % p, (Nat.div_add_mod' _ _).symm, Nat.mod_lt _ hp.pos⟩
    have hK : (p + (a + d)) * j = (j + s) * p + t := by linarith
    obtain ⟨d1, d2⟩ := digit hp hQR hK hab2' ht h1
    have hsb : s < a + d := quotLt (by omega) hst hjp
    rcases Nat.lt_or_ge (j + s) p with hjs | hjs
    · have d3 := digit1 hp hab_lt hjs d2
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · subst hs0
        have : (a + d) * j ≤ (a + d) * a := by rw [mul_comm (a + d) a]; omega
        have hja := Nat.le_of_mul_le_mul_left this (by omega)
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hle2 : (a + d) * (j' + 1) ≤ p + (a + d) := by omega
        obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hle2
        have hK2 : p * (j' + 1) = j' * (p + (a + d)) + w := by linarith
        have hw_lt : w < p + (a + d) := by
          nlinarith [Nat.mul_pos (show 0 < a + d by omega) (show 0 < j' + 1 by omega)]
        obtain ⟨d4, -⟩ := digit hr hPQ hK2 hbd_lt hw_lt h2
        have : (a + d) * (j' + 1) ≤ (a + d) * a := Nat.mul_le_mul_left _ hja
        nlinarith
      · have h1' : p ≤ s * p := Nat.le_mul_of_pos_left p hs0
        have h2' : (a + d) * j ≤ (a + d) * (a + (a + d)) := Nat.mul_le_mul_left _ (by omega)
        nlinarith
    · have ht' : t ≤ (a + d) * (a + d) := by
        have : a * (a + d) ≤ (a + d) * (a + d) := Nat.mul_le_mul_right _ (by omega)
        omega
      exact arB hst ht' hsb hjs le_rfl hs
  · obtain ⟨c, rfl⟩ : ∃ c, j = p + c := ⟨j - p, by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, a + d = c + g := ⟨a + d - c, by omega⟩
    obtain ⟨h, hh⟩ : ∃ h, p = g + h := ⟨p - g, by omega⟩
    have hK : p * (p + c) = h * (p + (a + d)) + (a + d) * g := by subst hh; rw [hg]; ring
    have hK0 : (a + d) * g < p + (a + d) := by
      have : (a + d) * g ≤ (a + d) * (a + d) := Nat.mul_le_mul_left _ (by omega)
      omega
    obtain ⟨d1, -⟩ := digit hr hPQ hK hbd_lt hK0 h2
    have := Nat.le_of_mul_le_mul_left d1 (show 0 < a + d by omega)
    omega

/-- The pair `q = p + a, r = p + b`: `k = q r j` with `0 < j < p`. -/
theorem caseQR (p a b j : ℕ) (hq : (p + a).Prime) (hr : (p + b).Prime) (ha : 0 < a)
    (hab : 2 * a < b) (hs : 2 * (b * b) < p) (hj1 : 1 ≤ j) (hj2 : j < p)
    (h1 : ¬ (p + a) ∣ (p * (p + b)).choose ((p + b) * j))
    (h2 : ¬ (p + b) ∣ (p * (p + a)).choose ((p + a) * j)) : False := by
  have hab' : a < b := by omega
  have hab2 : a * b < b * b := Nat.mul_lt_mul_of_pos_right hab' (by omega)
  have hbb : b ≤ b * b := Nat.le_mul_self b
  obtain ⟨e, rfl⟩ : ∃ e, b = 2 * a + 1 + e := ⟨b - (2 * a + 1), by omega⟩
  have hdb : (a + 1 + e) * (a + 1 + e) ≤ (2 * a + 1 + e) * (2 * a + 1 + e) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hdb2 : (2 * a + 1 + e) * (a + 1 + e) ≤ (2 * a + 1 + e) * (2 * a + 1 + e) :=
    Nat.mul_le_mul_left _ (by omega)
  have hle : a * (a + 1 + e) ≤ p + a := by
    have : a * (a + 1 + e) ≤ (2 * a + 1 + e) * (2 * a + 1 + e) := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hle
  have hPR : p * (p + (2 * a + 1 + e)) = (p + a + e) * (p + a) + u := by linarith
  have hu_lt : u < p + a := by
    have := Nat.mul_pos ha (show 0 < a + 1 + e by omega)
    omega
  have hPR2 : p + a + e = 1 * (p + a) + e := by ring
  have he_lt : e < p + a := by omega
  obtain ⟨m, hm⟩ : ∃ m, p = (a + 1 + e) + m := ⟨p - (a + 1 + e), by omega⟩
  have hPQ : p * (p + a) = m * (p + (2 * a + 1 + e)) + (2 * a + 1 + e) * (a + 1 + e) := by
    subst hm; ring
  have hbd_lt : (2 * a + 1 + e) * (a + 1 + e) < p + (2 * a + 1 + e) := by omega
  rcases Nat.lt_or_ge (p + a) (j + (a + 1 + e)) with hjd | hjd
  · -- `j` close to `q`: only the prime `r` is needed
    obtain ⟨f, hf⟩ : ∃ f, p + a = j + f := ⟨p + a - j, by omega⟩
    obtain ⟨M, hM⟩ : ∃ M, j = (a + 1 + e) + M := ⟨j - (a + 1 + e), by omega⟩
    have hpa : p + a = (a + 1 + e) + M + f := by omega
    have hK : (p + a) * j = M * (p + (2 * a + 1 + e)) + (a + 1 + e) * ((a + 1 + e) + f) := by
      rw [show p + (2 * a + 1 + e) = (p + a) + (a + 1 + e) by ring, hpa, hM]; ring
    have hK0 : (a + 1 + e) * ((a + 1 + e) + f) < p + (2 * a + 1 + e) := by
      have : (a + 1 + e) * ((a + 1 + e) + f) ≤ (a + 1 + e) * (a + 1 + e) + (a + 1 + e) * (a + 1 + e) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    obtain ⟨d1, -⟩ := digit hr hPQ hK hbd_lt hK0 h2
    rw [mul_comm (2 * a + 1 + e) (a + 1 + e)] at d1
    have := Nat.le_of_mul_le_mul_left d1 (show 0 < a + 1 + e by omega)
    omega
  · obtain ⟨s, t, hst, ht⟩ : ∃ s t, (a + 1 + e) * j = s * (p + a) + t ∧ t < p + a :=
      ⟨(a + 1 + e) * j / (p + a), (a + 1 + e) * j % (p + a), (Nat.div_add_mod' _ _).symm,
        Nat.mod_lt _ hq.pos⟩
    have hK : (p + (2 * a + 1 + e)) * j = (j + s) * (p + a) + t := by linarith
    obtain ⟨-, d2⟩ := digit hq hPR hK hu_lt ht h1
    have hsd : s < a + 1 + e := by
      have h3 : (a + 1 + e) * j + (a + 1 + e) * (a + 1 + e) ≤ (a + 1 + e) * (p + a) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hjd
      have h4 : s * (p + a) < (a + 1 + e) * (p + a) := by
        have := Nat.mul_pos (show 0 < a + 1 + e by omega) (show 0 < a + 1 + e by omega)
        omega
      exact Nat.lt_of_mul_lt_mul_right h4
    rw [hPR2] at d2
    have d3 := digit1 (K0 := j + s) hq he_lt (by omega) d2
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hde : (a + 1 + e) * (j' + 1) ≤ (a + 1 + e) * e := Nat.mul_le_mul_left _ (by omega)
    have hde2 : (a + 1 + e) * e ≤ (a + 1 + e) * (a + 1 + e) := Nat.mul_le_mul_left _ (by omega)
    have hle2 : (a + 1 + e) * (j' + 1) ≤ p + (2 * a + 1 + e) := by omega
    obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hle2
    have hK2 : (p + a) * (j' + 1) = j' * (p + (2 * a + 1 + e)) + w := by linarith
    have hw_lt : w < p + (2 * a + 1 + e) := by
      have := Nat.mul_pos (show 0 < a + 1 + e by omega) (show 0 < j' + 1 by omega)
      omega
    obtain ⟨d4, -⟩ := digit hr hPQ hK2 hbd_lt hw_lt h2
    omega

theorem pairBound {n C x y : ℕ} (hn : 0 < n) (hx : x.Prime) (hy : y.Prime) (hxy : x ≠ y)
    (hxn : x ∣ n) (hyn : y ∣ n) (hxc : x ∣ C) (hyc : y ∣ C) : x * y ≤ Nat.gcd n C :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hx hy).mpr hxy)
      (Nat.dvd_gcd hxn hxc) (Nat.dvd_gcd hyn hyc))

theorem twoPrimes (p a b k : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (hr : (p + b).Prime)
    (ha : 0 < a) (hab : 2 * a < b) (hs : 2 * (b * b) < p) (hk0 : 0 < k)
    (hkn : k < p * (p + a) * (p + b)) :
    p * (p + a) ≤ Nat.gcd (p * (p + a) * (p + b)) ((p * (p + a) * (p + b)).choose k) := by
  have hn0 : 0 < p * (p + a) * (p + b) := by
    have := hp.pos; positivity
  have hpn : p ∣ p * (p + a) * (p + b) := ⟨(p + a) * (p + b), by ring⟩
  have hqn : (p + a) ∣ p * (p + a) * (p + b) := ⟨p * (p + b), by ring⟩
  have hrn : (p + b) ∣ p * (p + a) * (p + b) := ⟨p * (p + a), by ring⟩
  have hpq : p ≠ p + a := by omega
  have hpr : p ≠ p + b := by omega
  have hqr : p + a ≠ p + b := by omega
  have e1 : p * (p + a) * (p + b) = ((p + a) * (p + b)) * p := by ring
  have e2 : p * (p + a) * (p + b) = (p * (p + b)) * (p + a) := by ring
  have e3 : p * (p + a) * (p + b) = (p * (p + a)) * (p + b) := by ring
  have hqb : p * (p + a) ≤ p * (p + b) := Nat.mul_le_mul_left _ (by omega)
  have hqb2 : p * (p + a) ≤ (p + a) * (p + b) := by
    rw [mul_comm p]; exact Nat.mul_le_mul_left _ (by omega)
  by_cases hP : p ∣ (p * (p + a) * (p + b)).choose k
  · by_cases hQ : (p + a) ∣ (p * (p + a) * (p + b)).choose k
    · exact pairBound hn0 hp hq hpq hpn hqn hP hQ
    · by_cases hR : (p + b) ∣ (p * (p + a) * (p + b)).choose k
      · exact hqb.trans (pairBound hn0 hp hr hpr hpn hrn hP hR)
      · exfalso
        rw [e2] at hQ
        rw [e3] at hR
        obtain ⟨hqk, h1⟩ := split hq hQ
        obtain ⟨hrk, h2⟩ := split hr hR
        obtain ⟨j, rfl⟩ := ((Nat.coprime_primes hq hr).mpr hqr).mul_dvd_of_dvd_of_dvd hqk hrk
        rw [show (p + a) * (p + b) * j / (p + a) = (p + b) * j by
          rw [mul_assoc]; exact Nat.mul_div_cancel_left _ hq.pos] at h1
        rw [show (p + a) * (p + b) * j / (p + b) = (p + a) * j by
          rw [mul_comm (p + a) (p + b), mul_assoc]; exact Nat.mul_div_cancel_left _ hr.pos] at h2
        have hj1 : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · subst h0; simp at hk0
          · exact h0
        have hj2 : j < p := by
          have : (p + a) * (p + b) * j < (p + a) * (p + b) * p := by
            calc (p + a) * (p + b) * j < p * (p + a) * (p + b) := hkn
              _ = (p + a) * (p + b) * p := by ring
          exact Nat.lt_of_mul_lt_mul_left this
        exact caseQR p a b j hq hr ha hab hs hj1 hj2 h1 h2
  · by_cases hQ : (p + a) ∣ (p * (p + a) * (p + b)).choose k
    · by_cases hR : (p + b) ∣ (p * (p + a) * (p + b)).choose k
      · exact hqb2.trans (pairBound hn0 hq hr hqr hqn hrn hQ hR)
      · exfalso
        rw [e1] at hP
        rw [e3] at hR
        obtain ⟨hpk, h1⟩ := split hp hP
        obtain ⟨hrk, h2⟩ := split hr hR
        obtain ⟨j, rfl⟩ := ((Nat.coprime_primes hp hr).mpr hpr).mul_dvd_of_dvd_of_dvd hpk hrk
        rw [show p * (p + b) * j / p = (p + b) * j by
          rw [mul_assoc]; exact Nat.mul_div_cancel_left _ hp.pos] at h1
        rw [show p * (p + b) * j / (p + b) = p * j by
          rw [mul_comm p (p + b), mul_assoc]; exact Nat.mul_div_cancel_left _ hr.pos] at h2
        have hj1 : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · subst h0; simp at hk0
          · exact h0
        have hj2 : j < p + a := by
          have : p * (p + b) * j < p * (p + b) * (p + a) := by
            calc p * (p + b) * j < p * (p + a) * (p + b) := hkn
              _ = p * (p + b) * (p + a) := by ring
          exact Nat.lt_of_mul_lt_mul_left this
        exact casePR p a b j hp hr ha hab hs hj1 hj2 h1 h2
    · exfalso
      rw [e1] at hP
      rw [e2] at hQ
      obtain ⟨hpk, h1⟩ := split hp hP
      obtain ⟨hqk, h2⟩ := split hq hQ
      obtain ⟨j, rfl⟩ := ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpk hqk
      rw [show p * (p + a) * j / p = (p + a) * j by
        rw [mul_assoc]; exact Nat.mul_div_cancel_left _ hp.pos] at h1
      rw [show p * (p + a) * j / (p + a) = p * j by
        rw [mul_comm p (p + a), mul_assoc]; exact Nat.mul_div_cancel_left _ hq.pos] at h2
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; simp at hk0
        · exact h0
      have hj2 : j < p + b := by
        have : p * (p + a) * j < p * (p + a) * (p + b) := hkn
        exact Nat.lt_of_mul_lt_mul_left this
      exact casePQ p a b j hp hq ha hab hs hj1 hj2 h1 h2

theorem final (p a b : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (hr : (p + b).Prime)
    (ha : 0 < a) (hab : 2 * a < b) (hs : 2 * (b * b) < p) :
    Erdos700.f (p * (p + a) * (p + b)) ^ 2 > p * (p + a) * (p + b) := by
  have hp2 := hp.two_le
  have hbp : b < p := by nlinarith
  have hn4 : 2 ≤ p * (p + a) * (p + b) / 2 := by
    have h1 : 2 * 2 ≤ p * (p + a) := Nat.mul_le_mul hp2 (by omega)
    have h2 : p * (p + a) ≤ p * (p + a) * (p + b) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hne : (Erdos700.fSet (p * (p + a) * (p + b))).Nonempty :=
    ⟨_, Erdos700.f_mem _ 2 (by norm_num) hn4⟩
  obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
  rw [Erdos700.f_eq, hkeq]
  have hk0 : 0 < k := by omega
  have hkn : k < p * (p + a) * (p + b) := by omega
  have hg := twoPrimes p a b k hp hq hr ha hab hs hk0 hkn
  have h1 : p + b < p * (p + a) := by nlinarith
  have h2 : p * (p + a) * (p + b) < (p * (p + a)) * (p * (p + a)) :=
    Nat.mul_lt_mul_of_pos_left h1 (by positivity)
  have h3 := Nat.mul_le_mul hg hg
  rw [sq]
  omega

end OMA.E700H1

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H1 := by
  unfold OMA.R_Erdos700_erdos_700_parts_ii_R1.H1
  intro p q r hp hq hr hpq hqr hgap hsmall
  obtain ⟨a, rfl⟩ : ∃ a, q = p + a := ⟨q - p, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, r = p + b := ⟨r - p, by omega⟩
  have ha : 0 < a := by omega
  have hab : 2 * a < b := by omega
  have hs : 2 * (b * b) < p := by
    rw [Nat.add_sub_cancel_left, sq] at hsmall
    exact hsmall
  exact OMA.E700H1.final p a b hp hq hr ha hab hs
