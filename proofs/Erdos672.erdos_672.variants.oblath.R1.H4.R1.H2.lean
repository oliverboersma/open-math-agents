import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1
import Mathlib

/-!
# Step H2 of Erdős 672 (Obláth): No Positive Solutions to `g ^ 5 + 8 * b ^ 5 = s ^ 5`

We prove `OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1.H2`, namely that for positive natural
numbers `b` and `g`, `g ^ 5 + 8 * b ^ 5 ≠ s ^ 5`.

After dividing out any common prime factor of `g` and `s`, the equation splits into two branches
according to whether `5` divides `b`:
* When `5 ∤ b`, unique factorization in the PID `𝓞 (CyclotomicField 5 ℚ)` together with Kronecker's
  unit-conjugation identity forces a congruence modulo `5` incompatible with `g ^ 5 + 8 * b ^ 5 = s ^ 5`
  modulo `25`.
* When `5 ∣ b`, Dirichlet's 1825 fifth-power infinite descent in the Euclidean golden-ratio ring
  `QuadraticAlgebra ℤ 1 1` (`ℤ[(1 + √5)/2]`) yields an infinite descent on `b.natAbs`.
-/

open NumberField QuadraticAlgebra

namespace OMA672H2

/- ## Section 1: Euclidean Structure and Units of `ℤ[(1 + √5)/2]` -/

abbrev R := QuadraticAlgebra ℤ 1 1

lemma five_dvd_of_sq_dvd {x : ℤ} (h : (5 : ℤ) ∣ x ^ 2) : (5 : ℤ) ∣ x :=
  Int.Prime.dvd_pow' Nat.prime_five h

lemma not_isUnit_five : ¬ IsUnit (5 : ℤ) := by
  rw [Int.isUnit_iff]
  omega

lemma isCoprime_five_of_not_dvd {n : ℤ} (h : ¬ (5 : ℤ) ∣ n) : IsCoprime n 5 := by
  have hdiv : 5 * (n / 5) + n % 5 = n := Int.mul_ediv_add_emod n 5
  have hr0 : 0 ≤ n % 5 := Int.emod_nonneg n (by omega)
  have hr5 : n % 5 < 5 := Int.emod_lt_of_pos n (by omega)
  have hr_ne : n % 5 ≠ 0 := fun h0 => h (Int.dvd_of_emod_eq_zero h0)
  set q := n / 5
  set r := n % 5
  interval_cases r
  · exact absurd rfl hr_ne
  · exact ⟨1, -q, by omega⟩
  · exact ⟨3, -3 * q - 1, by omega⟩
  · exact ⟨2, -2 * q - 1, by omega⟩
  · exact ⟨-1, q + 1, by omega⟩

lemma even_iff_zmod2 (n : ℤ) : Even n ↔ (n : ZMod 2) = 0 := by
  have h2 : Even n ↔ ((2 : ℕ) : ℤ) ∣ n :=
    ⟨fun ⟨k, hk⟩ => ⟨k, by omega⟩, fun ⟨k, hk⟩ => ⟨k, by omega⟩⟩
  rw [h2, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma odd_iff_zmod2 (n : ℤ) : Odd n ↔ (n : ZMod 2) = 1 := by
  rw [← Int.not_even_iff_odd, even_iff_zmod2]
  generalize (n : ZMod 2) = x
  revert x; decide

lemma norm_eq_zero_aux : ∀ n : ℕ, ∀ x y : ℤ, y.natAbs = n →
    (2 * x + y) ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn h
    have h5a : (5 : ℤ) ∣ (2 * x + y) := five_dvd_of_sq_dvd (h ▸ dvd_mul_right 5 _)
    obtain ⟨k, hk⟩ := h5a
    have hy2 : y ^ 2 = 5 * k ^ 2 := by
      have h25 : 25 * k ^ 2 = 5 * y ^ 2 := by
        calc 25 * k ^ 2 = (5 * k) ^ 2 := by ring
          _ = 5 * y ^ 2 := by rw [← hk, h]
      linarith
    have h5y : (5 : ℤ) ∣ y := five_dvd_of_sq_dvd (hy2 ▸ dvd_mul_right 5 _)
    obtain ⟨y1, rfl⟩ := h5y
    have h5x : (5 : ℤ) ∣ x := by
      have h2x : (5 : ℤ) ∣ 2 * x := ⟨k - y1, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h2x with h2 | hx
      · norm_num at h2
      · exact hx
    obtain ⟨x1, rfl⟩ := h5x
    by_cases hy0 : y1 = 0
    · subst hy0
      simp at h
      exact ⟨by omega, rfl⟩
    · have h1 : (2 * x1 + y1) ^ 2 = 5 * y1 ^ 2 := by
        have : 25 * (2 * x1 + y1) ^ 2 = 25 * (5 * y1 ^ 2) := by linear_combination h
        linarith
      have hlt : y1.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have hypos : 0 < y1.natAbs := Int.natAbs_pos.mpr hy0
        have h5 : (5 : ℤ).natAbs = 5 := rfl
        rw [h5]
        omega
      obtain ⟨hx1, hy1⟩ := ih _ hlt x1 y1 rfl h1
      exact ⟨by simp [hx1], by simp [hy1]⟩

lemma R_norm_eq_zero {z : R} (hz : z.norm = 0) : z = 0 := by
  have h4 : (2 * z.re + z.im) ^ 2 = 5 * z.im ^ 2 := by
    have : z.re * z.re + 1 * z.re * z.im - 1 * z.im * z.im = 0 := hz
    linear_combination 4 * this
  obtain ⟨hre, him⟩ := norm_eq_zero_aux _ z.re z.im rfl h4
  ext <;> simp [hre, him]

instance : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have hn : a.norm * b.norm = 0 := by
      rw [← map_mul, hab, QuadraticAlgebra.norm_zero]
    rcases mul_eq_zero.mp hn with ha | hb
    · exact Or.inl (R_norm_eq_zero ha)
    · exact Or.inr (R_norm_eq_zero hb)

instance : IsDomain R := NoZeroDivisors.to_isDomain R

def nearestDiv (N d : ℤ) : ℤ :=
  let Ns := if 0 ≤ d then N else -N
  (2 * Ns + |d|) / (2 * |d|)

lemma nearestDiv_spec (N : ℤ) {d : ℤ} (hd : d ≠ 0) :
    4 * (N - nearestDiv N d * d) ^ 2 ≤ d ^ 2 := by
  dsimp [nearestDiv]
  set Ns := if 0 ≤ d then N else -N
  have hd_pos : 0 < |d| := abs_pos.mpr hd
  have h2d : 0 < 2 * |d| := by omega
  set q := (2 * Ns + |d|) / (2 * |d|)
  set r := (2 * Ns + |d|) % (2 * |d|)
  have hdiv : 2 * |d| * q + r = 2 * Ns + |d| := Int.mul_ediv_add_emod (2 * Ns + |d|) (2 * |d|)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hr1 : r < 2 * |d| := Int.emod_lt_of_pos _ h2d
  have hdiff : (N - q * d) ^ 2 = (Ns - q * |d|) ^ 2 := by
    by_cases h : 0 ≤ d
    · simp [Ns, h, abs_of_nonneg h]
    · have h' : d < 0 := lt_of_not_ge h
      simp [Ns, h, abs_of_neg h']
      ring
  rw [hdiff]
  have heq : 2 * (Ns - q * |d|) = r - |d| := by linear_combination -hdiv
  have hlin1 : -|d| ≤ 2 * (Ns - q * |d|) := by omega
  have hlin2 : 2 * (Ns - q * |d|) ≤ |d| := by omega
  have hsq : (2 * (Ns - q * |d|)) ^ 2 ≤ |d| ^ 2 := by nlinarith
  have habs : |d| ^ 2 = d ^ 2 := sq_abs d
  nlinarith

def R_div (a b : R) : R :=
  if b = 0 then 0 else
    let d := b.norm
    let num := a * star b
    ⟨nearestDiv num.re d, nearestDiv num.im d⟩

instance : EuclideanDomain R where
  quotient := R_div
  quotient_zero a := by simp [R_div]
  remainder a b := a - R_div a b * b
  quotient_mul_add_remainder_eq a b := by ring
  r a b := a.norm.natAbs < b.norm.natAbs
  r_wellFounded := InvImage.wf (fun z : R => z.norm.natAbs) wellFounded_lt
  remainder_lt a {b} hb := by
    have hd : b.norm ≠ 0 := fun h => hb (R_norm_eq_zero h)
    have hq : R_div a b = ⟨nearestDiv (a * star b).re b.norm, nearestDiv (a * star b).im b.norm⟩ := by
      simp [R_div, hb]
    set q := R_div a b
    set rem := a - q * b
    set d := b.norm
    set X := (a * star b).re - q.re * d
    set Y := (a * star b).im - q.im * d
    have hX : 4 * X ^ 2 ≤ d ^ 2 := by
      dsimp only [X]
      rw [hq]
      exact nearestDiv_spec _ hd
    have hY : 4 * Y ^ 2 ≤ d ^ 2 := by
      dsimp only [Y]
      rw [hq]
      exact nearestDiv_spec _ hd
    have hrem_mul : rem * star b = ⟨X, Y⟩ := by
      have hbb : b * star b = algebraMap ℤ R d := (algebraMap_norm_eq_mul_star b).symm
      calc rem * star b = a * star b - q * (b * star b) := by ring
        _ = a * star b - q * algebraMap ℤ R d := by rw [hbb]
        _ = ⟨X, Y⟩ := by ext <;> simp [X, Y]
    have hnorm_prod : rem.norm * d = X * X + 1 * X * Y - 1 * Y * Y := by
      have := congr_arg QuadraticAlgebra.norm hrem_mul
      rw [map_mul, QuadraticAlgebra.norm_star] at this
      exact this
    have hd2_pos : 1 ≤ d ^ 2 := by
      have : 0 < d ^ 2 := sq_pos_of_ne_zero hd
      omega
    have hup : rem.norm * d < d ^ 2 := by
      have : 16 * (rem.norm * d) = 20 * X ^ 2 - 4 * (X - 2 * Y) ^ 2 := by
        rw [hnorm_prod]; ring
      nlinarith [sq_nonneg (X - 2 * Y)]
    have hlo : -(d ^ 2) < rem.norm * d := by
      have : 16 * (rem.norm * d) = 4 * (2 * X + Y) ^ 2 - 20 * Y ^ 2 := by
        rw [hnorm_prod]; ring
      nlinarith [sq_nonneg (2 * X + Y)]
    have habs_lt : (rem.norm * d).natAbs < (d ^ 2).natAbs := by
      rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
        abs_of_pos (show 0 < d ^ 2 by omega), abs_lt]
      exact ⟨hlo, hup⟩
    rw [Int.natAbs_mul, sq, Int.natAbs_mul] at habs_lt
    exact Nat.lt_of_mul_lt_mul_right habs_lt
  mul_left_not_lt a {b} hb := by
    rw [map_mul, Int.natAbs_mul]
    have hbn : b.norm ≠ 0 := fun h => hb (R_norm_eq_zero h)
    have hb1 : 1 ≤ b.norm.natAbs := Int.natAbs_pos.mpr hbn
    exact not_lt.mpr (Nat.le_mul_of_pos_right _ hb1)

def ω₀ : R := ⟨0, 1⟩
def ω_inv : R := ⟨-1, 1⟩

lemma ω₀_mul_inv : ω₀ * ω_inv = 1 := by
  ext <;> simp [ω₀, ω_inv]

lemma isUnit_ω₀ : IsUnit ω₀ :=
  ⟨⟨ω₀, ω_inv, ω₀_mul_inv, by rw [mul_comm]; exact ω₀_mul_inv⟩, rfl⟩

lemma isUnit_ω_inv : IsUnit ω_inv :=
  ⟨⟨ω_inv, ω₀, by rw [mul_comm]; exact ω₀_mul_inv, ω₀_mul_inv⟩, rfl⟩

lemma unit_form_neg {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ -v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  exact ⟨r, hr, -η, hη.neg, by ring⟩

lemma unit_form_mul_ω₀ {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ ω₀ * v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  rw [Finset.mem_range] at hr
  interval_cases r
  · exact ⟨1, by simp, η, hη, by ring⟩
  · exact ⟨2, by simp, η, hη, by ring⟩
  · exact ⟨3, by simp, η, hη, by ring⟩
  · exact ⟨4, by simp, η, hη, by ring⟩
  · exact ⟨0, by simp, ω₀ * η, isUnit_ω₀.mul hη, by ring⟩

lemma unit_form_mul_inv {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ ω_inv * v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  rw [Finset.mem_range] at hr
  interval_cases r
  · refine ⟨4, by simp, ω_inv * η, isUnit_ω_inv.mul hη, ?_⟩
    have h4 : ω₀ ^ 4 * ω_inv ^ 5 = ω_inv := by
      calc ω₀ ^ 4 * ω_inv ^ 5 = (ω₀ * ω_inv) ^ 4 * ω_inv := by ring
        _ = ω_inv := by rw [ω₀_mul_inv]; ring
    calc ω_inv * (ω₀ ^ 0 * η ^ 5) = ω_inv * η ^ 5 := by ring
      _ = (ω₀ ^ 4 * ω_inv ^ 5) * η ^ 5 := by rw [h4]
      _ = ω₀ ^ 4 * (ω_inv * η) ^ 5 := by ring
  · refine ⟨0, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 1 * η ^ 5) = (ω₀ * ω_inv) * η ^ 5 := by ring
      _ = ω₀ ^ 0 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨1, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 2 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 1 * η ^ 5) := by ring
      _ = ω₀ ^ 1 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨2, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 3 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 2 * η ^ 5) := by ring
      _ = ω₀ ^ 2 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨3, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 4 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 3 * η ^ 5) := by ring
      _ = ω₀ ^ 3 * η ^ 5 := by rw [ω₀_mul_inv]; ring

lemma unit_form_aux : ∀ n : ℕ, ∀ u : R, u.re.natAbs + u.im.natAbs = n →
    (u.norm = 1 ∨ u.norm = -1) →
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ u = ω₀ ^ r * η ^ 5 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hn hnorm
    set x := u.re
    set y := u.im
    have hu : u = ⟨x, y⟩ := (QuadraticAlgebra.mk_eta u).symm
    have hxy : x * x + 1 * x * y - 1 * y * y = 1 ∨ x * x + 1 * x * y - 1 * y * y = -1 := hnorm
    by_cases hy0 : y = 0
    · rcases hxy with h1 | h1
      · rw [hy0] at h1
        have hx1 : x = 1 ∨ x = -1 := sq_eq_one_iff.mp (by linarith)
        rcases hx1 with hx1 | hx1
        · exact ⟨0, by simp, 1, isUnit_one, by rw [hu, hx1, hy0]; ext <;> simp⟩
        · refine ⟨0, by simp, -1, isUnit_one.neg, ?_⟩
          rw [show (-1 : R) ^ 5 = -1 by ring, hu, hx1, hy0]
          ext <;> simp
      · exfalso
        rw [hy0] at h1
        nlinarith [sq_nonneg x]
    · by_cases hx0 : x = 0
      · rcases hxy with h1 | h1
        · exfalso
          rw [hx0] at h1
          nlinarith [sq_nonneg y]
        · rw [hx0] at h1
          have hy1 : y = 1 ∨ y = -1 := sq_eq_one_iff.mp (by linarith)
          rcases hy1 with hy1 | hy1
          · exact ⟨1, by simp, 1, isUnit_one, by rw [hu, hx0, hy1]; ext <;> simp [ω₀]⟩
          · refine ⟨1, by simp, -1, isUnit_one.neg, ?_⟩
            rw [show (-1 : R) ^ 5 = -1 by ring, hu, hx0, hy1]
            ext <;> simp [ω₀]
      · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos <;>
        rcases lt_or_gt_of_ne hy0 with hyneg | hypos
        · set u' := ω_inv * (-u)
          have hu'_eq : u' = ⟨x - y, -x⟩ := by
            dsimp [u']; rw [hu]; ext
            · simp [ω_inv]; ring
            · simp [ω_inv]
          have hxley : y ≤ x := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hinv_n : ω_inv.norm = -1 := by decide
            rw [map_mul, QuadraticAlgebra.norm_neg, hinv_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_neg (unit_form_mul_ω₀ (ih _ hlt u' rfl hu'_norm))
          have heq : -(ω₀ * u') = u := by
            dsimp [u']
            calc -(ω₀ * (ω_inv * -u)) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω₀ * (-u)
          have hu'_eq : u' = ⟨-y, -x - y⟩ := by
            dsimp [u']; rw [hu]; ext
            · simp [ω₀]
            · simp [ω₀]; ring
          have hy_le : y ≤ -x := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hω_n : ω₀.norm = -1 := by decide
            rw [map_mul, QuadraticAlgebra.norm_neg, hω_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_neg (unit_form_mul_inv (ih _ hlt u' rfl hu'_norm))
          have heq : -(ω_inv * u') = u := by
            dsimp [u']
            calc -(ω_inv * (ω₀ * -u)) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω₀ * u
          have hu'_eq : u' = ⟨y, x + y⟩ := by
            dsimp [u']; rw [hu]; ext <;> simp [ω₀]
          have hxy_ge : 0 ≤ x + y := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hω_n : ω₀.norm = -1 := by decide
            rw [map_mul, hω_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_mul_inv (ih _ hlt u' rfl hu'_norm)
          have heq : ω_inv * u' = u := by
            dsimp [u']
            calc ω_inv * (ω₀ * u) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω_inv * u
          have hu'_eq : u' = ⟨-x + y, x⟩ := by
            dsimp [u']; rw [hu]; ext <;> simp [ω_inv]
          have hxley : x ≤ y := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hinv_n : ω_inv.norm = -1 := by decide
            rw [map_mul, hinv_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_mul_ω₀ (ih _ hlt u' rfl hu'_norm)
          have heq : ω₀ * u' = u := by
            dsimp [u']
            calc ω₀ * (ω_inv * u) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1

lemma unit_form (u : R) (hu : IsUnit u) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ u = ω₀ ^ r * η ^ 5 := by
  have hn : IsUnit u.norm := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
  exact unit_form_aux _ u rfl (Int.isUnit_iff.mp hn)

/- ## Section 2: Dirichlet's 1825 Lemma and Second-Case Infinite Descent -/

lemma mk_pow5 (c d : ℤ) :
    (⟨c, d⟩ : R) ^ 5 =
      ⟨c ^ 5 + 10 * c ^ 3 * d ^ 2 + 10 * c ^ 2 * d ^ 3 + 10 * c * d ^ 4 + 3 * d ^ 5,
       5 * d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4)⟩ := by
  ext <;> simp [pow_succ, pow_zero] <;> ring

lemma isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime n 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨1, -k, by ring⟩

lemma zmod2_im_zero : ∀ c d : ZMod 2,
    d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4) = 0 → d = 0 := by
  decide

theorem dirichlet_lemma {P Q w : ℤ} (hcop : IsCoprime P Q) (h5P : ¬ (5 : ℤ) ∣ P)
    (h5Q : (5 : ℤ) ∣ Q) (hpar : Odd (P + Q)) (hw : P ^ 2 - 5 * Q ^ 2 = w ^ 5) :
    ∃ a b : ℤ, P = a * (a ^ 4 + 50 * a ^ 2 * b ^ 2 + 125 * b ^ 4) ∧
      Q = 5 * b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) := by
  set ρ : R := ⟨P - Q, 2 * Q⟩
  set ρ' : R := star ρ
  have hprod : ρ * ρ' = (w : R) ^ 5 := by
    have hnorm : ρ.norm = P ^ 2 - 5 * Q ^ 2 := by
      simp only [QuadraticAlgebra.norm_def, ρ]
      ring
    calc ρ * ρ' = algebraMap ℤ R ρ.norm := (algebraMap_norm_eq_mul_star ρ).symm
      _ = algebraMap ℤ R (w ^ 5) := by rw [hnorm, hw]
      _ = (w : R) ^ 5 := by simp
  have hcop_ρ : IsCoprime ρ ρ' := by
    have hP5 : IsCoprime P 5 := isCoprime_five_of_not_dvd h5P
    have hA : IsCoprime (P ^ 2 - 5 * Q ^ 2) P := by
      have h1 : IsCoprime (5 * Q ^ 2) P := (hP5.symm.mul_left hcop.symm.pow_left)
      have h2 : IsCoprime (-(5 * Q ^ 2)) P := h1.neg_left
      have he : P ^ 2 - 5 * Q ^ 2 = -(5 * Q ^ 2) + P * P := by ring
      rw [he]
      exact h2.add_mul_left_left P
    have hB : IsCoprime (P ^ 2 - 5 * Q ^ 2) 2 := by
      apply isCoprime_two_of_odd
      obtain ⟨k, hk⟩ := hpar
      refine ⟨2 * k ^ 2 + 2 * k - 2 * k * Q - Q - 2 * Q ^ 2, ?_⟩
      have hP : P = 2 * k + 1 - Q := by omega
      rw [hP]; ring
    obtain ⟨A, B, hAB⟩ := hA.mul_right hB
    refine ⟨(A : R) * ρ' + B, B, ?_⟩
    have h1 : ((A * (P ^ 2 - 5 * Q ^ 2) + B * (P * 2) : ℤ) : R) = 1 := by
      rw [hAB]; simp
    have hsum : ρ + ρ' = ((P * 2 : ℤ) : R) := by
      ext
      · simp [ρ, ρ']; ring
      · simp [ρ, ρ']
    have hmul : ρ * ρ' = ((P ^ 2 - 5 * Q ^ 2 : ℤ) : R) := by
      rw [hprod, hw]; push_cast; rfl
    calc ((A : R) * ρ' + B) * ρ + (B : R) * ρ'
        = (A : R) * (ρ * ρ') + (B : R) * (ρ + ρ') := by ring
      _ = ((A * (P ^ 2 - 5 * Q ^ 2) + B * (P * 2) : ℤ) : R) := by
          rw [hmul, hsum]; push_cast; ring
      _ = 1 := h1
  obtain ⟨γ0, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop_ρ hprod
  obtain ⟨r, hr, η, -, hη⟩ := unit_form (u0 : R) u0.isUnit
  set γ : R := γ0 * η
  have hρ : ρ = ω₀ ^ r * γ ^ 5 := by
    calc ρ = γ0 ^ 5 * (u0 : R) := hu0.symm
      _ = γ0 ^ 5 * (ω₀ ^ r * η ^ 5) := by rw [hη]
      _ = ω₀ ^ r * γ ^ 5 := by dsimp [γ]; ring
  set c := γ.re
  set d := γ.im
  have hγ_mk : γ = ⟨c, d⟩ := (QuadraticAlgebra.mk_eta γ).symm
  set X5 := c ^ 5 + 10 * c ^ 3 * d ^ 2 + 10 * c ^ 2 * d ^ 3 + 10 * c * d ^ 4 + 3 * d ^ 5
  set Y5 := d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4)
  have hγ5 : γ ^ 5 = ⟨X5, 5 * Y5⟩ := by
    rw [hγ_mk, mk_pow5]
    dsimp [X5, Y5]
    ext
    · simp
    · simp; ring
  rw [hγ5] at hρ
  obtain ⟨Q', rfl⟩ := h5Q
  have h5_not_re : ¬ (5 : ℤ) ∣ (P - 5 * Q') := by
    intro hd
    exact h5P (by obtain ⟨m, hm⟩ := hd; exact ⟨m + Q', by omega⟩)
  rw [Finset.mem_range] at hr
  have hr0 : r = 0 := by
    interval_cases r
    · rfl
    · exfalso
      have hre : P - 5 * Q' = 5 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀] at this; linarith
      exact h5_not_re ⟨Y5, hre⟩
    · exfalso
      have hre : P - 5 * Q' = X5 + 5 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_two] at this; linarith
      have him : 10 * Q' = X5 + 10 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_two] at this; linarith
      exact h5_not_re ⟨2 * Q' - Y5, by omega⟩
    · exfalso
      have hre : P - 5 * Q' = X5 + 10 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have him : 10 * Q' = 2 * X5 + 15 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have h5X : (5 : ℤ) ∣ 2 * X5 := ⟨2 * Q' - 3 * Y5, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h5X with h2 | hX
      · norm_num at h2
      · obtain ⟨k, hk⟩ := hX
        exact h5_not_re ⟨k + 2 * Y5, by omega⟩
    · exfalso
      have hre : P - 5 * Q' = 2 * X5 + 15 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have him : 10 * Q' = 3 * X5 + 25 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have h5X : (5 : ℤ) ∣ 3 * X5 := ⟨2 * Q' - 5 * Y5, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h5X with h3 | hX
      · norm_num at h3
      · obtain ⟨k, hk⟩ := hX
        exact h5_not_re ⟨2 * k + 3 * Y5, by omega⟩
  subst hr0
  simp only [pow_zero, one_mul] at hρ
  have hre : P - 5 * Q' = X5 := congr_arg QuadraticAlgebra.re hρ
  have him : 2 * Q' = Y5 := by
    have := congr_arg QuadraticAlgebra.im hρ
    simp only [ρ] at this
    omega
  have hd_dvd : (2 : ℤ) ∣ d := by
    change ((2 : ℕ) : ℤ) ∣ d
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply zmod2_im_zero (c : ZMod 2) (d : ZMod 2)
    have hY2 : (Y5 : ZMod 2) = 0 := by
      rw [← him]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
    dsimp [Y5] at hY2
    push_cast at hY2
    exact hY2
  obtain ⟨b, hb⟩ := hd_dvd
  refine ⟨c + b, b, ?_, ?_⟩
  · have hX_eq : 2 * X5 + 5 * Y5 =
        2 * ((c + b) * ((c + b) ^ 4 + 50 * (c + b) ^ 2 * b ^ 2 + 125 * b ^ 4)) := by
      dsimp [X5, Y5]; rw [hb]; ring
    linarith [hre, him, hX_eq]
  · have hY_eq : Y5 = 2 * b * ((c + b) ^ 4 + 10 * (c + b) ^ 2 * b ^ 2 + 5 * b ^ 4) := by
      dsimp [Y5]; rw [hb]; ring
    linarith [him, hY_eq]

lemma pow5_of_coprime_int {a b c : ℤ} (h : IsCoprime a b) (habc : a * b = c ^ 5) :
    ∃ d : ℤ, a = d ^ 5 :=
  Int.eq_pow_of_mul_eq_pow_odd_left h (by decide) habc

lemma odd_add_of_odd_PQ5 {a b : ℤ}
    (h : Odd (a * (a ^ 4 + 50 * a ^ 2 * b ^ 2 + 125 * b ^ 4) +
      5 * b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4))) : Odd (a + b) := by
  rw [odd_iff_zmod2] at h ⊢
  push_cast at h ⊢
  revert h
  generalize (a : ZMod 2) = x, (b : ZMod 2) = y
  revert x y; decide

def Eq2 (a b Z : ℤ) (M N : ℕ) : Prop :=
  1 ≤ M ∧ 1 ≤ N ∧ IsCoprime a b ∧ Odd (a + b) ∧ ¬ (5 : ℤ) ∣ a ∧ b ≠ 0 ∧ IsCoprime Z 10 ∧
    b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) = 2 ^ M * 5 ^ N * Z ^ 5

theorem no_eq2_aux : ∀ n : ℕ, ∀ a b Z : ℤ, ∀ M N : ℕ, b.natAbs = n → Eq2 a b Z M N → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b Z M N hn ⟨hM, hN, hcop, hodd, h5a, hb0, hZ10, heq⟩
    set Q := a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4
    have hQ_odd : Odd Q := by
      rw [odd_iff_zmod2] at hodd ⊢
      dsimp [Q]
      push_cast at hodd ⊢
      revert hodd
      generalize (a : ZMod 2) = x, (b : ZMod 2) = y
      revert x y; decide
    have h5Q : ¬ (5 : ℤ) ∣ Q := by
      intro hd
      have h5a4 : (5 : ℤ) ∣ a ^ 4 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨k - 2 * a ^ 2 * b ^ 2 - b ^ 4, by dsimp [Q] at hk; linarith⟩
      exact h5a (Int.Prime.dvd_pow' Nat.prime_five h5a4)
    have hQ2 : IsCoprime Q 2 := isCoprime_two_of_odd hQ_odd
    have hQ5 : IsCoprime Q 5 := isCoprime_five_of_not_dvd h5Q
    have hQ_25 : IsCoprime Q (2 ^ M * 5 ^ N) := hQ2.pow_right.mul_right hQ5.pow_right
    have hdvd_b : (2 ^ M * 5 ^ N : ℤ) ∣ b := by
      refine hQ_25.symm.dvd_of_dvd_mul_right ?_
      exact ⟨Z ^ 5, heq⟩
    obtain ⟨b', hb'⟩ := hdvd_b
    have h25_ne : (2 ^ M * 5 ^ N : ℤ) ≠ 0 := by positivity
    have heq' : b' * Q = Z ^ 5 := by
      apply mul_left_cancel₀ h25_ne
      calc 2 ^ M * 5 ^ N * (b' * Q) = (2 ^ M * 5 ^ N * b') * Q := by ring
        _ = b * Q := by rw [← hb']
        _ = 2 ^ M * 5 ^ N * Z ^ 5 := heq
    have hbQ : IsCoprime b Q := by
      have hba4 : IsCoprime b (a ^ 4) := hcop.symm.pow_right
      have he : Q = a ^ 4 + b * (10 * a ^ 2 * b + 5 * b ^ 3) := by dsimp [Q]; ring
      rw [he]
      exact hba4.add_mul_left_right _
    have hb'Q : IsCoprime b' Q := by
      rw [hb'] at hbQ
      exact hbQ.of_mul_left_right
    obtain ⟨c, hc⟩ := pow5_of_coprime_int hb'Q heq'
    obtain ⟨d, hd⟩ := pow5_of_coprime_int hb'Q.symm (by rw [mul_comm]; exact heq')
    have hb_eq : b = 2 ^ M * 5 ^ N * c ^ 5 := by rw [hb', hc]
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hb0; rw [hb_eq]; ring
    have hc10 : IsCoprime (c ^ 2) 10 := by
      have hZ5_10 : IsCoprime (Z ^ 5) 10 := hZ10.pow_left
      rw [← heq', hc] at hZ5_10
      obtain ⟨u1, u2, hu12⟩ := hZ5_10.of_mul_left_left
      have hc_10 : IsCoprime c 10 := ⟨u1 * c ^ 4, u2, by linear_combination hu12⟩
      exact hc_10.pow_left
    have h5b : (5 : ℤ) ∣ b := by
      refine ⟨2 ^ M * 5 ^ (N - 1) * c ^ 5, ?_⟩
      rw [hb_eq]
      have hN' : 5 ^ N = (5 : ℤ) * 5 ^ (N - 1) := by
        conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ']
      rw [hN']; ring
    have h2b : Even b := by
      refine ⟨2 ^ (M - 1) * 5 ^ N * c ^ 5, ?_⟩
      rw [hb_eq]
      have hM' : 2 ^ M = (2 : ℤ) * 2 ^ (M - 1) := by
        conv_lhs => rw [show M = (M - 1) + 1 by omega, pow_succ']
      rw [hM']; ring
    set P1 := a ^ 2 + 5 * b ^ 2
    set R1 := 2 * b ^ 2
    have hPR_odd : Odd (P1 + R1) := by
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨m, hm⟩ := h2b
      refine ⟨2 * (k - m) ^ 2 + 2 * (k - m) + 14 * m ^ 2, ?_⟩
      have ha : a = 2 * (k - m) + 1 := by omega
      dsimp [P1, R1]; rw [ha, hm]; ring
    have h5P1 : ¬ (5 : ℤ) ∣ P1 := by
      intro hd
      have h5a2 : (5 : ℤ) ∣ a ^ 2 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨k - b ^ 2, by dsimp [P1] at hk; linarith⟩
      exact h5a (five_dvd_of_sq_dvd h5a2)
    have h5R1 : (5 : ℤ) ∣ R1 := by
      obtain ⟨k, hk⟩ := h5b
      exact ⟨10 * k ^ 2, by dsimp [R1]; rw [hk]; ring⟩
    have hcop_PR : IsCoprime P1 R1 := by
      have hP1_b : IsCoprime P1 b := by
        have he : P1 = a ^ 2 + b * (5 * b) := by dsimp [P1]; ring
        rw [he]
        exact hcop.pow_left.add_mul_left_left _
      have hP1_2 : IsCoprime P1 2 := by
        apply isCoprime_two_of_odd
        obtain ⟨k, hk⟩ := hPR_odd
        exact ⟨k - b ^ 2, by dsimp [R1] at hk; omega⟩
      exact hP1_2.mul_right hP1_b.pow_right
    have hd5 : P1 ^ 2 - 5 * R1 ^ 2 = d ^ 5 := by
      have he : P1 ^ 2 - 5 * R1 ^ 2 = Q := by dsimp [P1, R1, Q]; ring
      rw [he, hd]
    obtain ⟨a1, b1, ha1, hb1⟩ := dirichlet_lemma hcop_PR h5P1 h5R1 hPR_odd hd5
    have hcop1 : IsCoprime a1 b1 := by
      have h := hcop_PR
      rw [ha1, hb1] at h
      exact h.of_mul_left_left.of_mul_right_left.of_mul_right_right
    have hodd1 : Odd (a1 + b1) := by
      apply odd_add_of_odd_PQ5
      rw [← ha1, ← hb1]
      exact hPR_odd
    have h5a1 : ¬ (5 : ℤ) ∣ a1 := by
      intro hd
      exact h5P1 (ha1 ▸ dvd_mul_of_dvd_left hd _)
    have ha1_ne : a1 ≠ 0 := fun h0 => h5a1 (by simp [h0])
    set Q1 := a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4
    have hQ1_pos : 1 ≤ Q1 := by
      have : 0 < a1 ^ 2 := sq_pos_of_ne_zero ha1_ne
      have : 1 ≤ a1 ^ 4 := by nlinarith
      dsimp [Q1]
      nlinarith [sq_nonneg (a1 * b1), sq_nonneg (b1 ^ 2)]
    have hb1_pos : 0 < b1 := by
      have hR1_pos : 0 < R1 := by dsimp [R1]; positivity
      rw [hb1] at hR1_pos
      nlinarith
    have hb1_lt : b1.natAbs < n := by
      have hb1_2 : b1 ^ 2 ≤ b1 ^ 4 := by nlinarith [sq_nonneg (b1 - 1)]
      have h5b1_sq : 5 * b1 ^ 2 ≤ 2 * b ^ 2 := by
        have h1 : b1 ≤ Q1 := by dsimp [Q1]; nlinarith
        have h2 : 5 * b1 ^ 2 ≤ 5 * b1 * Q1 := by nlinarith
        linarith [hb1]
      have hbsq : b1 ^ 2 < b ^ 2 := by nlinarith
      have hlt_abs : |b1| < |b| := by
        rw [← sq_lt_sq]
        exact hbsq
      rw [← hn, ← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs]
      exact hlt_abs
    have heq1 : b1 * Q1 = 2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5 := by
      have h5pow : (5 : ℤ) ^ (2 * N) = 5 * 5 ^ (2 * N - 1) := by
        conv_lhs => rw [show 2 * N = (2 * N - 1) + 1 by omega, pow_succ']
      have hR : 5 * (b1 * Q1) = 5 * (2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5) := by
        calc 5 * (b1 * Q1) = R1 := by dsimp [Q1]; linarith [hb1]
          _ = 2 * (2 ^ M * 5 ^ N * c ^ 5) ^ 2 := by dsimp [R1]; rw [hb_eq]
          _ = 2 * 2 ^ (2 * M) * 5 ^ (2 * N) * (c ^ 2) ^ 5 := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
              ring_nf
          _ = 5 * (2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5) := by
              rw [h5pow, pow_succ]; ring
      linarith
    exact ih _ hb1_lt a1 b1 (c ^ 2) (2 * M + 1) (2 * N - 1) rfl
      ⟨by omega, by omega, hcop1, hodd1, h5a1, hb1_pos.ne', hc10, heq1⟩

theorem no_sol_case2 {x y Z : ℤ} {m n : ℕ} (hm : 1 ≤ m) (hn : 3 ≤ n)
    (hcop : IsCoprime x y) (hZ10 : IsCoprime Z 10) (hZ0 : Z ≠ 0) :
    x ^ 5 + y ^ 5 ≠ 2 ^ m * 5 ^ n * Z ^ 5 := by
  intro h
  have hxy_even : Even (x + y) := by
    have hm' : 2 ^ m = (2 : ℤ) * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    have h2 : Even (x ^ 5 + y ^ 5) := ⟨2 ^ (m - 1) * 5 ^ n * Z ^ 5, by rw [h, hm']; ring⟩
    rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at h2
    rwa [Int.even_add]
  obtain ⟨u, hu⟩ := hxy_even
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := by obtain ⟨r, hr⟩ := hx; exact ⟨u - r, by omega⟩
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
      have hd : (2 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hx.two_dvd hy.two_dvd
      rw [hg] at hd; norm_num at hd
    · exact hx
  set v := x - u
  have hx' : x = u + v := by omega
  have hy' : y = u - v := by omega
  have hpar : Odd (u + v) := hx' ▸ hxodd
  have huv : IsCoprime u v := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx', hy']; ring⟩
  have h5_xy : (5 : ℤ) ∣ (x + y) := by
    have hn' : 5 ^ n = (5 : ℤ) * 5 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
    have h5_pow : (5 : ℤ) ∣ (x + y) ^ 5 := by
      refine ⟨2 ^ m * 5 ^ (n - 1) * Z ^ 5 + x * y * (x + y) * (x ^ 2 + x * y + y ^ 2), ?_⟩
      calc (x + y) ^ 5 = (x ^ 5 + y ^ 5) + 5 * (x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by ring
        _ = 2 ^ m * 5 ^ n * Z ^ 5 + 5 * (x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by rw [h]
        _ = 5 * (2 ^ m * 5 ^ (n - 1) * Z ^ 5 + x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by
            rw [hn']; ring
    exact Int.Prime.dvd_pow' Nat.prime_five h5_pow
  have h5u : (5 : ℤ) ∣ u := by
    have h2u : (5 : ℤ) ∣ 2 * u := by rwa [show 2 * u = x + y by omega]
    rcases Int.Prime.dvd_mul' Nat.prime_five h2u with h2 | h5
    · norm_num at h2
    · exact h5
  obtain ⟨U, rfl⟩ := h5u
  have h5v : ¬ (5 : ℤ) ∣ v := by
    intro hd
    exact not_isUnit_five (huv.isUnit_of_dvd' (dvd_mul_right 5 U) hd)
  have hUv : IsCoprime U v := huv.of_mul_left_right
  have hU_odd : Odd (U + v) := by
    obtain ⟨k, hk⟩ := hpar
    exact ⟨k - 2 * U, by omega⟩
  set Q' := v ^ 4 + 50 * U ^ 2 * v ^ 2 + 125 * U ^ 4
  have heqU : U * Q' = 2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5 := by
    have hm' : 2 ^ m = (2 : ℤ) * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    have hn' : (5 : ℤ) ^ n = 25 * 5 ^ (n - 2) := by
      calc (5 : ℤ) ^ n = 5 ^ ((n - 2) + 2) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 25 * 5 ^ (n - 2) := by rw [pow_add]; ring
    have h50 : 50 * (U * Q') = 50 * (2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5) := by
      calc 50 * (U * Q') = (5 * U + v) ^ 5 + (5 * U - v) ^ 5 := by dsimp [Q']; ring
        _ = x ^ 5 + y ^ 5 := by rw [← hx', ← hy']
        _ = 2 ^ m * 5 ^ n * Z ^ 5 := h
        _ = 50 * (2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5) := by rw [hm', hn']; ring
    linarith
  have hQ'_odd : Odd Q' := by
    rw [odd_iff_zmod2] at hU_odd ⊢
    dsimp [Q']
    push_cast at hU_odd ⊢
    revert hU_odd
    generalize (U : ZMod 2) = x1, (v : ZMod 2) = y1
    revert x1 y1; decide
  have h5Q' : ¬ (5 : ℤ) ∣ Q' := by
    intro hd
    have h5v4 : (5 : ℤ) ∣ v ^ 4 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 10 * U ^ 2 * v ^ 2 - 25 * U ^ 4, by dsimp [Q'] at hk; linarith⟩
    exact h5v (Int.Prime.dvd_pow' Nat.prime_five h5v4)
  have hQ'2 : IsCoprime Q' 2 := isCoprime_two_of_odd hQ'_odd
  have hQ'5 : IsCoprime Q' 5 := isCoprime_five_of_not_dvd h5Q'
  have hQ'_25 : IsCoprime Q' (2 ^ (m - 1) * 5 ^ (n - 2)) := hQ'2.pow_right.mul_right hQ'5.pow_right
  have hdvd_U : (2 ^ (m - 1) * 5 ^ (n - 2) : ℤ) ∣ U := by
    refine hQ'_25.symm.dvd_of_dvd_mul_right ?_
    exact ⟨Z ^ 5, heqU⟩
  obtain ⟨U', hU'⟩ := hdvd_U
  have h25_ne : (2 ^ (m - 1) * 5 ^ (n - 2) : ℤ) ≠ 0 := by positivity
  have heqU' : U' * Q' = Z ^ 5 := by
    apply mul_left_cancel₀ h25_ne
    calc 2 ^ (m - 1) * 5 ^ (n - 2) * (U' * Q') = U * Q' := by rw [hU']; ring
      _ = 2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5 := heqU
  have hUQ' : IsCoprime U Q' := by
    have he : Q' = v ^ 4 + U * (50 * U * v ^ 2 + 125 * U ^ 3) := by dsimp [Q']; ring
    rw [he]
    exact hUv.pow_right.add_mul_left_right _
  have hU'Q' : IsCoprime U' Q' := by
    rw [hU'] at hUQ'
    exact hUQ'.of_mul_left_right
  obtain ⟨t, ht⟩ := pow5_of_coprime_int hU'Q' heqU'
  obtain ⟨w, hw⟩ := pow5_of_coprime_int hU'Q'.symm (by rw [mul_comm]; exact heqU')
  have hU_eq : U = 2 ^ (m - 1) * 5 ^ (n - 2) * t ^ 5 := by rw [hU', ht]
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hZ0
    rw [ht, zero_pow (by norm_num), zero_mul] at heqU'
    exact pow_eq_zero_iff (by norm_num) |>.mp heqU'.symm
  have ht10 : IsCoprime (t ^ 2) 10 := by
    have hZ5_10 : IsCoprime (Z ^ 5) 10 := hZ10.pow_left
    rw [← heqU', ht] at hZ5_10
    obtain ⟨u1, u2, hu12⟩ := hZ5_10.of_mul_left_left
    have ht_10 : IsCoprime t 10 := ⟨u1 * t ^ 4, u2, by linear_combination hu12⟩
    exact ht_10.pow_left
  set P2 := v ^ 2 + 25 * U ^ 2
  set R2 := 10 * U ^ 2
  have hPR2_odd : Odd (P2 + R2) := by
    obtain ⟨k, hk⟩ := hU_odd
    rcases Int.even_or_odd U with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hv' : v = 2 * (k - j) + 1 := by omega
      exact ⟨2 * (k - j) ^ 2 + 2 * (k - j) + 70 * j ^ 2, by dsimp [P2, R2]; rw [hj, hv']; ring⟩
    · have hv' : v = 2 * (k - j) := by omega
      exact ⟨2 * (k - j) ^ 2 + 70 * j ^ 2 + 70 * j + 17, by dsimp [P2, R2]; rw [hj, hv']; ring⟩
  have h5P2 : ¬ (5 : ℤ) ∣ P2 := by
    intro hd
    have h5v2 : (5 : ℤ) ∣ v ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 5 * U ^ 2, by dsimp [P2] at hk; linarith⟩
    exact h5v (five_dvd_of_sq_dvd h5v2)
  have h5R2 : (5 : ℤ) ∣ R2 := ⟨2 * U ^ 2, by dsimp [R2]; ring⟩
  have hcop_PR2 : IsCoprime P2 R2 := by
    have hP2_U : IsCoprime P2 U := by
      have he : P2 = v ^ 2 + U * (25 * U) := by dsimp [P2]; ring
      rw [he]
      exact hUv.symm.pow_left.add_mul_left_left _
    have hP2_2 : IsCoprime P2 2 := by
      apply isCoprime_two_of_odd
      obtain ⟨k, hk⟩ := hPR2_odd
      exact ⟨k - 5 * U ^ 2, by dsimp [R2] at hk; omega⟩
    have hP2_5 : IsCoprime P2 5 := isCoprime_five_of_not_dvd h5P2
    have h10 : R2 = (2 * 5) * U ^ 2 := by ring
    rw [h10]
    exact (hP2_2.mul_right hP2_5).mul_right hP2_U.pow_right
  have hw5 : P2 ^ 2 - 5 * R2 ^ 2 = w ^ 5 := by
    have he : P2 ^ 2 - 5 * R2 ^ 2 = Q' := by dsimp [P2, R2, Q']; ring
    rw [he, hw]
  obtain ⟨a1, b1, ha1, hb1⟩ := dirichlet_lemma hcop_PR2 h5P2 h5R2 hPR2_odd hw5
  have hcop1 : IsCoprime a1 b1 := by
    have hc := hcop_PR2
    rw [ha1, hb1] at hc
    exact hc.of_mul_left_left.of_mul_right_left.of_mul_right_right
  have hodd1 : Odd (a1 + b1) := by
    apply odd_add_of_odd_PQ5
    rw [← ha1, ← hb1]
    exact hPR2_odd
  have h5a1 : ¬ (5 : ℤ) ∣ a1 := fun hd => h5P2 (ha1 ▸ dvd_mul_of_dvd_left hd _)
  have hU0 : U ≠ 0 := by
    rw [hU_eq]
    exact mul_ne_zero (by positivity) (pow_ne_zero 5 ht0)
  have hb1_ne : b1 ≠ 0 := by
    rintro rfl
    have hR0 : R2 = 0 := by rw [hb1]; ring
    dsimp [R2] at hR0
    exact hU0 (by nlinarith)
  have heq1 : b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4) =
      2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5 := by
    have h2pow : 2 * (2 : ℤ) ^ (2 * (m - 1)) = 2 ^ (2 * m - 1) := by
      conv_rhs => rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, pow_succ']
    have h5R : 5 * (b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4)) =
        5 * (2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by
      calc 5 * (b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4)) = R2 := by linarith [hb1]
        _ = 10 * (2 ^ (m - 1) * 5 ^ (n - 2) * t ^ 5) ^ 2 := by dsimp [R2]; rw [hU_eq]
        _ = 5 * ((2 * 2 ^ (2 * (m - 1))) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by
            rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
            ring_nf
        _ = 5 * (2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by rw [h2pow]
    linarith
  exact no_eq2_aux _ a1 b1 (t ^ 2) (2 * m - 1) (2 * (n - 2)) rfl
    ⟨by omega, by omega, hcop1, hodd1, h5a1, hb1_ne, ht10, heq1⟩

/- ## Section 3: First-Case Elimination (`5 ∤ b`) in `𝓞 (CyclotomicField 5 ℚ)` -/

abbrev K5 := CyclotomicField 5 ℚ

instance : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
instance : IsCyclotomicExtension {5} ℚ K5 := CyclotomicField.isCyclotomicExtension 5 ℚ
instance : IsPrincipalIdealRing (𝓞 K5) := IsCyclotomicExtension.Rat.five_pid K5

lemma hζ5 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 5 ℚ K5) 5 :=
  IsCyclotomicExtension.zeta_spec 5 ℚ K5

noncomputable abbrev ζ : 𝓞 K5 := hζ5.toInteger

lemma ζ_pow5 : ζ ^ 5 = 1 := hζ5.toInteger_isPrimitiveRoot.pow_eq_one

lemma ζ_ne_one : ζ ≠ 1 := hζ5.toInteger_isPrimitiveRoot.ne_one (by decide)

lemma ζ_cyc : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr ζ_ne_one)
  calc (ζ - 1) * (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) = ζ ^ 5 - 1 := by ring
    _ = 0 := by rw [ζ_pow5, sub_self]
    _ = (ζ - 1) * 0 := by rw [mul_zero]

lemma ζ4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by linear_combination ζ_cyc
lemma ζ5 : ζ ^ 5 = 1 := ζ_pow5
lemma ζ6 : ζ ^ 6 = ζ := by
  calc ζ ^ 6 = ζ ^ 5 * ζ := by ring
    _ = ζ := by rw [ζ_pow5, one_mul]
lemma ζ7 : ζ ^ 7 = ζ ^ 2 := by
  calc ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
    _ = ζ ^ 2 := by rw [ζ_pow5, one_mul]
lemma ζ8 : ζ ^ 8 = ζ ^ 3 := by
  calc ζ ^ 8 = ζ ^ 5 * ζ ^ 3 := by ring
    _ = ζ ^ 3 := by rw [ζ_pow5, one_mul]
lemma ζ9 : ζ ^ 9 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
  calc ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := by ring
    _ = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by rw [ζ_pow5, one_mul, ζ4]
lemma ζ10 : ζ ^ 10 = 1 := by
  calc ζ ^ 10 = (ζ ^ 5) ^ 2 := by ring
    _ = 1 := by rw [ζ_pow5]; ring

lemma exists_coord5 (x : 𝓞 K5) :
    ∃ b0 b1 b2 b3 : ℤ, x = b0 + b1 * ζ + b2 * ζ ^ 2 + b3 * ζ ^ 3 := by
  obtain ⟨f, rfl⟩ := hζ5.integralPowerBasis.exists_eq_aeval' x
  rw [IsPrimitiveRoot.integralPowerBasis_gen]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a0, a1, a2, a3, ha⟩ := hp
    obtain ⟨c0, c1, c2, c3, hc⟩ := hq
    refine ⟨a0 + c0, a1 + c1, a2 + c2, a3 + c3, ?_⟩
    rw [map_add, ha, hc]; push_cast; ring
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    induction n with
    | zero => exact ⟨c, 0, 0, 0, by simp⟩
    | succ n ih =>
      obtain ⟨b0, b1, b2, b3, hb⟩ := ih
      refine ⟨-b3, b0 - b3, b1 - b3, b2 - b3, ?_⟩
      rw [pow_succ, ← mul_assoc, hb]
      push_cast
      linear_combination (b3 : 𝓞 K5) * ζ_cyc

lemma coord5_zero {b0 b1 b2 b3 : ℤ}
    (h : (b0 : 𝓞 K5) + b1 * ζ + b2 * ζ ^ 2 + b3 * ζ ^ 3 = 0) :
    b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  have hdim : hζ5.integralPowerBasis.dim = 4 := by
    rw [IsPrimitiveRoot.integralPowerBasis_dim]
    rfl
  let c : Fin 4 → ℤ := ![b0, b1, b2, b3]
  have hsum : ∑ i : Fin hζ5.integralPowerBasis.dim,
      c (finCongr hdim i) • hζ5.integralPowerBasis.basis i = 0 := by
    rw [← (finCongr hdim).symm.sum_comp]
    simp only [Equiv.apply_symm_apply, Fin.sum_univ_four, PowerBasis.basis_eq_pow,
      IsPrimitiveRoot.integralPowerBasis_gen]
    simpa [c, zsmul_eq_mul, pow_two] using h
  have hli := Fintype.linearIndependent_iff.mp hζ5.integralPowerBasis.basis.linearIndependent
    (fun i => c (finCongr hdim i)) hsum
  have hc : ∀ j : Fin 4, c j = 0 := fun j => by
    simpa using hli ((finCongr hdim).symm j)
  exact ⟨hc 0, hc 1, hc 2, hc 3⟩

lemma coord5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : ℤ}
    (h : (a0 : 𝓞 K5) + a1 * ζ + a2 * ζ ^ 2 + a3 * ζ ^ 3 =
         (b0 : 𝓞 K5) + b1 * ζ + b2 * ζ ^ 2 + b3 * ζ ^ 3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have hz := coord5_zero (b0 := a0 - b0) (b1 := a1 - b1) (b2 := a2 - b2) (b3 := a3 - b3)
    (by push_cast; linear_combination h)
  omega

noncomputable def conj5 : 𝓞 K5 ≃+* 𝓞 K5 :=
  RingOfIntegers.mapRingEquiv
    (IsCyclotomicExtension.fromZetaAut (hζ5.pow_of_coprime 4 (by decide))
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))).toRingEquiv

lemma conj5_ζ : conj5 ζ = ζ ^ 4 := by
  apply Subtype.ext
  change (IsCyclotomicExtension.fromZetaAut (hζ5.pow_of_coprime 4 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num)))
      (IsCyclotomicExtension.zeta 5 ℚ K5) = _
  rw [IsCyclotomicExtension.fromZetaAut_spec]
  rfl

lemma conj5_involution (x : 𝓞 K5) : conj5 (conj5 x) = x := by
  obtain ⟨b0, b1, b2, b3, rfl⟩ := exists_coord5 x
  have hζ4 : conj5 (ζ ^ 4) = ζ := by
    rw [map_pow, conj5_ζ, ← pow_mul]
    calc ζ ^ 16 = (ζ ^ 5) ^ 3 * ζ := by ring
      _ = ζ := by rw [ζ_pow5]; ring
  simp only [map_add, map_mul, map_pow, map_intCast, conj5_ζ, hζ4]

lemma sos4_bound {x y z w : ℤ}
    (h : (x - y) ^ 2 + (y - z) ^ 2 + (z - w) ^ 2 + (x - z) ^ 2 +
         (y - w) ^ 2 + (x - w) ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 4) :
    -1 ≤ x ∧ x ≤ 1 := by
  have hx2 : 5 * x ^ 2 ≤ 8 := by
    have hid : 5 * x ^ 2 + (x - 2 * y) ^ 2 + (x - 2 * z) ^ 2 + (x - 2 * w) ^ 2 +
        2 * (y - z) ^ 2 + 2 * (z - w) ^ 2 + 2 * (y - w) ^ 2 = 8 := by
      linear_combination 2 * h
    linarith [sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (x - 2 * w),
      sq_nonneg (y - z), sq_nonneg (z - w), sq_nonneg (y - w)]
  have hx1 : x ^ 2 ≤ 1 := by omega
  exact ⟨by by_contra! hc; nlinarith, by by_contra! hc; nlinarith⟩

lemma kronecker_unit5 {η : 𝓞 K5} (h : η * conj5 η = 1) :
    ∃ s : 𝓞 K5, (s = 1 ∨ s = -1) ∧ ∃ k ∈ Finset.range 5, η = s * ζ ^ k := by
  obtain ⟨b0, b1, b2, b3, hη_b⟩ := exists_coord5 η
  have ⟨a1, a2, a3, a4, hη⟩ : ∃ a1 a2 a3 a4 : ℤ,
      η = (a1 : 𝓞 K5) * ζ + a2 * ζ ^ 2 + a3 * ζ ^ 3 + a4 * ζ ^ 4 :=
    ⟨b1 - b0, b2 - b0, b3 - b0, -b0, by
      rw [hη_b]; push_cast; linear_combination (b0 : 𝓞 K5) * ζ_cyc⟩
  clear hη_b b0 b1 b2 b3
  have hconj : conj5 η = (a1 : 𝓞 K5) * ζ ^ 4 + a2 * ζ ^ 3 + a3 * ζ ^ 2 + a4 * ζ := by
    rw [hη]
    simp only [map_add, map_mul, map_pow, map_intCast, conj5_ζ]
    have h8 : (ζ ^ 4) ^ 2 = ζ ^ 3 := by
      calc (ζ ^ 4) ^ 2 = ζ ^ 5 * ζ ^ 3 := by ring
        _ = ζ ^ 3 := by rw [ζ_pow5, one_mul]
    have h12 : (ζ ^ 4) ^ 3 = ζ ^ 2 := by
      calc (ζ ^ 4) ^ 3 = (ζ ^ 5) ^ 2 * ζ ^ 2 := by ring
        _ = ζ ^ 2 := by rw [ζ_pow5]; ring
    have h16 : (ζ ^ 4) ^ 4 = ζ := by
      calc (ζ ^ 4) ^ 4 = (ζ ^ 5) ^ 3 * ζ := by ring
        _ = ζ := by rw [ζ_pow5]; ring
    rw [h8, h12, h16]
  set C0 := a1 ^ 2 - a1 * a2 + a2 ^ 2 - a2 * a3 + a3 ^ 2 - a3 * a4 + a4 ^ 2
  set C2 := -a1 * a2 + a1 * a3 + a1 * a4 - a2 * a3 + a2 * a4 - a3 * a4
  have hprod : η * conj5 η = (C0 : 𝓞 K5) + 0 * ζ + C2 * ζ ^ 2 + C2 * ζ ^ 3 := by
    rw [hconj, hη]
    dsimp [C0, C2]
    push_cast
    ring_nf
    simp only [ζ8, ζ7, ζ6, ζ5, ζ4]
    ring
  have heq : (C0 : 𝓞 K5) + (0 : ℤ) * ζ + C2 * ζ ^ 2 + C2 * ζ ^ 3 =
      (1 : ℤ) + (0 : ℤ) * ζ + (0 : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 := by
    simpa [hprod] using h
  obtain ⟨hC0, -, hC2, -⟩ := coord5_eq heq
  have hsos : (a1 - a2) ^ 2 + (a2 - a3) ^ 2 + (a3 - a4) ^ 2 + (a1 - a3) ^ 2 +
      (a2 - a4) ^ 2 + (a1 - a4) ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 = 4 := by
    dsimp [C0, C2] at hC0 hC2
    linarith
  obtain ⟨ha1_lo, ha1_hi⟩ := sos4_bound hsos
  obtain ⟨ha2_lo, ha2_hi⟩ := sos4_bound (x := a2) (y := a1) (z := a3) (w := a4) (by linarith)
  obtain ⟨ha3_lo, ha3_hi⟩ := sos4_bound (x := a3) (y := a1) (z := a2) (w := a4) (by linarith)
  obtain ⟨ha4_lo, ha4_hi⟩ := sos4_bound (x := a4) (y := a1) (z := a2) (w := a3) (by linarith)
  clear C0 C2 hC0 hC2 hprod heq hconj h
  interval_cases a1 <;> interval_cases a2 <;> interval_cases a3 <;> interval_cases a4
  all_goals try { exfalso; norm_num at hsos }
  · exact ⟨1, Or.inl rfl, 0, by simp, by rw [hη]; push_cast; linear_combination -ζ_cyc⟩
  · exact ⟨-1, Or.inr rfl, 1, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 2, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 3, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 4, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 4, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 3, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 2, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 1, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 0, by simp, by rw [hη]; push_cast; linear_combination ζ_cyc⟩

lemma five_eq_prod_zeta :
    (1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4) = (5 : 𝓞 K5) := by
  ring_nf
  simp only [ζ10, ζ9, ζ8, ζ5]
  ring

lemma pow5_sub_pow5_fac (x y : 𝓞 K5) :
    x ^ 5 - y ^ 5 =
      (x - y) * (x - ζ * y) * (x - ζ ^ 2 * y) * (x - ζ ^ 3 * y) * (x - ζ ^ 4 * y) := by
  ring_nf
  simp only [ζ10, ζ9, ζ8, ζ7, ζ6, ζ5, ζ4]
  ring

lemma pow5_cong_int (α : 𝓞 K5) : ∃ C : ℤ, ∃ q : 𝓞 K5, α ^ 5 = C + 5 * q := by
  obtain ⟨b0, b1, b2, b3, rfl⟩ := exists_coord5 α
  have hadd : ∀ A B : 𝓞 K5, ∃ r : 𝓞 K5, (A + B) ^ 5 = A ^ 5 + B ^ 5 + 5 * r := fun A B =>
    ⟨A * B * (A + B) * (A ^ 2 + A * B + B ^ 2), by ring⟩
  obtain ⟨r1, hr1⟩ := hadd ((b0 : 𝓞 K5) + b1 * ζ + b2 * ζ ^ 2) (b3 * ζ ^ 3)
  obtain ⟨r2, hr2⟩ := hadd ((b0 : 𝓞 K5) + b1 * ζ) (b2 * ζ ^ 2)
  obtain ⟨r3, hr3⟩ := hadd (b0 : 𝓞 K5) (b1 * ζ)
  refine ⟨b0 ^ 5 + b1 ^ 5 + b2 ^ 5 + b3 ^ 5, r1 + r2 + r3, ?_⟩
  rw [hr1, hr2, hr3, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    show 2 * 5 = 5 * 2 by rfl, show 3 * 5 = 5 * 3 by rfl, pow_mul, pow_mul, ζ_pow5]
  push_cast
  ring

lemma zmod25_no_sol_H2 : ∀ g b s : ZMod 25,
    (ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) b) ≠ 0 →
    (ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) g = 0 ∨
     ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) s = 0 ∨
     ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) (s + g) = 0) →
    g ^ 5 + 8 * b ^ 5 ≠ s ^ 5 := by
  decide

lemma isCoprime_factor_five {S G : ℤ} (hSG : IsCoprime S G)
    (h5 : IsCoprime ((S : 𝓞 K5) - ζ * G) (5 : 𝓞 K5))
    {u : 𝓞 K5} (hu : (1 - u) ∣ (5 : 𝓞 K5)) :
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ * u * G) := by
  obtain ⟨a, c, hac⟩ := hSG
  obtain ⟨d, hd⟩ := hu
  obtain ⟨x, y, hxy⟩ := h5
  refine ⟨x - y * d * ζ ^ 4 * (c + a * ζ * u), y * d * ζ ^ 4 * (c + a * ζ), ?_⟩
  have hlin : (c + a * ζ) * ((S : 𝓞 K5) - ζ * u * G) - (c + a * ζ * u) * ((S : 𝓞 K5) - ζ * G) =
      ζ * (1 - u) * ((a * S + c * G : ℤ) : 𝓞 K5) := by push_cast; ring
  rw [hac] at hlin
  have h5_eq : ((5 : 𝓞 K5)) = ζ ^ 4 * d * (ζ * (1 - u)) := by
    calc (5 : 𝓞 K5) = (1 - u) * d := hd
      _ = ζ ^ 5 * (1 - u) * d := by rw [ζ_pow5, one_mul]
      _ = ζ ^ 4 * d * (ζ * (1 - u)) := by ring
  calc (x - y * d * ζ ^ 4 * (c + a * ζ * u)) * ((S : 𝓞 K5) - ζ * G) +
        (y * d * ζ ^ 4 * (c + a * ζ)) * ((S : 𝓞 K5) - ζ * u * G)
      = x * ((S : 𝓞 K5) - ζ * G) +
        y * (ζ ^ 4 * d * ((c + a * ζ) * ((S : 𝓞 K5) - ζ * u * G) -
          (c + a * ζ * u) * ((S : 𝓞 K5) - ζ * G))) := by ring
    _ = x * ((S : 𝓞 K5) - ζ * G) + y * (5 : 𝓞 K5) := by
        rw [hlin]; simp [← h5_eq]
    _ = 1 := hxy

lemma isCoprime_conj_factors {S G : ℤ} (hSG : IsCoprime S G)
    (h5_cop : IsCoprime ((S : 𝓞 K5) - ζ * G) (5 : 𝓞 K5)) :
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - G) ∧
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ ^ 2 * G) ∧
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ ^ 3 * G) ∧
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ ^ 4 * G) := by
  have hd4 : (1 - ζ ^ 4) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3), by rw [← five_eq_prod_zeta]; ring⟩
  have hd1 : (1 - ζ) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4), by rw [← five_eq_prod_zeta]; ring⟩
  have hd2 : (1 - ζ ^ 2) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ) * (1 - ζ ^ 3) * (1 - ζ ^ 4), by rw [← five_eq_prod_zeta]; ring⟩
  have hd3 : (1 - ζ ^ 3) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 4), by rw [← five_eq_prod_zeta]; ring⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := isCoprime_factor_five hSG h5_cop hd4
    have he : (S : 𝓞 K5) - ζ * ζ ^ 4 * G = (S : 𝓞 K5) - G := by
      calc (S : 𝓞 K5) - ζ * ζ ^ 4 * G = (S : 𝓞 K5) - ζ ^ 5 * G := by ring
        _ = (S : 𝓞 K5) - G := by rw [ζ_pow5, one_mul]
    rwa [he] at h
  · have h := isCoprime_factor_five hSG h5_cop hd1
    have he : (S : 𝓞 K5) - ζ * ζ * G = (S : 𝓞 K5) - ζ ^ 2 * G := by ring
    rwa [he] at h
  · have h := isCoprime_factor_five hSG h5_cop hd2
    have he : (S : 𝓞 K5) - ζ * ζ ^ 2 * G = (S : 𝓞 K5) - ζ ^ 3 * G := by ring
    rwa [he] at h
  · have h := isCoprime_factor_five hSG h5_cop hd3
    have he : (S : 𝓞 K5) - ζ * ζ ^ 3 * G = (S : 𝓞 K5) - ζ ^ 4 * G := by ring
    rwa [he] at h

lemma unit_conj_cases {S G : ℤ} {s : 𝓞 K5} (hs : s = 1 ∨ s = -1)
    {k : ℕ} (hk : k ∈ Finset.range 5) {w : 𝓞 K5}
    (hdiff5 : ((S : 𝓞 K5) - ζ * G) - s * ζ ^ k * ((S : 𝓞 K5) - ζ ^ 4 * G) = 5 * w) :
    (5 : ℤ) ∣ G ∨ (5 : ℤ) ∣ S ∨ (5 : ℤ) ∣ (S + G) ∨ (5 : ℤ) ∣ (S - G) := by
  obtain ⟨r0, r1, r2, r3, hr⟩ := exists_coord5 w
  rw [hr] at hdiff5
  have hd' : ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 =
      ((S : 𝓞 K5) - ζ * G) - s * ζ ^ k * ((S : 𝓞 K5) - ζ ^ 4 * G) := by
    rw [hdiff5]; push_cast; ring
  clear hdiff5 hr w
  rw [Finset.mem_range] at hk
  rcases hs with rfl | rfl <;> interval_cases k
  · have hc : ((-G : ℤ) : 𝓞 K5) + (-2 * G : ℤ) * ζ + (-G : ℤ) * ζ ^ 2 + (-G : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ4]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inl ⟨-r0, by omega⟩
  · have hc : ((S + G : ℤ) : 𝓞 K5) + (-(S + G) : ℤ) * ζ + (0 : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ5]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inr (Or.inl ⟨r0, h0⟩))
  · have hc : (S : 𝓞 K5) + (0 : ℤ) * ζ + (-S : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ6]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : (S : 𝓞 K5) + (-G : ℤ) * ζ + (G : ℤ) * ζ ^ 2 + (-S : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ7]
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : ((2 * S : ℤ) : 𝓞 K5) + ((S - G : ℤ)) * ζ + (S : ℤ) * ζ ^ 2 + ((S + G : ℤ)) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ8, ζ4]; ring
    obtain ⟨-, -, h2, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r2, h2⟩)
  · have hc : ((2 * S + G : ℤ) : 𝓞 K5) + (0 : ℤ) * ζ + (G : ℤ) * ζ ^ 2 + (G : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ4]; ring
    obtain ⟨-, -, h2, -⟩ := coord5_eq hc
    exact Or.inl ⟨r2, h2⟩
  · have hc : ((S - G : ℤ) : 𝓞 K5) + ((S - G : ℤ)) * ζ + (0 : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ5]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inr (Or.inr ⟨r0, h0⟩))
  · have hc : (S : 𝓞 K5) + ((-2 * G : ℤ)) * ζ + (S : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ6]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : (S : 𝓞 K5) + (-G : ℤ) * ζ + (-G : ℤ) * ζ ^ 2 + (S : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ7]
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : ((0 : ℤ) : 𝓞 K5) + ((-S - G : ℤ)) * ζ + (-S : ℤ) * ζ ^ 2 + ((-S - G : ℤ)) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ8, ζ4]; ring
    obtain ⟨-, -, h2, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨-r2, by omega⟩)

theorem no_sol_case1_H2 {G B S : ℤ} (hSG : IsCoprime S G) (h5B : ¬ (5 : ℤ) ∣ B)
    (heq : G ^ 5 + 8 * B ^ 5 = S ^ 5) : False := by
  have hS_odd : Odd S := by
    rcases Int.even_or_odd S with hSe | hSo
    · exfalso
      have hGe : Even G := by
        have hG5 : Even (G ^ 5) := by
          obtain ⟨k, hk⟩ := hSe
          exact ⟨16 * k ^ 5 - 4 * B ^ 5, by rw [show G ^ 5 = S ^ 5 - 8 * B ^ 5 by linarith, hk]; ring⟩
        exact (Int.even_pow' (by norm_num)).mp hG5
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hSG
      have hd : (2 : ℤ) ∣ (Int.gcd S G : ℤ) := Int.dvd_coe_gcd hSe.two_dvd hGe.two_dvd
      rw [hg] at hd; norm_num at hd
    · exact hSo
  have hG_odd : Odd G := by
    rcases Int.even_or_odd G with hGe | hGo
    · exfalso
      have hSe : Even S := by
        have hS5 : Even (S ^ 5) := by
          obtain ⟨k, hk⟩ := hGe
          exact ⟨16 * k ^ 5 + 4 * B ^ 5, by rw [← heq, hk]; ring⟩
        exact (Int.even_pow' (by norm_num)).mp hS5
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hSG
      have hd : (2 : ℤ) ∣ (Int.gcd S G : ℤ) := Int.dvd_coe_gcd hSe.two_dvd hGe.two_dvd
      rw [hg] at hd; norm_num at hd
    · exact hGo
  set Q4 := S ^ 4 + S ^ 3 * G + S ^ 2 * G ^ 2 + S * G ^ 3 + G ^ 4
  have hQ4_odd : Odd Q4 := by
    have h1 : Even (S ^ 4 + S ^ 3 * G) := hS_odd.pow.add_odd (hS_odd.pow.mul hG_odd)
    have h2 : Even (S ^ 2 * G ^ 2 + S * G ^ 3) :=
      (hS_odd.pow.mul hG_odd.pow).add_odd (hS_odd.mul hG_odd.pow)
    have he : Q4 = (S ^ 4 + S ^ 3 * G) + (S ^ 2 * G ^ 2 + S * G ^ 3) + G ^ 4 := by
      dsimp [Q4]; ring
    rw [he]
    exact (h1.add h2).add_odd hG_odd.pow
  have h8_dvd : (8 : ℤ) ∣ (S - G) := by
    have hQ4_8 : IsCoprime Q4 8 := by
      have h2 := isCoprime_two_of_odd hQ4_odd
      simpa using h2.pow_right (n := 3)
    refine hQ4_8.symm.dvd_of_dvd_mul_right ?_
    exact ⟨B ^ 5, by dsimp [Q4]; linear_combination -heq⟩
  obtain ⟨M, hM⟩ := h8_dvd
  have hfac : ((S : 𝓞 K5) - ζ * G) *
      ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)) =
      (B : 𝓞 K5) ^ 5 := by
    apply mul_left_cancel₀ (show (8 : 𝓞 K5) ≠ 0 by norm_num)
    have hSG8 : (S : 𝓞 K5) - G = 8 * M := by exact_mod_cast hM
    have hB8 : (S : 𝓞 K5) ^ 5 - (G : 𝓞 K5) ^ 5 = 8 * (B : 𝓞 K5) ^ 5 := by
      have : S ^ 5 - G ^ 5 = 8 * B ^ 5 := by linarith
      exact_mod_cast this
    calc (8 : 𝓞 K5) * (((S : 𝓞 K5) - ζ * G) *
          ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)))
        = ((8 * M : 𝓞 K5)) * (S - ζ * G) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G) := by
          ring
      _ = ((S : 𝓞 K5) - G) * (S - ζ * G) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G) := by
          rw [← hSG8]
      _ = (S : 𝓞 K5) ^ 5 - (G : 𝓞 K5) ^ 5 := (pow5_sub_pow5_fac _ _).symm
      _ = 8 * (B : 𝓞 K5) ^ 5 := hB8
  have h5_cop : IsCoprime ((S : 𝓞 K5) - ζ * G) (5 : 𝓞 K5) := by
    have hB5 : IsCoprime (B ^ 5) 5 := (isCoprime_five_of_not_dvd h5B).pow_left
    obtain ⟨x, y, hxy⟩ := hB5
    refine ⟨(x : 𝓞 K5) * ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)), y, ?_⟩
    calc (x : 𝓞 K5) * ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)) *
          ((S : 𝓞 K5) - ζ * G) + (y : 𝓞 K5) * 5
        = (x : 𝓞 K5) * (((S : 𝓞 K5) - ζ * G) *
          ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G))) + (y : 𝓞 K5) * 5 := by
          ring
      _ = (x : 𝓞 K5) * (B : 𝓞 K5) ^ 5 + (y : 𝓞 K5) * 5 := by rw [hfac]
      _ = ((x * B ^ 5 + y * 5 : ℤ) : 𝓞 K5) := by push_cast; ring
      _ = 1 := by rw [hxy]; simp
  obtain ⟨hcSG, hc2, hc3, hc4⟩ := isCoprime_conj_factors hSG h5_cop
  have hcM : IsCoprime ((S : 𝓞 K5) - ζ * G) (M : 𝓞 K5) := by
    have hSG8 : (S : 𝓞 K5) - G = 8 * M := by exact_mod_cast hM
    rw [hSG8] at hcSG
    exact hcSG.of_mul_right_right
  have hcop_fac : IsCoprime ((S : 𝓞 K5) - ζ * G)
      ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)) :=
    ((hcM.mul_right hc2).mul_right hc3).mul_right hc4
  obtain ⟨α, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop_fac hfac
  set u0_bar : (𝓞 K5)ˣ := Units.map conj5.toMonoidHom u0
  set η_u : (𝓞 K5)ˣ := u0 * u0_bar⁻¹
  have hη_norm : (η_u : 𝓞 K5) * conj5 (η_u : 𝓞 K5) = 1 := by
    have hub : (u0_bar : 𝓞 K5) = conj5 (u0 : 𝓞 K5) := rfl
    have hinv1 : (u0_bar : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = 1 := Units.mul_inv u0_bar
    have hinv2 : (u0 : 𝓞 K5) * conj5 ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = 1 := by
      have := congr_arg conj5 hinv1
      rw [map_mul, map_one, hub, conj5_involution] at this
      exact this
    have hη_val : (η_u : 𝓞 K5) = (u0 : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) := rfl
    rw [hη_val, map_mul]
    calc (u0 : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) *
          (conj5 (u0 : 𝓞 K5) * conj5 ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5))
        = ((u0 : 𝓞 K5) * conj5 ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) *
          ((u0_bar : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) := by rw [hub]; ring
      _ = 1 := by rw [hinv2, hinv1, mul_one]
  obtain ⟨s, hs, k, hk, hη_eq⟩ := kronecker_unit5 hη_norm
  have hu0_rel : (u0 : 𝓞 K5) = s * ζ ^ k * conj5 (u0 : 𝓞 K5) := by
    have hub : (u0_bar : 𝓞 K5) = conj5 (u0 : 𝓞 K5) := rfl
    have hu_eq : η_u * u0_bar = u0 := by simp [η_u]
    calc (u0 : 𝓞 K5) = ((η_u * u0_bar : (𝓞 K5)ˣ) : 𝓞 K5) := (congr_arg Units.val hu_eq).symm
      _ = (η_u : 𝓞 K5) * (u0_bar : 𝓞 K5) := Units.val_mul η_u u0_bar
      _ = s * ζ ^ k * conj5 (u0 : 𝓞 K5) := by rw [hη_eq, hub]
  have hu0_conj : (conj5 α) ^ 5 * conj5 (u0 : 𝓞 K5) = (S : 𝓞 K5) - ζ ^ 4 * G := by
    have := congr_arg conj5 hu0
    simpa [conj5_ζ] using this
  obtain ⟨C, q, hα5⟩ := pow5_cong_int α
  have hα5_conj : (conj5 α) ^ 5 = (C : 𝓞 K5) + 5 * conj5 q := by
    rw [← map_pow, hα5, map_add, map_intCast, map_mul, map_ofNat]
  have hdiff5 : ((S : 𝓞 K5) - ζ * G) - s * ζ ^ k * ((S : 𝓞 K5) - ζ ^ 4 * G) =
      5 * (q * (u0 : 𝓞 K5) - s * ζ ^ k * conj5 q * conj5 (u0 : 𝓞 K5)) := by
    have hu0_sub : (u0 : 𝓞 K5) - s * ζ ^ k * conj5 (u0 : 𝓞 K5) = 0 := sub_eq_zero.mpr hu0_rel
    rw [← hu0, ← hu0_conj, hα5, hα5_conj]
    calc ((C : 𝓞 K5) + 5 * q) * (u0 : 𝓞 K5) -
          s * ζ ^ k * (((C : 𝓞 K5) + 5 * conj5 q) * conj5 (u0 : 𝓞 K5))
        = (C : 𝓞 K5) * ((u0 : 𝓞 K5) - s * ζ ^ k * conj5 (u0 : 𝓞 K5)) +
          5 * (q * (u0 : 𝓞 K5) - s * ζ ^ k * conj5 q * conj5 (u0 : 𝓞 K5)) := by ring
      _ = 5 * (q * (u0 : 𝓞 K5) - s * ζ ^ k * conj5 q * conj5 (u0 : 𝓞 K5)) := by
          rw [hu0_sub]; ring
  have heq25 : (G : ZMod 25) ^ 5 + 8 * (B : ZMod 25) ^ 5 = (S : ZMod 25) ^ 5 := by
    have := congr_arg (Int.cast : ℤ → ZMod 25) heq
    push_cast at this
    exact this
  rcases unit_conj_cases hs hk hdiff5 with h5G | h5S | h5SG | h5SmG
  · apply zmod25_no_sol_H2 (G : ZMod 25) (B : ZMod 25) (S : ZMod 25)
    · simp only [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5B
    · left
      simp only [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5G
    · exact heq25
  · apply zmod25_no_sol_H2 (G : ZMod 25) (B : ZMod 25) (S : ZMod 25)
    · simp only [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5B
    · right; left
      simp only [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5S
    · exact heq25
  · apply zmod25_no_sol_H2 (G : ZMod 25) (B : ZMod 25) (S : ZMod 25)
    · simp only [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5B
    · right; right
      rw [← Int.cast_add]
      simp only [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5SG
    · exact heq25
  · obtain ⟨t, ht⟩ := h5SmG
    have h5_8B5 : (5 : ℤ) ∣ 8 * B ^ 5 := by
      refine ⟨t * Q4, ?_⟩
      calc 8 * B ^ 5 = S ^ 5 - G ^ 5 := by linarith
        _ = (S - G) * Q4 := by dsimp [Q4]; ring
        _ = 5 * (t * Q4) := by rw [ht]; ring
    rcases Int.Prime.dvd_mul' Nat.prime_five h5_8B5 with h8 | hB5
    · norm_num at h8
    · exact h5B (Int.Prime.dvd_pow' Nat.prime_five hB5)

/- ## Section 4: Assembling the Full Proof of `H2` -/

lemma strip_two_five : ∀ n : ℕ, ∀ B : ℤ, B.natAbs = n → B ≠ 0 →
    ∃ a c : ℕ, ∃ B0 : ℤ, B0 ≠ 0 ∧ IsCoprime B0 10 ∧ B = 2 ^ a * 5 ^ c * B0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hn hB0
    by_cases h2 : (2 : ℤ) ∣ B
    · obtain ⟨B', rfl⟩ := h2
      have hB'0 : B' ≠ 0 := fun h0 => hB0 (by simp [h0])
      have hlt : B'.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have : 0 < B'.natAbs := Int.natAbs_pos.mpr hB'0
        have h2a : (2 : ℤ).natAbs = 2 := rfl
        rw [h2a]
        omega
      obtain ⟨a, c, B0, h0, hcop, hB'⟩ := ih _ hlt B' rfl hB'0
      exact ⟨a + 1, c, B0, h0, hcop, by rw [hB', pow_succ]; ring⟩
    · by_cases h5 : (5 : ℤ) ∣ B
      · obtain ⟨B', rfl⟩ := h5
        have hB'0 : B' ≠ 0 := fun h0 => hB0 (by simp [h0])
        have hlt : B'.natAbs < n := by
          rw [← hn, Int.natAbs_mul]
          have : 0 < B'.natAbs := Int.natAbs_pos.mpr hB'0
          have h5a : (5 : ℤ).natAbs = 5 := rfl
          rw [h5a]
          omega
        obtain ⟨a, c, B0, h0, hcop, hB'⟩ := ih _ hlt B' rfl hB'0
        exact ⟨a, c + 1, B0, h0, hcop, by rw [hB', pow_succ]; ring⟩
      · refine ⟨0, 0, B, hB0, ?_, by simp⟩
        have hc2 : IsCoprime B 2 := (Prime.coprime_iff_not_dvd Int.prime_two).mpr h2 |>.symm
        have hc5 : IsCoprime B 5 := isCoprime_five_of_not_dvd h5
        simpa using hc2.mul_right hc5

theorem h2_aux : ∀ s : ℕ, ∀ b g : ℕ, 0 < b → 0 < g → g ^ 5 + 8 * b ^ 5 ≠ s ^ 5 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro b g hb hg heq
    have hs_pos : 0 < s := by
      by_contra hs0
      have hs0' : s = 0 := by omega
      subst hs0'
      have : 0 < g ^ 5 + 8 * b ^ 5 := by positivity
      omega
    by_cases hcop_gs : Nat.Coprime g s
    · let G : ℤ := (g : ℤ)
      let B : ℤ := (b : ℤ)
      let S : ℤ := (s : ℤ)
      have heqZ : G ^ 5 + 8 * B ^ 5 = S ^ 5 := by dsimp only [G, B, S]; exact_mod_cast heq
      have hSG : IsCoprime S G :=
        Int.isCoprime_iff_gcd_eq_one.mpr (by change s.gcd g = 1; exact hcop_gs.symm)
      by_cases h5B : (5 : ℤ) ∣ B
      · have hB0 : B ≠ 0 := by omega
        obtain ⟨a, c, B0, hB0_ne, hB0_10, hB_eq⟩ := strip_two_five _ B rfl hB0
        have hc_pos : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | hpos
          · exfalso
            rw [pow_zero, mul_one] at hB_eq
            rw [hB_eq] at h5B
            have h2a_5 : IsCoprime (2 ^ a : ℤ) 5 := by
              have h25 : IsCoprime (2 : ℤ) 5 := ⟨-2, 1, by ring⟩
              exact h25.pow_left
            have h5B0 : (5 : ℤ) ∣ B0 := h2a_5.symm.dvd_of_dvd_mul_left h5B
            have hB0_5 : IsCoprime B0 5 := by
              have : (10 : ℤ) = 2 * 5 := by norm_num
              rw [this] at hB0_10
              exact hB0_10.of_mul_right_right
            exact not_isUnit_five (hB0_5.isUnit_of_dvd' h5B0 dvd_rfl)
          · exact hpos
        apply no_sol_case2 (x := S) (y := -G) (Z := B0) (m := 5 * a + 3) (n := 5 * c)
          (by omega) (by omega) hSG.neg_right hB0_10 hB0_ne
        calc S ^ 5 + (-G) ^ 5 = S ^ 5 - G ^ 5 := by ring
          _ = 8 * B ^ 5 := by linarith [heqZ]
          _ = 8 * (2 ^ a * 5 ^ c * B0) ^ 5 := by rw [hB_eq]
          _ = 2 ^ (5 * a + 3) * 5 ^ (5 * c) * B0 ^ 5 := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a 5, Nat.mul_comm c 5, pow_add]
              ring
      · exact no_sol_case1_H2 hSG h5B heqZ
    · obtain ⟨p, hp, hpg, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop_gs
      obtain ⟨g1, rfl⟩ := hpg
      obtain ⟨s1, rfl⟩ := hps
      have hpb : p ∣ b := by
        have hp5_dvd : p ^ 5 ∣ 8 * b ^ 5 := by
          have hp5_eq : p ^ 5 * g1 ^ 5 + 8 * b ^ 5 = p ^ 5 * s1 ^ 5 := by
            calc p ^ 5 * g1 ^ 5 + 8 * b ^ 5 = (p * g1) ^ 5 + 8 * b ^ 5 := by ring
              _ = (p * s1) ^ 5 := heq
              _ = p ^ 5 * s1 ^ 5 := by ring
          refine ⟨s1 ^ 5 - g1 ^ 5, ?_⟩
          rw [Nat.mul_sub_left_distrib]
          omega
        by_cases hp2 : p = 2
        · subst hp2
          obtain ⟨k, hk⟩ := hp5_dvd
          have hb5_even : 2 ∣ b ^ 5 := ⟨2 * k, by omega⟩
          exact Nat.prime_two.dvd_of_dvd_pow hb5_even
        · have hcop_p8 : Nat.Coprime (p ^ 5) 8 := by
            have hp_odd : Odd p := hp.odd_of_ne_two hp2
            exact hp_odd.coprime_two_right.pow 5 3
          have hp_b5 : p ∣ b ^ 5 := dvd_trans (dvd_pow_self p (by norm_num))
            (hcop_p8.dvd_of_dvd_mul_left hp5_dvd)
          exact hp.dvd_of_dvd_pow hp_b5
      obtain ⟨b1, rfl⟩ := hpb
      have hb1_pos : 0 < b1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hb)
      have hg1_pos : 0 < g1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hg)
      have hs1_pos : 0 < s1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hs_pos)
      have hs1_lt : s1 < p * s1 := by nlinarith [hp.one_lt]
      have heq1 : g1 ^ 5 + 8 * b1 ^ 5 = s1 ^ 5 := by
        have hp5_pos : 0 < p ^ 5 := pow_pos hp.pos 5
        apply Nat.eq_of_mul_eq_mul_left hp5_pos
        calc p ^ 5 * (g1 ^ 5 + 8 * b1 ^ 5) = (p * g1) ^ 5 + 8 * (p * b1) ^ 5 := by ring
          _ = (p * s1) ^ 5 := heq
          _ = p ^ 5 * s1 ^ 5 := by ring
      exact ih s1 hs1_lt b1 g1 hb1_pos hg1_pos heq1

end OMA672H2

theorem OMA.solution : OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1.H2 := by
  intro b g s hb hg
  exact OMA672H2.h2_aux s b g hb hg


