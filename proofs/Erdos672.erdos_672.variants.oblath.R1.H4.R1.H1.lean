import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1
import Mathlib

/-!
# Integer fifth powers in arithmetic progression: exact Obláth H1

New quartic descent formalization and integration: Hanan Beer (@hananzlt).
Mathematical proof: Dirichlet and V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵,
https://www.numdam.org/item/JMPA_1843_1_8__49_0.pdf (especially Propositions III–IV).

The golden-integer Euclidean ring, unit classification, fifth-power norm extraction, and
Dirichlet second-case descent below are reused from Pedro Bessa (@nijv):
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5575
Immutable source commit: 572ffd235e0a734035a1737d90d28c37c24417ee.
The exact reduction H1 is authored by @mudkjp, PR3625.
All original source attribution is retained in the component comments below.
This proves an auxiliary step expressing a classical known theorem, not a new mathematical discovery.
-/

/- Component: Dirichlet.lean -/

/-
Golden-integer fifth-power descent, reused from Pedro Bessa (@nijv), PR #5575:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5575
Immutable source head: 572ffd235e0a734035a1737d90d28c37c24417ee.
The source theorem formalizes Dirichlet's classical descent; the mathematical source is also
V.-A. Lebesgue (1843), Théorèmes nouveaux sur l'équation indéterminée x⁵ + y⁵ = az⁵.
Adaptation and integration for exact H1 by Hanan Beer (@hananzlt).
This is supporting material and is not an exact target proof.
-/


open NumberField QuadraticAlgebra

namespace OMA672H2

/- ## Section 1: Euclidean Structure and Units of `ℤ[(1 + √5)/2]` -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
abbrev R := QuadraticAlgebra ℤ 1 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma five_dvd_of_sq_dvd {x : ℤ} (h : (5 : ℤ) ∣ x ^ 2) : (5 : ℤ) ∣ x :=
  Int.Prime.dvd_pow' Nat.prime_five h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma not_isUnit_five : ¬ IsUnit (5 : ℤ) := by
  rw [Int.isUnit_iff]
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_iff_zmod2 (n : ℤ) : Even n ↔ (n : ZMod 2) = 0 := by
  have h2 : Even n ↔ ((2 : ℕ) : ℤ) ∣ n :=
    ⟨fun ⟨k, hk⟩ => ⟨k, by omega⟩, fun ⟨k, hk⟩ => ⟨k, by omega⟩⟩
  rw [h2, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_iff_zmod2 (n : ℤ) : Odd n ↔ (n : ZMod 2) = 1 := by
  rw [← Int.not_even_iff_odd, even_iff_zmod2]
  generalize (n : ZMod 2) = x
  revert x; decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma R_norm_eq_zero {z : R} (hz : z.norm = 0) : z = 0 := by
  have h4 : (2 * z.re + z.im) ^ 2 = 5 * z.im ^ 2 := by
    have : z.re * z.re + 1 * z.re * z.im - 1 * z.im * z.im = 0 := hz
    linear_combination 4 * this
  obtain ⟨hre, him⟩ := norm_eq_zero_aux _ z.re z.im rfl h4
  ext <;> simp [hre, him]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
instance : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have hn : a.norm * b.norm = 0 := by
      rw [← map_mul, hab, QuadraticAlgebra.norm_zero]
    rcases mul_eq_zero.mp hn with ha | hb
    · exact Or.inl (R_norm_eq_zero ha)
    · exact Or.inr (R_norm_eq_zero hb)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
instance : IsDomain R := NoZeroDivisors.to_isDomain R

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def nearestDiv (N d : ℤ) : ℤ :=
  let Ns := if 0 ≤ d then N else -N
  (2 * Ns + |d|) / (2 * |d|)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def R_div (a b : R) : R :=
  if b = 0 then 0 else
    let d := b.norm
    let num := a * star b
    ⟨nearestDiv num.re d, nearestDiv num.im d⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def ω₀ : R := ⟨0, 1⟩
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def ω_inv : R := ⟨-1, 1⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma ω₀_mul_inv : ω₀ * ω_inv = 1 := by
  ext <;> simp [ω₀, ω_inv]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma isUnit_ω₀ : IsUnit ω₀ :=
  ⟨⟨ω₀, ω_inv, ω₀_mul_inv, by rw [mul_comm]; exact ω₀_mul_inv⟩, rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma isUnit_ω_inv : IsUnit ω_inv :=
  ⟨⟨ω_inv, ω₀, by rw [mul_comm]; exact ω₀_mul_inv, ω₀_mul_inv⟩, rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma unit_form_neg {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ -v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  exact ⟨r, hr, -η, hη.neg, by ring⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma unit_form (u : R) (hu : IsUnit u) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ u = ω₀ ^ r * η ^ 5 := by
  have hn : IsUnit u.norm := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
  exact unit_form_aux _ u rfl (Int.isUnit_iff.mp hn)

/- ## Section 2: Dirichlet's 1825 Lemma and Second-Case Infinite Descent -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma mk_pow5 (c d : ℤ) :
    (⟨c, d⟩ : R) ^ 5 =
      ⟨c ^ 5 + 10 * c ^ 3 * d ^ 2 + 10 * c ^ 2 * d ^ 3 + 10 * c * d ^ 4 + 3 * d ^ 5,
       5 * d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4)⟩ := by
  ext <;> simp [pow_succ, pow_zero] <;> ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime n 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨1, -k, by ring⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma zmod2_im_zero : ∀ c d : ZMod 2,
    d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4) = 0 → d = 0 := by
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma pow5_of_coprime_int {a b c : ℤ} (h : IsCoprime a b) (habc : a * b = c ^ 5) :
    ∃ d : ℤ, a = d ^ 5 :=
  Int.eq_pow_of_mul_eq_pow_odd_left h (by decide) habc

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_add_of_odd_PQ5 {a b : ℤ}
    (h : Odd (a * (a ^ 4 + 50 * a ^ 2 * b ^ 2 + 125 * b ^ 4) +
      5 * b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4))) : Odd (a + b) := by
  rw [odd_iff_zmod2] at h ⊢
  push_cast at h ⊢
  revert h
  generalize (a : ZMod 2) = x, (b : ZMod 2) = y
  revert x y; decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def Eq2 (a b Z : ℤ) (M N : ℕ) : Prop :=
  1 ≤ M ∧ 1 ≤ N ∧ IsCoprime a b ∧ Odd (a + b) ∧ ¬ (5 : ℤ) ∣ a ∧ b ≠ 0 ∧ IsCoprime Z 10 ∧
    b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) = 2 ^ M * 5 ^ N * Z ^ 5

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
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


end OMA672H2


/- Component: Necessary.lean -/

/-
Elementary residue constraints for the fifth-power arithmetic-progression equation.
Work by Hanan Beer (@hananzlt). This is partial supporting work, not a proof of the target.
The modulo-25 split follows the classical approach of V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵ + y⁵ = az⁵.
-/


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem pow5_residue (a : Fin 25) :
    a.val ^ 5 % 25 = (a.val % 5) ^ 5 % 25 := by
  fin_cases a <;> norm_num

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem mod25_fifth_fin (a b c : Fin 5)
    (h : (a.val ^ 5 + b.val ^ 5) % 25 = (2 * c.val ^ 5) % 25) :
    (a.val = b.val ∧ a.val = c.val) ∨
    ((a.val + b.val) % 5 = 0 ∧ c.val = 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num at *

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem mod25_fifth (a b c : Fin 25)
    (h : (a.val ^ 5 + b.val ^ 5) % 25 = (2 * c.val ^ 5) % 25) :
    (a.val % 5 = b.val % 5 ∧ a.val % 5 = c.val % 5) ∨
    ((a.val + b.val) % 5 = 0 ∧ c.val % 5 = 0) := by
  rw [Nat.add_mod, Nat.mul_mod, pow5_residue a, pow5_residue b, pow5_residue c,
    ← Nat.add_mod, ← Nat.mul_mod] at h
  let a' : Fin 5 := ⟨a.val % 5, Nat.mod_lt _ (by decide)⟩
  let b' : Fin 5 := ⟨b.val % 5, Nat.mod_lt _ (by decide)⟩
  let c' : Fin 5 := ⟨c.val % 5, Nat.mod_lt _ (by decide)⟩
  simpa [a', b', c', Nat.add_mod] using mod25_fifth_fin a' b' c' h


/- A necessary congruence for the target equation; this is not sufficient for the target. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem fifth_ap_mod_five (x y z : ℤ) (h : x ^ 5 + y ^ 5 = 2 * z ^ 5) :
    (x % 5 = y % 5 ∧ x % 5 = z % 5) ∨ ((x + y) % 5 = 0 ∧ z % 5 = 0) := by
  let f (t : ℤ) : Fin 25 := ⟨(t % 25).toNat, by omega⟩
  have hf (t : ℤ) : ((f t).val : ℤ) = t % 25 := by
    dsimp [f]
    omega
  have hmod : ((x % 25) ^ 5 + (y % 25) ^ 5) % 25 = (2 * (z % 25) ^ 5) % 25 := by
    have hr (t : ℤ) : Int.ModEq 25 (t % 25) t := by
      show (t % 25) % 25 = t % 25
      exact Int.emod_emod t 25
    have hl := ((hr x).pow 5).add ((hr y).pow 5)
    have hz := ((hr z).pow 5).mul_left 2
    exact hl.eq.trans ((congrArg (fun t => t % 25) h).trans hz.eq.symm)
  have hnat : ((f x).val ^ 5 + (f y).val ^ 5) % 25 = (2 * (f z).val ^ 5) % 25 := by
    zify
    simpa only [hf] using hmod
  have hlift (t : ℤ) : (((f t).val % 5 : ℕ) : ℤ) = t % 5 := by
    push_cast
    rw [hf]
    omega
  rcases mod25_fifth (f x) (f y) (f z) hnat with ⟨hxy, hxz⟩ | ⟨hxy, hz⟩
  · left
    constructor
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hxy
      simpa only [hlift] using hh
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hxz
      simpa only [hlift] using hh
  · right
    constructor
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hxy
      push_cast at hh
      rw [hf, hf] at hh
      omega
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hz
      simpa only [hlift, Int.natCast_zero] using hh


/- Component: Primitive5.lean -/

/-
Primitive branch reductions for the exact fifth-power arithmetic-progression target.
New work by Hanan Beer (@hananzlt). The imported Dirichlet descent is by
Pedro Bessa (@nijv), PR5575 at head572ffd235e0a734035a1737d90d28c37c24417ee;
see Dirichlet.lean for source and mathematical attribution.
This file is supporting material, not a completed exact target proof.
-/

namespace OblathH1
open OMA672H2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_five_not_dvd {x y z : ℤ} (hcop : IsCoprime x y)
    (hz : z ≠ 0) (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : ¬ (5 : ℤ) ∣ z := by
  intro h5z
  obtain ⟨a, c, Z, hZ0, hZ10, hz_eq⟩ := strip_two_five _ z rfl hz
  have hc : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · exfalso
      simp only [pow_zero, mul_one] at hz_eq
      rw [hz_eq] at h5z
      have h25 : IsCoprime (2 : ℤ) 5 := ⟨-2, 1, by ring⟩
      have h5Z : (5 : ℤ) ∣ Z := h25.pow_left.symm.dvd_of_dvd_mul_left h5z
      have hZ5 : IsCoprime Z 5 := by
        rw [show (10 : ℤ) = 2 * 5 by norm_num] at hZ10
        exact hZ10.of_mul_right_right
      exact not_isUnit_five (hZ5.isUnit_of_dvd' h5Z dvd_rfl)
    · exact hc
  apply no_sol_case2 (x := x) (y := y) (Z := Z) (m := 5 * a + 1) (n := 5 * c)
    (by omega) (by omega) hcop hZ10 hZ0
  calc x ^ 5 + y ^ 5 = 2 * z ^ 5 := heq
    _ = 2 * (2 ^ a * 5 ^ c * Z) ^ 5 := by rw [hz_eq]
    _ = 2 ^ (5 * a + 1) * 5 ^ (5 * c) * Z ^ 5 := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a 5,
        Nat.mul_comm c 5, pow_succ]
      ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_five_dvd_sub {x y z : ℤ} (hcop : IsCoprime x y)
    (hz : z ≠ 0) (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : (5 : ℤ) ∣ x - y := by
  have hz5 := primitive_five_not_dvd hcop hz heq
  rcases fifth_ap_mod_five x y z heq with ⟨hxy, -⟩ | ⟨-, hzmod⟩
  · exact Int.dvd_of_emod_eq_zero (by omega)
  · exact False.elim (hz5 (Int.dvd_of_emod_eq_zero hzmod))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_odd_xy {x y z : ℤ} (hcop : IsCoprime x y)
    (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : Odd x ∧ Odd y := by
  have hev : Even (x ^ 5 + y ^ 5) := ⟨z ^ 5, by linarith⟩
  rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at hev
  rcases Int.even_or_odd x with hx | hx
  · have hy : Even y := hev.mp hx
    have h2unit := hcop.isUnit_of_dvd' hx.two_dvd hy.two_dvd
    norm_num [Int.isUnit_iff] at h2unit
  · refine ⟨hx, ?_⟩
    rcases Int.even_or_odd y with hy | hy
    · have hxev : Even x := hev.mpr hy
      exact False.elim (Int.not_even_iff_odd.mpr hx hxev)
    · exact hy

end OblathH1


/- Component: Factor.lean -/

/-
Coprime power-factor extraction for Lebesgue's quartic descent.
New formalization by Hanan Beer (@hananzlt), following V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
This file is supporting work for exact Oblath H1, not a complete solution.
-/

namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_pow_signed {A B C : ℤ} {k : ℕ} (hk : Even k) (hk0 : k ≠ 0)
    (hc : C ≠ 0) (hab : IsCoprime A B) (heq : A * B = C ^ k) :
    ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
      A = ε * u ^ k ∧ B = ε * v ^ k ∧ |C| = |u * v| := by
  obtain ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hab heq
  obtain ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hab.symm
    (show B * A = C ^ k by rw [mul_comm]; exact heq)
  replace hu := hu.symm
  replace hv := hv.symm
  rw [Int.associated_iff_natAbs, Int.natAbs_eq_natAbs_iff] at hu hv
  have hcpos : 0 < C ^ k := lt_of_le_of_ne (hk.pow_nonneg _) (Ne.symm (pow_ne_zero _ hc))
  have hu0 : 0 ≤ u ^ k := hk.pow_nonneg _
  have hv0 : 0 ≤ v ^ k := hk.pow_nonneg _
  have finish (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (ha : A = ε * u ^ k)
      (hb : B = ε * v ^ k) :
      ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
        A = ε * u ^ k ∧ B = ε * v ^ k ∧ |C| = |u * v| := by
    refine ⟨u, v, ε, hε, ?_, ha, hb, ?_⟩
    · have hcuv : IsCoprime (u ^ k) (v ^ k) := by
        rcases hε with rfl | rfl
        · simpa [ha, hb] using hab
        · simpa [ha, hb] using hab.neg_left.neg_right
      exact (IsCoprime.pow_left_iff (Nat.pos_of_ne_zero hk0)).mp
        ((IsCoprime.pow_right_iff (Nat.pos_of_ne_zero hk0)).mp hcuv)
    · have he : C ^ k = (u * v) ^ k := by
        rw [← heq, ha, hb, mul_pow]
        rcases hε with rfl | rfl <;> ring
      apply (pow_left_inj₀ (abs_nonneg C) (abs_nonneg (u * v)) hk0).mp
      rw [hk.pow_abs, hk.pow_abs]
      exact he
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact finish 1 (Or.inl rfl) (by simpa using hu) (by simpa using hv)
  · have hm : A * B ≤ 0 := by rw [hu, hv]; nlinarith
    omega
  · have hm : A * B ≤ 0 := by rw [hu, hv]; nlinarith
    omega
  · exact finish (-1) (Or.inr rfl) (by simpa using hu) (by simpa using hv)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma five_pow_split_left {A B C : ℤ} {r k : ℕ} (hk : Even k) (hk0 : k ≠ 0)
    (hc : C ≠ 0) (hab : IsCoprime A B) (hA5 : ¬ (5 : ℤ) ∣ A)
    (heq : A * B = 5 ^ r * C ^ k) :
    ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
      A = ε * u ^ k ∧ B = ε * 5 ^ r * v ^ k ∧ |C| = |u * v| ∧
      ¬ (5 : ℤ) ∣ u := by
  have h5A : IsCoprime (5 : ℤ) A :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Nat.prime_five)).mpr hA5
  have hdiv : (5 : ℤ) ^ r ∣ B := h5A.pow_left.dvd_of_dvd_mul_left ⟨C ^ k, heq⟩
  obtain ⟨B0, hB⟩ := hdiv
  have hAB0 : A * B0 = C ^ k := by
    apply mul_left_cancel₀ (show (5 : ℤ) ^ r ≠ 0 by positivity)
    calc 5 ^ r * (A * B0) = A * B := by rw [hB]; ring
      _ = 5 ^ r * C ^ k := heq
  have hcop0 : IsCoprime A B0 := by
    rw [hB] at hab
    exact hab.of_mul_right_right
  obtain ⟨u, v, ε, hε, huv, hu, hv, hcuv⟩ := even_pow_signed hk hk0 hc hcop0 hAB0
  refine ⟨u, v, ε, hε, huv, hu, ?_, hcuv, ?_⟩
  · rw [hB, hv]; ring
  · intro h5u
    apply hA5
    rw [hu]
    exact dvd_mul_of_dvd_right (dvd_pow h5u hk0) _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma five_pow_split {A B C : ℤ} {r k : ℕ} (hk : Even k) (hk0 : k ≠ 0)
    (hc : C ≠ 0) (hab : IsCoprime A B) (heq : A * B = 5 ^ r * C ^ k) :
    ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
      A + B = ε * (u ^ k + 5 ^ r * v ^ k) ∧ |C| = |u * v| ∧
      ¬ (5 : ℤ) ∣ u := by
  by_cases hA5 : (5 : ℤ) ∣ A
  · have hB5 : ¬ (5 : ℤ) ∣ B := by
      intro hB5
      have hu := hab.isUnit_of_dvd' hA5 hB5
      norm_num [Int.isUnit_iff] at hu
    obtain ⟨u, v, ε, hε, huv, hB, hA, hcuv, hu5⟩ :=
      five_pow_split_left hk hk0 hc hab.symm hB5 (by rw [mul_comm]; exact heq)
    exact ⟨u, v, ε, hε, huv, by rw [hA, hB]; ring, hcuv, hu5⟩
  · obtain ⟨u, v, ε, hε, huv, hA, hB, hcuv, hu5⟩ :=
      five_pow_split_left hk hk0 hc hab hA5 heq
    exact ⟨u, v, ε, hε, huv, by rw [hA, hB]; ring, hcuv, hu5⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_factors_of_sum {A B M D : ℤ} (hsum : A + B = M)
    (hprod : A * B = D) (hcop : IsCoprime M D) : IsCoprime A B := by
  rw [← hsum, ← hprod] at hcop
  have h := hcop.of_mul_right_right
  obtain ⟨r, s, hrs⟩ := h
  exact ⟨r, r + s, by linear_combination hrs⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_factors_five_pow {A B M C : ℤ} {r k : ℕ} (hsum : A + B = M)
    (hprod : A * B = 5 ^ r * C ^ k) (hcop : IsCoprime M C)
    (h5 : ¬ (5 : ℤ) ∣ M) : IsCoprime A B := by
  have hM5 : IsCoprime M 5 :=
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Nat.prime_five)).mpr h5).symm
  exact coprime_factors_of_sum hsum hprod (hM5.pow_right.mul_right hcop.pow_right)

end OblathH1


/- Component: Quartic.lean -/

/-
Lebesgue's quartic obstruction, supporting the exact Oblath H1 target.
New formalization by Hanan Beer (@hananzlt), following V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
This is incomplete supporting work; no exact target theorem is claimed here.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_pow_of_abs_eq {a b : ℤ} (h : |a| = |b|) {k : ℕ} (hk : Even k) :
    a ^ k = b ^ k := by
  rw [← hk.pow_abs a, ← hk.pow_abs b, h]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_four_mod16 {a : ℤ} (ha : Odd a) : a ^ 4 % 16 = 1 := by
  have hz : ((a ^ 4 : ℤ) : ZMod 16) = (1 : ℤ) := by
    obtain ⟨t, rfl⟩ := ha
    push_cast
    have h (t : ZMod 16) : (t + t + 1) ^ 4 = 1 := by fin_cases t <;> decide
    simpa [two_mul] using h (t : ZMod 16)
  exact (ZMod.intCast_eq_intCast_iff' _ _ 16).mp hz

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_eight_mod16 {a : ℤ} (ha : Odd a) : a ^ 8 % 16 = 1 := by
  have h : Int.ModEq 16 (a ^ 4) 1 := odd_four_mod16 ha
  have hh := h.pow 2
  simpa [← pow_mul] using hh.eq

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma not_five_dvd_four {a : ℤ} (ha : ¬ (5 : ℤ) ∣ a) : ¬ (5 : ℤ) ∣ a ^ 4 :=
  fun h => ha (Int.Prime.dvd_pow' Nat.prime_five h)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_product_of_abs_eq {a b c : ℤ} (ha : Odd a) (h : |a| = |b * c|) :
    Odd b ∧ Odd c := by
  have hbc : Odd |b * c| := h ▸ (odd_abs.mpr ha)
  exact Int.odd_mul.mp (odd_abs.mp hbc)

/- The first factorization of the odd branch. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_first {a d h : ℤ} (hah : IsCoprime a h) (ha5 : ¬ (5 : ℤ) ∣ a)
    (ha : Odd a) (hh : Odd h) (hh0 : h ≠ 0)
    (heq : d ^ 2 = a ^ 4 + 250 * a ^ 2 * h ^ 4 + 3125 * h ^ 8) :
    ∃ u v : ℤ, IsCoprime u v ∧ Odd u ∧ Odd v ∧ ¬ (5 : ℤ) ∣ u ∧
      |h| = |u * v| ∧ a ^ 2 = u ^ 8 - 125 * u ^ 4 * v ^ 4 + 3125 * v ^ 8 := by
  let M := a ^ 2 + 125 * h ^ 4
  have hMeven : Even M := by
    apply Int.even_iff.mpr
    have ha2 : Odd (a ^ 2) := ha.pow
    have hh4 : Odd (h ^ 4) := hh.pow
    rw [Int.odd_iff] at ha2 hh4
    dsimp [M]
    omega
  have hdeven : Even d := by
    apply (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    rw [heq]
    apply Int.even_iff.mpr
    have ha4 : Odd (a ^ 4) := ha.pow
    have hh8 : Odd (h ^ 8) := hh.pow
    rw [Int.odd_iff] at ha4 hh8
    rw [show a ^ 4 + 250 * a ^ 2 * h ^ 4 + 3125 * h ^ 8 =
      a ^ 4 + 250 * (a ^ 2 * h ^ 4) + 3125 * h ^ 8 by ring]
    omega
  obtain ⟨m, hm⟩ := hMeven
  obtain ⟨e, he⟩ := hdeven
  let A := m + e
  let B := m - e
  have hsum : A + B = M := by dsimp [A, B]; omega
  have hprod : A * B = 5 ^ 5 * h ^ 8 := by
    have hid : M ^ 2 - d ^ 2 = 4 * 5 ^ 5 * h ^ 8 := by
      dsimp [M]; linear_combination -heq
    dsimp [A, B]
    rw [hm, he] at hid
    nlinarith only [hid]
  have hMh : IsCoprime M h := by
    have hrep : M = a ^ 2 + h * (125 * h ^ 3) := by dsimp [M]; ring
    rw [hrep]
    exact hah.pow_left.add_mul_left_left _
  have hM5 : ¬ (5 : ℤ) ∣ M := by
    intro hd
    apply not_five_dvd_four ha5
    have ha2 : (5 : ℤ) ∣ a ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 25 * h ^ 4, by dsimp [M] at hk; linarith⟩
    exact dvd_trans ha2 (by use a ^ 2; ring)
  have hAB := coprime_factors_five_pow hsum hprod hMh hM5
  obtain ⟨u, v, ε, hε, huv, huv_sum, huv_abs, hu5⟩ :=
    five_pow_split (by decide : Even 8) (by decide) hh0 hAB hprod
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · have hMpos : 0 < M := by dsimp [M]; positivity
      have hu8 : 0 ≤ u ^ 8 := by positivity
      have hv8 : 0 ≤ v ^ 8 := by positivity
      rw [hsum, hε] at huv_sum
      nlinarith
  obtain ⟨huodd, hvodd⟩ := odd_product_of_abs_eq hh huv_abs
  have hh4 : h ^ 4 = (u * v) ^ 4 := even_pow_of_abs_eq huv_abs (by decide)
  refine ⟨u, v, huv, huodd, hvodd, hu5, huv_abs, ?_⟩
  rw [hsum, hε1] at huv_sum
  dsimp [M] at huv_sum
  rw [hh4] at huv_sum
  linear_combination huv_sum

end OblathH1

/- Component: QuarticOdd.lean -/

/-
The odd branch of Lebesgue's quartic obstruction.
Formalization: Hanan Beer (@hananzlt); mathematical proof: V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Proposition III.
Supporting work for exact Oblath H1. Not a complete exact solution.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_four_zmod16 {a : ℤ} (ha : Odd a) : (a : ZMod 16) ^ 4 = 1 := by
  have h := (ZMod.intCast_eq_intCast_iff' (a ^ 4) 1 16).mpr (odd_four_mod16 ha)
  simpa using h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_eight_zmod16 {a : ℤ} (ha : Odd a) : (a : ZMod 16) ^ 8 = 1 := by
  have h := (ZMod.intCast_eq_intCast_iff' (a ^ 8) 1 16).mpr (odd_eight_mod16 ha)
  simpa using h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma nonzero_of_odd {a : ℤ} (ha : Odd a) : a ≠ 0 := by
  rw [Int.odd_iff] at ha
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_of_abs_product {a b c d : ℤ} (hab : IsCoprime a b) (h : |b| = |c * d|) :
    IsCoprime a c ∧ IsCoprime a d := by
  rcases abs_eq_abs.mp h with hb | hb
  · rw [hb] at hab
    exact ⟨hab.of_mul_right_left, hab.of_mul_right_right⟩
  · have h' : IsCoprime a (c * d) := by
      simpa [hb] using hab.neg_right
    exact ⟨h'.of_mul_right_left, h'.of_mul_right_right⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_second {a u v : ℤ} (huv : IsCoprime u v)
    (huodd : Odd u) (hvodd : Odd v) (hu5 : ¬ (5 : ℤ) ∣ u)
    (heq : a ^ 2 = u ^ 8 - 125 * u ^ 4 * v ^ 4 + 3125 * v ^ 8) :
    ∃ p q L : ℤ, IsCoprime p q ∧ IsCoprime p u ∧ Odd p ∧ Odd q ∧ Odd L ∧
      ¬ (5 : ℤ) ∣ p ∧ p ^ 8 - u ^ 4 = 80 * L ^ 2 ∧
      p ^ 4 - 25 * q ^ 4 = 8 * L := by
  let D := 2 * u ^ 4 - 125 * v ^ 4
  let A := D + 2 * a
  let B := D - 2 * a
  have hsum : A + B = 2 * D := by dsimp [A, B]; ring
  have hprod : A * B = 5 ^ 5 * v ^ 8 := by
    dsimp [A, B, D]
    linear_combination -4 * heq
  have h2v : IsCoprime (2 : ℤ) v := Int.isCoprime_two_left.mpr hvodd
  have hDv : IsCoprime D v := by
    have hr : D = 2 * u ^ 4 + v * (-(125 * v ^ 3)) := by dsimp [D]; ring
    rw [hr]
    exact (h2v.mul_left huv.pow_left).add_mul_left_left _
  have h2D5 : ¬ (5 : ℤ) ∣ 2 * D := by
    intro hd
    have h4u : (5 : ℤ) ∣ 4 * u ^ 4 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k + 50 * v ^ 4, by dsimp [D] at hk; linarith⟩
    rcases Int.Prime.dvd_mul' Nat.prime_five h4u with h4 | hu
    · norm_num at h4
    · exact hu5 (Int.Prime.dvd_pow' Nat.prime_five hu)
  have hAB := coprime_factors_five_pow hsum hprod (h2v.mul_left hDv) h2D5
  obtain ⟨p, q, ε, hε, hpq, hsum2, hvabs, hp5⟩ :=
    five_pow_split (by decide : Even 8) (by decide) (nonzero_of_odd hvodd) hAB hprod
  obtain ⟨hpodd, hqodd⟩ := odd_product_of_abs_eq hvodd hvabs
  have hv4 := even_pow_of_abs_eq hvabs (by decide : Even 4)
  have hbase : 4 * u ^ 4 = ε * (p ^ 8 + 3125 * q ^ 8) + 250 * p ^ 4 * q ^ 4 := by
    rw [hsum] at hsum2
    dsimp [D] at hsum2
    rw [hv4] at hsum2
    linear_combination hsum2
  have hεneg : ε = -1 := by
    rcases hε with hε | hε
    · exfalso
      rw [hε] at hbase
      have hmod := congrArg (fun x : ℤ => (x : ZMod 16)) hbase
      push_cast at hmod
      rw [odd_four_zmod16 huodd, odd_eight_zmod16 hpodd, odd_eight_zmod16 hqodd,
        odd_four_zmod16 hpodd, odd_four_zmod16 hqodd] at hmod
      norm_num at hmod
      exact (by decide : (4 : ZMod 16) ≠ 3376) hmod
    · exact hε
  let L := (p ^ 4 - 25 * q ^ 4) / 8
  have hp4 := odd_four_mod16 hpodd
  have hq4 := odd_four_mod16 hqodd
  have hL : p ^ 4 - 25 * q ^ 4 = 8 * L := by dsimp [L]; omega
  have hLodd : Odd L := by rw [Int.odd_iff]; dsimp [L]; omega
  have hpu : IsCoprime p u := ((coprime_of_abs_product huv hvabs).1).symm
  refine ⟨p, q, L, hpq, hpu, hpodd, hqodd, hLodd, hp5, ?_, hL⟩
  have hid : 4 * (p ^ 8 - u ^ 4) = 5 * (p ^ 4 - 25 * q ^ 4) ^ 2 := by
    rw [hεneg] at hbase
    linear_combination -hbase
  rw [hL] at hid
  nlinarith only [hid]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_sq_zmod8 {a : ℤ} (ha : Odd a) : (a : ZMod 8) ^ 2 = 1 := by
  obtain ⟨t, rfl⟩ := ha
  push_cast
  have h (t : ZMod 8) : (t + t + 1) ^ 2 = 1 := by fin_cases t <;> decide
  simpa [two_mul] using h (t : ZMod 8)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_four_zmod8 {a : ℤ} (ha : Odd a) : (a : ZMod 8) ^ 4 = 1 := by
  calc (a : ZMod 8) ^ 4 = ((a : ZMod 8) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [odd_sq_zmod8 ha]; norm_num

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_final {p q u L : ℤ} (hpq : IsCoprime p q)
    (hpodd : Odd p) (huodd : Odd u) (hLodd : Odd L)
    (hp5 : ¬ (5 : ℤ) ∣ p) (heq : p ^ 8 - u ^ 4 = 80 * L ^ 2)
    (hL : p ^ 4 - 25 * q ^ 4 = 8 * L) : False := by
  have hpL : IsCoprime p L := by
    have hp5cop : IsCoprime p 5 :=
      ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Nat.prime_five)).mpr hp5).symm
    have hp25 : IsCoprime p 25 := by simpa using (hp5cop.pow_right (n := 2))
    have hc := (hp25.mul_right (hpq.pow_right (n := 4))).neg_right.add_mul_left_right (p ^ 3)
    have he : -(25 * q ^ 4) + p * p ^ 3 = 8 * L := by linear_combination hL
    rw [he] at hc
    exact hc.of_mul_right_right
  have hp2 : IsCoprime p 2 := Int.isCoprime_two_right.mpr hpodd
  have hp2L : IsCoprime p (2 * L) := hp2.mul_right hpL
  have hp4odd : Odd (p ^ 4) := hpodd.pow
  have hu2odd : Odd (u ^ 2) := huodd.pow
  obtain ⟨A, hA⟩ : Even (p ^ 4 + u ^ 2) := hp4odd.add_odd hu2odd
  obtain ⟨B, hB⟩ : Even (p ^ 4 - u ^ 2) := hp4odd.sub_odd hu2odd
  have hsum : A + B = p ^ 4 := by omega
  have hprod : A * B = 5 ^ 1 * (2 * L) ^ 2 := by
    have hid : (p ^ 4 + u ^ 2) * (p ^ 4 - u ^ 2) = 4 * (5 ^ 1 * (2 * L) ^ 2) := by
      linear_combination heq
    rw [hA, hB] at hid
    nlinarith only [hid]
  have hAB := coprime_factors_five_pow hsum hprod hp2L.pow_left (not_five_dvd_four hp5)
  have h2L0 : 2 * L ≠ 0 := mul_ne_zero (by norm_num) (nonzero_of_odd hLodd)
  obtain ⟨r, s, ε, hε, hrs, hrs_sum, hrs_abs, -⟩ :=
    five_pow_split (by decide : Even 2) (by decide) h2L0 hAB hprod
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · have hp4pos : 0 < p ^ 4 := by
        exact pow_pos (abs_pos.mpr (nonzero_of_odd hpodd)) 4 |>.trans_eq (by rw [Even.pow_abs (by decide : Even 4)])
      rw [hsum, hε] at hrs_sum
      nlinarith [sq_nonneg r, sq_nonneg s]
  have hrs_eq : r ^ 2 + 5 * s ^ 2 = p ^ 4 := by
    rw [hsum, hε1] at hrs_sum
    simpa using hrs_sum.symm
  have hrs_prod : (r * s) ^ 2 = (2 * L) ^ 2 :=
    (even_pow_of_abs_eq hrs_abs (by decide : Even 2)).symm
  have hsumz : (r : ZMod 8) ^ 2 + 5 * (s : ZMod 8) ^ 2 = 1 := by
    have hh := congrArg (fun x : ℤ => (x : ZMod 8)) hrs_eq
    push_cast at hh
    rwa [odd_four_zmod8 hpodd] at hh
  have hprodz : ((r : ZMod 8) * (s : ZMod 8)) ^ 2 = 4 := by
    have hh := congrArg (fun x : ℤ => (x : ZMod 8)) hrs_prod
    push_cast at hh
    rw [mul_pow, mul_pow, odd_sq_zmod8 hLodd] at hh
    norm_num at hh ⊢
    simpa only [mul_pow] using hh
  have hres : (r : ZMod 8) ^ 2 = 4 ∧ (s : ZMod 8) ^ 2 = 1 := by
    have hh : ∀ r s : ZMod 8, r ^ 2 + 5 * s ^ 2 = 1 → (r * s) ^ 2 = 4 →
        r ^ 2 = 4 ∧ s ^ 2 = 1 := by
      intro r s; fin_cases r <;> fin_cases s <;> decide
    exact hh (r : ZMod 8) (s : ZMod 8) hsumz hprodz
  have hrmod : r ^ 2 % 8 = 4 := (ZMod.intCast_eq_intCast_iff' (r ^ 2) 4 8).mp (by
    push_cast; exact hres.1)
  have hsmod : s ^ 2 % 8 = 1 := (ZMod.intCast_eq_intCast_iff' (s ^ 2) 1 8).mp (by
    push_cast; exact hres.2)
  have hreven : Even r := (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    (Int.even_iff.mpr (by omega))
  have hsodd : Odd s := (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    (Int.odd_iff.mpr (by omega))
  obtain ⟨R, hR⟩ := hreven
  have hps := (coprime_of_abs_product hp2L hrs_abs).2
  let C := p ^ 2 + 2 * R
  let D := p ^ 2 - 2 * R
  have hsum2 : C + D = 2 * p ^ 2 := by dsimp [C, D]; ring
  have hprod2 : C * D = 5 ^ 1 * s ^ 2 := by
    dsimp [C, D]
    rw [hR] at hrs_eq
    linear_combination -hrs_eq
  have h2s : IsCoprime (2 : ℤ) s := Int.isCoprime_two_left.mpr hsodd
  have h2p5 : ¬ (5 : ℤ) ∣ 2 * p ^ 2 := by
    intro hd
    rcases Int.Prime.dvd_mul' Nat.prime_five hd with h2 | hp
    · norm_num at h2
    · exact hp5 (Int.Prime.dvd_pow' Nat.prime_five hp)
  have hCD := coprime_factors_five_pow hsum2 hprod2 (h2s.mul_left hps.pow_left) h2p5
  obtain ⟨t, w, η, hη, -, htw, -, -⟩ :=
    five_pow_split (by decide : Even 2) (by decide) (nonzero_of_odd hsodd) hCD hprod2
  have hη1 : η = 1 := by
    rcases hη with hη | hη
    · exact hη
    · have hp2pos := sq_pos_of_ne_zero (nonzero_of_odd hpodd)
      rw [hsum2, hη] at htw
      nlinarith [sq_nonneg t, sq_nonneg w]
  rw [hsum2, hη1] at htw
  have hmod := congrArg (fun x : ℤ => (x : ZMod 5)) htw
  push_cast at hmod
  rw [show (5 : ZMod 5) = 0 by decide, zero_mul, add_zero] at hmod
  norm_num at hmod
  have hres5 : ∀ p t : ZMod 5, 2 * p ^ 2 = t ^ 2 → p = 0 := by
    decide
  have hpzero : (p : ZMod 5) = 0 := hres5 (p : ZMod 5) (t : ZMod 5) hmod
  exact hp5 ((ZMod.intCast_zmod_eq_zero_iff_dvd p 5).mp hpzero)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_no_solution {a h d : ℤ} (hah : IsCoprime a h)
    (ha5 : ¬ (5 : ℤ) ∣ a) (ha : Odd a) (hh : Odd h) (hh0 : h ≠ 0)
    (heq : d ^ 2 = a ^ 4 + 250 * a ^ 2 * h ^ 4 + 3125 * h ^ 8) : False := by
  obtain ⟨u, v, huv, huodd, hvodd, hu5, -, hfirst⟩ :=
    odd_quartic_first hah ha5 ha hh hh0 heq
  obtain ⟨p, q, L, hpq, -, hpodd, -, hLodd, hp5, hsecond, hL⟩ :=
    odd_quartic_second huv huodd hvodd hu5 hfirst
  exact odd_quartic_final hpq hpodd huodd hLodd hp5 hsecond hL

end OblathH1


/- Component: Squareclass.lean -/

/-
Preservation of the 5/10 square classes in Lebesgue's quartic descent.
Formalization by Hanan Beer (@hananzlt); mathematical source V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Proposition III.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma positive_five_square_extract {A B H : ℤ} (hA : 0 < A) (hB : 0 < B)
    (hcop : IsCoprime A B) (hA5 : ¬ (5 : ℤ) ∣ A) (heq : A * B = 5 * H ^ 2) :
    ∃ v : ℤ, B = 5 * v ^ 2 := by
  have hH0 : H ≠ 0 := by intro h; rw [h] at heq; nlinarith
  obtain ⟨u, v, ε, hε, -, -, hBv, -, -⟩ := five_pow_split_left
    (by decide : Even 2) (by decide) hH0 hcop hA5
    (show A * B = 5 ^ 1 * H ^ 2 by simpa using heq)
  rcases hε with rfl | rfl
  · exact ⟨v, by simpa using hBv⟩
  · nlinarith [sq_nonneg v]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma squareclass_descend {A B H : ℤ} (hA : 0 < A) (hB : 0 < B)
    (hcop : IsCoprime A B) (hA5 : ¬ (5 : ℤ) ∣ A)
    (heq : 2 * A * B = 5 * H ^ 2 ∨ 2 * A * B = 10 * H ^ 2) :
    ∃ v : ℤ, B = 5 * v ^ 2 ∨ B = 10 * v ^ 2 := by
  rcases heq with heq | heq
  · have hHeven : Even H := by
      apply (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
      apply Int.even_iff.mpr
      have hlin : 2 * (A * B) = 5 * H ^ 2 := by linear_combination heq
      omega
    obtain ⟨K, hK⟩ := hHeven
    have heq' : A * B = 10 * K ^ 2 := by rw [hK] at heq; nlinarith only [heq]
    rcases Int.even_or_odd B with hBeven | hBodd
    · have hAodd : Odd A := by
        rcases Int.even_or_odd A with hAe | hAo
        · have hu := hcop.isUnit_of_dvd' hAe.two_dvd hBeven.two_dvd
          norm_num [Int.isUnit_iff] at hu
        · exact hAo
      have hA2 : IsCoprime A 2 := Int.isCoprime_two_right.mpr hAodd
      obtain ⟨v, hv⟩ := positive_five_square_extract hA (by omega : 0 < 2 * B)
        (hA2.mul_right hcop) hA5 (show A * (2 * B) = 5 * (2 * K) ^ 2 by
          linear_combination 2 * heq')
      have hveven : Even v := by
        apply (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
        apply Int.even_iff.mpr
        omega
      obtain ⟨w, hw⟩ := hveven
      exact ⟨w, Or.inr (by rw [hw] at hv; nlinarith only [hv])⟩
    · have h2B : IsCoprime (2 : ℤ) B := Int.isCoprime_two_left.mpr hBodd
      have h2A5 : ¬ (5 : ℤ) ∣ 2 * A := by
        intro hd
        rcases Int.Prime.dvd_mul' Nat.prime_five hd with h2 | hA
        · norm_num at h2
        · exact hA5 hA
      obtain ⟨v, hv⟩ := positive_five_square_extract (by omega : 0 < 2 * A) hB
        (h2B.mul_left hcop) h2A5 (show (2 * A) * B = 5 * (2 * K) ^ 2 by
          linear_combination 2 * heq')
      exact ⟨v, Or.inl hv⟩
  · obtain ⟨v, hv⟩ := positive_five_square_extract hA hB hcop hA5
      (show A * B = 5 * H ^ 2 by nlinarith only [heq])
    exact ⟨v, Or.inl hv⟩

end OblathH1

/- Component: QuarticEven.lean -/

/-
The even branch of Lebesgue's quartic descent.
Formalization by Hanan Beer (@hananzlt), following V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
Supporting work for exact Oblath H1, not a complete solution.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_first {a c d : ℤ} (hac : IsCoprime a c)
    (haodd : Odd a) (hceven : Even c) (hc0 : c ≠ 0) (ha5 : ¬ (5 : ℤ) ∣ a)
    (heq : d ^ 2 = a ^ 4 + 10 * a ^ 2 * c ^ 2 + 5 * c ^ 4) :
    ∃ g f : ℤ, IsCoprime g f ∧ ¬ (5 : ℤ) ∣ g ∧ |c| = |g * f| ∧
      a ^ 2 = g ^ 4 - 5 * g ^ 2 * f ^ 2 + 5 * f ^ 4 := by
  let M := a ^ 2 + 5 * c ^ 2
  have hModd : Odd M := by
    have ha2 : Odd (a ^ 2) := haodd.pow
    have hc2 : Even (c ^ 2) := hceven.pow_of_ne_zero (by decide)
    rw [Int.odd_iff] at ha2 ⊢
    rw [Int.even_iff] at hc2
    dsimp [M]; omega
  have hdodd : Odd d := by
    apply (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    rw [heq, Int.odd_iff]
    have ha4 : Odd (a ^ 4) := haodd.pow
    have hc4 : Even (c ^ 4) := hceven.pow_of_ne_zero (by decide)
    rw [Int.odd_iff] at ha4
    rw [Int.even_iff] at hc4
    rw [show a ^ 4 + 10 * a ^ 2 * c ^ 2 + 5 * c ^ 4 =
      a ^ 4 + 10 * (a ^ 2 * c ^ 2) + 5 * c ^ 4 by ring]
    omega
  obtain ⟨A, hA⟩ := hModd.add_odd hdodd
  obtain ⟨B, hB⟩ := hModd.sub_odd hdodd
  have hsum : A + B = M := by omega
  have hprod : A * B = 5 ^ 1 * c ^ 4 := by
    have hid : (M + d) * (M - d) = 4 * (5 ^ 1 * c ^ 4) := by
      dsimp [M]; linear_combination -heq
    rw [hA, hB] at hid
    nlinarith only [hid]
  have hMc : IsCoprime M c := by
    have hrep : M = a ^ 2 + c * (5 * c) := by dsimp [M]; ring
    rw [hrep]
    exact hac.pow_left.add_mul_left_left _
  have hM5 : ¬ (5 : ℤ) ∣ M := by
    intro hd
    have ha2 : (5 : ℤ) ∣ a ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - c ^ 2, by dsimp [M] at hk; linarith⟩
    exact ha5 (Int.Prime.dvd_pow' Nat.prime_five ha2)
  have hAB := coprime_factors_five_pow hsum hprod hMc hM5
  obtain ⟨g, f, ε, hε, hgf, hgf_sum, hgf_abs, hg5⟩ :=
    five_pow_split (by decide : Even 4) (by decide) hc0 hAB hprod
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · have hMpos : 0 < M := by
        dsimp [M]; nlinarith [sq_pos_of_ne_zero (nonzero_of_odd haodd), sq_nonneg c]
      rw [hsum, hε] at hgf_sum
      nlinarith [sq_nonneg (g ^ 2), sq_nonneg (f ^ 2)]
  have hc2 := even_pow_of_abs_eq hgf_abs (by decide : Even 2)
  refine ⟨g, f, hgf, hg5, hgf_abs, ?_⟩
  rw [hsum, hε1] at hgf_sum
  dsimp [M] at hgf_sum
  rw [hc2] at hgf_sum
  linear_combination hgf_sum

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_step_even {a g h : ℤ} (hgh : IsCoprime g h)
    (haodd : Odd a) (hgodd : Odd g) (hg5 : ¬ (5 : ℤ) ∣ g) (hh0 : h ≠ 0)
    (heq : a ^ 2 = g ^ 4 - 20 * g ^ 2 * h ^ 2 + 80 * h ^ 4) :
    ∃ u v : ℤ, IsCoprime u v ∧ Odd u ∧ ¬ (5 : ℤ) ∣ u ∧ |h| = |u * v| ∧
      g ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 := by
  let D := g ^ 2 - 10 * h ^ 2
  have hDodd : Odd D := by
    have hg2 : Odd (g ^ 2) := hgodd.pow
    rw [Int.odd_iff] at hg2 ⊢
    dsimp [D]; omega
  obtain ⟨A, hA⟩ := hDodd.add_odd haodd
  obtain ⟨B, hB⟩ := hDodd.sub_odd haodd
  have hsum : A + B = D := by omega
  have hprod : A * B = 5 ^ 1 * h ^ 4 := by
    have hid : (D + a) * (D - a) = 4 * (5 ^ 1 * h ^ 4) := by
      dsimp [D]; linear_combination -heq
    rw [hA, hB] at hid
    nlinarith only [hid]
  have hDh : IsCoprime D h := by
    have hr : D = g ^ 2 + h * (-10 * h) := by dsimp [D]; ring
    rw [hr]
    exact hgh.pow_left.add_mul_left_left _
  have hD5 : ¬ (5 : ℤ) ∣ D := by
    intro hd
    have hg2 : (5 : ℤ) ∣ g ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k + 2 * h ^ 2, by dsimp [D] at hk; linarith⟩
    exact hg5 (Int.Prime.dvd_pow' Nat.prime_five hg2)
  have hAB := coprime_factors_five_pow hsum hprod hDh hD5
  obtain ⟨u, v, ε, hε, huv, huv_sum, huv_abs, hu5⟩ :=
    five_pow_split (by decide : Even 4) (by decide) hh0 hAB hprod
  have hh2 := even_pow_of_abs_eq huv_abs (by decide : Even 2)
  have hbase : g ^ 2 = ε * (u ^ 4 + 5 * v ^ 4) + 10 * u ^ 2 * v ^ 2 := by
    rw [hsum] at huv_sum
    dsimp [D] at huv_sum
    rw [hh2] at huv_sum
    linear_combination huv_sum
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · exfalso
      rw [hε] at hbase
      have hmod := congrArg (fun x : ℤ => (x : ZMod 8)) hbase
      push_cast at hmod
      rw [odd_sq_zmod8 hgodd] at hmod
      have impossible : ∀ u v : ZMod 8,
          1 ≠ -1 * (u ^ 4 + 5 * v ^ 4) + 10 * u ^ 2 * v ^ 2 := by
        intro u v; fin_cases u <;> fin_cases v <;> decide
      exact impossible (u : ZMod 8) (v : ZMod 8) hmod
  have hnew : g ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 := by
    rw [hε1] at hbase
    linear_combination hbase
  have huodd : Odd u := by
    have hmod := congrArg (fun x : ℤ => (x : ZMod 8)) hnew
    push_cast at hmod
    rw [odd_sq_zmod8 hgodd] at hmod
    have hc : ∀ u v : ZMod 8,
        1 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 → u ^ 2 = 1 := by
      intro u v; fin_cases u <;> fin_cases v <;> decide
    have hu2z := hc (u : ZMod 8) (v : ZMod 8) hmod
    have hu2mod : u ^ 2 % 8 = 1 := (ZMod.intCast_eq_intCast_iff' (u ^ 2) 1 8).mp (by
      push_cast; exact hu2z)
    exact (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp (Int.odd_iff.mpr (by omega))
  exact ⟨u, v, huv, huodd, hu5, huv_abs, hnew⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_step_odd {a f h : ℤ} (hhf : IsCoprime h f)
    (hfodd : Odd f) (hh5 : ¬ (5 : ℤ) ∣ h)
    (heq : a ^ 2 = 16 * h ^ 4 - 20 * h ^ 2 * f ^ 2 + 5 * f ^ 4) :
    ∃ u v : ℤ, IsCoprime u v ∧ Odd u ∧ Odd v ∧ ¬ (5 : ℤ) ∣ u ∧ |f| = |u * v| ∧
      (4 * h) ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 := by
  let D := 8 * h ^ 2 - 5 * f ^ 2
  let A := D + 2 * a
  let B := D - 2 * a
  have hsum : A + B = 2 * D := by dsimp [A, B]; ring
  have hprod : A * B = 5 ^ 1 * f ^ 4 := by
    dsimp [A, B, D]
    linear_combination -4 * heq
  have h2f : IsCoprime (2 : ℤ) f := Int.isCoprime_two_left.mpr hfodd
  have h8f : IsCoprime (8 : ℤ) f := by simpa using (h2f.pow_left (m := 3))
  have hDf : IsCoprime D f := by
    have hr : D = 8 * h ^ 2 + f * (-5 * f) := by dsimp [D]; ring
    rw [hr]
    exact (h8f.mul_left hhf.pow_left).add_mul_left_left _
  have h2D5 : ¬ (5 : ℤ) ∣ 2 * D := by
    intro hd
    have h16h : (5 : ℤ) ∣ 16 * h ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k + 2 * f ^ 2, by dsimp [D] at hk; linarith⟩
    rcases Int.Prime.dvd_mul' Nat.prime_five h16h with h16 | hh
    · norm_num at h16
    · exact hh5 (Int.Prime.dvd_pow' Nat.prime_five hh)
  have hAB := coprime_factors_five_pow hsum hprod (h2f.mul_left hDf) h2D5
  obtain ⟨u, v, ε, hε, huv, huv_sum, huv_abs, hu5⟩ :=
    five_pow_split (by decide : Even 4) (by decide) (nonzero_of_odd hfodd) hAB hprod
  obtain ⟨huodd, hvodd⟩ := odd_product_of_abs_eq hfodd huv_abs
  have hf2 := even_pow_of_abs_eq huv_abs (by decide : Even 2)
  have hbase : 16 * h ^ 2 = ε * (u ^ 4 + 5 * v ^ 4) + 10 * u ^ 2 * v ^ 2 := by
    rw [hsum] at huv_sum
    dsimp [D] at huv_sum
    rw [hf2] at huv_sum
    linear_combination huv_sum
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · exfalso
      rw [hε] at hbase
      have hmod := congrArg (fun x : ℤ => (x : ZMod 16)) hbase
      push_cast at hmod
      rw [odd_four_zmod16 huodd, odd_four_zmod16 hvodd] at hmod
      have hu2 := odd_sq_zmod8 huodd
      have hv2 := odd_sq_zmod8 hvodd
      have hmod8 := congrArg (fun x : ℤ => (x : ZMod 8)) hbase
      push_cast at hmod8
      rw [odd_four_zmod8 huodd, odd_four_zmod8 hvodd, hu2, hv2] at hmod8
      rw [show (16 : ZMod 8) = 0 by decide, zero_mul] at hmod8
      norm_num at hmod8
      exact (by decide : (0 : ZMod 8) ≠ 4) hmod8
  refine ⟨u, v, huv, huodd, hvodd, hu5, huv_abs, ?_⟩
  rw [hε1] at hbase
  linear_combination hbase

end OblathH1

/- Component: Descent.lean -/

/-
Assembly of Lebesgue's quartic descent, supporting exact Oblath H1.
Formalization by Hanan Beer (@hananzlt); proof source V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def FiveSquareclass (c : ℤ) : Prop := ∃ H : ℤ, c = 5 * H ^ 2 ∨ c = 10 * H ^ 2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def QuarticCandidate (c : ℤ) : Prop :=
  0 < c ∧ ∃ a d : ℤ, IsCoprime a c ∧ Odd a ∧ ¬ (5 : ℤ) ∣ a ∧
    FiveSquareclass c ∧ d ^ 2 = a ^ 4 + 10 * a ^ 2 * c ^ 2 + 5 * c ^ 4

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma nonzero_of_not_five_dvd {a : ℤ} (ha : ¬ (5 : ℤ) ∣ a) : a ≠ 0 := by
  intro h; apply ha; simp [h]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_abs_right_int {a b : ℤ} (h : IsCoprime a b) : IsCoprime a |b| := by
  rcases le_total 0 b with hb | hb
  · simpa [abs_of_nonneg hb] using h
  · simpa [abs_of_nonpos hb] using h.neg_right

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_candidate {c : ℤ} (hc : QuarticCandidate c) (hcodd : Odd c) : False := by
  obtain ⟨hcpos, a, d, hac, haodd, ha5, ⟨H, hH⟩, heq⟩ := hc
  rcases hH with hH | hH
  · have hHodd : Odd H := by
      have hprod : Odd (5 * H ^ 2) := hH ▸ hcodd
      have hsq := (Int.odd_mul.mp hprod).2
      exact (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp hsq
    have haH : IsCoprime a H := hac.of_isCoprime_of_dvd_right
      ⟨5 * H, by rw [hH]; ring⟩
    have heq' : d ^ 2 = a ^ 4 + 250 * a ^ 2 * H ^ 4 + 3125 * H ^ 8 := by
      rw [hH] at heq
      linear_combination heq
    exact odd_quartic_no_solution haH ha5 haodd hHodd (nonzero_of_odd hHodd) heq'
  · have hceven : Even c := ⟨5 * H ^ 2, by linarith⟩
    exact Int.not_even_iff_odd.mpr hcodd hceven

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma package_descent {c k u v d : ℤ} (_hc : 0 < c)
    (hclass : FiveSquareclass c) (hcid : c = 2 * |k * u| * |v|)
    (hkv : IsCoprime k v) (huv : IsCoprime u v)
    (hk5 : ¬ (5 : ℤ) ∣ k) (hu5 : ¬ (5 : ℤ) ∣ u) (huodd : Odd u) (hv0 : v ≠ 0)
    (heq : d ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4) :
    ∃ c' : ℤ, c' < c ∧ QuarticCandidate c' := by
  have hA : 0 < |k * u| := abs_pos.mpr
    (mul_ne_zero (nonzero_of_not_five_dvd hk5) (nonzero_of_not_five_dvd hu5))
  have hB : 0 < |v| := abs_pos.mpr hv0
  have hcop : IsCoprime |k * u| |v| :=
    (coprime_abs_right_int (coprime_abs_right_int (hkv.mul_left huv)).symm).symm
  have hA5 : ¬ (5 : ℤ) ∣ |k * u| := by
    intro hd
    rcases Int.Prime.dvd_mul' Nat.prime_five ((dvd_abs _ _).mp hd) with hk | hu
    · exact hk5 hk
    · exact hu5 hu
  obtain ⟨H, hH⟩ := hclass
  obtain ⟨V, hV⟩ := squareclass_descend hA hB hcop hA5 (by rwa [← hcid])
  refine ⟨|v|, ?_, hB, u, d, coprime_abs_right_int huv, huodd, hu5, ⟨V, hV⟩, ?_⟩
  · have hA1 : 1 ≤ |k * u| := by omega
    nlinarith
  · rw [Even.pow_abs (by decide : Even 2), Even.pow_abs (by decide : Even 4)]
    exact heq

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_candidate {c : ℤ} (hc : QuarticCandidate c) (hceven : Even c) :
    ∃ c' : ℤ, c' < c ∧ QuarticCandidate c' := by
  obtain ⟨hcpos, a, d, hac, haodd, ha5, hclass, heq⟩ := hc
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  obtain ⟨g, f, hgf, hg5, hgf_abs, hfirst⟩ :=
    even_quartic_first hac haodd hceven hc0 ha5 heq
  have hcabs : c = |g * f| := by rw [← hgf_abs, abs_of_pos hcpos]
  rcases Int.even_or_odd f with hfeven | hfodd
  · obtain ⟨h, hf⟩ := hfeven
    have hf' : f = 2 * h := by omega
    have hgh : IsCoprime g h := by rw [hf'] at hgf; exact hgf.of_mul_right_right
    have hgodd : Odd g := by
      rcases Int.even_or_odd g with hgeven | hgodd
      · have hu := hgf.isUnit_of_dvd' hgeven.two_dvd (by rw [hf']; exact dvd_mul_right 2 h)
        norm_num [Int.isUnit_iff] at hu
      · exact hgodd
    have hh0 : h ≠ 0 := by
      intro h0
      rw [hf', h0] at hcabs
      simp at hcabs
      exact hc0 hcabs
    have hstep : a ^ 2 = g ^ 4 - 20 * g ^ 2 * h ^ 2 + 80 * h ^ 4 := by
      rw [hf'] at hfirst
      linear_combination hfirst
    obtain ⟨u, v, huv, huodd, hu5, hhabs, hnew⟩ :=
      even_quartic_step_even hgh haodd hgodd hg5 hh0 hstep
    have hgv := (coprime_of_abs_product hgh hhabs).2
    have hv0 : v ≠ 0 := by
      intro hv
      apply hh0
      have : |h| = 0 := by simpa [hv] using hhabs
      exact abs_eq_zero.mp this
    have hcid : c = 2 * |g * u| * |v| := by
      calc c = |g * f| := hcabs
        _ = 2 * |g| * |h| := by rw [hf']; simp only [abs_mul]; norm_num; ring
        _ = 2 * |g * u| * |v| := by rw [hhabs]; simp only [abs_mul]; ring
    exact package_descent hcpos hclass hcid hgv huv hg5 hu5 huodd hv0 hnew
  · have hgeven : Even g := by
      have hev : Even (g * f) := even_abs.mp (hgf_abs ▸ even_abs.mpr hceven)
      rcases Int.even_mul.mp hev with hg | hf
      · exact hg
      · exact False.elim (Int.not_even_iff_odd.mpr hfodd hf)
    obtain ⟨h, hg⟩ := hgeven
    have hg' : g = 2 * h := by omega
    have hhf : IsCoprime h f := by rw [hg'] at hgf; exact hgf.of_mul_left_right
    have hh5 : ¬ (5 : ℤ) ∣ h := by
      intro hd; apply hg5; rw [hg']; exact dvd_mul_of_dvd_right hd 2
    have hstep : a ^ 2 = 16 * h ^ 4 - 20 * h ^ 2 * f ^ 2 + 5 * f ^ 4 := by
      rw [hg'] at hfirst
      linear_combination hfirst
    obtain ⟨u, v, huv, huodd, -, hu5, hfabs, hnew⟩ :=
      even_quartic_step_odd hhf hfodd hh5 hstep
    have hhv := (coprime_of_abs_product hhf hfabs).2
    have hv0 : v ≠ 0 := by
      intro hv
      apply nonzero_of_odd hfodd
      have : |f| = 0 := by simpa [hv] using hfabs
      exact abs_eq_zero.mp this
    have hcid : c = 2 * |h * u| * |v| := by
      calc c = |g * f| := hcabs
        _ = 2 * |h| * |f| := by rw [hg']; simp only [abs_mul]; norm_num
        _ = 2 * |h * u| * |v| := by rw [hfabs]; simp only [abs_mul]; ring
    exact package_descent hcpos hclass hcid hhv huv hh5 hu5 huodd hv0 hnew

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma no_quartic_candidate_aux : ∀ n : ℕ, ∀ c : ℤ, c.natAbs = n → ¬ QuarticCandidate c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hcn hc
    rcases Int.even_or_odd c with hceven | hcodd
    · obtain ⟨c', hc'lt, hc'⟩ := even_quartic_candidate hc hceven
      have hn : c'.natAbs < n := by
        rw [← hcn, ← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_pos hc'.1, abs_of_pos hc.1]
        exact hc'lt
      exact ih _ hn c' rfl hc'
    · exact odd_quartic_candidate hc hcodd

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma no_quartic_candidate (c : ℤ) : ¬ QuarticCandidate c :=
  no_quartic_candidate_aux _ c rfl

end OblathH1

/- Component: PrimitiveFirst.lean -/

/-
First-case bridge from primitive fifth-power arithmetic progressions to Lebesgue's quartic descent.
New formalization by Hanan Beer (@hananzlt). The imported Dirichlet extraction and its
parity/coprimality patterns are reused from Pedro Bessa (@nijv), PR5575, immutable head
572ffd235e0a734035a1737d90d28c37c24417ee; full provenance is in Dirichlet.lean.
Mathematical source: V.-A. Lebesgue (1843), Théorèmes nouveaux sur l'équation indéterminée
x⁵+y⁵=az⁵, Propositions III–IV. Existing exact reduction authored by @mudkjp.
-/
namespace OblathH1
open OMA672H2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma square_of_pos_mul {A B C : ℤ} (hA : 0 < A) (hcop : IsCoprime A B)
    (heq : A * B = C ^ 2) : ∃ r : ℤ, A = r ^ 2 := by
  obtain ⟨r, hr | hr⟩ := Int.sq_of_isCoprime hcop heq
  · exact ⟨r, hr⟩
  · nlinarith [sq_nonneg r]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma quartic_fifth_impossible {u v w : ℤ} (huv : IsCoprime u v)
    (hpar : Odd (u + v)) (hu5 : ¬ (5 : ℤ) ∣ u) (hv5 : (5 : ℤ) ∣ v) (hv0 : v ≠ 0)
    (heq : u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 = w ^ 5) : False := by
  let P := u ^ 2 + 5 * v ^ 2
  let R := 2 * v ^ 2
  have hPodd : Odd P := by
    rw [odd_iff_zmod2] at hpar ⊢
    dsimp [P]
    push_cast at hpar ⊢
    revert hpar
    generalize (u : ZMod 2) = x, (v : ZMod 2) = y
    revert x y; decide
  have hPRodd : Odd (P + R) := hPodd.add_even ⟨v ^ 2, by dsimp [R]; ring⟩
  have hPv : IsCoprime P v := by
    have hr : P = u ^ 2 + v * (5 * v) := by dsimp [P]; ring
    rw [hr]
    exact huv.pow_left.add_mul_left_left _
  have hPR : IsCoprime P R :=
    (isCoprime_two_of_odd hPodd).mul_right hPv.pow_right
  have hP5 : ¬ (5 : ℤ) ∣ P := by
    intro hd
    have hu2 : (5 : ℤ) ∣ u ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - v ^ 2, by dsimp [P] at hk; linarith⟩
    exact hu5 (Int.Prime.dvd_pow' Nat.prime_five hu2)
  have hR5 : (5 : ℤ) ∣ R := by
    obtain ⟨k, hk⟩ := hv5
    exact ⟨10 * k ^ 2, by dsimp [R]; rw [hk]; ring⟩
  have hnorm : P ^ 2 - 5 * R ^ 2 = w ^ 5 := by
    dsimp [P, R]
    linear_combination heq
  obtain ⟨a, b, ha, hb⟩ := dirichlet_lemma hPR hP5 hR5 hPRodd hnorm
  have hab : IsCoprime a b := by
    have hc := hPR
    rw [ha, hb] at hc
    exact hc.of_mul_left_left.of_mul_right_left.of_mul_right_right
  have habodd : Odd (a + b) := by
    apply odd_add_of_odd_PQ5
    rw [← ha, ← hb]
    exact hPRodd
  have ha5 : ¬ (5 : ℤ) ∣ a := fun hd => hP5 (ha ▸ dvd_mul_of_dvd_left hd _)
  let T := a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4
  have hTpos : 0 < T := by
    have ha0 := nonzero_of_not_five_dvd ha5
    have ha4 : 1 ≤ a ^ 4 := by nlinarith [sq_pos_of_ne_zero ha0]
    dsimp [T]
    nlinarith [sq_nonneg (a * b), sq_nonneg (b ^ 2)]
  have hTodd : Odd T := by
    rw [odd_iff_zmod2] at habodd ⊢
    dsimp [T]
    push_cast at habodd ⊢
    revert habodd
    generalize (a : ZMod 2) = x, (b : ZMod 2) = y
    revert x y; decide
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hbpos : 0 < b := by
    have hr : R = 5 * b * T := hb
    nlinarith
  have hbEven : Even b := by
    have he : Even (5 * b * T) := ⟨v ^ 2, by dsimp [R] at hb; linarith⟩
    rw [Int.even_mul, Int.even_mul] at he
    rcases he with (h5 | hb) | hT
    · norm_num at h5
    · exact hb
    · exact False.elim (Int.not_even_iff_odd.mpr hTodd hT)
  obtain ⟨B, hB⟩ := hbEven
  have hB' : b = 2 * B := by omega
  have hBpos : 0 < B := by omega
  have hbT : IsCoprime b T := by
    have hr : T = a ^ 4 + b * (10 * a ^ 2 * b + 5 * b ^ 3) := by dsimp [T]; ring
    rw [hr]
    exact hab.symm.pow_right.add_mul_left_right _
  have hBT : IsCoprime B T := by rw [hB'] at hbT; exact hbT.of_mul_left_right
  have hT5 : ¬ (5 : ℤ) ∣ T := by
    intro hd
    have ha4 : (5 : ℤ) ∣ a ^ 4 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 2 * a ^ 2 * b ^ 2 - b ^ 4, by dsimp [T] at hk; linarith⟩
    exact ha5 (Int.Prime.dvd_pow' Nat.prime_five ha4)
  have h5BT : IsCoprime (5 * B) T := (isCoprime_five_of_not_dvd hT5).symm.mul_left hBT
  have heBT : (5 * B) * T = v ^ 2 := by
    change R = 5 * b * T at hb
    dsimp [R] at hb
    rw [hB'] at hb
    nlinarith only [hb]
  obtain ⟨r, hr⟩ := square_of_pos_mul (by positivity : 0 < 5 * B) h5BT heBT
  obtain ⟨l, hl⟩ := square_of_pos_mul hTpos h5BT.symm
    (show T * (5 * B) = v ^ 2 by rw [mul_comm]; exact heBT)
  have hr5 : (5 : ℤ) ∣ r := Int.Prime.dvd_pow' Nat.prime_five
    (show (5 : ℤ) ∣ r ^ 2 by rw [← hr]; exact dvd_mul_right 5 B)
  obtain ⟨H, hH⟩ := hr5
  have hbclass : b = 10 * H ^ 2 := by rw [hH] at hr; nlinarith only [hr, hB']
  have haodd : Odd a := by
    obtain ⟨k, hk⟩ := habodd
    exact ⟨k - B, by omega⟩
  apply no_quartic_candidate b
  exact ⟨hbpos, a, l, hab, haodd, ha5, ⟨H, Or.inr hbclass⟩, hl.symm⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_eq {x y z : ℤ} (hcop : IsCoprime x y) (hz : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : x = y := by
  by_contra hxy
  obtain ⟨hxodd, hyodd⟩ := primitive_odd_xy hcop heq
  obtain ⟨u, hu⟩ := hxodd.add_odd hyodd
  let v := x - u
  have hx : x = u + v := by dsimp [v]; omega
  have hy : y = u - v := by dsimp [v]; omega
  have huv : IsCoprime u v := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx, hy]; ring⟩
  have hpar : Odd (u + v) := hx ▸ hxodd
  have hv5 : (5 : ℤ) ∣ v := by
    have hsub := primitive_five_dvd_sub hcop hz heq
    have h2v : (5 : ℤ) ∣ 2 * v := by
      convert hsub using 1
      rw [hx, hy]; ring
    rcases Int.Prime.dvd_mul' Nat.prime_five h2v with h2 | hv
    · norm_num at h2
    · exact hv
  have hu5 : ¬ (5 : ℤ) ∣ u := by
    intro hd
    exact not_isUnit_five (huv.isUnit_of_dvd' hd hv5)
  have hv0 : v ≠ 0 := by intro hv; apply hxy; omega
  let Q := u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4
  have hprod : u * Q = z ^ 5 := by
    have h2 : 2 * (u * Q) = 2 * z ^ 5 := by
      rw [hx, hy] at heq
      dsimp [Q]
      linear_combination heq
    omega
  have huQ : IsCoprime u Q := by
    have hu5cop := isCoprime_five_of_not_dvd hu5
    have hc : IsCoprime u (5 * v ^ 4) := hu5cop.mul_right huv.pow_right
    have hr : Q = 5 * v ^ 4 + u * (u ^ 3 + 10 * u * v ^ 2) := by dsimp [Q]; ring
    rw [hr]
    exact hc.add_mul_left_right _
  obtain ⟨w, hw⟩ := pow5_of_coprime_int huQ.symm
    (show Q * u = z ^ 5 by rw [mul_comm]; exact hprod)
  exact quartic_fifth_impossible huv hpar hu5 hv5 hv0 hw

end OblathH1

/- Component: Main.lean -/

/-
Exact H1 of the Oblath reduction for Erdős672: integer fifth powers in arithmetic progression.
New formalization and integration by Hanan Beer (@hananzlt), following the classical
Dirichlet–Lebesgue proof. Mathematical source: V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵.
The golden-integer and Dirichlet helper proof is reused from Pedro Bessa (@nijv), PR5575,
immutable head572ffd235e0a734035a1737d90d28c37c24417ee. Full attribution is in Dirichlet.lean.
The exact H1 reduction is due to @mudkjp, PR3625.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma all_int_aux : ∀ n : ℕ, ∀ x y z : ℤ, z.natAbs = n →
    x ^ 5 + y ^ 5 = 2 * z ^ 5 → x = y ∨ z = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y z hzn heq
    by_cases hz : z = 0
    · exact Or.inr hz
    by_cases hcop : IsCoprime x y
    · exact Or.inl (primitive_eq hcop hz heq)
    have hnc : ¬ Nat.Coprime x.natAbs y.natAbs :=
      fun h => hcop (Int.isCoprime_iff_nat_coprime.mpr h)
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    obtain ⟨X, hX⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨Y, hY⟩ := Int.natCast_dvd.mpr hpy
    have heq' : (p : ℤ) ^ 5 * (X ^ 5 + Y ^ 5) = 2 * z ^ 5 := by
      rw [hX, hY] at heq
      linear_combination heq
    have hpz : (p : ℤ) ∣ z := by
      by_cases hp2 : p = 2
      · subst p
        have hz5 : (2 : ℤ) ∣ z ^ 5 := by
          refine ⟨8 * (X ^ 5 + Y ^ 5), ?_⟩
          norm_num at heq'
          nlinarith only [heq']
        exact Int.Prime.dvd_pow' Nat.prime_two hz5
      · have hpProd : (p : ℤ) ∣ 2 * z ^ 5 := by
          rw [← heq']
          exact dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by decide : 5 ≠ 0)) _
        rcases Int.Prime.dvd_mul' hp hpProd with hp2dvd | hpz5
        · have hp2Nat : p ∣ 2 := by exact_mod_cast hp2dvd
          have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hp2Nat
          have hpge := hp.two_le
          exact False.elim (hp2 (by omega))
        · exact Int.Prime.dvd_pow' hp hpz5
    obtain ⟨Z, hZ⟩ := hpz
    have hZ0 : Z ≠ 0 := by intro h0; apply hz; simp [hZ, h0]
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have heq_small : X ^ 5 + Y ^ 5 = 2 * Z ^ 5 := by
      apply mul_left_cancel₀ (pow_ne_zero 5 hp0)
      rw [heq', hZ]
      ring
    have hlt : Z.natAbs < n := by
      rw [← hzn, hZ, Int.natAbs_mul, Int.natAbs_natCast]
      have hZpos := Int.natAbs_pos.mpr hZ0
      nlinarith [hp.two_le]
    rcases ih _ hlt X Y Z rfl heq_small with hXY | hZzero
    · exact Or.inl (by rw [hX, hY, hXY])
    · exact False.elim (hZ0 hZzero)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma all_int (x y z : ℤ) (h : x ^ 5 + y ^ 5 = 2 * z ^ 5) : x = y ∨ z = 0 :=
  all_int_aux _ x y z rfl h

end OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1.H1 := by
  intro x y z h
  exact OblathH1.all_int x y z h

