import OMAReductions.R_OeisA287616_conjecture_R1_H1_R1

-- Step OeisA287616.conjecture.R1.H1.R1.H2: hypothesis H2 of reduction OeisA287616.conjecture.R1.H1.R1

/-!
Twice the form is `(2x - y)^2 + 15 (y^2 + 2 z^2)`. Multiplying `y + z √-2` by one of the norm-one
numbers `(1 ± 2 √-2) / 3` keeps `2x - y` and `y^2 + 2 z^2`, hence the represented number. Write
`y = 3^k y0`, `z = 3^k z0` with `y0, z0` not both divisible by `3`. One of the two maps sends
`(y, z)` to `3^(k-1) (y0', z0')` with `y0', z0'` again not both divisible by `3`, so induction
on `k` ends at a representation with `y, z` not both divisible by `3`. Primitivity is kept: a
common prime factor of the new triple is not `3` (the represented number is `2 mod 3`), and then
it divides the old triple because `3x, 3y, 3z` are integer combinations of the new one.
-/

namespace OMA

theorem gcd_one_of (x y z : ℤ)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → (p : ℤ) ∣ y → (p : ℤ) ∣ z → False) :
    Int.gcd x (Int.gcd y z) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpd2 : (p : ℤ) ∣ (Int.gcd x (Int.gcd y z) : ℤ) := Int.natCast_dvd_natCast.2 hpd
  have h1 : (p : ℤ) ∣ x := hpd2.trans (Int.gcd_dvd_left _ _)
  have h2 : (p : ℤ) ∣ (Int.gcd y z : ℤ) := hpd2.trans (Int.gcd_dvd_right _ _)
  exact h p hp h1 (h2.trans (Int.gcd_dvd_left _ _)) (h2.trans (Int.gcd_dvd_right _ _))

theorem step (N x y z x1 y1 z1 a1 b1 a2 b2 b3 c3 : ℤ) (hN3 : ¬ (3 : ℤ) ∣ N)
    (hg1 : 2 * x1 ^ 2 - 2 * x1 * y1 + 8 * y1 ^ 2 + 15 * z1 ^ 2 = N)
    (h1 : 3 * y = a1 * y1 + b1 * z1) (h2 : 3 * z = a2 * y1 + b2 * z1)
    (h3 : 3 * x = 3 * x1 + b3 * y1 + c3 * z1)
    (hgcd : Int.gcd x (Int.gcd y z) = 1) : Int.gcd x1 (Int.gcd y1 z1) = 1 := by
  apply OMA.gcd_one_of
  intro p hp hx1 hy1 hz1
  have hp3 : p ≠ 3 := by
    rintro rfl
    apply hN3
    have hx3 : (3 : ℤ) ∣ x1 := by exact_mod_cast hx1
    have hy3 : (3 : ℤ) ∣ y1 := by exact_mod_cast hy1
    have hz3 : (3 : ℤ) ∣ z1 := by exact_mod_cast hz1
    have e : 2 * x1 ^ 2 - 2 * x1 * y1 + 8 * y1 ^ 2 + 15 * z1 ^ 2 =
        x1 * (2 * x1 - 2 * y1) + y1 * (8 * y1) + z1 * (15 * z1) := by ring
    rw [← hg1, e]
    exact dvd_add (dvd_add (Dvd.dvd.mul_right hx3 _) (Dvd.dvd.mul_right hy3 _))
      (Dvd.dvd.mul_right hz3 _)
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hnot3 : ¬ (p : ℤ) ∣ 3 := by
    intro hd
    have hd2 : p ∣ 3 := by exact_mod_cast hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd2)
  have hy : (p : ℤ) ∣ y := by
    have hd : (p : ℤ) ∣ 3 * y := by
      rw [h1]
      exact dvd_add (Dvd.dvd.mul_left hy1 _) (Dvd.dvd.mul_left hz1 _)
    exact (hpp.dvd_or_dvd hd).resolve_left hnot3
  have hz : (p : ℤ) ∣ z := by
    have hd : (p : ℤ) ∣ 3 * z := by
      rw [h2]
      exact dvd_add (Dvd.dvd.mul_left hy1 _) (Dvd.dvd.mul_left hz1 _)
    exact (hpp.dvd_or_dvd hd).resolve_left hnot3
  have hx : (p : ℤ) ∣ x := by
    have hd : (p : ℤ) ∣ 3 * x := by
      rw [h3]
      exact dvd_add (dvd_add (Dvd.dvd.mul_left hx1 _) (Dvd.dvd.mul_left hy1 _))
        (Dvd.dvd.mul_left hz1 _)
    exact (hpp.dvd_or_dvd hd).resolve_left hnot3
  have hd : (p : ℤ) ∣ (Int.gcd x (Int.gcd y z) : ℤ) := Int.dvd_coe_gcd hx (Int.dvd_coe_gcd hy hz)
  rw [hgcd] at hd
  have hd2 : p ∣ 1 := by exact_mod_cast hd
  exact hp.one_lt.ne' (Nat.dvd_one.1 hd2)

theorem main (N : ℤ) (hN3 : ¬ (3 : ℤ) ∣ N) : ∀ (k : ℕ) (x y0 z0 : ℤ),
    2 * x ^ 2 - 2 * x * (3 ^ k * y0) + 8 * (3 ^ k * y0) ^ 2 + 15 * (3 ^ k * z0) ^ 2 = N →
    Int.gcd x (Int.gcd (3 ^ k * y0) (3 ^ k * z0)) = 1 → ¬ ((3 : ℤ) ∣ y0 ∧ (3 : ℤ) ∣ z0) →
    ∃ x' y' z' : ℤ, 2 * x' ^ 2 - 2 * x' * y' + 8 * y' ^ 2 + 15 * z' ^ 2 = N ∧
      Int.gcd x' (Int.gcd y' z') = 1 ∧ ¬ ((3 : ℤ) ∣ y' ∧ (3 : ℤ) ∣ z') := by
  intro k
  induction k with
  | zero =>
    intro x y0 z0 hg hgcd hnd
    refine ⟨x, y0, z0, ?_, ?_, hnd⟩
    · simpa using hg
    · simpa using hgcd
  | succ k ih =>
    intro x y0 z0 hg hgcd hnd
    by_cases hc : (3 : ℤ) ∣ y0 - z0
    · have hg1 : 2 * (x - 3 ^ k * (y0 - 2 * z0)) ^ 2 -
          2 * (x - 3 ^ k * (y0 - 2 * z0)) * (3 ^ k * (y0 + 4 * z0)) +
          8 * (3 ^ k * (y0 + 4 * z0)) ^ 2 + 15 * (3 ^ k * (-2 * y0 + z0)) ^ 2 = N := by
        rw [← hg]
        ring
      refine ih (x - 3 ^ k * (y0 - 2 * z0)) (y0 + 4 * z0) (-2 * y0 + z0) hg1 ?_ ?_
      · exact OMA.step N x (3 ^ (k + 1) * y0) (3 ^ (k + 1) * z0) _ _ _ 1 (-4) 2 1 (-1) (-2)
          hN3 hg1 (by ring) (by ring) (by ring) hgcd
      · rintro ⟨h1, h2⟩
        apply hnd
        constructor <;> omega
    · have hg1 : 2 * (x - 3 ^ k * (y0 + 2 * z0)) ^ 2 -
          2 * (x - 3 ^ k * (y0 + 2 * z0)) * (3 ^ k * (y0 - 4 * z0)) +
          8 * (3 ^ k * (y0 - 4 * z0)) ^ 2 + 15 * (3 ^ k * (2 * y0 + z0)) ^ 2 = N := by
        rw [← hg]
        ring
      refine ih (x - 3 ^ k * (y0 + 2 * z0)) (y0 - 4 * z0) (2 * y0 + z0) hg1 ?_ ?_
      · exact OMA.step N x (3 ^ (k + 1) * y0) (3 ^ (k + 1) * z0) _ _ _ 1 4 (-2) 1 (-1) 2
          hN3 hg1 (by ring) (by ring) (by ring) hgcd
      · rintro ⟨h1, h2⟩
        apply hc
        omega

theorem decomp : ∀ (m : ℕ) (y z : ℤ), y.natAbs + z.natAbs = m → (y ≠ 0 ∨ z ≠ 0) →
    ∃ (k : ℕ) (y0 z0 : ℤ), y = 3 ^ k * y0 ∧ z = 3 ^ k * z0 ∧ ¬ ((3 : ℤ) ∣ y0 ∧ (3 : ℤ) ∣ z0) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y z hm hne
    by_cases hd : (3 : ℤ) ∣ y ∧ (3 : ℤ) ∣ z
    · obtain ⟨⟨Y, rfl⟩, ⟨Z, rfl⟩⟩ := hd
      have hne2 : Y ≠ 0 ∨ Z ≠ 0 := by omega
      have hlt : Y.natAbs + Z.natAbs < m := by omega
      obtain ⟨k, y0, z0, hy, hz, hnd⟩ := ih _ hlt Y Z rfl hne2
      refine ⟨k + 1, y0, z0, ?_, ?_, hnd⟩
      · rw [hy]
        ring
      · rw [hz]
        ring
    · exact ⟨0, y, z, by simp, by simp, hd⟩

end OMA

theorem OMA.solution : OMA.R_OeisA287616_conjecture_R1_H1_R1.H2 := by
  unfold OMA.R_OeisA287616_conjecture_R1_H1_R1.H2
  intro n x y z hg hgcd _ _
  have hN3 : ¬ (3 : ℤ) ∣ 120 * (n : ℤ) + 23 := by omega
  have hne : y ≠ 0 ∨ z ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨hy0, hz0⟩ := hcon
    rw [hy0, hz0] at hg
    have h2 : 2 * x ^ 2 = 120 * (n : ℤ) + 23 := by
      rw [← hg]
      ring
    generalize x ^ 2 = t at h2
    omega
  obtain ⟨k, y0, z0, hy, hz, hnd⟩ := OMA.decomp _ y z rfl hne
  rw [hy, hz] at hg hgcd
  exact OMA.main (120 * (n : ℤ) + 23) hN3 k x y0 z0 hg hgcd hnd
