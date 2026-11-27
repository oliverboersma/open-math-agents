import OMAReductions.R_OeisA287616_conjecture_R1

/-!
Primitive seeds for A287616 via the mate form. The two explicit integral
transfers are from Cao, Guo, Qiu, Feng and Gao, arXiv:2606.26035, Section 3.3.
The hypotheses are primitive representation by one of the two genus classes
and escape from the exceptional residue class of the mate.
-/

namespace OMA.R_OeisA287616_conjecture_R1_H1_R1

def H1 : Prop :=
  ∀ n : ℕ,
    (∃ u v w : ℤ,
      15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23 ∧
        Int.gcd u (Int.gcd v w) = 1) ∨
    (∃ x y z : ℤ,
      2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = 120 * (n : ℤ) + 23 ∧
        Int.gcd x (Int.gcd y z) = 1)

def H2 : Prop :=
  ∀ (n : ℕ) (x y z : ℤ),
    2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = 120 * (n : ℤ) + 23 →
    Int.gcd x (Int.gcd y z) = 1 →
    (3 : ℤ) ∣ y → (3 : ℤ) ∣ z →
    ∃ x' y' z' : ℤ,
      2 * x' ^ 2 - 2 * x' * y' + 8 * y' ^ 2 + 15 * z' ^ 2 = 120 * (n : ℤ) + 23 ∧
        Int.gcd x' (Int.gcd y' z') = 1 ∧ ¬ ((3 : ℤ) ∣ y' ∧ (3 : ℤ) ∣ z')

theorem mate_not_dvd_add {n : ℕ} {x y z : ℤ}
    (h : 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = 120 * (n : ℤ) + 23) :
    ¬ (3 : ℤ) ∣ x + y := by
  rintro ⟨k, hk⟩
  have hnorm : 2 * (120 * (n : ℤ) + 23) =
      (x + y) ^ 2 + 3 * ((x - y) ^ 2 + 4 * y ^ 2 + 10 * z ^ 2) := by
    rw [← h]
    ring
  rw [hk] at hnorm
  have hdiv : (3 : ℤ) ∣ 2 * (120 * (n : ℤ) + 23) :=
    ⟨3 * k ^ 2 + (x - y) ^ 2 + 4 * y ^ 2 + 10 * z ^ 2, by rw [hnorm]; ring⟩
  omega

theorem primitive_of_inverse {x y z u v w : ℤ}
    (hprim : Int.gcd x (Int.gcd y z) = 1)
    (hnot : ¬ ((3 : ℤ) ∣ u ∧ (3 : ℤ) ∣ v ∧ (3 : ℤ) ∣ w))
    (hinverse : ∀ d : ℤ, d ∣ u → d ∣ v → d ∣ w → d ∣ 3 * x ∧ d ∣ 3 * y ∧ d ∣ 3 * z) :
    Int.gcd u (Int.gcd v w) = 1 := by
  let d := Int.gcd u (Int.gcd v w)
  have hu : (d : ℤ) ∣ u := Int.gcd_dvd_left _ _
  have hvw : (d : ℤ) ∣ (Int.gcd v w : ℤ) := Int.gcd_dvd_right _ _
  have hv : (d : ℤ) ∣ v := dvd_trans hvw (Int.gcd_dvd_left _ _)
  have hw : (d : ℤ) ∣ w := dvd_trans hvw (Int.gcd_dvd_right _ _)
  obtain ⟨hx, hy, hz⟩ := hinverse d hu hv hw
  have hd := Int.dvd_gcd hx (Int.dvd_coe_gcd hy hz)
  rw [Int.gcd_mul_left] at hd
  change d ∣ Int.gcd (3 * x) ((3 * Int.gcd y z : ℕ) : ℤ) at hd
  rw [Int.natCast_mul] at hd
  change d ∣ Int.gcd (3 * x) (3 * (Int.gcd y z : ℤ)) at hd
  rw [Int.gcd_mul_left, hprim] at hd
  have hd3 : d ∣ 3 := by simpa using hd
  change d = 1
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd3 with hone | hthree
  · exact hone
  · rw [hthree] at hu hv hw
    exact (hnot ⟨hu, hv, hw⟩).elim

private theorem norm_not_dvd_middle {n : ℕ} {u v w : ℤ}
    (h : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23) :
    ¬ (3 : ℤ) ∣ v := by
  rintro ⟨k, rfl⟩
  have hdiv : (3 : ℤ) ∣ 120 * (n : ℤ) + 23 :=
    ⟨5 * u ^ 2 + 15 * k ^ 2 + w ^ 2, by rw [← h]; ring⟩
  omega

private theorem transfer_first {n : ℕ} {x y z : ℤ}
    (h : 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = 120 * (n : ℤ) + 23)
    (hprim : Int.gcd x (Int.gcd y z) = 1)
    (hdiv : (3 : ℤ) ∣ x + z) :
    ∃ u v w : ℤ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23 ∧
      Int.gcd u (Int.gcd v w) = 1 := by
  obtain ⟨s, hs⟩ := hdiv
  have hx : x = 3 * s - z := by omega
  let u := -s
  let v := -y + z
  let w := s - 2 * z - y
  have hnorm : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23 := by
    rw [← h, hx]
    dsimp [u, v, w]
    ring
  refine ⟨u, v, w, hnorm, primitive_of_inverse hprim
    (fun hthree => norm_not_dvd_middle hnorm hthree.2.1) ?_⟩
  have hix : 3 * x = -8 * u - v + w := by dsimp [u, v, w]; omega
  have hiy : 3 * y = -u - 2 * v - w := by dsimp [u, v, w]; omega
  have hiz : 3 * z = -u + v - w := by dsimp [u, v, w]; omega
  rintro d ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  refine ⟨⟨-8 * a - b + c, ?_⟩, ⟨-a - 2 * b - c, ?_⟩, ⟨-a + b - c, ?_⟩⟩
  · rw [hix, ha, hb, hc]; ring
  · rw [hiy, ha, hb, hc]; ring
  · rw [hiz, ha, hb, hc]; ring

private theorem transfer_second {n : ℕ} {x y z : ℤ}
    (h : 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = 120 * (n : ℤ) + 23)
    (hprim : Int.gcd x (Int.gcd y z) = 1)
    (hdiv : (3 : ℤ) ∣ x - y - z) :
    ∃ u v w : ℤ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23 ∧
      Int.gcd u (Int.gcd v w) = 1 := by
  obtain ⟨s, hs⟩ := hdiv
  have hx : x = 3 * s + y + z := by omega
  let u := s
  let v := y - z
  let w := s + y + 2 * z
  have hnorm : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23 := by
    rw [← h, hx]
    dsimp [u, v, w]
    ring
  refine ⟨u, v, w, hnorm, primitive_of_inverse hprim
    (fun hthree => norm_not_dvd_middle hnorm hthree.2.1) ?_⟩
  have hix : 3 * x = 7 * u + v + 2 * w := by dsimp [u, v, w]; omega
  have hiy : 3 * y = w - u + 2 * v := by dsimp [u, v, w]; omega
  have hiz : 3 * z = w - u - v := by dsimp [u, v, w]; omega
  rintro d ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  refine ⟨⟨7 * a + b + 2 * c, ?_⟩, ⟨c - a + 2 * b, ?_⟩, ⟨c - a - b, ?_⟩⟩
  · rw [hix, ha, hb, hc]; ring
  · rw [hiy, ha, hb, hc]; ring
  · rw [hiz, ha, hb, hc]; ring

private theorem transfer_mate {n : ℕ} {x y z : ℤ}
    (h : 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = 120 * (n : ℤ) + 23)
    (hprim : Int.gcd x (Int.gcd y z) = 1)
    (hgood : ¬ ((3 : ℤ) ∣ y ∧ (3 : ℤ) ∣ z)) :
    ∃ u v w : ℤ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23 ∧
      Int.gcd u (Int.gcd v w) = 1 := by
  have hxy := mate_not_dvd_add h
  have hchoice : ((3 : ℤ) ∣ x + z) ∨ ((3 : ℤ) ∣ x + -z) ∨
      ((3 : ℤ) ∣ x - y - z) ∨ ((3 : ℤ) ∣ x - y - -z) := by
    have rx : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    have ry : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    have rz : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
    rcases rx with hx | hx | hx <;> rcases ry with hy | hy | hy <;>
      rcases rz with hz | hz | hz <;> omega
  have hneg : 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * (-z) ^ 2 =
      120 * (n : ℤ) + 23 := by simpa only [neg_sq] using h
  have hpneg : Int.gcd x (Int.gcd y (-z)) = 1 := by simpa only [Int.gcd_neg] using hprim
  rcases hchoice with hfirst | hfirstneg | hsecond | hsecondneg
  · exact transfer_first h hprim hfirst
  · exact transfer_first hneg hpneg hfirstneg
  · exact transfer_second h hprim hsecond
  · exact transfer_second hneg hpneg hsecondneg

theorem main : H1 → H2 → OMA.R_OeisA287616_conjecture_R1.H1 := by
  intro hgenus hescape n
  have hint : ∃ u v w : ℤ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * (n : ℤ) + 23 ∧
      Int.gcd u (Int.gcd v w) = 1 := by
    rcases hgenus n with hdiag | hmate
    · exact hdiag
    · obtain ⟨x, y, z, hnorm, hprim⟩ := hmate
      by_cases hbad : (3 : ℤ) ∣ y ∧ (3 : ℤ) ∣ z
      · obtain ⟨x', y', z', hnorm', hprim', hgood⟩ := hescape n x y z hnorm hprim hbad.1 hbad.2
        exact transfer_mate hnorm' hprim' hgood
      · exact transfer_mate hnorm hprim hbad
  obtain ⟨u, v, w, hnorm, hprim⟩ := hint
  refine ⟨u.natAbs, v.natAbs, w.natAbs, ?_, ?_⟩
  · have habs (a : ℤ) : (a.natAbs : ℤ) ^ 2 = a ^ 2 := by simp
    have hnat : 15 * (u.natAbs : ℤ) ^ 2 + 5 * (v.natAbs : ℤ) ^ 2 +
        3 * (w.natAbs : ℤ) ^ 2 = 120 * (n : ℤ) + 23 := by
      simpa only [habs] using hnorm
    exact_mod_cast hnat
  · simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] using hprim

end OMA.R_OeisA287616_conjecture_R1_H1_R1
