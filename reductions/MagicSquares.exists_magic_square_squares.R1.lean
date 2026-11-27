import FormalConjectures.Wikipedia.MagicSquares

-- Reduction MagicSquares.exists_magic_square_squares.R1 of Magic Squares - exists magic square squares
-- Credit: @mvanhorn
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_MagicSquares_exists_magic_square_squares_R1

-- Bremner (1999, Acta Arithmetica 88): infinitely many rational parameter pairs (s, t)
-- produce a normalized 3x3 Lucas magic square with 7 square entries (center 1, 1 +- a(s),
-- 1 +- a(t), and 1 +- (a(s) + a(t)), where a(r) = 4 r (1 - r^2) / (1 + r^2)^2).
def H1 : Prop :=
  { p : ℚ × ℚ |
    let a := 4 * p.1 * (1 - p.1 ^ 2) / (1 + p.1 ^ 2) ^ 2
    let b := 4 * p.2 * (1 - p.2 ^ 2) / (1 + p.2 ^ 2) ^ 2
    0 < a ∧ a < b ∧ b ≠ 2 * a ∧ a + b < 1 ∧
    IsSquare (1 - (a + b)) ∧ IsSquare (1 + (a + b)) }.Infinite

-- Open frontier: among the infinite Bremner 7-square rational locus, some parameter pair
-- also makes the final conjugate pair 1 - (b - a) and 1 + (b - a) rational squares.
def H2 : Prop :=
  { p : ℚ × ℚ |
    let a := 4 * p.1 * (1 - p.1 ^ 2) / (1 + p.1 ^ 2) ^ 2
    let b := 4 * p.2 * (1 - p.2 ^ 2) / (1 + p.2 ^ 2) ^ 2
    0 < a ∧ a < b ∧ b ≠ 2 * a ∧ a + b < 1 ∧
    IsSquare (1 - (a + b)) ∧ IsSquare (1 + (a + b)) }.Infinite →
  ∃ p : ℚ × ℚ,
    let a := 4 * p.1 * (1 - p.1 ^ 2) / (1 + p.1 ^ 2) ^ 2
    let b := 4 * p.2 * (1 - p.2 ^ 2) / (1 + p.2 ^ 2) ^ 2
    0 < a ∧ a < b ∧ b ≠ 2 * a ∧ a + b < 1 ∧
    IsSquare (1 - (a + b)) ∧ IsSquare (1 + (a + b)) ∧
    IsSquare (1 - (b - a)) ∧ IsSquare (1 + (b - a))

section Proof

private lemma bremner_one_sub_isSquare (r : ℚ) :
    IsSquare (1 - 4 * r * (1 - r ^ 2) / (1 + r ^ 2) ^ 2) := by
  refine ⟨(1 - 2 * r - r ^ 2) / (1 + r ^ 2), ?_⟩
  have hpos : (1 + r ^ 2 : ℚ) ≠ 0 := by positivity
  field_simp
  ring

private lemma bremner_one_add_isSquare (r : ℚ) :
    IsSquare (1 + 4 * r * (1 - r ^ 2) / (1 + r ^ 2) ^ 2) := by
  refine ⟨(1 + 2 * r - r ^ 2) / (1 + r ^ 2), ?_⟩
  have hpos : (1 + r ^ 2 : ℚ) ≠ 0 := by positivity
  field_simp
  ring

private lemma clear_rat_mul (q : ℚ) (D : ℕ) (hd : q.den ∣ D) :
    ∃ z : ℤ, (D : ℚ) * q = (z : ℚ) := by
  obtain ⟨k, hk⟩ := hd
  refine ⟨(k : ℤ) * q.num, ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  calc (D : ℚ) * q = ((q.den * k : ℕ) : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by
        rw [hk, Rat.num_div_den]
    _ = ((q.den : ℚ) * (k : ℚ)) * ((q.num : ℚ) / (q.den : ℚ)) := by rw [Nat.cast_mul]
    _ = (k : ℚ) * (q.num : ℚ) := by field_simp
    _ = (((k : ℤ) * q.num : ℤ) : ℚ) := by push_cast; rfl

private lemma clear_rat_pos_mul_sq (q : ℚ) (hq : 0 < q) (D : ℕ) (hD : 0 < D) (hd : q.den ∣ D) :
    ∃ n : ℕ, (n : ℚ) = (D : ℚ) ^ 2 * q := by
  obtain ⟨z, hz⟩ := clear_rat_mul q D hd
  have hpos : (0 : ℚ) < (D : ℚ) * (z : ℚ) := by
    have : (D : ℚ) * (z : ℚ) = (D : ℚ) ^ 2 * q := by rw [← hz]; ring
    rw [this]; positivity
  have hzn : (0 : ℤ) < (D : ℤ) * z := by exact_mod_cast hpos
  refine ⟨((D : ℤ) * z).toNat, ?_⟩
  have h1 : ((((D : ℤ) * z).toNat : ℕ) : ℤ) = (D : ℤ) * z := Int.toNat_of_nonneg (le_of_lt hzn)
  calc ((((D : ℤ) * z).toNat : ℕ) : ℚ)
      = (((((D : ℤ) * z).toNat : ℕ) : ℤ) : ℚ) := by rw [Int.cast_natCast]
    _ = (((D : ℤ) * z : ℤ) : ℚ) := by rw [h1]
    _ = (D : ℚ) * (z : ℚ) := by push_cast; rfl
    _ = (D : ℚ) ^ 2 * q := by rw [← hz]; ring

private lemma clear_rat_sq_to_nat (q : ℚ) (D : ℕ) (hd : q.den ∣ D) (n : ℕ)
    (hn : (n : ℚ) = (D : ℚ) ^ 2 * (q * q)) : IsSquare n := by
  obtain ⟨z, hz⟩ := clear_rat_mul q D hd
  refine ⟨z.natAbs, ?_⟩
  have h3 : ((z.natAbs : ℕ) : ℤ) ^ 2 = z ^ 2 := Int.natAbs_sq z
  have h2 : ((z.natAbs : ℕ) : ℚ) ^ 2 = (z : ℚ) ^ 2 := by
    have h4 : ((((z.natAbs : ℕ) : ℤ) ^ 2 : ℤ) : ℚ) = ((z ^ 2 : ℤ) : ℚ) := congrArg Int.cast h3
    simpa using h4
  have hq : (n : ℚ) = ((z.natAbs * z.natAbs : ℕ) : ℚ) := by
    rw [hn]
    calc (D : ℚ) ^ 2 * (q * q) = ((D : ℚ) * q) ^ 2 := by ring
      _ = (z : ℚ) ^ 2 := by rw [hz]
      _ = ((z.natAbs : ℕ) : ℚ) ^ 2 := h2.symm
      _ = ((z.natAbs * z.natAbs : ℕ) : ℚ) := by push_cast; ring
  exact_mod_cast hq

private lemma exists_common_den_10 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 : ℕ)
    (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3) (h4 : 0 < n4) (h5 : 0 < n5)
    (h6 : 0 < n6) (h7 : 0 < n7) (h8 : 0 < n8) (h9 : 0 < n9) (h10 : 0 < n10) :
    ∃ D : ℕ, 0 < D ∧
      n1 ∣ D ∧ n2 ∣ D ∧ n3 ∣ D ∧ n4 ∣ D ∧ n5 ∣ D ∧
      n6 ∣ D ∧ n7 ∣ D ∧ n8 ∣ D ∧ n9 ∣ D ∧ n10 ∣ D := by
  refine ⟨n1 * n2 * n3 * n4 * n5 * n6 * n7 * n8 * n9 * n10, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_right n1 n2) _) _) _) _) _) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_left n2 n1) _) _) _) _) _) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _) _) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_left _ _) _) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact dvd_mul_left _ _

private lemma lucas_magic_square_of_nat (c u v : ℕ)
    (hu : 0 < u) (huv : u < v) (hne2 : v ≠ 2 * u) (hsum : u + v < c ^ 2)
    (h1 : IsSquare (c ^ 2 - u)) (h2 : IsSquare (c ^ 2 + u))
    (h3 : IsSquare (c ^ 2 - v)) (h4 : IsSquare (c ^ 2 + v))
    (h5 : IsSquare (c ^ 2 - (u + v))) (h6 : IsSquare (c ^ 2 + (u + v)))
    (h7 : IsSquare (c ^ 2 - (v - u))) (h8 : IsSquare (c ^ 2 + (v - u))) :
    ∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
      m.Injective2 ∧
      (∀ i j, 0 < m i j ∧ IsSquare (m i j)) ∧
      (∀ i, ∑ j, m i j = t) ∧
      (∀ j, ∑ i, m i j = t) ∧
      m 0 0 + m 1 1 + m 2 2 = t ∧
      m 0 2 + m 1 1 + m 2 0 = t := by
  let m : Fin 3 → Fin 3 → ℕ := fun i j =>
    if i.val = 0 then
      if j.val = 0 then c ^ 2 + u else if j.val = 1 then c ^ 2 - (u + v) else c ^ 2 + v
    else if i.val = 1 then
      if j.val = 0 then c ^ 2 + (v - u) else if j.val = 1 then c ^ 2 else c ^ 2 - (v - u)
    else
      if j.val = 0 then c ^ 2 - v else if j.val = 1 then c ^ 2 + (u + v) else c ^ 2 - u
  refine ⟨m, 3 * c ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i1 j1 i2 j2 hij
    rcases i1 with ⟨a1, ha1⟩; rcases j1 with ⟨b1, hb1⟩
    rcases i2 with ⟨a2, ha2⟩; rcases j2 with ⟨b2, hb2⟩
    interval_cases a1 <;> interval_cases b1 <;> interval_cases a2 <;> interval_cases b2 <;>
      simp [m] at hij <;> first | exact ⟨rfl, rfl⟩ | omega
  · intro i j
    rcases i with ⟨a, ha⟩; rcases j with ⟨b, hb⟩
    interval_cases a <;> interval_cases b
    · change 0 < c ^ 2 + u ∧ IsSquare (c ^ 2 + u); exact ⟨by omega, h2⟩
    · change 0 < c ^ 2 - (u + v) ∧ IsSquare (c ^ 2 - (u + v)); exact ⟨by omega, h5⟩
    · change 0 < c ^ 2 + v ∧ IsSquare (c ^ 2 + v); exact ⟨by omega, h4⟩
    · change 0 < c ^ 2 + (v - u) ∧ IsSquare (c ^ 2 + (v - u)); exact ⟨by omega, h8⟩
    · change 0 < c ^ 2 ∧ IsSquare (c ^ 2); exact ⟨by omega, ⟨c, by ring⟩⟩
    · change 0 < c ^ 2 - (v - u) ∧ IsSquare (c ^ 2 - (v - u)); exact ⟨by omega, h7⟩
    · change 0 < c ^ 2 - v ∧ IsSquare (c ^ 2 - v); exact ⟨by omega, h3⟩
    · change 0 < c ^ 2 + (u + v) ∧ IsSquare (c ^ 2 + (u + v)); exact ⟨by omega, h6⟩
    · change 0 < c ^ 2 - u ∧ IsSquare (c ^ 2 - u); exact ⟨by omega, h1⟩
  · intro i
    rcases i with ⟨a, ha⟩
    rw [Fin.sum_univ_three]
    interval_cases a
    · change (c ^ 2 + u) + (c ^ 2 - (u + v)) + (c ^ 2 + v) = 3 * c ^ 2; omega
    · change (c ^ 2 + (v - u)) + c ^ 2 + (c ^ 2 - (v - u)) = 3 * c ^ 2; omega
    · change (c ^ 2 - v) + (c ^ 2 + (u + v)) + (c ^ 2 - u) = 3 * c ^ 2; omega
  · intro j
    rcases j with ⟨b, hb⟩
    rw [Fin.sum_univ_three]
    interval_cases b
    · change (c ^ 2 + u) + (c ^ 2 + (v - u)) + (c ^ 2 - v) = 3 * c ^ 2; omega
    · change (c ^ 2 - (u + v)) + c ^ 2 + (c ^ 2 + (u + v)) = 3 * c ^ 2; omega
    · change (c ^ 2 + v) + (c ^ 2 - (v - u)) + (c ^ 2 - u) = 3 * c ^ 2; omega
  · change (c ^ 2 + u) + c ^ 2 + (c ^ 2 - u) = 3 * c ^ 2; omega
  · change (c ^ 2 + v) + c ^ 2 + (c ^ 2 - v) = 3 * c ^ 2; omega

private lemma rat_magic_square_to_nat (a b : ℚ)
    (ha_pos : 0 < a) (hab : a < b) (hne2 : b ≠ 2 * a) (hsum_lt : a + b < 1)
    (h1m_a : IsSquare (1 - a)) (h1p_a : IsSquare (1 + a))
    (h1m_b : IsSquare (1 - b)) (h1p_b : IsSquare (1 + b))
    (h1m_ab : IsSquare (1 - (a + b))) (h1p_ab : IsSquare (1 + (a + b)))
    (h1m_ba : IsSquare (1 - (b - a))) (h1p_ba : IsSquare (1 + (b - a))) :
    ∃ m : Fin 3 → Fin 3 → ℕ, ∃ t : ℕ,
      m.Injective2 ∧
      (∀ i j, 0 < m i j ∧ IsSquare (m i j)) ∧
      (∀ i, ∑ j, m i j = t) ∧
      (∀ j, ∑ i, m i j = t) ∧
      m 0 0 + m 1 1 + m 2 2 = t ∧
      m 0 2 + m 1 1 + m 2 0 = t := by
  rcases h1m_a with ⟨q1, hq1⟩
  rcases h1p_a with ⟨q2, hq2⟩
  rcases h1m_b with ⟨q3, hq3⟩
  rcases h1p_b with ⟨q4, hq4⟩
  rcases h1m_ab with ⟨q5, hq5⟩
  rcases h1p_ab with ⟨q6, hq6⟩
  rcases h1m_ba with ⟨q7, hq7⟩
  rcases h1p_ba with ⟨q8, hq8⟩
  obtain ⟨D, hD_pos, hda, hdb, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩ :=
    exists_common_den_10 a.den b.den q1.den q2.den q3.den q4.den q5.den q6.den q7.den q8.den
      a.den_pos b.den_pos q1.den_pos q2.den_pos q3.den_pos q4.den_pos q5.den_pos q6.den_pos q7.den_pos q8.den_pos
  obtain ⟨u, hu_eq⟩ := clear_rat_pos_mul_sq a ha_pos D hD_pos hda
  obtain ⟨v, hv_eq⟩ := clear_rat_pos_mul_sq b (ha_pos.trans hab) D hD_pos hdb
  have hD2_pos : (0 : ℚ) < (D : ℚ) ^ 2 := by positivity
  have hu_pos : 0 < u := by
    have : (0 : ℚ) < (u : ℚ) := by rw [hu_eq]; exact mul_pos hD2_pos ha_pos
    exact_mod_cast this
  have huv : u < v := by
    have : (u : ℚ) < (v : ℚ) := by rw [hu_eq, hv_eq]; exact mul_lt_mul_of_pos_left hab hD2_pos
    exact_mod_cast this
  have hne2_nat : v ≠ 2 * u := by
    intro h
    have hq : (v : ℚ) = 2 * (u : ℚ) := by exact_mod_cast h
    rw [hu_eq, hv_eq] at hq
    have hq' : (D : ℚ) ^ 2 * b = (D : ℚ) ^ 2 * (2 * a) := by
      calc (D : ℚ) ^ 2 * b = 2 * ((D : ℚ) ^ 2 * a) := hq
        _ = (D : ℚ) ^ 2 * (2 * a) := by ring
    exact hne2 (mul_left_cancel₀ (ne_of_gt hD2_pos) hq')
  have hsum_nat : u + v < D ^ 2 := by
    have hq : ((u + v : ℕ) : ℚ) < ((D ^ 2 : ℕ) : ℚ) := by
      push_cast
      rw [hu_eq, hv_eq]
      calc (D : ℚ) ^ 2 * a + (D : ℚ) ^ 2 * b = (D : ℚ) ^ 2 * (a + b) := by ring
        _ < (D : ℚ) ^ 2 * 1 := mul_lt_mul_of_pos_left hsum_lt hD2_pos
        _ = (D : ℚ) ^ 2 := mul_one _
    exact_mod_cast hq
  have hsq1 : IsSquare (D ^ 2 - u) := by
    apply clear_rat_sq_to_nat q1 D hd1
    rw [Nat.cast_sub (by omega), Nat.cast_pow, hu_eq, ← hq1]; ring
  have hsq2 : IsSquare (D ^ 2 + u) := by
    apply clear_rat_sq_to_nat q2 D hd2
    rw [Nat.cast_add, Nat.cast_pow, hu_eq, ← hq2]; ring
  have hsq3 : IsSquare (D ^ 2 - v) := by
    apply clear_rat_sq_to_nat q3 D hd3
    rw [Nat.cast_sub (by omega), Nat.cast_pow, hv_eq, ← hq3]; ring
  have hsq4 : IsSquare (D ^ 2 + v) := by
    apply clear_rat_sq_to_nat q4 D hd4
    rw [Nat.cast_add, Nat.cast_pow, hv_eq, ← hq4]; ring
  have hsq5 : IsSquare (D ^ 2 - (u + v)) := by
    apply clear_rat_sq_to_nat q5 D hd5
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_pow, hu_eq, hv_eq, ← hq5]; ring
  have hsq6 : IsSquare (D ^ 2 + (u + v)) := by
    apply clear_rat_sq_to_nat q6 D hd6
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, hu_eq, hv_eq, ← hq6]; ring
  have hsq7 : IsSquare (D ^ 2 - (v - u)) := by
    apply clear_rat_sq_to_nat q7 D hd7
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_pow, hu_eq, hv_eq, ← hq7]; ring
  have hsq8 : IsSquare (D ^ 2 + (v - u)) := by
    apply clear_rat_sq_to_nat q8 D hd8
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_pow, hu_eq, hv_eq, ← hq8]; ring
  exact lucas_magic_square_of_nat D u v hu_pos huv hne2_nat hsum_nat
    hsq1 hsq2 hsq3 hsq4 hsq5 hsq6 hsq7 hsq8

end Proof

theorem main : H1 → H2 → type_of% @MagicSquares.exists_magic_square_squares := by
  intro h1 h2
  obtain ⟨⟨s, t⟩, ha_pos, hab, hne2, hsum_lt, h1m_ab, h1p_ab, h1m_ba, h1p_ba⟩ := h2 h1
  exact rat_magic_square_to_nat
    (4 * s * (1 - s ^ 2) / (1 + s ^ 2) ^ 2)
    (4 * t * (1 - t ^ 2) / (1 + t ^ 2) ^ 2)
    ha_pos hab hne2 hsum_lt
    (bremner_one_sub_isSquare s) (bremner_one_add_isSquare s)
    (bremner_one_sub_isSquare t) (bremner_one_add_isSquare t)
    h1m_ab h1p_ab h1m_ba h1p_ba

end OMA.R_MagicSquares_exists_magic_square_squares_R1
