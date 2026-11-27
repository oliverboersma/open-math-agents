import OMAReductions.R_Erdos364_erdos_364_variants_strong_R1
import Mathlib

/-!
Reduce the gap bound for non-arithmetic triples of powerful numbers to two
estimates involving the product of their squarefree parts.
-/

namespace OMA.R_Erdos364_erdos_364_variants_strong_R1_H1_R1

private theorem same_weight_gap {m n s x y : ℕ}
    (hs : 0 < s) (hm : x ^ 2 * s = m) (hn : y ^ 2 * s = n) (hmn : m < n) :
    m < (n - m) ^ 2 := by
  have hxy : x < y := by
    by_contra! h
    have hmono : y ^ 2 * s ≤ x ^ 2 * s := by gcongr
    omega
  have hnext : (x + 1) ^ 2 * s ≤ n := by
    rw [← hn]
    gcongr
    omega
  have hsum : n - m + m = n := Nat.sub_add_cancel hmn.le
  have hxs : x * s < n - m := by
    nlinarith [Nat.zero_le (x * s)]
  have hsquare : s ≤ s ^ 2 := by
    nlinarith [Nat.one_le_iff_ne_zero.mpr hs.ne']
  calc
    m = x ^ 2 * s := hm.symm
    _ ≤ x ^ 2 * s ^ 2 := Nat.mul_le_mul_left _ hsquare
    _ = (x * s) ^ 2 := (mul_pow _ _ _).symm
    _ < (n - m) ^ 2 := by gcongr

private theorem root_lt_of_lt_pow {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    {j : ℕ} (hj : 0 < j) (h : a < d ^ j) : a ^ (1 / (j : ℝ)) < d := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  calc
    a ^ (1 / (j : ℝ)) < (d ^ j) ^ (1 / (j : ℝ)) :=
      Real.rpow_lt_rpow ha h (by positivity)
    _ = d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd, mul_one_div,
        div_self hj'.ne', Real.rpow_one]

/-- A bound on the product of the squarefree parts, obtained conditionally by
applying the rational abc conjecture to the pairs in the triple. -/
def H1 : Prop :=
  ∀ k : ℕ, 0 < k → ∃ l M : ℕ, ∀ a b c s t u x y z : ℕ,
    0 < a → a < b → b < c → c ≤ 2 * a → a + c ≠ 2 * b →
    a.Powerful → b.Powerful → c.Powerful →
    Squarefree s → Squarefree t → Squarefree u → s ≠ t → s ≠ u → t ≠ u →
    x ^ 2 * s = a → y ^ 2 * t = b → z ^ 2 * u = c →
    (s * t * u) ^ k ≤ M * a * (c - a) ^ l

/-- A polynomial height bound for simultaneous differences of weighted squares
with distinct squarefree weights. -/
def H2 : Prop :=
  ∃ k C : ℕ, 0 < k ∧ ∀ a b c s t u x y z : ℕ,
    0 < a → a < b → b < c → c ≤ 2 * a → a + c ≠ 2 * b →
    a.Powerful → b.Powerful → c.Powerful →
    Squarefree s → Squarefree t → Squarefree u → s ≠ t → s ≠ u → t ≠ u →
    x ^ 2 * s = a → y ^ 2 * t = b → z ^ 2 * u = c →
    a ≤ C * (s * t * u * (c - a)) ^ k

theorem main : H1 → H2 → OMA.R_Erdos364_erdos_364_variants_strong_R1.H1 := by
  intro hWeights hHeight
  obtain ⟨k, C, hk, hHeight⟩ := hHeight
  obtain ⟨l, M, hWeights⟩ := hWeights (2 * k) (by omega)
  let K := C ^ 2 * M
  let q := l + 2 * k
  let j := q + q
  have hj : 0 < j := by dsimp [j, q]; omega
  refine ⟨1 / (j : ℝ), by positivity, K ^ 2 + 2, ?_⟩
  intro a b c ha hab hbc hpa hpb hpc hAP
  let D := c - a
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hExtend {i : ℕ} (hi : i ≤ j) (h : a < D ^ i) : a < D ^ j :=
    h.trans_le (pow_le_pow_right₀ hD hi)
  have haPos : 0 < a := by omega
  have hGap : a < D ^ j := by
    by_cases hc : c ≤ 2 * a
    · obtain ⟨s, x, hs, _, hxs, hsf⟩ := Nat.sq_mul_squarefree_of_pos haPos
      obtain ⟨t, y, ht, _, hyt, htf⟩ := Nat.sq_mul_squarefree_of_pos (haPos.trans hab)
      obtain ⟨u, z, _, _, hzu, huf⟩ := Nat.sq_mul_squarefree_of_pos (haPos.trans (hab.trans hbc))
      have hTwo : 2 ≤ j := by dsimp [j, q]; omega
      by_cases hst : s = t
      · subst t
        refine hExtend hTwo ((same_weight_gap hs hxs hyt hab).trans_le ?_)
        dsimp [D]
        gcongr
      by_cases hsu : s = u
      · subst u
        exact hExtend hTwo (same_weight_gap hs hxs hzu (hab.trans hbc))
      by_cases htu : t = u
      · subst u
        refine hExtend hTwo (hab.trans ((same_weight_gap ht hyt hzu hbc).trans_le ?_))
        dsimp [D]
        gcongr
      let S := s * t * u
      have hProduct : S ^ (2 * k) ≤ M * a * D ^ l :=
        hWeights a b c s t u x y z haPos hab hbc hc hAP hpa hpb hpc
          hsf htf huf hst hsu htu hxs hyt hzu
      have hHeight' : a ≤ C * (S * D) ^ k :=
        hHeight a b c s t u x y z haPos hab hbc hc hAP hpa hpb hpc
          hsf htf huf hst hsu htu hxs hyt hzu
      have hSquare : a ^ 2 ≤ (K * D ^ q) * a := by
        calc
          a ^ 2 ≤ (C * (S * D) ^ k) ^ 2 := by gcongr
          _ = C ^ 2 * (S ^ (2 * k) * D ^ (2 * k)) := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm k 2, mul_pow]
          _ ≤ C ^ 2 * ((M * a * D ^ l) * D ^ (2 * k)) := by gcongr
          _ = (K * D ^ q) * a := by
            dsimp [K, q]
            rw [pow_add]
            ring
      have hBound : a ≤ K * D ^ q := by
        exact Nat.le_of_mul_le_mul_right (by simpa only [pow_two] using hSquare) haPos
      have hK : K < D ^ q := by
        by_contra! h
        have hbad : a ≤ K ^ 2 := hBound.trans (by rw [pow_two]; gcongr)
        omega
      calc
        a ≤ K * D ^ q := hBound
        _ < D ^ q * D ^ q := by gcongr
        _ = D ^ j := (pow_add D q q).symm
    · apply hExtend (i := 1) (by omega)
      rw [pow_one]
      dsimp [D]
      omega
  have hReal : (a : ℝ) < (D : ℝ) ^ j := by exact_mod_cast hGap
  have hResult := root_lt_of_lt_pow (by positivity) (by positivity) hj hReal
  have hCast : (D : ℝ) = (c : ℝ) - (a : ℝ) := Nat.cast_sub (hab.trans hbc).le
  rwa [hCast] at hResult

end OMA.R_Erdos364_erdos_364_variants_strong_R1_H1_R1
