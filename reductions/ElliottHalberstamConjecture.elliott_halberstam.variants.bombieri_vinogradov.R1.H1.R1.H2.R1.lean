import OMAReductions.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1
import Mathlib

/- Scalar cutoff, reciprocal Abel summation and logarithmic estimates adapted from
Jonas Whidden (@kimihiro64), Bombieri–Vinogradov in Lean, commit
7a1748306e026825ed6a5555516cc2f28989b2ac, used under Apache-2.0. -/
section
namespace BombieriVinogradov.RealAnalysis


theorem floor_half_bounds {T : Real} (hT : 2 <= T) :
    And (1 <= Nat.floor T)
      (And ((Nat.floor T : Real) <= T) (T / 2 <= (Nat.floor T : Real))) := by
  have hOne : (1 : Real) <= T := by linarith
  have hRaw : (((1 : Nat) : Real) <= T) := by simpa only [Nat.cast_one] using hOne
  have hUpper : (Nat.floor T : Real) <= T := Nat.floor_le (show 0 <= T by linarith)
  refine And.intro (Nat.le_floor hRaw) (And.intro hUpper ?_)
  have hFloor := Nat.lt_floor_add_one T
  linarith

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem polylog_floor_cutoff_bounds {X B : Real}
    (hX : Real.exp (4 : Real) <= X) (hB : 1 <= B) :
    And (1 <= Nat.floor ((Real.log X) ^ B))
      (And ((Nat.floor ((Real.log X) ^ B) : Real) <= (Real.log X) ^ B)
        ((Real.log X) ^ B / 2 <= (Nat.floor ((Real.log X) ^ B) : Real))) := by
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hLogOne : 1 <= Real.log X := by linarith
  have hPower : Real.log X <= (Real.log X) ^ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hLogOne hB
  have hTwo : 2 <= (Real.log X) ^ B := by linarith
  exact floor_half_bounds hTwo

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem exists_bounded_half_power_gap {theta : Real} (hTheta : theta < 1 / 2) :
    exists delta : Real, And (0 < delta) (And (delta <= 1 / 6) (theta + delta <= 1 / 2)) := by
  have hPos : 0 < min (1 / 6 : Real) (1 / 2 - theta) :=
    lt_min (by linarith) (by linarith)
  have hCap := min_le_left (1 / 6 : Real) (1 / 2 - theta)
  have hGap := min_le_right (1 / 6 : Real) (1 / 2 - theta)
  exact Exists.intro (min (1 / 6 : Real) (1 / 2 - theta))
    (And.intro hPos (And.intro hCap (by linarith)))

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem eventually_log_rpow_le_rpow (b : Real) {delta : Real} (hDelta : 0 < delta) :
    Filter.Eventually (fun X : Real => (Real.log X) ^ b <= X ^ delta) Filter.atTop := by
  have hBound := (_root_.isLittleO_log_rpow_rpow_atTop b hDelta).def
    (show (0 : Real) < 1 from zero_lt_one)
  refine (hBound.and (Filter.eventually_ge_atTop (1 : Real))).mono ?_
  intro X h
  have hX : 0 <= X := zero_le_one.trans h.2
  have hLog : 0 <= (Real.log X) ^ b := Real.rpow_nonneg (Real.log_nonneg h.2) b
  have hPower : 0 <= X ^ delta := Real.rpow_nonneg hX delta
  simpa only [Real.norm_of_nonneg hLog, Real.norm_of_nonneg hPower, one_mul] using h.1

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_Icc_le_sum_Icc_add_sum_Ioc (F : Nat -> Real) (hF : forall n, 0 <= F n)
    (R Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) F <=
      Finset.sum (Finset.Icc 1 R) F + Finset.sum (Finset.Ioc R Q) F := by
  have hCover : forall n, (Finset.Icc 1 Q : Set Nat) n ->
      ((Union.union (Finset.Icc 1 R) (Finset.Ioc R Q) : Finset Nat) : Set Nat) n := by
    intro n hn
    have hAlternatives : Or ((Finset.Icc 1 R : Set Nat) n)
        ((Finset.Ioc R Q : Set Nat) n) := by
      by_cases hnR : n <= R
      case pos =>
        exact Or.inl (Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp hn).1 hnR))
      case neg =>
        exact Or.inr (Finset.mem_Ioc.mpr (And.intro (Nat.lt_of_not_ge hnR)
          (Finset.mem_Icc.mp hn).2))
    exact (Finset.mem_union (a := n) (s := Finset.Icc 1 R)
      (t := Finset.Ioc R Q)).mpr hAlternatives
  have hDisjoint : Disjoint (Finset.Icc 1 R) (Finset.Ioc R Q) :=
    Finset.disjoint_left.mpr (fun _ hn hnTail =>
      (Nat.not_lt_of_ge (Finset.mem_Icc.mp hn).2) (Finset.mem_Ioc.mp hnTail).1)
  calc
    Finset.sum (Finset.Icc 1 Q) F <=
        Finset.sum (Union.union (Finset.Icc 1 R) (Finset.Ioc R Q)) F :=
      Finset.sum_le_sum_of_subset_of_nonneg hCover (fun n _ _ => hF n)
    _ = Finset.sum (Finset.Icc 1 R) F + Finset.sum (Finset.Ioc R Q) F :=
      Finset.sum_union hDisjoint

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem quadratic_div_boundary_le (a b c q r : Real)
    (ha : 0 <= a) (hr : 0 < r) (hrq : r <= q) :
    (a + b * q + c * q ^ 2) / q <= a / r + b + c * q := by
  have hq : 0 < q := hr.trans_le hrq
  have hqZero : Ne q 0 := by positivity
  have hIdentity : (a + b * q + c * q ^ 2) / q = a / q + b + c * q := by
    field_simp
  have hConstant : a / q <= a / r := div_le_div_of_nonneg_left ha hr hrq
  rw [hIdentity]
  linarith

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem quadratic_div_reciprocal_kernel_le (a b c k : Real) (hc : 0 <= c) (hk : 0 < k) :
    (a + b * k + c * k ^ 2) / (k * (k + 1)) <=
      a / (k * (k + 1)) + b / (k + 1) + c := by
  have hkZero : Ne k 0 := by positivity
  have hkOne : Ne (k + 1) 0 := by positivity
  have hIdentity : (a + b * k + c * k ^ 2) / (k * (k + 1)) =
      a / (k * (k + 1)) + b / (k + 1) + c - c / (k + 1) := by
    field_simp
    ring
  have hRemainder : 0 <= c / (k + 1) := by positivity
  rw [hIdentity]
  linarith

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem mul_sub_reciprocal_eq_div_mul (a x : Real)
    (hx : Ne x 0) (hxOne : Ne (x + 1) 0) :
    a * (1 / x - 1 / (x + 1)) = a / (x * (x + 1)) := by
  field_simp
  ring

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_reciprocal_product_Ico {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) * ((k : Real) + 1))) =
      1 / (R : Real) - 1 / (Q : Real) := by
  induction Q, hRQ using Nat.le_induction with
  | base => simp
  | succ Q hRQ ih =>
    have hQ : 0 < Q := Nat.lt_of_lt_of_le Nat.zero_lt_one (hR.trans hRQ)
    have hQReal : (0 : Real) < (Q : Real) := Nat.cast_pos.mpr hQ
    have hDiff : 1 / (Q : Real) - 1 / ((Q : Real) + 1) =
        1 / ((Q : Real) * ((Q : Real) + 1)) := by
      simpa only [one_mul] using mul_sub_reciprocal_eq_div_mul 1 (Q : Real)
        (by positivity) (by positivity)
    rw [Finset.sum_Ico_succ_top hRQ, ih, <- hDiff]
    simp only [Nat.cast_add, Nat.cast_one]
    ring


theorem sum_reciprocal_product_Ico_le {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) * ((k : Real) + 1))) <=
      1 / (R : Real) := by
  rw [sum_reciprocal_product_Ico hR hRQ]
  have hInv : (0 : Real) <= 1 / (Q : Real) := by positivity
  linarith

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis

theorem sum_one_div_Icc_le_one_add_log (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) <=
      1 + Real.log (Q : Real) := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) = (harmonic Q : Real) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
    _ <= 1 + Real.log (Q : Real) := harmonic_le_one_add_log Q

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_one_div_add_one_Ico_le {R Q : Nat} (hR : 1 <= R) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) <=
      1 + Real.log (Q : Real) := by
  have hSubset : forall k, (Finset.Ico R Q : Set Nat) k ->
      (Finset.Icc 1 Q : Set Nat) k := by
    intro k hk
    exact Finset.mem_Icc.mpr (And.intro (hR.trans (Finset.mem_Ico.mp hk).1)
      (Finset.mem_Ico.mp hk).2.le)
  calc
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) <=
        Finset.sum (Finset.Ico R Q) (fun k => 1 / (k : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hR.trans (Finset.mem_Ico.mp hk).1)
      have hkReal : (0 : Real) < (k : Real) := Nat.cast_pos.mpr hkPos
      exact one_div_le_one_div_of_le hkReal (by linarith)
    _ <= Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k : Real)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun k _ _ => by positivity)
    _ <= 1 + Real.log (Q : Real) := sum_one_div_Icc_le_one_add_log Q

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_quadratic_div_reciprocal_kernel_le (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) {R Q : Nat}
    (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) <=
      a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real) := by
  have hCard : ((Finset.Ico R Q).card : Real) <= (Q : Real) := by
    rw [Nat.card_Ico]
    exact Nat.cast_le.mpr (Nat.sub_le Q R)
  have hConstant := mul_le_mul_of_nonneg_left
    (sum_reciprocal_product_Ico_le hR hRQ) ha
  have hLinear := mul_le_mul_of_nonneg_left
    (sum_one_div_add_one_Ico_le (Q := Q) hR) hb
  have hQuadratic := mul_le_mul_of_nonneg_right hCard hc
  calc
    Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) <=
        Finset.sum (Finset.Ico R Q)
          (fun k => a / ((k : Real) * ((k : Real) + 1)) +
            b / ((k : Real) + 1) + c) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hR.trans (Finset.mem_Ico.mp hk).1)
      exact quadratic_div_reciprocal_kernel_le a b c (k : Real) hc
        (Nat.cast_pos.mpr hkPos)
    _ = a * Finset.sum (Finset.Ico R Q)
          (fun k => 1 / ((k : Real) * ((k : Real) + 1))) +
        b * Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) +
        ((Finset.Ico R Q).card : Real) * c := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.mul_sum, mul_one_div]
    _ <= a * (1 / (R : Real)) + b * (1 + Real.log (Q : Real)) + (Q : Real) * c :=
      add_le_add (add_le_add hConstant hLinear) hQuadratic
    _ = a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real) := by
      rw [mul_one_div]
      ring

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_Ioc_mul_eq_abel (F g : Nat -> Real) {R Q : Nat} (hRQ : R <= Q) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n * g n) =
      Finset.sum (Finset.Icc 1 Q) F * g Q -
        Finset.sum (Finset.Icc 1 R) F * g R +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F * (g k - g (k + 1))) := by
  induction Q, hRQ using Nat.le_induction with
  | base => simp
  | succ Q hRQ ih =>
    rw [Finset.sum_Ioc_succ_top hRQ, Finset.sum_Ico_succ_top hRQ,
      Finset.sum_Icc_succ_top (Nat.succ_pos Q), ih]
    ring

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_Ioc_div_eq_abel (F : Nat -> Real) {R Q : Nat}
    (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) =
      Finset.sum (Finset.Icc 1 Q) F / (Q : Real) -
        Finset.sum (Finset.Icc 1 R) F / (R : Real) +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) := by
  have hAbel := sum_Ioc_mul_eq_abel F (fun n => 1 / (n : Real)) hRQ
  simp only [mul_one_div] at hAbel
  rw [hAbel]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (hR.trans (Finset.mem_Ico.mp hk).1)
  have hkReal : (0 : Real) < (k : Real) := Nat.cast_pos.mpr hkPos
  simp only [Nat.cast_add, Nat.cast_one]
  exact mul_sub_reciprocal_eq_div_mul (Finset.sum (Finset.Icc 1 k) F) (k : Real)
    (by positivity) (by positivity)

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_Ioc_div_le_of_quadratic_partial_sums (F : Nat -> Real) (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hF : forall n, 0 <= F n)
    {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q)
    (hBound : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <= a + b * (k : Real) + c * (k : Real) ^ 2) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
      2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) + 2 * c * (Q : Real) := by
  have hRReal : (0 : Real) < (R : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hR)
  have hRQReal : (R : Real) <= (Q : Real) := Nat.cast_le.mpr hRQ
  have hBoundary : Finset.sum (Finset.Icc 1 Q) F / (Q : Real) <=
      a / (R : Real) + b + c * (Q : Real) :=
    (div_le_div_of_nonneg_right (hBound Q (hR.trans hRQ) (Nat.le_refl Q))
      (Nat.cast_nonneg Q)).trans
      (quadratic_div_boundary_le a b c (Q : Real) (R : Real) ha hRReal hRQReal)
  have hKernel :
      Finset.sum (Finset.Ico R Q)
        (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) <=
      Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact div_le_div_of_nonneg_right
      (hBound k (hR.trans (Finset.mem_Ico.mp hk).1) (Finset.mem_Ico.mp hk).2.le)
      (by positivity)
  have hKernelBound := hKernel.trans
    (sum_quadratic_div_reciprocal_kernel_le a b c ha hb hc hR hRQ)
  have hDiscard : 0 <= Finset.sum (Finset.Icc 1 R) F / (R : Real) :=
    div_nonneg (Finset.sum_nonneg (fun n _ => hF n)) (Nat.cast_nonneg R)
  rw [sum_Ioc_div_eq_abel F hR hRQ]
  calc
    Finset.sum (Finset.Icc 1 Q) F / (Q : Real) -
        Finset.sum (Finset.Icc 1 R) F / (R : Real) +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) <=
        (a / (R : Real) + b + c * (Q : Real)) +
          (a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real)) := by
      linarith
    _ = 2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real) := by ring


theorem sum_Ioc_div_le_of_scaled_quadratic_partial_sums
    (F : Nat -> Real) (L a b c : Real) (hL : 0 <= L)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hF : forall n, 0 <= F n)
    {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q)
    (hBound : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <= L * (a + b * (k : Real) + c * (k : Real) ^ 2)) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
      L * (2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real)) := by
  have hScaled : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <=
        L * a + (L * b) * (k : Real) + (L * c) * (k : Real) ^ 2 := by
    intro k hk hkQ
    calc
      Finset.sum (Finset.Icc 1 k) F <=
          L * (a + b * (k : Real) + c * (k : Real) ^ 2) := hBound k hk hkQ
      _ = L * a + (L * b) * (k : Real) + (L * c) * (k : Real) ^ 2 := by ring
  calc
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
        2 * (L * a) / (R : Real) + (L * b) * (2 + Real.log (Q : Real)) +
          2 * (L * c) * (Q : Real) :=
      sum_Ioc_div_le_of_quadratic_partial_sums F (L * a) (L * b) (L * c)
        (by positivity) (by positivity) (by positivity) hF hR hRQ hScaled
    _ = L * (2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real)) := by ring

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem log_mul_nat_nonneg {X : Real} {m : Nat} (hX : 1 <= X) (hm : 1 <= m) :
    0 <= Real.log (X * (m : Real)) := by
  apply Real.log_nonneg
  have hRaw : (((1 : Nat) : Real) <= (m : Real)) := Nat.cast_le.mpr hm
  have hM : (1 : Real) <= (m : Real) := by simpa only [Nat.cast_one] using hRaw
  calc
    (1 : Real) = 1 * 1 := by ring
    _ <= X * (m : Real) := by gcongr


theorem log_mul_nat_pow_le {X : Real} {m n : Nat}
    (hX : 1 <= X) (hm : 1 <= m) (hmn : m <= n) (p : Nat) :
    Real.log (X * (m : Real)) ^ p <= Real.log (X * (n : Real)) ^ p := by
  have hXPos : 0 < X := by linarith
  have hMPos : (0 : Real) < (m : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hProductPos : 0 < X * (m : Real) := by positivity
  have hProduct : X * (m : Real) <= X * (n : Real) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmn) hXPos.le
  have hLog := Real.log_le_log hProductPos hProduct
  have hNonneg := log_mul_nat_nonneg hX hm
  gcongr

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem conductor_log_range {X : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hQ : 1 <= Q) (hQX : (Q : Real) <= X) :
    And (4 <= Real.log X)
      (And (0 <= Real.log (Q : Real))
        (And (Real.log (Q : Real) <= Real.log X)
          (And (0 <= Real.log (X * (Q : Real)))
            (Real.log (X * (Q : Real)) <= 2 * Real.log X)))) := by
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hQPos : (0 : Real) < (Q : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hQNonneg : 0 <= Real.log (Q : Real) := Real.log_natCast_nonneg Q
  have hQLe : Real.log (Q : Real) <= Real.log X := Real.log_le_log hQPos hQX
  have hProduct : Real.log (X * (Q : Real)) = Real.log X + Real.log (Q : Real) :=
    Real.log_mul (ne_of_gt hXPos) (ne_of_gt hQPos)
  have hProductNonneg : 0 <= Real.log (X * (Q : Real)) := by rw [hProduct]; linarith
  have hProductLe : Real.log (X * (Q : Real)) <= 2 * Real.log X := by rw [hProduct]; linarith
  exact And.intro hLogFour (And.intro hQNonneg
    (And.intro hQLe (And.intro hProductNonneg hProductLe)))

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem conductor_log_envelopes {X : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hQ : 1 <= Q) (hQX : (Q : Real) <= X) :
    And (Real.log (X * (Q : Real)) ^ 3 <= 8 * (Real.log X) ^ 3)
      (And ((1 + Real.log (Q : Real)) ^ 2 <= 4 * (Real.log X) ^ 2)
        (2 + Real.log (Q : Real) <= 3 * Real.log X)) := by
  have hRange := conductor_log_range hX hQ hQX
  have hLogFour := hRange.1
  have hQNonneg := hRange.2.1
  have hQLe := hRange.2.2.1
  have hProductNonneg := hRange.2.2.2.1
  have hProductLe := hRange.2.2.2.2
  have hCube : Real.log (X * (Q : Real)) ^ 3 <= 8 * (Real.log X) ^ 3 := by
    calc
      Real.log (X * (Q : Real)) ^ 3 <= (2 * Real.log X) ^ 3 := by gcongr
      _ = 8 * (Real.log X) ^ 3 := by ring
  have hSquareRange : 1 + Real.log (Q : Real) <= 2 * Real.log X := by linarith
  have hSquareNonneg : 0 <= 1 + Real.log (Q : Real) := by linarith
  have hSquare : (1 + Real.log (Q : Real)) ^ 2 <= 4 * (Real.log X) ^ 2 := by
    calc
      (1 + Real.log (Q : Real)) ^ 2 <= (2 * Real.log X) ^ 2 := by gcongr
      _ = 4 * (Real.log X) ^ 2 := by ring
  exact And.intro hCube (And.intro hSquare (by linarith))

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem two_mul_div_le_of_half_le {T r X : Real}
    (hT : 0 < T) (hCut : T / 2 <= r) (hX : 0 <= X) :
    2 * X / r <= 4 * X / T := by
  calc
    2 * X / r <= 2 * X / (T / 2) :=
      div_le_div_of_nonneg_left (a := 2 * X) (b := r) (c := T / 2)
        (by positivity) (by positivity) hCut
    _ = 4 * X / T := by ring

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.RealAnalysis


theorem rpow_mul_div_le_div {L X u v w : Real}
    (hL : 1 <= L) (hX : 0 <= X) (hDegree : u + w <= v) :
    L ^ u * (X / L ^ v) <= X / L ^ w := by
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hVPos : 0 < L ^ v := Real.rpow_pos_of_pos hLPos v
  have hWPos : 0 < L ^ w := Real.rpow_pos_of_pos hLPos w
  have hVNe : Ne (L ^ v) 0 := ne_of_gt hVPos
  have hWNe : Ne (L ^ w) 0 := ne_of_gt hWPos
  have hProduct : (L ^ u * (X / L ^ v)) * L ^ w <= X := by
    calc
      (L ^ u * (X / L ^ v)) * L ^ w = X * L ^ (u + w) / L ^ v := by
        rw [Real.rpow_add hLPos u w]
        ring
      _ <= X * L ^ v / L ^ v :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hDegree) hX)
          hVPos.le
      _ = X := by field_simp
  calc
    L ^ u * (X / L ^ v) = (L ^ u * (X / L ^ v)) * L ^ w / L ^ w := by field_simp
    _ <= X / L ^ w := div_le_div_of_nonneg_right hProduct hWPos.le


theorem pow_mul_div_le_div {L X v w : Real} (n : Nat)
    (hL : 1 <= L) (hX : 0 <= X) (hDegree : (n : Real) + w <= v) :
    L ^ n * (X / L ^ v) <= X / L ^ w := by
  simpa only [Real.rpow_natCast] using
    (rpow_mul_div_le_div (L := L) (X := X) (u := (n : Real)) (v := v) (w := w)
      hL hX hDegree)

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


theorem normalized_inverse_term {X A C : Real} {R Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C)
    (hQ : 1 <= Q) (hQX : (Q : Real) <= X)
    (hR : (Real.log X) ^ (A + 8) / 2 <= (R : Real)) :
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X / (R : Real)) <=
      32 * C * (X / (Real.log X) ^ (A + 2)) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hLogPos : 0 < Real.log X := by linarith
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hEnvelope := RealAnalysis.conductor_log_envelopes hX hQ hQX
  have hInverse := RealAnalysis.two_mul_div_le_of_half_le
    (T := (Real.log X) ^ (A + 8)) (r := (R : Real)) (X := X)
    (Real.rpow_pos_of_pos hLogPos (A + 8)) hR hXPos.le
  have hDenominator := RealAnalysis.pow_mul_div_le_div
    (L := Real.log X) (X := X) (v := A + 8) (w := A + 2) 3
    hLogOne hXPos.le (show (3 : Real) + (A + 2) <= A + 8 by linarith)
  calc
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X / (R : Real)) <=
        (C * (8 * (Real.log X) ^ 3)) * (4 * X / (Real.log X) ^ (A + 8)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEnvelope.1 hC) hInverse
        (by positivity) (by positivity)
    _ = 32 * C * ((Real.log X) ^ 3 * (X / (Real.log X) ^ (A + 8))) := by ring
    _ <= 32 * C * (X / (Real.log X) ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left hDenominator (by positivity)

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.RealAnalysis


theorem rpow_mul_rpow_le_div_of_saving {X L b t delta w p : Real}
    (hX : 1 <= X) (hL : 1 <= L) (hLog : L ^ b <= X ^ delta)
    (hDegree : w + p <= b) (hGap : t + delta <= 1) :
    X ^ t * L ^ p <= X / L ^ w := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hWPos : 0 < L ^ w := Real.rpow_pos_of_pos hLPos w
  have hWNe : Ne (L ^ w) 0 := ne_of_gt hWPos
  have hLogDegree : L ^ (w + p) <= X ^ delta :=
    (Real.rpow_le_rpow_of_exponent_le hL hDegree).trans hLog
  have hProduct : (X ^ t * L ^ p) * L ^ w <= X := by
    calc
      (X ^ t * L ^ p) * L ^ w = X ^ t * L ^ (w + p) := by
        rw [Real.rpow_add hLPos w p]
        ring
      _ <= X ^ t * X ^ delta :=
        mul_le_mul_of_nonneg_left hLogDegree (Real.rpow_nonneg hXPos.le t)
      _ = X ^ (t + delta) := (Real.rpow_add hXPos t delta).symm
      _ <= X ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hX hGap
      _ = X := Real.rpow_one X
  calc
    X ^ t * L ^ p = (X ^ t * L ^ p) * L ^ w / L ^ w := by field_simp
    _ <= X / L ^ w := div_le_div_of_nonneg_right hProduct hWPos.le


theorem rpow_mul_pow_le_div_of_saving {X L b t delta w : Real} (p : Nat)
    (hX : 1 <= X) (hL : 1 <= L) (hLog : L ^ b <= X ^ delta)
    (hDegree : w + (p : Real) <= b) (hGap : t + delta <= 1) :
    X ^ t * L ^ p <= X / L ^ w := by
  simpa only [Real.rpow_natCast] using
    (rpow_mul_rpow_le_div_of_saving (X := X) (L := L) (b := b) (t := t)
      (delta := delta) (w := w) (p := (p : Real)) hX hL hLog hDegree hGap)

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


theorem normalized_mixed_term {X A C delta : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C)
    (hQ : 1 <= Q) (hQX : (Q : Real) <= X)
    (hSaving : (Real.log X) ^ (A + 8) <= X ^ delta) (hDelta : delta <= 1 / 6) :
    (C * Real.log (X * (Q : Real)) ^ 3) *
        (X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real))) <=
      24 * C * (X / (Real.log X) ^ (A + 2)) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hQLogNonneg : 0 <= Real.log (Q : Real) := hRange.2.1
  have hEnvelope := RealAnalysis.conductor_log_envelopes hX hQ hQX
  have hXOne : 1 <= X := (Real.one_le_exp (show (0 : Real) <= 4 by linarith)).trans hX
  have hPower := RealAnalysis.rpow_mul_pow_le_div_of_saving
    (X := X) (L := Real.log X) (b := A + 8) (t := (5 / 6 : Real))
    (delta := delta) (w := A + 2) 4 hXOne hLogOne hSaving
    (show (A + 2) + (4 : Real) <= A + 8 by linarith) (by linarith)
  have hLinear : X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real)) <=
      X ^ (5 / 6 : Real) * (3 * Real.log X) :=
    mul_le_mul_of_nonneg_left hEnvelope.2.2 (Real.rpow_nonneg hXPos.le (5 / 6))
  calc
    (C * Real.log (X * (Q : Real)) ^ 3) *
        (X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real))) <=
      (C * (8 * (Real.log X) ^ 3)) * (X ^ (5 / 6 : Real) * (3 * Real.log X)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEnvelope.1 hC) hLinear
        (by positivity) (by positivity)
    _ = 24 * C * (X ^ (5 / 6 : Real) * (Real.log X) ^ 4) := by ring
    _ <= 24 * C * (X / (Real.log X) ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left hPower (by positivity)

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


theorem normalized_root_term {X A C theta delta : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hC : 0 <= C)
    (hQ : 1 <= Q) (hQX : (Q : Real) <= X) (hPowerQ : (Q : Real) <= X ^ theta)
    (hSaving : (Real.log X) ^ (A + 8) <= X ^ delta)
    (hGap : theta + delta <= 1 / 2) :
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X ^ (1 / 2 : Real) * (Q : Real)) <=
      16 * C * (X / (Real.log X) ^ (A + 2)) := by
  have hRange := RealAnalysis.conductor_log_range hX hQ hQX
  have hLogOne : 1 <= Real.log X := by linarith [hRange.1]
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hEnvelope := RealAnalysis.conductor_log_envelopes hX hQ hQX
  have hXOne : 1 <= X := (Real.one_le_exp (show (0 : Real) <= 4 by linarith)).trans hX
  have hPower := RealAnalysis.rpow_mul_pow_le_div_of_saving
    (X := X) (L := Real.log X) (b := A + 8) (t := (1 / 2 : Real) + theta)
    (delta := delta) (w := A + 2) 3 hXOne hLogOne hSaving
    (show (A + 2) + (3 : Real) <= A + 8 by linarith) (by linarith)
  have hRoot : 2 * X ^ (1 / 2 : Real) * (Q : Real) <=
      2 * X ^ (1 / 2 : Real) * X ^ theta :=
    mul_le_mul_of_nonneg_left hPowerQ (by positivity)
  calc
    (C * Real.log (X * (Q : Real)) ^ 3) * (2 * X ^ (1 / 2 : Real) * (Q : Real)) <=
        (C * (8 * (Real.log X) ^ 3)) * (2 * X ^ (1 / 2 : Real) * X ^ theta) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEnvelope.1 hC) hRoot
        (by positivity) (by positivity)
    _ = 16 * C * (X ^ ((1 / 2 : Real) + theta) * (Real.log X) ^ 3) := by
      rw [Real.rpow_add hXPos (1 / 2) theta]
      ring
    _ <= 16 * C * (X / (Real.log X) ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left hPower (by positivity)

end BombieriVinogradov.WeightedBombieriVinogradov
end

namespace OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1_H2_R1
open Finset Real Filter ArithmeticFunction
open scoped Classical

/-- Maximal Siegel-Walfisz estimate for individual nonprincipal primitive characters. -/
def H1 : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C > (0:ℝ), ∀ᶠ x : ℕ in atTop,
    ∀ d : ℕ, 1 ≤ d → (d:ℝ) ≤ (Real.log x)^B →
    ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ ≠ 1 → ∀ y ≤ x,
      ‖∑ n ∈ Icc 1 y, (Λ n : ℂ) * χ (n : ZMod d)‖ ≤ C*x/(Real.log x)^A

/-- Vaughan's cumulative mean-value estimate, before reciprocal Abel summation. -/
def H2 : Prop :=
  let P (x d : ℕ) := (∑ χ ∈ ((Finset.univ.filter
    (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
      (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
        (Λ n : ℂ) * χ (n : ZMod d)‖)) / (d.totient : ℝ)
  ∃ C > (0:ℝ), ∀ x k : ℕ, 2 ≤ x → 1 ≤ k →
    ∑ d ∈ Icc 1 k, (d:ℝ) * P x d ≤ (C * Real.log ((x:ℝ)*k)^3) *
      (x + (x:ℝ)^(5/6:ℝ)*k + (x:ℝ)^(1/2:ℝ)*(k:ℝ)^2)

lemma finite_initial_bound (F : ℕ → ℝ) (B C : ℝ) (hC : 0 < C)
    (h : ∀ᶠ x : ℕ in atTop, F x ≤ C*x/(Real.log x)^B) :
    ∃ D > (0:ℝ), ∀ x : ℕ, 2 < x → F x ≤ D*x/(Real.log x)^B := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 h
  let T := ∑ i ∈ range N, |F i * (Real.log i)^B / i|
  have t0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C+T,by linarith,?_⟩
  intro x hx
  have xp : 0 < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have L : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1<x))
  have lb := Real.rpow_pos_of_pos L B
  by_cases hnx : N ≤ x
  · exact (hN x hnx).trans (by gcongr; linarith)
  have hk : F x * (Real.log x)^B / x ≤ T := (le_abs_self _).trans
    (single_le_sum (fun (i : ℕ) _ => abs_nonneg (F i * (Real.log i)^B / i))
      (mem_range.mpr (by omega : x < N)))
  apply (le_div_iff₀ lb).mpr
  exact (div_le_iff₀ xp).mp (by linarith : F x * (Real.log x)^B / x ≤ C+T)

theorem main : H1 → H2 → OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1.H2 := by
  intro small large θ ht B hB
  let P (x d : ℕ) := (∑ χ ∈ ((Finset.univ.filter
    (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
      (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
        (Λ n : ℂ) * χ (n : ZMod d)‖)) / (d.totient : ℝ)
  obtain ⟨V,hV,vaughan⟩ := large
  obtain ⟨δ,hδ,hcap,hgap⟩ := BombieriVinogradov.RealAnalysis.exists_bounded_half_power_gap ht
  let A := B-2
  let E := A+8
  have epos : 0<E := by dsimp [E,A]; linarith
  have aB : A+2=B := by dsimp [A]; ring
  obtain ⟨S,hS,hs⟩ := small (B+E) E (by linarith) epos
  apply finite_initial_bound (fun x => ∑ d ∈ Icc 1 ⌊(x:ℝ)^θ⌋₊, P x d) B (S+72*V) (by positivity)
  have natlim := (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hs, natlim.eventually (eventually_ge_atTop (Real.exp 4)),
    natlim.eventually (BombieriVinogradov.RealAnalysis.eventually_log_rpow_le_rpow E hδ)] with x hs hx hsav
  let X := (x:ℝ)
  have hx4 : Real.exp 4 ≤ X := hx
  have xp : 0<X := (Real.exp_pos _).trans_le hx4
  have L4 : 4 ≤ Real.log X := (Real.le_log_iff_exp_le xp).2 hx4
  have lp : 0 < Real.log X := by linarith
  have x2 : 2 ≤ x := by
    have hh := Real.add_one_le_exp (4:ℝ)
    have : (2:ℝ) ≤ X := by linarith
    change (2:ℝ) ≤ (x:ℝ) at this
    exact_mod_cast this
  have x1 : 1 ≤ X := by change (1:ℝ) ≤ (x:ℝ); exact_mod_cast (by omega : 1≤x)
  let R := ⌊(Real.log X)^E⌋₊
  let Q := ⌊X^θ⌋₊
  have cut := BombieriVinogradov.RealAnalysis.polylog_floor_cutoff_bounds (B := E) hx4
    (by dsimp [E,A]; linarith)
  have hR : 1 ≤ R := cut.1
  have hP (d : ℕ) : 0 ≤ P x d := by
    dsimp [P]
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply sum_nonneg
    intro χ _
    exact (norm_nonneg _).trans (Finset.le_sup' (fun y => ‖∑ n ∈ Icc 1 y, (Λ n : ℂ) * χ (n : ZMod d)‖) (by simp : 0 ∈ range (x+1)))
  have sBound : ∑ d ∈ Icc 1 R, P x d ≤ S*X/(Real.log X)^B := by
    let K := S*X/(Real.log X)^(B+E)
    have kn : 0 ≤ K := by dsimp [K]; positivity
    have each (d : ℕ) (hd : d ∈ Icc 1 R) : P x d ≤ K := by
      have h1 := (mem_Icc.mp hd).1
      have dr : (d:ℝ) ≤ (Real.log X)^E := (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans cut.2.1
      have tot : 0 < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0<d)
      dsimp only [P]
      apply (div_le_iff₀ tot).2
      let T := (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1
      have cc : T.card ≤ d.totient := by
        have bound := card_le_univ T
        haveI : NeZero d := ⟨by omega⟩
        simpa only [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity] using bound
      calc
        _ ≤ ∑ χ ∈ T, K := by
          dsimp only [T]
          apply sum_le_sum
          intro χ hc
          apply Finset.sup'_le
          intro y hy
          exact hs d h1 dr χ (mem_filter.mp (mem_erase.mp hc).2).2 (mem_erase.mp hc).1 y
            (by have := mem_range.mp hy; omega)
        _ = (T.card:ℝ)*K := by simp
        _ ≤ _ := by rw [mul_comm K]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast cc) kn
    calc
      _ ≤ ∑ _d ∈ Icc 1 R, K := sum_le_sum each
      _ = (R:ℝ)*K := by simp
      _ ≤ (Real.log X)^E*K := mul_le_mul_of_nonneg_right cut.2.1 kn
      _ = _ := by dsimp [K]; rw [Real.rpow_add lp B E]; field_simp <;> ring
  by_cases hrq : R ≤ Q
  · have hQ : 1 ≤ Q := hR.trans hrq
    have powQ : (Q:ℝ) ≤ X^θ := Nat.floor_le (Real.rpow_nonneg xp.le _)
    have qx : (Q:ℝ) ≤ X := powQ.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le x1 (by linarith : θ ≤ 1))
    have scale := BombieriVinogradov.RealAnalysis.log_mul_nat_nonneg x1 hQ
    have tail := BombieriVinogradov.RealAnalysis.sum_Ioc_div_le_of_scaled_quadratic_partial_sums
      (fun d => (d:ℝ)*P x d) (V*Real.log (X*Q)^3) X (X^(5/6:ℝ)) (X^(1/2:ℝ))
      (by positivity) xp.le (by positivity) (by positivity) (fun d => mul_nonneg (Nat.cast_nonneg _) (hP d)) hR hrq
      (fun k hk hq => (vaughan x k x2 hk).trans (by
        have logle := BombieriVinogradov.RealAnalysis.log_mul_nat_pow_le x1 hk hq 3
        change (V*Real.log (X*k)^3)*_ ≤ (V*Real.log (X*Q)^3)*_
        gcongr))
    have cutid : ∑ d ∈ Ioc R Q, P x d = ∑ d ∈ Ioc R Q, (d:ℝ)*P x d/d := by
      apply sum_congr rfl
      intro d hd
      have pos : (0:ℝ)<d := by exact_mod_cast (by have := (mem_Ioc.mp hd).1; omega : 0<d)
      field_simp
    have iB := BombieriVinogradov.WeightedBombieriVinogradov.normalized_inverse_term (A:=A) hx4 hV.le hQ qx cut.2.2
    have mB := BombieriVinogradov.WeightedBombieriVinogradov.normalized_mixed_term (A:=A) hx4 hV.le hQ qx hsav hcap
    have rB := BombieriVinogradov.WeightedBombieriVinogradov.normalized_root_term (A:=A) hx4 hV.le hQ qx powQ hsav hgap
    rw [aB] at iB mB rB
    have split := BombieriVinogradov.RealAnalysis.sum_Icc_le_sum_Icc_add_sum_Ioc (P x) hP R Q
    rw [cutid] at split
    change ∑ d ∈ Icc 1 Q, P x d ≤ (S+72*V)*X/(Real.log X)^B
    refine (split.trans (add_le_add sBound tail)).trans ?_
    change V*Real.log (X*Q)^3*(2*X/(R:ℝ)) ≤ _ at iB
    ring_nf at iB mB rB ⊢
    linarith only [iB,mB,rB]
  · have sub : Icc 1 Q ⊆ Icc 1 R := Icc_subset_Icc_right (by omega)
    refine (sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => hP d)).trans (sBound.trans ?_)
    gcongr; linarith

end OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1_H2_R1
