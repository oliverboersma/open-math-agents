import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1_H3_R1
import Mathlib

namespace Hilbert17H2Proof

lemma mul_pos_of_abs_sub_lt {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y : K} (h : |x - y| < |y|) : 0 < x * y := by
  have hsq : (x - y) ^ 2 < y ^ 2 := by
    simpa [sq_abs] using sq_lt_sq.mpr h
  nlinarith [sq_nonneg x]

lemma sign_equiv_of_mul_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y : K} (h : 0 < x * y) : (0 < x ↔ 0 < y) ∧ (x < 0 ↔ y < 0) := by
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at h
    exact lt_irrefl 0 h
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hx : x < 0 := neg_of_mul_pos_left h hy.le
    exact ⟨⟨fun h1 => absurd h1 (not_lt.mpr hx.le), fun h2 => absurd h2 (not_lt.mpr hy.le)⟩,
      ⟨fun _ => hy, fun _ => hx⟩⟩
  · exact absurd rfl hy0
  · have hx : 0 < x := pos_of_mul_pos_left h hy.le
    exact ⟨⟨fun _ => hy, fun _ => hx⟩,
      ⟨fun h1 => absurd h1 (not_lt.mpr hx.le), fun h2 => absurd h2 (not_lt.mpr hy.le)⟩⟩

lemma asymptotic_leading_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ M : K, ∀ x : K, M < x →
      (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0) := by
  by_cases hn : p.natDegree = 0
  · refine ⟨0, fun x _ => ?_⟩
    have hpeq : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hn] using Polynomial.eq_C_of_natDegree_eq_zero hn
    have hev : p.eval x = p.leadingCoeff := by
      conv_lhs => rw [hpeq]
      simp
    rw [hev]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · have hn_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hn
    set n := p.natDegree
    set a := p.leadingCoeff
    have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    set S : K := ∑ i ∈ Finset.range n, |p.coeff i|
    have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    refine ⟨1 + S / |a|, fun x hx => ?_⟩
    have ha_pos : 0 < |a| := abs_pos.mpr ha
    have h1x : 1 < x := by
      have : 0 ≤ S / |a| := div_nonneg hS ha_pos.le
      linarith
    have hx_pos : 0 < x := lt_trans zero_lt_one h1x
    have hSx : S < |a| * x := by
      have hdiv : S / |a| < x := by linarith
      simpa [mul_comm] using (div_lt_iff₀ ha_pos).mp hdiv
    have heval : p.eval x = (∑ i ∈ Finset.range n, p.coeff i * x ^ i) + a * x ^ n := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
      rfl
    have hpow_le : ∀ i ∈ Finset.range n, x ^ i ≤ x ^ (n - 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact pow_le_pow_right₀ h1x.le (Nat.le_sub_one_of_lt hi)
    have hrem : |p.eval x - a * x ^ n| < |a * x ^ n| := by
      have hsub : p.eval x - a * x ^ n = ∑ i ∈ Finset.range n, p.coeff i * x ^ i := by
        rw [heval]
        ring
      rw [hsub]
      calc
        |∑ i ∈ Finset.range n, p.coeff i * x ^ i|
            ≤ ∑ i ∈ Finset.range n, |p.coeff i * x ^ i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.range n, |p.coeff i| * x ^ i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [abs_mul, abs_pow, abs_of_pos hx_pos]
        _ ≤ ∑ i ∈ Finset.range n, |p.coeff i| * x ^ (n - 1) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact mul_le_mul_of_nonneg_left (hpow_le i hi) (abs_nonneg _)
        _ = S * x ^ (n - 1) := by rw [← Finset.sum_mul]
        _ < (|a| * x) * x ^ (n - 1) := by
          exact mul_lt_mul_of_pos_right hSx (pow_pos hx_pos _)
        _ = |a| * (x ^ 1 * x ^ (n - 1)) := by rw [pow_one]; ring
        _ = |a| * x ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' hn_pos]
        _ = |a * x ^ n| := by
          rw [abs_mul, abs_pow, abs_of_pos hx_pos]
    have hmul : 0 < p.eval x * (a * x ^ n) := mul_pos_of_abs_sub_lt hrem
    have hpow_pos : 0 < x ^ n := pow_pos hx_pos n
    have hmul' : 0 < p.eval x * a := by
      have : p.eval x * (a * x ^ n) = (p.eval x * a) * x ^ n := by ring
      rw [this] at hmul
      exact pos_of_mul_pos_left hmul hpow_pos.le
    exact sign_equiv_of_mul_pos hmul'

lemma eval_near_zero_mul_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Polynomial K) (m : ℕ) (hzero : ∀ i < m, p.coeff i = 0) (hcm : p.coeff m ≠ 0) :
    ∃ δ : K, 0 < δ ∧ ∀ t : K, t ≠ 0 → |t| < δ → 0 < p.eval t * (p.coeff m * t ^ m) := by
  set N := p.natDegree
  have hmN : m ≤ N := Polynomial.le_natDegree_of_ne_zero hcm
  set S : K := ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcm_pos : 0 < |p.coeff m| := abs_pos.mpr hcm
  refine ⟨min 1 (|p.coeff m| / (S + 1)), lt_min zero_lt_one (div_pos hcm_pos (by linarith)), ?_⟩
  intro t ht0 ht
  have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht (min_le_left _ _)).le
  have htS : S * |t| < |p.coeff m| := by
    have hdiv : |t| < |p.coeff m| / (S + 1) := lt_of_lt_of_le ht (min_le_right _ _)
    have h1 : (S + 1) * |t| < |p.coeff m| := (lt_div_iff₀' (by linarith)).mp hdiv
    have h2 : S * |t| ≤ (S + 1) * |t| := by nlinarith [abs_nonneg t]
    exact lt_of_le_of_lt h2 h1
  have hsplit : p.eval t - p.coeff m * t ^ m = ∑ i ∈ Finset.Ico (m + 1) (N + 1), p.coeff i * t ^ i := by
    rw [Polynomial.eval_eq_sum_range]
    have h1 : ∑ i ∈ Finset.range (N + 1), p.coeff i * t ^ i =
        (∑ i ∈ Finset.range (m + 1), p.coeff i * t ^ i) +
        ∑ i ∈ Finset.Ico (m + 1) (N + 1), p.coeff i * t ^ i := by
      rw [← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range]
      exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)).symm
    have h2 : ∑ i ∈ Finset.range (m + 1), p.coeff i * t ^ i = p.coeff m * t ^ m := by
      rw [Finset.sum_range_succ]
      have h0 : ∑ i ∈ Finset.range m, p.coeff i * t ^ i = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        rw [hzero i hi, zero_mul]
      rw [h0, zero_add]
    rw [h1, h2]
    ring
  have hpow_pos : 0 < |t| ^ m := pow_pos (abs_pos.mpr ht0) m
  have hbound : |p.eval t - p.coeff m * t ^ m| < |p.coeff m * t ^ m| := by
    rw [hsplit]
    calc
      |∑ i ∈ Finset.Ico (m + 1) (N + 1), p.coeff i * t ^ i|
          ≤ ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i * t ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i| * |t| ^ i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_pow]
      _ ≤ ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i| * (|t| ^ m * |t|) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [Finset.mem_Ico] at hi
        have hi_eq : i = m + 1 + (i - (m + 1)) := by omega
        have hpow_i : |t| ^ i ≤ |t| ^ m * |t| := by
          conv_lhs => rw [hi_eq, pow_add, pow_add, pow_one]
          have hrem_le : |t| ^ (i - (m + 1)) ≤ 1 := pow_le_one₀ (abs_nonneg t) ht1
          calc
            |t| ^ m * |t| * |t| ^ (i - (m + 1))
                ≤ |t| ^ m * |t| * 1 := mul_le_mul_of_nonneg_left hrem_le (mul_nonneg (pow_nonneg (abs_nonneg t) m) (abs_nonneg t))
            _ = |t| ^ m * |t| := mul_one _
        exact mul_le_mul_of_nonneg_left hpow_i (abs_nonneg _)
      _ = (S * |t|) * |t| ^ m := by rw [← Finset.sum_mul]; ring
      _ < |p.coeff m| * |t| ^ m := mul_lt_mul_of_pos_right htS hpow_pos
      _ = |p.coeff m * t ^ m| := by rw [abs_mul, abs_pow]
  exact mul_pos_of_abs_sub_lt hbound

lemma local_poly_deriv_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Polynomial K) (a : K) (hf : f ≠ 0) (hfa : f.eval a = 0) :
    ∃ δ : K, 0 < δ ∧ ∀ t : K, 0 < t → t < δ →
      0 < f.eval (a + t) * f.derivative.eval (a + t) ∧
      f.eval (a - t) * f.derivative.eval (a - t) < 0 := by
  set g : Polynomial K := f.comp (Polynomial.X + Polynomial.C a)
  have hg : g ≠ 0 := by
    intro h0
    have hcomp : g.comp (Polynomial.X - Polynomial.C a) = f := by
      dsimp [g]
      rw [Polynomial.comp_assoc]
      simp
    rw [h0, Polynomial.zero_comp] at hcomp
    exact hf hcomp.symm
  have hex : ∃ i, g.coeff i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hg (Polynomial.ext (fun i => by simpa using hnone i))
  classical
  set k := Nat.find hex
  have hck : g.coeff k ≠ 0 := Nat.find_spec hex
  have hk_min : ∀ i < k, g.coeff i = 0 := fun i hi => by
    by_contra hne
    exact Nat.find_min hex hi hne
  have hk_pos : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    have hg0 : g.eval 0 = 0 := by
      dsimp [g]
      simpa [Polynomial.eval_comp] using hfa
    have hcoeff0 : g.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hg0
    rw [hk0] at hck
    exact hck hcoeff0
  set m := k - 1
  have hkm : k = m + 1 := by omega
  have hderiv_zero : ∀ j < m, g.derivative.coeff j = 0 := by
    intro j hj
    rw [Polynomial.coeff_derivative]
    have hjk : j + 1 < k := by omega
    rw [hk_min (j + 1) hjk, zero_mul]
  have hk_cast : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm_cast : (m : K) + 1 = (k : K) := by exact_mod_cast hkm.symm
  have hderiv_m : g.derivative.coeff m ≠ 0 := by
    rw [Polynomial.coeff_derivative, hm_cast, ← hkm]
    exact mul_ne_zero hck hk_cast
  obtain ⟨δ₁, hδ₁, h1⟩ := eval_near_zero_mul_pos g k hk_min hck
  obtain ⟨δ₂, hδ₂, h2⟩ := eval_near_zero_mul_pos g.derivative m hderiv_zero hderiv_m
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht_pos ht_lt => ?_⟩
  have ht1 : |t| < δ₁ := by
    rw [abs_of_pos ht_pos]
    exact lt_of_lt_of_le ht_lt (min_le_left _ _)
  have ht2 : |t| < δ₂ := by
    rw [abs_of_pos ht_pos]
    exact lt_of_lt_of_le ht_lt (min_le_right _ _)
  have hnt1 : |-t| < δ₁ := by simpa [abs_neg] using ht1
  have hnt2 : |-t| < δ₂ := by simpa [abs_neg] using ht2
  have hgderiv : g.derivative = f.derivative.comp (Polynomial.X + Polynomial.C a) := by
    dsimp [g]
    rw [Polynomial.derivative_comp]
    simp
  have heval_add : g.eval t = f.eval (a + t) := by
    dsimp [g]
    rw [Polynomial.eval_comp]
    simp [add_comm]
  have hdeval_add : g.derivative.eval t = f.derivative.eval (a + t) := by
    rw [hgderiv, Polynomial.eval_comp]
    simp [add_comm]
  have heval_sub : g.eval (-t) = f.eval (a - t) := by
    dsimp [g]
    rw [Polynomial.eval_comp]
    simp [sub_eq_neg_add]
  have hdeval_sub : g.derivative.eval (-t) = f.derivative.eval (a - t) := by
    rw [hgderiv, Polynomial.eval_comp]
    simp [sub_eq_neg_add]
  have hpos_add : 0 < g.eval t * (g.coeff k * t ^ k) := h1 t ht_pos.ne' ht1
  have hpos_dadd : 0 < g.derivative.eval t * (g.derivative.coeff m * t ^ m) := h2 t ht_pos.ne' ht2
  have hdm_eq : g.derivative.coeff m = g.coeff k * (k : K) := by
    rw [Polynomial.coeff_derivative, hm_cast, ← hkm]
  have hmul_pos_add : 0 < f.eval (a + t) * f.derivative.eval (a + t) := by
    rw [← heval_add, ← hdeval_add]
    have hprod : 0 < (g.eval t * (g.coeff k * t ^ k)) * (g.derivative.eval t * (g.derivative.coeff m * t ^ m)) :=
      mul_pos hpos_add hpos_dadd
    have hcoeff_pos : 0 < g.coeff k * t ^ k * (g.derivative.coeff m * t ^ m) := by
      rw [hdm_eq]
      have hk_gt : (0 : K) < k := Nat.cast_pos.mpr hk_pos
      have hsq : 0 < (g.coeff k) ^ 2 := sq_pos_of_ne_zero hck
      have ht_k : 0 < t ^ k := pow_pos ht_pos k
      have ht_m : 0 < t ^ m := pow_pos ht_pos m
      have : g.coeff k * t ^ k * (g.coeff k * (k : K) * t ^ m) = (g.coeff k) ^ 2 * (k : K) * t ^ k * t ^ m := by ring
      rw [this]
      exact mul_pos (mul_pos (mul_pos hsq hk_gt) ht_k) ht_m
    have hprod' : 0 < (g.eval t * g.derivative.eval t) * (g.coeff k * t ^ k * (g.derivative.coeff m * t ^ m)) := by
      have : (g.eval t * (g.coeff k * t ^ k)) * (g.derivative.eval t * (g.derivative.coeff m * t ^ m)) =
          (g.eval t * g.derivative.eval t) * (g.coeff k * t ^ k * (g.derivative.coeff m * t ^ m)) := by ring
      rwa [← this]
    exact pos_of_mul_pos_left hprod' hcoeff_pos.le
  have hpos_sub : 0 < g.eval (-t) * (g.coeff k * (-t) ^ k) := h1 (-t) (neg_ne_zero.mpr ht_pos.ne') hnt1
  have hpos_dsub : 0 < g.derivative.eval (-t) * (g.derivative.coeff m * (-t) ^ m) := h2 (-t) (neg_ne_zero.mpr ht_pos.ne') hnt2
  have hmul_neg_sub : f.eval (a - t) * f.derivative.eval (a - t) < 0 := by
    rw [← heval_sub, ← hdeval_sub]
    have hprod : 0 < (g.eval (-t) * (g.coeff k * (-t) ^ k)) * (g.derivative.eval (-t) * (g.derivative.coeff m * (-t) ^ m)) :=
      mul_pos hpos_sub hpos_dsub
    have hcoeff_neg : g.coeff k * (-t) ^ k * (g.derivative.coeff m * (-t) ^ m) < 0 := by
      have hpow_k : (-t) ^ k = (-t) ^ m * (-t) := by rw [hkm, pow_succ]
      rw [hdm_eq, hpow_k]
      have hk_gt : (0 : K) < k := Nat.cast_pos.mpr hk_pos
      have hsq1 : 0 < (g.coeff k) ^ 2 := sq_pos_of_ne_zero hck
      have hsq2 : 0 < ((-t) ^ m) ^ 2 := sq_pos_of_ne_zero (pow_ne_zero m (neg_ne_zero.mpr ht_pos.ne'))
      have hneg : (-t) < 0 := neg_lt_zero.mpr ht_pos
      have : g.coeff k * ((-t) ^ m * (-t)) * (g.coeff k * (k : K) * (-t) ^ m) =
          (g.coeff k) ^ 2 * (k : K) * ((-t) ^ m) ^ 2 * (-t) := by ring
      rw [this]
      exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hsq1 hk_gt) hsq2) hneg
    have hprod' : 0 < (g.eval (-t) * g.derivative.eval (-t)) * (g.coeff k * (-t) ^ k * (g.derivative.coeff m * (-t) ^ m)) := by
      have : (g.eval (-t) * (g.coeff k * (-t) ^ k)) * (g.derivative.eval (-t) * (g.derivative.coeff m * (-t) ^ m)) =
          (g.eval (-t) * g.derivative.eval (-t)) * (g.coeff k * (-t) ^ k * (g.derivative.coeff m * (-t) ^ m)) := by ring
      rwa [← this]
    exact neg_of_mul_pos_left hprod' hcoeff_neg.le
  exact ⟨hmul_pos_add, hmul_neg_sub⟩

lemma rolle_no_root_pos_contra {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (r : Polynomial K) {u v : K} (huv : u < v) (hruv : r.eval u = r.eval v)
    (hpos : ∀ c : K, u < c → c < v → 0 < r.derivative.eval c) : False := by
  set h : Polynomial K := r - Polynomial.C (r.eval u)
  have hhu : h.eval u = 0 := by simp [h]
  have hhv : h.eval v = 0 := by simp [h, hruv]
  have hhderiv : h.derivative = r.derivative := by simp [h]
  have hh_ne : h ≠ 0 := by
    intro h0
    have hd0 : r.derivative = 0 := by rw [← hhderiv, h0, Polynomial.derivative_zero]
    have hm : 0 < r.derivative.eval ((u + v) / 2) := hpos ((u + v) / 2) (by linarith) (by linarith)
    rw [hd0, Polynomial.eval_zero] at hm
    exact lt_irrefl 0 hm
  obtain ⟨δ, hδ_pos, hloc_u⟩ := local_poly_deriv_sign h u hh_ne hhu
  set t₀ := min (δ / 2) ((v - u) / 2)
  have ht₀_pos : 0 < t₀ := lt_min (half_pos hδ_pos) (half_pos (sub_pos.mpr huv))
  have ht₀_lt : t₀ < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
  set a₀ := u + t₀
  have hua₀ : u < a₀ := lt_add_of_pos_right u ht₀_pos
  have ha₀v : a₀ < v := by
    have : t₀ ≤ (v - u) / 2 := min_le_right _ _
    linarith
  have ha₀_pos : 0 < h.eval a₀ := by
    have hmul : 0 < h.eval a₀ * h.derivative.eval a₀ := (hloc_u t₀ ht₀_pos ht₀_lt).1
    have hd_pos : 0 < h.derivative.eval a₀ := by rw [hhderiv]; exact hpos a₀ hua₀ ha₀v
    exact pos_of_mul_pos_left hmul hd_pos.le
  classical
  set S : Finset K := h.roots.toFinset.filter (fun x => a₀ < x ∧ x ≤ v)
  have hv_mem : v ∈ S := by
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne]
    exact ⟨hhv, ha₀v, le_rfl⟩
  have hS_ne : S.Nonempty := ⟨v, hv_mem⟩
  set w := S.min' hS_ne
  have hw_mem : w ∈ S := Finset.min'_mem S hS_ne
  have hw_root : h.eval w = 0 := by
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne] at hw_mem
    exact hw_mem.1
  have ha₀w : a₀ < w := (Finset.mem_filter.mp hw_mem).2.1
  have hwv : w ≤ v := (Finset.mem_filter.mp hw_mem).2.2
  have hw_pos : ∀ x : K, a₀ ≤ x → x < w → 0 < h.eval x := by
    intro x hax hxw
    rcases eq_or_lt_of_le hax with rfl | hax_lt
    · exact ha₀_pos
    · by_contra hxle
      have hx_ne : h.eval x ≠ 0 := by
        intro hx0
        have hxS : x ∈ S := by
          rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne]
          exact ⟨hx0, hax_lt, le_trans hxw.le hwv⟩
        have hle : w ≤ x := Finset.min'_le S x hxS
        exact not_lt.mpr hle hxw
      have hx_neg : h.eval x < 0 := lt_of_le_of_ne (not_lt.mp hxle) hx_ne
      obtain ⟨c, hac, hcx, hc0⟩ := hIVT (-h) hax_lt (by simpa using ha₀_pos) (by simpa using hx_neg)
      have hcS : c ∈ S := by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne]
        refine ⟨?_, hac, le_trans (lt_trans hcx hxw).le hwv⟩
        simpa using hc0
      have hle : w ≤ c := Finset.min'_le S c hcS
      exact not_lt.mpr hle (lt_trans hcx hxw)
  obtain ⟨ε, hε_pos, hloc_w⟩ := local_poly_deriv_sign h w hh_ne hw_root
  set t₁ := min (ε / 2) ((w - a₀) / 2)
  have ht₁_pos : 0 < t₁ := lt_min (half_pos hε_pos) (half_pos (sub_pos.mpr ha₀w))
  have ht₁_lt : t₁ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε_pos)
  set y := w - t₁
  have hay : a₀ < y := by
    have : t₁ ≤ (w - a₀) / 2 := min_le_right _ _
    linarith
  have hyw : y < w := sub_lt_self w ht₁_pos
  have hy_pos : 0 < h.eval y := hw_pos y hay.le hyw
  have hdy_pos : 0 < h.derivative.eval y := by
    rw [hhderiv]
    exact hpos y (lt_trans hua₀ hay) (lt_of_lt_of_le hyw hwv)
  have hmul_neg : h.eval y * h.derivative.eval y < 0 := (hloc_w t₁ ht₁_pos ht₁_lt).2
  exact lt_irrefl 0 (lt_trans (mul_pos hy_pos hdy_pos) hmul_neg)

lemma poly_rolle {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (r : Polynomial K) {u v : K} (huv : u < v) (hruv : r.eval u = r.eval v) :
    ∃ c : K, u < c ∧ c < v ∧ r.derivative.eval c = 0 := by
  by_contra hno
  push Not at hno
  set m := (u + v) / 2
  have hum : u < m := by dsimp [m]; linarith
  have hmv : m < v := by dsimp [m]; linarith
  have hm_ne : r.derivative.eval m ≠ 0 := hno m hum hmv
  rcases lt_trichotomy (r.derivative.eval m) 0 with hm_neg | hm0 | hm_pos
  · have hneg_all : ∀ c : K, u < c → c < v → r.derivative.eval c < 0 := by
      intro c huc hcv
      rcases lt_trichotomy c m with hcm | rfl | hmc
      · by_contra hge
        have hpos_c : 0 < r.derivative.eval c := lt_of_le_of_ne (not_lt.mp hge) (hno c huc hcv).symm
        obtain ⟨z, hcz, hzm, hz0⟩ := hIVT (-r.derivative) hcm (by simpa using hpos_c) (by simpa using hm_neg)
        exact hno z (lt_trans huc hcz) (lt_trans hzm hmv) (by simpa using hz0)
      · exact hm_neg
      · by_contra hge
        have hpos_c : 0 < r.derivative.eval c := lt_of_le_of_ne (not_lt.mp hge) (hno c huc hcv).symm
        obtain ⟨z, hmz, hzc, hz0⟩ := hIVT r.derivative hmc hm_neg hpos_c
        exact hno z (lt_trans hum hmz) (lt_trans hzc hcv) hz0
    have hpos_neg : ∀ c : K, u < c → c < v → 0 < (-r).derivative.eval c := by
      intro c huc hcv
      rw [Polynomial.derivative_neg, Polynomial.eval_neg]
      exact neg_pos.mpr (hneg_all c huc hcv)
    exact rolle_no_root_pos_contra hIVT (-r) huv (by simp [hruv]) hpos_neg
  · exact hm_ne hm0
  · have hpos_all : ∀ c : K, u < c → c < v → 0 < r.derivative.eval c := by
      intro c huc hcv
      rcases lt_trichotomy c m with hcm | rfl | hmc
      · by_contra hle
        have hneg_c : r.derivative.eval c < 0 := lt_of_le_of_ne (not_lt.mp hle) (hno c huc hcv)
        obtain ⟨z, hcz, hzm, hz0⟩ := hIVT r.derivative hcm hneg_c hm_pos
        exact hno z (lt_trans huc hcz) (lt_trans hzm hmv) hz0
      · exact hm_pos
      · by_contra hle
        have hneg_c : r.derivative.eval c < 0 := lt_of_le_of_ne (not_lt.mp hle) (hno c huc hcv)
        obtain ⟨z, hmz, hzc, hz0⟩ := hIVT (-r.derivative) hmc (by simpa using hm_pos) (by simpa using hneg_c)
        exact hno z (lt_trans hum hmz) (lt_trans hzc hcv) (by simpa using hz0)
    exact rolle_no_root_pos_contra hIVT r huv hruv hpos_all

end Hilbert17H2Proof

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1.H2 := by
  intro K _ _ _ hIVT
  refine ⟨?_, Hilbert17H2Proof.asymptotic_leading_sign⟩
  intro p u v huv
  set r : Polynomial K := Polynomial.C (v - u) * p - Polynomial.C (p.eval v - p.eval u) * Polynomial.X
  have hruv : r.eval u = r.eval v := by
    dsimp [r]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  obtain ⟨c, huc, hcv, hc0⟩ := Hilbert17H2Proof.poly_rolle hIVT r huv hruv
  refine ⟨c, huc, hcv, ?_⟩
  have hrderiv : r.derivative = Polynomial.C (v - u) * p.derivative - Polynomial.C (p.eval v - p.eval u) := by
    dsimp [r]
    simp
  rw [hrderiv] at hc0
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at hc0
  linarith
