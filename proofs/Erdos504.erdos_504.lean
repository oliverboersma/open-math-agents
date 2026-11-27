import FormalConjectures.ErdosProblems.«504»
import Mathlib

section R1Section
/-
# Reduction of Erdős 504 (Erdős–Szekeres 1960) to its two published halves

- `H1` (known, Szekeres 1941): for every `t > 0` and `ε > 0` there are `2^t` points all of whose
  angles are below `π(1 - 1/t) + ε` (verbatim `erdos_504.variants.szekeres_upper`).
- `H2` (known, Erdős–Szekeres 1960): any `2^n` points, `n ≥ 3`, contain an angle above
  `π(1 - 1/n)` (verbatim `erdos_504.variants.erdos_szekeres_1960`).
- `main` identifies the supremum: `H2` puts `π(1 - 1/n)` in the set, `H1` bounds the set above.
-/
-- Credit: @senamakel

namespace OMA.Erdos504R1

open Real EuclideanGeometry

-- Szekeres (1941), upper-bound construction.
def H1 : Prop :=
  ∀ {t : ℕ}, 0 < t → ∀ {ε : ℝ}, 0 < ε →
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε

-- Erdős–Szekeres (1960), lower bound.
def H2 : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (S : Finset ℂ), S.card = 2 ^ n →
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r

theorem main : H1 → H2 → type_of% @Erdos504.erdos_504 := by
  intro h1 h2 n hn
  unfold Erdos504.minimaxAngle
  set a0 : ℝ := (1 - 1 / (n : ℝ)) * π with ha0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hinv : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]; exact_mod_cast (by omega : 1 ≤ n)
  have hinv0 : 0 < 1 / (n : ℝ) := by positivity
  have ha0nn : 0 ≤ a0 := mul_nonneg (by linarith) pi_pos.le
  have ha0le : a0 ≤ π := by nlinarith [pi_pos]
  have hbdd : BddAbove {α : ℝ | α ∈ Set.Icc 0 π ∧
      ∀ S : Finset ℂ, S.card = 2 ^ n →
        ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
          α ≤ EuclideanGeometry.angle x z y} := ⟨π, fun α hα => hα.1.2⟩
  have hmem : a0 ∈ {α : ℝ | α ∈ Set.Icc 0 π ∧
      ∀ S : Finset ℂ, S.card = 2 ^ n →
        ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
          α ≤ EuclideanGeometry.angle x z y} := by
    refine ⟨⟨ha0nn, ha0le⟩, fun S hS => ?_⟩
    obtain ⟨p, hp, q, hq, r, hr, hpq, hrq, hlt⟩ := h2 hn S hS
    refine ⟨p, hp, q, hq, r, hr, hpq, hrq, ?_, hlt.le⟩
    rintro rfl
    rw [EuclideanGeometry.angle_self_of_ne hpq] at hlt
    linarith
  apply le_antisymm
  · apply csSup_le ⟨a0, hmem⟩
    rintro α ⟨_, hα⟩
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    obtain ⟨S, hS, hang⟩ := h1 (t := n) (by omega) (ε := (α - a0) / 2) (by linarith)
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, _, hle⟩ := hα S hS
    have := hang x hx z hz y hy hxz hyz
    linarith
  · exact le_csSup hbdd hmem

end OMA.Erdos504R1
end R1Section

section H1Section
-- Step Erdos504.erdos_504.R1.H1: hypothesis H1 of reduction Erdos504.erdos_504.R1
-- Credit: @senamakel
-- Szekeres (1941) construction, by induction: double a shrunken copy of the previous set along the direction exp(i m pi / t).


open Real

namespace OMA.Erdos504Szekeres

lemma dir_angle_le (t : ℕ) (ht : 0 < t) (d : ℤ) (hd : ¬ (t : ℤ) ∣ d) (x y : ℝ)
    (hxy : x - y = (d : ℝ) * π / t) :
    |toIocMod Real.two_pi_pos (-π) (x - y)| ≤ (1 - 1 / (t : ℝ)) * π := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  set k := toIocDiv Real.two_pi_pos (-π) (x - y) with hk
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos (-π) (x - y)
  have hval : toIocMod Real.two_pi_pos (-π) (x - y) = ((d - 2 * k * t : ℤ) : ℝ) * π / t := by
    rw [toIocMod, ← hk, hxy]
    push_cast
    field_simp
    simp [zsmul_eq_mul]
    ring
  rw [hval] at hmem ⊢
  set e : ℤ := d - 2 * k * t with he
  obtain ⟨h1, h2⟩ := hmem
  have h1' : -(t : ℝ) < e := by
    rw [lt_div_iff₀ htR] at h1
    have : -(t : ℝ) * π < e * π := by linarith
    exact lt_of_mul_lt_mul_right this pi_pos.le
  have h2' : (e : ℝ) ≤ t := by
    rw [div_le_iff₀ htR] at h2
    have : (e : ℝ) * π ≤ t * π := by linarith
    exact le_of_mul_le_mul_right this pi_pos
  have h1z : -(t : ℤ) < e := by exact_mod_cast h1'
  have h2z : e ≤ (t : ℤ) := by exact_mod_cast h2'
  have hne0 : e ≠ 0 := by
    intro h0; apply hd; refine ⟨2 * k, ?_⟩; rw [he] at h0; linarith
  have hnet : e ≠ t := by
    intro h0; apply hd; refine ⟨2 * k + 1, ?_⟩; rw [he] at h0; linarith
  have habs : |e| ≤ (t : ℤ) - 1 := by
    rw [abs_le]; constructor <;> omega
  have habsR : |(e : ℝ)| ≤ (t : ℝ) - 1 := by exact_mod_cast habs
  rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos htR]
  rw [div_le_iff₀ htR]
  have : (1 - 1 / (t : ℝ)) * π * t = ((t : ℝ) - 1) * π := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right habsR pi_pos.le

lemma angle_dirs (t : ℕ) (ht : 0 < t) (a b : ℤ) (hd : ¬ (t : ℤ) ∣ (a - b)) :
    InnerProductGeometry.angle (Complex.exp (((a : ℝ) * π / t : ℝ) * Complex.I))
      (Complex.exp (((b : ℝ) * π / t : ℝ) * Complex.I)) ≤ (1 - 1 / (t : ℝ)) * π := by
  rw [Complex.angle_exp_exp]
  apply dir_angle_le t ht (a - b) hd
  push_cast; ring


open InnerProductGeometry in
lemma mixed_bound {x y d v : ℂ} {β δ : ℝ} (h1 : angle x d < δ) (h2 : angle y v < δ)
    (h3 : angle d v ≤ β) : angle x y < β + 2 * δ := by
  have a := angle_le_angle_add_angle x d y
  have b := angle_le_angle_add_angle d v y
  rw [angle_comm y v] at h2
  linarith

open InnerProductGeometry in
lemma both_bound {x y v : ℂ} {β δ : ℝ} (h1 : angle x v < δ) (h2 : angle y v < δ)
    (h3 : 0 ≤ β) : angle x y < β + 2 * δ := by
  have a := angle_le_angle_add_angle x v y
  rw [angle_comm y v] at h2
  linarith

lemma exp_add_t (t : ℕ) (ht : 0 < t) (m : ℕ) :
    Complex.exp (((((m : ℤ) + t : ℤ) : ℝ) * π / t : ℝ) * Complex.I) =
      -Complex.exp (((((m : ℤ)) : ℝ) * π / t : ℝ) * Complex.I) := by
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have : (((((m : ℤ) + t : ℤ) : ℝ) * π / t : ℝ) : ℂ) * Complex.I =
      (((((m : ℤ)) : ℝ) * π / t : ℝ) : ℂ) * Complex.I + π * Complex.I := by
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast; field_simp
  rw [this, Complex.exp_add, Complex.exp_pi_mul_I]; ring

open InnerProductGeometry in
lemma step (t m : ℕ) (ht : 0 < t) (hm : m < t) {δ : ℝ} (hδ : 0 < δ) (S : Finset ℂ)
    (hcard : S.card = 2 ^ m)
    (hdir : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ j : ℤ, 0 ≤ j % t ∧ j % t < m ∧
      angle (p - q) (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) < δ)
    (hang : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      angle (p - q) (r - q) < (1 - 1 / (t : ℝ)) * π + 2 * δ) :
    ∃ S' : Finset ℂ, S'.card = 2 ^ (m + 1) ∧
    (∀ p ∈ S', ∀ q ∈ S', p ≠ q → ∃ j : ℤ, 0 ≤ j % t ∧ j % t < m + 1 ∧
      angle (p - q) (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) < δ) ∧
    (∀ p ∈ S', ∀ q ∈ S', ∀ r ∈ S', p ≠ q → r ≠ q →
      angle (p - q) (r - q) < (1 - 1 / (t : ℝ)) * π + 2 * δ) := by
  set β := (1 - 1 / (t : ℝ)) * π with hβ
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hβ0 : 0 ≤ β := by
    have : 1 / (t : ℝ) ≤ 1 := by
      rw [div_le_one htR]; exact_mod_cast (by omega : 1 ≤ t)
    exact mul_nonneg (by linarith) pi_pos.le
  set u : ℂ := Complex.exp ((((m : ℤ) : ℝ) * π / t : ℝ) * Complex.I) with hu
  have hun : ‖u‖ = 1 := by rw [hu, Complex.norm_exp_ofReal_mul_I]
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hnu : -u = Complex.exp (((((m : ℤ) + t : ℤ) : ℝ) * π / t : ℝ) * Complex.I) :=
    (exp_add_t t ht m).symm
  -- continuity of the angle at (u, u)
  obtain ⟨ρ, hρ, hcont⟩ : ∃ ρ > 0, ∀ e : ℂ, ‖e‖ < ρ → angle (u + e) u < δ := by
    have hc : ContinuousAt (fun e : ℂ => angle (u + e) u) 0 := by
      have h := continuousAt_angle (x := (u + 0, u)) (by simpa using hu0) hu0
      exact h.comp (f := fun e : ℂ => (u + e, u)) (by fun_prop)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨ρ, hρ, h⟩ := hc δ hδ
    refine ⟨ρ, hρ, fun e he => ?_⟩
    have := h (x := e) (by simpa using he)
    simp only [add_zero, angle_self hu0, dist_zero_right, Real.norm_eq_abs] at this
    exact lt_of_abs_lt this
  have hcross : ∀ e : ℂ, ‖e‖ < ρ → angle (-(u + e)) (-u) < δ := by
    intro e he; rw [angle_neg_neg]; exact hcont e he
  -- bound on S
  set R : ℝ := ∑ s ∈ S, ‖s‖ with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun s _ => norm_nonneg s)
  have hsR : ∀ s ∈ S, ‖s‖ ≤ R := fun s hs =>
    Finset.single_le_sum (f := fun s => ‖s‖) (fun s _ => norm_nonneg s) hs
  set c : ℝ := min ρ 1 / (2 * R + 1) with hc
  have hmin : 0 < min ρ 1 := lt_min hρ one_pos
  have hc0 : 0 < c := by positivity
  have hsmall : ∀ s ∈ S, ∀ s' ∈ S, ‖c • (s - s')‖ < min ρ 1 := by
    intro s hs s' hs'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    have h1 : ‖s - s'‖ ≤ 2 * R := by
      have := norm_sub_le s s'; linarith [hsR s hs, hsR s' hs']
    calc c * ‖s - s'‖ ≤ c * (2 * R) := mul_le_mul_of_nonneg_left h1 hc0.le
      _ < c * (2 * R + 1) := by nlinarith
      _ = min ρ 1 := by rw [hc]; field_simp
  have hsmallρ : ∀ s ∈ S, ∀ s' ∈ S, ‖c • (s - s')‖ < ρ := fun s hs s' hs' =>
    lt_of_lt_of_le (hsmall s hs s' hs') (min_le_left _ _)
  set A := S.image (fun s => c • s) with hA
  set B := S.image (fun s => c • s + u) with hB
  have hinjA : Function.Injective (fun s : ℂ => c • s) := smul_right_injective ℂ hc0.ne'
  have hinjB : Function.Injective (fun s : ℂ => c • s + u) := fun a b h =>
    hinjA (add_right_cancel h)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨s', hs', hss⟩ := Finset.mem_image.mp hxB
    have : u = c • (s - s') := by rw [smul_sub, ← hss]; ring
    have h := hsmall s hs s' hs'
    rw [← this, hun] at h
    exact absurd (min_le_right ρ 1) (not_le.mpr h)
  refine ⟨A ∪ B, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjA,
      Finset.card_image_of_injective _ hinjB, hcard, pow_succ]; ring
  · intro p hp q hq hpq
    rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq <;>
    obtain ⟨sp, hsp, rfl⟩ := Finset.mem_image.mp hp <;>
    obtain ⟨sq, hsq, rfl⟩ := Finset.mem_image.mp hq
    · have hne : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne
      refine ⟨j, hj0, by omega, ?_⟩
      rw [← smul_sub, angle_smul_left_of_pos _ _ hc0]; exact hjd
    · refine ⟨(m : ℤ) + t, ?_, ?_, ?_⟩
      · exact Int.emod_nonneg _ (by exact_mod_cast ht.ne')
      · rw [Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]; omega
      · rw [← hnu]
        have : c • sp - (c • sq + u) = -(u + c • (sq - sp)) := by rw [smul_sub]; ring
        rw [this]; exact hcross _ (hsmallρ sq hsq sp hsp)
    · refine ⟨(m : ℤ), by omega, ?_, ?_⟩
      · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      · have : c • sp + u - c • sq = u + c • (sp - sq) := by rw [smul_sub]; ring
        rw [this]; exact hcont _ (hsmallρ sp hsp sq hsq)
    · have hne : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne
      refine ⟨j, hj0, by omega, ?_⟩
      have : c • sp + u - (c • sq + u) = c • (sp - sq) := by rw [smul_sub]; ring
      rw [this, angle_smul_left_of_pos _ _ hc0]; exact hjd
  · have gu : ∀ j : ℤ, 0 ≤ j % t → j % t < m →
        angle (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) u ≤ β := by
      intro j hj0 hj
      apply angle_dirs t ht j m
      intro hdv
      have h := (Int.modEq_iff_dvd.mpr hdv)
      unfold Int.ModEq at h
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
      omega
    have gnu : ∀ j : ℤ, 0 ≤ j % t → j % t < m →
        angle (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (-u) ≤ β := by
      intro j hj0 hj
      rw [hnu]
      apply angle_dirs t ht j ((m : ℤ) + t)
      intro hdv
      have h := (Int.modEq_iff_dvd.mpr hdv)
      unfold Int.ModEq at h
      rw [Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)] at h
      omega
    intro p hp q hq r hr hpq hrq
    rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq <;>
    rcases Finset.mem_union.mp hr with hr | hr <;>
    obtain ⟨sp, hsp, rfl⟩ := Finset.mem_image.mp hp <;>
    obtain ⟨sq, hsq, rfl⟩ := Finset.mem_image.mp hq <;>
    obtain ⟨sr, hsr, rfl⟩ := Finset.mem_image.mp hr
    · -- A A A
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      rw [← smul_sub, ← smul_sub, angle_smul_left_of_pos _ _ hc0,
        angle_smul_right_of_pos _ _ hc0]
      exact hang sp hsp sq hsq sr hsr hne1 hne2
    · -- A A B
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne1
      have e1 : c • sp - c • sq = c • (sp - sq) := by rw [smul_sub]
      have e2 : c • sr + u - c • sq = u + c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := u) ?_
        (hcont _ (hsmallρ sr hsr sq hsq)) (gu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- A B A
      have e1 : c • sp - (c • sq + u) = -(u + c • (sq - sp)) := by rw [smul_sub]; ring
      have e2 : c • sr - (c • sq + u) = -(u + c • (sq - sr)) := by rw [smul_sub]; ring
      rw [e1, e2]
      exact both_bound (hcross _ (hsmallρ sq hsq sp hsp)) (hcross _ (hsmallρ sq hsq sr hsr)) hβ0
    · -- A B B
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sr hsr sq hsq hne2
      have e1 : c • sp - (c • sq + u) = -(u + c • (sq - sp)) := by rw [smul_sub]; ring
      have e2 : c • sr + u - (c • sq + u) = c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2, angle_comm]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := -u) ?_
        (hcross _ (hsmallρ sq hsq sp hsp)) (gnu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- B A A
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sr hsr sq hsq hne2
      have e1 : c • sp + u - c • sq = u + c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr - c • sq = c • (sr - sq) := by rw [smul_sub]
      rw [e1, e2, angle_comm]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := u) ?_
        (hcont _ (hsmallρ sp hsp sq hsq)) (gu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- B A B
      have e1 : c • sp + u - c • sq = u + c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr + u - c • sq = u + c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2]
      exact both_bound (hcont _ (hsmallρ sp hsp sq hsq)) (hcont _ (hsmallρ sr hsr sq hsq)) hβ0
    · -- B B A
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      obtain ⟨j, hj0, hj, hjd⟩ := hdir sp hsp sq hsq hne1
      have e1 : c • sp + u - (c • sq + u) = c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr - (c • sq + u) = -(u + c • (sq - sr)) := by rw [smul_sub]; ring
      rw [e1, e2]
      refine mixed_bound (d := Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) (v := -u) ?_
        (hcross _ (hsmallρ sq hsq sr hsr)) (gnu j hj0 hj)
      rw [angle_smul_left_of_pos _ _ hc0]; exact hjd
    · -- B B B
      have hne1 : sp ≠ sq := fun h => hpq (by rw [h])
      have hne2 : sr ≠ sq := fun h => hrq (by rw [h])
      have e1 : c • sp + u - (c • sq + u) = c • (sp - sq) := by rw [smul_sub]; ring
      have e2 : c • sr + u - (c • sq + u) = c • (sr - sq) := by rw [smul_sub]; ring
      rw [e1, e2, angle_smul_left_of_pos _ _ hc0, angle_smul_right_of_pos _ _ hc0]
      exact hang sp hsp sq hsq sr hsr hne1 hne2

lemma build (t : ℕ) (ht : 0 < t) {δ : ℝ} (hδ : 0 < δ) : ∀ m : ℕ, m ≤ t →
    ∃ S : Finset ℂ, S.card = 2 ^ m ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ j : ℤ, 0 ≤ j % t ∧ j % t < m ∧
      InnerProductGeometry.angle (p - q) (Complex.exp (((j : ℝ) * π / t : ℝ) * Complex.I)) < δ) ∧
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      InnerProductGeometry.angle (p - q) (r - q) < (1 - 1 / (t : ℝ)) * π + 2 * δ) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨{0}, by simp, ?_, ?_⟩
    · intro p hp q hq hpq
      simp only [Finset.mem_singleton] at hp hq
      exact absurd (hp.trans hq.symm) hpq
    · intro p hp q hq r hr hpq
      simp only [Finset.mem_singleton] at hp hq
      exact absurd (hp.trans hq.symm) hpq
  | succ k ih =>
    intro hk
    obtain ⟨S, h1, h2, h3⟩ := ih (by omega)
    exact step t k ht (by omega) hδ S h1 h2 h3

theorem szekeres_upper {t : ℕ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε := by
  obtain ⟨S, h1, _, h3⟩ := build t ht (δ := ε / 2) (by positivity) t le_rfl
  refine ⟨S, h1, fun p hp q hq r hr hpq hrq => ?_⟩
  have := h3 p hp q hq r hr hpq hrq
  rw [EuclideanGeometry.angle]
  simp only [vsub_eq_sub]
  linarith

end OMA.Erdos504Szekeres

theorem h1_proof : OMA.Erdos504R1.H1 := by
  intro t ht ε hε
  exact OMA.Erdos504Szekeres.szekeres_upper ht hε
end H1Section

section H2Section
-- Step Erdos504.erdos_504.R1.H2: hypothesis H2 of reduction Erdos504.erdos_504.R1
-- Credit: @graydeveloper01
--
-- Theorem (Erdos and Szekeres 1960): any 2^n points of the plane (n >= 3) contain an
-- angle strictly greater than (1 - 1/n) * pi.
--
-- Mathematical credit: the sector colouring and the 2^n bound are due to G. Szekeres
-- (On an extremum problem in the plane, Amer. J. Math. 63, 1941); the rigidity of the
-- colouring at exactly 2^n points and the theorem itself are due to P. Erdos and
-- G. Szekeres (On some extremum problems in elementary geometry, Ann. Univ. Sci.
-- Budapest 3-4, 1960-61).  An independent Lean formalization of the same theorem exists
-- at github.com/ToshiDad/erdos-504; the proof below was written independently of it
-- and follows a different, shorter route for the equality case.
--
-- Outline (theta = pi / n, all angles assumed <= pi - theta, for a contradiction).
-- 1. Fix a frame angle a.  A direction lies in sector k when its polar angle is in
--    [a + k theta, a + (k+1) theta).  For a point u, sides u is the set of sectors k in
--    which u has a forward neighbour.  The angle bound forbids a forward and a backward
--    neighbour in one sector, so u -> sides u is injective, hence bijective onto the
--    subsets of Fin n because there are exactly 2^n points (sides_surj).
-- 2. The point whose side set is everything is extreme; its neighbours fill a wedge
--    of opening at most pi - theta (exists_wedge).  Bijectivity forces a neighbour on
--    the last boundary ray of every such wedge, and that neighbour again carries a
--    wedge, turned by theta (step).  Four steps give five consecutive vertices
--    Q0 .. Q4 of an equiangular convex polygon containing all the points.
-- 3. For consecutive vertices A B C D, with the frame along B -> C, the point Y whose
--    side set omits exactly sectors 0 and n-1 lies in the thin triangle over the edge
--    B C with base angles theta, but not below A or D.  Comparing heights gives
--    2 cos(theta) |AB| < |BC| and 2 cos(theta) |CD| < |BC|, hence both neighbouring
--    edges are strictly shorter than B C (core; this uses n >= 3).  Applying this to
--    the edges Q1 Q2 and Q2 Q3 gives |Q2 Q3| < |Q1 Q2| < |Q2 Q3|, a contradiction.

namespace OMA.ES504

open Real

def Pol (w : ℂ) (φ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ w = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)

lemma Pol.ne_zero {w : ℂ} {φ : ℝ} (h : Pol w φ) : w ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := h
  exact mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)

lemma Pol.neg {w : ℂ} {φ : ℝ} (h : Pol w φ) : Pol (-w) (φ + π) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, hr, ?_⟩
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

lemma Pol.neg' {w : ℂ} {φ : ℝ} (h : Pol w φ) : Pol (-w) (φ - π) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, hr, ?_⟩
  push_cast
  rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
  field_simp

lemma Pol.norm_eq {w : ℂ} {φ : ℝ} {r : ℝ} (hr : 0 < r)
    (h : w = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) : ‖w‖ = r := by
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr.le]

lemma Pol.unique {w : ℂ} {φ ψ : ℝ} (h1 : Pol w φ) (h2 : Pol w ψ)
    (h : |φ - ψ| < 2 * π) : φ = ψ := by
  obtain ⟨r, hr, e1⟩ := h1
  obtain ⟨s, hs, e2⟩ := h2
  have n1 := Pol.norm_eq hr e1
  have n2 := Pol.norm_eq hs e2
  have hrs : r = s := by rw [← n1, ← n2]
  subst hrs
  rw [e1] at e2
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e3 := mul_left_cancel₀ hr0 e2
  rw [Complex.exp_eq_exp_iff_exists_int] at e3
  obtain ⟨m, hm⟩ := e3
  have hm' : φ = ψ + m * (2 * π) := by
    have := congrArg Complex.im hm
    simpa using this
  have hpi := Real.pi_pos
  rw [abs_lt] at h
  have hm1 : (-1 : ℝ) < m := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have hm2 : (m : ℝ) < 1 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have hm0 : m = 0 := by
    have a1 : (-1 : ℤ) < m := by exact_mod_cast hm1
    have a2 : m < (1 : ℤ) := by exact_mod_cast hm2
    omega
  rw [hm'] ; simp [hm0]

lemma pol_exists {w : ℂ} (hw : w ≠ 0) (c : ℝ) :
    ∃ φ : ℝ, c ≤ φ ∧ φ < c + 2 * π ∧ Pol w φ := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  refine ⟨toIcoMod h2 c (Complex.arg w), (toIcoMod_mem_Ico h2 c _).1,
    (toIcoMod_mem_Ico h2 c _).2, ‖w‖, norm_pos_iff.mpr hw, ?_⟩
  have e : Complex.exp ((toIcoMod h2 c (Complex.arg w) : ℝ) * Complex.I)
      = Complex.exp ((Complex.arg w : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-(toIcoDiv h2 c (Complex.arg w)), ?_⟩
    rw [toIcoMod]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e, Complex.norm_mul_exp_arg_mul_I]

lemma pol_arg {w : ℂ} (hw : w ≠ 0) : Pol w (Complex.arg w) :=
  ⟨‖w‖, norm_pos_iff.mpr hw, (Complex.norm_mul_exp_arg_mul_I w).symm⟩

noncomputable def hgt (a : ℝ) (w : ℂ) : ℝ := w.im * Real.cos a - w.re * Real.sin a

lemma hgt_sub (a : ℝ) (z w : ℂ) : hgt a (z - w) = hgt a z - hgt a w := by
  simp only [hgt, Complex.sub_re, Complex.sub_im]; ring

lemma hgt_exp (a : ℝ) {w : ℂ} {r φ : ℝ}
    (h : w = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) :
    hgt a w = r * Real.sin (φ - a) := by
  subst h
  simp only [hgt, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_sub]
  ring

lemma hgt_add_sub (a θ : ℝ) (w : ℂ) :
    hgt (a + θ) w + hgt (a - θ) w = 2 * Real.cos θ * hgt a w := by
  simp only [hgt, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]; ring

lemma Pol.data {w : ℂ} {φ : ℝ} (h : Pol w φ) :
    ∃ r : ℝ, 0 < r ∧ ‖w‖ = r ∧ ∀ a : ℝ, hgt a w = r * Real.sin (φ - a) := by
  obtain ⟨r, hr, e⟩ := h
  exact ⟨r, hr, Pol.norm_eq hr e, fun a => hgt_exp a e⟩

lemma angle_pol {p q r : ℂ} {φ ψ : ℝ} (h1 : Pol (p - q) φ) (h2 : Pol (r - q) ψ)
    (h : |φ - ψ| ≤ π) : EuclideanGeometry.angle p q r = |φ - ψ| := by
  obtain ⟨s, hs, e1⟩ := h1
  obtain ⟨t, ht, e2⟩ := h2
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [e1, e2]
  have c1 : ((s : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
      = s • Complex.exp ((φ : ℂ) * Complex.I) := by simp
  have c2 : ((t : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      = t • Complex.exp ((ψ : ℂ) * Complex.I) := by simp
  rw [c1, c2, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]
  unfold InnerProductGeometry.angle
  have hin : inner ℝ (Complex.exp ((φ : ℂ) * Complex.I)) (Complex.exp ((ψ : ℂ) * Complex.I))
      = Real.cos (|φ - ψ|) := by
    rw [Real.cos_abs, Real.cos_sub, Complex.inner]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hin, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
  simp only [mul_one, div_one]
  exact Real.arccos_cos (abs_nonneg _) h

structure Cfg (θ : ℝ) (n : ℕ) (S : Finset ℂ) : Prop where
  hθ : 0 < θ
  hn : (n : ℝ) * θ = π
  hn3 : 3 ≤ n
  hG : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q → EuclideanGeometry.angle p q r ≤ π - θ
  hcard : S.card = 2 ^ n

def Sec (θ a : ℝ) (k : ℕ) (w : ℂ) : Prop :=
  ∃ φ : ℝ, a + k * θ ≤ φ ∧ φ < a + k * θ + θ ∧ Pol w φ

def sides (θ : ℝ) (n : ℕ) (S : Finset ℂ) (a : ℝ) (u : ℂ) : Set (Fin n) :=
  {k | ∃ v ∈ S, Sec θ a k (v - u)}

def Wedge (θ : ℝ) (S : Finset ℂ) (Q : ℂ) (a : ℝ) : Prop :=
  ∀ X ∈ S, X ≠ Q → ∃ φ : ℝ, a ≤ φ ∧ φ ≤ a + π - θ ∧ Pol (X - Q) φ

variable {θ : ℝ} {n : ℕ} {S : Finset ℂ}

lemma Cfg.three (G : Cfg θ n S) : 3 * θ ≤ π := by
  have h : (3 : ℝ) ≤ n := by exact_mod_cast G.hn3
  have := G.hn
  have := G.hθ
  nlinarith

lemma Cfg.idx (G : Cfg θ n S) {k : ℕ} (hk : k < n) :
    0 ≤ (k : ℝ) * θ ∧ (k : ℝ) * θ + θ ≤ π := by
  have h : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have := G.hn
  have := G.hθ
  constructor
  · positivity
  · nlinarith

lemma Cfg.cast_last (G : Cfg θ n S) : ((n - 1 : ℕ) : ℝ) * θ = π - θ := by
  have h : 1 ≤ n := by have := G.hn3; omega
  rw [Nat.cast_sub h]
  have := G.hn
  push_cast
  linarith

lemma sec_total (G : Cfg θ n S) {w : ℂ} (hw : w ≠ 0) (a : ℝ) :
    ∃ k, k < n ∧ (Sec θ a k w ∨ Sec θ a k (-w)) := by
  have hθ := G.hθ
  have hn := G.hn
  obtain ⟨φ, h1, h2, hp⟩ := pol_exists hw a
  have key : ∀ ψ : ℝ, a ≤ ψ → ψ < a + π →
      ∃ k, k < n ∧ a + (k : ℝ) * θ ≤ ψ ∧ ψ < a + (k : ℝ) * θ + θ := by
    intro ψ h1 h2
    have hnn : 0 ≤ (ψ - a) / θ := div_nonneg (by linarith) hθ.le
    refine ⟨⌊(ψ - a) / θ⌋₊, ?_, ?_, ?_⟩
    · have h3 : ((⌊(ψ - a) / θ⌋₊ : ℕ) : ℝ) ≤ (ψ - a) / θ := Nat.floor_le hnn
      have h4 : (ψ - a) / θ < n := by rw [div_lt_iff₀ hθ]; linarith
      exact_mod_cast lt_of_le_of_lt h3 h4
    · have h3 : ((⌊(ψ - a) / θ⌋₊ : ℕ) : ℝ) ≤ (ψ - a) / θ := Nat.floor_le hnn
      rw [le_div_iff₀ hθ] at h3
      linarith
    · have h3 := Nat.lt_floor_add_one ((ψ - a) / θ)
      rw [div_lt_iff₀ hθ] at h3
      linarith
  by_cases hc : φ < a + π
  · obtain ⟨k, hk, b1, b2⟩ := key φ h1 hc
    exact ⟨k, hk, Or.inl ⟨φ, b1, b2, hp⟩⟩
  · rw [not_lt] at hc
    obtain ⟨k, hk, b1, b2⟩ := key (φ - π) (by linarith) (by linarith)
    exact ⟨k, hk, Or.inr ⟨φ - π, b1, b2, hp.neg'⟩⟩

lemma sec_clash (G : Cfg θ n S) {a : ℝ} {k : ℕ} {u v w : ℂ}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (h1 : Sec θ a k (v - u)) (h2 : Sec θ a k (u - w)) : False := by
  obtain ⟨φ, a1, a2, p1⟩ := h1
  obtain ⟨ψ, b1, b2, p2⟩ := h2
  have hθ := G.hθ
  have h3 := G.three
  have hvu : v ≠ u := fun h => p1.ne_zero (by rw [h, sub_self])
  have hwu : w ≠ u := fun h => p2.ne_zero (by rw [h, sub_self])
  have hg := G.hG v hv u hu w hw hvu hwu
  by_cases hc : ψ ≤ φ
  · have p3 : Pol (w - u) (ψ + π) := by
      have := p2.neg
      rwa [neg_sub] at this
    have hab : |φ - (ψ + π)| = π - (φ - ψ) := by
      rw [abs_of_nonpos (by linarith)]; ring
    have := angle_pol p1 p3 (by rw [hab]; linarith)
    rw [this, hab] at hg
    linarith
  · rw [not_le] at hc
    have p3 : Pol (w - u) (ψ - π) := by
      have := p2.neg'
      rwa [neg_sub] at this
    have hab : |φ - (ψ - π)| = π - (ψ - φ) := by
      rw [abs_of_nonneg (by linarith)]; ring
    have := angle_pol p1 p3 (by rw [hab]; linarith)
    rw [this, hab] at hg
    linarith

lemma edge_alt (G : Cfg θ n S) (a : ℝ) {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    ∃ k, ∃ hk : k < n,
      (Sec θ a k (v - u) ∧ (⟨k, hk⟩ : Fin n) ∈ sides θ n S a u ∧
        (⟨k, hk⟩ : Fin n) ∉ sides θ n S a v) ∨
      (Sec θ a k (u - v) ∧ (⟨k, hk⟩ : Fin n) ∈ sides θ n S a v ∧
        (⟨k, hk⟩ : Fin n) ∉ sides θ n S a u) := by
  obtain ⟨k, hk, h | h⟩ := sec_total G (sub_ne_zero.mpr (Ne.symm huv)) a
  · refine ⟨k, hk, Or.inl ⟨h, ⟨v, hv, h⟩, ?_⟩⟩
    rintro ⟨w, hw, hsec⟩
    exact sec_clash G hv hw hu hsec h
  · rw [neg_sub] at h
    refine ⟨k, hk, Or.inr ⟨h, ⟨u, hu, h⟩, ?_⟩⟩
    rintro ⟨w, hw, hsec⟩
    exact sec_clash G hu hw hv hsec h

lemma sides_surj (G : Cfg θ n S) (a : ℝ) (T : Set (Fin n)) :
    ∃ u ∈ S, sides θ n S a u = T := by
  classical
  have hinj : Set.InjOn (sides θ n S a) (S : Set ℂ) := by
    intro u hu v hv he
    by_contra huv
    obtain ⟨k, hk, h | h⟩ := edge_alt G a hu hv huv
    · exact h.2.2 (he ▸ h.2.1)
    · exact h.2.2 (he.symm ▸ h.2.1)
  have hcard : (S.image (sides θ n S a)).card = Fintype.card (Set (Fin n)) := by
    rw [Finset.card_image_of_injOn hinj, G.hcard, Fintype.card_set, Fintype.card_fin]
  have huniv := Finset.eq_univ_of_card _ hcard
  have hT : T ∈ S.image (sides θ n S a) := by rw [huniv]; exact Finset.mem_univ _
  obtain ⟨u, hu, e⟩ := Finset.mem_image.mp hT
  exact ⟨u, hu, e⟩

lemma nbr_exists (G : Cfg θ n S) (a : ℝ) {Q : ℂ} (hQ : Q ∈ S) {k : ℕ} (hk : k < n) :
    ∃ v ∈ S, Sec θ a k (v - Q) ∨ Sec θ a k (Q - v) := by
  obtain ⟨u, hu, hs⟩ := sides_surj G a
    {j | ¬ (j ∈ sides θ n S a Q ↔ j = (⟨k, hk⟩ : Fin n))}
  have hmem : ∀ j : Fin n, j ∈ sides θ n S a u ↔
      ¬ (j ∈ sides θ n S a Q ↔ j = (⟨k, hk⟩ : Fin n)) := by
    intro j; rw [hs]; rfl
  have hne : Q ≠ u := by
    intro h
    rw [← h] at hmem
    have := hmem ⟨k, hk⟩
    tauto
  obtain ⟨j, hj, h | h⟩ := edge_alt G a hQ hu hne
  · have hjk : (⟨j, hj⟩ : Fin n) = ⟨k, hk⟩ := by
      have := hmem ⟨j, hj⟩
      have h1 := h.2.1
      have h2 := h.2.2
      tauto
    have e : j = k := by simpa using hjk
    subst e
    exact ⟨u, hu, Or.inl h.1⟩
  · have hjk : (⟨j, hj⟩ : Fin n) = ⟨k, hk⟩ := by
      have := hmem ⟨j, hj⟩
      have h1 := h.2.1
      have h2 := h.2.2
      tauto
    have e : j = k := by simpa using hjk
    subst e
    exact ⟨u, hu, Or.inr h.1⟩

lemma exists_wedge (G : Cfg θ n S) : ∃ Q ∈ S, ∃ a : ℝ, Wedge θ S Q a := by
  have hθ := G.hθ
  have hπ := Real.pi_pos
  obtain ⟨Q, hQ, hs⟩ := sides_surj G 0 Set.univ
  have hfw : ∀ X ∈ S, X ≠ Q → 0 ≤ Complex.arg (X - Q) ∧ Complex.arg (X - Q) < π := by
    intro X hX hXQ
    obtain ⟨k, hk, h | h⟩ := edge_alt G 0 hQ hX (Ne.symm hXQ)
    · obtain ⟨φ, b1, b2, hp⟩ := h.1
      obtain ⟨i0, i1⟩ := G.idx hk
      have e : Complex.arg (X - Q) = φ := Pol.unique (pol_arg hp.ne_zero) hp (by
        have := Complex.neg_pi_lt_arg (X - Q)
        have := Complex.arg_le_pi (X - Q)
        rw [abs_lt]; constructor <;> linarith)
      rw [e]; constructor <;> linarith
    · exact absurd (hs ▸ Set.mem_univ _) h.2.2
  have hne : (S.erase Q).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hQ, G.hcard]
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := G.hn3; omega)
    omega
  obtain ⟨X0, hX0, hmin⟩ :=
    Finset.exists_min_image (S.erase Q) (fun X => Complex.arg (X - Q)) hne
  refine ⟨Q, hQ, Complex.arg (X0 - Q), ?_⟩
  intro X hX hXQ
  have hX0' := Finset.mem_erase.mp hX0
  have h0 := hfw X0 hX0'.2 hX0'.1
  have h1 := hfw X hX hXQ
  have hm : Complex.arg (X0 - Q) ≤ Complex.arg (X - Q) :=
    hmin X (Finset.mem_erase.mpr ⟨hXQ, hX⟩)
  have ha := angle_pol (pol_arg (sub_ne_zero.mpr hX0'.1)) (pol_arg (sub_ne_zero.mpr hXQ))
    (by rw [abs_le]; constructor <;> linarith)
  have hg := G.hG X0 hX0'.2 Q hQ X hX hX0'.1 hXQ
  rw [ha, abs_of_nonpos (by linarith)] at hg
  exact ⟨Complex.arg (X - Q), hm, by linarith, pol_arg (sub_ne_zero.mpr hXQ)⟩

lemma step (G : Cfg θ n S) {Q : ℂ} (hQ : Q ∈ S) {a : ℝ} (hW : Wedge θ S Q a) :
    ∃ R ∈ S, Pol (Q - R) (a - θ) ∧ Wedge θ S R (a - θ) := by
  have hθ := G.hθ
  have hπ := Real.pi_pos
  have h3 := G.three
  have hn1 : n - 1 < n := by have := G.hn3; omega
  have hcast := G.cast_last
  obtain ⟨u, hu, h⟩ := nbr_exists G a hQ hn1
  have huQ : u ≠ Q := by
    intro e
    rcases h with h | h
    · obtain ⟨φ, -, -, hp⟩ := h
      exact hp.ne_zero (by rw [e, sub_self])
    · obtain ⟨φ, -, -, hp⟩ := h
      exact hp.ne_zero (by rw [e, sub_self])
  obtain ⟨ψ, c1, c2, hpψ⟩ := hW u hu huQ
  have hpol : Pol (u - Q) (a + π - θ) := by
    rcases h with h | h
    · obtain ⟨φ, b1, b2, hp⟩ := h
      rw [hcast] at b1 b2
      have e := Pol.unique hp hpψ (by rw [abs_lt]; constructor <;> linarith)
      have e' : ψ = a + π - θ := by linarith
      rw [← e']; exact hpψ
    · exfalso
      obtain ⟨φ, b1, b2, hp⟩ := h
      rw [hcast] at b1 b2
      have hp' : Pol (u - Q) (φ + π) := by
        have := hp.neg
        rwa [neg_sub] at this
      have e := Pol.unique hp' hpψ (by rw [abs_lt]; constructor <;> linarith)
      linarith
  have hQu : Pol (Q - u) (a - θ) := by
    have := hpol.neg'
    rw [neg_sub] at this
    have e : a + π - θ - π = a - θ := by ring
    rwa [e] at this
  refine ⟨u, hu, hQu, ?_⟩
  intro X hX hXu
  by_cases hXQ : X = Q
  · rw [hXQ]
    exact ⟨a - θ, le_refl _, by linarith, hQu⟩
  · obtain ⟨φ, d1, d2, hpX⟩ := hW X hX hXQ
    obtain ⟨χ, e1, e2, hpχ⟩ := pol_exists (sub_ne_zero.mpr hXu) (a - θ)
    obtain ⟨r1, hr1, -, H1⟩ := hpX.data
    obtain ⟨r2, hr2, -, H2⟩ := hQu.data
    obtain ⟨r3, hr3, -, H3⟩ := hpχ.data
    have hh : hgt (a - θ) (X - u) = hgt (a - θ) (X - Q) + hgt (a - θ) (Q - u) := by
      rw [hgt_sub, hgt_sub, hgt_sub]; ring
    rw [H1, H2, H3, sub_self, Real.sin_zero, mul_zero, add_zero] at hh
    have s1 : 0 ≤ Real.sin (φ - (a - θ)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have s3 : 0 ≤ Real.sin (χ - (a - θ)) := by
      have h0 : 0 ≤ r3 * Real.sin (χ - (a - θ)) := by rw [hh]; positivity
      exact (mul_nonneg_iff_of_pos_left hr3).mp h0
    have hχ : χ - (a - θ) ≤ π := by
      by_contra hc
      rw [not_le] at hc
      have hneg : Real.sin (χ - (a - θ) - 2 * π) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
      rw [Real.sin_sub_two_pi] at hneg
      linarith
    have ha := angle_pol hQu hpχ (by rw [abs_le]; constructor <;> linarith)
    have hg := G.hG Q hQ u hu X hX (Ne.symm huQ) hXu
    rw [ha, abs_of_nonpos (by linarith)] at hg
    exact ⟨χ, e1, by linarith, hpχ⟩

lemma core (G : Cfg θ n S) {A B C D : ℂ} {a : ℝ}
    (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hD : D ∈ S)
    (wA : Wedge θ S A (a - θ)) (wB : Wedge θ S B a) (wC : Wedge θ S C (a + θ))
    (wD : Wedge θ S D (a + θ + θ))
    (pBA : Pol (B - A) (a - θ)) (pCB : Pol (C - B) a) (pDC : Pol (D - C) (a + θ)) :
    ‖B - A‖ < ‖C - B‖ ∧ ‖D - C‖ < ‖C - B‖ := by
  have hθ := G.hθ
  have hπ := Real.pi_pos
  have h3 := G.three
  have hn0 : 0 < n := by have := G.hn3; omega
  have hn1 : n - 1 < n := by omega
  have hcast := G.cast_last
  obtain ⟨Y, hY, hsY⟩ := sides_surj G a {j : Fin n | j.val ≠ 0 ∧ j.val ≠ n - 1}
  have Ymem : ∀ k (hk : k < n),
      (⟨k, hk⟩ : Fin n) ∈ sides θ n S a Y ↔ (k ≠ 0 ∧ k ≠ n - 1) := by
    intro k hk; rw [hsY]; rfl
  have kb : ∀ k, k < n → 0 ≤ (k : ℝ) * θ ∧ (k : ℝ) * θ + θ ≤ π := fun k hk => G.idx hk
  have kpos : ∀ k : ℕ, k ≠ 0 → θ ≤ (k : ℝ) * θ := by
    intro k hk
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  have klast : ∀ k, k < n → k ≠ n - 1 → (k : ℝ) * θ + θ ≤ π - θ := by
    intro k hk hk'
    have h2 : k + 2 ≤ n := by omega
    have h2' : (k : ℝ) + 2 ≤ n := by exact_mod_cast h2
    have := G.hn
    nlinarith
  have k0 : ∀ k : ℕ, k = 0 → (k : ℝ) * θ = 0 := by
    intro k hk; rw [hk]; simp
  have kl : ∀ k : ℕ, k = n - 1 → (k : ℝ) * θ = π - θ := by
    intro k hk; rw [hk]; exact hcast
  have ksplit : ∀ k : ℕ, ¬ (k ≠ 0 ∧ k ≠ n - 1) → k = 0 ∨ k = n - 1 := by
    intro k hk; by_contra hc; rw [not_or] at hc; exact hk hc
  -- Y is none of the four polygon vertices
  have YneB : Y ≠ B := by
    intro e
    have hm : (⟨0, hn0⟩ : Fin n) ∈ sides θ n S a Y := by
      rw [e]
      refine ⟨C, hC, ?_⟩
      show Sec θ a 0 (C - B)
      exact ⟨a, by simp, by simpa using hθ, pCB⟩
    exact ((Ymem 0 hn0).mp hm).1 rfl
  have YneC : Y ≠ C := by
    intro e
    obtain ⟨v, hv, h | h⟩ := nbr_exists G a hC hn1
    · have hm : (⟨n - 1, hn1⟩ : Fin n) ∈ sides θ n S a Y := by rw [e]; exact ⟨v, hv, h⟩
      exact ((Ymem _ hn1).mp hm).2 rfl
    · obtain ⟨φ, b1, b2, hp⟩ := h
      rw [hcast] at b1 b2
      have hvC : v ≠ C := fun e' => hp.ne_zero (by rw [e', sub_self])
      obtain ⟨ψ, c1, c2, hq⟩ := wC v hv hvC
      have hp' : Pol (v - C) (φ + π) := by
        have := hp.neg
        rwa [neg_sub] at this
      have := Pol.unique hp' hq (by rw [abs_lt]; constructor <;> linarith)
      linarith
  have YneD : Y ≠ D := by
    intro e
    obtain ⟨v, hv, h | h⟩ := nbr_exists G a hD hn1
    · have hm : (⟨n - 1, hn1⟩ : Fin n) ∈ sides θ n S a Y := by rw [e]; exact ⟨v, hv, h⟩
      exact ((Ymem _ hn1).mp hm).2 rfl
    · obtain ⟨φ, b1, b2, hp⟩ := h
      rw [hcast] at b1 b2
      have hvD : v ≠ D := fun e' => hp.ne_zero (by rw [e', sub_self])
      obtain ⟨ψ, c1, c2, hq⟩ := wD v hv hvD
      have hp' : Pol (v - D) (φ + π) := by
        have := hp.neg
        rwa [neg_sub] at this
      have := Pol.unique hp' hq (by rw [abs_lt]; constructor <;> linarith)
      linarith
  have YneA : Y ≠ A := by
    intro e
    obtain ⟨v, hv, h | h⟩ := nbr_exists G a hA hn0
    · have hm : (⟨0, hn0⟩ : Fin n) ∈ sides θ n S a Y := by rw [e]; exact ⟨v, hv, h⟩
      exact ((Ymem _ hn0).mp hm).1 rfl
    · obtain ⟨φ, b1, b2, hp⟩ := h
      simp only [Nat.cast_zero, zero_mul, add_zero] at b1 b2
      have hvA : v ≠ A := fun e' => hp.ne_zero (by rw [e', sub_self])
      obtain ⟨ψ, c1, c2, hq⟩ := wA v hv hvA
      have hp' : Pol (v - A) (φ - π) := by
        have := hp.neg'
        rwa [neg_sub] at this
      have := Pol.unique hp' hq (by rw [abs_lt]; constructor <;> linarith)
      linarith
  -- position of Y relative to C
  have sC : ∃ φ, a + π - θ ≤ φ ∧ φ < a + π ∧ Pol (Y - C) φ := by
    obtain ⟨ψ, c1, c2, hq⟩ := wC Y hY YneC
    obtain ⟨k, hk, h | h⟩ := edge_alt G a hC hY (Ne.symm YneC)
    · obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hk' : ¬ (k ≠ 0 ∧ k ≠ n - 1) := fun hh => h.2.2 ((Ymem k hk).mpr hh)
      have hu := Pol.unique hp hq (by rw [abs_lt]; constructor <;> linarith [kb k hk])
      rcases ksplit k hk' with h0 | hl
      · have := k0 k h0
        linarith
      · have := kl k hl
        exact ⟨φ, by linarith, by linarith, hp⟩
    · exfalso
      obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hk' := (Ymem k hk).mp h.2.1
      have hp' : Pol (Y - C) (φ + π) := by
        have := hp.neg
        rwa [neg_sub] at this
      have hu := Pol.unique hp' hq (by rw [abs_lt]; constructor <;> linarith [kb k hk])
      linarith [kpos k hk'.1]
  -- position of Y relative to A
  have sA : ∃ φ, a ≤ φ ∧ φ < a + θ ∧ Pol (Y - A) φ := by
    obtain ⟨ψ, c1, c2, hq⟩ := wA Y hY YneA
    obtain ⟨k, hk, h | h⟩ := edge_alt G a hA hY (Ne.symm YneA)
    · obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hk' : ¬ (k ≠ 0 ∧ k ≠ n - 1) := fun hh => h.2.2 ((Ymem k hk).mpr hh)
      have hu := Pol.unique hp hq (by rw [abs_lt]; constructor <;> linarith [kb k hk])
      rcases ksplit k hk' with h0 | hl
      · have := k0 k h0
        exact ⟨φ, by linarith, by linarith, hp⟩
      · have := kl k hl
        linarith
    · exfalso
      obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hk' := (Ymem k hk).mp h.2.1
      have hp' : Pol (Y - A) (φ - π) := by
        have := hp.neg'
        rwa [neg_sub] at this
      have hu := Pol.unique hp' hq (by rw [abs_lt]; constructor <;> linarith [kb k hk])
      linarith [klast k hk hk'.2]
  -- position of Y relative to B
  have sB : ∃ φ, a ≤ φ ∧ φ < a + θ ∧ Pol (Y - B) φ := by
    obtain ⟨ψ, c1, c2, hq⟩ := wB Y hY YneB
    obtain ⟨k, hk, h | h⟩ := edge_alt G a hB hY (Ne.symm YneB)
    · obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hk' : ¬ (k ≠ 0 ∧ k ≠ n - 1) := fun hh => h.2.2 ((Ymem k hk).mpr hh)
      have hu := Pol.unique hp hq (by rw [abs_lt]; constructor <;> linarith [kb k hk])
      rcases ksplit k hk' with h0 | hl
      · have := k0 k h0
        exact ⟨φ, by linarith, by linarith, hp⟩
      · exfalso
        have := kl k hl
        obtain ⟨φA, x1, x2, hpA⟩ := sA
        obtain ⟨rA, hrA, -, HA⟩ := hpA.data
        obtain ⟨tm, htm, -, Hm⟩ := pBA.data
        obtain ⟨r, hr, -, H⟩ := hp.data
        have hh : hgt (a + π - θ) (Y - B) = hgt (a + π - θ) (Y - A) - hgt (a + π - θ) (B - A) := by
          rw [hgt_sub, hgt_sub, hgt_sub]; ring
        rw [H, HA, Hm] at hh
        have e1 : φ - (a + π - θ) = 0 := by linarith
        have e2 : a - θ - (a + π - θ) = -π := by ring
        rw [e1, e2, Real.sin_zero, Real.sin_neg, Real.sin_pi] at hh
        have hs : Real.sin (φA - (a + π - θ)) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
        have := mul_neg_of_pos_of_neg hrA hs
        linarith
    · exfalso
      obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hp' : Pol (Y - B) (φ + π) := by
        have := hp.neg
        rwa [neg_sub] at this
      have hu := Pol.unique hp' hq (by rw [abs_lt]; constructor <;> linarith [kb k hk])
      linarith [kb k hk]
  -- position of Y relative to D
  have sD : ∃ φ, a + π - θ ≤ φ ∧ φ < a + π ∧ Pol (Y - D) φ := by
    obtain ⟨ψ, c1, c2, hq⟩ := wD Y hY YneD
    obtain ⟨k, hk, h | h⟩ := edge_alt G a hD hY (Ne.symm YneD)
    · obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hk' : ¬ (k ≠ 0 ∧ k ≠ n - 1) := fun hh => h.2.2 ((Ymem k hk).mpr hh)
      have hu := Pol.unique hp hq (by rw [abs_lt]; constructor <;> linarith [kb k hk])
      rcases ksplit k hk' with h0 | hl
      · have := k0 k h0
        linarith
      · have := kl k hl
        exact ⟨φ, by linarith, by linarith, hp⟩
    · exfalso
      obtain ⟨φ, b1, b2, hp⟩ := h.1
      have hk' := (Ymem k hk).mp h.2.1
      have hp' : Pol (Y - D) (φ + π) := by
        have := hp.neg
        rwa [neg_sub] at this
      have hu := Pol.unique hp' hq (by
        rw [abs_lt]; constructor <;> linarith [kb k hk, kpos k hk'.1])
      have hφ : φ = a + θ := by linarith [kpos k hk'.1]
      obtain ⟨φC, x1, x2, hpC⟩ := sC
      obtain ⟨rC, hrC, -, HC⟩ := hpC.data
      obtain ⟨t1, ht1, -, H1⟩ := pDC.data
      obtain ⟨r, hr, -, H⟩ := hp'.data
      have hh : hgt (a + θ) (Y - C) = hgt (a + θ) (Y - D) + hgt (a + θ) (D - C) := by
        rw [hgt_sub, hgt_sub, hgt_sub]; ring
      rw [H, HC, H1] at hh
      have e1 : φ + π - (a + θ) = π := by linarith
      rw [e1, sub_self, Real.sin_zero, Real.sin_pi, mul_zero, mul_zero, add_zero] at hh
      have hs : 0 < Real.sin (φC - (a + θ)) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have := mul_pos hrC hs
      linarith
  -- the length comparison
  obtain ⟨φA, xA1, xA2, hpA⟩ := sA
  obtain ⟨φB, xB1, xB2, hpB⟩ := sB
  obtain ⟨φC, xC1, xC2, hpC⟩ := sC
  obtain ⟨φD, xD1, xD2, hpD⟩ := sD
  obtain ⟨rA, hrA, -, HA⟩ := hpA.data
  obtain ⟨rB, hrB, -, HB⟩ := hpB.data
  obtain ⟨rC, hrC, -, HC⟩ := hpC.data
  obtain ⟨rD, hrD, -, HD⟩ := hpD.data
  obtain ⟨tm, htm, nm, Hm⟩ := pBA.data
  obtain ⟨t0, ht0, n0, H0⟩ := pCB.data
  obtain ⟨t1, ht1, n1, H1⟩ := pDC.data
  rw [nm, n0, n1]
  have i1 : hgt (a + θ) (Y - B) < 0 := by
    rw [HB]
    exact mul_neg_of_pos_of_neg hrB
      (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))
  have i2 : hgt (a - θ) (Y - B) ≤ t0 * Real.sin θ := by
    have hh : hgt (a - θ) (Y - C) = hgt (a - θ) (Y - B) - hgt (a - θ) (C - B) := by
      rw [hgt_sub, hgt_sub, hgt_sub]; ring
    rw [HC, H0] at hh
    have e : a - (a - θ) = θ := by ring
    rw [e] at hh
    have s : Real.sin (φC - (a - θ)) ≤ 0 := by
      have h0 : 0 ≤ Real.sin (φC - (a - θ) - π) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at h0
      linarith
    have := mul_nonpos_of_nonneg_of_nonpos hrC.le s
    linarith
  have i3 := hgt_add_sub a θ (Y - B)
  have i4 : tm * Real.sin θ ≤ hgt a (Y - B) := by
    have hh : hgt a (Y - A) = hgt a (Y - B) + hgt a (B - A) := by
      rw [hgt_sub, hgt_sub, hgt_sub]; ring
    rw [HA, Hm] at hh
    have e : a - θ - a = -θ := by ring
    rw [e, Real.sin_neg] at hh
    have : 0 ≤ rA * Real.sin (φA - a) :=
      mul_nonneg hrA.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    linarith
  have i5 : t1 * Real.sin θ < hgt a (Y - B) := by
    have hh : hgt a (Y - D) = hgt a (Y - B) - hgt a (C - B) - hgt a (D - C) := by
      rw [hgt_sub, hgt_sub, hgt_sub, hgt_sub]; ring
    rw [HD, H0, H1] at hh
    have e1 : a + θ - a = θ := by ring
    rw [sub_self, e1, Real.sin_zero, mul_zero, sub_zero] at hh
    have : 0 < rD * Real.sin (φD - a) :=
      mul_pos hrD (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    linarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hc : 1 / 2 ≤ Real.cos θ := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ.le (by linarith) (by linarith)
  have hy0 : 0 ≤ hgt a (Y - B) := le_trans (by positivity) i4
  have key : hgt a (Y - B) < t0 * Real.sin θ := by nlinarith
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  · by_contra hcon
    rw [not_lt] at hcon
    nlinarith

theorem no_cfg (G : Cfg θ n S) : False := by
  obtain ⟨Q4, h4, c, w4⟩ := exists_wedge G
  obtain ⟨Q3, h3, p3, w3⟩ := step G h4 w4
  obtain ⟨Q2, h2, p2, w2⟩ := step G h3 w3
  obtain ⟨Q1, h1, p1, w1⟩ := step G h2 w2
  obtain ⟨Q0, h0, p0, w0⟩ := step G h1 w1
  have e1 : c - θ - θ = c - θ - θ - θ + θ := by ring
  have e2 : c - θ = c - θ - θ - θ + θ + θ := by ring
  have e3 : c - θ = c - θ - θ + θ := by ring
  have e4 : c = c - θ - θ + θ + θ := by ring
  have a1 := core G (a := c - θ - θ - θ) h0 h1 h2 h3 w0 w1 (e1 ▸ w2) (e2 ▸ w3) p0 p1 (e1 ▸ p2)
  have a2 := core G (a := c - θ - θ) h1 h2 h3 h4 w1 w2 (e3 ▸ w3) (e4 ▸ w4) p1 p2 (e3 ▸ p3)
  exact lt_asymm a1.2 a2.1

end OMA.ES504

theorem h2_proof : OMA.Erdos504R1.H2 := by
  unfold OMA.Erdos504R1.H2
  intro n hn S hcard
  by_contra hcon
  push Not at hcon
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply OMA.ES504.no_cfg (θ := Real.pi / n) (n := n) (S := S)
  refine ⟨by positivity, by field_simp, hn, ?_, hcard⟩
  intro p hp q hq r hr hpq hrq
  have h := hcon p hp q hq r hr hpq hrq
  have e : (1 - 1 / (n : ℝ)) * Real.pi = Real.pi - Real.pi / n := by field_simp
  linarith
end H2Section

theorem OMA.solution : type_of% @Erdos504.erdos_504 :=
  OMA.Erdos504R1.main h1_proof h2_proof
