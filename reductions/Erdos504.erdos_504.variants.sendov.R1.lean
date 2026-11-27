import FormalConjectures.ErdosProblems.«504»
import Mathlib

-- Reduction Erdos504.erdos_504.variants.sendov.R1 of Sendov (1995).
-- Credit: @graydeveloper01
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The split.  Put v1 = (1 - 1/n) pi and v2 = (1 - 2/(2n-1)) pi.  Sendov 1995 determines the
-- minimax angle alpha(N) for 2^(n-1) < N <= 2^n: it is v1 if N > 2^(n-1) + 2^(n-3), else v2.
--   H1  the first lower bound of Sendov: more than 2^(n-1) + 2^(n-3) points always contain
--       an angle of at least v1.
--   H2  the second lower bound of Sendov: more than 2^(n-1) points always contain an angle
--       of at least v2.
-- The theorem at the end of this file proves everything else:
--   upper   the Szekeres subset-sum cluster: the 2^n subset sums of 1, z, .., z^(n-1) with
--           z = rho exp(i pi/n), rho tiny, have all angles < v1 + eps.
--   upper2  a new triangle-of-clusters construction.  Put eta = pi/(2n-1).  Take the triangle
--           A = 0, B = 1, C = exp(i eta)/(2 cos eta) with angles eta, eta, pi - 2 eta, and
--           replace A, B, C by tiny subset-sum clusters
--             A + d exp(3 i eta) * sums of 1, z, .., z^(n-3)     (2^(n-2) points)
--             B + d exp(2 i eta) * sums of 1, z, .., z^(n-3)     (2^(n-2) points)
--             C + d exp(3 i eta) * sums of 1, z, .., z^(n-4)     (2^(n-3) points)
--           with z = rho exp(2 i eta).  All rays from a point have nominal directions that
--           are multiples of eta and pairwise at most pi - 2 eta apart (lemma good), so these
--           2^(n-1) + 2^(n-3) points have all angles < v2 + eps.
--   minimax_eq, assembly  the sSup bookkeeping (IsGreatest.csSup_eq) giving the value.
--
-- References.  Bl. Sendov, Minimax of the angles in a plane configuration of points,
-- Acta Math. Hungar. 69 (1995) 27-46.  G. Szekeres, On an extremum problem in the plane,
-- Amer. J. Math. 63 (1941).  P. Erdos and G. Szekeres, On some extremum problems in elementary
-- geometry, Ann. Univ. Sci. Budapest 3-4 (1960-61).
--
-- Note.  The construction code (polar-form toolkit and the first construction) reuses our
-- merged file proofs/Erdos504.erdos_504.variants.endpoint.lean.  Since only the H definitions
-- may be declared here, the polar-form predicate (w = r exp(i phi) with r > 0) and the point
-- maps are written out inline in the lemma statements.

namespace OMA.R_Erdos504_erdos_504_variants_sendov_R1

open Real

def H1 : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (S : Finset ℂ), 2 ^ (n - 1) + 2 ^ (n - 3) < S.card →
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
      (1 - 1 / (n : ℝ)) * π ≤ EuclideanGeometry.angle x z y

def H2 : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (S : Finset ℂ), 2 ^ (n - 1) < S.card →
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
      (1 - 2 / (2 * (n : ℝ) - 1)) * π ≤ EuclideanGeometry.angle x z y

lemma pol_ne_zero {w : ℂ} {φ : ℝ} (h : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp (((φ :
    ℝ) : ℂ) * Complex.I))) : w ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := h
  exact mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)

lemma pol_neg {w : ℂ} {φ : ℝ} (h : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp (((φ : ℝ) :
    ℂ) * Complex.I))) : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((-w) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((φ + π) : ℝ) :
    ℂ) * Complex.I)) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, hr, ?_⟩
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

lemma pol_neg' {w : ℂ} {φ : ℝ} (h : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp (((φ : ℝ)
    : ℂ) * Complex.I))) : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((-w) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((φ - π) : ℝ) :
    ℂ) * Complex.I)) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, hr, ?_⟩
  push_cast
  rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
  field_simp

lemma pol_norm_eq {w : ℂ} {φ : ℝ} {r : ℝ} (hr : 0 < r)
    (h : w = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) : ‖w‖ = r := by
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr.le]

lemma pol_arg {w : ℂ} (hw : w ≠ 0) : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp
    ((((Complex.arg w) : ℝ) : ℂ) * Complex.I)) :=
  ⟨‖w‖, norm_pos_iff.mpr hw, (Complex.norm_mul_exp_arg_mul_I w).symm⟩

lemma angle_pol {p q r : ℂ} {φ ψ : ℝ} (h1 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((p - q) : ℂ) = (ρ₀ : ℂ) *
    Complex.exp (((φ : ℝ) : ℂ) * Complex.I))) (h2 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((r - q) : ℂ) = (ρ₀ : ℂ) *
    Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)))
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

lemma pol_add_two_pi {w : ℂ} {φ : ℝ} (h : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp (((φ
    : ℝ) : ℂ) * Complex.I))) : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((φ + 2 * π)
    : ℝ) : ℂ) * Complex.I)) := by
  have := pol_neg (pol_neg h)
  rw [neg_neg] at this
  have e : φ + π + π = φ + 2 * π := by ring
  rwa [e] at this

lemma pol_sub_two_pi {w : ℂ} {φ : ℝ} (h : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp (((φ
    : ℝ) : ℂ) * Complex.I))) : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((φ - 2 * π)
    : ℝ) : ℂ) * Complex.I)) := by
  have := pol_neg' (pol_neg' h)
  rw [neg_neg] at this
  have e : φ - π - π = φ - 2 * π := by ring
  rwa [e] at this

lemma pol_mul {w w' : ℂ} {φ φ' : ℝ} (h : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w : ℂ) = (ρ₀ : ℂ) * Complex.exp (((φ
    : ℝ) : ℂ) * Complex.I))) (h' : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (w' : ℂ) = (ρ₀ : ℂ) * Complex.exp (((φ' : ℝ)
    : ℂ) * Complex.I))) : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((w * w') : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((φ + φ') :
    ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := h'
  refine ⟨r * s, mul_pos hr hs, ?_⟩
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

lemma angle_le {p q r : ℂ} {φ φ' B : ℝ} (h1 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((p - q) : ℂ) = (ρ₀ : ℂ) *
    Complex.exp (((φ : ℝ) : ℂ) * Complex.I))) (h2 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((r - q) : ℂ) = (ρ₀ : ℂ) *
    Complex.exp (((φ' : ℝ) : ℂ) * Complex.I)))
    (hB : B ≤ π)
    (h : |φ - φ'| ≤ B ∨ |φ - φ' + 2 * π| ≤ B ∨ |φ - φ' - 2 * π| ≤ B) :
    EuclideanGeometry.angle p q r ≤ B := by
  rcases h with h | h | h
  · rw [angle_pol h1 h2 (by linarith)]; exact h
  · have e : φ + 2 * π - φ' = φ - φ' + 2 * π := by ring
    rw [angle_pol (pol_add_two_pi h1) h2 (by rw [e]; linarith), e]; exact h
  · have e : φ - 2 * π - φ' = φ - φ' - 2 * π := by ring
    rw [angle_pol (pol_sub_two_pi h1) h2 (by rw [e]; linarith), e]; exact h

lemma angle_dirs {θ η : ℝ} {n : ℕ} (hθ : 0 < θ) (hn : (n : ℝ) * θ = π)
    (hη2 : 2 * η ≤ θ) {p q r : ℂ} {k k' : ℕ} (hk : k < n) (hk' : k' < n) {ψ ψ' σ σ' : ℝ}
    (hψ : |ψ| ≤ η) (hψ' : |ψ'| ≤ η) (hσ : σ = 0 ∨ σ = π) (hσ' : σ' = 0 ∨ σ' = π)
    (hs : k = k' → σ = σ')
    (h1 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((p - q) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((k * θ + ψ + σ) : ℝ) : ℂ) *
        Complex.I))) (h2 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((r - q) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((k' * θ +
        ψ' + σ') : ℝ) : ℂ) * Complex.I))) :
    EuclideanGeometry.angle p q r ≤ π - θ + 2 * η := by
  have hπ := Real.pi_pos
  obtain ⟨x1, x2⟩ := abs_le.mp hψ
  obtain ⟨y1, y2⟩ := abs_le.mp hψ'
  refine angle_le h1 h2 (by linarith) ?_
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have c1 : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hlt
    have c2 : (k' : ℝ) + 1 ≤ n := by exact_mod_cast hk'
    have c0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have d1 : (k : ℝ) * θ + θ ≤ k' * θ := by nlinarith
    have d2 : (k' : ℝ) * θ + θ ≤ π := by nlinarith
    have d3 : 0 ≤ (k : ℝ) * θ := by positivity
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
    · left; rw [abs_le]; constructor <;> linarith
    · right; left; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith
  · have e := hs heq
    subst heq
    subst e
    have c2 : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have c0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have d2 : θ ≤ π := by nlinarith
    left; rw [abs_le]; constructor <;> linarith
  · have c1 : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hgt
    have c2 : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have c0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
    have d1 : (k' : ℝ) * θ + θ ≤ k * θ := by nlinarith
    have d2 : (k : ℝ) * θ + θ ≤ π := by nlinarith
    have d3 : 0 ≤ (k' : ℝ) * θ := by positivity
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
    · left; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith
    · right; right; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith

lemma pol_one_add {η : ℝ} (hη : 0 < η) (hη2 : η ≤ π / 2) {u : ℂ}
    (hu : 2 * ‖u‖ ≤ Real.sin η) : ∃ ψ : ℝ, |ψ| ≤ η ∧ (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((1 + u) : ℂ) = (ρ₀ : ℂ) *
        Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)) := by
  have hs1 : Real.sin η ≤ 1 := Real.sin_le_one η
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hre : (1 : ℝ) / 2 ≤ (1 + u).re := by
    have := Complex.abs_re_le_norm u
    have := (abs_le.mp this).1
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hne : (1 + u) ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hnorm : (1 : ℝ) / 2 ≤ ‖1 + u‖ := le_trans hre (Complex.re_le_norm _)
  have hnpos : 0 < ‖1 + u‖ := by linarith
  have him : |(1 + u).im| ≤ ‖u‖ := by
    simpa using Complex.abs_im_le_norm u
  have ht : |(1 + u).im / ‖1 + u‖| ≤ Real.sin η := by
    rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    nlinarith
  refine ⟨Complex.arg (1 + u), ?_, pol_arg hne⟩
  rw [Complex.arg_of_re_nonneg (by linarith)]
  obtain ⟨t1, t2⟩ := abs_le.mp ht
  rw [abs_le]
  constructor
  · have := Real.arcsin_le_arcsin (x := Real.sin (-η)) (y := (1 + u).im / ‖1 + u‖)
      (by rw [Real.sin_neg]; exact t1)
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at this
  · have := Real.arcsin_le_arcsin t2
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at this

lemma pol_pow {z : ℂ} {ρ θ : ℝ} (hρ : 0 < ρ)
    (hz : z = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (k : ℕ) :
    (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((z ^ k) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((k * θ) : ℝ) : ℂ) * Complex.I))
        := by
  refine ⟨ρ ^ k, pow_pos hρ k, ?_⟩
  rw [hz, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma pt_diff {z : ℂ} {n : ℕ} (hz : ‖z‖ ≤ 1) {T T' : Finset ℕ}
    (hT : T ⊆ Finset.range n) (hT' : T' ⊆ Finset.range n) (hne : T ≠ T') :
    ∃ k, k < n ∧ (k ∈ T ↔ k ∉ T') ∧ ∃ u : ℂ, ‖u‖ ≤ n * ‖z‖ ∧
      (k ∈ T → (∑ k ∈ Finset.range n, if k ∈ T then z ^ k else 0) - (∑ k ∈ Finset.range n, if k ∈
          T' then z ^ k else 0) = z ^ k * (1 + u)) ∧
      (k ∉ T → (∑ k ∈ Finset.range n, if k ∈ T then z ^ k else 0) - (∑ k ∈ Finset.range n, if k ∈
          T' then z ^ k else 0) = -(z ^ k * (1 + u))) := by
  classical
  have hD : ((Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T'))).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hne
    ext k
    by_cases hk : k ∈ Finset.range n
    · have : k ∉ (Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T')) := by
        rw [hemp]; exact Finset.notMem_empty _
      rw [Finset.mem_filter] at this
      tauto
    · exact ⟨fun h => absurd (hT h) hk, fun h => absurd (hT' h) hk⟩
  set k0 := ((Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T'))).min' hD with hk0
  have hk0mem := Finset.min'_mem _ hD
  rw [← hk0, Finset.mem_filter, Finset.mem_range] at hk0mem
  obtain ⟨hk0n, hk0d⟩ := hk0mem
  have hbelow : ∀ k, k < k0 → (k ∈ T ↔ k ∈ T') := by
    intro k hk
    by_contra hc
    have hmem : k ∈ (Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T')) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩
    have := Finset.min'_le _ k hmem
    omega
  set e : ℕ → ℂ := fun k => (if k ∈ T then (1 : ℂ) else 0) - (if k ∈ T' then 1 else 0) with he
  set w : ℂ := ∑ k ∈ Finset.range n, if k0 < k then e k * z ^ (k - k0) else 0 with hw
  have hsum : (∑ k ∈ Finset.range n, if k ∈ T then z ^ k else 0) - (∑ k ∈ Finset.range n, if k ∈ T'
      then z ^ k else 0) = z ^ k0 * (e k0 + w) := by
    rw [← Finset.sum_sub_distrib, mul_add, hw, Finset.mul_sum]
    have h1 : z ^ k0 * e k0 = ∑ k ∈ Finset.range n, if k = k0 then z ^ k0 * e k0 else 0 := by
      rw [Finset.sum_ite_eq' (Finset.range n) k0]
      simp [hk0n]
    rw [h1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rcases lt_trichotomy k k0 with hlt | heq | hgt
    · have := hbelow k hlt
      have hk1 : ¬ k = k0 := by omega
      have hk2 : ¬ k0 < k := by omega
      rw [if_neg hk1, if_neg hk2]
      by_cases hkT : k ∈ T
      · have hkT' : k ∈ T' := this.mp hkT
        simp [hkT, hkT']
      · have hkT' : k ∉ T' := fun h => hkT (this.mpr h)
        simp [hkT, hkT']
    · have hk2 : ¬ k0 < k := by omega
      rw [if_pos heq, if_neg hk2, heq]
      simp only [he]
      split_ifs <;> ring
    · have hk1 : ¬ k = k0 := by omega
      rw [if_neg hk1, if_pos hgt]
      have hpow : z ^ k = z ^ k0 * z ^ (k - k0) := by
        rw [← pow_add]; congr 1; omega
      simp only [he, hpow]
      split_ifs <;> ring
  have hebound : ∀ k, ‖e k‖ ≤ 1 := by
    intro k
    simp only [he]
    split_ifs <;> simp
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hwb : ‖w‖ ≤ n * ‖z‖ := by
    have := norm_sum_le_of_le (Finset.range n)
      (f := fun k => if k0 < k then e k * z ^ (k - k0) else 0) (n := fun _ => ‖z‖) (by
        intro k _
        by_cases hk : k0 < k
        · rw [if_pos hk, norm_mul, norm_pow]
          have h1 : ‖z‖ ^ (k - k0) ≤ ‖z‖ := pow_le_of_le_one hz0 hz (by omega)
          have h2 := hebound k
          have h3 : 0 ≤ ‖z‖ ^ (k - k0) := pow_nonneg hz0 _
          nlinarith [norm_nonneg (e k)]
        · rw [if_neg hk, norm_zero]; exact hz0)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  refine ⟨k0, hk0n, by tauto, ?_⟩
  by_cases hkT : k0 ∈ T
  · have hkT' : k0 ∉ T' := by tauto
    refine ⟨w, hwb, fun _ => ?_, fun h => absurd hkT h⟩
    rw [hsum]
    simp [he, hkT, hkT']
  · have hkT' : k0 ∈ T' := by tauto
    refine ⟨-w, by rw [norm_neg]; exact hwb, fun h => absurd h hkT, fun _ => ?_⟩
    rw [hsum]
    simp [he, hkT, hkT']
    ring

set_option maxHeartbeats 1000000 in
lemma upper {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ n ∧ ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < π - π / n + ε := by
  classical
  have hπ := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set θ : ℝ := π / n with hθdef
  have hθ : 0 < θ := by positivity
  have hnθ : (n : ℝ) * θ = π := by rw [hθdef]; field_simp
  have hθπ : θ ≤ π := by nlinarith
  set η : ℝ := min ε θ / 4 with hηdef
  have hm : 0 < min ε θ := lt_min hε hθ
  have hη : 0 < η := by positivity
  have hηε : 4 * η ≤ ε := by rw [hηdef]; linarith [min_le_left ε θ]
  have hηθ : 4 * η ≤ θ := by rw [hηdef]; linarith [min_le_right ε θ]
  have hsin : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη (by linarith)
  set ρ : ℝ := Real.sin η / (2 * n) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ2 : 2 * (n * ρ) = Real.sin η := by rw [hρdef]; field_simp
  have hρ1 : ρ ≤ 1 := by
    have := Real.sin_le_one η
    nlinarith
  set z : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hzn : ‖z‖ = ρ := pol_norm_eq hρ hz
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ → ℂ, ∀ T, P T = (∑ k ∈ Finset.range n, if k ∈ T then z ^ k else
      0) := ⟨_, fun _ => rfl⟩
  have hdir : ∀ T ∈ (Finset.range n).powerset, ∀ T' ∈ (Finset.range n).powerset, T ≠ T' →
      ∃ k, k < n ∧ (k ∈ T ↔ k ∉ T') ∧ ∃ ψ σ : ℝ, |ψ| ≤ η ∧ (σ = 0 ∨ σ = π) ∧
        (σ = 0 ↔ k ∈ T) ∧ (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((P T - P T') : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((k * θ
            + ψ + σ) : ℝ) : ℂ) * Complex.I)) := by
    intro T hT T' hT' hne
    rw [hP, hP]
    obtain ⟨k, hk, hiff, u, hu, h1, h2⟩ := pt_diff (z := z) (n := n) (by rw [hzn]; exact hρ1)
      (Finset.mem_powerset.mp hT) (Finset.mem_powerset.mp hT') hne
    rw [hzn] at hu
    obtain ⟨ψ, hψ, hpol⟩ := pol_one_add hη (by linarith) (u := u) (by linarith)
    have hmul := pol_mul (pol_pow hρ hz k) hpol
    refine ⟨k, hk, hiff, ψ, ?_⟩
    by_cases hkT : k ∈ T
    · refine ⟨0, hψ, Or.inl rfl, by simp [hkT], ?_⟩
      rw [h1 hkT, add_zero]
      exact hmul
    · refine ⟨π, hψ, Or.inr rfl, by simp [hkT, hπ.ne'], ?_⟩
      rw [h2 hkT]
      exact pol_neg hmul
  have hinj : Set.InjOn P ((Finset.range n).powerset : Set (Finset ℕ)) := by
    intro T hT T' hT' he
    by_contra hne
    obtain ⟨k, -, -, ψ, σ, -, -, -, hpol⟩ := hdir T hT T' hT' hne
    exact pol_ne_zero hpol (by rw [he, sub_self])
  refine ⟨(Finset.range n).powerset.image P, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.card_range]
  · intro p hp q hq r hr hpq hrq
    obtain ⟨Tp, hTp, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨Tq, hTq, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨Tr, hTr, rfl⟩ := Finset.mem_image.mp hr
    have hpq' : Tp ≠ Tq := fun h => hpq (by rw [h])
    have hrq' : Tr ≠ Tq := fun h => hrq (by rw [h])
    obtain ⟨k, hk, hiff, ψ, σ, hψ, hσ, hσT, hpol⟩ := hdir Tp hTp Tq hTq hpq'
    obtain ⟨k', hk', hiff', ψ', σ', hψ', hσ', hσT', hpol'⟩ := hdir Tr hTr Tq hTq hrq'
    have hs : k = k' → σ = σ' := by
      intro e
      subst e
      have hTT : k ∈ Tp ↔ k ∈ Tr :=
        ⟨fun h => hiff'.mpr (hiff.mp h), fun h => hiff.mpr (hiff'.mp h)⟩
      rcases hσ with h | h <;> rcases hσ' with h' | h'
      · rw [h, h']
      · exfalso
        have a1 := hσT.mp h
        have a2 : ¬ σ' = 0 := by rw [h']; exact hπ.ne'
        exact a2 (hσT'.mpr (hTT.mp a1))
      · exfalso
        have a1 := hσT'.mp h'
        have a2 : ¬ σ = 0 := by rw [h]; exact hπ.ne'
        exact a2 (hσT.mpr (hTT.mpr a1))
      · rw [h, h']
    have := angle_dirs hθ hnθ (by linarith) hk hk' hψ hψ' hσ hσ' hs hpol hpol'
    linarith

-- ===== U2: the second construction (proved) =====
lemma good_symm {η ν1 ν2 : ℝ} (h : (|(ν1 : ℝ) - (ν2 : ℝ)| ≤ π - 2 * η ∨ |(ν1 : ℝ) - (ν2 : ℝ) + 2 *
    π| ≤ π - 2 * η ∨ |(ν1 : ℝ) - (ν2 : ℝ) - 2 * π| ≤ π - 2 * η)) : (|(ν2 : ℝ) - (ν1 : ℝ)| ≤ π - 2 *
    η ∨ |(ν2 : ℝ) - (ν1 : ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν2 : ℝ) - (ν1 : ℝ) - 2 * π| ≤ π - 2 * η) := by
  rcases h with h | h | h
  · left; rw [abs_sub_comm]; exact h
  · right; right
    have e : ν2 - ν1 - 2 * π = -(ν1 - ν2 + 2 * π) := by ring
    rw [e, abs_neg]; exact h
  · right; left
    have e : ν2 - ν1 + 2 * π = -(ν1 - ν2 - 2 * π) := by ring
    rw [e, abs_neg]; exact h

lemma kfacts {η j : ℝ} {n k : ℕ} (hη : 0 < η) (hk : (k : ℝ) + j ≤ n) :
    0 ≤ (k : ℝ) * η ∧ (k : ℝ) * η + j * η ≤ n * η := by
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · positivity
  · nlinarith

lemma good_intra {η β : ℝ} {n : ℕ} (hη : 0 < η) (hM : 2 * (n : ℝ) * η - η = π)
    {T : Finset ℕ} {k k' : ℕ} (hk : k + 3 ≤ n) (hk' : k' + 3 ≤ n) :
    (|((β + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) - ((β + k' * (2 * η) + (if k' ∈ T then π
        else 0)) : ℝ)| ≤ π - 2 * η ∨ |((β + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) - ((β + k'
        * (2 * η) + (if k' ∈ T then π else 0)) : ℝ) + 2 * π| ≤ π - 2 * η ∨ |((β + k * (2 * η) + (if
        k ∈ T then π else 0)) : ℝ) - ((β + k' * (2 * η) + (if k' ∈ T then π else 0)) : ℝ) - 2 * π|
        ≤ π - 2 * η) := by
  have c2 : (k : ℝ) + 3 ≤ n := by exact_mod_cast hk
  have c2' : (k' : ℝ) + 3 ≤ n := by exact_mod_cast hk'
  obtain ⟨a1, a2⟩ := kfacts hη c2
  obtain ⟨b1, b2⟩ := kfacts hη c2'
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have c1 : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hlt
    have d1 : (k : ℝ) * η + η ≤ k' * η := by nlinarith
    split_ifs <;>
    first
      | (left; rw [abs_le]; constructor <;> linarith)
      | (right; left; rw [abs_le]; constructor <;> linarith)
      | (right; right; rw [abs_le]; constructor <;> linarith)
  · subst heq
    left
    rw [sub_self, abs_zero]
    linarith
  · have c1 : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hgt
    have d1 : (k' : ℝ) * η + η ≤ k * η := by nlinarith
    split_ifs <;>
    first
      | (left; rw [abs_le]; constructor <;> linarith)
      | (right; left; rw [abs_le]; constructor <;> linarith)
      | (right; right; rw [abs_le]; constructor <;> linarith)

lemma good_mix {η : ℝ} {n : ℕ} (hη : 0 < η) (hM : 2 * (n : ℝ) * η - η = π)
    {T : Finset ℕ} {k : ℕ} {ν : ℝ} :
    (k + 3 ≤ n → (ν = 0 ∨ ν = η) →
      (|(ν : ℝ) - ((3 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ)| ≤ π - 2 * η ∨ |(ν : ℝ) -
          ((3 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν : ℝ) -
          ((3 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) - 2 * π| ≤ π - 2 * η)) ∧
    (k + 3 ≤ n → (ν = π ∨ ν = π - η) →
      (|(ν : ℝ) - ((2 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ)| ≤ π - 2 * η ∨ |(ν : ℝ) -
          ((2 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν : ℝ) -
          ((2 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) - 2 * π| ≤ π - 2 * η)) ∧
    (k + 4 ≤ n → (ν = η + π ∨ ν = -η) →
      (|(ν : ℝ) - ((3 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ)| ≤ π - 2 * η ∨ |(ν : ℝ) -
          ((3 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν : ℝ) -
          ((3 * η + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) - 2 * π| ≤ π - 2 * η)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hk hν
    have c2 : (k : ℝ) + 3 ≤ n := by exact_mod_cast hk
    obtain ⟨a1, a2⟩ := kfacts hη c2
    rcases hν with rfl | rfl <;> split_ifs <;>
    first
      | (left; rw [abs_le]; constructor <;> linarith)
      | (right; left; rw [abs_le]; constructor <;> linarith)
      | (right; right; rw [abs_le]; constructor <;> linarith)
  · intro hk hν
    have c2 : (k : ℝ) + 3 ≤ n := by exact_mod_cast hk
    obtain ⟨a1, a2⟩ := kfacts hη c2
    rcases hν with rfl | rfl <;> split_ifs <;>
    first
      | (left; rw [abs_le]; constructor <;> linarith)
      | (right; left; rw [abs_le]; constructor <;> linarith)
      | (right; right; rw [abs_le]; constructor <;> linarith)
  · intro hk hν
    have c2 : (k : ℝ) + 4 ≤ n := by exact_mod_cast hk
    obtain ⟨a1, a2⟩ := kfacts hη c2
    rcases hν with rfl | rfl <;> split_ifs <;>
    first
      | (left; rw [abs_le]; constructor <;> linarith)
      | (right; left; rw [abs_le]; constructor <;> linarith)
      | (right; right; rw [abs_le]; constructor <;> linarith)

lemma good_inter {η : ℝ} {n : ℕ} (hη : 0 < η) (hn : 3 ≤ n) (hM : 2 * (n : ℝ) * η - η = π)
    {ν1 ν2 : ℝ} :
    ((ν1 = 0 ∨ ν1 = η) → (ν2 = 0 ∨ ν2 = η) → (|(ν1 : ℝ) - (ν2 : ℝ)| ≤ π - 2 * η ∨ |(ν1 : ℝ) - (ν2 :
        ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν1 : ℝ) - (ν2 : ℝ) - 2 * π| ≤ π - 2 * η)) ∧
    ((ν1 = π ∨ ν1 = π - η) → (ν2 = π ∨ ν2 = π - η) → (|(ν1 : ℝ) - (ν2 : ℝ)| ≤ π - 2 * η ∨ |(ν1 : ℝ)
        - (ν2 : ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν1 : ℝ) - (ν2 : ℝ) - 2 * π| ≤ π - 2 * η)) ∧
    ((ν1 = η + π ∨ ν1 = -η) → (ν2 = η + π ∨ ν2 = -η) → (|(ν1 : ℝ) - (ν2 : ℝ)| ≤ π - 2 * η ∨ |(ν1 :
        ℝ) - (ν2 : ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν1 : ℝ) - (ν2 : ℝ) - 2 * π| ≤ π - 2 * η)) := by
  have c : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have d : 3 * η ≤ n * η := by nlinarith
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    first
      | (left; rw [abs_le]; constructor <;> linarith)
      | (right; left; rw [abs_le]; constructor <;> linarith)
      | (right; right; rw [abs_le]; constructor <;> linarith)

lemma good {η : ℝ} {n : ℕ} (hη : 0 < η) (hn : 3 ≤ n) (hM : 2 * (n : ℝ) * η - η = π)
    {c : ℕ} {T : Finset ℕ} {ν1 ν2 : ℝ} (h1 : (((c : ℕ) = 0 ∧ ((ν1 : ℝ) = 0 ∨ (ν1 : ℝ) = η ∨ ∃ κ₀ :
        ℕ, κ₀ + 3 ≤ n ∧ (ν1 : ℝ) = 3 * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else 0))) ∨ ((c : ℕ) =
        1 ∧ ((ν1 : ℝ) = π ∨ (ν1 : ℝ) = π - η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ (ν1 : ℝ) = 2 * η + κ₀ * (2 *
        η) + (if κ₀ ∈ T then π else 0))) ∨ ((c : ℕ) = 2 ∧ ((ν1 : ℝ) = η + π ∨ (ν1 : ℝ) = -η ∨ ∃ κ₀
        : ℕ, κ₀ + 4 ≤ n ∧ (ν1 : ℝ) = 3 * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else 0))))) (h2 :
        (((c : ℕ) = 0 ∧ ((ν2 : ℝ) = 0 ∨ (ν2 : ℝ) = η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ (ν2 : ℝ) = 3 * η + κ₀
        * (2 * η) + (if κ₀ ∈ T then π else 0))) ∨ ((c : ℕ) = 1 ∧ ((ν2 : ℝ) = π ∨ (ν2 : ℝ) = π - η ∨
        ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ (ν2 : ℝ) = 2 * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else 0))) ∨ ((c
        : ℕ) = 2 ∧ ((ν2 : ℝ) = η + π ∨ (ν2 : ℝ) = -η ∨ ∃ κ₀ : ℕ, κ₀ + 4 ≤ n ∧ (ν2 : ℝ) = 3 * η + κ₀
        * (2 * η) + (if κ₀ ∈ T then π else 0))))) :
    (|(ν1 : ℝ) - (ν2 : ℝ)| ≤ π - 2 * η ∨ |(ν1 : ℝ) - (ν2 : ℝ) + 2 * π| ≤ π - 2 * η ∨ |(ν1 : ℝ) -
        (ν2 : ℝ) - 2 * π| ≤ π - 2 * η) := by
  rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩
  · rcases h2 with ⟨-, h2⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    · rcases h1 with a | a | ⟨k, hk, rfl⟩
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact (good_inter hη hn hM).1 (Or.inl a) (Or.inl b)
        · exact (good_inter hη hn hM).1 (Or.inl a) (Or.inr b)
        · exact (good_mix hη hM).1 hk' (Or.inl a)
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact (good_inter hη hn hM).1 (Or.inr a) (Or.inl b)
        · exact (good_inter hη hn hM).1 (Or.inr a) (Or.inr b)
        · exact (good_mix hη hM).1 hk' (Or.inr a)
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact good_symm ((good_mix hη hM).1 hk (Or.inl b))
        · exact good_symm ((good_mix hη hM).1 hk (Or.inr b))
        · exact good_intra hη hM hk hk'
    · omega
    · omega
  · rcases h2 with ⟨hc, -⟩ | ⟨-, h2⟩ | ⟨hc, -⟩
    · omega
    · rcases h1 with a | a | ⟨k, hk, rfl⟩
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact (good_inter hη hn hM).2.1 (Or.inl a) (Or.inl b)
        · exact (good_inter hη hn hM).2.1 (Or.inl a) (Or.inr b)
        · exact (good_mix hη hM).2.1 hk' (Or.inl a)
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact (good_inter hη hn hM).2.1 (Or.inr a) (Or.inl b)
        · exact (good_inter hη hn hM).2.1 (Or.inr a) (Or.inr b)
        · exact (good_mix hη hM).2.1 hk' (Or.inr a)
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact good_symm ((good_mix hη hM).2.1 hk (Or.inl b))
        · exact good_symm ((good_mix hη hM).2.1 hk (Or.inr b))
        · exact good_intra hη hM hk hk'
    · omega
  · rcases h2 with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨-, h2⟩
    · omega
    · omega
    · rcases h1 with a | a | ⟨k, hk, rfl⟩
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact (good_inter hη hn hM).2.2 (Or.inl a) (Or.inl b)
        · exact (good_inter hη hn hM).2.2 (Or.inl a) (Or.inr b)
        · exact (good_mix hη hM).2.2 hk' (Or.inl a)
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact (good_inter hη hn hM).2.2 (Or.inr a) (Or.inl b)
        · exact (good_inter hη hn hM).2.2 (Or.inr a) (Or.inr b)
        · exact (good_mix hη hM).2.2 hk' (Or.inr a)
      · rcases h2 with b | b | ⟨k', hk', rfl⟩
        · exact good_symm ((good_mix hη hM).2.2 hk (Or.inl b))
        · exact good_symm ((good_mix hη hM).2.2 hk (Or.inr b))
        · exact good_intra hη hM (by omega) (by omega)

lemma pt_norm {z : ℂ} (hz : ‖z‖ ≤ 1) (m : ℕ) (T : Finset ℕ) : ‖(∑ k ∈ Finset.range m, if k ∈ T then
    z ^ k else 0)‖ ≤ m := by
  have := norm_sum_le_of_le (Finset.range m) (f := fun k => if k ∈ T then z ^ k else 0)
    (n := fun _ => (1 : ℝ)) (by
      intro k _
      split_ifs
      · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz
      · rw [norm_zero]; exact zero_le_one)
  simpa using this

lemma pol_far {η' d : ℝ} (hη : 0 < η') (hη2 : η' ≤ π / 2) {D w : ℂ} (hD : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (D :
    ℂ) = (ρ₀ : ℂ) * Complex.exp (((d : ℝ) : ℂ) * Complex.I)))
    (hDn : 1 / 2 ≤ ‖D‖) (hw : 4 * ‖w‖ ≤ Real.sin η') :
    ∃ ψ : ℝ, |ψ| ≤ η' ∧ (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((D + w) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((d + ψ) : ℝ)
        : ℂ) * Complex.I)) := by
  have hD0 := pol_ne_zero hD
  have hpos : 0 < ‖D‖ := by linarith
  have hw0 := norm_nonneg w
  obtain ⟨ψ, hψ, hp⟩ := pol_one_add hη hη2 (u := w / D) (by
    rw [norm_div, ← mul_div_assoc, div_le_iff₀ hpos]
    nlinarith)
  refine ⟨ψ, hψ, ?_⟩
  have := pol_mul hD hp
  have e : D * (1 + w / D) = D + w := by field_simp
  rwa [e] at this

lemma ctr_dir {η : ℝ} (hη : 0 < η) (hη2 : η < π / 2) {c c' : ℕ} (hc : c ≤ 2) (hc' : c' ≤ 2)
    (hne : c ≠ c') :
    ∃ d : ℝ, (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (((if (c' : ℕ) = 0 then (0 : ℂ) else if (c' : ℕ) = 1 then (1 : ℂ)
        else ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) - (if (c : ℕ) =
        0 then (0 : ℂ) else if (c : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos η) : ℝ) : ℂ) *
        Complex.exp ((η : ℂ) * Complex.I))) : ℂ) = (ρ₀ : ℂ) * Complex.exp (((d : ℝ) : ℂ) *
        Complex.I)) ∧ 1 / 2 ≤ ‖(if (c' : ℕ) = 0 then (0 : ℂ) else if (c' : ℕ) = 1 then (1 : ℂ) else
        ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) - (if (c : ℕ) = 0
        then (0 : ℂ) else if (c : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos η) : ℝ) : ℂ) *
        Complex.exp ((η : ℂ) * Complex.I))‖ ∧
      ((c = 0 ∧ (d = 0 ∨ d = η)) ∨ (c = 1 ∧ (d = π ∨ d = π - η)) ∨
        (c = 2 ∧ (d = η + π ∨ d = -η))) := by
  have hcos : 0 < Real.cos η := Real.cos_pos_of_mem_Ioo ⟨by linarith, hη2⟩
  have hcos1 : Real.cos η ≤ 1 := Real.cos_le_one η
  set r : ℝ := 1 / (2 * Real.cos η) with hr
  have hr0 : 0 < r := by positivity
  have hr2 : 1 / 2 ≤ r := by
    rw [hr, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hrc : r * Real.cos η = 1 / 2 := by rw [hr]; field_simp
  have p01 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((1 : ℂ) : ℂ) = (ρ₀ : ℂ) * Complex.exp (((0 : ℝ) : ℂ) *
      Complex.I)) := ⟨1, one_pos, by simp⟩
  have p02 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (((r : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) : ℂ) = (ρ₀ : ℂ) *
      Complex.exp (((η : ℝ) : ℂ) * Complex.I)) := ⟨r, hr0, rfl⟩
  have p12 : (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (((r : ℂ) * Complex.exp ((η : ℂ) * Complex.I) - 1) : ℂ) = (ρ₀ : ℂ)
      * Complex.exp ((((π - η) : ℝ) : ℂ) * Complex.I)) := by
    refine ⟨r, hr0, ?_⟩
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_re,
        Real.cos_pi_sub]
      linarith
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_im,
        Real.sin_pi_sub]
      ring
  have n01 : ‖(1 : ℂ)‖ = 1 := norm_one
  have n02 : ‖(r : ℂ) * Complex.exp ((η : ℂ) * Complex.I)‖ = r := pol_norm_eq hr0 rfl
  have n12 : ‖(r : ℂ) * Complex.exp ((η : ℂ) * Complex.I) - 1‖ = r := by
    obtain ⟨s, hs, e⟩ := p12
    have h1 := pol_norm_eq hs e
    have h2 : s = r := by
      have := congrArg Complex.im e
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_im,
        Real.sin_pi_sub] at this
      have hs : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη (by linarith)
      nlinarith
    rw [h1, h2]
  have e0 : (if (0 : ℕ) = 0 then (0 : ℂ) else if (0 : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos
      η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) = 0 := by simp
  have e1 : (if (1 : ℕ) = 0 then (0 : ℂ) else if (1 : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos
      η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) = 1 := by simp
  have e2 : (if (2 : ℕ) = 0 then (0 : ℂ) else if (2 : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos
      η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) = (r : ℂ) * Complex.exp ((η : ℂ) *
      Complex.I) := by
    rw [if_neg (by norm_num), if_neg (by norm_num)]
  have s20 : (0 : ℂ) - (r : ℂ) * Complex.exp ((η : ℂ) * Complex.I)
      = -((r : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) := by ring
  have s21 : (1 : ℂ) - (r : ℂ) * Complex.exp ((η : ℂ) * Complex.I)
      = -((r : ℂ) * Complex.exp ((η : ℂ) * Complex.I) - 1) := by ring
  have s10 : (0 : ℂ) - 1 = -1 := by ring
  interval_cases c <;> interval_cases c'
  · exact absurd rfl hne
  · refine ⟨0, ?_, ?_, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    · rw [e1, e0, sub_zero]; exact p01
    · rw [e1, e0, sub_zero, n01]; norm_num
  · refine ⟨η, ?_, ?_, Or.inl ⟨rfl, Or.inr rfl⟩⟩
    · rw [e2, e0, sub_zero]; exact p02
    · rw [e2, e0, sub_zero, n02]; exact hr2
  · refine ⟨π, ?_, ?_, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
    · have := pol_neg p01
      rw [zero_add] at this
      rw [e1, e0, s10]; exact this
    · rw [e1, e0, s10, norm_neg, n01]; norm_num
  · exact absurd rfl hne
  · refine ⟨π - η, ?_, ?_, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩
    · rw [e2, e1]; exact p12
    · rw [e2, e1, n12]; exact hr2
  · refine ⟨η + π, ?_, ?_, Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)⟩
    · rw [e2, e0, s20]; exact pol_neg p02
    · rw [e2, e0, s20, norm_neg, n02]; exact hr2
  · refine ⟨-η, ?_, ?_, Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)⟩
    · rw [e2, e1, s21]
      have h := pol_neg' p12
      have e : π - η - π = -η := by ring
      rwa [e] at h
    · rw [e2, e1, s21, norm_neg, n12]; exact hr2
  · exact absurd rfl hne

lemma ray {n : ℕ} {η η' ρ δ : ℝ} (hη : 0 < η) (hη2 : η < π / 2)
    (hη' : 0 < η') (hη'2 : η' ≤ π / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρ2 : 2 * (n * ρ) ≤ Real.sin η') (hδ : 0 < δ) (hδ2 : 8 * (n * δ) ≤ Real.sin η')
    {z : ℂ} (hz : z = (ρ : ℂ) * Complex.exp (((2 * η : ℝ) : ℂ) * Complex.I))
    {c c' : ℕ} {T T' : Finset ℕ} (hc : c ≤ 2) (hc' : c' ≤ 2)
    (hT : T ⊆ Finset.range (if c = 2 then n - 3 else n - 2))
    (hT' : T' ⊆ Finset.range (if c' = 2 then n - 3 else n - 2))
    (hne : (c, T) ≠ (c', T')) :
    ∃ ν ψ : ℝ, |ψ| ≤ η' ∧
      (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((((if (c' : ℕ) = 0 then (0 : ℂ) else if (c' : ℕ) = 1 then (1 : ℂ) else
          ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) + ((δ : ℂ) *
          Complex.exp ((((if (c' : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) * (∑ k ∈
          Finset.range (n - 2), if k ∈ T' then z ^ k else 0)) - ((if (c : ℕ) = 0 then (0 : ℂ) else
          if (c : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ)
          * Complex.I)) + ((δ : ℂ) * Complex.exp ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) :
          ℂ) * Complex.I)) * (∑ k ∈ Finset.range (n - 2), if k ∈ T then z ^ k else 0))) : ℂ) = (ρ₀
          : ℂ) * Complex.exp ((((ν + ψ) : ℝ) : ℂ) * Complex.I)) ∧ (((c : ℕ) = 0 ∧ ((ν : ℝ) = 0 ∨ (ν
          : ℝ) = η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ (ν : ℝ) = 3 * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else
          0))) ∨ ((c : ℕ) = 1 ∧ ((ν : ℝ) = π ∨ (ν : ℝ) = π - η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ (ν : ℝ) = 2
          * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else 0))) ∨ ((c : ℕ) = 2 ∧ ((ν : ℝ) = η + π ∨ (ν :
          ℝ) = -η ∨ ∃ κ₀ : ℕ, κ₀ + 4 ≤ n ∧ (ν : ℝ) = 3 * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else
          0)))) := by
  have hπ := Real.pi_pos
  have hzn : ‖z‖ = ρ := pol_norm_eq hρ hz
  have hz1 : ‖z‖ ≤ 1 := by rw [hzn]; exact hρ1
  have hnn : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
  have hE : ∀ c : ℕ, (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ (((δ : ℂ) * Complex.exp ((((if (c : ℕ) = 1 then 2 * η else
      3 * η) : ℝ) : ℂ) * Complex.I)) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((((if (c : ℕ) = 1 then 2 * η
      else 3 * η) : ℝ)) : ℝ) : ℂ) * Complex.I)) :=
    fun c => ⟨δ, hδ, rfl⟩
  have hsub : ∀ {c : ℕ} {T : Finset ℕ}, T ⊆ Finset.range (if c = 2 then n - 3 else n - 2) →
      T ⊆ Finset.range (n - 2) := by
    intro c T h
    refine h.trans ?_
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    split_ifs at hk <;> omega
  by_cases hcc : c = c'
  · subst hcc
    have hTT : T' ≠ T := fun h => hne (by rw [h])
    obtain ⟨k, hk, hiff, u, hu, h1, h2⟩ := pt_diff (z := z) (n := n - 2) hz1
      (hsub hT') (hsub hT) hTT
    rw [hzn] at hu
    have hρn : ((n - 2 : ℕ) : ℝ) * ρ ≤ n * ρ := mul_le_mul_of_nonneg_right hnn hρ.le
    obtain ⟨ψ, hψ, hpol⟩ := pol_one_add hη' hη'2 (u := u) (by linarith)
    have hmul := pol_mul (pol_pow hρ hz k) hpol
    have hdiff : ((if (c : ℕ) = 0 then (0 : ℂ) else if (c : ℕ) = 1 then (1 : ℂ) else ((1 / (2 *
        Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) + ((δ : ℂ) * Complex.exp ((((if
        (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) * (∑ k ∈ Finset.range (n - 2),
        if k ∈ T' then z ^ k else 0)) - ((if (c : ℕ) = 0 then (0 : ℂ) else if (c : ℕ) = 1 then (1 :
        ℂ) else ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) + ((δ : ℂ) *
        Complex.exp ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) * (∑ k ∈
        Finset.range (n - 2), if k ∈ T then z ^ k else 0))
        = ((δ : ℂ) * Complex.exp ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I))
          * ((∑ k ∈ Finset.range (n - 2), if k ∈ T' then z ^ k else 0) - (∑ k ∈ Finset.range (n -
              2), if k ∈ T then z ^ k else 0)) := by
      ring
    have hk4 : c = 2 → k + 4 ≤ n := by
      intro h2c
      have hkm : k ∈ T ∨ k ∈ T' := by
        by_cases hkT : k ∈ T
        · exact Or.inl hkT
        · exact Or.inr (by tauto)
      rcases hkm with hm | hm
      · have := hT hm
        rw [if_pos h2c, Finset.mem_range] at this
        omega
      · have := hT' hm
        rw [if_pos h2c, Finset.mem_range] at this
        omega
    have hnom : (((c : ℕ) = 0 ∧ (((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 * η) + (if
        k ∈ T then π else 0)) : ℝ) = 0 ∨ ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 *
        η) + (if k ∈ T then π else 0)) : ℝ) = η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ ((((if (c : ℕ) = 1 then 2
        * η else 3 * η) : ℝ) + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) = 3 * η + κ₀ * (2 * η)
        + (if κ₀ ∈ T then π else 0))) ∨ ((c : ℕ) = 1 ∧ (((((if (c : ℕ) = 1 then 2 * η else 3 * η) :
        ℝ) + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) = π ∨ ((((if (c : ℕ) = 1 then 2 * η else
        3 * η) : ℝ) + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) = π - η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧
        ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 * η) + (if k ∈ T then π else 0)) :
        ℝ) = 2 * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else 0))) ∨ ((c : ℕ) = 2 ∧ (((((if (c : ℕ) =
        1 then 2 * η else 3 * η) : ℝ) + k * (2 * η) + (if k ∈ T then π else 0)) : ℝ) = η + π ∨
        ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 * η) + (if k ∈ T then π else 0)) :
        ℝ) = -η ∨ ∃ κ₀ : ℕ, κ₀ + 4 ≤ n ∧ ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 *
        η) + (if k ∈ T then π else 0)) : ℝ) = 3 * η + κ₀ * (2 * η) + (if κ₀ ∈ T then π else 0))))
        := by
      interval_cases c
      · exact Or.inl ⟨rfl, Or.inr (Or.inr ⟨k, by omega, by simp⟩)⟩
      · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨k, by omega, by simp⟩)⟩)
      · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨k, hk4 rfl, by simp⟩)⟩)
    refine ⟨((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 * η) + (if k ∈ T then π else 0),
        ψ, hψ, ?_, hnom⟩
    by_cases hkT' : k ∈ T'
    · have hkT : k ∉ T := hiff.mp hkT'
      rw [if_neg hkT, hdiff, h1 hkT']
      have := pol_mul (hE c) hmul
      have e : ((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + ((k : ℝ) * (2 * η) + ψ) = ((if (c :
          ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 * η) + 0 + ψ := by ring
      rwa [e] at this
    · have hkT : k ∈ T := by tauto
      rw [if_pos hkT, hdiff, h2 hkT']
      have := pol_mul (hE c) (pol_neg hmul)
      have e : ((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + ((k : ℝ) * (2 * η) + ψ + π) = ((if (c
          : ℕ) = 1 then 2 * η else 3 * η) : ℝ) + k * (2 * η) + π + ψ := by ring
      rwa [e] at this
  · obtain ⟨d, hpol, hnorm, hcase⟩ := ctr_dir hη hη2 hc hc' hcc
    set w : ℂ := ((δ : ℂ) * Complex.exp ((((if (c' : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) *
        Complex.I)) * (∑ k ∈ Finset.range (n - 2), if k ∈ T' then z ^ k else 0)
      - ((δ : ℂ) * Complex.exp ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) *
          (∑ k ∈ Finset.range (n - 2), if k ∈ T then z ^ k else 0) with hw
    have hb : ∀ (c : ℕ) (T : Finset ℕ),
        ‖((δ : ℂ) * Complex.exp ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) *
            (∑ k ∈ Finset.range (n - 2), if k ∈ T then z ^ k else 0)‖ ≤ δ * n := by
      intro c T
      rw [norm_mul, pol_norm_eq hδ rfl]
      have := pt_norm hz1 (n - 2) T
      nlinarith
    have hwn : ‖w‖ ≤ δ * n + δ * n := by
      rw [hw]
      exact (norm_sub_le _ _).trans (add_le_add (hb c' T') (hb c T))
    obtain ⟨ψ, hψ, hp⟩ := pol_far hη' hη'2 hpol hnorm (w := w) (by nlinarith)
    have hdiff : ((if (c' : ℕ) = 0 then (0 : ℂ) else if (c' : ℕ) = 1 then (1 : ℂ) else ((1 / (2 *
        Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) + ((δ : ℂ) * Complex.exp ((((if
        (c' : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) * (∑ k ∈ Finset.range (n - 2),
        if k ∈ T' then z ^ k else 0)) - ((if (c : ℕ) = 0 then (0 : ℂ) else if (c : ℕ) = 1 then (1 :
        ℂ) else ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) + ((δ : ℂ) *
        Complex.exp ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) * (∑ k ∈
        Finset.range (n - 2), if k ∈ T then z ^ k else 0))
        = (if (c' : ℕ) = 0 then (0 : ℂ) else if (c' : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos
            η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) - (if (c : ℕ) = 0 then (0 : ℂ) else
            if (c : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η :
            ℂ) * Complex.I)) + w := by
      simp only [hw]; ring
    refine ⟨d, ψ, hψ, by rw [hdiff]; exact hp, ?_⟩
    rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rcases h with h | h
      · exact Or.inl ⟨rfl, Or.inl h⟩
      · exact Or.inl ⟨rfl, Or.inr (Or.inl h)⟩
    · rcases h with h | h
      · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
      · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl h)⟩)
    · rcases h with h | h
      · exact Or.inr (Or.inr ⟨rfl, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl h)⟩)

set_option maxHeartbeats 1000000 in
lemma upper2 {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ (n - 1) + 2 ^ (n - 3) ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < π - 2 * (π / (2 * n - 1)) + ε := by
  classical
  have hπ := Real.pi_pos
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by linarith
  set η : ℝ := π / (2 * n - 1) with hηdef
  have hden : (0 : ℝ) < 2 * n - 1 := by linarith
  have hη : 0 < η := by positivity
  have hM : 2 * (n : ℝ) * η - η = π := by rw [hηdef]; field_simp
  have hη5 : 5 * η ≤ π := by nlinarith
  have hη2 : η < π / 2 := by linarith
  set η' : ℝ := min ε η / 4 with hη'def
  have hm : 0 < min ε η := lt_min hε hη
  have hη' : 0 < η' := by positivity
  have hη'ε : 4 * η' ≤ ε := by rw [hη'def]; linarith [min_le_left ε η]
  have hη'η : 4 * η' ≤ η := by rw [hη'def]; linarith [min_le_right ε η]
  have hsin : 0 < Real.sin η' := Real.sin_pos_of_pos_of_lt_pi hη' (by linarith)
  set ρ : ℝ := Real.sin η' / (2 * n) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ2 : 2 * (n * ρ) = Real.sin η' := by rw [hρdef]; field_simp
  have hρ1 : ρ ≤ 1 := by
    have := Real.sin_le_one η'
    nlinarith
  set δ : ℝ := Real.sin η' / (8 * n) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ2 : 8 * (n * δ) = Real.sin η' := by rw [hδdef]; field_simp
  set z : ℂ := (ρ : ℂ) * Complex.exp (((2 * η : ℝ) : ℂ) * Complex.I) with hz
  set I : Finset (ℕ × Finset ℕ) :=
    ((Finset.range 2) ×ˢ (Finset.range (n - 2)).powerset) ∪
      (({2} : Finset ℕ) ×ˢ (Finset.range (n - 3)).powerset) with hI
  have hImem : ∀ i ∈ I, i.1 ≤ 2 ∧ i.2 ⊆ Finset.range (if i.1 = 2 then n - 3 else n - 2) := by
    intro i hi
    rw [hI, Finset.mem_union, Finset.mem_product, Finset.mem_product, Finset.mem_range,
      Finset.mem_powerset, Finset.mem_powerset, Finset.mem_singleton] at hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨by omega, ?_⟩
      rw [if_neg (by omega)]; exact h2
    · refine ⟨by omega, ?_⟩
      rw [if_pos h1]; exact h2
  obtain ⟨F, hF⟩ : ∃ F : ℕ × Finset ℕ → ℂ, ∀ (c : ℕ) (T : Finset ℕ),
      F (c, T) = ((if (c : ℕ) = 0 then (0 : ℂ) else if (c : ℕ) = 1 then (1 : ℂ) else ((1 / (2 *
          Real.cos η) : ℝ) : ℂ) * Complex.exp ((η : ℂ) * Complex.I)) + ((δ : ℂ) * Complex.exp
          ((((if (c : ℕ) = 1 then 2 * η else 3 * η) : ℝ) : ℂ) * Complex.I)) * (∑ k ∈ Finset.range
          (n - 2), if k ∈ T then z ^ k else 0)) := ⟨fun i => ((if (i.1 : ℕ) = 0 then (0 : ℂ) else
          if (i.1 : ℕ) = 1 then (1 : ℂ) else ((1 / (2 * Real.cos η) : ℝ) : ℂ) * Complex.exp ((η :
          ℂ) * Complex.I)) + ((δ : ℂ) * Complex.exp ((((if (i.1 : ℕ) = 1 then 2 * η else 3 * η) :
          ℝ) : ℂ) * Complex.I)) * (∑ k ∈ Finset.range (n - 2), if k ∈ i.2 then z ^ k else 0)), fun
          _ _ => rfl⟩
  have hray : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∃ ν ψ : ℝ, |ψ| ≤ η' ∧
      (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ((F j - F i) : ℂ) = (ρ₀ : ℂ) * Complex.exp ((((ν + ψ) : ℝ) : ℂ) *
          Complex.I)) ∧ (((i.1 : ℕ) = 0 ∧ ((ν : ℝ) = 0 ∨ (ν : ℝ) = η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ (ν :
          ℝ) = 3 * η + κ₀ * (2 * η) + (if κ₀ ∈ i.2 then π else 0))) ∨ ((i.1 : ℕ) = 1 ∧ ((ν : ℝ) = π
          ∨ (ν : ℝ) = π - η ∨ ∃ κ₀ : ℕ, κ₀ + 3 ≤ n ∧ (ν : ℝ) = 2 * η + κ₀ * (2 * η) + (if κ₀ ∈ i.2
          then π else 0))) ∨ ((i.1 : ℕ) = 2 ∧ ((ν : ℝ) = η + π ∨ (ν : ℝ) = -η ∨ ∃ κ₀ : ℕ, κ₀ + 4 ≤
          n ∧ (ν : ℝ) = 3 * η + κ₀ * (2 * η) + (if κ₀ ∈ i.2 then π else 0)))) := by
    rintro ⟨c, T⟩ hi ⟨c', T'⟩ hj hne
    rw [hF, hF]
    obtain ⟨a1, a2⟩ := hImem _ hi
    obtain ⟨b1, b2⟩ := hImem _ hj
    exact ray hη hη2 hη' (by linarith) hρ hρ1 hρ2.le hδ hδ2.le hz a1 b1 a2 b2 hne
  have hinj : Set.InjOn F (I : Set (ℕ × Finset ℕ)) := by
    intro i hi j hj he
    by_contra hne
    obtain ⟨ν, ψ, -, hpol, -⟩ := hray i hi j hj hne
    exact pol_ne_zero hpol (by rw [he, sub_self])
  have hcard : I.card = 2 ^ (n - 1) + 2 ^ (n - 3) := by
    rw [hI, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
      Finset.card_powerset, Finset.card_powerset, Finset.card_range, Finset.card_range,
      Finset.card_range, Finset.card_singleton]
    · have : n - 1 = (n - 2) + 1 := by omega
      rw [this, pow_succ]; ring
    · rw [Finset.disjoint_left]
      intro i h1 h2
      rw [Finset.mem_product, Finset.mem_range] at h1
      rw [Finset.mem_product, Finset.mem_singleton] at h2
      omega
  refine ⟨I.image F, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, hcard]
  · intro p hp q hq r hr hpq hrq
    obtain ⟨ip, hip, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨iq, hiq, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ir, hir, rfl⟩ := Finset.mem_image.mp hr
    have hpq' : iq ≠ ip := fun h => hpq (by rw [h])
    have hrq' : iq ≠ ir := fun h => hrq (by rw [h])
    obtain ⟨ν1, ψ1, hψ1, hpol1, hnom1⟩ := hray iq hiq ip hip hpq'
    obtain ⟨ν2, ψ2, hψ2, hpol2, hnom2⟩ := hray iq hiq ir hir hrq'
    have hg := good hη hn hM hnom1 hnom2
    obtain ⟨x1, x2⟩ := abs_le.mp hψ1
    obtain ⟨y1, y2⟩ := abs_le.mp hψ2
    have hle : EuclideanGeometry.angle (F ip) (F iq) (F ir) ≤ π - 2 * η + 2 * η' := by
      refine angle_le hpol1 hpol2 (by linarith) ?_
      rcases hg with h | h | h
      · left
        obtain ⟨g1, g2⟩ := abs_le.mp h
        rw [abs_le]; constructor <;> linarith
      · right; left
        obtain ⟨g1, g2⟩ := abs_le.mp h
        rw [abs_le]; constructor <;> linarith
      · right; right
        obtain ⟨g1, g2⟩ := abs_le.mp h
        rw [abs_le]; constructor <;> linarith
    linarith

-- ===== L1, L2: the lower bounds of Sendov 1995 (NOT YET PROVED: the only two open pieces) =====
-- lower1: more than 2^(n-1) + 2^(n-3) points contain an angle >= (1 - 1/n) pi.
-- lower2: more than 2^(n-1) points contain an angle >= (1 - 2/(2n-1)) pi.
-- ===== Assembly: the supremum bookkeeping, from H1, H2, upper and upper2 =====

lemma minimax_eq {N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ π)
    (hL : ∀ S : Finset ℂ, S.card = N → ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
      v ≤ EuclideanGeometry.angle x z y)
    (hU : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℂ, N ≤ S.card ∧ ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
      p ≠ q → r ≠ q → EuclideanGeometry.angle p q r < v + ε) :
    Erdos504.minimaxAngle N = v := by
  unfold Erdos504.minimaxAngle
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨⟨hv0, hv1⟩, hL⟩
  · rintro α ⟨-, hα⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨S, hc, hS⟩ := hU (α - v) (by linarith)
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hc
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, -, hle⟩ := hα t htc
    have := hS x (hts hx) z (hts hz) y (hts hy) hxz hyz
    linarith

theorem assembly (L1 : H1) (L2 : H2) {n N : ℕ} (hn : 3 ≤ n) (h1 : 2 ^ (n - 1) < N) (h2 : N ≤ 2 ^ n)
    :
    Erdos504.minimaxAngle N =
      if 2 ^ (n - 1) + 2 ^ (n - 3) < N then (1 - 1 / (n : ℝ)) * π
      else (1 - 2 / (2 * (n : ℝ) - 1)) * π := by
  have hπ := Real.pi_pos
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  split_ifs with h
  · have e : (1 - 1 / (n : ℝ)) * π = π - π / n := by field_simp
    have hdiv : 0 < π / n := by positivity
    have hdiv1 : π / n ≤ π := div_le_self hπ.le (by linarith)
    apply minimax_eq (by rw [e]; linarith) (by rw [e]; linarith)
    · intro S hS
      exact L1 hn S (by rw [hS]; exact h)
    · intro ε hε
      obtain ⟨S, hc, hS⟩ := upper (n := n) (by omega) hε
      refine ⟨S, by rw [hc]; exact h2, ?_⟩
      rw [e]; exact hS
  · have hden : (0 : ℝ) < 2 * n - 1 := by linarith
    have e : (1 - 2 / (2 * (n : ℝ) - 1)) * π = π - 2 * (π / (2 * n - 1)) := by field_simp
    have hdiv : 0 < π / (2 * n - 1) := by positivity
    have hdiv1 : 2 * (π / (2 * (n : ℝ) - 1)) ≤ π := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith
    apply minimax_eq (by rw [e]; linarith) (by rw [e]; linarith)
    · intro S hS
      exact L2 hn S (by rw [hS]; exact h1)
    · intro ε hε
      obtain ⟨S, hc, hS⟩ := upper2 hn hε
      refine ⟨S, by rw [hc]; omega, ?_⟩
      rw [e]; exact hS

theorem main : H1 → H2 → type_of% @Erdos504.erdos_504.variants.sendov := by
  intro L1 L2 n N hn h1 h2
  exact assembly L1 L2 hn h1 h2

end OMA.R_Erdos504_erdos_504_variants_sendov_R1
