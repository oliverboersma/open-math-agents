import OMAReductions.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1
import Mathlib

/-!
# Small and dyadic conductors for the primitive character mean

The split and the quantitative estimates are adapted from nil-commits,
Arithmetica4, RHDirect/Stage11BombieriVinogradov.lean at commit
023f6441c22a9ca0db1670e351e8ac44f00555ea, used under Apache-2.0.
Siegel–Walfisz gives cancellation for the small conductors. For larger
conductors, Vaughan's identity and the multiplicative large sieve give a
dyadic estimate. The proof sums the dyadic intervals and fixes the
logarithmic parameters for the two ranges.
-/
noncomputable section
open Complex DirichletCharacter Finset Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators Classical
namespace OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1
private lemma eventually_log_rpow_le_rpow_eighth (M : ℝ) (hM : 0 < M) :
    ∃ X : ℝ, 4 ≤ X ∧ ∀ x : ℝ, X ≤ x → (Real.log x) ^ M ≤ x ^ (1 / 8 : ℝ) := by
  have hα : (0 : ℝ) < 1 / (8 * M) := by positivity
  have hev := ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨max 4 X₁, le_max_left _ _, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hLx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlt : Real.log x / x ^ (1 / (8 * M)) < 1 := hX₁ x hx1
  have hle1 : Real.log x ≤ x ^ (1 / (8 * M)) :=
    ((div_lt_one (Real.rpow_pos_of_pos hx0 _)).mp hlt).le
  have hpow := Real.rpow_le_rpow hLx_nn hle1 hM.le
  rw [← Real.rpow_mul hx0.le] at hpow
  have hexp : 1 / (8 * M) * M = 1 / 8 := by field_simp [hM.ne']
  rwa [hexp] at hpow

/-- Helper: for any `c > 0` and `P > 0`, `∃ X ≥ 4, ∀ x ≥ X, (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1`. -/
private lemma eventually_log_rpow_mul_exp_neg_sqrt_le_one {c P : ℝ} (hc : 0 < c) (hP : 0 < P) :
    ∃ X : ℝ, 4 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
  have hratio : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun u => by rw [Real.sqrt_eq_rpow]
  have hcomp : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) atTop (𝓝 0) :=
    hratio.comp Real.tendsto_log_atTop
  have hev := hcomp.eventually (Iio_mem_nhds (div_pos hc hP))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨max 4 X₁, le_max_left _ _, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hsq_pos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLx_pos
  have hlt : Real.log (Real.log x) / Real.sqrt (Real.log x) < c / P := hX₁ x hx1
  have hmul : P * Real.log (Real.log x) < c * Real.sqrt (Real.log x) := by
    have h1 := (div_lt_iff₀ hsq_pos).mp hlt
    have h2 := mul_lt_mul_of_pos_left h1 hP
    have h3 : P * (c / P * Real.sqrt (Real.log x)) = c * Real.sqrt (Real.log x) := by
      field_simp [hP.ne']
    linarith
  rw [Real.rpow_def_of_pos hLx_pos, ← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by linarith)

private lemma sum_biUnion_le_local {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion :
        ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) (f := f) fun b _ => hf b]
    linarith

/-- Siegel–Walfisz for nonprincipal primitive characters of logarithmic conductor. -/
def H1 : Prop := ∃ c : ℝ, 0<c ∧ ∀ D : ℝ, 0<D → ∃ C : ℝ, 0<C ∧
  ∀ x : ℝ, 4≤x → ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ (Real.log x)^D →
  ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ≠1 →
    ‖∑ n ∈ range (⌊x⌋₊+1), χ (n:ZMod q)*(Λ n:ℂ)‖ ≤ C*x*Real.exp (-c*Real.sqrt (Real.log x))

/-- Vaughan's dyadic estimate with two truncation parameters and a relative block width. -/
def H2 : Prop := ∀ {D U V : ℕ} {x Δ : ℝ},
  1≤D → 1≤U → 1≤V → 3≤x → (D:ℝ)≤x → (V:ℝ)≤x → 0<Δ → Δ<1 →
    ∑ k ∈ Finset.Ico D (2 * D),
        (1 / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖(∑ n ∈ range (⌊x⌋₊+1), χ (n:ZMod (k+1))*(Λ n:ℂ))‖ ≤
      180 * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 4

open Classical in

set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1.H2 := by
  classical
  intro sw dyad A hA
  let psi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :=
    ∑ n ∈ range (⌊x⌋₊+1), χ (n:ZMod q)*(Λ n:ℂ)
  set A' : ℝ := max A 1 with hA'_def
  have hA'1 : 1 ≤ A' := le_max_right A 1
  have hA_le_A' : A ≤ A' := le_max_left A 1
  set B : ℝ := 2 * A' + 20 with hB_def
  set B₁ : ℝ := A' + 10 with hB1_def
  set E : ℝ := 2 * A' + 16 with hE_def
  set K : ℝ := 4 * A' + 40 with hK_def
  set M_exp : ℝ := 10 * A' + 100 with hM_def
  have hB_pos : 0 < B := by dsimp only [B]; linarith
  have hB1_pos : 0 < B₁ := by dsimp only [B₁]; linarith
  have hE_pos : 0 < E := by dsimp only [E]; linarith
  have hK_pos : 0 < K := by dsimp only [K]; linarith

  obtain ⟨c_sw,hc_sw,hsw_all⟩ := sw
  obtain ⟨C_sw,hC_sw,hsw_char⟩ := hsw_all B₁ hB1_pos
  obtain ⟨X_pow, hX_pow4, hlog_pow⟩ := eventually_log_rpow_le_rpow_eighth M_exp (by dsimp only [M_exp]; linarith)
  obtain ⟨X_sw, hX_sw4, hlog_sw⟩ := eventually_log_rpow_mul_exp_neg_sqrt_le_one hc_sw (by dsimp only [B₁]; linarith : 0 < B₁ + A' + 5)

  let C := 12*C_sw+99999000
  refine ⟨B,C,by dsimp [B]; linarith,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop X_pow,eventually_ge_atTop X_sw,eventually_ge_atTop (Real.exp 2)] with x hp hs he
  have hx4 : 4≤x := hX_pow4.trans hp
  have hx3 : 3≤x := by linarith
  have hx0 : 0<x := by linarith
  have hLx_ge2 : 2≤Real.log x := by simpa using Real.log_le_log (Real.exp_pos _) he
  have hLx_gt1 : 1<Real.log x := by linarith
  have hLx_pos : 0<Real.log x := by linarith
  have hpow_bd := hlog_pow x hp
  have hsw_decay := hlog_sw x hs
  set Q : ℕ := ⌊Real.sqrt x / (Real.log x)^B⌋₊ with hQ_def
  have hL_le_x8 : ∀ p : ℝ, 0 ≤ p → p ≤ M_exp → (Real.log x) ^ p ≤ x ^ (1 / 8 : ℝ) := fun p _ hpM =>
    (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hpM).trans hpow_bd
  have hQR_le : (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B :=
    Nat.floor_le (by positivity)
  have hQ_le_x : (Q : ℝ) ≤ x := by
    calc (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B := hQR_le
      _ ≤ Real.sqrt x := div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLx_gt1.le hB_pos.le)
      _ ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  set Q₁ : ℕ := ⌊(Real.log x) ^ B₁⌋₊ with hQ1_def
  have hQ1_ge2 : 2 ≤ Q₁ := by
    have h2B1 : (2 : ℝ) ≤ (Real.log x) ^ B₁ := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (Real.log x) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hLx_ge2 (by norm_num)
        _ ≤ (Real.log x) ^ B₁ := Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B₁]; linarith)
    exact Nat.le_floor h2B1
  have hQ1_le_R : (Q₁ : ℝ) ≤ (Real.log x) ^ B₁ := Nat.floor_le (by positivity)
  have hQ1_ge_half : (Real.log x) ^ B₁ / 2 ≤ (Q₁ : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((Real.log x) ^ B₁)
    have h2 : (2 : ℝ) ≤ (Q₁ : ℝ) := by exact_mod_cast hQ1_ge2
    linarith
  -- Split `Ico 2 Q` into `Ico 2 (min Q₁ Q)` and `Ico Q₁ Q`
  have hsplit_prim :
      ∑ k ∈ Finset.Ico 2 Q,
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖psi ψ x‖ ≤
        (∑ k ∈ Finset.Ico 2 (min Q₁ Q),
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖psi ψ x‖) +
        (∑ k ∈ Finset.Ico Q₁ Q,
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖psi ψ x‖) := by
    by_cases hQQ1 : Q ≤ Q₁
    · have hmin : min Q₁ Q = Q := Nat.min_eq_right hQQ1
      have hempty : Finset.Ico Q₁ Q = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hmin, hempty, Finset.sum_empty, add_zero]
    · push Not at hQQ1
      have hmin : min Q₁ Q = Q₁ := Nat.min_eq_left hQQ1.le
      rw [hmin]
      have hunion : Finset.Ico 2 Q = Finset.Ico 2 Q₁ ∪ Finset.Ico Q₁ Q := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Ico 2 Q₁) (Finset.Ico Q₁ Q) := by
        rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj]
  -- Bound 3a: Small conductors `k ∈ Ico 2 (min Q₁ Q)` via Siegel–Walfisz
  have hsmall_cond :
      12 * Real.log x *
        ∑ k ∈ Finset.Ico 2 (min Q₁ Q),
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖psi ψ x‖ ≤
        12 * C_sw * x / (Real.log x) ^ A' := by
    have hper_k : ∀ k ∈ Finset.Ico 2 (min Q₁ Q),
        (1 / (Nat.totient (k + 1) : ℝ)) *
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
            ‖psi ψ x‖ ≤
          C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) := by
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
      have hkQ1 : k + 1 ≤ Q₁ := by have := (Finset.mem_Ico.mp hk).2; omega
      have hmod_le : ((k + 1 : ℕ) : ℝ) ≤ (Real.log x) ^ B₁ :=
        (by exact_mod_cast hkQ1 : ((k + 1 : ℕ) : ℝ) ≤ (Q₁ : ℝ)).trans hQ1_le_R
      have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
        Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
      have htot : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (k + 1)
      have hcard :
          ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card : ℝ) ≤
            (Nat.totient (k + 1) : ℝ) := by
        have hnat : (Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card ≤
            (k + 1).totient := by
          calc _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).card := Finset.card_filter_le _ _
            _ = (k + 1).totient := by rw [Finset.card_univ, htot]
        exact_mod_cast hnat
      calc (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖psi ψ x‖
          ≤ (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ _ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ψ hψ => ?_) (by positivity)
            have hprim : ψ.IsPrimitive := (Finset.mem_filter.mp hψ).2
            have hne1 : ψ ≠ 1 := by
              intro h1
              have hc : ψ.conductor = k + 1 := hprim
              rw [h1, DirichletCharacter.conductor_one] at hc
              omega
            exact hsw_char x hx4 (k + 1) hmod_le ψ hprim hne1
        _ = (((Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card : ℝ) /
              (Nat.totient (k + 1) : ℝ)) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) :=
            mul_le_mul_of_nonneg_right ((div_le_one hphi_pos).mpr hcard) (by positivity)
        _ = C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) := one_mul _
    have hsum_k :
        ∑ k ∈ Finset.Ico 2 (min Q₁ Q),
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖psi ψ x‖ ≤
          (Q₁ : ℝ) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
      calc _ ≤ ∑ _k ∈ Finset.Ico 2 (min Q₁ Q), (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) :=
              Finset.sum_le_sum hper_k
        _ = ((Finset.Ico 2 (min Q₁ Q)).card : ℝ) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Q₁ : ℝ) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [Nat.card_Ico]; exact_mod_cast (by omega : min Q₁ Q - 2 ≤ Q₁)
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
    have hpow_le : Real.log x * (Real.log x) ^ B₁ * (Real.log x) ^ A' ≤ (Real.log x) ^ (B₁ + A' + 5) := by
      have hEq : (Real.log x) ^ (1 + B₁ + A') = Real.log x * (Real.log x) ^ B₁ * (Real.log x) ^ A' := by
        rw [Real.rpow_add hLx_pos, Real.rpow_add hLx_pos, Real.rpow_one]
      rw [← hEq]
      exact Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by linarith)
    calc 12 * Real.log x *
          (∑ k ∈ Finset.Ico 2 (min Q₁ Q),
            (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖psi ψ x‖) * (Real.log x) ^ A'
        ≤ 12 * Real.log x * ((Real.log x) ^ B₁ * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)))) *
            (Real.log x) ^ A' := by
          have h1 := hsum_k.trans (mul_le_mul_of_nonneg_right hQ1_le_R (by positivity))
          have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 12 * Real.log x by positivity)
          exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLx_pos.le A')
      _ = 12 * C_sw * x * ((Real.log x * (Real.log x) ^ B₁ * (Real.log x) ^ A') *
            Real.exp (-c_sw * Real.sqrt (Real.log x))) := by ring
      _ ≤ 12 * C_sw * x * ((Real.log x) ^ (B₁ + A' + 5) * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
          gcongr
      _ ≤ 12 * C_sw * x * 1 := mul_le_mul_of_nonneg_left hsw_decay (by positivity)
      _ = 12 * C_sw * x := mul_one _
  -- Bound 3b: Large conductors `k ∈ Ico Q₁ Q` via Dyadic Vaughan + Large Sieve!
  have hlarge_cond :
      12 * Real.log x *
        ∑ k ∈ Finset.Ico Q₁ Q,
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖psi ψ x‖ ≤
        99999000 * x / (Real.log x) ^ A' := by
    by_cases hQQ1 : Q ≤ Q₁
    · have hempty : Finset.Ico Q₁ Q = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, mul_zero]; positivity
    · push Not at hQQ1
      set Δ : ℝ := (Real.log x) ^ (-E) with hΔ_def
      have hΔ0 : 0 < Δ := Real.rpow_pos_of_pos hLx_pos (-E)
      have hΔ1 : Δ < 1 := by
        rw [hΔ_def, Real.rpow_neg hLx_pos.le]
        exact inv_lt_one_of_one_lt₀ (by
          calc (1 : ℝ) < Real.log x := hLx_gt1
            _ = (Real.log x) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (Real.log x) ^ E := Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [E]; linarith))
      set U : ℕ := ⌊(Real.log x) ^ K⌋₊ with hU_def
      have hU_ge2 : 2 ≤ U := by
        have h2K : (2 : ℝ) ≤ (Real.log x) ^ K := by
          calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
            _ ≤ (Real.log x) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hLx_ge2 (by norm_num)
            _ ≤ (Real.log x) ^ K := Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [K]; linarith)
        exact Nat.le_floor h2K
      have hU_le_R : (U : ℝ) ≤ (Real.log x) ^ K := Nat.floor_le (by positivity)
      have hU_ge_half : (Real.log x) ^ K / 2 ≤ (U : ℝ) := by
        have hlt := Nat.lt_floor_add_one ((Real.log x) ^ K)
        have h2 : (2 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU_ge2
        linarith
      have hU_le_x : (U : ℝ) ≤ x := by
        calc (U : ℝ) ≤ (Real.log x) ^ K := hU_le_R
          _ ≤ x ^ (1 / 8 : ℝ) := hL_le_x8 K hK_pos.le (by dsimp only [K, M_exp]; linarith)
          _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = x := Real.rpow_one x
      -- Cover `Ico Q₁ Q` by `J = Nat.log 2 (Q / Q₁) + 1` dyadic blocks `Ico (Q₁ * 2^j) (2 * (Q₁ * 2^j))`
      set J : ℕ := Nat.log 2 (Q / Q₁) + 1 with hJ_def
      have hcover : Finset.Ico Q₁ Q ⊆
          (Finset.range J).biUnion (fun j => Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j))) := by
        intro k hk
        simp only [Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_range] at hk ⊢
        refine ⟨Nat.log 2 (k / Q₁), ?_, ?_, ?_⟩
        · have hdiv_le : k / Q₁ ≤ Q / Q₁ := Nat.div_le_div_right hk.2.le
          have hlog_le : Nat.log 2 (k / Q₁) ≤ Nat.log 2 (Q / Q₁) := Nat.log_mono_right hdiv_le
          omega
        · have hk_div : 1 ≤ k / Q₁ := Nat.div_pos hk.1 (by omega)
          have hpow : 2 ^ Nat.log 2 (k / Q₁) ≤ k / Q₁ := Nat.pow_log_le_self 2 (by omega)
          calc Q₁ * 2 ^ Nat.log 2 (k / Q₁) ≤ Q₁ * (k / Q₁) := Nat.mul_le_mul_left Q₁ hpow
            _ ≤ k := Nat.mul_div_le k Q₁
        · have hlt : k / Q₁ < 2 ^ (Nat.log 2 (k / Q₁) + 1) :=
            Nat.lt_pow_succ_log_self (by omega) (k / Q₁)
          have hdiv := Nat.div_add_mod k Q₁
          have hmod : k % Q₁ < Q₁ := Nat.mod_lt k (by omega)
          have hpow : 2 ^ (Nat.log 2 (k / Q₁) + 1) = 2 * 2 ^ Nat.log 2 (k / Q₁) := by
            rw [pow_succ, mul_comm]
          have h1 : k < Q₁ * (k / Q₁ + 1) := by nlinarith
          have h2 : k / Q₁ + 1 ≤ 2 * 2 ^ Nat.log 2 (k / Q₁) := by omega
          calc k < Q₁ * (k / Q₁ + 1) := h1
            _ ≤ Q₁ * (2 * 2 ^ Nat.log 2 (k / Q₁)) := Nat.mul_le_mul_left Q₁ h2
            _ = 2 * (Q₁ * 2 ^ Nat.log 2 (k / Q₁)) := by ring
      have hbiUnion_le :
          ∑ k ∈ Finset.Ico Q₁ Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖psi ψ x‖ ≤
            ∑ j ∈ Finset.range J,
              ∑ k ∈ Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j)),
                (1 / (Nat.totient (k + 1) : ℝ)) *
                  ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                    ‖psi ψ x‖ := by
        calc _ ≤ ∑ k ∈ (Finset.range J).biUnion (fun j => Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j))),
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖psi ψ x‖ :=
                Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ =>
                  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          _ ≤ _ := sum_biUnion_le_local _ _ _ fun _ =>
                mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      -- Bound each dyadic block `j < J` (with `D = Q₁ * 2^j ∈ [Q₁, Q]`) by `50000 * x / (log x)^(A' + 2)`!
      have hper_j : ∀ j ∈ Finset.range J,
          ∑ k ∈ Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j)),
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖psi ψ x‖ ≤
            60000 * x / (Real.log x) ^ (A' + 2) := by
        intro j hj
        set D : ℕ := Q₁ * 2 ^ j
        have hD1 : 1 ≤ D := Nat.mul_pos (by omega) (by positivity)
        have hD_ge_Q1 : Q₁ ≤ D := Nat.le_mul_of_pos_right Q₁ (by positivity)
        have hD_le_Q : D ≤ Q := by
          have hj_le : j ≤ Nat.log 2 (Q / Q₁) := by have := Finset.mem_range.mp hj; omega
          have hpow : 2 ^ j ≤ Q / Q₁ :=
            (Nat.pow_le_pow_right (by omega) hj_le).trans (Nat.pow_log_le_self 2 (by
              have : 1 ≤ Q / Q₁ := Nat.div_pos hQQ1.le (by omega); omega))
          calc D = Q₁ * 2 ^ j := rfl
            _ ≤ Q₁ * (Q / Q₁) := Nat.mul_le_mul_left Q₁ hpow
            _ ≤ Q := Nat.mul_div_le Q Q₁
        have hD_le_QR : (D : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B :=
          (by exact_mod_cast hD_le_Q : (D : ℝ) ≤ (Q : ℝ)).trans hQR_le
        have hD_le_x : (D : ℝ) ≤ x := (by exact_mod_cast hD_le_Q : (D : ℝ) ≤ (Q : ℝ)).trans hQ_le_x
        have hD_le_sqx : (D : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]
          exact hD_le_QR.trans (div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLx_gt1.le hB_pos.le))
        have hdy := dyad hD1 (by omega : 1 ≤ U) (by omega : 1 ≤ U)
          hx3 hD_le_x hU_le_x hΔ0 hΔ1
        -- Bound each of the 9 terms inside `hdy` by `2 * x / (log x)^(A' + 6)`
        have hsqrtΔ : Real.sqrt Δ = (Real.log x) ^ (-(E / 2)) := by
          rw [hΔ_def, Real.sqrt_eq_rpow, ← Real.rpow_mul hLx_pos.le]; congr 1; ring
        have hsqrtU_ge : (Real.log x) ^ (K / 2) / 2 ≤ Real.sqrt (U : ℝ) := by
          have h1 : Real.sqrt ((Real.log x) ^ K / 2) ≤ Real.sqrt (U : ℝ) := Real.sqrt_le_sqrt hU_ge_half
          have h2 : (Real.log x) ^ (K / 2) / 2 ≤ Real.sqrt ((Real.log x) ^ K / 2) := by
            rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hLx_pos.le,
              show K * (1 / 2 : ℝ) = K / 2 by ring]
            exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by norm_num))
              (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
          exact h2.trans h1
        have ht1 : (D : ℝ) * (U : ℝ) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos _)]
          have h1 : (U : ℝ) * (Real.log x) ^ (A' + 6) ≤ x ^ (1 / 8 : ℝ) := by
            have hEq : (Real.log x) ^ K * (Real.log x) ^ (A' + 6) = (Real.log x) ^ (K + A' + 6) := by
              rw [← Real.rpow_add hLx_pos]; congr 1; ring
            calc (U : ℝ) * (Real.log x) ^ (A' + 6)
                ≤ (Real.log x) ^ K * (Real.log x) ^ (A' + 6) :=
                  mul_le_mul_of_nonneg_right hU_le_R (by positivity)
              _ = (Real.log x) ^ (K + A' + 6) := hEq
              _ ≤ x ^ (1 / 8 : ℝ) := hL_le_x8 _ (by dsimp only [K]; linarith) (by dsimp only [K, M_exp]; linarith)
          calc (D : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6)
              = (D : ℝ) * ((U : ℝ) * (Real.log x) ^ (A' + 6)) := by ring
            _ ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 8 : ℝ) := mul_le_mul hD_le_sqx h1 (by positivity) (by positivity)
            _ = x ^ (5 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
            _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = x := Real.rpow_one x
            _ ≤ 2 * x := by linarith
        have ht2 : (U : ℝ) * (U : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos _)]
          have hD32 : (D : ℝ) * Real.sqrt (D : ℝ) ≤ x ^ (3 / 4 : ℝ) := by
            have hsqD : Real.sqrt (D : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
              calc ((D : ℝ)) ^ (1 / 2 : ℝ) ≤ (x ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
                    Real.rpow_le_rpow (Nat.cast_nonneg _) hD_le_sqx (by norm_num)
                _ = x ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hx0.le]; norm_num
            calc (D : ℝ) * Real.sqrt (D : ℝ) ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) :=
                  mul_le_mul hD_le_sqx hsqD (Real.sqrt_nonneg _) (by positivity)
              _ = x ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
          have hU2 : (U : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6) ≤ x ^ (1 / 8 : ℝ) := by
            have hEq : (Real.log x) ^ K * (Real.log x) ^ K * (Real.log x) ^ (A' + 6) =
                (Real.log x) ^ (2 * K + A' + 6) := by
              rw [← Real.rpow_add hLx_pos, ← Real.rpow_add hLx_pos]; congr 1; ring
            calc (U : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6)
                ≤ (Real.log x) ^ K * (Real.log x) ^ K * (Real.log x) ^ (A' + 6) := by gcongr
              _ = (Real.log x) ^ (2 * K + A' + 6) := hEq
              _ ≤ x ^ (1 / 8 : ℝ) := hL_le_x8 _ (by dsimp only [K]; linarith) (by dsimp only [K, M_exp]; linarith)
          calc (U : ℝ) * (U : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) * (Real.log x) ^ (A' + 6)
              = ((U : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6)) * ((D : ℝ) * Real.sqrt (D : ℝ)) := by ring
            _ ≤ x ^ (1 / 8 : ℝ) * x ^ (3 / 4 : ℝ) := mul_le_mul hU2 hD32 (by positivity) (by positivity)
            _ = x ^ (7 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
            _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = x := Real.rpow_one x
            _ ≤ 2 * x := by linarith
        have ht3 : x / (D : ℝ) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          have hD_lo : (Real.log x) ^ (A' + 6) / 2 ≤ (D : ℝ) := by
            calc (Real.log x) ^ (A' + 6) / 2
                ≤ (Real.log x) ^ B₁ / 2 := div_le_div_of_nonneg_right
                  (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B₁]; linarith)) (by norm_num)
              _ ≤ (Q₁ : ℝ) := hQ1_ge_half
              _ ≤ (D : ℝ) := by exact_mod_cast hD_ge_Q1
          calc x / (D : ℝ) ≤ x / ((Real.log x) ^ (A' + 6) / 2) :=
                div_le_div_of_nonneg_left hx0.le (by positivity) hD_lo
            _ = 2 * x / (Real.log x) ^ (A' + 6) := by ring
        have ht4 : x / Real.sqrt (U : ℝ) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          have hU_lo : (Real.log x) ^ (A' + 6) / 2 ≤ Real.sqrt (U : ℝ) := by
            calc (Real.log x) ^ (A' + 6) / 2
                ≤ (Real.log x) ^ (K / 2) / 2 := div_le_div_of_nonneg_right
                  (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [K]; linarith)) (by norm_num)
              _ ≤ Real.sqrt (U : ℝ) := hsqrtU_ge
          calc x / Real.sqrt (U : ℝ) ≤ x / ((Real.log x) ^ (A' + 6) / 2) :=
                div_le_div_of_nonneg_left hx0.le (by positivity) hU_lo
            _ = 2 * x / (Real.log x) ^ (A' + 6) := by ring
        have ht5 : x / Real.sqrt (Δ * (U : ℝ)) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          rw [Real.sqrt_mul hΔ0.le, hsqrtΔ]
          have hden : (Real.log x) ^ (A' + 6) / 2 ≤ (Real.log x) ^ (-(E / 2)) * Real.sqrt (U : ℝ) := by
            calc (Real.log x) ^ (A' + 6) / 2
                ≤ (Real.log x) ^ (-(E / 2) + K / 2) / 2 := div_le_div_of_nonneg_right
                  (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [E, K]; linarith)) (by norm_num)
              _ = (Real.log x) ^ (-(E / 2)) * ((Real.log x) ^ (K / 2) / 2) := by
                  rw [Real.rpow_add hLx_pos]; ring
              _ ≤ (Real.log x) ^ (-(E / 2)) * Real.sqrt (U : ℝ) :=
                  mul_le_mul_of_nonneg_left hsqrtU_ge (by positivity)
          calc x / ((Real.log x) ^ (-(E / 2)) * Real.sqrt (U : ℝ))
              ≤ x / ((Real.log x) ^ (A' + 6) / 2) := div_le_div_of_nonneg_left hx0.le (by positivity) hden
            _ = 2 * x / (Real.log x) ^ (A' + 6) := by ring
        have ht6 : (D : ℝ) * Real.sqrt x / Real.sqrt Δ ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          rw [hsqrtΔ, Real.rpow_neg hLx_pos.le, div_inv_eq_mul]
          calc (D : ℝ) * Real.sqrt x * (Real.log x) ^ (E / 2)
              ≤ (Real.sqrt x / (Real.log x) ^ B) * Real.sqrt x * (Real.log x) ^ (E / 2) := by gcongr
            _ = (Real.sqrt x * Real.sqrt x) * ((Real.log x) ^ (E / 2) / (Real.log x) ^ B) := by ring
            _ = x / (Real.log x) ^ (B - E / 2) := by
                rw [Real.mul_self_sqrt hx0.le, ← Real.rpow_sub hLx_pos,
                  show E / 2 - B = -(B - E / 2) by ring, Real.rpow_neg hLx_pos.le, ← div_eq_mul_inv]
            _ ≤ x / (Real.log x) ^ (A' + 6) := div_le_div_of_nonneg_left hx0.le (by positivity)
                (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B, E]; linarith))
            _ ≤ 2 * x / (Real.log x) ^ (A' + 6) :=
                div_le_div_of_nonneg_right (by linarith) (by positivity)
        have ht7 : Real.sqrt Δ * x ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          rw [hsqrtΔ, Real.rpow_neg hLx_pos.le, inv_mul_eq_div]
          calc x / (Real.log x) ^ (E / 2)
              ≤ x / (Real.log x) ^ (A' + 6) := div_le_div_of_nonneg_left hx0.le (by positivity)
                (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [E]; linarith))
            _ ≤ 2 * x / (Real.log x) ^ (A' + 6) :=
                div_le_div_of_nonneg_right (by linarith) (by positivity)
        have ht8 : Real.sqrt x ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos _), Real.sqrt_eq_rpow]
          calc x ^ (1 / 2 : ℝ) * (Real.log x) ^ (A' + 6)
              ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 8 : ℝ) := mul_le_mul_of_nonneg_left
                (hL_le_x8 _ (by linarith) (by dsimp only [M_exp]; linarith)) (by positivity)
            _ = x ^ (5 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
            _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = x := Real.rpow_one x
            _ ≤ 2 * x := by linarith
        have ht9 : (D : ℝ) * Real.sqrt x ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
          calc (D : ℝ) * Real.sqrt x
              ≤ (Real.sqrt x / (Real.log x) ^ B) * Real.sqrt x := by gcongr
            _ = (Real.sqrt x * Real.sqrt x) / (Real.log x) ^ B := by ring
            _ = x / (Real.log x) ^ B := by rw [Real.mul_self_sqrt hx0.le]
            _ ≤ x / (Real.log x) ^ (A' + 6) := div_le_div_of_nonneg_left hx0.le (by positivity)
                (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B]; linarith))
            _ ≤ 2 * x / (Real.log x) ^ (A' + 6) :=
                div_le_div_of_nonneg_right (by linarith) (by positivity)
        have h9 :
            ((D : ℝ) * (U : ℝ) + (U : ℝ) * (U : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
              x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (U : ℝ)) +
              (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
              (D : ℝ) * Real.sqrt x) ≤ 18 * x / (Real.log x) ^ (A' + 6) := by
          have hEq : 18 * x / (Real.log x) ^ (A' + 6) = 9 * (2 * x / (Real.log x) ^ (A' + 6)) := by ring
          linarith
        have hlog4 : (1 + Real.log x) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
          have h1 : 1 + Real.log x ≤ 2 * Real.log x := by linarith
          calc (1 + Real.log x) ^ 4 ≤ (2 * Real.log x) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
            _ = 16 * (Real.log x) ^ 4 := by ring
        have hpow_cancel : (x / (Real.log x) ^ (A' + 6)) * (Real.log x) ^ 4 =
            x / (Real.log x) ^ (A' + 2) := by
          have hsplit : (Real.log x) ^ (A' + 6) = (Real.log x) ^ (A' + 2) * (Real.log x) ^ (4 : ℕ) := by
            rw [← Real.rpow_natCast (Real.log x) 4, ← Real.rpow_add hLx_pos]; congr 1; push_cast; ring
          rw [hsplit]
          have hne1 : (Real.log x) ^ (A' + 2) ≠ 0 := (Real.rpow_pos_of_pos hLx_pos _).ne'
          have hne2 : (Real.log x) ^ (4 : ℕ) ≠ 0 := pow_ne_zero 4 hLx_pos.ne'
          field_simp [hne1, hne2]
        calc _ ≤ 180 * (18 * x / (Real.log x) ^ (A' + 6)) * (16 * (Real.log x) ^ 4) := by
                refine hdy.trans (mul_le_mul (mul_le_mul_of_nonneg_left h9 (by norm_num)) hlog4
                  (by positivity) (by positivity))
          _ = 51840 * ((x / (Real.log x) ^ (A' + 6)) * (Real.log x) ^ 4) := by ring
          _ = 51840 * (x / (Real.log x) ^ (A' + 2)) := by rw [hpow_cancel]
          _ ≤ 60000 * x / (Real.log x) ^ (A' + 2) := by
                have : 0 ≤ x / (Real.log x) ^ (A' + 2) := by positivity
                have hEq : 60000 * x / (Real.log x) ^ (A' + 2) = 60000 * (x / (Real.log x) ^ (A' + 2)) := by ring
                linarith
      -- Sum over `j ∈ Finset.range J` using `J ≤ 4 * Real.log x`
      have hJ_le : (J : ℝ) ≤ 4 * Real.log x := by
        have hdiv_pos : 1 ≤ Q / Q₁ := Nat.div_pos hQQ1.le (by omega)
        have hpow : 2 ^ Nat.log 2 (Q / Q₁) ≤ Q / Q₁ := Nat.pow_log_le_self 2 (by omega)
        have hpowR : (2 : ℝ) ^ Nat.log 2 (Q / Q₁) ≤ x := by
          have h1 : 2 ^ Nat.log 2 (Q / Q₁) ≤ Q := hpow.trans (Nat.div_le_self Q Q₁)
          exact (by exact_mod_cast h1 : (2 : ℝ) ^ Nat.log 2 (Q / Q₁) ≤ (Q : ℝ)).trans hQ_le_x
        have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 (Q / Q₁)) hpowR
        rw [Real.log_pow] at hlog
        have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hnat : (Nat.log 2 (Q / Q₁) : ℝ) ≤ 2 * Real.log x := by nlinarith
        dsimp only [J]; push_cast; linarith
      have hlog_cancel : (Real.log x) ^ 2 * (x / (Real.log x) ^ (A' + 2)) = x / (Real.log x) ^ A' := by
        have hsplit : (Real.log x) ^ (A' + 2) = (Real.log x) ^ A' * (Real.log x) ^ (2 : ℕ) := by
          rw [← Real.rpow_natCast (Real.log x) 2, ← Real.rpow_add hLx_pos]; congr 1
        rw [hsplit]
        have hne1 : (Real.log x) ^ A' ≠ 0 := (Real.rpow_pos_of_pos hLx_pos _).ne'
        have hne2 : (Real.log x) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hLx_pos.ne'
        field_simp [hne1, hne2]
      calc 12 * Real.log x *
            ∑ k ∈ Finset.Ico Q₁ Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖psi ψ x‖
          ≤ 12 * Real.log x * ((J : ℝ) * (60000 * x / (Real.log x) ^ (A' + 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc _ ≤ ∑ _j ∈ Finset.range J, (60000 * x / (Real.log x) ^ (A' + 2)) :=
                    hbiUnion_le.trans (Finset.sum_le_sum hper_j)
              _ = (J : ℝ) * (60000 * x / (Real.log x) ^ (A' + 2)) := by
                    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ 12 * Real.log x * ((4 * Real.log x) * (60000 * x / (Real.log x) ^ (A' + 2))) := by
            gcongr
        _ = 2880000 * ((Real.log x) ^ 2 * (x / (Real.log x) ^ (A' + 2))) := by ring
        _ = 2880000 * (x / (Real.log x) ^ A') := by rw [hlog_cancel]
        _ ≤ 99999000 * x / (Real.log x) ^ A' := by
            have : 0 ≤ x / (Real.log x) ^ A' := by positivity
            have hEq : 99999000 * x / (Real.log x) ^ A' = 99999000 * (x / (Real.log x) ^ A') := by ring
            linarith
  have hprim_comb :
      12 * Real.log x *
        ∑ k ∈ Finset.Ico 2 Q,
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖psi ψ x‖ ≤
        (12 * C_sw + 99999000) * x / (Real.log x) ^ A' := by
    have hmul := mul_le_mul_of_nonneg_left hsplit_prim (show 0 ≤ 12 * Real.log x by positivity)
    rw [mul_add] at hmul
    have hEq : (12 * C_sw + 99999000) * x / (Real.log x) ^ A' =
        12 * C_sw * x / (Real.log x) ^ A' + 99999000 * x / (Real.log x) ^ A' := by ring
    linarith

  let T := ∑ k ∈ Ico 2 Q, (1/(Nat.totient (k+1):ℝ)) *
    ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (k+1) => χ.IsPrimitive), ‖psi χ x‖
  change 12 * Real.log x * T ≤ C * x / (Real.log x)^A' at hprim_comb
  change T ≤ C * x / (Real.log x)^A
  have hn : 0≤T := by dsimp [T]; positivity
  calc
    T ≤ 12*Real.log x*T := by nlinarith [mul_nonneg (show 0≤12*Real.log x-1 by linarith) hn]
    _ ≤ _ := hprim_comb
    _ ≤ _ := div_le_div_of_nonneg_left (by dsimp [C]; positivity) (Real.rpow_pos_of_pos hLx_pos A)
      (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hA_le_A')
end OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1
end
