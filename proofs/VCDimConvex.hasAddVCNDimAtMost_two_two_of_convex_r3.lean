import FormalConjectures.Other.VCDimConvex

/-!
# Proof that every convex set in R^3 has VC_2 dimension at most 2

We prove `VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3`: no convex subset `C` of
`EuclideanSpace ℝ (Fin 3)` can 2-shatter a 3 x 3 sumset grid `a i + b j`.

The proof proceeds by:
1. Showing that shattering forbids any opposite-sign convex dependency between `a` and `b`
   (including degenerate single-side affine dependencies), hence the direction planes `H_A` and `H_B`
   are distinct 2-dimensional subspaces of `ℝ^3`.
2. Intersecting `H_A` and `H_B` along a 1-dimensional line, normalizing the intersection vector in
   each triangle, and constructing a spanning triple `(e₁, e₂, e₃)` with positive parameters
   `c, ρ, σ > 0` putting all nine grid points into canonical form.
3. Selecting two 7-point subsets `S_a, S_b` whose translation difference `w = t_b - t_a ≠ 0` lies in
   at least one of four facial cones (F1, F2, B1, B2) covering `ℝ^3 \ {0}`, yielding a two-translate
   convex-combination contradiction.
-/

namespace VCDimConvexProof

section Grid

variable {E : Type*} [AddCommGroup E]

private def ShattersGrid (C : Set E) (a b : Fin 3 → E) : Prop :=
  ∀ S : Set (Fin 3 × Fin 3), ∃ t : E, ∀ i j : Fin 3, t + (a i + b j) ∈ C ↔ (i, j) ∈ S

private lemma ShattersGrid.swap {C : Set E} {a b : Fin 3 → E}
    (h : ShattersGrid C a b) : ShattersGrid C b a := by
  intro S
  obtain ⟨t, ht⟩ := h {p | (p.2, p.1) ∈ S}
  refine ⟨t, fun i j => ?_⟩
  simpa [add_comm] using ht j i

private lemma ShattersGrid.perm {C : Set E} {a b : Fin 3 → E}
    (h : ShattersGrid C a b) (πA πB : Equiv.Perm (Fin 3)) :
    ShattersGrid C (a ∘ πA) (b ∘ πB) := by
  intro S
  obtain ⟨t, ht⟩ := h {p | (πA.symm p.1, πB.symm p.2) ∈ S}
  refine ⟨t, fun i j => ?_⟩
  simpa using ht (πA i) (πB j)

end Grid

section Abstract

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private lemma no_opposite_sign_le_one {C : Set E} {a b : Fin 3 → E}
    (hC : Convex ℝ C) (hS : ShattersGrid C a b)
    {i₀ i₁ i₂ j₀ j₁ j₂ : Fin 3} (hi₁ : i₁ ≠ i₀) (hi₂ : i₂ ≠ i₀)
    {c l₁ l₂ μ₁ μ₂ : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hl : l₁ + l₂ = 1)
    (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂) (hμ : μ₁ + μ₂ = 1)
    (heq : a i₀ - (l₁ • a i₁ + l₂ • a i₂) = c • ((μ₁ • b j₁ + μ₂ • b j₂) - b j₀)) :
    False := by
  obtain ⟨t, ht⟩ := hS {p | p ≠ (i₀, j₀)}
  set abar : E := l₁ • a i₁ + l₂ • a i₂
  set bbar : E := μ₁ • b j₁ + μ₂ • b j₂
  have hrow : ∀ j : Fin 3, t + abar + b j ∈ C := by
    intro j
    have h1 : t + (a i₁ + b j) ∈ C := (ht i₁ j).mpr (by simp [hi₁])
    have h2 : t + (a i₂ + b j) ∈ C := (ht i₂ j).mpr (by simp [hi₂])
    have hmem := hC h1 h2 hl₁ hl₂ hl
    have hcomb : l₁ • (t + (a i₁ + b j)) + l₂ • (t + (a i₂ + b j)) = t + abar + b j := by
      calc l₁ • (t + (a i₁ + b j)) + l₂ • (t + (a i₂ + b j))
          = (l₁ + l₂) • t + abar + (l₁ + l₂) • b j := by
            simp only [abar]; module
        _ = t + abar + b j := by rw [hl, one_smul, one_smul]
    rwa [hcomb] at hmem
  have hbbar_mem : t + abar + bbar ∈ C := by
    have hmem := hC (hrow j₁) (hrow j₂) hμ₁ hμ₂ hμ
    have hcomb : μ₁ • (t + abar + b j₁) + μ₂ • (t + abar + b j₂) = t + abar + bbar := by
      calc μ₁ • (t + abar + b j₁) + μ₂ • (t + abar + b j₂)
          = (μ₁ + μ₂) • (t + abar) + bbar := by
            simp only [bbar]; module
        _ = t + abar + bbar := by rw [hμ, one_smul]
    rwa [hcomb] at hmem
  have hfinal := hC (hrow j₀) hbbar_mem (sub_nonneg.mpr hc1) hc0 (sub_add_cancel 1 c)
  have hcomb : (1 - c) • (t + abar + b j₀) + c • (t + abar + bbar) = t + (a i₀ + b j₀) := by
    have ha0 : a i₀ = abar + c • (bbar - b j₀) := eq_add_of_sub_eq' heq
    rw [ha0]
    module
  rw [hcomb] at hfinal
  exact ((ht i₀ j₀).mp hfinal) rfl

private lemma no_opposite_sign {C : Set E} {a b : Fin 3 → E}
    (hC : Convex ℝ C) (hS : ShattersGrid C a b)
    {i₀ i₁ i₂ j₀ j₁ j₂ : Fin 3}
    (hi₁ : i₁ ≠ i₀) (hi₂ : i₂ ≠ i₀) (hj₁ : j₁ ≠ j₀) (hj₂ : j₂ ≠ j₀)
    {c l₁ l₂ μ₁ μ₂ : ℝ} (hc : 0 < c)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hl : l₁ + l₂ = 1)
    (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂) (hμ : μ₁ + μ₂ = 1)
    (heq : a i₀ - (l₁ • a i₁ + l₂ • a i₂) = c • ((μ₁ • b j₁ + μ₂ • b j₂) - b j₀)) :
    False := by
  by_cases hc1 : c ≤ 1
  · exact no_opposite_sign_le_one hC hS hi₁ hi₂ hc.le hc1 hl₁ hl₂ hl hμ₁ hμ₂ hμ heq
  · push Not at hc1
    have hci0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    have hci1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1.le
    have heq' : b j₀ - (μ₁ • b j₁ + μ₂ • b j₂) = c⁻¹ • ((l₁ • a i₁ + l₂ • a i₂) - a i₀) := by
      have h1 : c⁻¹ • (a i₀ - (l₁ • a i₁ + l₂ • a i₂)) = (μ₁ • b j₁ + μ₂ • b j₂) - b j₀ := by
        rw [heq, inv_smul_smul₀ hc.ne']
      calc b j₀ - (μ₁ • b j₁ + μ₂ • b j₂)
          = -((μ₁ • b j₁ + μ₂ • b j₂) - b j₀) := by module
        _ = -(c⁻¹ • (a i₀ - (l₁ • a i₁ + l₂ • a i₂))) := by rw [h1]
        _ = c⁻¹ • ((l₁ • a i₁ + l₂ • a i₂) - a i₀) := by module
    exact no_opposite_sign_le_one hC hS.swap hj₁ hj₂ hci0 hci1 hμ₁ hμ₂ hμ hl₁ hl₂ hl heq'

private lemma forbidden_cone_a {C : Set E} {a b : Fin 3 → E}
    (hC : Convex ℝ C)
    {Sa Sb : Set (Fin 3 × Fin 3)} {ta tb : E}
    (hta : ∀ i j, ta + (a i + b j) ∈ C ↔ (i, j) ∈ Sa)
    (htb : ∀ i j, tb + (a i + b j) ∈ C ↔ (i, j) ∈ Sb)
    {p0 p1 p2 p3 : Fin 3 × Fin 3}
    (hp0b : p0 ∈ Sb) (hp0a : p0 ∉ Sa)
    (hp1 : p1 ∈ Sa) (hp2 : p2 ∈ Sa) (hp3 : p3 ∈ Sa)
    {α₁ α₂ α₃ : ℝ} (h1 : 0 ≤ α₁) (h2 : 0 ≤ α₂) (h3 : 0 ≤ α₃)
    (hsum : 0 < α₁ + α₂ + α₃)
    (hw : tb - ta = α₁ • ((a p0.1 + b p0.2) - (a p1.1 + b p1.2))
                  + α₂ • ((a p0.1 + b p0.2) - (a p2.1 + b p2.2))
                  + α₃ • ((a p0.1 + b p0.2) - (a p3.1 + b p3.2))) :
    False := by
  set S : ℝ := α₁ + α₂ + α₃
  set P0 : E := a p0.1 + b p0.2
  set P1 : E := a p1.1 + b p1.2
  set P2 : E := a p2.1 + b p2.2
  set P3 : E := a p3.1 + b p3.2
  have hSpos : 0 < S := hsum
  have hS1pos : 0 < S + 1 := by linarith
  let w : Fin 3 → ℝ := ![α₁ / S, α₂ / S, α₃ / S]
  let z : Fin 3 → E := ![ta + P1, ta + P2, ta + P3]
  have hqstar_mem : (∑ k : Fin 3, w k • z k) ∈ C := by
    refine hC.sum_mem (fun k _ => ?_) ?_ (fun k _ => ?_)
    · fin_cases k <;> dsimp [w] <;> positivity
    · have hsum_w : ∑ k : Fin 3, w k = α₁ / S + α₂ / S + α₃ / S := by
        simp [Fin.sum_univ_three, w]
      rw [hsum_w]
      have hSne : S ≠ 0 := hSpos.ne'
      field_simp
      simp only [S]
    · fin_cases k
      · exact (hta p1.1 p1.2).mpr hp1
      · exact (hta p2.1 p2.2).mpr hp2
      · exact (hta p3.1 p3.2).mpr hp3
  set qstar : E := (α₁ / S) • (ta + P1) + (α₂ / S) • (ta + P2) + (α₃ / S) • (ta + P3)
  have hqstar_eq : (∑ k : Fin 3, w k • z k) = qstar := by
    simp [Fin.sum_univ_three, w, z, qstar]
  rw [hqstar_eq] at hqstar_mem
  have htb_mem : tb + P0 ∈ C := (htb p0.1 p0.2).mpr hp0b
  have hcomb_mem : (S / (S + 1)) • qstar + (1 / (S + 1)) • (tb + P0) ∈ C := by
    refine hC hqstar_mem htb_mem (by positivity) (by positivity) ?_
    have hS1ne : S + 1 ≠ 0 := hS1pos.ne'
    field_simp
  have hcomb_eq : (S / (S + 1)) • qstar + (1 / (S + 1)) • (tb + P0) = ta + P0 := by
    apply smul_right_injective E hS1pos.ne'
    dsimp only
    have hq : S • qstar = α₁ • (ta + P1) + α₂ • (ta + P2) + α₃ • (ta + P3) := by
      simp only [qstar, smul_add, smul_smul, mul_div_cancel₀ _ hSpos.ne']
    have hstep : (S + 1) • ((S / (S + 1)) • qstar + (1 / (S + 1)) • (tb + P0))
        = S • qstar + (tb + P0) := by
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ hS1pos.ne', one_smul]
    have htb_eq : tb = ta + α₁ • (P0 - P1) + α₂ • (P0 - P2) + α₃ • (P0 - P3) := by
      have := eq_add_of_sub_eq' hw
      rw [this]
      module
    rw [hstep, hq, htb_eq]
    simp only [S]
    module
  rw [hcomb_eq] at hcomb_mem
  exact hp0a ((hta p0.1 p0.2).mp hcomb_mem)

private lemma forbidden_cone_b {C : Set E} {a b : Fin 3 → E}
    (hC : Convex ℝ C)
    {Sa Sb : Set (Fin 3 × Fin 3)} {ta tb : E}
    (hta : ∀ i j, ta + (a i + b j) ∈ C ↔ (i, j) ∈ Sa)
    (htb : ∀ i j, tb + (a i + b j) ∈ C ↔ (i, j) ∈ Sb)
    {p0 p1 p2 p3 : Fin 3 × Fin 3}
    (hp0a : p0 ∈ Sa) (hp0b : p0 ∉ Sb)
    (hp1 : p1 ∈ Sb) (hp2 : p2 ∈ Sb) (hp3 : p3 ∈ Sb)
    {α₁ α₂ α₃ : ℝ} (h1 : 0 ≤ α₁) (h2 : 0 ≤ α₂) (h3 : 0 ≤ α₃)
    (hsum : 0 < α₁ + α₂ + α₃)
    (hw : tb - ta = α₁ • ((a p1.1 + b p1.2) - (a p0.1 + b p0.2))
                  + α₂ • ((a p2.1 + b p2.2) - (a p0.1 + b p0.2))
                  + α₃ • ((a p3.1 + b p3.2) - (a p0.1 + b p0.2))) :
    False := by
  refine forbidden_cone_a hC htb hta hp0a hp0b hp1 hp2 hp3 h1 h2 h3 hsum ?_
  calc ta - tb = -(tb - ta) := by module
    _ = -(α₁ • ((a p1.1 + b p1.2) - (a p0.1 + b p0.2))
        + α₂ • ((a p2.1 + b p2.2) - (a p0.1 + b p0.2))
        + α₃ • ((a p3.1 + b p3.2) - (a p0.1 + b p0.2))) := by rw [hw]
    _ = α₁ • ((a p0.1 + b p0.2) - (a p1.1 + b p1.2))
      + α₂ • ((a p0.1 + b p0.2) - (a p2.1 + b p2.2))
      + α₃ • ((a p0.1 + b p0.2) - (a p3.1 + b p3.2)) := by module

private lemma three_reals_pos_case (γ : Fin 3 → ℝ) (π : Equiv.Perm (Fin 3))
    (hsum : γ (π 0) + γ (π 1) + γ (π 2) = 0)
    (h0 : 0 < γ (π 0)) (h1 : γ (π 1) ≤ 0) (h2 : γ (π 2) ≤ 0) :
    ∃ (ε s θ₁ θ₂ : ℝ),
      (ε = 1 ∨ ε = -1) ∧ 0 < s ∧ 0 ≤ θ₁ ∧ 0 ≤ θ₂ ∧ θ₁ + θ₂ = 1 ∧
      γ (π 0) = ε * s ∧ γ (π 1) = -(ε * s * θ₁) ∧ γ (π 2) = -(ε * s * θ₂) := by
  have h0ne : γ (π 0) ≠ 0 := h0.ne'
  refine ⟨1, γ (π 0), -γ (π 1) / γ (π 0), -γ (π 2) / γ (π 0), Or.inl rfl, h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (neg_nonneg.mpr h1) h0.le
  · exact div_nonneg (neg_nonneg.mpr h2) h0.le
  · field_simp
    linarith
  · ring
  · field_simp
  · field_simp

private lemma three_reals_neg_case (γ : Fin 3 → ℝ) (π : Equiv.Perm (Fin 3))
    (hsum : γ (π 0) + γ (π 1) + γ (π 2) = 0)
    (h0 : γ (π 0) < 0) (h1 : 0 ≤ γ (π 1)) (h2 : 0 ≤ γ (π 2)) :
    ∃ (ε s θ₁ θ₂ : ℝ),
      (ε = 1 ∨ ε = -1) ∧ 0 < s ∧ 0 ≤ θ₁ ∧ 0 ≤ θ₂ ∧ θ₁ + θ₂ = 1 ∧
      γ (π 0) = ε * s ∧ γ (π 1) = -(ε * s * θ₁) ∧ γ (π 2) = -(ε * s * θ₂) := by
  have hs : 0 < -γ (π 0) := neg_pos.mpr h0
  have h0ne : γ (π 0) ≠ 0 := h0.ne
  refine ⟨-1, -γ (π 0), γ (π 1) / (-γ (π 0)), γ (π 2) / (-γ (π 0)), Or.inr rfl, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg h1 hs.le
  · exact div_nonneg h2 hs.le
  · field_simp
    linarith
  · ring
  · field_simp
  · field_simp

private lemma three_reals_sign_normal (γ : Fin 3 → ℝ)
    (hsum : γ 0 + γ 1 + γ 2 = 0)
    (hne : γ 0 ≠ 0 ∨ γ 1 ≠ 0 ∨ γ 2 ≠ 0) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε s θ₁ θ₂ : ℝ),
      (ε = 1 ∨ ε = -1) ∧ 0 < s ∧ 0 ≤ θ₁ ∧ 0 ≤ θ₂ ∧ θ₁ + θ₂ = 1 ∧
      γ (π 0) = ε * s ∧ γ (π 1) = -(ε * s * θ₁) ∧ γ (π 2) = -(ε * s * θ₂) := by
  have h01_2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have h02_1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  by_cases h0 : 0 < γ 0 <;> by_cases h1 : 0 < γ 1 <;> by_cases h2 : 0 < γ 2
  · linarith
  · push Not at h2
    have h2' : γ 2 < 0 := by linarith
    obtain ⟨ε, s, θ₁, θ₂, h⟩ := three_reals_neg_case γ (Equiv.swap 0 2)
      (by simp [h02_1]; linarith) (by simpa using h2') (by simpa [h02_1] using h1.le) (by simpa using h0.le)
    exact ⟨Equiv.swap 0 2, ε, s, θ₁, θ₂, h⟩
  · push Not at h1
    have h1' : γ 1 < 0 := by linarith
    obtain ⟨ε, s, θ₁, θ₂, h⟩ := three_reals_neg_case γ (Equiv.swap 0 1)
      (by simp [h01_2]; linarith) (by simpa using h1') (by simpa using h0.le) (by simpa [h01_2] using h2.le)
    exact ⟨Equiv.swap 0 1, ε, s, θ₁, θ₂, h⟩
  · push Not at h1 h2
    obtain ⟨ε, s, θ₁, θ₂, h⟩ := three_reals_pos_case γ (Equiv.refl _) (by simpa using hsum) h0 h1 h2
    exact ⟨Equiv.refl _, ε, s, θ₁, θ₂, h⟩
  · push Not at h0
    have h0' : γ 0 < 0 := by linarith
    obtain ⟨ε, s, θ₁, θ₂, h⟩ := three_reals_neg_case γ (Equiv.refl _) (by simpa using hsum) h0' h1.le h2.le
    exact ⟨Equiv.refl _, ε, s, θ₁, θ₂, h⟩
  · push Not at h0 h2
    obtain ⟨ε, s, θ₁, θ₂, h⟩ := three_reals_pos_case γ (Equiv.swap 0 1)
      (by simp [h01_2]; linarith) (by simpa using h1) (by simpa using h0) (by simpa [h01_2] using h2)
    exact ⟨Equiv.swap 0 1, ε, s, θ₁, θ₂, h⟩
  · push Not at h0 h1
    obtain ⟨ε, s, θ₁, θ₂, h⟩ := three_reals_pos_case γ (Equiv.swap 0 2)
      (by simp [h02_1]; linarith) (by simpa using h2) (by simpa [h02_1] using h1) (by simpa using h0)
    exact ⟨Equiv.swap 0 2, ε, s, θ₁, θ₂, h⟩
  · push Not at h0 h1 h2
    rcases hne with hne | hne | hne
    · exact False.elim (hne (by linarith))
    · exact False.elim (hne (by linarith))
    · exact False.elim (hne (by linarith))

private lemma sign_normal_form (z : Fin 3 → E) {r₁ r₂ : ℝ}
    (hne : r₁ • (z 1 - z 0) + r₂ • (z 2 - z 0) ≠ 0) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε s θ₁ θ₂ : ℝ),
      (ε = 1 ∨ ε = -1) ∧ 0 < s ∧ 0 ≤ θ₁ ∧ 0 ≤ θ₂ ∧ θ₁ + θ₂ = 1 ∧
      r₁ • (z 1 - z 0) + r₂ • (z 2 - z 0) =
        (ε * s) • (z (π 0) - (θ₁ • z (π 1) + θ₂ • z (π 2))) := by
  let γ : Fin 3 → ℝ := ![-(r₁ + r₂), r₁, r₂]
  have hγ0_val : γ 0 = -(r₁ + r₂) := rfl
  have hγ1_val : γ 1 = r₁ := rfl
  have hγ2_val : γ 2 = r₂ := rfl
  have hsum : γ 0 + γ 1 + γ 2 = 0 := by
    rw [hγ0_val, hγ1_val, hγ2_val]
    ring
  have hγne : γ 0 ≠ 0 ∨ γ 1 ≠ 0 ∨ γ 2 ≠ 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨_, h1, h2⟩
    rw [hγ1_val] at h1
    rw [hγ2_val] at h2
    exact hne (by rw [h1, h2]; simp)
  obtain ⟨π, ε, s, θ₁, θ₂, hε, hs, hθ₁, hθ₂, hθ, hγ0, hγ1, hγ2⟩ :=
    three_reals_sign_normal γ hsum hγne
  refine ⟨π, ε, s, θ₁, θ₂, hε, hs, hθ₁, hθ₂, hθ, ?_⟩
  have hcomp : ∑ k : Fin 3, γ k • z k = ∑ k : Fin 3, γ (π k) • z (π k) :=
    (Equiv.sum_comp π (fun k => γ k • z k)).symm
  simp only [Fin.sum_univ_three] at hcomp
  calc r₁ • (z 1 - z 0) + r₂ • (z 2 - z 0)
      = γ 0 • z 0 + γ 1 • z 1 + γ 2 • z 2 := by
        rw [hγ0_val, hγ1_val, hγ2_val]
        module
    _ = γ (π 0) • z (π 0) + γ (π 1) • z (π 1) + γ (π 2) • z (π 2) := hcomp
    _ = (ε * s) • z (π 0) + (-(ε * s * θ₁)) • z (π 1) + (-(ε * s * θ₂)) • z (π 2) := by
        rw [hγ0, hγ1, hγ2]
    _ = (ε * s) • (z (π 0) - (θ₁ • z (π 1) + θ₂ • z (π 2))) := by module

private lemma linIndep_diffs {C : Set E} {a b : Fin 3 → E}
    (hC : Convex ℝ C) (hS : ShattersGrid C a b) :
    LinearIndependent ℝ ![a 1 - a 0, a 2 - a 0] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • (a 1 - a 0) + g 1 • (a 2 - a 0) = 0 := by
    simpa [Fin.sum_univ_two] using hg
  by_contra hne
  push Not at hne
  obtain ⟨k, hk⟩ := hne
  let γ : Fin 3 → ℝ := ![-(g 0 + g 1), g 0, g 1]
  have hγ0_val : γ 0 = -(g 0 + g 1) := rfl
  have hγ1_val : γ 1 = g 0 := rfl
  have hγ2_val : γ 2 = g 1 := rfl
  have hsum : γ 0 + γ 1 + γ 2 = 0 := by
    rw [hγ0_val, hγ1_val, hγ2_val]
    ring
  have hγne : γ 0 ≠ 0 ∨ γ 1 ≠ 0 ∨ γ 2 ≠ 0 := by
    fin_cases k
    · exact Or.inr (Or.inl (by simpa [hγ1_val] using hk))
    · exact Or.inr (Or.inr (by simpa [hγ2_val] using hk))
  obtain ⟨π, ε, s, θ₁, θ₂, hε, hs, hθ₁, hθ₂, hθ, hγ0, hγ1, hγ2⟩ :=
    three_reals_sign_normal γ hsum hγne
  have hcomp : ∑ j : Fin 3, γ j • a j = ∑ j : Fin 3, γ (π j) • a (π j) :=
    (Equiv.sum_comp π (fun j => γ j • a j)).symm
  simp only [Fin.sum_univ_three] at hcomp
  have hzero : (ε * s) • (a (π 0) - (θ₁ • a (π 1) + θ₂ • a (π 2))) = 0 := by
    calc (ε * s) • (a (π 0) - (θ₁ • a (π 1) + θ₂ • a (π 2)))
        = (ε * s) • a (π 0) + (-(ε * s * θ₁)) • a (π 1) + (-(ε * s * θ₂)) • a (π 2) := by
          module
      _ = γ (π 0) • a (π 0) + γ (π 1) • a (π 1) + γ (π 2) • a (π 2) := by
          rw [hγ0, hγ1, hγ2]
      _ = γ 0 • a 0 + γ 1 • a 1 + γ 2 • a 2 := hcomp.symm
      _ = g 0 • (a 1 - a 0) + g 1 • (a 2 - a 0) := by
          rw [hγ0_val, hγ1_val, hγ2_val]
          module
      _ = 0 := hg'
  have hεs : ε * s ≠ 0 := by
    rcases hε with rfl | rfl <;> positivity
  have hdiff : a (π 0) - (θ₁ • a (π 1) + θ₂ • a (π 2)) = 0 :=
    (smul_eq_zero.mp hzero).resolve_left hεs
  have hi₁ : π 1 ≠ π 0 := fun h => absurd (π.injective h) (by decide)
  have hi₂ : π 2 ≠ π 0 := fun h => absurd (π.injective h) (by decide)
  exact no_opposite_sign_le_one hC hS hi₁ hi₂ (le_refl 0) (by norm_num)
    hθ₁ hθ₂ hθ (μ₁ := 1) (μ₂ := 0) (by norm_num) (le_refl 0) (by norm_num)
    (j₀ := 0) (j₁ := 1) (j₂ := 2) (by simp [hdiff])

private lemma mem_span_range_pair {u v x : E} :
    x ∈ Submodule.span ℝ (Set.range ![u, v]) ↔ ∃ r₁ r₂ : ℝ, r₁ • u + r₂ • v = x := by
  have hrange : Set.range ![u, v] = {u, v} := by
    ext y
    simp
    tauto
  rw [hrange, Submodule.mem_span_pair]

private lemma span_ne_span {C : Set E} {a b : Fin 3 → E}
    (hC : Convex ℝ C) (hS : ShattersGrid C a b) :
    Submodule.span ℝ (Set.range ![a 1 - a 0, a 2 - a 0]) ≠
      Submodule.span ℝ (Set.range ![b 1 - b 0, b 2 - b 0]) := by
  intro hEq
  have hliA := linIndep_diffs hC hS
  have hne : a 1 - a 0 ≠ 0 := by
    have := hliA.ne_zero (0 : Fin 2)
    simpa using this
  have hmemA : a 1 - a 0 ∈ Submodule.span ℝ (Set.range ![a 1 - a 0, a 2 - a 0]) :=
    Submodule.subset_span ⟨0, rfl⟩
  rw [hEq, mem_span_range_pair] at hmemA
  obtain ⟨r₁, r₂, hr⟩ := hmemA
  obtain ⟨πB, ε, s, μ₁, μ₂, hε, hs, hμ₁, hμ₂, hμ, hform⟩ :=
    sign_normal_form b (by rwa [hr])
  rw [hr] at hform
  have hj₁ : πB 1 ≠ πB 0 := fun h => absurd (πB.injective h) (by decide)
  have hj₂ : πB 2 ≠ πB 0 := fun h => absurd (πB.injective h) (by decide)
  rcases hε with rfl | rfl
  · refine no_opposite_sign hC hS (i₀ := 0) (i₁ := 1) (i₂ := 2)
      (by decide) (by decide) hj₁ hj₂ hs
      (l₁ := 1) (l₂ := 0) (by norm_num) (le_refl 0) (by norm_num) hμ₁ hμ₂ hμ ?_
    have hform' : a 1 - a 0 = s • (b (πB 0) - (μ₁ • b (πB 1) + μ₂ • b (πB 2))) := by
      simpa using hform
    calc a 0 - ((1 : ℝ) • a 1 + (0 : ℝ) • a 2)
        = -(a 1 - a 0) := by module
      _ = -(s • (b (πB 0) - (μ₁ • b (πB 1) + μ₂ • b (πB 2)))) := by rw [hform']
      _ = s • ((μ₁ • b (πB 1) + μ₂ • b (πB 2)) - b (πB 0)) := by module
  · refine no_opposite_sign hC hS (i₀ := 1) (i₁ := 0) (i₂ := 2)
      (by decide) (by decide) hj₁ hj₂ hs
      (l₁ := 1) (l₂ := 0) (by norm_num) (le_refl 0) (by norm_num) hμ₁ hμ₂ hμ ?_
    calc a 1 - ((1 : ℝ) • a 0 + (0 : ℝ) • a 2)
        = a 1 - a 0 := by module
      _ = (-1 * s) • (b (πB 0) - (μ₁ • b (πB 1) + μ₂ • b (πB 2))) := hform
      _ = s • ((μ₁ • b (πB 1) + μ₂ • b (πB 2)) - b (πB 0)) := by module

end Abstract

private lemma canonical_basis {C : Set (EuclideanSpace ℝ (Fin 3))}
    {a b : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hC : Convex ℝ C) (hS : ShattersGrid C a b) :
    ∃ (πA πB : Equiv.Perm (Fin 3)) (c ρ σ : ℝ)
      (abar bbar e₁ e₂ e₃ : EuclideanSpace ℝ (Fin 3)),
      0 < c ∧ 0 < ρ ∧ 0 < σ ∧
      Submodule.span ℝ ({e₁, e₂, e₃} : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ ∧
      a (πA 0) = abar + c • e₁ ∧ a (πA 1) = abar + e₂ ∧ a (πA 2) = abar - ρ • e₂ ∧
      b (πB 0) = bbar + e₁ ∧ b (πB 1) = bbar + e₃ ∧ b (πB 2) = bbar - σ • e₃ := by
  let HA : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.span ℝ (Set.range ![a 1 - a 0, a 2 - a 0])
  let HB : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.span ℝ (Set.range ![b 1 - b 0, b 2 - b 0])
  have hliA := linIndep_diffs hC hS
  have hliB := linIndep_diffs hC hS.swap
  have hdimA : Module.finrank ℝ HA = 2 := by
    simpa [HA] using finrank_span_eq_card hliA
  have hdimB : Module.finrank ℝ HB = 2 := by
    simpa [HB] using finrank_span_eq_card hliB
  have hdimE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    simp
  have hAB : HA ≠ HB := span_ne_span hC hS
  have hlt : HA < HA ⊔ HB := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    have hBA : HB ≤ HA := le_sup_right.trans hEq.symm.le
    exact hAB (Submodule.eq_of_le_of_finrank_eq hBA (by omega)).symm
  have hsup_dim : Module.finrank ℝ ↥(HA ⊔ HB) = 3 := by
    have h1 : 2 < Module.finrank ℝ ↥(HA ⊔ HB) := by
      rw [← hdimA]
      exact Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : Module.finrank ℝ ↥(HA ⊔ HB) ≤ 3 :=
      (Submodule.finrank_le (HA ⊔ HB)).trans hdimE.le
    omega
  have hsup_top : HA ⊔ HB = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hsup_dim, hdimE])
  have hinf_dim : Module.finrank ℝ ↥(HA ⊓ HB) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq HA HB
    omega
  have hinf_ne : (HA ⊓ HB) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hinf_dim
    simp at hinf_dim
  obtain ⟨e, he_mem, he_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf_ne
  obtain ⟨heA, heB⟩ := Submodule.mem_inf.mp he_mem
  obtain ⟨r₁, r₂, hr⟩ := mem_span_range_pair.mp heA
  obtain ⟨q₁, q₂, hq⟩ := mem_span_range_pair.mp heB
  obtain ⟨πA, εA, sA, l₁, l₂, hεA, hsA, hl₁, hl₂, hl, hformA⟩ :=
    sign_normal_form a (by rwa [hr])
  obtain ⟨πB, εB, sB, μ₁, μ₂, hεB, hsB, hμ₁, hμ₂, hμ, hformB⟩ :=
    sign_normal_form b (by rwa [hq])
  rw [hr] at hformA
  rw [hq] at hformB
  set a' : Fin 3 → EuclideanSpace ℝ (Fin 3) := a ∘ πA
  set b' : Fin 3 → EuclideanSpace ℝ (Fin 3) := b ∘ πB
  have hS' : ShattersGrid C a' b' := hS.perm πA πB
  have hAB_eq : (εA * sA) • (a' 0 - (l₁ • a' 1 + l₂ • a' 2)) =
      (εB * sB) • (b' 0 - (μ₁ • b' 1 + μ₂ • b' 2)) := by
    simpa [a', b'] using hformA.symm.trans hformB
  have hε_eq : εA = εB := by
    by_contra hneε
    have hcpos : 0 < sB / sA := div_pos hsB hsA
    have hεAne : εA * sA ≠ 0 := by rcases hεA with rfl | rfl <;> positivity
    have hrel : a' 0 - (l₁ • a' 1 + l₂ • a' 2) =
        (sB / sA) • ((μ₁ • b' 1 + μ₂ • b' 2) - b' 0) := by
      have h1 := congr_arg ((εA * sA)⁻¹ • ·) hAB_eq
      simp only [inv_smul_smul₀ hεAne, smul_smul] at h1
      have hcoeff : (εA * sA)⁻¹ * (εB * sB) = -(sB / sA) := by
        have hεA0 : εA ≠ 0 := by rcases hεA with rfl | rfl <;> norm_num
        have hsA0 : sA ≠ 0 := hsA.ne'
        have hεB_eq : εB = -εA := by
          rcases hεA with rfl | rfl <;> rcases hεB with rfl | rfl
          · exact absurd rfl hneε
          · norm_num
          · norm_num
          · exact absurd rfl hneε
        rw [hεB_eq]
        field_simp
      rw [hcoeff] at h1
      rw [h1]
      module
    exact no_opposite_sign hC hS' (by decide) (by decide) (by decide) (by decide)
      hcpos hl₁ hl₂ hl hμ₁ hμ₂ hμ hrel
  set c : ℝ := sB / sA
  have hcpos : 0 < c := div_pos hsB hsA
  have hrel : a' 0 - (l₁ • a' 1 + l₂ • a' 2) = c • (b' 0 - (μ₁ • b' 1 + μ₂ • b' 2)) := by
    have hεAne : εA * sA ≠ 0 := by rcases hεA with rfl | rfl <;> positivity
    have h1 := congr_arg ((εA * sA)⁻¹ • ·) hAB_eq
    simp only [inv_smul_smul₀ hεAne, smul_smul] at h1
    have hcoeff : (εA * sA)⁻¹ * (εB * sB) = c := by
      rw [← hε_eq]
      have hεA0 : εA ≠ 0 := by rcases hεA with rfl | rfl <;> norm_num
      have hsA0 : sA ≠ 0 := hsA.ne'
      simp only [c]
      field_simp
    rwa [hcoeff] at h1
  have hl₂pos : 0 < l₂ := by
    refine lt_of_le_of_ne hl₂ ?_
    intro h0
    have hl₁1 : l₁ = 1 := by linarith
    refine no_opposite_sign hC hS' (i₀ := 1) (i₁ := 0) (i₂ := 2) (j₀ := 0) (j₁ := 1) (j₂ := 2)
      (by decide) (by decide) (by decide) (by decide)
      hcpos (l₁ := 1) (l₂ := 0) (by norm_num) (le_refl 0) (by norm_num) hμ₁ hμ₂ hμ ?_
    have hrel' : a' 0 - a' 1 = c • (b' 0 - (μ₁ • b' 1 + μ₂ • b' 2)) := by
      simpa [← h0, hl₁1] using hrel
    calc a' 1 - ((1 : ℝ) • a' 0 + (0 : ℝ) • a' 2)
        = -(a' 0 - a' 1) := by module
      _ = -(c • (b' 0 - (μ₁ • b' 1 + μ₂ • b' 2))) := by rw [hrel']
      _ = c • ((μ₁ • b' 1 + μ₂ • b' 2) - b' 0) := by module
  have hl₁pos : 0 < l₁ := by
    refine lt_of_le_of_ne hl₁ ?_
    intro h0
    have hl₂1 : l₂ = 1 := by linarith
    refine no_opposite_sign hC hS' (i₀ := 2) (i₁ := 0) (i₂ := 1) (j₀ := 0) (j₁ := 1) (j₂ := 2)
      (by decide) (by decide) (by decide) (by decide)
      hcpos (l₁ := 1) (l₂ := 0) (by norm_num) (le_refl 0) (by norm_num) hμ₁ hμ₂ hμ ?_
    have hrel' : a' 0 - a' 2 = c • (b' 0 - (μ₁ • b' 1 + μ₂ • b' 2)) := by
      simpa [← h0, hl₂1] using hrel
    calc a' 2 - ((1 : ℝ) • a' 0 + (0 : ℝ) • a' 1)
        = -(a' 0 - a' 2) := by module
      _ = -(c • (b' 0 - (μ₁ • b' 1 + μ₂ • b' 2))) := by rw [hrel']
      _ = c • ((μ₁ • b' 1 + μ₂ • b' 2) - b' 0) := by module
  have hμ₂pos : 0 < μ₂ := by
    refine lt_of_le_of_ne hμ₂ ?_
    intro h0
    have hμ₁1 : μ₁ = 1 := by linarith
    refine no_opposite_sign hC hS'.swap (i₀ := 1) (i₁ := 0) (i₂ := 2) (j₀ := 0) (j₁ := 1) (j₂ := 2)
      (by decide) (by decide) (by decide) (by decide)
      (inv_pos.mpr hcpos) (l₁ := 1) (l₂ := 0) (by norm_num) (le_refl 0) (by norm_num) hl₁ hl₂ hl ?_
    have hrel' : a' 0 - (l₁ • a' 1 + l₂ • a' 2) = c • (b' 0 - b' 1) := by
      simpa [← h0, hμ₁1] using hrel
    have h1 := congr_arg (c⁻¹ • ·) hrel'
    simp only [inv_smul_smul₀ hcpos.ne'] at h1
    calc b' 1 - ((1 : ℝ) • b' 0 + (0 : ℝ) • b' 2)
        = -(b' 0 - b' 1) := by module
      _ = -(c⁻¹ • (a' 0 - (l₁ • a' 1 + l₂ • a' 2))) := by rw [h1]
      _ = c⁻¹ • ((l₁ • a' 1 + l₂ • a' 2) - a' 0) := by module
  have hμ₁pos : 0 < μ₁ := by
    refine lt_of_le_of_ne hμ₁ ?_
    intro h0
    have hμ₂1 : μ₂ = 1 := by linarith
    refine no_opposite_sign hC hS'.swap (i₀ := 2) (i₁ := 0) (i₂ := 1) (j₀ := 0) (j₁ := 1) (j₂ := 2)
      (by decide) (by decide) (by decide) (by decide)
      (inv_pos.mpr hcpos) (l₁ := 1) (l₂ := 0) (by norm_num) (le_refl 0) (by norm_num) hl₁ hl₂ hl ?_
    have hrel' : a' 0 - (l₁ • a' 1 + l₂ • a' 2) = c • (b' 0 - b' 2) := by
      simpa [← h0, hμ₂1] using hrel
    have h1 := congr_arg (c⁻¹ • ·) hrel'
    simp only [inv_smul_smul₀ hcpos.ne'] at h1
    calc b' 2 - ((1 : ℝ) • b' 0 + (0 : ℝ) • b' 1)
        = -(b' 0 - b' 2) := by module
      _ = -(c⁻¹ • (a' 0 - (l₁ • a' 1 + l₂ • a' 2))) := by rw [h1]
      _ = c⁻¹ • ((l₁ • a' 1 + l₂ • a' 2) - a' 0) := by module
  set abar := l₁ • a' 1 + l₂ • a' 2
  set bbar := μ₁ • b' 1 + μ₂ • b' 2
  set ρ := l₁ / l₂
  set σ := μ₁ / μ₂
  set e₁ := b' 0 - bbar
  set e₂ := a' 1 - abar
  set e₃ := b' 1 - bbar
  have hρpos : 0 < ρ := div_pos hl₁pos hl₂pos
  have hσpos : 0 < σ := div_pos hμ₁pos hμ₂pos
  have ha0 : a' 0 = abar + c • e₁ := eq_add_of_sub_eq' hrel
  have ha1 : a' 1 = abar + e₂ := by simp only [e₂]; module
  have ha2 : a' 2 = abar - ρ • e₂ := by
    apply smul_right_injective (EuclideanSpace ℝ (Fin 3)) hl₂pos.ne'
    dsimp only
    have hmul : l₂ * ρ = l₁ := mul_div_cancel₀ _ hl₂pos.ne'
    calc l₂ • a' 2
        = (l₁ + l₂) • abar - l₁ • a' 1 := by
          rw [hl, one_smul]
          simp only [abar]
          module
      _ = l₂ • abar - (l₂ * ρ) • (a' 1 - abar) := by
          rw [hmul]
          module
      _ = l₂ • (abar - ρ • e₂) := by
          simp only [e₂, smul_sub, smul_smul]
  have hb0 : b' 0 = bbar + e₁ := by simp only [e₁]; module
  have hb1 : b' 1 = bbar + e₃ := by simp only [e₃]; module
  have hb2 : b' 2 = bbar - σ • e₃ := by
    apply smul_right_injective (EuclideanSpace ℝ (Fin 3)) hμ₂pos.ne'
    dsimp only
    have hmul : μ₂ * σ = μ₁ := mul_div_cancel₀ _ hμ₂pos.ne'
    calc μ₂ • b' 2
        = (μ₁ + μ₂) • bbar - μ₁ • b' 1 := by
          rw [hμ, one_smul]
          simp only [bbar]
          module
      _ = μ₂ • bbar - (μ₂ * σ) • (b' 1 - bbar) := by
          rw [hmul]
          module
      _ = μ₂ • (bbar - σ • e₃) := by
          simp only [e₃, smul_sub, smul_smul]
  have hspan : Submodule.span ℝ ({e₁, e₂, e₃} : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    set W := Submodule.span ℝ ({e₁, e₂, e₃} : Set (EuclideanSpace ℝ (Fin 3)))
    have he₁W : e₁ ∈ W := Submodule.subset_span (by simp)
    have he₂W : e₂ ∈ W := Submodule.subset_span (by simp)
    have he₃W : e₃ ∈ W := Submodule.subset_span (by simp)
    have haW : ∀ k : Fin 3, a' k - abar ∈ W := by
      intro k
      match k with
      | 0 =>
        rw [ha0, add_sub_cancel_left]
        exact W.smul_mem c he₁W
      | 1 =>
        rw [ha1, add_sub_cancel_left]
        exact he₂W
      | 2 =>
        rw [ha2]
        have : abar - ρ • e₂ - abar = (-ρ) • e₂ := by module
        rw [this]
        exact W.smul_mem (-ρ) he₂W
    have hbW : ∀ k : Fin 3, b' k - bbar ∈ W := by
      intro k
      match k with
      | 0 =>
        rw [hb0, add_sub_cancel_left]
        exact he₁W
      | 1 =>
        rw [hb1, add_sub_cancel_left]
        exact he₃W
      | 2 =>
        rw [hb2]
        have : bbar - σ • e₃ - bbar = (-σ) • e₃ := by module
        rw [this]
        exact W.smul_mem (-σ) he₃W
    have hHAW : HA ≤ W := by
      rw [Submodule.span_le]
      rintro x ⟨k, rfl⟩
      have hdiff : ∀ i : Fin 3, a i - a 0 ∈ W := by
        intro i
        have h1 : a i - a 0 = (a' (πA.symm i) - abar) - (a' (πA.symm 0) - abar) := by
          simp only [a', Function.comp_apply, Equiv.apply_symm_apply]
          module
        rw [h1]
        exact W.sub_mem (haW _) (haW _)
      fin_cases k
      · simpa using hdiff 1
      · simpa using hdiff 2
    have hHBW : HB ≤ W := by
      rw [Submodule.span_le]
      rintro x ⟨k, rfl⟩
      have hdiff : ∀ j : Fin 3, b j - b 0 ∈ W := by
        intro j
        have h1 : b j - b 0 = (b' (πB.symm j) - bbar) - (b' (πB.symm 0) - bbar) := by
          simp only [b', Function.comp_apply, Equiv.apply_symm_apply]
          module
        rw [h1]
        exact W.sub_mem (hbW _) (hbW _)
      fin_cases k
      · simpa using hdiff 1
      · simpa using hdiff 2
    exact top_unique (hsup_top.symm.le.trans (sup_le hHAW hHBW))
  exact ⟨πA, πB, c, ρ, σ, abar, bbar, e₁, e₂, e₃, hcpos, hρpos, hσpos, hspan,
    ha0, ha1, ha2, hb0, hb1, hb2⟩

private lemma no_shatters_grid_r3 {C : Set (EuclideanSpace ℝ (Fin 3))}
    {a b : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hC : Convex ℝ C) (hS : ShattersGrid C a b) : False := by
  obtain ⟨πA, πB, c, ρ, σ, abar, bbar, e₁, e₂, e₃, hc, hρ, hσ, hspan,
    ha0, ha1, ha2, hb0, hb1, hb2⟩ := canonical_basis hC hS
  set a' : Fin 3 → EuclideanSpace ℝ (Fin 3) := a ∘ πA
  set b' : Fin 3 → EuclideanSpace ℝ (Fin 3) := b ∘ πB
  have hS' : ShattersGrid C a' b' := hS.perm πA πB
  set Sa : Set (Fin 3 × Fin 3) := {p | p ≠ (1, 0) ∧ p ≠ (2, 0)}
  set Sb : Set (Fin 3 × Fin 3) := {p | p ≠ (0, 1) ∧ p ≠ (0, 2)}
  obtain ⟨ta, hta⟩ := hS' Sa
  obtain ⟨tb, htb⟩ := hS' Sb
  set w : EuclideanSpace ℝ (Fin 3) := tb - ta
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hteq : tb = ta := sub_eq_zero.mp hw0
    have hin : ta + (a' 0 + b' 1) ∈ C := (hta 0 1).mpr (by simp [Sa])
    rw [← hteq] at hin
    have hmem := (htb 0 1).mp hin
    simp [Sb] at hmem
  have hw_mem : w ∈ Submodule.span ℝ ({e₁, e₂, e₃} : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [hspan]
    trivial
  rw [Submodule.mem_span_insert] at hw_mem
  obtain ⟨wx, v, hv, hw_eq⟩ := hw_mem
  rw [Submodule.mem_span_pair] at hv
  obtain ⟨wy, wz, hv_eq⟩ := hv
  have hw_vec : w = wx • e₁ + wy • e₂ + wz • e₃ := by
    rw [hw_eq, ← hv_eq]
    module
  have hF1 : ∀ {α₁ α₂ α₃ : ℝ}, 0 ≤ α₁ → 0 ≤ α₂ → 0 ≤ α₃ →
      α₁ + α₂ - c * α₃ = wx → α₃ = wy → -α₁ + σ * α₂ = wz → False := by
    intro α₁ α₂ α₃ h1 h2 h3 hcx hcy hcz
    have hsum : 0 < α₁ + α₂ + α₃ := by
      by_contra hle
      push Not at hle
      have hα1 : α₁ = 0 := by linarith
      have hα2 : α₂ = 0 := by linarith
      have hα3 : α₃ = 0 := by linarith
      have hwx : wx = 0 := by rw [← hcx, hα1, hα2, hα3]; ring
      have hwy : wy = 0 := by rw [← hcy, hα3]
      have hwz : wz = 0 := by rw [← hcz, hα1, hα2]; ring
      exact hw_ne (by rw [hw_vec, hwx, hwy, hwz]; simp)
    refine forbidden_cone_a hC hta htb (p0 := (1, 0)) (p1 := (1, 1)) (p2 := (1, 2)) (p3 := (0, 0))
      (by simp [Sb]) (by simp [Sa]) (by simp [Sa]) (by simp [Sa]) (by simp [Sa])
      h1 h2 h3 hsum ?_
    change w = _
    rw [hw_vec, ← hcx, ← hcy, ← hcz]
    simp only [a', b', Function.comp_apply, ha0, ha1, hb0, hb1, hb2]
    module
  have hF2 : ∀ {α₁ α₂ α₃ : ℝ}, 0 ≤ α₁ → 0 ≤ α₂ → 0 ≤ α₃ →
      α₁ + α₂ - c * α₃ = wx → -ρ * α₃ = wy → -α₁ + σ * α₂ = wz → False := by
    intro α₁ α₂ α₃ h1 h2 h3 hcx hcy hcz
    have hsum : 0 < α₁ + α₂ + α₃ := by
      by_contra hle
      push Not at hle
      have hα1 : α₁ = 0 := by linarith
      have hα2 : α₂ = 0 := by linarith
      have hα3 : α₃ = 0 := by linarith
      have hwx : wx = 0 := by rw [← hcx, hα1, hα2, hα3]; ring
      have hwy : wy = 0 := by rw [← hcy, hα3]; ring
      have hwz : wz = 0 := by rw [← hcz, hα1, hα2]; ring
      exact hw_ne (by rw [hw_vec, hwx, hwy, hwz]; simp)
    refine forbidden_cone_a hC hta htb (p0 := (2, 0)) (p1 := (2, 1)) (p2 := (2, 2)) (p3 := (0, 0))
      (by simp [Sb]) (by simp [Sa]) (by simp [Sa]) (by simp [Sa]) (by simp [Sa])
      h1 h2 h3 hsum ?_
    change w = _
    rw [hw_vec, ← hcx, ← hcy, ← hcz]
    simp only [a', b', Function.comp_apply, ha0, ha2, hb0, hb1, hb2]
    module
  have hB1 : ∀ {α₁ α₂ α₃ : ℝ}, 0 ≤ α₁ → 0 ≤ α₂ → 0 ≤ α₃ →
      -c * (α₁ + α₂) + α₃ = wx → α₁ - ρ * α₂ = wy → -α₃ = wz → False := by
    intro α₁ α₂ α₃ h1 h2 h3 hcx hcy hcz
    have hsum : 0 < α₁ + α₂ + α₃ := by
      by_contra hle
      push Not at hle
      have hα1 : α₁ = 0 := by linarith
      have hα2 : α₂ = 0 := by linarith
      have hα3 : α₃ = 0 := by linarith
      have hwx : wx = 0 := by rw [← hcx, hα1, hα2, hα3]; ring
      have hwy : wy = 0 := by rw [← hcy, hα1, hα2]; ring
      have hwz : wz = 0 := by rw [← hcz, hα3]; ring
      exact hw_ne (by rw [hw_vec, hwx, hwy, hwz]; simp)
    refine forbidden_cone_b hC hta htb (p0 := (0, 1)) (p1 := (1, 1)) (p2 := (2, 1)) (p3 := (0, 0))
      (by simp [Sa]) (by simp [Sb]) (by simp [Sb]) (by simp [Sb]) (by simp [Sb])
      h1 h2 h3 hsum ?_
    change w = _
    rw [hw_vec, ← hcx, ← hcy, ← hcz]
    simp only [a', b', Function.comp_apply, ha0, ha1, ha2, hb0, hb1]
    module
  have hB2 : ∀ {α₁ α₂ α₃ : ℝ}, 0 ≤ α₁ → 0 ≤ α₂ → 0 ≤ α₃ →
      -c * (α₁ + α₂) + α₃ = wx → α₁ - ρ * α₂ = wy → σ * α₃ = wz → False := by
    intro α₁ α₂ α₃ h1 h2 h3 hcx hcy hcz
    have hsum : 0 < α₁ + α₂ + α₃ := by
      by_contra hle
      push Not at hle
      have hα1 : α₁ = 0 := by linarith
      have hα2 : α₂ = 0 := by linarith
      have hα3 : α₃ = 0 := by linarith
      have hwx : wx = 0 := by rw [← hcx, hα1, hα2, hα3]; ring
      have hwy : wy = 0 := by rw [← hcy, hα1, hα2]; ring
      have hwz : wz = 0 := by rw [← hcz, hα3]; ring
      exact hw_ne (by rw [hw_vec, hwx, hwy, hwz]; simp)
    refine forbidden_cone_b hC hta htb (p0 := (0, 2)) (p1 := (1, 2)) (p2 := (2, 2)) (p3 := (0, 0))
      (by simp [Sa]) (by simp [Sb]) (by simp [Sb]) (by simp [Sb]) (by simp [Sb])
      h1 h2 h3 hsum ?_
    change w = _
    rw [hw_vec, ← hcx, ← hcy, ← hcz]
    simp only [a', b', Function.comp_apply, ha0, ha1, ha2, hb0, hb2]
    module
  have hF1_of : 0 ≤ wy → 0 ≤ σ * (wx + c * wy) - wz → 0 ≤ wx + c * wy + wz → False := by
    intro hwy h1 h2
    refine hF1 (α₁ := (σ * (wx + c * wy) - wz) / (1 + σ))
      (α₂ := (wx + c * wy + wz) / (1 + σ)) (α₃ := wy)
      (div_nonneg h1 (by positivity)) (div_nonneg h2 (by positivity)) hwy ?_ rfl ?_
    · have : 1 + σ ≠ 0 := by positivity
      field_simp; ring
    · have : 1 + σ ≠ 0 := by positivity
      field_simp; ring
  have hF2_of : wy ≤ 0 → 0 ≤ σ * (ρ * wx - c * wy) - ρ * wz →
      0 ≤ ρ * wx - c * wy + ρ * wz → False := by
    intro hwy h1 h2
    refine hF2 (α₁ := (σ * (ρ * wx - c * wy) - ρ * wz) / (ρ * (1 + σ)))
      (α₂ := (ρ * wx - c * wy + ρ * wz) / (ρ * (1 + σ))) (α₃ := -wy / ρ)
      (div_nonneg h1 (by positivity)) (div_nonneg h2 (by positivity))
      (div_nonneg (by linarith) hρ.le) ?_ ?_ ?_
    · have hρ0 : ρ ≠ 0 := hρ.ne'
      have hσ1 : 1 + σ ≠ 0 := by positivity
      field_simp; ring
    · have hρ0 : ρ ≠ 0 := hρ.ne'
      field_simp
    · have hρ0 : ρ ≠ 0 := hρ.ne'
      have hσ1 : 1 + σ ≠ 0 := by positivity
      field_simp; ring
  have hB1_of : wz ≤ 0 → 0 ≤ ρ * (-wx - wz) + c * wy → 0 ≤ -wx - wz - c * wy → False := by
    intro hwz h1 h2
    refine hB1 (α₁ := (ρ * (-wx - wz) + c * wy) / (c * (1 + ρ)))
      (α₂ := (-wx - wz - c * wy) / (c * (1 + ρ))) (α₃ := -wz)
      (div_nonneg h1 (by positivity)) (div_nonneg h2 (by positivity)) (by linarith) ?_ ?_ (by ring)
    · have hc0 : c ≠ 0 := hc.ne'
      have hρ1 : 1 + ρ ≠ 0 := by positivity
      field_simp; ring
    · have hc0 : c ≠ 0 := hc.ne'
      have hρ1 : 1 + ρ ≠ 0 := by positivity
      field_simp; ring
  have hB2_of : 0 ≤ wz → 0 ≤ ρ * (wz - σ * wx) + c * σ * wy →
      0 ≤ wz - σ * wx - c * σ * wy → False := by
    intro hwz h1 h2
    refine hB2 (α₁ := (ρ * (wz - σ * wx) + c * σ * wy) / (c * σ * (1 + ρ)))
      (α₂ := (wz - σ * wx - c * σ * wy) / (c * σ * (1 + ρ))) (α₃ := wz / σ)
      (div_nonneg h1 (by positivity)) (div_nonneg h2 (by positivity))
      (div_nonneg hwz hσ.le) ?_ ?_ ?_
    · have hc0 : c ≠ 0 := hc.ne'
      have hσ0 : σ ≠ 0 := hσ.ne'
      have hρ1 : 1 + ρ ≠ 0 := by positivity
      field_simp; ring
    · have hc0 : c ≠ 0 := hc.ne'
      have hσ0 : σ ≠ 0 := hσ.ne'
      have hρ1 : 1 + ρ ≠ 0 := by positivity
      field_simp; ring
    · have hσ0 : σ ≠ 0 := hσ.ne'
      field_simp
  rcases le_total 0 wy with hwy | hwy <;> rcases le_total 0 wz with hwz | hwz
  · rcases le_or_gt 0 (σ * (wx + c * wy) - wz) with h | h
    · refine hF1_of hwy h ?_
      have hσw : 0 ≤ σ * (wx + c * wy) := by linarith
      have hw : 0 ≤ wx + c * wy := nonneg_of_mul_nonneg_right hσw hσ
      linarith
    · refine hB2_of hwz ?_ (by linarith)
      have hcσy : 0 ≤ c * σ * wy := mul_nonneg (mul_nonneg hc.le hσ.le) hwy
      have hpos : 0 ≤ wz - σ * wx := by linarith
      have hρpos : 0 ≤ ρ * (wz - σ * wx) := mul_nonneg hρ.le hpos
      linarith
  · rcases le_or_gt 0 (wx + c * wy + wz) with h | h
    · refine hF1_of hwy ?_ h
      have hpos : 0 ≤ wx + c * wy := by linarith
      have hσpos : 0 ≤ σ * (wx + c * wy) := mul_nonneg hσ.le hpos
      linarith
    · refine hB1_of hwz ?_ (by linarith)
      have hcy : 0 ≤ c * wy := mul_nonneg hc.le hwy
      have hpos : 0 ≤ -wx - wz := by linarith
      have hρpos : 0 ≤ ρ * (-wx - wz) := mul_nonneg hρ.le hpos
      linarith
  · rcases le_or_gt 0 (σ * (ρ * wx - c * wy) - ρ * wz) with h | h
    · refine hF2_of hwy h ?_
      have hρz : 0 ≤ ρ * wz := mul_nonneg hρ.le hwz
      have hσw : 0 ≤ σ * (ρ * wx - c * wy) := by linarith
      have hw : 0 ≤ ρ * wx - c * wy := nonneg_of_mul_nonneg_right hσw hσ
      linarith
    · refine hB2_of hwz (by linarith) ?_
      have hneg : c * σ * (1 + ρ) * wy ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hwy
      have hprod : 0 ≤ ρ * (wz - σ * wx - c * σ * wy) := by linarith
      exact nonneg_of_mul_nonneg_right hprod hρ
  · rcases le_or_gt 0 (ρ * wx - c * wy + ρ * wz) with h | h
    · refine hF2_of hwy ?_ h
      have hρz : ρ * wz ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le hwz
      have hw : 0 ≤ ρ * wx - c * wy := by linarith
      have hσw : 0 ≤ σ * (ρ * wx - c * wy) := mul_nonneg hσ.le hw
      linarith
    · refine hB1_of hwz (by linarith) ?_
      have hneg : c * (1 + ρ) * wy ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hwy
      have hprod : 0 ≤ ρ * (-wx - wz - c * wy) := by linarith
      exact nonneg_of_mul_nonneg_right hprod hρ

end VCDimConvexProof

theorem OMA.solution : type_of% @VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3 := by
  intro C hC x y hxy
  refine VCDimConvexProof.no_shatters_grid_r3 hC (a := x 0) (b := x 1) ?_
  intro S
  refine ⟨y {f : Fin 2 → Fin 3 | (f 0, f 1) ∈ S}, fun i j => ?_⟩
  have h := hxy ![i, j] {f : Fin 2 → Fin 3 | (f 0, f 1) ∈ S}
  simpa [Fin.sum_univ_two] using h
