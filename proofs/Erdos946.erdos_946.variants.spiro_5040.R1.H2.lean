import OMAReductions.R_Erdos946_erdos_946_variants_spiro_5040_R1

-- Step Erdos946.erdos_946.variants.spiro_5040.R1.H2: hypothesis H2 of reduction Erdos946.erdos_946.variants.spiro_5040.R1

/-!
Every `v ∈ S` is a multiple of `d ^ 2` for some `B < d ≤ X`, and `[1, X]` has `⌊X / d²⌋` such
multiples, so `|S| ≤ ∑_{B < d ≤ X} X / d²`. Since `1 / d² ≤ 1 / (d - 1) - 1 / d`, the sum
telescopes to at most `X (1 / B - 1 / X) ≤ X / B`.
-/

namespace OMA

theorem tele (B : ℕ) (hB : 0 < B) : ∀ N : ℕ, B ≤ N →
    ∑ d ∈ Finset.Ioc B N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / (B : ℝ) - 1 / (N : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN]
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := by omega
      exact_mod_cast this
    have hstep : (1 : ℝ) / (((N + 1 : ℕ)) : ℝ) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hN0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

end OMA

theorem OMA.solution : OMA.R_Erdos946_erdos_946_variants_spiro_5040_R1.H2 := by
  unfold OMA.R_Erdos946_erdos_946_variants_spiro_5040_R1.H2
  intro B X hB S hS
  have hsub : S ⊆ (Finset.Ioc B X).biUnion
      (fun d => (Finset.Ioc 0 X).filter (fun v => d ^ 2 ∣ v)) := by
    intro v hv
    obtain ⟨hv0, hvX, d, hd, hdv⟩ := hS v hv
    have h1 : d ^ 2 ≤ v := Nat.le_of_dvd hv0 hdv
    have h2 : d ≤ d ^ 2 := Nat.le_self_pow (by norm_num) d
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_Ioc.mpr ⟨hd, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hv0, hvX⟩, hdv⟩⟩
  have hcard : S.card ≤ ∑ d ∈ Finset.Ioc B X, X / d ^ 2 := by
    calc S.card ≤ ((Finset.Ioc B X).biUnion
          (fun d => (Finset.Ioc 0 X).filter (fun v => d ^ 2 ∣ v))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ d ∈ Finset.Ioc B X, ((Finset.Ioc 0 X).filter (fun v => d ^ 2 ∣ v)).card :=
          Finset.card_biUnion_le
      _ = ∑ d ∈ Finset.Ioc B X, X / d ^ 2 :=
          Finset.sum_congr rfl (fun d _ => Nat.Ioc_filter_dvd_card_eq_div X (d ^ 2))
  rcases Nat.lt_or_ge X B with hXB | hXB
  · have he : Finset.Ioc B X = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [he, Finset.sum_empty] at hcard
    have : S.card = 0 := by omega
    rw [this]
    omega
  · have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    have hXr : (0 : ℝ) < (X : ℝ) := by
      have : 0 < X := by omega
      exact_mod_cast this
    have h1 : (S.card : ℝ) ≤ ∑ d ∈ Finset.Ioc B X, (X : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) := by
      have hc : (S.card : ℝ) ≤ ((∑ d ∈ Finset.Ioc B X, X / d ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcard
      refine le_trans hc ?_
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro d _
      have h := Nat.cast_div_le (α := ℝ) (m := X) (n := d ^ 2)
      push_cast at h
      rw [mul_one_div]
      exact h
    rw [← Finset.mul_sum] at h1
    have h2 := OMA.tele B hB X hXB
    have h3 : (X : ℝ) * ∑ d ∈ Finset.Ioc B X, (1 : ℝ) / (d : ℝ) ^ 2 ≤
        (X : ℝ) * (1 / (B : ℝ) - 1 / (X : ℝ)) := mul_le_mul_of_nonneg_left h2 hXr.le
    have h4 : (X : ℝ) * (1 / (B : ℝ) - 1 / (X : ℝ)) = (X : ℝ) / (B : ℝ) - 1 := by
      field_simp
    have h5 : (S.card : ℝ) ≤ (X : ℝ) / (B : ℝ) := by linarith
    have h6 : (B : ℝ) * (S.card : ℝ) ≤ (X : ℝ) := by
      rw [le_div_iff₀ hBr] at h5
      linarith
    exact_mod_cast h6
