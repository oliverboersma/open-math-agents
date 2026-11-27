import OMAReductions.R_Erdos208_erdos_208_variants_log_bound_R1

-- Step Erdos208.erdos_208.variants.log_bound.R1.H1
-- Credit: @caa1982

open Finset

private lemma card_filter_dvd_Ioc_le (x m k : ℕ) (hk : 0 < k) :
    ((Finset.Ioc x (x + m)).filter (fun y => k ∣ y)).card ≤ m / k + 1 := by
  have hcard : ((Finset.Ioc x (x + m)).filter (fun y => k ∣ y)).card ≤
      (Finset.Ioc (x / k) ((x + m) / k)).card := by
    apply Finset.card_le_card_of_injOn (fun y => y / k)
    · intro y hy
      obtain ⟨hyI, hdvd⟩ := Finset.mem_filter.mp hy
      obtain ⟨hxy, hyxm⟩ := Finset.mem_Ioc.mp hyI
      have hy_eq : k * (y / k) = y := Nat.mul_div_cancel' hdvd
      refine Finset.mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hyxm⟩
      have h1 : k * (x / k) ≤ x := Nat.mul_div_le x k
      by_contra! hle
      have h2 : k * (y / k) ≤ k * (x / k) := Nat.mul_le_mul_left k hle
      omega
    · intro y₁ hy₁ y₂ hy₂ heq
      dsimp only at heq
      have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp hy₁).2
      have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp hy₂).2
      rw [← h1, ← h2, heq]
  rw [Nat.card_Ioc] at hcard
  have hdiv : (x + m) / k ≤ x / k + m / k + 1 := by
    have hx := Nat.div_add_mod x k
    have hm := Nat.div_add_mod m k
    have hxm := Nat.div_add_mod (x + m) k
    have hrx := Nat.mod_lt x hk
    have hrm := Nat.mod_lt m hk
    have hlt : x + m < k * (x / k + m / k + 2) := by nlinarith
    have hle : k * ((x + m) / k) ≤ x + m := Nat.mul_div_le (x + m) k
    have : (x + m) / k < x / k + m / k + 2 := by
      by_contra! hge
      have := Nat.mul_le_mul_left k hge
      omega
    omega
  exact le_trans hcard (Nat.sub_le_of_le_add (by linarith))

private lemma sum_telescope_Icc (L : ℕ) (hL : 2 ≤ L) :
    ∑ d ∈ Finset.Icc 3 L, (1 / ((d : ℚ) - 1) - 1 / (d : ℚ)) ≤ (1 / 2 : ℚ) := by
  induction L, hL using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hstep : ∑ d ∈ Finset.Icc 3 (k + 1), (1 / ((d : ℚ) - 1) - 1 / (d : ℚ)) =
        1 / 2 - 1 / ((k + 1 : ℕ) : ℚ) := by
      clear ih
      induction k, hk using Nat.le_induction with
      | base =>
        norm_num
      | succ m hm ihm =>
        have hmem : m + 2 ∉ Finset.Icc 3 (m + 1) := by simp
        have hIcc : Finset.Icc 3 (m + 2) = insert (m + 2) (Finset.Icc 3 (m + 1)) := by
          ext d
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hIcc, Finset.sum_insert hmem, ihm]
        push_cast
        ring
    rw [hstep]
    have hpos : (0 : ℚ) ≤ 1 / ((k + 1 : ℕ) : ℚ) := by positivity
    linarith

theorem OMA.solution : OMA.R_Erdos208_erdos_208_variants_log_bound_R1.H1 := by
  intro x L
  by_cases hL : L < 2
  · have hemp : Finset.Icc 2 L = ∅ := Finset.Icc_eq_empty (by omega)
    simp [hemp]
  push Not at hL
  have hsub : (Finset.Ioc x (x + 8 * L)).filter (fun y => ∃ d ∈ Finset.Icc 2 L, d * d ∣ y) ⊆
      (Finset.Icc 2 L).biUnion (fun d => (Finset.Ioc x (x + 8 * L)).filter (fun y => d * d ∣ y)) := by
    intro y hy
    obtain ⟨hyI, d, hd, hdvd⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hyI, hdvd⟩⟩
  have h1 : #{y ∈ Finset.Ioc x (x + 8 * L) | ∃ d ∈ Finset.Icc 2 L, d * d ∣ y} ≤
      ∑ d ∈ Finset.Icc 2 L, (8 * L / (d * d) + 1) := by
    calc #{y ∈ Finset.Ioc x (x + 8 * L) | ∃ d ∈ Finset.Icc 2 L, d * d ∣ y}
        ≤ ((Finset.Icc 2 L).biUnion
            (fun d => (Finset.Ioc x (x + 8 * L)).filter (fun y => d * d ∣ y))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ d ∈ Finset.Icc 2 L, ((Finset.Ioc x (x + 8 * L)).filter (fun y => d * d ∣ y)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ d ∈ Finset.Icc 2 L, (8 * L / (d * d) + 1) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
          exact card_filter_dvd_Ioc_le x (8 * L) (d * d) (by positivity)
  have hIcc : Finset.Icc 2 L = insert 2 (Finset.Icc 3 L) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1' : #{y ∈ Finset.Ioc x (x + 8 * L) | ∃ d ∈ Finset.Icc 2 L, d * d ∣ y} ≤
      (8 * L / (2 * 2) + 1) + ∑ d ∈ Finset.Icc 3 L, (8 * L / (d * d) + 1) := by
    refine le_trans h1 ?_
    rw [hIcc, Finset.sum_insert (by simp)]
  have hsum_q : ((∑ d ∈ Finset.Icc 3 L, (8 * L / (d * d) + 1) : ℕ) : ℚ) ≤
      (4 * L : ℚ) + ((L - 2 : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    have hterm : ∀ d ∈ Finset.Icc 3 L,
        ((8 * L / (d * d) + 1 : ℕ) : ℚ) ≤
          (8 * L : ℚ) * (1 / ((d : ℚ) - 1) - 1 / (d : ℚ)) + 1 := by
      intro d hd
      have hd3 : 3 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd_pos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
      have hd1_pos : (0 : ℚ) < (d : ℚ) - 1 := by
        have : (3 : ℚ) ≤ d := by exact_mod_cast hd3
        linarith
      have hdiv_le : ((8 * L / (d * d) : ℕ) : ℚ) ≤ (8 * L : ℚ) / ((d : ℚ) * (d : ℚ)) := by
        rw [le_div_iff₀ (mul_pos hd_pos hd_pos)]
        have : (8 * L / (d * d)) * (d * d) ≤ 8 * L := Nat.div_mul_le_self _ _
        exact_mod_cast this
      have hfrac : (1 : ℚ) / ((d : ℚ) * (d : ℚ)) ≤ 1 / ((d : ℚ) - 1) - 1 / (d : ℚ) := by
        have heq : 1 / ((d : ℚ) - 1) - 1 / (d : ℚ) = 1 / (((d : ℚ) - 1) * (d : ℚ)) := by
          field_simp [hd1_pos.ne', hd_pos.ne']
          ring
        rw [heq, div_le_div_iff₀ (mul_pos hd_pos hd_pos) (mul_pos hd1_pos hd_pos)]
        nlinarith
      push_cast
      have hmul : (8 * (L : ℚ)) / ((d : ℚ) * (d : ℚ)) ≤
          (8 * (L : ℚ)) * (1 / ((d : ℚ) - 1) - 1 / (d : ℚ)) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hfrac (by positivity)
      linarith
    calc ∑ d ∈ Finset.Icc 3 L, ((8 * L / (d * d) + 1 : ℕ) : ℚ)
        ≤ ∑ d ∈ Finset.Icc 3 L, ((8 * L : ℚ) * (1 / ((d : ℚ) - 1) - 1 / (d : ℚ)) + 1) :=
          Finset.sum_le_sum hterm
      _ = (8 * L : ℚ) * (∑ d ∈ Finset.Icc 3 L, (1 / ((d : ℚ) - 1) - 1 / (d : ℚ))) +
            ((Finset.Icc 3 L).card : ℚ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (8 * L : ℚ) * (1 / 2) + ((L - 2 : ℕ) : ℚ) := by
          have hcard : (Finset.Icc 3 L).card = L - 2 := by simp
          rw [hcard]
          linarith [mul_le_mul_of_nonneg_left (sum_telescope_Icc L hL) (show (0 : ℚ) ≤ 8 * L by positivity)]
      _ = (4 * L : ℚ) + ((L - 2 : ℕ) : ℚ) := by ring
  have hsum_nat : ∑ d ∈ Finset.Icc 3 L, (8 * L / (d * d) + 1) ≤ 4 * L + (L - 2) := by
    exact_mod_cast hsum_q
  have h2 : 8 * L / (2 * 2) = 2 * L := by omega
  omega
