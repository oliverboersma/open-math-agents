import OMAStatements.S_erdos_1112

/-!
# Disproof of `OMA.S_erdos_1112.main`

We refute the statement for `(d₁, d₂, k) = (1, 2, 3)`.

Given any threshold `r : ℤ`, pick an even multiplier `M ≥ max 4 (r.toNat + 1)` and define
`b 0 = 2`, `b (i + 1) = M * b i + (i % 2) + 1`. Then `b` is positive, strictly increasing,
lacunary with `r * b i ≤ b (i + 1)` for all `i`, and takes arbitrarily large even and odd values.

For any strictly increasing sequence `a` with gaps `a (i + 1) - a i ∈ {1, 2}`:
1. If every gap equals `2`, then `a i = a 0 + 2 * i`, so `sumset 3 a` contains every integer
   `≥ 3 * a 0` having the same parity as `3 * a 0`, hence meets `Set.range b`.
2. If some gap equals `1`, say `a (j + 1) = a j + 1`, then the pairwise sums
   `u m = a (m / 2) + a ((m + 1) / 2)` satisfy `u 0 = 2 * a 0` and `u (m + 1) - u m ∈ {1, 2}`,
   so adding `a j` or `a (j + 1) = a j + 1` covers every integer `≥ a j + 2 * a 0`,
   hence `sumset 3 a` again meets `Set.range b`.
-/

namespace OMA.P_erdos_1112

open OMA.S_erdos_1112

private lemma exists_u_close {u : ℕ → ℕ}
    (hstep : ∀ m, u m < u (m + 1) ∧ u (m + 1) ≤ u m + 2) :
    ∀ y : ℕ, u 0 ≤ y → ∃ m : ℕ, u m ≤ y ∧ y ≤ u m + 1 := by
  intro y hy
  induction y with
  | zero =>
    exact ⟨0, by omega, by omega⟩
  | succ y ih =>
    by_cases h0 : u 0 = y + 1
    · exact ⟨0, by omega, by omega⟩
    · obtain ⟨m, hm1, hm2⟩ := ih (by omega)
      by_cases heq : u m = y
      · exact ⟨m, by omega, by omega⟩
      · have hsm := hstep m
        exact ⟨m + 1, by omega, by omega⟩

private lemma mem_sumset_three (a : ℕ → ℕ) (p q s : ℕ) :
    a p + a q + a s ∈ sumset 3 a := by
  refine ⟨![p, q, s], ?_⟩
  simp [Fin.sum_univ_three, add_assoc]

theorem prove_disproof : ¬ (type_of% @OMA.S_erdos_1112.main) := by
  intro hmain
  obtain ⟨r, hr⟩ := hmain 1 2 3 le_rfl (by omega) le_rfl
  let M : ℕ := 2 * max 2 (r.toNat + 1)
  have hM_ge4 : 4 ≤ M := by dsimp [M]; omega
  have hM_even : M % 2 = 0 := by dsimp [M]; omega
  have hr_le_M : r ≤ (M : ℤ) := by dsimp [M]; omega
  let b : ℕ → ℕ := Nat.rec 2 (fun i prev => M * prev + (i % 2) + 1)
  have hb_zero : b 0 = 2 := rfl
  have hb_succ : ∀ i, b (i + 1) = M * b i + (i % 2) + 1 := fun _ => rfl
  have hb_pos : ∀ i, 0 < b i := by
    intro i
    induction i with
    | zero => rw [hb_zero]; omega
    | succ i _ => rw [hb_succ]; omega
  have hb_mono : StrictMono b := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    have hi := hb_pos i
    have hmul : 4 * b i ≤ M * b i := Nat.mul_le_mul_right (b i) hM_ge4
    rw [hb_succ]
    omega
  have hb_lac : Lacunary b := by
    refine ⟨2, by norm_num, fun i => ?_⟩
    have hmul : 4 * b i ≤ M * b i := Nat.mul_le_mul_right (b i) hM_ge4
    have hstep : 2 * b i ≤ b (i + 1) := by
      rw [hb_succ]
      omega
    exact_mod_cast hstep
  have hb_growth : ∀ i : ℕ, r * Int.ofNat (b i) ≤ Int.ofNat (b (i + 1)) := by
    intro i
    have h1 : Int.ofNat M * Int.ofNat (b i) ≤ Int.ofNat (b (i + 1)) := by
      have : M * b i ≤ b (i + 1) := by rw [hb_succ]; omega
      simp only [Int.ofNat_eq_natCast]
      rw [← Nat.cast_mul]
      exact Nat.cast_le.mpr this
    have h2 : r * Int.ofNat (b i) ≤ Int.ofNat M * Int.ofNat (b i) :=
      mul_le_mul_of_nonneg_right hr_le_M (Int.natCast_nonneg (b i))
    exact h2.trans h1
  have hb_even : ∀ m : ℕ, b (2 * m) % 2 = 0 := by
    intro m
    cases m with
    | zero => simp [hb_zero]
    | succ m =>
      have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [hidx, hb_succ (2 * m + 1)]
      have hmul : (M * b (2 * m + 1)) % 2 = 0 := by rw [Nat.mul_mod, hM_even]; simp
      omega
  have hb_odd : ∀ m : ℕ, b (2 * m + 1) % 2 = 1 := by
    intro m
    rw [hb_succ (2 * m)]
    have hmul : (M * b (2 * m)) % 2 = 0 := by rw [Nat.mul_mod, hM_even]; simp
    omega
  obtain ⟨a, _ha_pos, ha_mono, ha_gap, hdisj⟩ := hr b hb_pos hb_mono hb_lac hb_growth
  have ha_step : ∀ i, a (i + 1) = a i + 1 ∨ a (i + 1) = a i + 2 := by
    intro i
    have hlt : a i < a (i + 1) := ha_mono (Nat.lt_succ_self i)
    have ⟨hlo, hhi⟩ := ha_gap i
    omega
  by_cases hall2 : ∀ i, a (i + 1) = a i + 2
  · have ha_lin : ∀ i, a i = a 0 + 2 * i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [hall2 i, ih]; omega
    let N : ℕ := 3 * a 0
    let t : ℕ := if (3 * a 0) % 2 = 0 then 2 * N else 2 * N + 1
    have ht_ge : 3 * a 0 ≤ b t := by
      have hid : t ≤ b t := hb_mono.id_le t
      dsimp only [t, N] at hid ⊢
      split_ifs at hid ⊢ <;> omega
    have ht_par : b t % 2 = (3 * a 0) % 2 := by
      dsimp only [t]
      split_ifs with hpar
      · rw [hb_even N, hpar]
      · rw [hb_odd N]; omega
    let m : ℕ := (b t - 3 * a 0) / 2
    have hbt_eq : a 0 + a 0 + a m = b t := by
      rw [ha_lin m]
      omega
    have hmem : b t ∈ sumset 3 a := hbt_eq ▸ mem_sumset_three a 0 0 m
    exact Set.disjoint_left.mp hdisj hmem ⟨t, rfl⟩
  · push Not at hall2
    obtain ⟨j, hj_ne⟩ := hall2
    have hj : a (j + 1) = a j + 1 := by
      rcases ha_step j with h1 | h2
      · exact h1
      · exact absurd h2 hj_ne
    let u : ℕ → ℕ := fun m => a (m / 2) + a ((m + 1) / 2)
    have hu_step : ∀ m, u m < u (m + 1) ∧ u (m + 1) ≤ u m + 2 := by
      intro m
      dsimp only [u]
      rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
      · have h1 : m / 2 = q := by omega
        have h2 : (m + 1) / 2 = q := by omega
        have h3 : (m + 1 + 1) / 2 = q + 1 := by omega
        rw [h1, h2, h3]
        rcases ha_step q with hs | hs <;> omega
      · have h1 : m / 2 = q := by omega
        have h2 : (m + 1) / 2 = q + 1 := by omega
        have h3 : (m + 1 + 1) / 2 = q + 1 := by omega
        rw [h1, h2, h3]
        rcases ha_step q with hs | hs <;> omega
    let t : ℕ := a j + 2 * a 0
    have hbt_ge : a j + 2 * a 0 ≤ b t := hb_mono.id_le t
    have hy_ge : u 0 ≤ b t - a j := by
      have : u 0 = 2 * a 0 := by dsimp [u]; omega
      omega
    obtain ⟨m, hm1, hm2⟩ := exists_u_close hu_step (b t - a j) hy_ge
    have hmem : b t ∈ sumset 3 a := by
      by_cases heq : u m = b t - a j
      · have hbt : a j + a (m / 2) + a ((m + 1) / 2) = b t := by
          dsimp only [u] at heq; omega
        exact hbt ▸ mem_sumset_three a j (m / 2) ((m + 1) / 2)
      · have hbt : a (j + 1) + a (m / 2) + a ((m + 1) / 2) = b t := by
          dsimp only [u] at hm1 hm2 heq; omega
        exact hbt ▸ mem_sumset_three a (j + 1) (m / 2) ((m + 1) / 2)
    exact Set.disjoint_left.mp hdisj hmem ⟨t, rfl⟩

end OMA.P_erdos_1112

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_1112.main) :=
  OMA.P_erdos_1112.prove_disproof
