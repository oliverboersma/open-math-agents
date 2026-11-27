import FormalConjectures.ErdosProblems.«673»

/-!
Proof of Erdos673.erdos_673.variants.tao: Tao's inequality
`((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card`
for any `0 < n`, `1 < m`, and `m ∣ n`.
-/

open Erdos673

theorem OMA.solution : type_of% @Erdos673.erdos_673.variants.tao := by
  intro n m hn hm hmn
  have hn0 : n ≠ 0 := hn.ne'
  have hS : {d : ℕ | d ∣ n} = (n.divisors : Set ℕ) := by
    ext d
    simp [Nat.mem_divisors, hn0]
  have hSfin : {d : ℕ | d ∣ n}.Finite := hS ▸ n.divisors.finite_toSet
  have htoFinset : hSfin.toFinset = n.divisors := by
    ext d
    simp [Nat.mem_divisors, hn0]
  have hnth_mem : ∀ k < n.divisors.card, Nat.nth (· ∣ n) k ∣ n := by
    intro k hk
    have hk' : k < hSfin.toFinset.card := by rw [htoFinset]; exact hk
    exact Nat.nth_mem_of_lt_card hSfin hk'
  have hnth_lt : ∀ {a b : ℕ}, a < b → b < n.divisors.card →
      Nat.nth (· ∣ n) a < Nat.nth (· ∣ n) b := by
    intro a b hab hb
    exact Nat.nth_strictMonoOn hSfin (by simp [Set.mem_Iio, htoFinset]; omega)
      (by simp [Set.mem_Iio, htoFinset]; exact hb) hab
  have hnth_le : ∀ {a b : ℕ}, a ≤ b → b < n.divisors.card →
      Nat.nth (· ∣ n) a ≤ Nat.nth (· ∣ n) b := by
    intro a b hab hb
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (hnth_lt hlt hb).le
  have hcount_lt_card : ∀ d, d ∣ n → Nat.count (· ∣ n) d < n.divisors.card := by
    intro d hd
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨d, Nat.mem_divisors.2 ⟨hd, hn0⟩, by simp⟩
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact Nat.mem_divisors.2 ⟨hx.2, hn0⟩
  constructor
  · -- Lower bound: ((n / m).divisors.card : ℝ) / m ≤ G n
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_trans Nat.zero_lt_one hm)
    -- Multiplication by m gives a later divisor still in the ordered divisor list.
    have divisorIndex (d : ℕ) (hd : d ∈ (n / m).divisors) :
        d ∣ n ∧ m * d ∣ n ∧
        Nat.count (· ∣ n) d < Nat.count (· ∣ n) (m * d) ∧
        Nat.count (· ∣ n) (m * d) < n.divisors.card := by
      have hd_nm : d ∣ n / m := (Nat.mem_divisors.1 hd).1
      have hd_n : d ∣ n := dvd_trans hd_nm (Nat.div_dvd_of_dvd hmn)
      have hmd_n : m * d ∣ n := by
        rcases hd_nm with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        calc n = m * (n / m) := (Nat.mul_div_cancel' hmn).symm
          _ = m * (d * k) := by rw [hk]
          _ = m * d * k := by rw [mul_assoc]
      have hlt : d < m * d := by
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hm (Nat.pos_of_dvd_of_pos hd_n hn)
      exact ⟨hd_n, hmd_n, Nat.count_strict_mono (p := (· ∣ n)) hd_n hlt,
        hcount_lt_card (m * d) hmd_n⟩
    let f : ℕ → Fin (n.divisors.card - 1) := fun d =>
      if h : d ∈ (n / m).divisors then
        ⟨Nat.count (· ∣ n) d, by
          obtain ⟨_, _, hlt, hfin⟩ := divisorIndex d h
          omega⟩
      else
        ⟨0, by
          have h1 : 1 ∈ n.divisors := Nat.mem_divisors.2 ⟨one_dvd n, hn0⟩
          have hm_mem : m ∈ n.divisors := Nat.mem_divisors.2 ⟨hmn, hn0⟩
          have h2 : 2 ≤ n.divisors.card := by
            have hsub : ({1, m} : Finset ℕ) ⊆ n.divisors := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            have hc := Finset.card_le_card hsub
            rw [Finset.card_pair hm.ne] at hc
            exact hc
          omega⟩
    have hf_inj : Set.InjOn f ((n / m).divisors : Set ℕ) := by
      intro a ha b hb hab
      have ha' : a ∈ (n / m).divisors := ha
      have hb' : b ∈ (n / m).divisors := hb
      have ha_n : a ∣ n := (divisorIndex a ha').1
      have hb_n : b ∣ n := (divisorIndex b hb').1
      have hval : (f a).1 = (f b).1 := congrArg Fin.val hab
      simp only [f, ha', hb', ↓reduceDIte] at hval
      have := congrArg (Nat.nth (· ∣ n)) hval
      rwa [Nat.nth_count (p := (· ∣ n)) ha_n, Nat.nth_count (p := (· ∣ n)) hb_n] at this
    calc ((n / m).divisors.card : ℝ) / m
        = ∑ _d ∈ (n / m).divisors, (1 : ℝ) / m := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ∑ d ∈ (n / m).divisors,
            (Nat.nth (· ∣ n) (f d).1 : ℝ) / (Nat.nth (· ∣ n) ((f d).1 + 1) : ℝ) := by
            apply Finset.sum_le_sum
            intro d hd
            obtain ⟨hd_n, hmd_n, hci_lt_cj, hcj_lt⟩ := divisorIndex d hd
            have hfd_val : (f d).1 = Nat.count (· ∣ n) d := by simp only [f, hd, ↓reduceDIte]
            rw [hfd_val, Nat.nth_count (p := (· ∣ n)) hd_n]
            have hnext_le : Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) ≤ m * d := by
              calc Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1)
                  ≤ Nat.nth (· ∣ n) (Nat.count (· ∣ n) (m * d)) :=
                    hnth_le hci_lt_cj hcj_lt
                _ = m * d := Nat.nth_count (p := (· ∣ n)) hmd_n
            have hnext_pos_nat : 0 < Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) :=
              Nat.pos_of_dvd_of_pos (hnth_mem _ (lt_of_le_of_lt hci_lt_cj hcj_lt)) hn
            have hnext_pos : (0 : ℝ) < Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) := by
              exact_mod_cast hnext_pos_nat
            have hnext_le_r : (Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) : ℝ) ≤ (m : ℝ) * (d : ℝ) := by
              exact_mod_cast hnext_le
            rw [div_le_div_iff₀ hm0 hnext_pos]
            linarith
      _ = ∑ i ∈ (n / m).divisors.image f,
            (Nat.nth (· ∣ n) i.1 : ℝ) / (Nat.nth (· ∣ n) (i.1 + 1) : ℝ) := by
            rw [Finset.sum_image (fun a ha b hb hab => hf_inj ha hb hab)]
      _ ≤ ∑ i : Fin (n.divisors.card - 1),
            (Nat.nth (· ∣ n) i.1 : ℝ) / (Nat.nth (· ∣ n) (i.1 + 1) : ℝ) := by
            apply Finset.sum_le_univ_sum_of_nonneg
            intro i
            exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = G n := rfl
  · -- Upper bound: G n ≤ n.divisors.card
    unfold G
    calc ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)
        ≤ ∑ _i : Fin (n.divisors.card - 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hi1 : i.1 + 1 < n.divisors.card := by omega
          have hlt : Nat.nth (· ∣ n) i.1 < Nat.nth (· ∣ n) (i.1 + 1) :=
            hnth_lt (Nat.lt_succ_self i.1) hi1
          have hpos_nat : 0 < Nat.nth (· ∣ n) (i.1 + 1) :=
            Nat.pos_of_dvd_of_pos (hnth_mem _ hi1) hn
          have hpos : (0 : ℝ) < Nat.nth (· ∣ n) (i.1 + 1) := by exact_mod_cast hpos_nat
          rw [div_le_one hpos]
          exact_mod_cast hlt.le
      _ = ((n.divisors.card - 1 : ℕ) : ℝ) := by
          simp
      _ ≤ (n.divisors.card : ℝ) := by
          exact_mod_cast Nat.sub_le n.divisors.card 1
