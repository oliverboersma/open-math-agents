import OMAReductions.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R1
import Mathlib

/-!
Step H2 of Erdos820.erdos_820.variants.erdos_lower.R1.H1.R1, by double counting.
Some dyadic block [D, 2D) contains at least d(K)/(log_2 K + 1) divisors d of K. For each such d
there are at least X/(2 A D log X) primes p ≤ X with d | p - 1. Each pair (d, p) gives
m = (p - 1)/d in [1, X/D], and p - 1 = d m divides n = K m with p ≤ n + 1; distinct pairs with the
same m have distinct p. Averaging over the at most X/D values of m gives some n = K m with at
least d(K) / (2 (log_2 K + 1) A log X) primes p with p - 1 dividing n.
-/

open scoped Classical in
theorem OMA.solution : OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R1.H2
  intro K X hK hKX A hA hd
  have hX2 : 2 ≤ X := le_trans hK hKX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  set L := Nat.log 2 K with hL
  set Div := K.divisors with hDiv
  let blk : ℕ → Finset ℕ := fun j => Div.filter (fun d => Nat.log 2 d = j)
  obtain ⟨j, -, hblk⟩ : ∃ j ∈ Finset.range (L + 1), Div.card ≤ (L + 1) * (blk j).card := by
    by_contra hcon
    push Not at hcon
    have hmaps : ∀ d ∈ Div, Nat.log 2 d ∈ Finset.range (L + 1) := by
      intro d hdd
      rw [Finset.mem_range]
      have h1 : d ≤ K := Nat.divisor_le hdd
      have h2 : Nat.log 2 d ≤ Nat.log 2 K := Nat.log_mono_right h1
      omega
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    have hlt := Finset.sum_lt_sum_of_nonempty (⟨0, by simp⟩ : (Finset.range (L + 1)).Nonempty) hcon
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt
    have hs : ∑ i ∈ Finset.range (L + 1), (blk i).card = Div.card := hsum.symm
    rw [hs] at hlt
    exact lt_irrefl _ hlt
  have hKmem : K ∈ Div := Nat.mem_divisors_self K (by omega)
  have hDivpos : 0 < Div.card := Finset.card_pos.mpr ⟨K, hKmem⟩
  have hblkne : (blk j).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    push Not at h0
    have : (blk j).card = 0 := by omega
    rw [this, mul_zero] at hblk
    omega
  set D := 2 ^ j with hD
  have hDpos : 0 < D := by positivity
  have hblkD : ∀ d ∈ blk j, D ≤ d ∧ d < 2 * D := by
    intro d hdd
    obtain ⟨hdd1, hdd2⟩ := Finset.mem_filter.mp hdd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hdd1)
    constructor
    · rw [hD, ← hdd2]
      exact Nat.pow_log_le_self 2 hd0
    · rw [hD, ← hdd2, ← pow_succ']
      exact Nat.lt_pow_succ_log_self (by norm_num) d
  have hDX : D ≤ X := by
    obtain ⟨d0, hd0⟩ := hblkne
    have h1 := (hblkD d0 hd0).1
    have h2 : d0 ≤ K := Nat.divisor_le (Finset.mem_filter.mp hd0).1
    omega
  let primesFor : ℕ → Finset ℕ := fun d => (Finset.range (X + 1)).filter (fun p => p.Prime ∧ d ∣ p - 1)
  let Q := (blk j).sigma primesFor
  let g : (Σ _ : ℕ, ℕ) → ℕ := fun s => (s.2 - 1) / s.1
  let Mset := Finset.Icc 1 (X / D)
  have hgmaps : ∀ s ∈ Q, g s ∈ Mset := by
    rintro ⟨d, p⟩ hs
    rw [Finset.mem_sigma] at hs
    dsimp only at hs
    obtain ⟨hdb, hp⟩ := hs
    obtain ⟨hpr, hpp, hdp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hD1, -⟩ := hblkD d hdb
    obtain ⟨m, hm⟩ := hdp
    have hp2 := hpp.two_le
    have hd0 : 0 < d := by omega
    have hpX : p ≤ X := by
      rw [Finset.mem_range] at hpr
      omega
    show (p - 1) / d ∈ Finset.Icc 1 (X / D)
    rw [hm, Nat.mul_div_cancel_left m hd0, Finset.mem_Icc]
    constructor
    · rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm
        omega
      · exact h0
    · rw [Nat.le_div_iff_mul_le hDpos]
      calc m * D = D * m := mul_comm _ _
        _ ≤ d * m := Nat.mul_le_mul_right m hD1
        _ = p - 1 := hm.symm
        _ ≤ X := by omega
  obtain ⟨m, hmM, hQm⟩ : ∃ m ∈ Mset, Q.card ≤ Mset.card * (Q.filter (fun s => g s = m)).card := by
    by_contra hcon
    push Not at hcon
    have hsum := Finset.card_eq_sum_card_fiberwise hgmaps
    have hne : Mset.Nonempty := ⟨1, by
      rw [Finset.mem_Icc]
      exact ⟨le_rfl, (Nat.one_le_div_iff hDpos).mpr hDX⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne hcon
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul, ← hsum] at hlt
    exact lt_irrefl _ hlt
  have hm1 := Finset.mem_Icc.mp hmM
  have hmpos : 0 < m := hm1.1
  let T := (Finset.range (K * m + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ K * m)
  have hFT : (Q.filter (fun s => g s = m)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun s => s.2)
    · rintro ⟨d, p⟩ hs
      have hs' := Finset.mem_filter.mp hs
      obtain ⟨hsQ, hgs⟩ := hs'
      rw [Finset.mem_sigma] at hsQ
      dsimp only at hsQ
      obtain ⟨hdb, hp⟩ := hsQ
      obtain ⟨-, hpp, hdp⟩ := Finset.mem_filter.mp hp
      have hgs' : (p - 1) / d = m := hgs
      have hdK : d ∣ K := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdb).1
      have hdle : d ≤ K := Nat.divisor_le (Finset.mem_filter.mp hdb).1
      have hpm : p - 1 = d * m := by
        rw [← hgs']
        exact (Nat.mul_div_cancel' hdp).symm
      have hp2 := hpp.two_le
      have hle : d * m ≤ K * m := Nat.mul_le_mul_right m hdle
      show p ∈ T
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, hpp, ?_⟩
      rw [hpm]
      exact Nat.mul_dvd_mul_right hdK m
    · rintro ⟨d, p⟩ hs ⟨d', p'⟩ hs' hpp'
      have hpe : p = p' := hpp'
      subst hpe
      have h1 := Finset.mem_filter.mp hs
      have h2 := Finset.mem_filter.mp hs'
      rw [Finset.mem_sigma] at h1 h2
      have hdp := (Finset.mem_filter.mp h1.1.2).2.2
      have hdp' := (Finset.mem_filter.mp h2.1.2).2.2
      have hg1 : (p - 1) / d = m := h1.2
      have hg2 : (p - 1) / d' = m := h2.2
      have e1 : p - 1 = d * m := by rw [← hg1]; exact (Nat.mul_div_cancel' hdp).symm
      have e2 : p - 1 = d' * m := by rw [← hg2]; exact (Nat.mul_div_cancel' hdp').symm
      have hdd : d = d' := Nat.eq_of_mul_eq_mul_right hmpos (e1.symm.trans e2)
      subst hdd
      rfl
  have hQcard : Q.card = ∑ d ∈ blk j, (primesFor d).card := Finset.card_sigma _ _
  have hMcard : Mset.card = X / D := by simp [Mset]
  have hcnt : ∀ d ∈ blk j, (X : ℝ) ≤ A * (2 * D) * Real.log X * (primesFor d).card := by
    intro d hdb
    have h1 := hd d (Finset.mem_filter.mp hdb).1
    have h2 : (d : ℝ) ≤ 2 * D := by exact_mod_cast (hblkD d hdb).2.le
    calc (X : ℝ) ≤ A * d * Real.log X * (primesFor d).card := h1
      _ ≤ A * (2 * D) * Real.log X * (primesFor d).card := by
        gcongr
  have hsumR : ((blk j).card : ℝ) * X ≤ A * (2 * D) * Real.log X * Q.card := by
    rw [hQcard, Nat.cast_sum, Finset.mul_sum]
    calc ((blk j).card : ℝ) * X = ∑ _d ∈ blk j, (X : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hcnt
  have hQT : (Q.card : ℝ) ≤ (X / D : ℝ) * T.card := by
    have h1 : Q.card ≤ (X / D) * T.card := by
      calc Q.card ≤ Mset.card * (Q.filter (fun s => g s = m)).card := hQm
        _ ≤ (X / D) * T.card := by rw [hMcard]; exact Nat.mul_le_mul_left _ hFT
    calc (Q.card : ℝ) ≤ ((X / D : ℕ) : ℝ) * T.card := by exact_mod_cast h1
      _ ≤ (X / D : ℝ) * T.card := by
        gcongr
        exact Nat.cast_div_le
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hblkR : ((blk j).card : ℝ) ≤ 2 * A * Real.log X * T.card := by
    have h3 : ((blk j).card : ℝ) * X ≤ A * (2 * D) * Real.log X * ((X / D : ℝ) * T.card) := by
      calc ((blk j).card : ℝ) * X ≤ A * (2 * D) * Real.log X * Q.card := hsumR
        _ ≤ A * (2 * D) * Real.log X * ((X / D : ℝ) * T.card) := by
          gcongr
    have h4 : A * (2 * D) * Real.log X * ((X / D : ℝ) * T.card) =
        (2 * A * Real.log X * T.card) * X := by
      field_simp
    rw [h4] at h3
    exact le_of_mul_le_mul_right h3 hXpos
  refine ⟨K * m, ?_, ?_, ?_⟩
  · calc K = K * 1 := (mul_one K).symm
      _ ≤ K * m := Nat.mul_le_mul_left K hmpos
  · have : m ≤ X := le_trans hm1.2 (Nat.div_le_self X D)
    exact Nat.mul_le_mul_left K this
  · have hDivR : (Div.card : ℝ) ≤ ((L : ℝ) + 1) * (blk j).card := by exact_mod_cast hblk
    have hL0 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
    calc (K.divisors.card : ℝ) = Div.card := rfl
      _ ≤ ((L : ℝ) + 1) * (blk j).card := hDivR
      _ ≤ ((L : ℝ) + 1) * (2 * A * Real.log X * T.card) := by gcongr
      _ = 2 * ((L : ℝ) + 1) * A * Real.log X * T.card := by ring
