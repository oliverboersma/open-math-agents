import OMAReductions.R_Erdos50_erdos_50_singular_R1
import Mathlib

/-! Approximate the totient ratio by the totient ratio of an isolated divisor.
For almost every integer in the density sense one needs a divisor d above any
given threshold, sharing precisely the prime factors up to d⁴. A first-moment
bound shows that the omitted primes usually change the ratio by at most d⁻².
The intervals of this radius have summable lengths, giving a Lebesgue-null
limsup. The prime-tail estimates are adapted from @Genbox's Schoenberg proof. -/
namespace OMA.R_Erdos50_erdos_50_singular_R1_H2_R1
open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped Classical

lemma one_sub_nonneg' (p : ℕ) : 0 ≤ 1 - 1 / (p : ℝ) := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    linarith

lemma g_nonneg (D : Finset ℕ) : 0 ≤ ∏ p ∈ D, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p _ => one_sub_nonneg' p

lemma phi_eq {n : ℕ} (hn : n ≠ 0) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  simpa [one_div] using h

lemma prod_ge (s : Finset ℕ) : 1 - ∑ p ∈ s, 1 / (p : ℝ) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 := one_sub_nonneg' a
    have hy : 0 ≤ ∑ p ∈ s, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
    have hx : 0 ≤ 1 / (a : ℝ) := by positivity
    have : (1 - 1 / (a : ℝ)) * (1 - ∑ p ∈ s, 1 / (p : ℝ)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) := mul_le_mul_of_nonneg_left ih h0
    nlinarith

lemma phi_split {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (Nat.totient n : ℝ) = n *
      ((∏ p ∈ ((Finset.range (K+1)).filter Nat.Prime).filter (· ∣ n), (1 - 1/(p:ℝ))) *
       ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1/(p:ℝ))) := by
  rw [phi_eq hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ K)]
  congr 2
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h4⟩; exact ⟨⟨by omega, h1⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3, hn⟩, by omega⟩

lemma tail_sq (K : ℕ) (hK : 1 ≤ K) (N : ℕ) :
    ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  have key : ∀ j : ℕ, ∑ m ∈ (Finset.range (j + K + 1)).filter (fun m => ¬ m ≤ K),
      1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((j + K : ℕ) : ℝ) := by
    intro j
    induction j with
    | zero =>
      have : (Finset.range (0 + K + 1)).filter (fun m => ¬ m ≤ K) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro m hm; simp only [Finset.mem_range] at hm; omega
      rw [this]; simp
    | succ j ih =>
      rw [show j + 1 + K + 1 = (j + K + 1) + 1 by ring, Finset.range_add_one,
        Finset.filter_insert, if_pos (by omega),
        Finset.sum_insert (by simp)]
      have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hjK : (0 : ℝ) < (j + K : ℕ) := by push_cast; positivity
      have e : 1 / (((j + K + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / ((j + K : ℕ) : ℝ) - 1 / ((j + 1 + K : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  have hsub : (Finset.range N).filter (fun m => ¬ m ≤ K) ⊆
      (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K) :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega))
  calc _ ≤ ∑ m ∈ (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 / (K : ℝ) - 1 / ((N + K : ℕ) : ℝ) := key N
    _ ≤ 1 / (K : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((N + K : ℕ) : ℝ) := by positivity
        linarith

lemma card_mult_le (p N : ℕ) (hp : 0 < p) :
    (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ N / p := by
  have h : (Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0) ⊆
      (Finset.Icc 1 (N / p)).image (p * ·) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, ⟨k, rfl⟩, hn0⟩ := hn
    simp only [Finset.mem_image, Finset.mem_Icc]
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hn0
      · exact h
    · rw [Nat.le_div_iff_mul_le hp]; linarith
  have h1 := Finset.card_le_card h
  have h2 := Finset.card_image_le (s := Finset.Icc 1 (N / p)) (f := (p * ·))
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h2
  have h3 : ((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card ≤ N / p := h1.trans h2
  calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ ((N / p : ℕ) : ℝ) := by
        exact_mod_cast h3
    _ ≤ N / p := Nat.cast_div_le

lemma sum_hK (K N : ℕ) (hK1 : 1 ≤ K) : ∑ n ∈ Finset.range N, (∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 1 / (p : ℝ)) ≤ N / K := by
  let hK := fun (K n : ℕ) => ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 1 / (p : ℝ)
  have e1 : ∀ n ∈ Finset.range N, hK K n = ∑ p ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    dsimp only [hK]
    congr 1
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range] at hn ⊢
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2) hn, ⟨h1, h4⟩, h2, h3⟩
    · rintro ⟨_, ⟨h1, h4⟩, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ p ∈ Finset.range N, (∑ n ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0) ≤
      if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0 := by
    intro p _
    by_cases hp : p.Prime ∧ ¬ p ≤ K
    · have hiff : ∀ n, ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) ↔ (p ∣ n ∧ n ≠ 0) :=
        fun n => ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
      rw [if_pos hp.2, Finset.sum_congr rfl (fun n _ => if_congr (hiff n) rfl rfl),
        ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have := card_mult_le p N hp.1.pos
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
      calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) * (1 / p)
          ≤ (N / p) * (1 / p) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = N * (1 / (p : ℝ) ^ 2) := by field_simp
    · have : ∀ n, ¬ ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) := fun n h => hp h.1
      simp only [this, if_false, Finset.sum_const_zero]
      split_ifs <;> positivity
  calc _ ≤ ∑ p ∈ Finset.range N, (if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0) :=
        Finset.sum_le_sum e2
    _ = N * ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_filter]
    _ ≤ N * (1 / K) := mul_le_mul_of_nonneg_left (tail_sq K hK1 N) (by positivity)
    _ = N / K := by ring

lemma cnt_bad (K N : ℕ) (hK1 : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    (((Finset.range N).filter (fun n => δ <
      ∑ p ∈ n.primeFactors.filter (fun p => ¬p ≤ K), (1:ℝ)/(p:ℕ))).card : ℝ) ≤ N / (K * δ) := by
  let cnt := fun (S : Set ℕ) (b : ℕ) => ((Finset.range b).filter (· ∈ S)).card
  let hK := fun (K n : ℕ) => ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 1 / (p : ℝ)
  have hnn : ∀ n, 0 ≤ hK K n := fun n => Finset.sum_nonneg fun p _ => by positivity
  have h1 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ ∑ n ∈ Finset.range N, hK K n := by
    calc (((Finset.range N).filter (· ∈ {n | δ < hK K n})).card : ℝ) * δ
        = ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), hK K n :=
          Finset.sum_le_sum fun n hn => (Finset.mem_filter.1 hn).2.le
      _ ≤ ∑ n ∈ Finset.range N, hK K n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hnn n)
  have h2 := sum_hK K N hK1
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK1
  have h3 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ N / K := h1.trans h2
  rw [le_div_iff₀ hK'] at h3
  rw [le_div_iff₀ (by positivity)]
  calc (cnt {n | δ < hK K n} N : ℝ) * (K * δ) = cnt {n | δ < hK K n} N * δ * K := by ring
    _ ≤ N := h3

/-- The closed-set inequality for empirical measures, with their continuous limiting CDF. -/
def H1 : Prop :=
  let cnt := fun (S : Set ℕ) (b : ℕ) => ((Finset.range b).filter (· ∈ S)).card
  let ratio := fun (n : ℕ) => (n.totient : ℝ) / n
  ∀ f : ℝ → ℝ, Erdos50.IsDistributionOfPhiRatio f →
    ContinuousOn f (Icc 0 1) → ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
    EqOn f (cdf μ) (Icc 0 1) ∧ ∀ C : Set ℝ, IsClosed C → ∀ a : ℝ,
    (∀ᶠ N : ℕ in atTop, a*N ≤ (cnt (ratio ⁻¹' C) N : ℝ)) → ENNReal.ofReal a ≤ μ C

/-- Almost every integer has an isolated initial segment of its prime factors
at some bounded scale above any prescribed threshold. This is a finite
divisibility-pattern question to which the Chinese remainder theorem applies. -/
def H2 : Prop :=
  let cnt := fun (S : Set ℕ) (b : ℕ) => ((Finset.range b).filter (· ∈ S)).card
  let status := fun (Q : Finset ℕ) (n : ℕ) => Q.filter (· ∣ n)
  let QK := fun (K : ℕ) => (Finset.range (K + 1)).filter Nat.Prime
  let isolated := fun (d n : ℕ) => n ≠ 0 ∧ status (QK (d^4)) n = d.primeFactors
  ∀ K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ᶠ N : ℕ in atTop,
    (1-ε)*N ≤ (cnt {n | ∃ d ∈ Finset.Ioc K D, isolated d n} N : ℝ)

lemma approx {d n : ℕ} (hd : 0 < d)
    (hi : n ≠ 0 ∧ ((Finset.range (d^4+1)).filter Nat.Prime).filter (· ∣ n) = d.primeFactors)
    (hb : (∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ d^4), 1/(p:ℝ)) ≤ 1/(d:ℝ)^2) :
    (n.totient : ℝ)/n ∈ Icc ((d.totient:ℝ)/d - 1/(d:ℝ)^2) ((d.totient:ℝ)/d) := by
  let g := fun (D : Finset ℕ) => ∏ p ∈ D, (1 - 1 / (p : ℝ))
  let ratio := fun (n : ℕ) => (n.totient : ℝ) / n
  obtain ⟨hn,hp⟩ := hi
  have factor : ratio n = g d.primeFactors *
      ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ d^4), (1 - 1/(p:ℝ)) := by
    simp [ratio,g,phi_split hn (d^4),hp, hn]
  have center : ratio d = g d.primeFactors := by
    simp [ratio,phi_eq hd.ne',g,hd.ne']
  have g₀ := g_nonneg d.primeFactors
  have prod_le (S : Finset ℕ) : ∏ p ∈ S, (1 - 1/(p:ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p _ => one_sub_nonneg' p) (fun p _ => sub_le_self _ (by positivity))
  have g₁ := prod_le d.primeFactors
  change g d.primeFactors ≤ 1 at g₁
  let S := n.primeFactors.filter (fun p => ¬ p ≤ d^4)
  have hlow : 1-1/(d:ℝ)^2 ≤ ∏ p ∈ S, (1-1/(p:ℝ)) :=
    (sub_le_sub_left hb 1).trans (prod_ge S)
  change ratio d - _ ≤ ratio n ∧ ratio n ≤ ratio d
  rw [center,factor]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlow g₀,
      mul_le_mul_of_nonneg_right g₁ (show 0 ≤ 1/(d:ℝ)^2 by positivity)]
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left (prod_le S) g₀

lemma count_window (K D N : ℕ) (hk : 1 ≤ K) :
  let cnt := fun (S : Set ℕ) (b : ℕ) => ((Finset.range b).filter (· ∈ S)).card
  let status := fun (Q : Finset ℕ) (n : ℕ) => Q.filter (· ∣ n)
  let hK := fun (K n : ℕ) => ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 1 / (p : ℝ)
  let QK := fun (K : ℕ) => (Finset.range (K + 1)).filter Nat.Prime
  let ratio := fun (n : ℕ) => (n.totient : ℝ) / n
  let window := fun (d : ℕ) => Icc (ratio d - 1/(d:ℝ)^2) (ratio d)
  let isolated := fun (d n : ℕ) => n ≠ 0 ∧ status (QK (d^4)) n = d.primeFactors
  (cnt {n | ∃ d ∈ Finset.Ioc K D, isolated d n} N : ℝ) ≤
    cnt (ratio ⁻¹' (⋃ d ∈ Finset.Ioc K D, window d)) N + N/(K:ℝ) := by
  intro cnt status hK QK ratio window isolated
  classical
  let I := Finset.Ioc K D
  let B (d : ℕ) := (Finset.range N).filter (fun n => 1/(d:ℝ)^2 < hK (d^4) n)
  let A := (Finset.range N).filter (fun n => ratio n ∈ ⋃ d ∈ I, window d)
  have incl : (Finset.range N).filter (fun n => ∃ d ∈ I, isolated d n) ⊆ A ∪ I.biUnion B := by
    intro n hn
    obtain ⟨hn, d, hd, hi⟩ := Finset.mem_filter.mp hn
    by_cases hb : 1/(d:ℝ)^2 < hK (d^4) n
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_filter.mpr ⟨hn,hb⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,mem_iUnion.mpr ⟨d,
        mem_iUnion.mpr ⟨hd,approx (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hd).1) hi (le_of_not_gt hb)⟩⟩⟩)
  have card := (Finset.card_le_card incl).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_biUnion_le) _))
  have cast : (cnt {n | ∃ d ∈ I, isolated d n} N : ℝ) ≤
      (A.card:ℝ) + ∑ d ∈ I, ((B d).card:ℝ) := by
    have e : cnt {n | ∃ d ∈ I, isolated d n} N = ((Finset.range N).filter (fun n => ∃ d ∈ I, isolated d n)).card := by
      apply congrArg Finset.card
      ext n
      simp [cnt]
    rw [e]
    exact_mod_cast card
  apply cast.trans
  apply add_le_add_right
  calc
    ∑ d ∈ I, ((B d).card:ℝ) ≤ ∑ d ∈ I, (N:ℝ)*(1/(d:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hd
      have dp : 0 < d := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hd).1
      have h := cnt_bad (d^4) N (Nat.one_le_pow _ _ dp) (δ := 1/(d:ℝ)^2) (by positivity)
      change ((B d).card:ℝ) ≤ _ at h
      push_cast at h
      exact h.trans_eq (by field_simp)
    _ = (N:ℝ) * (∑ d ∈ I, 1/(d:ℝ)^2) := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      have he : I = (Finset.range (D+1)).filter (fun d => ¬d ≤ K) := by ext d; simp [I]; omega
      rw [he,div_eq_mul_inv (N:ℝ)]
      simpa only [one_div] using mul_le_mul_of_nonneg_left (tail_sq K hk (D+1)) (Nat.cast_nonneg (α := ℝ) N)

lemma volume_rare :
    let ratio (n : ℕ) := (n.totient:ℝ) / n
    let window (d : ℕ) := Icc (ratio d - 1/(d:ℝ)^2) (ratio d)
    ∀ᵐ x : ℝ, ∀ᶠ d : ℕ in atTop, x ∉ window d := by
  intro ratio window
  apply ae_eventually_notMem
  have meas (d : ℕ) : volume (window d) = ENNReal.ofReal (1/(d:ℝ)^2) := by
    simp [window,Real.volume_Icc]
  change (∑' d, volume (window d)) ≠ ⊤
  simp_rw [meas]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n : ℕ => by positivity)
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))]
  exact ENNReal.ofReal_ne_top

theorem main : H1 → H2 → OMA.R_Erdos50_erdos_50_singular_R1.H2 := by
  let cnt := fun (S : Set ℕ) (b : ℕ) => ((Finset.range b).filter (· ∈ S)).card
  let ratio := fun (n : ℕ) => (n.totient : ℝ) / n
  let window := fun (d : ℕ) => Icc (ratio d - 1/(d:ℝ)^2) (ratio d)
  classical
  intro law isolated_often f hf hc
  obtain ⟨μ,hprob,heq,hclosed⟩ := law f hf hc
  letI := hprob
  let U (k : ℕ) := ⋃ d ≥ k, window d
  have full (k : ℕ) : μ (U k) = 1 := by
    apply le_antisymm prob_le_one
    by_contra! h
    have hμ : (μ (U k)).toReal < 1 := by
      exact_mod_cast (ENNReal.toReal_lt_toReal (measure_ne_top μ (U k)) ENNReal.one_ne_top).mpr h
    let ε := (1-(μ (U k)).toReal)/3
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨m,hm⟩ := exists_nat_gt (1/ε)
    let K := max (max k 1) m
    have hK : 1 ≤ K := (le_max_right _ _).trans (le_max_left ..)
    have hk : k ≤ K := (le_max_left ..).trans (le_max_left ..)
    have inv : 1/(K:ℝ) ≤ ε := by
      have a : 1/ε ≤ (K:ℝ) := hm.le.trans (by exact_mod_cast (le_max_right (max k 1) m))
      calc 1/(K:ℝ) ≤ 1/(1/ε) := one_div_le_one_div_of_le (by positivity) a
           _ = ε := by simp
    obtain ⟨D,hD⟩ := isolated_often K ε hε
    let C := ⋃ d ∈ Finset.Ioc K D, window d
    have closed : IsClosed C := isClosed_biUnion_finset fun _ _ => isClosed_Icc
    have lb := hclosed C closed (1-2*ε) (by
      filter_upwards [hD] with N hN
      have bound := count_window K D N hK
      change _ ≤ (cnt (ratio ⁻¹' C) N : ℝ) + _ at bound
      have err : (N:ℝ)/K ≤ ε*N := by
        simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_right inv (Nat.cast_nonneg (α := ℝ) N)
      have comb := hN.trans bound
      change (1-2*ε)*N ≤ (cnt (ratio ⁻¹' C) N : ℝ)
      linarith only [comb,err])
    have incl : C ⊆ U k := by
      intro x hx
      obtain ⟨d,hh⟩ := mem_iUnion.mp hx
      obtain ⟨hd,hx⟩ := mem_iUnion.mp hh
      exact mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨hk.trans (Finset.mem_Ioc.mp hd).1.le,hx⟩⟩
    have := ENNReal.toReal_mono (measure_ne_top μ (U k)) (lb.trans (measure_mono incl))
    rw [ENNReal.toReal_ofReal (by dsimp [ε]; linarith [ENNReal.toReal_nonneg (a := μ (U k))])] at this
    dsimp [ε] at this
    linarith
  have lim : ∀ᵐ x ∂μ, ∃ᶠ d : ℕ in atTop, x ∈ window d := by
    have hall : ∀ k, ∀ᵐ x ∂μ, x ∈ U k := by
      intro k
      rw [ae_iff]
      change μ (U k)ᶜ = 0
      have hms : MeasurableSet (U k) := MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun _ => measurableSet_Icc
      rw [measure_compl hms (measure_ne_top μ (U k)),full]
      simp
    filter_upwards [ae_all_iff.mpr hall] with x hx
    apply frequently_atTop.mpr
    intro k
    simpa [U] using hx k
  have sing : μ ⟂ₘ volume := Measure.mutuallySingular_iff_disjoint_ae.mpr
    (disjoint_of_disjoint_of_mem (s := {x | ∃ᶠ d : ℕ in atTop, x ∈ window d})
      disjoint_compl_right lim (by
        filter_upwards [volume_rare] with x hx
        exact fun h => h hx))
  have dh := (cdf μ).ae_hasDerivAt
  rw [measure_cdf] at dh
  filter_upwards [ae_restrict_of_ae dh,ae_restrict_of_ae sing.rnDeriv_ae_eq_zero,
    ae_restrict_mem (μ := volume) (measurableSet_Icc (a := (0:ℝ)) (b := 1))] with x hx hz hxI
  rw [hz] at hx
  simpa using (hx.hasDerivWithinAt.congr (fun y hy => heq hy) (heq hxI)).derivWithin
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) x hxI)

end OMA.R_Erdos50_erdos_50_singular_R1_H2_R1
