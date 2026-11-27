import FormalConjectures.ErdosProblems.«17»

-- Problem: Erdős Problem 17 — upper BES
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/17.lean:56 (declaration Erdos17.erdos_17.variants.upper_BES)
-- Credit: @akhtyamovpavel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Elementary proof of Blecksmith-Erdos-Selfridge (1999):
clusterPrimeCount x = O(x / (log x)^A) for every A > 0.
-/

open Filter Asymptotics Real BigOperators
open scoped Classical

namespace Erdos17BES

/- Block 1: Cluster primes imply prime (K + 1)-tuples -/

def gapM : ℕ → ℕ
  | 0 => 9
  | i + 1 => (gapM i + 3).factorial + gapM i + 2

lemma gapM_ge_nine (i : ℕ) : 9 ≤ gapM i := by
  induction i with
  | zero => decide
  | succ i ih =>
    simp only [gapM]
    omega

lemma gapM_odd (i : ℕ) : Odd (gapM i) := by
  induction i with
  | zero => decide
  | succ i ih =>
    simp only [gapM]
    have hge : 2 ≤ gapM i + 3 := by have := gapM_ge_nine i; omega
    have h2 : 2 ∣ (gapM i + 3).factorial := Nat.dvd_factorial (by decide) hge
    rcases h2 with ⟨k, hk⟩
    rcases ih with ⟨m, hm⟩
    exact ⟨k + m + 1, by omega⟩

lemma gapM_strictMono : StrictMono gapM := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  simp only [gapM]
  have hpos := Nat.factorial_pos (gapM i + 3)
  omega

lemma gapM_not_prime (i : ℕ) : ¬ (gapM i).Prime := by
  induction i with
  | zero => decide
  | succ i _ =>
    simp only [gapM]
    have hge := gapM_ge_nine i
    have hdvd : gapM i + 2 ∣ (gapM i + 3).factorial :=
      Nat.dvd_factorial (by omega) (by omega)
    have hdvd2 : gapM i + 2 ∣ (gapM i + 3).factorial + gapM i + 2 := by
      have : (gapM i + 3).factorial + gapM i + 2 = (gapM i + 3).factorial + (gapM i + 2) := by omega
      rw [this]
      exact dvd_add hdvd dvd_rfl
    have hpos := Nat.factorial_pos (gapM i + 3)
    intro hp
    rcases hp.eq_one_or_self_of_dvd (gapM i + 2) hdvd2 with h1 | hself <;> omega

lemma gapM_composite_interval {i t : ℕ} (h1 : gapM (i + 1) - gapM i ≤ t)
    (h2 : t ≤ gapM (i + 1)) : ¬ t.Prime := by
  have hgap : gapM (i + 1) = (gapM i + 3).factorial + gapM i + 2 := rfl
  have hge := gapM_ge_nine i
  have hpos := Nat.factorial_pos (gapM i + 3)
  set s := t - (gapM i + 3).factorial with hs
  have hs1 : 2 ≤ s := by omega
  have hs2 : s ≤ gapM i + 2 := by omega
  have ht : t = (gapM i + 3).factorial + s := by omega
  have hdvd : s ∣ (gapM i + 3).factorial :=
    Nat.dvd_factorial (by omega) (by omega)
  have hdvd_t : s ∣ t := by
    rw [ht]
    exact dvd_add hdvd dvd_rfl
  intro hp
  rcases hp.eq_one_or_self_of_dvd s hdvd_t with h1s | hself <;> omega

def shiftSet (i : ℕ) : Finset ℕ :=
  ((Finset.range (gapM i)).filter (fun r => r.Prime ∧ Odd r)).image (fun r => gapM i - r)

lemma shiftSet_pos {i d : ℕ} (hd : d ∈ shiftSet i) : 0 < d ∧ d < gapM i := by
  simp only [shiftSet, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
  rcases hd with ⟨r, ⟨hr, hrp, -⟩, rfl⟩
  have h2 := hrp.two_le
  omega

lemma shiftSet_gt_prev {i d : ℕ} (hd : d ∈ shiftSet (i + 1)) : gapM i < d := by
  simp only [shiftSet, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
  rcases hd with ⟨r, ⟨hr, hrp, -⟩, rfl⟩
  have hlt : r < gapM (i + 1) - gapM i := by
    by_contra! hge
    exact gapM_composite_interval hge (le_of_lt hr) hrp
  have hm : gapM i < gapM (i + 1) := gapM_strictMono (Nat.lt_succ_self i)
  omega

lemma cluster_prime_has_shift {p i : ℕ} (hp : Erdos17.IsClusterPrime p) (hgt : gapM i < p) :
    ∃ d ∈ shiftSet i, (p - d).Prime ∧ d < p := by
  have hge9 := gapM_ge_nine i
  have hp_odd : Odd p := by
    rcases hp.1.eq_two_or_odd with rfl | hodd
    · omega
    · exact Nat.odd_iff.mpr hodd
  have hm_odd := gapM_odd i
  have heven : Even (p - gapM i) := by
    rcases hp_odd with ⟨a, ha⟩
    rcases hm_odd with ⟨b, hb⟩
    exact ⟨a - b, by omega⟩
  have hle : ((p - gapM i : ℕ) : ℤ) ≤ (p : ℤ) - 3 := by omega
  obtain ⟨q₁, q₂, hq1p, hq2p, hq1le, hq2le, heq⟩ := hp.2 heven hle
  have hq_eq : p - gapM i + q₂ = q₁ := by omega
  have hq2_le : q₂ ≤ gapM i := by omega
  have hq2_ne : q₂ ≠ gapM i := by
    intro heq2
    exact gapM_not_prime i (heq2 ▸ hq2p)
  have hq2_lt : q₂ < gapM i := lt_of_le_of_ne hq2_le hq2_ne
  have hq2_odd : Odd q₂ := by
    rcases hq2p.eq_two_or_odd with rfl | hodd
    · have hq1_even : Even q₁ := by
        rw [← hq_eq]
        rcases heven with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      have hq1_ge : 4 ≤ q₁ := by
        rcases heven with ⟨k, hk⟩
        have hpos : 0 < p - gapM i := by omega
        omega
      rcases hq1p.eq_two_or_odd with h2 | hodd1
      · omega
      · rcases hq1_even with ⟨r, hr⟩
        omega
    · exact Nat.odd_iff.mpr hodd
  refine ⟨gapM i - q₂, ?_, ?_, ?_⟩
  · simp only [shiftSet, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨q₂, ⟨hq2_lt, hq2p, hq2_odd⟩, rfl⟩
  · have hpd : p - (gapM i - q₂) = q₁ := by omega
    rw [hpd]
    exact hq1p
  · omega

def validTuples (K : ℕ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset (fun i : Fin K => shiftSet i.val)

def tupleShift {K : ℕ} (d : Fin K → ℕ) : Fin (K + 1) → ℕ :=
  Fin.cases 0 d

lemma tupleShift_zero {K : ℕ} (d : Fin K → ℕ) : tupleShift d 0 = 0 := rfl

lemma validTuples_strictMono {K : ℕ} {d : Fin K → ℕ} (hd : d ∈ validTuples K) :
    StrictMono (tupleShift d) := by
  have hd_mem : ∀ i : Fin K, d i ∈ shiftSet i.val := by
    simpa [validTuples] using hd
  have hmono_d : StrictMono d := by
    intro i j hij
    have hi : d i < gapM i.val := (shiftSet_pos (hd_mem i)).2
    obtain ⟨k, hk⟩ : ∃ k, j.val = k + 1 := ⟨j.val - 1, by omega⟩
    have hle : gapM i.val ≤ gapM k := gapM_strictMono.monotone (by omega)
    have hj_mem : d j ∈ shiftSet (k + 1) := hk ▸ hd_mem j
    have hj : gapM k < d j := shiftSet_gt_prev hj_mem
    omega
  intro a b hab
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => exact absurd hab (lt_irrefl _)
    | succ j => exact (shiftSet_pos (hd_mem j)).1
  | succ i =>
    cases b using Fin.cases with
    | zero => exact absurd hab (Nat.not_lt_zero _)
    | succ j => exact hmono_d (Fin.succ_lt_succ_iff.mp hab)

lemma validTuples_lt_gapM {K : ℕ} {d : Fin K → ℕ} (hd : d ∈ validTuples K) (j : Fin (K + 1)) :
    tupleShift d j < gapM K := by
  have hd_mem : ∀ i : Fin K, d i ∈ shiftSet i.val := by
    simpa [validTuples] using hd
  refine Fin.cases ?_ (fun i => ?_) j
  · have := gapM_ge_nine K
    simp only [tupleShift_zero]
    omega
  · simp only [tupleShift, Fin.cases_succ]
    have hi : d i < gapM i.val := (shiftSet_pos (hd_mem i)).2
    have hlt : gapM i.val < gapM K := gapM_strictMono i.isLt
    omega

lemma clusterPrimeCount_le_tuples (K x : ℕ) :
    (Erdos17.clusterPrimeCount x : ℝ) ≤ (gapM K + 1 : ℝ) +
      ∑ d ∈ validTuples K,
        (((Finset.Icc 0 x).filter (fun p => ∀ j : Fin (K + 1), (p - tupleShift d j).Prime)).card : ℝ) := by
  have hset : {p : ℕ | p ≤ x ∧ Erdos17.IsClusterPrime p} =
      ↑((Finset.Icc 0 x).filter Erdos17.IsClusterPrime) := by
    ext p
    simp [Finset.mem_Icc]
  have hcard : Erdos17.clusterPrimeCount x =
      ((Finset.Icc 0 x).filter Erdos17.IsClusterPrime).card := by
    rw [Erdos17.clusterPrimeCount, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard]
  norm_cast
  set S := (Finset.Icc 0 x).filter Erdos17.IsClusterPrime
  have hsub : S ⊆ Finset.Icc 0 (gapM K) ∪
      (validTuples K).biUnion (fun d =>
        (Finset.Icc 0 x).filter (fun p => ∀ j : Fin (K + 1), (p - tupleShift d j).Prime)) := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨_, hpx⟩, hcp⟩
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_biUnion]
    rcases le_or_gt p (gapM K) with hle | hgt
    · exact Or.inl ⟨Nat.zero_le p, hle⟩
    · refine Or.inr ?_
      have hchoice : ∀ i : Fin K, ∃ d ∈ shiftSet i.val, (p - d).Prime := by
        intro i
        have hi : gapM i.val < p := lt_trans (gapM_strictMono i.isLt) hgt
        obtain ⟨d, hd, hpd, -⟩ := cluster_prime_has_shift hcp hi
        exact ⟨d, hd, hpd⟩
      choose d hd using hchoice
      refine ⟨d, ?_, ?_⟩
      · simpa [validTuples] using fun i => (hd i).1
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.zero_le p, hpx⟩, Fin.cases ?_ (fun i => ?_)⟩
        · simp only [tupleShift, Fin.cases_zero, Nat.sub_zero]
          exact hcp.1
        · exact (hd i).2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.Icc 0 (gapM K))
    ((validTuples K).biUnion (fun d =>
      (Finset.Icc 0 x).filter (fun p => ∀ j : Fin (K + 1), (p - tupleShift d j).Prime)))
  have h3 : ((validTuples K).biUnion (fun d =>
      (Finset.Icc 0 x).filter (fun p => ∀ j : Fin (K + 1), (p - tupleShift d j).Prime))).card ≤
      ∑ d ∈ validTuples K,
        ((Finset.Icc 0 x).filter (fun p => ∀ j : Fin (K + 1), (p - tupleShift d j).Prime)).card :=
    Finset.card_biUnion_le
  have hIcc : (Finset.Icc 0 (gapM K)).card = gapM K + 1 := by simp
  omega

/- Block 2A: Selberg sieve weights, GoodMod, and divisor identities -/

def GoodMod (P₀ d : ℕ) : Prop :=
  Squarefree d ∧ ∀ p ∈ d.primeFactors, P₀ < p

noncomputable def S_R (P₀ R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (GoodMod P₀)

def ω (k1 d : ℕ) : ℕ := k1 ^ d.primeFactors.card

noncomputable def h_val (k1 d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, ((p : ℝ) - k1) / (k1 : ℝ)

noncomputable def G_val (k1 P₀ R : ℕ) : ℝ :=
  ∑ k ∈ S_R P₀ R, (h_val k1 k)⁻¹

lemma goodMod_pos {P₀ d : ℕ} (hd : GoodMod P₀ d) : 0 < d :=
  Nat.pos_of_ne_zero hd.1.ne_zero

lemma goodMod_one (P₀ : ℕ) : GoodMod P₀ 1 :=
  ⟨squarefree_one, by simp⟩

lemma goodMod_dvd {P₀ d k : ℕ} (hd : GoodMod P₀ d) (hk : k ∣ d) : GoodMod P₀ k :=
  ⟨hd.1.squarefree_of_dvd hk, fun p hp => hd.2 p (Nat.primeFactors_mono hk hd.1.ne_zero hp)⟩

lemma goodMod_mul {P₀ a b : ℕ} (ha : GoodMod P₀ a) (hb : GoodMod P₀ b) (hab : Nat.Coprime a b) :
    GoodMod P₀ (a * b) := by
  refine ⟨Nat.squarefree_mul_iff.mpr ⟨hab, ha.1, hb.1⟩, fun p hp => ?_⟩
  rw [Nat.primeFactors_mul ha.1.ne_zero hb.1.ne_zero, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact ha.2 p hp
  · exact hb.2 p hp

lemma goodMod_lcm {P₀ a b : ℕ} (ha : GoodMod P₀ a) (hb : GoodMod P₀ b) :
    GoodMod P₀ (Nat.lcm a b) := by
  have hlcm0 : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha.1.ne_zero hb.1.ne_zero
  have hsq : Squarefree (Nat.lcm a b) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp ⟨k, hk⟩
    have hdvd : p * p ∣ Nat.lcm a b := ⟨k, hk⟩
    have hlcm_dvd : Nat.lcm a b = a * (b / Nat.gcd a b) := by
      rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right a b)]
    have hcop : Nat.Coprime a (b / Nat.gcd a b) := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_div_gcd_of_squarefree hb.1 ha.1.ne_zero).symm
    have hp_dvd : p * p ∣ a * (b / Nat.gcd a b) := hlcm_dvd ▸ hdvd
    have hsq_b : Squarefree (b / Nat.gcd a b) := hb.1.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a b))
    have hsq_lcm : Squarefree (a * (b / Nat.gcd a b)) :=
      Nat.squarefree_mul_iff.mpr ⟨hcop, ha.1, hsq_b⟩
    exact Nat.squarefree_iff_prime_squarefree.mp hsq_lcm p hp hp_dvd
  refine ⟨hsq, fun p hp => ?_⟩
  have hdvd : p ∣ a * b := (Nat.mem_primeFactors.mp hp).2.1.trans (Nat.lcm_dvd_mul a b)
  rcases (Nat.mem_primeFactors.mp hp).1.dvd_mul.mp hdvd with hpa | hpb
  · exact ha.2 p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hpa, ha.1.ne_zero⟩)
  · exact hb.2 p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hpb, hb.1.ne_zero⟩)

lemma ω_one (k1 : ℕ) : ω k1 1 = 1 := by simp [ω]

lemma h_val_one (k1 : ℕ) : h_val k1 1 = 1 := by simp [h_val]

lemma ω_mul_coprime {k1 a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    ω k1 (a * b) = ω k1 a * ω k1 b := by
  simp only [ω, Nat.primeFactors_mul ha hb]
  rw [Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hab), pow_add]

lemma h_val_mul_coprime {k1 a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    h_val k1 (a * b) = h_val k1 a * h_val k1 b := by
  simp only [h_val, Nat.primeFactors_mul ha hb]
  exact Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)

lemma h_val_pos {k1 P₀ d : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hd : GoodMod P₀ d) :
    0 < h_val k1 d := by
  refine Finset.prod_pos fun p hp => ?_
  have hp_gt : k1 < p := lt_of_le_of_lt hP0 (hd.2 p hp)
  have h1 : (k1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_gt
  have hk0 : (0 : ℝ) < (k1 : ℝ) := by exact_mod_cast hk1
  exact div_pos (sub_pos.mpr h1) hk0

lemma G_val_ge_one {k1 P₀ R : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hR : 1 ≤ R) :
    1 ≤ G_val k1 P₀ R := by
  have hmem : 1 ∈ S_R P₀ R := by
    simp only [S_R, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hR⟩, goodMod_one P₀⟩
  have h1 : (1 : ℝ) = (h_val k1 1)⁻¹ := by simp [h_val_one]
  rw [h1]
  refine Finset.single_le_sum (f := fun k => (h_val k1 k)⁻¹) (fun k hk => ?_) hmem
  simp only [S_R, Finset.mem_filter] at hk
  exact inv_nonneg.mpr (le_of_lt (h_val_pos hk1 hP0 hk.2))

lemma ω_pow_four_le {k1 P₀ d : ℕ} (hP0 : k1 ^ 4 ≤ P₀) (hd : GoodMod P₀ d) :
    (ω k1 d) ^ 4 ≤ d := by
  rw [ω, ← pow_mul, mul_comm, pow_mul]
  calc
    (k1 ^ 4) ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, k1 ^ 4 := by simp
    _ ≤ ∏ p ∈ d.primeFactors, p := by
      refine Finset.prod_le_prod' fun p hp => ?_
      have := hd.2 p hp
      omega
    _ = d := Nat.prod_primeFactors_of_squarefree hd.1

lemma ω_real_le_rpow {k1 P₀ d : ℕ} (hP0 : k1 ^ 4 ≤ P₀) (hd : GoodMod P₀ d) :
    (ω k1 d : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / 4) := by
  have hle : ((ω k1 d : ℝ) ^ 4) ≤ (d : ℝ) := by exact_mod_cast ω_pow_four_le hP0 hd
  calc
    (ω k1 d : ℝ) = ((ω k1 d : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    _ ≤ (d : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) 4) hle (by norm_num)

lemma ω_lcm_le_mul {k1 P₀ a b : ℕ} (hk1 : 1 ≤ k1) (ha : GoodMod P₀ a) (hb : GoodMod P₀ b) :
    ω k1 (Nat.lcm a b) ≤ ω k1 a * ω k1 b := by
  simp only [ω, ← pow_add]
  refine Nat.pow_le_pow_right hk1 ?_
  have hsub : (Nat.lcm a b).primeFactors ⊆ a.primeFactors ∪ b.primeFactors := by
    intro p hp
    have hdvd : p ∣ a * b := (Nat.mem_primeFactors.mp hp).2.1.trans (Nat.lcm_dvd_mul a b)
    rw [← Nat.primeFactors_mul ha.1.ne_zero hb.1.ne_zero]
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hdvd, mul_ne_zero ha.1.ne_zero hb.1.ne_zero⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma sum_divisors_eq_sum_powerset {d : ℕ} (hd : Squarefree d) (g : ℕ → ℝ) :
    ∑ k ∈ d.divisors, g k = ∑ t ∈ d.primeFactors.powerset, g (∏ p ∈ t, p) := by
  symm
  refine Finset.sum_bij' (fun t _ => ∏ p ∈ t, p) (fun k _ => k.primeFactors)
    (fun t ht => ?_) (fun k hk => ?_) (fun t ht => ?_) (fun k hk => ?_) (fun _ _ => rfl)
  · rw [Finset.mem_powerset] at ht
    rw [Nat.mem_divisors]
    refine ⟨?_, hd.ne_zero⟩
    calc
      ∏ p ∈ t, p ∣ ∏ p ∈ d.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ ht
      _ = d := Nat.prod_primeFactors_of_squarefree hd
  · rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hk) hd.ne_zero
  · rw [Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  · exact Nat.prod_primeFactors_of_squarefree (hd.squarefree_of_dvd (Nat.dvd_of_mem_divisors hk))

lemma h_val_prod_primes {k1 : ℕ} {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    h_val k1 (∏ p ∈ t, p) = ∏ p ∈ t, ((p : ℝ) - k1) / (k1 : ℝ) := by
  rw [h_val, Nat.primeFactors_prod ht]

lemma sum_h_divisors {k1 P₀ d : ℕ} (hk1 : 1 ≤ k1) (hd : GoodMod P₀ d) :
    ∑ k ∈ d.divisors, h_val k1 k = (d : ℝ) / (ω k1 d : ℝ) := by
  rw [sum_divisors_eq_sum_powerset hd.1]
  have h1 : ∀ t ∈ d.primeFactors.powerset,
      h_val k1 (∏ p ∈ t, p) = ∏ p ∈ t, ((p : ℝ) - k1) / (k1 : ℝ) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    exact h_val_prod_primes fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  rw [Finset.sum_congr rfl h1, ← Finset.prod_one_add]
  have hk0 : (k1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : k1 ≠ 0)
  have h2 : ∏ p ∈ d.primeFactors, (1 + ((p : ℝ) - k1) / (k1 : ℝ)) =
      ∏ p ∈ d.primeFactors, ((p : ℝ) / (k1 : ℝ)) := by
    refine Finset.prod_congr rfl fun p _ => ?_
    field_simp
    ring
  rw [h2, Finset.prod_div_distrib, Finset.prod_const, ω]
  push_cast
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd.1]

lemma sum_inv_h_divisors {k1 P₀ d : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hd : GoodMod P₀ d) :
    ∑ r ∈ d.divisors, (h_val k1 r)⁻¹ = (d : ℝ) / ((ω k1 d : ℝ) * h_val k1 d) := by
  rw [sum_divisors_eq_sum_powerset hd.1]
  have h1 : ∀ t ∈ d.primeFactors.powerset,
      (h_val k1 (∏ p ∈ t, p))⁻¹ = ∏ p ∈ t, (((p : ℝ) - k1) / (k1 : ℝ))⁻¹ := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [h_val_prod_primes fun p hp => Nat.prime_of_mem_primeFactors (ht hp), Finset.prod_inv_distrib]
  rw [Finset.sum_congr rfl h1, ← Finset.prod_one_add]
  have h2 : ∏ p ∈ d.primeFactors, (1 + (((p : ℝ) - k1) / (k1 : ℝ))⁻¹) =
      ∏ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - k1)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_gt : (k1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_le_of_lt hP0 (hd.2 p hp)
    have hk0 : (k1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : k1 ≠ 0)
    have hpk0 : (p : ℝ) - k1 ≠ 0 := sub_ne_zero.mpr hp_gt.ne'
    field_simp
    ring
  rw [h2, Finset.prod_div_distrib]
  have hden : ∏ p ∈ d.primeFactors, ((p : ℝ) - k1) = (ω k1 d : ℝ) * h_val k1 d := by
    rw [h_val, Finset.prod_div_distrib, Finset.prod_const, ω]
    have hk0 : ((k1 : ℝ) ^ d.primeFactors.card) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (by omega : k1 ≠ 0))
    push_cast
    field_simp
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd.1, hden]

/- Block 2B: CRT residue counting for GoodMod d -/

def polyProd {K : ℕ} (c : Fin (K + 1) → ℕ) (n : ℕ) : ℕ :=
  ∏ j : Fin (K + 1), (n - c j)

noncomputable def polyRoots {K : ℕ} (c : Fin (K + 1) → ℕ) (d : ℕ) [NeZero d] : Finset (ZMod d) :=
  Finset.univ.filter (fun r => (∏ j : Fin (K + 1), (r - (c j : ZMod d))) = 0)

lemma card_polyRoots_prime {K P₀ p : ℕ} {c : Fin (K + 1) → ℕ}
    (hc : StrictMono c) (hc_le : ∀ j, c j ≤ P₀) (hp : p.Prime) (hp_gt : P₀ < p) [NeZero p] :
    (polyRoots c p).card = K + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsub : polyRoots c p = Finset.image (fun j : Fin (K + 1) => (c j : ZMod p)) Finset.univ := by
    ext r
    simp only [polyRoots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨j, _, hj⟩
      exact ⟨j, (sub_eq_zero.mp hj).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, Finset.mem_univ j, sub_self _⟩
  rw [hsub, Finset.card_image_of_injective _ ?_, Finset.card_fin]
  have hlt_absurd : ∀ {u v : Fin (K + 1)}, u < v → (c u : ZMod p) = (c v : ZMod p) → False := by
    intro u v hlt huv
    have hclt : c u < c v := hc hlt
    have hcle : c v < p := lt_of_le_of_lt (hc_le v) hp_gt
    have hdvd : p ∣ c v - c u := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (le_of_lt hclt), huv, sub_self]
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hclt) hdvd
    omega
  intro i j hij
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact False.elim (hlt_absurd hlt hij)
  · rfl
  · exact False.elim (hlt_absurd hgt hij.symm)

lemma card_polyRoots {K P₀ d : ℕ} {c : Fin (K + 1) → ℕ}
    (hc : StrictMono c) (hc_le : ∀ j, c j ≤ P₀) (hd : GoodMod P₀ d) [NeZero d] :
    (polyRoots c d).card = ω (K + 1) d := by
  induction hd_card : d.primeFactors.card generalizing d with
  | zero =>
    have hd1 : d = 1 := by
      rw [← Nat.prod_primeFactors_of_squarefree hd.1, Finset.card_eq_zero.mp hd_card, Finset.prod_empty]
    subst hd1
    simp only [ω_one, polyRoots]
    have huniv : Finset.univ.filter (fun r : ZMod 1 => (∏ j : Fin (K + 1), (r - (c j : ZMod 1))) = 0) =
        Finset.univ := by
      ext r
      simp [Subsingleton.elim _ (0 : ZMod 1)]
    rw [huniv, Finset.card_univ, ZMod.card]
  | succ m ih =>
    have hd_ne1 : d ≠ 1 := by
      intro h1
      subst h1
      simp at hd_card
    let p := d.minFac
    have hp : p.Prime := Nat.minFac_prime hd_ne1
    have hpd : p ∣ d := Nat.minFac_dvd d
    set d' := d / p with hd'
    have hmul : p * d' = d := Nat.mul_div_cancel' hpd
    have hd'_good : GoodMod P₀ d' := goodMod_dvd hd (Nat.div_dvd_of_dvd hpd)
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero d' := ⟨hd'_good.1.ne_zero⟩
    have : NeZero (p * d') := ⟨mul_ne_zero hp.ne_zero hd'_good.1.ne_zero⟩
    have hcop : Nat.Coprime p d' := by
      rw [hp.coprime_iff_not_dvd]
      intro hpd'
      have hpp : p * p ∣ d := by
        rw [← hmul]
        exact mul_dvd_mul_left p hpd'
      exact Nat.squarefree_iff_prime_squarefree.mp hd.1 p hp hpp
    have hp_mem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd.1.ne_zero⟩
    have hp_gt : P₀ < p := hd.2 p hp_mem
    have hpf : d.primeFactors = insert p d'.primeFactors := by
      rw [← hmul, Nat.primeFactors_mul hp.ne_zero hd'_good.1.ne_zero, Nat.Prime.primeFactors hp]
      simp
    have hp_not_mem : p ∉ d'.primeFactors := by
      intro hp'
      have hpd' : p ∣ d' := Nat.dvd_of_mem_primeFactors hp'
      exact hp.coprime_iff_not_dvd.mp hcop hpd'
    have hcard_d' : d'.primeFactors.card = m := by
      rw [hpf, Finset.card_insert_of_notMem hp_not_mem] at hd_card
      omega
    have ih_d' := ih hd'_good hcard_d'
    have hroots_p := card_polyRoots_prime hc hc_le hp hp_gt
    let e := ZMod.chineseRemainder hcop
    have hbij : (polyRoots c (p * d')).card = (polyRoots c p ×ˢ polyRoots c d').card := by
      refine Finset.card_bij (fun r _ => e r) (fun r hr => ?_) (fun r₁ _ r₂ _ h => e.injective h)
        (fun ab hab => ?_)
      · simp only [polyRoots, Finset.mem_filter, Finset.mem_product] at hr ⊢
        have he0 : e (∏ j : Fin (K + 1), (r - (c j : ZMod (p * d')))) = 0 := by rw [hr.2, map_zero]
        have he_prod : e (∏ j : Fin (K + 1), (r - (c j : ZMod (p * d')))) =
            (∏ j : Fin (K + 1), ((e r).1 - (c j : ZMod p)),
             ∏ j : Fin (K + 1), ((e r).2 - (c j : ZMod d'))) := by
          rw [map_prod]
          have hc_eq : ∀ j : Fin (K + 1), e (c j : ZMod (p * d')) = ((c j : ZMod p), (c j : ZMod d')) := by
            intro j
            ext <;> simp [map_natCast]
          have h1 : (∏ j : Fin (K + 1), e (r - (c j : ZMod (p * d')))).1 =
              ∏ j : Fin (K + 1), ((e r).1 - (c j : ZMod p)) := by
            rw [Prod.fst_prod]
            refine Finset.prod_congr rfl fun j _ => ?_
            rw [map_sub, hc_eq j, Prod.fst_sub]
          have h2 : (∏ j : Fin (K + 1), e (r - (c j : ZMod (p * d')))).2 =
              ∏ j : Fin (K + 1), ((e r).2 - (c j : ZMod d')) := by
            rw [Prod.snd_prod]
            refine Finset.prod_congr rfl fun j _ => ?_
            rw [map_sub, hc_eq j, Prod.snd_sub]
          exact Prod.ext h1 h2
        rw [he_prod, Prod.mk_eq_zero] at he0
        exact ⟨⟨Finset.mem_univ _, he0.1⟩, ⟨Finset.mem_univ _, he0.2⟩⟩
      · simp only [Finset.mem_product, polyRoots, Finset.mem_filter] at hab ⊢
        refine ⟨e.symm ab, ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply ab⟩
        apply e.injective
        rw [map_zero]
        have hc_eq : ∀ j : Fin (K + 1), e (c j : ZMod (p * d')) = ((c j : ZMod p), (c j : ZMod d')) := by
          intro j
          ext <;> simp [map_natCast]
        have h1 : (e (∏ j : Fin (K + 1), (e.symm ab - (c j : ZMod (p * d'))))).1 = 0 := by
          rw [map_prod, Prod.fst_prod]
          trans ∏ j : Fin (K + 1), (ab.1 - (c j : ZMod p))
          · refine Finset.prod_congr rfl fun j _ => ?_
            rw [map_sub, e.apply_symm_apply ab, hc_eq j, Prod.fst_sub]
          · exact hab.1.2
        have h2 : (e (∏ j : Fin (K + 1), (e.symm ab - (c j : ZMod (p * d'))))).2 = 0 := by
          rw [map_prod, Prod.snd_prod]
          trans ∏ j : Fin (K + 1), (ab.2 - (c j : ZMod d'))
          · refine Finset.prod_congr rfl fun j _ => ?_
            rw [map_sub, e.apply_symm_apply ab, hc_eq j, Prod.snd_sub]
          · exact hab.2.2
        exact Prod.ext h1 h2
    have hω : ω (K + 1) d = (K + 1) * ω (K + 1) d' := by
      simp only [ω, hpf, Finset.card_insert_of_notMem hp_not_mem, pow_succ']
    have hpd_card : (polyRoots c d).card = (polyRoots c (p * d')).card := by
      have helper : ∀ {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂], d₁ = d₂ →
          (polyRoots c d₁).card = (polyRoots c d₂).card := by
        intro d₁ d₂ _ _ heq
        subst heq
        rfl
      exact helper hmul.symm
    rw [hω, hpd_card, hbij, Finset.card_product, hroots_p, ih_d']

lemma zmod_cast_injOn_Ico {a d L : ℕ} (hL : L ≤ d) :
    Set.InjOn (fun n : ℕ => (n : ZMod d)) ↑(Finset.Ico a (a + L)) := by
  have hlt_absurd : ∀ {u v : ℕ}, u ∈ Finset.Ico a (a + L) → v ∈ Finset.Ico a (a + L) →
      (u : ZMod d) = (v : ZMod d) → u < v → False := by
    intro u v hu hv huv hlt
    simp only [Finset.mem_Ico] at hu hv
    have hdvd : d ∣ v - u := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (le_of_lt hlt), huv, sub_self]
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
    omega
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · exact False.elim (hlt_absurd hx hy hxy hlt)
  · rfl
  · exact False.elim (hlt_absurd hy hx hxy.symm hgt)

lemma card_Ico_mod_block {a d : ℕ} (hd : 0 < d) (r : ZMod d) :
    ((Finset.Ico a (a + d)).filter (fun n : ℕ => (n : ZMod d) = r)).card = 1 := by
  have : NeZero d := ⟨hd.ne'⟩
  have himg : (Finset.Ico a (a + d)).image (fun n : ℕ => (n : ZMod d)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (zmod_cast_injOn_Ico le_rfl), Nat.card_Ico, add_tsub_cancel_left]
    exact (ZMod.card d).symm
  have hr_mem : r ∈ (Finset.Ico a (a + d)).image (fun n : ℕ => (n : ZMod d)) := by
    rw [himg]; exact Finset.mem_univ r
  rw [Finset.mem_image] at hr_mem
  rcases hr_mem with ⟨n₀, hn₀, rfl⟩
  have hfilt : (Finset.Ico a (a + d)).filter (fun n : ℕ => (n : ZMod d) = (n₀ : ZMod d)) = {n₀} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, heq⟩
      exact zmod_cast_injOn_Ico le_rfl hn hn₀ heq
    · rintro rfl
      exact ⟨hn₀, rfl⟩
  rw [hfilt, Finset.card_singleton]

lemma card_Ico_mod_le_one {a d L : ℕ} (hL : L ≤ d) (r : ZMod d) :
    ((Finset.Ico a (a + L)).filter (fun n : ℕ => (n : ZMod d) = r)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter] at hx hy
  exact zmod_cast_injOn_Ico hL hx.1 hy.1 (hx.2.trans hy.2.symm)

lemma card_Ico_mod_bounds {A d L : ℕ} (hd : 0 < d) (r : ZMod d) :
    L / d ≤ ((Finset.Ico A (A + L)).filter (fun n : ℕ => (n : ZMod d) = r)).card ∧
      ((Finset.Ico A (A + L)).filter (fun n : ℕ => (n : ZMod d) = r)).card ≤ L / d + 1 := by
  have hblocks : ∀ q a : ℕ,
      ((Finset.Ico a (a + q * d)).filter (fun n : ℕ => (n : ZMod d) = r)).card = q := by
    intro q
    induction q with
    | zero => intro a; simp
    | succ q ih =>
      intro a
      have hsplit : Finset.Ico a (a + (q + 1) * d) =
          Finset.Ico a (a + q * d) ∪ Finset.Ico (a + q * d) (a + q * d + d) := by
        ext n
        simp only [Finset.mem_Ico, Finset.mem_union]
        have : (q + 1) * d = q * d + d := by ring
        omega
      have hdisj : Disjoint (Finset.Ico a (a + q * d)) (Finset.Ico (a + q * d) (a + q * d + d)) :=
        Finset.Ico_disjoint_Ico_consecutive a (a + q * d) (a + q * d + d)
      rw [hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        ih a, card_Ico_mod_block hd r]
  set q := L / d
  set rem := L % d
  have hrem_lt : rem < d := Nat.mod_lt L hd
  have hL_eq : L = q * d + rem := (Nat.div_add_mod L d).symm.trans (by ring)
  have hsplit : Finset.Ico A (A + L) =
      Finset.Ico A (A + q * d) ∪ Finset.Ico (A + q * d) (A + q * d + rem) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Ico A (A + q * d)) (Finset.Ico (A + q * d) (A + q * d + rem)) :=
    Finset.Ico_disjoint_Ico_consecutive A (A + q * d) (A + q * d + rem)
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    hblocks q A]
  have htail := card_Ico_mod_le_one (le_of_lt hrem_lt) r (a := A + q * d)
  omega

lemma count_polyProd_dvd {K P₀ A d L : ℕ} {c : Fin (K + 1) → ℕ}
    (hc : StrictMono c) (hc_le : ∀ j, c j ≤ P₀) (hA : P₀ ≤ A) (hd : GoodMod P₀ d) :
    |(((Finset.Ico A (A + L)).filter (fun n => d ∣ polyProd c n)).card : ℝ) -
      ((ω (K + 1) d : ℝ) / (d : ℝ)) * (L : ℝ)| ≤ (ω (K + 1) d : ℝ) := by
  have hd_pos := goodMod_pos hd
  have : NeZero d := ⟨hd_pos.ne'⟩
  have hfilt : (Finset.Ico A (A + L)).filter (fun n : ℕ => d ∣ polyProd c n) =
      (polyRoots c d).biUnion (fun r => (Finset.Ico A (A + L)).filter (fun n : ℕ => (n : ZMod d) = r)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_biUnion, polyRoots, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hn, hdvd⟩
      refine ⟨(n : ZMod d), ?_, hn, rfl⟩
      rw [← ZMod.natCast_eq_zero_iff] at hdvd
      have hcast : ((polyProd c n : ℕ) : ZMod d) =
          ∏ j : Fin (K + 1), ((n : ZMod d) - (c j : ZMod d)) := by
        simp only [polyProd, Nat.cast_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Nat.cast_sub ((hc_le j).trans (hA.trans hn.1))]
      exact hcast ▸ hdvd
    · rintro ⟨r, hr, hn, rfl⟩
      refine ⟨hn, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      have hcast : ((polyProd c n : ℕ) : ZMod d) =
          ∏ j : Fin (K + 1), ((n : ZMod d) - (c j : ZMod d)) := by
        simp only [polyProd, Nat.cast_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Nat.cast_sub ((hc_le j).trans (hA.trans hn.1))]
      exact hcast.trans hr
  have hdisj : Set.PairwiseDisjoint (polyRoots c d : Set (ZMod d))
      (fun r => (Finset.Ico A (A + L)).filter (fun n : ℕ => (n : ZMod d) = r)) := by
    intro r₁ _ r₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    simp only [Finset.mem_filter] at hn₁ hn₂
    exact hne (hn₁.2.symm.trans hn₂.2)
  rw [hfilt, Finset.card_biUnion hdisj, Nat.cast_sum]
  have hsum_target : ((ω (K + 1) d : ℝ) / (d : ℝ)) * (L : ℝ) =
      ∑ _r ∈ polyRoots c d, (L : ℝ) / (d : ℝ) := by
    rw [Finset.sum_const, card_polyRoots hc hc_le hd, nsmul_eq_mul]
    ring
  rw [hsum_target, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ r ∈ polyRoots c d, |(((Finset.Ico A (A + L)).filter (fun n : ℕ => (n : ZMod d) = r)).card : ℝ) -
        (L : ℝ) / (d : ℝ)|
      ≤ ∑ _r ∈ polyRoots c d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun r _ => ?_
        obtain ⟨hlb, hub⟩ := card_Ico_mod_bounds hd_pos r (A := A) (L := L)
        have h1 : (L : ℝ) / (d : ℝ) - 1 ≤ (L / d : ℕ) := by
          have hq : (L : ℝ) < ((L / d : ℕ) + 1) * (d : ℝ) := by
            have := Nat.div_add_mod L d
            have := Nat.mod_lt L hd_pos
            exact_mod_cast (by nlinarith : L < (L / d + 1) * d)
          have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
          linarith [(div_lt_iff₀ hd_r).mpr hq]
        have h2 : ((L / d : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) := by
          have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
          rw [le_div_iff₀ hd_r]
          exact_mod_cast Nat.div_mul_le_self L d
        have hlb_r : ((L / d : ℕ) : ℝ) ≤
            (((Finset.Ico A (A + L)).filter (fun n : ℕ => (n : ZMod d) = r)).card : ℝ) := by
          exact_mod_cast hlb
        have hub_r : (((Finset.Ico A (A + L)).filter (fun n : ℕ => (n : ZMod d) = r)).card : ℝ) ≤
            (L / d : ℕ) + 1 := by
          exact_mod_cast hub
        rw [abs_le]
        constructor <;> linarith
    _ = (ω (K + 1) d : ℝ) := by
        rw [Finset.sum_const, card_polyRoots hc hc_le hd, nsmul_eq_mul, mul_one]

/- Block 2C: Selberg sieve weights, diagonalization, and upper bound -/

noncomputable def lam (k1 P₀ R d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) / G_val k1 P₀ R *
    ((d : ℝ) / ((ω k1 d : ℝ) * h_val k1 d)) *
    ∑ m ∈ (Finset.Icc 1 (R / d)).filter (fun m => GoodMod P₀ m ∧ Nat.Coprime m d), (h_val k1 m)⁻¹

lemma lam_one {k1 P₀ R : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hR : 1 ≤ R) :
    lam k1 P₀ R 1 = 1 := by
  have hG : 0 < G_val k1 P₀ R := lt_of_lt_of_le zero_lt_one (G_val_ge_one hk1 hP0 hR)
  have hfilt : (Finset.Icc 1 (R / 1)).filter (fun m => GoodMod P₀ m ∧ Nat.Coprime m 1) = S_R P₀ R := by
    ext m
    simp [S_R]
  rw [lam, hfilt, ArithmeticFunction.moebius_apply_one, ω_one, h_val_one]
  simp only [Int.cast_one, Nat.cast_one, mul_one, div_one]
  change (1 : ℝ) / G_val k1 P₀ R * G_val k1 P₀ R = 1
  field_simp

lemma gcd_mul_eq_left_of_dvd_of_coprime {r m d : ℕ} (hrd : r ∣ d) (hm : Nat.Coprime m d) :
    Nat.gcd (r * m) d = r := by
  apply Nat.dvd_antisymm
  · have hcop_md : Nat.Coprime (Nat.gcd (r * m) d) m :=
      (Nat.coprime_comm.mp hm).coprime_dvd_left (Nat.gcd_dvd_right _ _)
    have hdvd_rm : Nat.gcd (r * m) d ∣ r * m := Nat.gcd_dvd_left _ _
    exact hcop_md.dvd_of_dvd_mul_right hdvd_rm
  · exact Nat.dvd_gcd (dvd_mul_right r m) hrd

lemma abs_lam_le_one {k1 P₀ R d : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hR : 1 ≤ R)
    (hd : d ∈ S_R P₀ R) : |lam k1 P₀ R d| ≤ 1 := by
  have hG : 0 < G_val k1 P₀ R := lt_of_lt_of_le zero_lt_one (G_val_ge_one hk1 hP0 hR)
  simp only [S_R, Finset.mem_filter, Finset.mem_Icc] at hd
  rcases hd with ⟨⟨hd1, hdR⟩, hd_good⟩
  set M_d := (Finset.Icc 1 (R / d)).filter (fun m => GoodMod P₀ m ∧ Nat.Coprime m d)
  have hsum_inv := sum_inv_h_divisors hk1 hP0 hd_good
  have hprod_sum : ((d : ℝ) / ((ω k1 d : ℝ) * h_val k1 d)) * ∑ m ∈ M_d, (h_val k1 m)⁻¹ =
      ∑ rm ∈ d.divisors ×ˢ M_d, (h_val k1 (rm.1 * rm.2))⁻¹ := by
    rw [← hsum_inv, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun m hm => ?_
    have hrd : r ∣ d := Nat.dvd_of_mem_divisors hr
    have hr0 : r ≠ 0 := (Nat.pos_of_mem_divisors hr).ne'
    simp only [M_d, Finset.mem_filter, Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    have hcop : Nat.Coprime r m := (hm.2.2.coprime_dvd_right hrd).symm
    rw [h_val_mul_coprime hr0 hm0 hcop, mul_inv]
  have hle_G : ∑ rm ∈ d.divisors ×ˢ M_d, (h_val k1 (rm.1 * rm.2))⁻¹ ≤ G_val k1 P₀ R := by
    rw [G_val]
    have hinj : Set.InjOn (fun rm : ℕ × ℕ => rm.1 * rm.2) ↑(d.divisors ×ˢ M_d) := by
      intro rm₁ hrm₁ rm₂ hrm₂ heq
      simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors, M_d, Finset.mem_filter,
        Finset.mem_Icc] at hrm₁ hrm₂
      have hr1 : rm₁.1 = Nat.gcd (rm₁.1 * rm₁.2) d :=
        (gcd_mul_eq_left_of_dvd_of_coprime hrm₁.1.1 hrm₁.2.2.2).symm
      have hr2 : rm₂.1 = Nat.gcd (rm₂.1 * rm₂.2) d :=
        (gcd_mul_eq_left_of_dvd_of_coprime hrm₂.1.1 hrm₂.2.2.2).symm
      have hfst : rm₁.1 = rm₂.1 := by
        dsimp only at heq
        rw [hr1, hr2, heq]
      have hr1_pos : 0 < rm₁.1 := Nat.pos_of_dvd_of_pos hrm₁.1.1 (goodMod_pos hd_good)
      have heq' : rm₁.1 * rm₁.2 = rm₂.1 * rm₂.2 := heq
      have hsnd : rm₁.2 = rm₂.2 := mul_left_cancel₀ hr1_pos.ne' (hfst ▸ heq')
      exact Prod.ext hfst hsnd
    have himg : (d.divisors ×ˢ M_d).image (fun rm : ℕ × ℕ => rm.1 * rm.2) ⊆ S_R P₀ R := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨rm, hrm, rfl⟩
      simp only [Finset.mem_product, Nat.mem_divisors, M_d, Finset.mem_filter, Finset.mem_Icc] at hrm
      rcases hrm with ⟨⟨hrd, _⟩, ⟨⟨hm1, hmR⟩, hm_good, hm_cop⟩⟩
      have hr0 : 0 < rm.1 := Nat.pos_of_dvd_of_pos hrd (goodMod_pos hd_good)
      have hrle : rm.1 ≤ d := Nat.le_of_dvd (by omega) hrd
      have hrm_le : rm.1 * rm.2 ≤ R := (Nat.mul_le_mul hrle hmR).trans (Nat.mul_div_le R d)
      have hrm_good : GoodMod P₀ (rm.1 * rm.2) :=
        goodMod_mul (goodMod_dvd hd_good hrd) hm_good (hm_cop.coprime_dvd_right hrd).symm
      simp only [S_R, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.mul_pos hr0 hm1, hrm_le⟩, hrm_good⟩
    calc
      ∑ rm ∈ d.divisors ×ˢ M_d, (h_val k1 (rm.1 * rm.2))⁻¹
        = ∑ x ∈ (d.divisors ×ˢ M_d).image (fun rm : ℕ × ℕ => rm.1 * rm.2), (h_val k1 x)⁻¹ :=
            (Finset.sum_image (f := fun x => (h_val k1 x)⁻¹) (g := fun rm : ℕ × ℕ => rm.1 * rm.2)
              hinj).symm
      _ ≤ ∑ x ∈ S_R P₀ R, (h_val k1 x)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg himg fun n hn _ => by
              simp only [S_R, Finset.mem_filter] at hn
              exact inv_nonneg.mpr (le_of_lt (h_val_pos hk1 hP0 hn.2))
  have hprod_nonneg : 0 ≤ ((d : ℝ) / ((ω k1 d : ℝ) * h_val k1 d)) * ∑ m ∈ M_d, (h_val k1 m)⁻¹ := by
    rw [hprod_sum]
    refine Finset.sum_nonneg fun rm hrm => ?_
    simp only [Finset.mem_product, M_d, Finset.mem_filter] at hrm
    have hr_good := goodMod_dvd hd_good (Nat.dvd_of_mem_divisors hrm.1)
    have hcop := (hrm.2.2.2.coprime_dvd_right (Nat.dvd_of_mem_divisors hrm.1)).symm
    exact inv_nonneg.mpr (le_of_lt (h_val_pos hk1 hP0 (goodMod_mul hr_good hrm.2.2.1 hcop)))
  rw [lam, mul_assoc ((ArithmeticFunction.moebius d : ℝ) / G_val k1 P₀ R),
    abs_mul, abs_div, abs_of_pos hG, abs_of_nonneg hprod_nonneg]
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have : |ArithmeticFunction.moebius d| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    exact_mod_cast this
  calc
    |(ArithmeticFunction.moebius d : ℝ)| / G_val k1 P₀ R *
        (((d : ℝ) / ((ω k1 d : ℝ) * h_val k1 d)) * ∑ m ∈ M_d, (h_val k1 m)⁻¹)
      ≤ 1 / G_val k1 P₀ R * G_val k1 P₀ R := by
        refine mul_le_mul (div_le_div_of_nonneg_right hmu hG.le) (hprod_sum ▸ hle_G) hprod_nonneg
          (div_nonneg zero_le_one hG.le)
    _ = 1 := by field_simp

lemma sum_moebius_divisors_eq_ite {n : ℕ} (_hn : 0 < n) :
    ∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℝ) = if n = 1 then 1 else 0 := by
  have hZ : ∑ r ∈ n.divisors, ArithmeticFunction.moebius r = if n = 1 then 1 else 0 := by
    have hmul := ArithmeticFunction.ext_iff.mp ArithmeticFunction.moebius_mul_coe_zeta n
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmul
    exact hmul
  have hcast : (∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℝ)) =
      ((∑ r ∈ n.divisors, ArithmeticFunction.moebius r : ℤ) : ℝ) := by
    push_cast; rfl
  rw [hcast, hZ]
  split_ifs <;> simp

lemma selberg_linear_form {k1 P₀ R k : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hR : 1 ≤ R)
    (hk : k ∈ S_R P₀ R) :
    ∑ d ∈ (S_R P₀ R).filter (fun d => k ∣ d), ((ω k1 d : ℝ) / (d : ℝ)) * lam k1 P₀ R d =
      (ArithmeticFunction.moebius k : ℝ) / (h_val k1 k * G_val k1 P₀ R) := by
  have hG : 0 < G_val k1 P₀ R := lt_of_lt_of_le zero_lt_one (G_val_ge_one hk1 hP0 hR)
  simp only [S_R, Finset.mem_filter, Finset.mem_Icc] at hk
  rcases hk with ⟨⟨hk1_pos, hkR⟩, hk_good⟩
  have hhk : 0 < h_val k1 k := h_val_pos hk1 hP0 hk_good
  set M_k := (Finset.Icc 1 (R / k)).filter (fun r => GoodMod P₀ r ∧ Nat.Coprime r k)
  have hbij_d : ∑ d ∈ (S_R P₀ R).filter (fun d => k ∣ d), ((ω k1 d : ℝ) / (d : ℝ)) * lam k1 P₀ R d =
      ∑ r ∈ M_k, ((ω k1 (k * r) : ℝ) / (k * r : ℝ)) * lam k1 P₀ R (k * r) := by
    refine Finset.sum_bij (fun d _ => d / k) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, S_R, Finset.mem_Icc] at hd
      rcases hd with ⟨⟨⟨hd1, hdR⟩, hd_good⟩, hkd⟩
      have hr0 : 0 < d / k := Nat.div_pos (Nat.le_of_dvd hd1 hkd) hk1_pos
      have hr_le : d / k ≤ R / k := Nat.div_le_div_right hdR
      have hr_good : GoodMod P₀ (d / k) := goodMod_dvd hd_good (Nat.div_dvd_of_dvd hkd)
      have hcop : Nat.Coprime (d / k) k := by
        have hkm : k * (d / k) = d := Nat.mul_div_cancel' hkd
        have := Nat.squarefree_mul_iff.mp (hkm ▸ hd_good.1)
        exact this.1.symm
      simp only [M_k, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hr0, hr_le⟩, hr_good, hcop⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      simp only [Finset.mem_filter] at hd₁ hd₂
      rw [← Nat.mul_div_cancel' hd₁.2, ← Nat.mul_div_cancel' hd₂.2, heq]
    · intro r hr
      simp only [M_k, Finset.mem_filter, Finset.mem_Icc] at hr
      rcases hr with ⟨⟨hr1, hr_le⟩, hr_good, hr_cop⟩
      refine ⟨k * r, ?_, Nat.mul_div_cancel_left r hk1_pos⟩
      simp only [Finset.mem_filter, S_R, Finset.mem_Icc]
      refine ⟨⟨⟨Nat.mul_pos hk1_pos hr1, ?_⟩, goodMod_mul hk_good hr_good hr_cop.symm⟩, dvd_mul_right k r⟩
      calc
        k * r ≤ k * (R / k) := Nat.mul_le_mul_left k hr_le
        _ ≤ R := Nat.mul_div_le R k
    · intro d hd
      simp only [Finset.mem_filter] at hd
      have hdk : k * (d / k) = d := Nat.mul_div_cancel' hd.2
      conv_lhs => rw [← hdk]
      rw [Nat.cast_mul]
  rw [hbij_d]
  have hterm : ∀ r ∈ M_k, ((ω k1 (k * r) : ℝ) / (k * r : ℝ)) * lam k1 P₀ R (k * r) =
      ((ArithmeticFunction.moebius k : ℝ) / (h_val k1 k * G_val k1 P₀ R)) *
        ((ArithmeticFunction.moebius r : ℝ) * (h_val k1 r)⁻¹ *
          ∑ m ∈ (Finset.Icc 1 ((R / k) / r)).filter (fun m => GoodMod P₀ m ∧ Nat.Coprime m (k * r)),
            (h_val k1 m)⁻¹) := by
    intro r hr
    simp only [M_k, Finset.mem_filter, Finset.mem_Icc] at hr
    rcases hr with ⟨⟨hr1, _⟩, hr_good, hr_cop⟩
    have hkr_good := goodMod_mul hk_good hr_good hr_cop.symm
    have hω_pos : (0 : ℝ) < (ω k1 (k * r) : ℝ) := by
      simp only [ω]; positivity
    have hkr_pos : (0 : ℝ) < ((k * r : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hk1_pos hr1
    have hh_pos : 0 < h_val k1 (k * r) := h_val_pos hk1 hP0 hkr_good
    have hmu : ArithmeticFunction.moebius (k * r) =
        ArithmeticFunction.moebius k * ArithmeticFunction.moebius r :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hr_cop.symm
    have hh_mul : h_val k1 (k * r) = h_val k1 k * h_val k1 r :=
      h_val_mul_coprime hk_good.1.ne_zero hr_good.1.ne_zero hr_cop.symm
    rw [lam]
    conv_rhs => rw [Nat.div_div_eq_div_mul]
    push_cast [hmu, hh_mul]
    have hk_ne : ((k * r : ℕ) : ℝ) ≠ 0 := hkr_pos.ne'
    have hω_ne : (ω k1 (k * r) : ℝ) ≠ 0 := hω_pos.ne'
    have hhk_ne : h_val k1 k ≠ 0 := hhk.ne'
    have hhr_ne : h_val k1 r ≠ 0 := (h_val_pos hk1 hP0 hr_good).ne'
    have hG_ne : G_val k1 P₀ R ≠ 0 := hG.ne'
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hdouble : ∑ r ∈ M_k, ((ArithmeticFunction.moebius r : ℝ) * (h_val k1 r)⁻¹ *
        ∑ m ∈ (Finset.Icc 1 ((R / k) / r)).filter (fun m => GoodMod P₀ m ∧ Nat.Coprime m (k * r)),
          (h_val k1 m)⁻¹) =
      ∑ n ∈ M_k, (h_val k1 n)⁻¹ * ∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℝ) := by
    have hL : ∑ r ∈ M_k, ((ArithmeticFunction.moebius r : ℝ) * (h_val k1 r)⁻¹ *
          ∑ m ∈ (Finset.Icc 1 ((R / k) / r)).filter (fun m => GoodMod P₀ m ∧ Nat.Coprime m (k * r)),
            (h_val k1 m)⁻¹) =
        ∑ r ∈ M_k, ∑ m ∈ (Finset.Icc 1 ((R / k) / r)).filter (fun m => GoodMod P₀ m ∧ Nat.Coprime m (k * r)),
          (ArithmeticFunction.moebius r : ℝ) * (h_val k1 (r * m))⁻¹ := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [M_k, Finset.mem_filter, Finset.mem_Icc] at hr hm
      have hcop_rm : Nat.Coprime r m := hm.2.2.coprime_dvd_right (dvd_mul_left r k) |>.symm
      rw [h_val_mul_coprime hr.2.1.1.ne_zero hm.2.1.1.ne_zero hcop_rm, mul_inv]
      ring
    have hR_sum : ∑ n ∈ M_k, (h_val k1 n)⁻¹ * ∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℝ) =
        ∑ n ∈ M_k, ∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℝ) * (h_val k1 n)⁻¹ := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => mul_comm _ _
    rw [hL, hR_sum, Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, M_k, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      rcases hp with ⟨⟨⟨hr1, _⟩, hr_good, hr_cop⟩, ⟨⟨hm1, hm_le⟩, hm_good, hm_cop⟩⟩
      have hcop_rm : Nat.Coprime p.1 p.2 := hm_cop.coprime_dvd_right (dvd_mul_left p.1 k) |>.symm
      have hle : p.1 * p.2 ≤ R / k := (Nat.mul_le_mul_left p.1 hm_le).trans (Nat.mul_div_le (R / k) p.1)
      have hn_good := goodMod_mul hr_good hm_good hcop_rm
      have hcop_nk : Nat.Coprime (p.1 * p.2) k := hr_cop.mul_left (hm_cop.coprime_dvd_right (dvd_mul_right k p.1))
      refine ⟨⟨⟨Nat.mul_pos hr1 hm1, hle⟩, hn_good, hcop_nk⟩, ?_⟩
      exact Nat.mem_divisors.mpr ⟨dvd_mul_right p.1 p.2, hn_good.1.ne_zero⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      rcases p₁ with ⟨r₁, m₁⟩
      rcases p₂ with ⟨r₂, m₂⟩
      simp only [Finset.mem_sigma, M_k, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
      have hfst : r₁ * m₁ = r₂ * m₂ := congr_arg Sigma.fst heq
      have hsnd : r₁ = r₂ := by simpa using congr_arg Sigma.snd heq
      have hr1 : r₁ ≠ 0 := by omega
      have hm : m₁ = m₂ := mul_left_cancel₀ hr1 (hsnd ▸ hfst)
      subst hsnd hm
      rfl
    · intro q hq
      rcases q with ⟨n, r⟩
      simp only [Finset.mem_sigma, M_k, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors] at hq
      rcases hq with ⟨⟨⟨hn1, hn_le⟩, hn_good, hn_cop⟩, ⟨hrn, _⟩⟩
      have hr_pos : 0 < r := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hrn, hn_good.1.ne_zero⟩)
      have hr_le : r ≤ R / k := (Nat.le_of_dvd hn1 hrn).trans hn_le
      have hm_eq : r * (n / r) = n := Nat.mul_div_cancel' hrn
      have hm_pos : 0 < n / r := Nat.div_pos (Nat.le_of_dvd hn1 hrn) hr_pos
      have hm_le : n / r ≤ (R / k) / r := Nat.div_le_div_right hn_le
      have hr_good : GoodMod P₀ r := goodMod_dvd hn_good hrn
      have hm_good : GoodMod P₀ (n / r) := goodMod_dvd hn_good (Nat.div_dvd_of_dvd hrn)
      have hcop_rk : Nat.Coprime r k := hn_cop.coprime_dvd_left hrn
      have hcop_mk : Nat.Coprime (n / r) k := hn_cop.coprime_dvd_left (Nat.div_dvd_of_dvd hrn)
      have hcop_rm : Nat.Coprime r (n / r) := (Nat.squarefree_mul_iff.mp (hm_eq.symm ▸ hn_good.1)).1
      refine ⟨⟨r, n / r⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, M_k, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨⟨hr_pos, hr_le⟩, hr_good, hcop_rk⟩, ⟨⟨hm_pos, hm_le⟩, hm_good, hcop_mk.mul_right hcop_rm.symm⟩⟩
      · simp only [Sigma.mk.inj_iff]
        exact ⟨hm_eq, HEq.rfl⟩
    · intro p _; rfl
  have hsum1 : ∑ n ∈ M_k, (h_val k1 n)⁻¹ * ∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℝ) = 1 := by
    have h1_mem : 1 ∈ M_k := by
      simp only [M_k, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, Nat.div_pos hkR hk1_pos⟩, goodMod_one P₀, Nat.coprime_one_left k⟩
    rw [Finset.sum_eq_single 1]
    · simp [h_val_one]
    · intro n hn hn1
      simp only [M_k, Finset.mem_filter, Finset.mem_Icc] at hn
      rw [sum_moebius_divisors_eq_ite hn.1.1, if_neg hn1, mul_zero]
    · intro h; exact absurd h1_mem h
  rw [hdouble, hsum1, mul_one]

lemma ω_lcm_mul_gcd {k1 P₀ a b : ℕ} (ha : GoodMod P₀ a) (hb : GoodMod P₀ b) :
    ω k1 (Nat.lcm a b) * ω k1 (Nat.gcd a b) = ω k1 a * ω k1 b := by
  simp only [ω, ← pow_add]
  congr 1
  have hlcm_pf : (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_union]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      have h1 : p ∣ a * b := hdvd.trans (Nat.lcm_dvd_mul a b)
      rcases hp.dvd_mul.mp h1 with hpa | hpb
      · exact Or.inl ⟨hp, hpa, ha.1.ne_zero⟩
      · exact Or.inr ⟨hp, hpb, hb.1.ne_zero⟩
    · rintro (⟨hp, hpa, _⟩ | ⟨hp, hpb, _⟩)
      · exact ⟨hp, hpa.trans (Nat.dvd_lcm_left a b), Nat.lcm_ne_zero ha.1.ne_zero hb.1.ne_zero⟩
      · exact ⟨hp, hpb.trans (Nat.dvd_lcm_right a b), Nat.lcm_ne_zero ha.1.ne_zero hb.1.ne_zero⟩
  have hgcd_pf : (Nat.gcd a b).primeFactors = a.primeFactors ∩ b.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_inter]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      exact ⟨⟨hp, hdvd.trans (Nat.gcd_dvd_left a b), ha.1.ne_zero⟩,
             ⟨hp, hdvd.trans (Nat.gcd_dvd_right a b), hb.1.ne_zero⟩⟩
    · rintro ⟨⟨hp, hpa, _⟩, ⟨_, hpb, _⟩⟩
      exact ⟨hp, Nat.dvd_gcd hpa hpb, (Nat.gcd_ne_zero_left ha.1.ne_zero)⟩
  rw [hlcm_pf, hgcd_pf, Finset.card_union_add_card_inter]

lemma selberg_main_identity {k1 P₀ R : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hR : 1 ≤ R) :
    ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
      lam k1 P₀ R d₁ * lam k1 P₀ R d₂ * ((ω k1 (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) =
      (G_val k1 P₀ R)⁻¹ := by
  have hG : 0 < G_val k1 P₀ R := lt_of_lt_of_le zero_lt_one (G_val_ge_one hk1 hP0 hR)
  have hterm : ∀ d₁ ∈ S_R P₀ R, ∀ d₂ ∈ S_R P₀ R,
      lam k1 P₀ R d₁ * lam k1 P₀ R d₂ * ((ω k1 (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) =
      ∑ k ∈ S_R P₀ R, if k ∣ d₁ ∧ k ∣ d₂ then
        h_val k1 k * (((ω k1 d₁ : ℝ) / (d₁ : ℝ)) * lam k1 P₀ R d₁) *
          (((ω k1 d₂ : ℝ) / (d₂ : ℝ)) * lam k1 P₀ R d₂) else 0 := by
    intro d₁ hd₁ d₂ hd₂
    simp only [S_R, Finset.mem_filter, Finset.mem_Icc] at hd₁ hd₂
    rcases hd₁ with ⟨⟨hd1_pos, hd1_le⟩, hd1_good⟩
    rcases hd₂ with ⟨⟨hd2_pos, _⟩, hd2_good⟩
    set g := Nat.gcd d₁ d₂
    have hg_good : GoodMod P₀ g := goodMod_dvd hd1_good (Nat.gcd_dvd_left d₁ d₂)
    have hmul_lcm : (Nat.lcm d₁ d₂ : ℝ) * (g : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by
      exact_mod_cast Nat.lcm_mul_gcd d₁ d₂
    have hω_lcm : (ω k1 (Nat.lcm d₁ d₂) : ℝ) * (ω k1 g : ℝ) = (ω k1 d₁ : ℝ) * (ω k1 d₂ : ℝ) := by
      exact_mod_cast ω_lcm_mul_gcd hd1_good hd2_good
    have hlcm_ne : (Nat.lcm d₁ d₂ : ℝ) ≠ 0 := by
      exact_mod_cast Nat.lcm_ne_zero hd1_good.1.ne_zero hd2_good.1.ne_zero
    have hg_ne : (g : ℝ) ≠ 0 := by exact_mod_cast (goodMod_pos hg_good).ne'
    have hωg_ne : (ω k1 g : ℝ) ≠ 0 := by simp only [ω]; positivity
    have hd1_ne : (d₁ : ℝ) ≠ 0 := by exact_mod_cast hd1_good.1.ne_zero
    have hd2_ne : (d₂ : ℝ) ≠ 0 := by exact_mod_cast hd2_good.1.ne_zero
    have hratio : (ω k1 (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ) =
        ((ω k1 d₁ : ℝ) / (d₁ : ℝ)) * ((ω k1 d₂ : ℝ) / (d₂ : ℝ)) * ∑ k ∈ g.divisors, h_val k1 k := by
      rw [sum_h_divisors hk1 hg_good]
      have hlcm_eq : (Nat.lcm d₁ d₂ : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) / (g : ℝ) := by
        field_simp [hg_ne]
        linarith
      have hω_eq : (ω k1 (Nat.lcm d₁ d₂) : ℝ) = (ω k1 d₁ : ℝ) * (ω k1 d₂ : ℝ) / (ω k1 g : ℝ) := by
        field_simp [hωg_ne]
        linarith
      rw [hlcm_eq, hω_eq]
      field_simp
    rw [hratio]
    have hsub : g.divisors ⊆ S_R P₀ R := by
      intro k hk
      simp only [Nat.mem_divisors] at hk
      have hkd1 : k ∣ d₁ := hk.1.trans (Nat.gcd_dvd_left d₁ d₂)
      have hk_good := goodMod_dvd hd1_good hkd1
      have hk_pos := goodMod_pos hk_good
      have hk_le : k ≤ R := (Nat.le_of_dvd hd1_pos hkd1).trans hd1_le
      simp only [S_R, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hk_pos, hk_le⟩, hk_good⟩
    have hdiv_sum : ∑ k ∈ g.divisors, h_val k1 k =
        ∑ k ∈ S_R P₀ R, if k ∣ d₁ ∧ k ∣ d₂ then h_val k1 k else 0 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · intro ⟨hkd, _⟩
        exact ⟨hsub (Nat.mem_divisors.mpr ⟨hkd, hg_good.1.ne_zero⟩), Nat.dvd_gcd_iff.mp hkd⟩
      · intro ⟨_, hk12⟩
        exact ⟨Nat.dvd_gcd_iff.mpr hk12, hg_good.1.ne_zero⟩
    rw [hdiv_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  calc
    ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
        lam k1 P₀ R d₁ * lam k1 P₀ R d₂ * ((ω k1 (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ))
      = ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R, ∑ k ∈ S_R P₀ R,
          if k ∣ d₁ ∧ k ∣ d₂ then
            h_val k1 k * (((ω k1 d₁ : ℝ) / (d₁ : ℝ)) * lam k1 P₀ R d₁) *
              (((ω k1 d₂ : ℝ) / (d₂ : ℝ)) * lam k1 P₀ R d₂) else 0 :=
        Finset.sum_congr rfl fun d₁ hd1 => Finset.sum_congr rfl fun d₂ hd2 => hterm d₁ hd1 d₂ hd2
    _ = ∑ k ∈ S_R P₀ R, h_val k1 k *
          (∑ d ∈ (S_R P₀ R).filter (fun d => k ∣ d), ((ω k1 d : ℝ) / (d : ℝ)) * lam k1 P₀ R d) ^ 2 := by
        have hswap1 : ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R, ∑ k ∈ S_R P₀ R,
              (if k ∣ d₁ ∧ k ∣ d₂ then
                h_val k1 k * (((ω k1 d₁ : ℝ) / (d₁ : ℝ)) * lam k1 P₀ R d₁) *
                  (((ω k1 d₂ : ℝ) / (d₂ : ℝ)) * lam k1 P₀ R d₂) else 0) =
            ∑ k ∈ S_R P₀ R, ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
              if k ∣ d₁ ∧ k ∣ d₂ then
                h_val k1 k * (((ω k1 d₁ : ℝ) / (d₁ : ℝ)) * lam k1 P₀ R d₁) *
                  (((ω k1 d₂ : ℝ) / (d₂ : ℝ)) * lam k1 P₀ R d₂) else 0 := by
          trans ∑ d₁ ∈ S_R P₀ R, ∑ k ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
              if k ∣ d₁ ∧ k ∣ d₂ then
                h_val k1 k * (((ω k1 d₁ : ℝ) / (d₁ : ℝ)) * lam k1 P₀ R d₁) *
                  (((ω k1 d₂ : ℝ) / (d₂ : ℝ)) * lam k1 P₀ R d₂) else 0
          · refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
          · exact Finset.sum_comm
        rw [hswap1]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sq, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        by_cases h1 : k ∣ d₁ <;> by_cases h2 : k ∣ d₂ <;> (simp [h1, h2]; try ring)
    _ = ∑ k ∈ S_R P₀ R, h_val k1 k * ((ArithmeticFunction.moebius k : ℝ) / (h_val k1 k * G_val k1 P₀ R)) ^ 2 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [selberg_linear_form hk1 hP0 hR hk]
    _ = ∑ k ∈ S_R P₀ R, (G_val k1 P₀ R)⁻¹ ^ 2 * (h_val k1 k)⁻¹ := by
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [S_R, Finset.mem_filter] at hk
        have hhk : h_val k1 k ≠ 0 := (h_val_pos hk1 hP0 hk.2).ne'
        have hmu2 : (ArithmeticFunction.moebius k : ℝ) ^ 2 = 1 := by
          have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hk.2.1
          exact_mod_cast this
        rw [div_pow, mul_pow, hmu2]
        field_simp
    _ = (G_val k1 P₀ R)⁻¹ := by
        rw [← Finset.mul_sum, ← G_val, sq]
        field_simp [hG.ne']

lemma selberg_prime_tuple_upper {K P₀ R x : ℕ} {c : Fin (K + 1) → ℕ}
    (hc : StrictMono c) (hc_le : ∀ j, c j ≤ P₀) (hP0 : (K + 1) ^ 4 ≤ P₀) (hR : 1 ≤ R) :
    (((Finset.Icc 0 x).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card : ℝ) ≤
      (P₀ + R + 1 : ℝ) + (x : ℝ) / G_val (K + 1) P₀ R +
        ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
  have hk1 : 1 ≤ K + 1 := Nat.succ_pos K
  have hP0_ge : K + 1 ≤ P₀ := le_trans (Nat.le_self_pow (by decide) _) hP0
  have hG_pos : 0 < G_val (K + 1) P₀ R := lt_of_lt_of_le zero_lt_one (G_val_ge_one hk1 hP0_ge hR)
  rcases le_or_gt x (P₀ + R) with hx_le | hx_gt
  · have hsub : (Finset.Icc 0 x).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime) ⊆ Finset.Icc 0 x :=
      Finset.filter_subset _ _
    have hcard : ((Finset.Icc 0 x).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card ≤ P₀ + R + 1 := by
      calc
        ((Finset.Icc 0 x).filter _).card ≤ (Finset.Icc 0 x).card := Finset.card_le_card hsub
        _ = x + 1 := by simp
        _ ≤ P₀ + R + 1 := by omega
    have h1 : (((Finset.Icc 0 x).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card : ℝ) ≤
        (P₀ + R + 1 : ℝ) := by exact_mod_cast hcard
    have h2 : 0 ≤ (x : ℝ) / G_val (K + 1) P₀ R := div_nonneg (Nat.cast_nonneg x) hG_pos.le
    have h3 : 0 ≤ ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := sq_nonneg _
    linarith
  · set A := P₀ + R + 1
    set L := x + 1 - A
    have hsplit : Finset.Icc 0 x = Finset.Icc 0 (P₀ + R) ∪ Finset.Ico A (A + L) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.Icc 0 (P₀ + R)) (Finset.Ico A (A + L)) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hn1 hn2
      omega
    have hcard_split :
        (((Finset.Icc 0 x).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card : ℝ) ≤
        (P₀ + R + 1 : ℝ) +
          (((Finset.Ico A (A + L)).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card : ℝ) := by
      rw [hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      have hfst : ((Finset.Icc 0 (P₀ + R)).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card ≤
          P₀ + R + 1 := by
        calc
          _ ≤ (Finset.Icc 0 (P₀ + R)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = P₀ + R + 1 := by simp
      push_cast
      linarith [show (((Finset.Icc 0 (P₀ + R)).filter _).card : ℝ) ≤ (P₀ + R + 1 : ℝ) from by exact_mod_cast hfst]
    have hquad : (((Finset.Ico A (A + L)).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card : ℝ) ≤
        ∑ n ∈ Finset.Ico A (A + L),
          (∑ d ∈ S_R P₀ R, if d ∣ polyProd c n then lam (K + 1) P₀ R d else 0) ^ 2 := by
      calc
        (((Finset.Ico A (A + L)).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime)).card : ℝ)
          = ∑ n ∈ (Finset.Ico A (A + L)).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime), (1 : ℝ) := by
              simp
        _ ≤ ∑ n ∈ (Finset.Ico A (A + L)).filter (fun n => ∀ j : Fin (K + 1), (n - c j).Prime),
              (∑ d ∈ S_R P₀ R, if d ∣ polyProd c n then lam (K + 1) P₀ R d else 0) ^ 2 := by
            refine Finset.sum_le_sum fun n hn => ?_
            simp only [Finset.mem_filter, Finset.mem_Ico] at hn
            have honly1 : ∀ d ∈ S_R P₀ R, d ∣ polyProd c n → d = 1 := by
              intro d hd hdvd
              simp only [S_R, Finset.mem_filter, Finset.mem_Icc] at hd
              by_contra hd1
              obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
              have hp_dvd_prod : p ∣ ∏ j : Fin (K + 1), (n - c j) := hpd.trans hdvd
              obtain ⟨j, _, hp_dvd_j⟩ := (hp.prime.dvd_finsetProd_iff _).mp hp_dvd_prod
              have hj_prime : (n - c j).Prime := hn.2 j
              have hp_eq : p = n - c j := ((hj_prime.dvd_iff_eq hp.ne_one).mp hp_dvd_j).symm
              have hp_le_d : p ≤ d := Nat.le_of_dvd hd.1.1 hpd
              have hnj : R + 1 ≤ n - c j := by
                have := hc_le j
                omega
              omega
            have hsum1 : ∑ d ∈ S_R P₀ R, (if d ∣ polyProd c n then lam (K + 1) P₀ R d else 0) = 1 := by
              have h1_mem : 1 ∈ S_R P₀ R := by
                simp only [S_R, Finset.mem_filter, Finset.mem_Icc]
                exact ⟨⟨le_rfl, hR⟩, goodMod_one P₀⟩
              rw [Finset.sum_eq_single 1]
              · simp [lam_one hk1 hP0_ge hR]
              · intro d hd hd1
                split_ifs with hdvd
                · exact absurd (honly1 d hd hdvd) hd1
                · rfl
              · intro h; exact absurd h1_mem h
            rw [hsum1, one_pow]
        _ ≤ ∑ n ∈ Finset.Ico A (A + L),
              (∑ d ∈ S_R P₀ R, if d ∣ polyProd c n then lam (K + 1) P₀ R d else 0) ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
    have hexpand : ∑ n ∈ Finset.Ico A (A + L),
          (∑ d ∈ S_R P₀ R, if d ∣ polyProd c n then lam (K + 1) P₀ R d else 0) ^ 2 =
        ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
          lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ *
            (((Finset.Ico A (A + L)).filter (fun n => Nat.lcm d₁ d₂ ∣ polyProd c n)).card : ℝ) := by
      have hsq : ∀ n ∈ Finset.Ico A (A + L),
          (∑ d ∈ S_R P₀ R, if d ∣ polyProd c n then lam (K + 1) P₀ R d else 0) ^ 2 =
          ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
            if Nat.lcm d₁ d₂ ∣ polyProd c n then lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ else 0 := by
        intro n _
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        have hlcm : Nat.lcm d₁ d₂ ∣ polyProd c n ↔ d₁ ∣ polyProd c n ∧ d₂ ∣ polyProd c n :=
          Nat.lcm_dvd_iff
        by_cases h1 : d₁ ∣ polyProd c n <;> by_cases h2 : d₂ ∣ polyProd c n <;> simp [hlcm, h1, h2]
      rw [Finset.sum_congr rfl hsq, Finset.sum_comm]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d₂ _ => ?_
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hcount_bound : ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
          lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ *
            (((Finset.Ico A (A + L)).filter (fun n => Nat.lcm d₁ d₂ ∣ polyProd c n)).card : ℝ) ≤
        (L : ℝ) / G_val (K + 1) P₀ R + ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
      set M_main := ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
        lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ *
          (((ω (K + 1) (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) * (L : ℝ))
      have hmain : M_main = (L : ℝ) / G_val (K + 1) P₀ R := by
        have hpull : M_main = (L : ℝ) * ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
            lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ *
              ((ω (K + 1) (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d₂ _ => by ring
        rw [hpull, selberg_main_identity hk1 hP0_ge hR, div_eq_mul_inv]
      have herr : ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
            lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ *
              ((((Finset.Ico A (A + L)).filter (fun n => Nat.lcm d₁ d₂ ∣ polyProd c n)).card : ℝ) -
                ((ω (K + 1) (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) * (L : ℝ)) ≤
          ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
        calc
          _ ≤ ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
                |lam (K + 1) P₀ R d₁| * |lam (K + 1) P₀ R d₂| *
                  |(((Finset.Ico A (A + L)).filter (fun n => Nat.lcm d₁ d₂ ∣ polyProd c n)).card : ℝ) -
                    ((ω (K + 1) (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) * (L : ℝ)| := by
              refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => ?_
              refine (le_abs_self _).trans ?_
              rw [abs_mul, abs_mul]
          _ ≤ ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
                1 * 1 * ((R : ℝ) ^ ((1 : ℝ) / 4) * (R : ℝ) ^ ((1 : ℝ) / 4)) := by
              refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
              simp only [S_R, Finset.mem_filter, Finset.mem_Icc] at hd₁ hd₂
              have hl1 := abs_lam_le_one hk1 hP0_ge hR (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hd₁.1, hd₁.2⟩)
              have hl2 := abs_lam_le_one hk1 hP0_ge hR (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hd₂.1, hd₂.2⟩)
              have hlcm := goodMod_lcm hd₁.2 hd₂.2
              have hcnt := count_polyProd_dvd hc hc_le (by omega : P₀ ≤ A) hlcm (L := L)
              have hω1 : (ω (K + 1) d₁ : ℝ) ≤ (R : ℝ) ^ ((1 : ℝ) / 4) := by
                refine (ω_real_le_rpow hP0 hd₁.2).trans ?_
                exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hd₁.1.2) (by norm_num)
              have hω2 : (ω (K + 1) d₂ : ℝ) ≤ (R : ℝ) ^ ((1 : ℝ) / 4) := by
                refine (ω_real_le_rpow hP0 hd₂.2).trans ?_
                exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hd₂.1.2) (by norm_num)
              have hω_lcm : (ω (K + 1) (Nat.lcm d₁ d₂) : ℝ) ≤
                  (R : ℝ) ^ ((1 : ℝ) / 4) * (R : ℝ) ^ ((1 : ℝ) / 4) := by
                calc
                  (ω (K + 1) (Nat.lcm d₁ d₂) : ℝ) ≤ (ω (K + 1) d₁ : ℝ) * (ω (K + 1) d₂ : ℝ) := by
                    exact_mod_cast ω_lcm_le_mul hk1 hd₁.2 hd₂.2
                  _ ≤ (R : ℝ) ^ ((1 : ℝ) / 4) * (R : ℝ) ^ ((1 : ℝ) / 4) :=
                    mul_le_mul hω1 hω2 (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              have hprod_le : |lam (K + 1) P₀ R d₁| * |lam (K + 1) P₀ R d₂| ≤ 1 * 1 :=
                mul_le_mul hl1 hl2 (abs_nonneg _) zero_le_one
              exact mul_le_mul hprod_le (hcnt.trans hω_lcm) (abs_nonneg _) (by positivity)
          _ ≤ ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
              have hcard_SR : ((S_R P₀ R).card : ℝ) ≤ (R : ℝ) := by
                have hsub_SR : S_R P₀ R ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
                have hle := Finset.card_le_card hsub_SR
                simp only [Nat.card_Icc, add_tsub_cancel_right] at hle
                exact_mod_cast hle
              simp only [one_mul, Finset.sum_const, nsmul_eq_mul]
              have hr_nonneg : 0 ≤ (R : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg R) _
              calc
                ((S_R P₀ R).card : ℝ) * (((S_R P₀ R).card : ℝ) * ((R : ℝ) ^ ((1 : ℝ) / 4) * (R : ℝ) ^ ((1 : ℝ) / 4)))
                  ≤ (R : ℝ) * ((R : ℝ) * ((R : ℝ) ^ ((1 : ℝ) / 4) * (R : ℝ) ^ ((1 : ℝ) / 4))) :=
                    mul_le_mul hcard_SR
                      (mul_le_mul hcard_SR le_rfl (mul_nonneg hr_nonneg hr_nonneg) (Nat.cast_nonneg R))
                      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hr_nonneg hr_nonneg)) (Nat.cast_nonneg R)
                _ = ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
      have hsum_split : ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
            lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ *
              (((Finset.Ico A (A + L)).filter (fun n => Nat.lcm d₁ d₂ ∣ polyProd c n)).card : ℝ) =
          M_main + ∑ d₁ ∈ S_R P₀ R, ∑ d₂ ∈ S_R P₀ R,
            lam (K + 1) P₀ R d₁ * lam (K + 1) P₀ R d₂ *
              ((((Finset.Ico A (A + L)).filter (fun n => Nat.lcm d₁ d₂ ∣ polyProd c n)).card : ℝ) -
                ((ω (K + 1) (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) * (L : ℝ)) := by
        simp only [M_main, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => by ring
      rw [hsum_split, hmain]
      exact add_le_add le_rfl herr
    have hLx : (L : ℝ) / G_val (K + 1) P₀ R ≤ (x : ℝ) / G_val (K + 1) P₀ R := by
      refine div_le_div_of_nonneg_right ?_ hG_pos.le
      exact_mod_cast (by omega : L ≤ x)
    linarith

/- Block 3A: Harmonic lower bound, smooth Euler product, coprime factorization, Bernoulli -/

lemma harmonic_ge_log (U : ℕ) :
    Real.log ((U : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 U, (1 : ℝ) / m := by
  induction U with
  | zero => simp
  | succ U ih =>
    have hsplit : Finset.Icc 1 (U + 1) = insert (U + 1) (Finset.Icc 1 U) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : U + 1 ∉ Finset.Icc 1 U := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have h1 : (0 : ℝ) < (U : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < ((U + 1 : ℕ) : ℝ) + 1 := by positivity
    have hdiv : ((U + 1 : ℕ) : ℝ) + 1 = ((U : ℝ) + 1) * ((((U + 1 : ℕ) : ℝ) + 1) / ((U : ℝ) + 1)) := by
      field_simp
    have hlog_step : Real.log ((((U + 1 : ℕ) : ℝ) + 1) / ((U : ℝ) + 1)) ≤
        1 / ((U + 1 : ℕ) : ℝ) := by
      have hpos_div : 0 < (((U + 1 : ℕ) : ℝ) + 1) / ((U : ℝ) + 1) := div_pos h2 h1
      have hle := Real.log_le_sub_one_of_pos hpos_div
      have heq : ((((U + 1 : ℕ) : ℝ) + 1) / ((U : ℝ) + 1)) - 1 = 1 / ((U + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      exact heq ▸ hle
    rw [hdiv, Real.log_mul h1.ne' (div_pos h2 h1).ne']
    linarith

lemma geom_sum_inv_prime_le (U p : ℕ) (hp : 2 ≤ p) :
    ∑ e ∈ Finset.range (U + 1), ((1 : ℝ) / (p : ℝ)) ^ e ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hr_lt1 : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hp_gt1
  have hr_ne1 : (1 : ℝ) / (p : ℝ) ≠ 1 := hr_lt1.ne
  rw [geom_sum_eq hr_ne1]
  have hnum : ((1 : ℝ) / (p : ℝ)) ^ (U + 1) - 1 ≤ 0 := by
    have hpow_le : ((1 : ℝ) / (p : ℝ)) ^ (U + 1) ≤ 1 := pow_le_one₀ (by positivity) hr_lt1.le
    linarith
  have hden : (1 : ℝ) / (p : ℝ) - 1 < 0 := sub_neg.mpr hr_lt1
  have heq : (((1 : ℝ) / (p : ℝ)) ^ (U + 1) - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
      (1 - ((1 : ℝ) / (p : ℝ)) ^ (U + 1)) / (1 - (1 : ℝ) / (p : ℝ)) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [heq]
  have h1_sub_pos : 0 < 1 - (1 : ℝ) / (p : ℝ) := sub_pos.mpr hr_lt1
  have hle_num : 1 - ((1 : ℝ) / (p : ℝ)) ^ (U + 1) ≤ 1 := by
    have : 0 ≤ ((1 : ℝ) / (p : ℝ)) ^ (U + 1) := by positivity
    linarith
  calc
    (1 - ((1 : ℝ) / (p : ℝ)) ^ (U + 1)) / (1 - (1 : ℝ) / (p : ℝ))
      ≤ 1 / (1 - (1 : ℝ) / (p : ℝ)) := div_le_div_of_nonneg_right hle_num h1_sub_pos.le
    _ = (p : ℝ) / ((p : ℝ) - 1) := by
        have hp0 : (p : ℝ) ≠ 0 := by positivity
        have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp_gt1.ne'
        field_simp

lemma padicValNat_lt_succ_self {p s U : ℕ} (hp : 2 ≤ p) (hs1 : 1 ≤ s) (hsU : s ≤ U) :
    padicValNat p s < U + 1 := by
  have hp_gt1 : 1 < p := by omega
  have hpow_dvd : p ^ padicValNat p s ∣ s := pow_padicValNat_dvd
  have hpow_le : p ^ padicValNat p s ≤ s := Nat.le_of_dvd hs1 hpow_dvd
  have hlt : padicValNat p s < p ^ padicValNat p s := Nat.lt_pow_self hp_gt1
  omega

lemma smooth_prod_padicValNat {s P₀ : ℕ} (hs : 1 ≤ s) (hs_sm : ∀ p ∈ s.primeFactors, p ≤ P₀) :
    ∏ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, p ^ padicValNat p s = s := by
  have hsub : s.primeFactors ⊆ (Finset.Icc 1 P₀).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    exact ⟨⟨hp_prime.pos, hs_sm p hp⟩, hp_prime⟩
  have hs0 : s ≠ 0 := by omega
  have h1 : ∏ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, p ^ padicValNat p s =
      ∏ p ∈ s.primeFactors, p ^ padicValNat p s := by
    rw [← Finset.prod_subset hsub]
    intro p hp hp_not
    simp only [Finset.mem_filter] at hp
    have hnot_dvd : ¬ p ∣ s := by
      intro hdvd
      exact hp_not (Nat.mem_primeFactors.mpr ⟨hp.2, hdvd, hs0⟩)
    rw [padicValNat.eq_zero_of_not_dvd hnot_dvd, pow_zero]
  rw [h1]
  have h2 : ∏ p ∈ s.primeFactors, p ^ padicValNat p s =
      ∏ p ∈ s.primeFactors, p ^ s.factorization p := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_def s hp_prime]
  rw [h2]
  exact Nat.prod_factorization_pow_eq_self hs0

lemma smooth_inv_sum_le_aux (U : ℕ) (Pr Smooth : Finset ℕ)
    (hPr : ∀ p ∈ Pr, p.Prime)
    (hSmooth : ∀ s ∈ Smooth, 1 ≤ s ∧ s ≤ U ∧
      ∏ p ∈ Pr, p ^ padicValNat p s = s) :
    ∑ s ∈ Smooth, (1 : ℝ) / s ≤ ∏ p ∈ Pr, (p : ℝ) / ((p : ℝ) - 1) := by
  set Box := Pr.pi (fun _ => Finset.range (U + 1))
  let φ : ℕ → ∀ p ∈ Pr, ℕ := fun s p _ => padicValNat p s
  have hinj : Set.InjOn φ ↑Smooth := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := (hSmooth s₁ hs₁).2.2
    have h2 := (hSmooth s₂ hs₂).2.2
    rw [← h1, ← h2]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_eq : φ s₁ p hp = φ s₂ p hp := congr_fun (congr_fun heq p) hp
    dsimp [φ] at hp_eq
    rw [hp_eq]
  have himg : Smooth.image φ ⊆ Box := by
    intro e he
    rw [Finset.mem_image] at he
    rcases he with ⟨s, hs, rfl⟩
    simp only [Box, Finset.mem_pi, Finset.mem_range]
    intro p hp
    have hsm := hSmooth s hs
    exact padicValNat_lt_succ_self (hPr p hp).two_le hsm.1 hsm.2.1
  have hsum_eq : ∑ s ∈ Smooth, (1 : ℝ) / (s : ℝ) =
      ∑ e ∈ Smooth.image φ, ∏ x ∈ Pr.attach, ((1 : ℝ) / (x.1 : ℝ)) ^ e x.1 x.2 := by
    rw [Finset.sum_image (fun s₁ h₁ s₂ h₂ heq => hinj h₁ h₂ heq)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hprod := (hSmooth s hs).2.2
    have hattach : ∏ x ∈ Pr.attach, ((1 : ℝ) / (x.1 : ℝ)) ^ φ s x.1 x.2 =
        ∏ p ∈ Pr, ((1 : ℝ) / (p : ℝ)) ^ padicValNat p s :=
      Finset.prod_attach Pr (fun p => ((1 : ℝ) / (p : ℝ)) ^ padicValNat p s)
    rw [hattach]
    conv_lhs => rw [← hprod]
    push_cast
    simp only [one_div, Finset.prod_inv_distrib, inv_pow]
  calc
    ∑ s ∈ Smooth, (1 : ℝ) / (s : ℝ)
      = ∑ e ∈ Smooth.image φ, ∏ x ∈ Pr.attach, ((1 : ℝ) / (x.1 : ℝ)) ^ e x.1 x.2 := hsum_eq
    _ ≤ ∑ e ∈ Box, ∏ x ∈ Pr.attach, ((1 : ℝ) / (x.1 : ℝ)) ^ e x.1 x.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ =>
          Finset.prod_nonneg fun _ _ => by positivity
    _ = ∏ p ∈ Pr, ∑ k ∈ Finset.range (U + 1), ((1 : ℝ) / (p : ℝ)) ^ k :=
        (Finset.prod_sum Pr (fun _ => Finset.range (U + 1)) (fun p k => ((1 : ℝ) / (p : ℝ)) ^ k)).symm
    _ ≤ ∏ p ∈ Pr, (p : ℝ) / ((p : ℝ) - 1) := by
        refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
        exact geom_sum_inv_prime_le U p (hPr p hp).two_le

lemma smooth_inv_sum_le (U P₀ : ℕ) :
    ∑ s ∈ (Finset.Icc 1 U).filter (fun s => ∀ p ∈ s.primeFactors, p ≤ P₀), (1 : ℝ) / s ≤
      ∏ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1) := by
  refine smooth_inv_sum_le_aux U _ _ (fun p hp => (Finset.mem_filter.mp hp).2) (fun s hs => ?_)
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  exact ⟨hs.1.1, hs.1.2, smooth_prod_padicValNat hs.1.1 hs.2⟩

lemma coprime_harmonic_ge (P₀ U : ℕ) :
    Real.log ((U : ℝ) + 1) ≤
      (∏ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1)) *
        ∑ n ∈ (Finset.Icc 1 U).filter (fun n => ∀ p ∈ n.primeFactors, P₀ < p), (1 : ℝ) / n := by
  set Smooth := (Finset.Icc 1 U).filter (fun s => ∀ p ∈ s.primeFactors, p ≤ P₀)
  set Cop := (Finset.Icc 1 U).filter (fun n => ∀ p ∈ n.primeFactors, P₀ < p)
  let sPart : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors.filter (fun p => p ≤ P₀), p ^ m.factorization p
  let nPart : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors.filter (fun p => P₀ < p), p ^ m.factorization p
  have hm_eq : ∀ {m : ℕ}, 1 ≤ m → sPart m * nPart m = m := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hsplit : m.primeFactors =
        m.primeFactors.filter (fun p => p ≤ P₀) ∪ m.primeFactors.filter (fun p => P₀ < p) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases hp : p ≤ P₀ <;> simp [hp]
      exact fun _ _ _ => Nat.lt_of_not_ge hp
    have hdisj : Disjoint (m.primeFactors.filter (fun p => p ≤ P₀))
        (m.primeFactors.filter (fun p => P₀ < p)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      omega
    have hprod : sPart m * nPart m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      dsimp [sPart, nPart]
      rw [← Finset.prod_union hdisj, ← hsplit]
    rw [hprod]
    exact Nat.prod_factorization_pow_eq_self hm0
  have hinj : Set.InjOn (fun m => (sPart m, nPart m)) ↑(Finset.Icc 1 U) := by
    intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.mem_coe, Finset.mem_Icc] at hm₁ hm₂
    have h1 := hm_eq hm₁.1
    have h2 := hm_eq hm₂.1
    have hs : sPart m₁ = sPart m₂ := congr_arg Prod.fst heq
    have hn : nPart m₁ = nPart m₂ := congr_arg Prod.snd heq
    rw [← h1, ← h2, hs, hn]
  have himg : (Finset.Icc 1 U).image (fun m => (sPart m, nPart m)) ⊆ Smooth ×ˢ Cop := by
    intro sn hsn
    rw [Finset.mem_image] at hsn
    rcases hsn with ⟨m, hm, rfl⟩
    simp only [Finset.mem_Icc] at hm
    have hmul := hm_eq hm.1
    have hs_pos : 0 < sPart m := Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
    have hn_pos : 0 < nPart m := Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
    have hs_le : sPart m ≤ U := le_trans (Nat.le_of_dvd hm.1 ⟨nPart m, hmul.symm⟩) hm.2
    have hn_le : nPart m ≤ U := le_trans (Nat.le_of_dvd hm.1 ⟨sPart m, hmul.symm.trans (mul_comm _ _)⟩) hm.2
    have hs_pf : ∀ p ∈ (sPart m).primeFactors, p ≤ P₀ := by
      intro p hp
      have hp_dvd : p ∣ sPart m := Nat.dvd_of_mem_primeFactors hp
      have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      obtain ⟨q, hq, hpq⟩ := (hp_prime.prime.dvd_finsetProd_iff _).mp hp_dvd
      have hqp : q.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
      have hpeq : p = q := by
        have := hp_prime.dvd_of_dvd_pow hpq
        exact ((hqp.dvd_iff_eq hp_prime.ne_one).mp this).symm
      exact hpeq ▸ (Finset.mem_filter.mp hq).2
    have hn_pf : ∀ p ∈ (nPart m).primeFactors, P₀ < p := by
      intro p hp
      have hp_dvd : p ∣ nPart m := Nat.dvd_of_mem_primeFactors hp
      have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      obtain ⟨q, hq, hpq⟩ := (hp_prime.prime.dvd_finsetProd_iff _).mp hp_dvd
      have hqp : q.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
      have hpeq : p = q := by
        have := hp_prime.dvd_of_dvd_pow hpq
        exact ((hqp.dvd_iff_eq hp_prime.ne_one).mp this).symm
      exact hpeq ▸ (Finset.mem_filter.mp hq).2
    simp only [Finset.mem_product, Smooth, Cop, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨hs_pos, hs_le⟩, hs_pf⟩, ⟨⟨hn_pos, hn_le⟩, hn_pf⟩⟩
  have hsum_le : ∑ m ∈ Finset.Icc 1 U, (1 : ℝ) / m ≤
      (∑ s ∈ Smooth, (1 : ℝ) / s) * (∑ n ∈ Cop, (1 : ℝ) / n) := by
    calc
      ∑ m ∈ Finset.Icc 1 U, (1 : ℝ) / m
        = ∑ m ∈ Finset.Icc 1 U, (1 : ℝ) / ((sPart m : ℝ) * (nPart m : ℝ)) := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hmul := hm_eq (Finset.mem_Icc.mp hm).1
            rw [← Nat.cast_mul, hmul]
      _ = ∑ sn ∈ (Finset.Icc 1 U).image (fun m => (sPart m, nPart m)),
            (1 : ℝ) / ((sn.1 : ℝ) * (sn.2 : ℝ)) :=
            (Finset.sum_image (f := fun sn : ℕ × ℕ => (1 : ℝ) / ((sn.1 : ℝ) * (sn.2 : ℝ)))
              (g := fun m => (sPart m, nPart m)) hinj).symm
      _ ≤ ∑ sn ∈ Smooth ×ˢ Cop, (1 : ℝ) / ((sn.1 : ℝ) * (sn.2 : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
      _ = (∑ s ∈ Smooth, (1 : ℝ) / s) * (∑ n ∈ Cop, (1 : ℝ) / n) := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun n _ => by
              rw [one_div_mul_one_div]
  have hC : 0 ≤ ∑ n ∈ Cop, (1 : ℝ) / n := Finset.sum_nonneg fun _ _ => by positivity
  calc
    Real.log ((U : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 U, (1 : ℝ) / m := harmonic_ge_log U
    _ ≤ (∑ s ∈ Smooth, (1 : ℝ) / s) * (∑ n ∈ Cop, (1 : ℝ) / n) := hsum_le
    _ ≤ (∏ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1)) *
          ∑ n ∈ Cop, (1 : ℝ) / n :=
        mul_le_mul_of_nonneg_right (smooth_inv_sum_le U P₀) hC

lemma bernoulli_prime_pow_le {k1 p : ℕ} (hk1 : 1 ≤ k1) (hp : k1 < p) :
    ((p : ℝ) / ((p : ℝ) - 1)) ^ k1 - 1 ≤ (k1 : ℝ) / ((p : ℝ) - k1) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_le_of_lt hk1 hp
  have hpk : (k1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hp_sub1 : 0 < (p : ℝ) - 1 := sub_pos.mpr hp1
  have hp_subk : 0 < (p : ℝ) - k1 := sub_pos.mpr hpk
  have hbern_all : ∀ n : ℕ, 1 - (n : ℝ) * ((1 : ℝ) / (p : ℝ)) ≤ (1 - (1 : ℝ) / (p : ℝ)) ^ n := by
    have hge0 : 0 ≤ 1 - (1 : ℝ) / (p : ℝ) := by
      have : (1 : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr hp1.le
      linarith
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hnonneg_prod : 0 ≤ (n : ℝ) * ((1 : ℝ) / (p : ℝ)) ^ 2 := by positivity
      calc
        1 - ((n + 1 : ℕ) : ℝ) * ((1 : ℝ) / (p : ℝ))
          ≤ (1 - (n : ℝ) * ((1 : ℝ) / (p : ℝ))) * (1 - (1 : ℝ) / (p : ℝ)) := by
              push_cast
              linarith
        _ ≤ (1 - (1 : ℝ) / (p : ℝ)) ^ n * (1 - (1 : ℝ) / (p : ℝ)) :=
              mul_le_mul_of_nonneg_right ih hge0
        _ = (1 - (1 : ℝ) / (p : ℝ)) ^ (n + 1) := (pow_succ _ _).symm
  have hbern : 1 - (k1 : ℝ) / (p : ℝ) ≤ (1 - (1 : ℝ) / (p : ℝ)) ^ k1 := by
    simpa [div_eq_mul_inv] using hbern_all k1
  have hpos_lhs : 0 < 1 - (k1 : ℝ) / (p : ℝ) := by
    have : (k1 : ℝ) / (p : ℝ) < 1 := (div_lt_one hp0).mpr hpk
    linarith
  have hinv : ((1 - (1 : ℝ) / (p : ℝ)) ^ k1)⁻¹ ≤ (1 - (k1 : ℝ) / (p : ℝ))⁻¹ :=
    (inv_le_inv₀ (pow_pos (by
      have : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one hp0).mpr hp1
      linarith) k1) hpos_lhs).mpr hbern
  have hlhs_eq : ((p : ℝ) / ((p : ℝ) - 1)) ^ k1 = ((1 - (1 : ℝ) / (p : ℝ)) ^ k1)⁻¹ := by
    rw [← inv_pow]
    congr 1
    field_simp
  have hrhs_eq : (1 - (k1 : ℝ) / (p : ℝ))⁻¹ - 1 = (k1 : ℝ) / ((p : ℝ) - k1) := by
    field_simp
    ring
  linarith

/- Block 3B: Lower bound on G_val R and final Blecksmith-Erdos-Selfridge theorem -/

lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert p s hps ih =>
    have hp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      obtain ⟨q, hqs, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
      have hq : q.Prime := hs' q hqs
      have hpeq : p = q := ((hq.dvd_iff_eq hp.ne_one).mp hpq).symm
      exact hps (hpeq ▸ hqs)
    rw [Finset.prod_insert hps]
    exact Nat.squarefree_mul_iff.mpr ⟨hcop, hp.squarefree, ih hs'⟩

lemma prod_padicValNat_of_subset {s : ℕ} (hs : 1 ≤ s) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hsub : s.primeFactors ⊆ S) :
    ∏ p ∈ S, p ^ padicValNat p s = s := by
  have hs0 : s ≠ 0 := by omega
  have h1 : ∏ p ∈ S, p ^ padicValNat p s = ∏ p ∈ s.primeFactors, p ^ padicValNat p s := by
    rw [← Finset.prod_subset hsub]
    intro p hp hp_not
    have hnot_dvd : ¬ p ∣ s := fun hdvd => hp_not (Nat.mem_primeFactors.mpr ⟨hS p hp, hdvd, hs0⟩)
    rw [padicValNat.eq_zero_of_not_dvd hnot_dvd, pow_zero]
  rw [h1]
  have h2 : ∏ p ∈ s.primeFactors, p ^ padicValNat p s =
      ∏ p ∈ s.primeFactors, p ^ s.factorization p := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def s (Nat.mem_primeFactors.mp hp).1]
  rw [h2]
  exact Nat.prod_factorization_pow_eq_self hs0

lemma fiber_sum_le_inv_h (k1 U : ℕ) (hk1 : 1 ≤ k1) (Pk : Finset ℕ) (Tk : Finset (Fin k1 → ℕ))
    (hPk : ∀ p ∈ Pk, p.Prime ∧ k1 < p)
    (hTk : ∀ t ∈ Tk, (∀ i, 1 ≤ t i ∧ t i ≤ U ∧ (t i).primeFactors ⊆ Pk) ∧ ∀ p ∈ Pk, ∃ i, p ∣ t i) :
    ∑ t ∈ Tk, ∏ i : Fin k1, (1 : ℝ) / (t i : ℝ) ≤
      ∏ p ∈ Pk, (k1 : ℝ) / ((p : ℝ) - k1) := by
  set Fset : Finset (Fin k1 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin k1 => Finset.range (U + 1))).filter (fun f => f ≠ 0)
  set Box := Pk.pi (fun _ => Fset)
  let φ : (Fin k1 → ℕ) → ∀ p ∈ Pk, Fin k1 → ℕ := fun t p _ i => padicValNat p (t i)
  have hPk_p : ∀ p ∈ Pk, p.Prime := fun p hp => (hPk p hp).1
  have hinj : Set.InjOn φ ↑Tk := by
    intro t₁ ht₁ t₂ ht₂ heq
    ext i
    have ht1_i := (hTk t₁ ht₁).1 i
    have ht2_i := (hTk t₂ ht₂).1 i
    have h1 := prod_padicValNat_of_subset ht1_i.1 hPk_p ht1_i.2.2
    have h2 := prod_padicValNat_of_subset ht2_i.1 hPk_p ht2_i.2.2
    rw [← h1, ← h2]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpeq : φ t₁ p hp i = φ t₂ p hp i :=
      congr_fun (congr_fun (congr_fun heq p) hp) i
    dsimp [φ] at hpeq
    rw [hpeq]
  have himg : Tk.image φ ⊆ Box := by
    intro e he
    rw [Finset.mem_image] at he
    rcases he with ⟨t, ht, rfl⟩
    simp only [Box, Finset.mem_pi, Fset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    intro p hp
    refine ⟨fun i => padicValNat_lt_succ_self (hPk p hp).1.two_le ((hTk t ht).1 i).1 ((hTk t ht).1 i).2.1, ?_⟩
    obtain ⟨i, hi⟩ := (hTk t ht).2 p hp
    have hti0 : t i ≠ 0 := by have := ((hTk t ht).1 i).1; omega
    have hpos : 0 < padicValNat p (t i) := by
      rw [← Nat.factorization_def (t i) (hPk p hp).1]
      exact (hPk p hp).1.factorization_pos_of_dvd hti0 hi
    intro h0
    have := congr_fun h0 i
    dsimp [φ] at this
    omega
  have hsum_eq : ∑ t ∈ Tk, ∏ i : Fin k1, (1 : ℝ) / (t i : ℝ) =
      ∑ e ∈ Tk.image φ, ∏ x ∈ Pk.attach, ∏ i : Fin k1, ((1 : ℝ) / (x.1 : ℝ)) ^ e x.1 x.2 i := by
    rw [Finset.sum_image (fun t₁ h₁ t₂ h₂ heq => hinj h₁ h₂ heq)]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hattach : ∏ x ∈ Pk.attach, ∏ i : Fin k1, ((1 : ℝ) / (x.1 : ℝ)) ^ φ t x.1 x.2 i =
        ∏ p ∈ Pk, ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ padicValNat p (t i) :=
      Finset.prod_attach Pk (fun p => ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ padicValNat p (t i))
    rw [hattach, Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hti := (hTk t ht).1 i
    have hprod := prod_padicValNat_of_subset hti.1 hPk_p hti.2.2
    conv_lhs => rw [← hprod]
    push_cast
    simp only [one_div, Finset.prod_inv_distrib, inv_pow]
  have hfactor : ∀ p ∈ Pk,
      ∑ f ∈ Fset, ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ f i ≤ (k1 : ℝ) / ((p : ℝ) - k1) := by
    intro p hp
    have h0_mem : (0 : Fin k1 → ℕ) ∈ Fintype.piFinset (fun _ : Fin k1 => Finset.range (U + 1)) := by
      simp [Fintype.mem_piFinset]
    have hadd1 : (∑ f ∈ Fset, ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ f i) + 1 =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin k1 => Finset.range (U + 1)),
          ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ f i := by
      have hsplit : Fintype.piFinset (fun _ : Fin k1 => Finset.range (U + 1)) = insert 0 Fset := by
        ext f
        simp only [Finset.mem_insert, Fset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        by_cases hf : f = 0 <;> simp [hf]
      have h0_not : (0 : Fin k1 → ℕ) ∉ Fset := by simp [Fset]
      rw [hsplit, Finset.sum_insert h0_not]
      simp [add_comm]
    have hprod_sum : ∑ f ∈ Fintype.piFinset (fun _ : Fin k1 => Finset.range (U + 1)),
          ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ f i =
        (∑ e ∈ Finset.range (U + 1), ((1 : ℝ) / (p : ℝ)) ^ e) ^ k1 := by
      rw [Finset.sum_prod_piFinset (Finset.range (U + 1)) (fun _ e => ((1 : ℝ) / (p : ℝ)) ^ e),
        Finset.prod_const, Finset.card_fin]
    have hpow_le : (∑ e ∈ Finset.range (U + 1), ((1 : ℝ) / (p : ℝ)) ^ e) ^ k1 ≤
        ((p : ℝ) / ((p : ℝ) - 1)) ^ k1 := by
      refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) ?_ k1
      exact geom_sum_inv_prime_le U p (hPk p hp).1.two_le
    have hbern := bernoulli_prime_pow_le hk1 (hPk p hp).2
    linarith
  calc
    ∑ t ∈ Tk, ∏ i : Fin k1, (1 : ℝ) / (t i : ℝ)
      = ∑ e ∈ Tk.image φ, ∏ x ∈ Pk.attach, ∏ i : Fin k1, ((1 : ℝ) / (x.1 : ℝ)) ^ e x.1 x.2 i := hsum_eq
    _ ≤ ∑ e ∈ Box, ∏ x ∈ Pk.attach, ∏ i : Fin k1, ((1 : ℝ) / (x.1 : ℝ)) ^ e x.1 x.2 i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ =>
          Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity
    _ = ∏ p ∈ Pk, ∑ f ∈ Fset, ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ f i :=
        (Finset.prod_sum Pk (fun _ => Fset) (fun p f => ∏ i : Fin k1, ((1 : ℝ) / (p : ℝ)) ^ f i)).symm
    _ ≤ ∏ p ∈ Pk, (k1 : ℝ) / ((p : ℝ) - k1) := by
        refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.prod_nonneg fun _ _ => by positivity) hfactor

lemma pow_coprime_sum_le_G {k1 P₀ R : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hR : 1 ≤ R) :
    (∑ n ∈ (Finset.Icc 1 (Nat.floor ((R : ℝ) ^ ((1 : ℝ) / k1)))).filter
        (fun n => ∀ p ∈ n.primeFactors, P₀ < p), (1 : ℝ) / n) ^ k1 ≤ G_val k1 P₀ R := by
  set U := Nat.floor ((R : ℝ) ^ ((1 : ℝ) / k1))
  set Cop := (Finset.Icc 1 U).filter (fun n => ∀ p ∈ n.primeFactors, P₀ < p)
  set T : Finset (Fin k1 → ℕ) := Fintype.piFinset (fun _ : Fin k1 => Cop)
  let rad : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors, p
  let radT : (Fin k1 → ℕ) → ℕ := fun t => rad (∏ i : Fin k1, t i)
  have hpow_sum : (∑ n ∈ Cop, (1 : ℝ) / n) ^ k1 = ∑ t ∈ T, ∏ i : Fin k1, (1 : ℝ) / (t i : ℝ) := by
    have hconst : (∑ n ∈ Cop, (1 : ℝ) / n) ^ k1 = ∏ _i : Fin k1, ∑ n ∈ Cop, (1 : ℝ) / n := by
      rw [Finset.prod_const, Finset.card_fin]
    rw [hconst, Finset.sum_prod_piFinset Cop (fun _ n => (1 : ℝ) / n)]
  have hmaps : ∀ t ∈ T, radT t ∈ S_R P₀ R := by
    intro t ht
    simp only [T, Fintype.mem_piFinset, Cop, Finset.mem_filter, Finset.mem_Icc] at ht
    have hU_pow : U ^ k1 ≤ R := by
      have hk1_ne : (k1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : k1 ≠ 0)
      have hU_le : (U : ℝ) ≤ (R : ℝ) ^ ((1 : ℝ) / k1) := Nat.floor_le (by positivity)
      have hpow : ((U ^ k1 : ℕ) : ℝ) ≤ (R : ℝ) := by
        calc
          ((U ^ k1 : ℕ) : ℝ) = (U : ℝ) ^ k1 := by push_cast; rfl
          _ ≤ ((R : ℝ) ^ ((1 : ℝ) / k1)) ^ k1 := pow_le_pow_left₀ (Nat.cast_nonneg _) hU_le k1
          _ = (R : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel hk1_ne,
                Real.rpow_one]
      exact_mod_cast hpow
    have hprod_pos : 0 < ∏ i : Fin k1, t i := Finset.prod_pos fun i _ => (ht i).1.1
    have hprod_le : ∏ i : Fin k1, t i ≤ U ^ k1 := by
      calc
        ∏ i : Fin k1, t i ≤ ∏ _i : Fin k1, U := Finset.prod_le_prod' fun i _ => (ht i).1.2
        _ = U ^ k1 := by simp
    have hrad_dvd : radT t ∣ ∏ i : Fin k1, t i := Nat.prod_primeFactors_dvd _
    have hrad_sq : Squarefree (radT t) :=
      squarefree_prod_primes fun p hp => (Nat.mem_primeFactors.mp hp).1
    have hrad_pos : 0 < radT t := Nat.pos_of_ne_zero hrad_sq.ne_zero
    have hrad_le : radT t ≤ R := (Nat.le_of_dvd hprod_pos hrad_dvd).trans (hprod_le.trans hU_pow)
    have hrad_pf : ∀ p ∈ (radT t).primeFactors, P₀ < p := by
      intro p hp
      dsimp only [radT, rad] at hp
      rw [Nat.primeFactors_prod_primeFactors] at hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have hp_dvd := (Nat.mem_primeFactors.mp hp).2.1
      obtain ⟨i, _, hi⟩ := (hp_prime.prime.dvd_finsetProd_iff _).mp hp_dvd
      have hti0 : t i ≠ 0 := by have := (ht i).1.1; omega
      exact (ht i).2 p (Nat.mem_primeFactors.mpr ⟨hp_prime, hi, hti0⟩)
    simp only [S_R, Finset.mem_filter, Finset.mem_Icc, GoodMod]
    exact ⟨⟨hrad_pos, hrad_le⟩, hrad_sq, hrad_pf⟩
  rw [hpow_sum, ← Finset.sum_fiberwise_of_maps_to hmaps, G_val]
  refine Finset.sum_le_sum fun k hk => ?_
  simp only [S_R, Finset.mem_filter, Finset.mem_Icc] at hk
  have hk_good := hk.2
  have hPk : ∀ p ∈ k.primeFactors, p.Prime ∧ k1 < p := by
    intro p hp
    exact ⟨(Nat.mem_primeFactors.mp hp).1, lt_of_le_of_lt hP0 (hk_good.2 p hp)⟩
  have hTk : ∀ t ∈ T.filter (fun t => radT t = k),
      (∀ i, 1 ≤ t i ∧ t i ≤ U ∧ (t i).primeFactors ⊆ k.primeFactors) ∧
        ∀ p ∈ k.primeFactors, ∃ i, p ∣ t i := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rcases ht with ⟨htT, hrad_eq⟩
    simp only [T, Fintype.mem_piFinset, Cop, Finset.mem_filter, Finset.mem_Icc] at htT
    have hprod_pf : (∏ i : Fin k1, t i).primeFactors = k.primeFactors := by
      dsimp only [radT, rad] at hrad_eq
      rw [← hrad_eq, Nat.primeFactors_prod_primeFactors]
    refine ⟨fun i => ?_, fun p hp => ?_⟩
    · refine ⟨(htT i).1.1, (htT i).1.2, ?_⟩
      rw [← hprod_pf]
      exact Nat.primeFactors_mono (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        (Finset.prod_pos fun j _ => (htT j).1.1).ne'
    · rw [← hprod_pf] at hp
      have hp_prime := (Nat.mem_primeFactors.mp hp).1
      have hp_dvd := (Nat.mem_primeFactors.mp hp).2.1
      obtain ⟨i, _, hi⟩ := (hp_prime.prime.dvd_finsetProd_iff _).mp hp_dvd
      exact ⟨i, hi⟩
  calc
    ∑ t ∈ T.filter (fun t => radT t = k), ∏ i : Fin k1, (1 : ℝ) / (t i : ℝ)
      ≤ ∏ p ∈ k.primeFactors, (k1 : ℝ) / ((p : ℝ) - k1) :=
          fiber_sum_le_inv_h k1 U hk1 k.primeFactors (T.filter (fun t => radT t = k)) hPk hTk
    _ = (h_val k1 k)⁻¹ := by
        have hh_pos : (∏ p ∈ k.primeFactors, ((p : ℝ) - k1) / (k1 : ℝ)) ≠ 0 := by
          rw [← h_val]
          exact (h_val_pos hk1 hP0 hk_good).ne'
        rw [h_val, ← one_div, eq_div_iff hh_pos, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun p hp => ?_
        have hp_gt := (hPk p hp).2
        have hpk : (p : ℝ) - k1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp_gt.ne')
        have hk0 : (k1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : k1 ≠ 0)
        field_simp

noncomputable def C_smooth (P₀ : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1)

lemma C_smooth_pos (P₀ : ℕ) : 0 < C_smooth P₀ := by
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact div_pos (by positivity) (sub_pos.mpr hp2)

lemma G_val_lower {k1 P₀ R : ℕ} (hk1 : 1 ≤ k1) (hP0 : k1 ≤ P₀) (hR : 1 ≤ R) :
    (Real.log (R : ℝ) / ((k1 : ℝ) * C_smooth P₀)) ^ k1 ≤ G_val k1 P₀ R := by
  set U := Nat.floor ((R : ℝ) ^ ((1 : ℝ) / k1))
  have hlogR_nonneg : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  have hC_pos : 0 < C_smooth P₀ := C_smooth_pos P₀
  have hk1_pos : (0 : ℝ) < (k1 : ℝ) := by exact_mod_cast hk1
  have hrpow_pos : 0 < (R : ℝ) ^ ((1 : ℝ) / k1) := Real.rpow_pos_of_pos (by exact_mod_cast hR) _
  have hrpow_lt : (R : ℝ) ^ ((1 : ℝ) / k1) < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog_le : Real.log (R : ℝ) / (k1 : ℝ) ≤ Real.log ((U : ℝ) + 1) := by
    calc
      Real.log (R : ℝ) / (k1 : ℝ) = (1 / (k1 : ℝ)) * Real.log (R : ℝ) := by ring
      _ = Real.log ((R : ℝ) ^ ((1 : ℝ) / k1)) := (Real.log_rpow (by exact_mod_cast hR) _).symm
      _ ≤ Real.log ((U : ℝ) + 1) := Real.log_le_log hrpow_pos hrpow_lt.le
  have hcop_har := coprime_harmonic_ge P₀ U
  change Real.log ((U : ℝ) + 1) ≤ C_smooth P₀ * ∑ n ∈ (Finset.Icc 1 U).filter
      (fun n => ∀ p ∈ n.primeFactors, P₀ < p), (1 : ℝ) / n at hcop_har
  have hdiv_le : Real.log (R : ℝ) / ((k1 : ℝ) * C_smooth P₀) ≤
      ∑ n ∈ (Finset.Icc 1 U).filter (fun n => ∀ p ∈ n.primeFactors, P₀ < p), (1 : ℝ) / n := by
    rw [← div_div, div_le_iff₀ hC_pos]
    calc
      Real.log (R : ℝ) / (k1 : ℝ) ≤ Real.log ((U : ℝ) + 1) := hlog_le
      _ ≤ _ := hcop_har
      _ = (∑ n ∈ (Finset.Icc 1 U).filter (fun n => ∀ p ∈ n.primeFactors, P₀ < p), (1 : ℝ) / n) *
            C_smooth P₀ := mul_comm _ _
  have hpow_le : (Real.log (R : ℝ) / ((k1 : ℝ) * C_smooth P₀)) ^ k1 ≤
      (∑ n ∈ (Finset.Icc 1 U).filter (fun n => ∀ p ∈ n.primeFactors, P₀ < p), (1 : ℝ) / n) ^ k1 :=
    pow_le_pow_left₀ (div_nonneg hlogR_nonneg (mul_pos hk1_pos hC_pos).le) hdiv_le k1
  exact hpow_le.trans (pow_coprime_sum_le_G hk1 hP0 hR)

lemma erdos_17_upper_BES {A : ℝ} (_hA : 0 < A) :
    (fun x : ℕ => (Erdos17.clusterPrimeCount x : ℝ)) =O[atTop]
      fun x : ℕ => (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  set K := max 1 (Nat.ceil A)
  have hK1 : 1 ≤ K := le_max_left 1 _
  have hAK : A ≤ (K : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast le_max_right 1 (Nat.ceil A))
  set P₀ := max (gapM K) ((K + 1) ^ 4)
  have hP0_gap : gapM K ≤ P₀ := le_max_left _ _
  have hP0_pow : (K + 1) ^ 4 ≤ P₀ := le_max_right _ _
  have hk1 : 1 ≤ K + 1 := Nat.succ_pos K
  have hP0_k1 : K + 1 ≤ P₀ := le_trans (Nat.le_self_pow (by decide) _) hP0_pow
  set c_G : ℝ := (1 / (6 * (K + 1 : ℝ) * C_smooth P₀)) ^ (K + 1)
  have hcG_pos : 0 < c_G := by
    have := C_smooth_pos P₀
    positivity
  set M_tup : ℝ := ((validTuples K).card : ℝ)
  set C_big : ℝ := (gapM K + 1 : ℝ) + M_tup * ((P₀ + 2 : ℝ) + c_G⁻¹ + 1)
  have hC_big_pos : 0 < C_big := by
    have hM0 : 0 ≤ M_tup := Nat.cast_nonneg _
    have hP00 : 0 ≤ (P₀ : ℝ) := Nat.cast_nonneg _
    have hgap0 : 0 ≤ (gapM K : ℝ) := Nat.cast_nonneg _
    positivity
  have hev_log1 : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hev_littleO : ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) ^ (K + 1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    have ho := (isLittleO_log_rpow_rpow_atTop (K + 1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 6)).comp_tendsto
      tendsto_natCast_atTop_atTop
    filter_upwards [ho.bound zero_lt_one, hev_log1, eventually_ge_atTop 1] with x hbound hlog1 hx1
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
    have h1 : 0 ≤ Real.log (x : ℝ) ^ (K + 1 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hlog1) _
    have h2 : 0 ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hx_pos.le _
    dsimp only [Function.comp_apply] at hbound
    rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2, one_mul] at hbound
    exact hbound
  rw [Asymptotics.isBigO_iff]
  refine ⟨C_big, ?_⟩
  filter_upwards [eventually_ge_atTop 512, hev_log1, hev_littleO] with x hx512 hlog1 hlog_x16
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx13_ge8 : (8 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    by_contra! hlt
    have h3 : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < (8 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hlt (Real.rpow_nonneg hx_pos.le _) (by decide)
    have heq : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (x : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
      norm_num
    have hx512_r : (512 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx512
    linarith [show (8 : ℝ) ^ 3 = 512 by norm_num]
  have hx16_ge2 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    by_contra! hlt
    have h6 : ((x : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 < (2 : ℝ) ^ 6 :=
      pow_lt_pow_left₀ hlt (Real.rpow_nonneg hx_pos.le _) (by decide)
    have heq : ((x : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = (x : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
      norm_num
    have hx512_r : (512 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx512
    linarith [show (2 : ℝ) ^ 6 = 64 by norm_num]
  set R := Nat.floor ((x : ℝ) ^ ((1 : ℝ) / 3))
  have hR_le : (R : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Nat.floor_le (Real.rpow_nonneg hx_pos.le _)
  have hR_ge_half : (1 / 2 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (R : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((x : ℝ) ^ ((1 : ℝ) / 3))
    linarith
  have hR_ge8 : 8 ≤ R := Nat.le_floor hx13_ge8
  have hR1 : 1 ≤ R := by omega
  have hR_ge_x16 : (x : ℝ) ^ ((1 : ℝ) / 6) ≤ (R : ℝ) := by
    have hmul13 : (x : ℝ) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hx_pos]
      norm_num
    calc
      (x : ℝ) ^ ((1 : ℝ) / 6) = 1 * (x : ℝ) ^ ((1 : ℝ) / 6) := (one_mul _).symm
      _ ≤ ((1 / 2 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 6)) * (x : ℝ) ^ ((1 : ℝ) / 6) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx_pos.le _)
      _ = (1 / 2 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) := by rw [hmul13]; ring
      _ ≤ (R : ℝ) := hR_ge_half
  have hlogR : (1 / 6 : ℝ) * Real.log (x : ℝ) ≤ Real.log (R : ℝ) := by
    calc
      (1 / 6 : ℝ) * Real.log (x : ℝ) = Real.log ((x : ℝ) ^ ((1 : ℝ) / 6)) :=
          (Real.log_rpow hx_pos _).symm
      _ ≤ Real.log (R : ℝ) := Real.log_le_log (Real.rpow_pos_of_pos hx_pos _) hR_ge_x16
  have hG_lb : c_G * Real.log (x : ℝ) ^ (K + 1) ≤ G_val (K + 1) P₀ R := by
    have h1 : (1 / (6 * (K + 1 : ℝ) * C_smooth P₀)) * Real.log (x : ℝ) ≤
        Real.log (R : ℝ) / (((K + 1 : ℕ) : ℝ) * C_smooth P₀) := by
      have hC := C_smooth_pos P₀
      have hk_r : (0 : ℝ) < (K + 1 : ℝ) := by positivity
      push_cast
      rw [le_div_iff₀ (mul_pos hk_r hC)]
      have heq : (1 / (6 * (K + 1 : ℝ) * C_smooth P₀)) * Real.log (x : ℝ) *
          (((K : ℝ) + 1) * C_smooth P₀) = (1 / 6 : ℝ) * Real.log (x : ℝ) := by
        field_simp
      rw [heq]
      exact hlogR
    have hpow : (1 / (6 * (K + 1 : ℝ) * C_smooth P₀) * Real.log (x : ℝ)) ^ (K + 1) ≤
        (Real.log (R : ℝ) / (((K + 1 : ℕ) : ℝ) * C_smooth P₀)) ^ (K + 1) :=
      pow_le_pow_left₀ (by have := C_smooth_pos P₀; positivity) h1 (K + 1)
    rw [mul_pow] at hpow
    exact hpow.trans (G_val_lower hk1 hP0_k1 hR1)
  have hG_lb_pos : 0 < c_G * Real.log (x : ℝ) ^ (K + 1) :=
    mul_pos hcG_pos (pow_pos (by linarith) _)
  have hx_div_G : (x : ℝ) / G_val (K + 1) P₀ R ≤
      c_G⁻¹ * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by
    have hdiv := div_le_div_of_nonneg_left hx_pos.le hG_lb_pos hG_lb
    calc
      (x : ℝ) / G_val (K + 1) P₀ R ≤ (x : ℝ) / (c_G * Real.log (x : ℝ) ^ (K + 1)) := hdiv
      _ = c_G⁻¹ * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by ring
  have hlogK_le_x16 : Real.log (x : ℝ) ^ (K + 1) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    have hcast : Real.log (x : ℝ) ^ (K + 1) = Real.log (x : ℝ) ^ ((K + 1 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    push_cast at hcast
    exact hcast ▸ hlog_x16
  have hx56_le : (x : ℝ) ^ ((5 : ℝ) / 6) ≤ (x : ℝ) / Real.log (x : ℝ) ^ (K + 1) := by
    have hlogK_pos : 0 < Real.log (x : ℝ) ^ (K + 1) := pow_pos (by linarith) _
    rw [le_div_iff₀ hlogK_pos]
    calc
      (x : ℝ) ^ ((5 : ℝ) / 6) * Real.log (x : ℝ) ^ (K + 1)
        ≤ (x : ℝ) ^ ((5 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) :=
            mul_le_mul_of_nonneg_left hlogK_le_x16 (Real.rpow_nonneg hx_pos.le _)
      _ = (x : ℝ) := by
            rw [← Real.rpow_add hx_pos]
            norm_num
  have hR52_le : ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 ≤ (x : ℝ) ^ ((5 : ℝ) / 6) := by
    have hR_pow : (R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((5 : ℝ) / 12) := by
      have h1 : (R : ℝ) ^ ((1 : ℝ) / 4) ≤ ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hR_le (by norm_num)
      calc
        (R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)
          ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 4) :=
            mul_le_mul hR_le h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hx_pos.le _)
        _ = (x : ℝ) ^ ((5 : ℝ) / 12) := by
            rw [← Real.rpow_mul hx_pos.le, ← Real.rpow_add hx_pos]
            norm_num
    calc
      ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 ≤ ((x : ℝ) ^ ((5 : ℝ) / 12)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          hR_pow 2
      _ = (x : ℝ) ^ ((5 : ℝ) / 6) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
          norm_num
  have hx13_le_x56 : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ ((5 : ℝ) / 6) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
  have h1_le_xdiv : 1 ≤ (x : ℝ) / Real.log (x : ℝ) ^ (K + 1) := by
    have hx56_ge1 : (1 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 6) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
    exact hx56_ge1.trans hx56_le
  have htuple_le : ∀ d ∈ validTuples K,
      (((Finset.Icc 0 x).filter (fun p => ∀ j : Fin (K + 1), (p - tupleShift d j).Prime)).card : ℝ) ≤
        ((P₀ + 2 : ℝ) + c_G⁻¹ + 1) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by
    intro d hd
    have hc_mono := validTuples_strictMono hd
    have hc_le : ∀ j, tupleShift d j ≤ P₀ := fun j => le_trans (le_of_lt (validTuples_lt_gapM hd j)) hP0_gap
    have hsel := selberg_prime_tuple_upper hc_mono hc_le hP0_pow hR1 (x := x)
    have hP0_bound : (P₀ + R + 1 : ℝ) ≤ (P₀ + 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by
      have hR_le_div : (R : ℝ) ≤ (x : ℝ) / Real.log (x : ℝ) ^ (K + 1) :=
        hR_le.trans (hx13_le_x56.trans hx56_le)
      have hP0_nonneg : 0 ≤ (P₀ : ℝ) + 1 := by positivity
      calc
        (P₀ + R + 1 : ℝ) = ((P₀ : ℝ) + 1) * 1 + (R : ℝ) := by ring
        _ ≤ ((P₀ : ℝ) + 1) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) +
              ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1_le_xdiv hP0_nonneg) hR_le_div
        _ = (P₀ + 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by ring
    have herr_bound : ((R : ℝ) * (R : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 ≤ (x : ℝ) / Real.log (x : ℝ) ^ (K + 1) :=
      hR52_le.trans hx56_le
    linarith
  have hsum_tuples : ∑ d ∈ validTuples K,
      (((Finset.Icc 0 x).filter (fun p => ∀ j : Fin (K + 1), (p - tupleShift d j).Prime)).card : ℝ) ≤
      M_tup * ((P₀ + 2 : ℝ) + c_G⁻¹ + 1) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by
    calc
      _ ≤ ∑ _d ∈ validTuples K, ((P₀ + 2 : ℝ) + c_G⁻¹ + 1) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) :=
          Finset.sum_le_sum htuple_le
      _ = M_tup * ((P₀ + 2 : ℝ) + c_G⁻¹ + 1) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hcount_le : (Erdos17.clusterPrimeCount x : ℝ) ≤ C_big * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by
    have h1 := clusterPrimeCount_le_tuples K x
    have hgap : (gapM K + 1 : ℝ) ≤ (gapM K + 1 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ (K + 1)) := by
      have : 0 ≤ (gapM K + 1 : ℝ) := by positivity
      simpa using mul_le_mul_of_nonneg_left h1_le_xdiv this
    linarith
  have hlog_pow_le : Real.log (x : ℝ) ^ A ≤ Real.log (x : ℝ) ^ (K + 1) := by
    have hcast : Real.log (x : ℝ) ^ (K + 1) = Real.log (x : ℝ) ^ ((K + 1 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    rw [hcast]
    refine Real.rpow_le_rpow_of_exponent_le hlog1 ?_
    push_cast
    linarith
  have hdiv_A : (x : ℝ) / Real.log (x : ℝ) ^ (K + 1) ≤ (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_le_div_of_nonneg_left hx_pos.le (Real.rpow_pos_of_pos (by linarith) A) hlog_pow_le
  have hnorm_lhs : ‖(Erdos17.clusterPrimeCount x : ℝ)‖ = (Erdos17.clusterPrimeCount x : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg _)
  have hnorm_rhs : ‖(x : ℝ) / Real.log (x : ℝ) ^ A‖ = (x : ℝ) / Real.log (x : ℝ) ^ A :=
    Real.norm_of_nonneg (div_nonneg hx_pos.le (Real.rpow_nonneg (zero_le_one.trans hlog1) A))
  rw [hnorm_lhs, hnorm_rhs]
  exact hcount_le.trans (mul_le_mul_of_nonneg_left hdiv_A hC_big_pos.le)

end Erdos17BES

theorem OMA.solution : type_of% @Erdos17.erdos_17.variants.upper_BES :=
  @Erdos17BES.erdos_17_upper_BES
