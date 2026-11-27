import FormalConjectures.ErdosProblems.«470»

/-!
An odd abundant number with at most five distinct prime factors must be
divisible by 3. If 3 occurs only once, it must also be divisible by 5.
This leaves two families of primitive abundant numbers for the subset-sum
part of the theorem of Liddy and Riedl. The least-divisor argument follows
the first reduction of this problem.

Credit: @LoopsGod
-/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2

open Finset

private lemma prime_power_sum_le {p : ℕ} (hp : 1 < p) (a : ℕ) {w : ℚ}
    (hw : (p : ℚ) ≤ w * (p - 1)) :
    (∑ j ∈ range (a + 1), (p : ℚ) ^ j) ≤ w * (p : ℚ) ^ a := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  apply (mul_le_mul_iff_left₀ (sub_pos.mpr hp')).mp
  rw [geom_sum_mul, pow_succ]
  have h := mul_le_mul_of_nonneg_right hw (show 0 ≤ (p : ℚ) ^ a by positivity)
  linarith only [h]

/- Each prime contributes at most a baseline factor b, times a correction
for the primes in E. Missing exceptional primes can only decrease the bound. -/
private lemma abundancy_bound {n : ℕ} (hn : 0 < n) (hc : n.primeFactors.card ≤ 5)
    (b : ℚ) (hb : 1 ≤ b) (E : Finset ℕ) (c : ℕ → ℚ)
    (hcorr : ∀ p ∈ E, 1 ≤ c p)
    (hlocal : ∀ p ∈ n.primeFactors, (∑ j ∈ range (n.factorization p + 1), (p : ℚ) ^ j) ≤
      b * (if p ∈ E then c p else 1) * (p : ℚ) ^ n.factorization p) :
    n.abundancyIndex ≤ b ^ 5 * ∏ p ∈ E, c p := by
  have hs : (∑ d ∈ n.divisors, (d : ℚ)) =
      ∏ p ∈ n.primeFactors, ∑ j ∈ range (n.factorization p + 1), (p : ℚ) ^ j := by
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℚ)) (Nat.sum_divisors hn.ne')
  have hnprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
  have hsub : n.primeFactors.filter (· ∈ E) ⊆ E :=
    fun _ hp => (mem_filter.mp hp).2
  have hexc : (∏ p ∈ n.primeFactors, if p ∈ E then c p else 1) ≤ ∏ p ∈ E, c p := by
    rw [← prod_filter]
    exact prod_le_prod_of_subset_of_one_le hsub
      (fun p hp => (hcorr p (hsub hp)).trans' zero_le_one) (fun p hp _ => hcorr p hp)
  rw [Nat.abundancyIndex, div_le_iff₀ (show 0 < (n : ℚ) by exact_mod_cast hn)]
  push_cast
  calc
    _ = _ := hs
    _ ≤ ∏ p ∈ n.primeFactors,
        (b * (if p ∈ E then c p else 1) * (p : ℚ) ^ n.factorization p) :=
      prod_le_prod (fun _ _ => sum_nonneg fun _ _ => by positivity) hlocal
    _ = (b ^ n.primeFactors.card *
          (∏ p ∈ n.primeFactors, if p ∈ E then c p else 1)) * n := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, ← hnprod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul (pow_le_pow_right₀ hb hc) hexc _ (by positivity)
      apply prod_nonneg
      intro p _
      split_ifs with h
      · exact (hcorr p h).trans' zero_le_one
      · norm_num

/-- With no prime factor 2 or 3, the two largest possible geometric
factors are 5/4 and 7/6. Each of the remaining factors is at most 11/10. -/
lemma three_dvd_of_odd_abundant {n : ℕ} (ho : Odd n) (ha : n.Abundant)
    (hc : n.primeFactors.card ≤ 5) : 3 ∣ n := by
  by_contra h3
  let E : Finset ℕ := {5, 7}
  let c : ℕ → ℚ := fun p => if p = 5 then 25 / 22 else 35 / 33
  have hsmall : ∀ p ∈ E, 1 ≤ c p := by
    intro p _
    dsimp [c]
    split <;> norm_num
  have h := abundancy_bound ho.pos hc (11 / 10) (by norm_num) E c hsmall (by
    intro p hp
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    apply prime_power_sum_le hprime.one_lt
    by_cases h5 : p = 5
    · subst p; norm_num [E, c]
    by_cases h7 : p = 7
    · subst p; norm_num [E, c]
    have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
    have hn3 : p ≠ 3 := by rintro rfl; exact h3 hdvd
    have h11 : 11 ≤ p := by
      by_contra! hl
      interval_cases p <;> norm_num at *
    have h11' : (11 : ℚ) ≤ p := by exact_mod_cast h11
    simp [E, h5, h7]
    linarith)
  norm_num [E, c] at h
  linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]

/-- If 3 occurs only once, its divisor-sum factor is 4/3. Without 5 the
other four factors are bounded by 7/6, 11/10, 13/12 and 17/16. -/
lemma five_dvd_of_nine_not_dvd {n : ℕ} (ho : Odd n) (ha : n.Abundant)
    (hc : n.primeFactors.card ≤ 5) (h9 : ¬ 9 ∣ n) : 5 ∣ n := by
  by_contra h5
  let E : Finset ℕ := {3, 7, 11, 13}
  let c : ℕ → ℚ := fun p =>
    if p = 3 then 64 / 51 else if p = 7 then 56 / 51 else if p = 11 then 88 / 85 else 52 / 51
  have hsmall : ∀ p ∈ E, 1 ≤ c p := by
    intro p _
    dsimp [c]
    split_ifs <;> norm_num
  have h := abundancy_bound ho.pos hc (17 / 16) (by norm_num) E c hsmall (by
    intro p hp
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    by_cases h3 : p = 3
    · subst p
      have hexp : n.factorization 3 = 1 := by
        have hpos := (Nat.Prime.pow_dvd_iff_le_factorization hprime ho.pos.ne' (k := 1)).mp
          (by simpa using hdvd)
        have hlt : ¬ 2 ≤ n.factorization 3 := fun h =>
          h9 ((hprime.pow_dvd_iff_le_factorization ho.pos.ne').mpr h)
        omega
      norm_num [hexp, E, c, sum_range_succ]
    apply prime_power_sum_le hprime.one_lt
    by_cases h7 : p = 7
    · subst p; norm_num [E, c]
    by_cases h11 : p = 11
    · subst p; norm_num [E, c]
    by_cases h13 : p = 13
    · subst p; norm_num [E, c]
    have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
    have hn5 : p ≠ 5 := by rintro rfl; exact h5 hdvd
    have h17 : 17 ≤ p := by
      by_contra! hl
      interval_cases p <;> norm_num at *
    have h17' : (17 : ℚ) ≤ p := by exact_mod_cast h17
    simp [E, h3, h7, h11, h13]
    linarith)
  norm_num [E, c] at h
  linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]

/-- Every odd abundant number with at most five distinct prime factors
is a multiple of 9 or 15. -/
theorem nine_or_fifteen_dvd {n : ℕ} (ho : Odd n) (ha : n.Abundant)
    (hc : n.primeFactors.card ≤ 5) : 9 ∣ n ∨ 15 ∣ n := by
  by_cases h9 : 9 ∣ n
  · exact Or.inl h9
  · exact Or.inr ((show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd
      (three_dvd_of_odd_abundant ho ha hc) (five_dvd_of_nine_not_dvd ho ha hc h9))

private lemma pseudoperfect_multiple {d n : ℕ} (hd : d ∣ n) (hn : 0 < n)
    (h : d.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨_, s, hsub, hsum⟩ := h
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  let scale : ℕ ↪ ℕ := ⟨(· * k), fun _ _ h => Nat.eq_of_mul_eq_mul_right hk h⟩
  refine ⟨hn, s.map scale, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨had, halt⟩ := Nat.mem_properDivisors.mp (hsub ha)
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right had k, Nat.mul_lt_mul_of_pos_right halt hk⟩
  · rw [sum_map]
    change (∑ a ∈ s, a * k) = d * k
    rw [← sum_mul, hsum]

/-- Odd primitive abundant multiples of 15 in which 3 occurs exactly once. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → 15 ∣ m → ¬ 9 ∣ m → m.Pseudoperfect

/-- Odd primitive abundant multiples of 9. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → 9 ∣ m → m.Pseudoperfect

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  classical
  intro h15 h9 n ho hw
  have hset : {p | p ∈ n.divisors ∧ p.Prime} = (n.primeFactors : Set ℕ) := by
    ext p
    simp only [Set.mem_ofPred_eq, mem_coe, Nat.mem_primeFactors, Nat.mem_divisors]
    tauto
  rw [hset, Set.ncard_coe_finset]
  by_contra! hcard
  have hex : ∃ m : ℕ, m ∣ n ∧ ¬ m.Deficient :=
    ⟨n, dvd_rfl, fun h => (not_lt_of_gt hw.1) h⟩
  let m := Nat.find hex
  obtain ⟨hdvd, hnd⟩ := Nat.find_spec hex
  change m ∣ n at hdvd
  change ¬ m.Deficient at hnd
  have hodd : Odd m := ho.of_dvd_nat hdvd
  have hproper : ∀ d ∈ m.properDivisors, d.Deficient := by
    intro d hd
    obtain ⟨hdm, hlt⟩ := Nat.mem_properDivisors.mp hd
    by_contra hnot
    exact (not_le_of_gt hlt) (Nat.find_min' hex ⟨hdm.trans hdvd, hnot⟩)
  apply hw.2
  apply pseudoperfect_multiple hdvd ho.pos
  by_cases ha : m.Abundant
  · have hc : m.primeFactors.card ≤ 5 :=
      (card_le_card (Nat.primeFactors_mono hdvd ho.pos.ne')).trans (by omega)
    by_cases hs : 9 ∣ m
    · exact h9 m hodd ha hc hproper hs
    · exact h15 m hodd ha hc hproper ((nine_or_fifteen_dvd hodd ha hc).resolve_left hs) hs
  · exact ((Nat.perfect_iff_not_abundant_and_not_deficient hodd.pos.ne).2
      ⟨ha, hnd⟩).pseudoperfect

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2
