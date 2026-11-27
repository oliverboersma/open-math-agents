import FormalConjectures.ErdosProblems.«542»

-- Reduction Erdos542.erdos_542.variants.only_two.R1 of Erdős Problem 542 — only two
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Fractional loss against uncovered integers

Let `A ⊆ {1, …, n}` with `lcm(a, b) > n` for distinct `a, b ∈ A`. The target says that
`∑ 1/a > 1` forces `A = {2, 3, 5}` or `A = {3, 4, 5, 7, 11}`. Those two sets need `n = 5` and
`n = 11`, so for `n ≥ 12` the target is the bound `∑ 1/a ≤ 1`.

This file proves, with no hypothesis:

* the target for every `n ≤ 11`, by a kernel computation over the `2 ^ 11` subsets of
  `{1, …, 11}`;
* the bound `∑ 1/a ≤ 1` for every `n ≥ 6` when `2 ∈ A`: then all other members are odd and
  exceed `n / 2`, and the odd integers in `(n / 2, n]` have reciprocal sum at most `1 / 2`
  (a two-range estimate for `n ≥ 64`, a kernel computation for `6 ≤ n ≤ 63`);
* the counting identity `∑ ⌊n / a⌋ + #uncovered = n`, where `uncovered` is the set of
  `m ≤ n` divisible by no member of `A`: distinct members have no common multiple up to `n`.
  Since `n / a = ⌊n / a⌋ + (n mod a) / a`, this gives
  `n * ∑ 1/a = n - #uncovered + ∑ (n mod a) / a`, so `∑ 1/a ≤ 1` is equivalent to
  `∑ (n mod a) / a ≤ #uncovered`.

What is left, for `n ≥ 12`, is split by the smallest member of `A`. Two of the three remaining
cases are stated through the identity above: the total fractional loss is at most the number of
uncovered integers.

* `3 ∈ A`: a weighting argument proved here bounds the other reciprocals by a sum that does not
  depend on `A`; what is left is a one-variable numerical inequality, elementary but not carried
  out here.
* `2, 3 ∉ A` and `A` has a member `a ≤ √n` (at most one, because `a * b ≥ lcm(a, b) > n`): open.
* every member of `A` exceeds `√n`: open.

An exact search found no set with `∑ 1/a > 1` other than the two above for `n ≤ 187`.
-/

namespace OMA.R_Erdos542_erdos_542_variants_only_two_R1

/-- The numerical inequality behind the case `3 ∈ A`: for `n ≥ 12`, the reciprocals of the
non-multiples of `3` in `(n / 2, n]`, plus half the reciprocals of the non-multiples of `3` in
`(n / 3, n / 2]`, sum to at most `2 / 3`. The sum tends to
`(2/3) log 2 + (1/3) log (3/2) ≈ 0.597`; numerically it is at most `0.6472` (at `n = 20`) for
`12 ≤ n ≤ 20000`, while at `n = 11` it is `0.6838`. Elementary, not carried out here. -/
def H1 : Prop :=
  ∀ n : ℕ, 12 ≤ n →
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m +
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) ≤ 2 / 3

/-- The case with a small element other than `2` and `3`: some member of `A` is at most `√n`. -/
def H2 : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), 12 ≤ n → Erdos542.IsLcmFree n A → 2 ∉ A → 3 ∉ A →
    (∃ a ∈ A, a * a ≤ n) →
    ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a ≤ ((Erdos542.uncovered n A).card : ℚ)

/-- The case without a small element: every member of `A` exceeds `√n`. -/
def H3 : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), 12 ≤ n → Erdos542.IsLcmFree n A → (∀ a ∈ A, n < a * a) →
    ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a ≤ ((Erdos542.uncovered n A).card : ℚ)

/-- The multiples of `a` in `{1, …, n}` number `⌊n / a⌋`. -/
lemma covered_card (n a : ℕ) : ((Finset.Icc 1 n).filter (fun m => a ∣ m)).card = n / a := by
  have h : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [h]
  exact Nat.Ioc_filter_dvd_card_eq_div n a

/-- Distinct members of `A` have no common multiple up to `n`, so the covered integers are counted
by `∑ ⌊n / a⌋`; together with the uncovered ones they make up `{1, …, n}`. -/
lemma count_identity {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) :
    ∑ a ∈ A, n / a + (Erdos542.uncovered n A).card = n := by
  classical
  have hdisj : (A : Set ℕ).PairwiseDisjoint
      (fun a => (Finset.Icc 1 n).filter (fun m => a ∣ m)) := by
    intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro m hma hmb
    rw [Finset.mem_filter, Finset.mem_Icc] at hma hmb
    have hl : Nat.lcm a b ∣ m := Nat.lcm_dvd hma.2 hmb.2
    have hle : Nat.lcm a b ≤ m := Nat.le_of_dvd (by omega) hl
    have hlt : n < Nat.lcm a b := hA.2 ha hb hab
    omega
  have hcov : (A.biUnion (fun a => (Finset.Icc 1 n).filter (fun m => a ∣ m))).card =
      ∑ a ∈ A, n / a := by
    rw [Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun a _ => covered_card n a)
  have hunion : A.biUnion (fun a => (Finset.Icc 1 n).filter (fun m => a ∣ m)) =
      (Finset.Icc 1 n).filter (fun m => ∃ a ∈ A, a ∣ m) := by
    ext m
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨a, ha, hm, hd⟩
      exact ⟨hm, a, ha, hd⟩
    · rintro ⟨hm, a, ha, hd⟩
      exact ⟨a, ha, hm, hd⟩
  have hunc : Erdos542.uncovered n A =
      (Finset.Icc 1 n).filter (fun m => ¬ ∃ a ∈ A, a ∣ m) := by
    unfold Erdos542.uncovered
    apply Finset.filter_congr
    intro m _
    constructor
    · rintro h ⟨a, ha, hd⟩
      exact h a ha hd
    · intro h a ha hd
      exact h ⟨a, ha, hd⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 n)
    (fun m => ∃ a ∈ A, a ∣ m)
  rw [← hcov, hunion, hunc, hsplit]
  simp

/-- If the total fractional loss `∑ (n mod a) / a` is at most the number of uncovered integers,
then the reciprocal sum is at most `1`. (The two quantities differ by exactly `n (∑ 1/a - 1)`.) -/
lemma sum_le_one_of_loss {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) (hn : 0 < n)
    (h : ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a ≤ ((Erdos542.uncovered n A).card : ℚ)) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ 1 := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => by
    have := Finset.mem_Icc.mp (hA.1 ha)
    omega
  have hq : ∑ a ∈ A, (1 : ℚ) / a ≤ 1 := by
    have hterm : ∀ a ∈ A, (n : ℚ) * ((1 : ℚ) / a) =
        ((n / a : ℕ) : ℚ) + ((n % a : ℕ) : ℚ) / a := by
      intro a ha
      have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (hpos a ha).ne'
      have hdm : (n : ℚ) = (a : ℚ) * ((n / a : ℕ) : ℚ) + ((n % a : ℕ) : ℚ) := by
        exact_mod_cast (Nat.div_add_mod n a).symm
      field_simp
      linarith
    have hsum : (n : ℚ) * ∑ a ∈ A, (1 : ℚ) / a =
        (∑ a ∈ A, ((n / a : ℕ) : ℚ)) + ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hterm
    have hcount : (∑ a ∈ A, ((n / a : ℕ) : ℚ)) + ((Erdos542.uncovered n A).card : ℚ) = n := by
      exact_mod_cast count_identity hA
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have hmul : (n : ℚ) * ∑ a ∈ A, (1 : ℚ) / a ≤ n * 1 := by
      rw [hsum]
      linarith
    exact le_of_mul_le_mul_left hmul hn'
  have hcast : (∑ a ∈ A, (1 : ℝ) / a) = ((∑ a ∈ A, (1 : ℚ) / a : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  exact_mod_cast hq

/-- Kernel computation over the `2 ^ 11` subsets of `{1, …, 11}`. -/
lemma small_dec : ∀ A ∈ (Finset.Icc 1 11).powerset, 27720 < ∑ a ∈ A, 27720 / a →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ c ∈ A, c < Nat.lcm a b) →
    A = {2, 3, 5} ∨ A = {3, 4, 5, 7, 11} := by
  decide +kernel

lemma dvd_27720 : ∀ a ∈ Finset.Icc 1 11, a ∣ 27720 := by
  decide

/-- The conjecture for `n ≤ 11`. -/
lemma small {n : ℕ} {A : Finset ℕ} (hn : n ≤ 11) (hA : Erdos542.IsLcmFree n A)
    (hsum : 1 < ∑ a ∈ A, (1 : ℝ) / a) : A = {2, 3, 5} ∨ A = {3, 4, 5, 7, 11} := by
  have hsub : A ⊆ Finset.Icc 1 11 := fun a ha => by
    have := Finset.mem_Icc.mp (hA.1 ha)
    exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  have hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ c ∈ A, c < Nat.lcm a b := by
    intro a ha b hb hab c hc
    have h1 : n < Nat.lcm a b := hA.2 ha hb hab
    have h2 := (Finset.mem_Icc.mp (hA.1 hc)).2
    omega
  have hnat : 27720 < ∑ a ∈ A, 27720 / a := by
    have hterm : ∀ a ∈ A, ((27720 / a : ℕ) : ℝ) = 27720 * ((1 : ℝ) / a) := by
      intro a ha
      have hd := dvd_27720 a (hsub ha)
      have ha0 : (a : ℝ) ≠ 0 := by
        have := (Finset.mem_Icc.mp (hsub ha)).1
        exact_mod_cast (by omega : a ≠ 0)
      rw [Nat.cast_div hd ha0]
      push_cast
      ring
    have hcast : ((∑ a ∈ A, 27720 / a : ℕ) : ℝ) = 27720 * ∑ a ∈ A, (1 : ℝ) / a := by
      rw [Nat.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl hterm
    have hr : (27720 : ℝ) < ((∑ a ∈ A, 27720 / a : ℕ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast hr
  exact small_dec A (Finset.mem_powerset.mpr hsub) hnat hpair

/-- Kernel computation: the odd integers in `(n / 2, n]` have reciprocal sum at most `1 / 2`,
for `6 ≤ n ≤ 63`. -/
lemma odd_half_small : ∀ n ∈ Finset.Icc (6 : ℕ) 63,
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℚ) / (b : ℚ) ≤ 1 / 2 := by
  decide +kernel

/-- The same bound for `n ≥ 64`, splitting `(n / 2, n]` at `3 n / 4`. -/
lemma odd_half_large {n : ℕ} (hn : 64 ≤ n) :
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℝ) / b ≤ 1 / 2 := by
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b) :=
    ⟨_, rfl⟩
  rw [← hS]
  have hmem : ∀ b ∈ S, 1 ≤ b ∧ b ≤ n ∧ b % 2 = 1 ∧ n < 2 * b := by
    intro b hb
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hb
    exact ⟨hb.1.1, hb.1.2, hb.2.1, hb.2.2⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : ∑ b ∈ S.filter (fun b => 4 * b ≤ 3 * n), (1 : ℝ) / b ≤
      ((S.filter (fun b => 4 * b ≤ 3 * n)).card : ℝ) * (2 / n) := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro b hb
    have hb' := hmem b (Finset.mem_filter.mp hb).1
    have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_le_div_iff₀ hbR hnR]
    have hle : (n : ℝ) ≤ 2 * b := by exact_mod_cast (by omega : n ≤ 2 * b)
    linarith
  have h2 : ∑ b ∈ S.filter (fun b => ¬ 4 * b ≤ 3 * n), (1 : ℝ) / b ≤
      ((S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card : ℝ) * (4 / (3 * n)) := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro b hb
    have hb1 := Finset.mem_filter.mp hb
    have hb' := hmem b hb1.1
    have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_le_div_iff₀ hbR (by positivity)]
    have hle : (3 * n : ℝ) ≤ 4 * b := by exact_mod_cast (by omega : 3 * n ≤ 4 * b)
    linarith
  have c1 : 8 * (S.filter (fun b => 4 * b ≤ 3 * n)).card ≤ n + 14 := by
    have hc : (S.filter (fun b => 4 * b ≤ 3 * n)).card ≤ (Finset.Icc (n / 4) (3 * n / 8)).card := by
      apply Finset.card_le_card_of_injOn (fun b => b / 2)
      · intro b hb
        have hb1 := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        have hb' := hmem b hb1.1
        have hb2 := hb1.2
        have hI : b / 2 ∈ Finset.Icc (n / 4) (3 * n / 8) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact Finset.mem_coe.mpr hI
      · intro b hb c hc hbc
        have hb1 := hmem b (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
        have hc1 := hmem c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).1
        have hbc' : b / 2 = c / 2 := hbc
        omega
    rw [Nat.card_Icc] at hc
    omega
  have c2 : 8 * (S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card ≤ n + 11 := by
    have hc : (S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card ≤
        (Finset.Icc (3 * n / 8) ((n - 1) / 2)).card := by
      apply Finset.card_le_card_of_injOn (fun b => b / 2)
      · intro b hb
        have hb1 := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        have hb' := hmem b hb1.1
        have hb2 := hb1.2
        have hI : b / 2 ∈ Finset.Icc (3 * n / 8) ((n - 1) / 2) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact Finset.mem_coe.mpr hI
      · intro b hb c hc hbc
        have hb1 := hmem b (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
        have hc1 := hmem c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).1
        have hbc' : b / 2 = c / 2 := hbc
        omega
    rw [Nat.card_Icc] at hc
    omega
  have c1R : (8 : ℝ) * ((S.filter (fun b => 4 * b ≤ 3 * n)).card : ℝ) ≤ n + 14 := by
    exact_mod_cast c1
  have c2R : (8 : ℝ) * ((S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card : ℝ) ≤ n + 11 := by
    exact_mod_cast c2
  have hn64 : (64 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Finset.sum_filter_add_sum_filter_not S (fun b => 4 * b ≤ 3 * n)]
  have key : ∀ x y : ℝ, x * (2 / n) + y * (4 / (3 * n)) = (6 * x + 4 * y) / (3 * n) := by
    intro x y
    field_simp
    ring
  have hfin : ((S.filter (fun b => 4 * b ≤ 3 * n)).card : ℝ) * (2 / n) +
      ((S.filter (fun b => ¬ 4 * b ≤ 3 * n)).card : ℝ) * (4 / (3 * n)) ≤ 1 / 2 := by
    rw [key, div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- The odd integers in `(n / 2, n]` have reciprocal sum at most `1 / 2`, for every `n ≥ 6`. -/
lemma odd_half {n : ℕ} (hn : 6 ≤ n) :
    ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℝ) / b ≤ 1 / 2 := by
  by_cases h : n ≤ 63
  · have hq := odd_half_small n (Finset.mem_Icc.mpr ⟨hn, h⟩)
    have hr : ((∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b),
        (1 : ℚ) / (b : ℚ) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    push_cast at hr
    exact hr
  · exact odd_half_large (by omega)

/-- The bound `∑ 1/a ≤ 1` for every `n ≥ 6` when `2 ∈ A`. -/
lemma two_mem {n : ℕ} {A : Finset ℕ} (hn : 6 ≤ n) (hA : Erdos542.IsLcmFree n A) (h2 : 2 ∈ A) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ 1 := by
  have hsub : A.erase 2 ⊆ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b) := by
    intro b hb
    obtain ⟨hb2, hbA⟩ := Finset.mem_erase.mp hb
    have hbI := Finset.mem_Icc.mp (hA.1 hbA)
    have hl : n < Nat.lcm 2 b := hA.2 h2 hbA (Ne.symm hb2)
    have hodd : b % 2 = 1 := by
      by_contra hne
      have hd : 2 ∣ b := by omega
      have hle : Nat.lcm 2 b ≤ b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd hd (dvd_refl b))
      omega
    have hle : Nat.lcm 2 b ≤ 2 * b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd_mul 2 b)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hbI, hodd, by omega⟩
  have h := odd_half hn
  have hmono : ∑ b ∈ A.erase 2, (1 : ℝ) / b ≤
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => b % 2 = 1 ∧ n < 2 * b), (1 : ℝ) / b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by positivity)
  rw [← Finset.add_sum_erase A _ h2]
  have e : (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [e]
  linarith

/-- The case `3 ∈ A`, reduced to a sum that does not depend on `A`. Every other member `b`
satisfies `3 ∤ b` and `b > n / 3`, and `A` contains no pair `b, 2 b`. Give weight `1 / m` to each
`m` in `(n / 2, n]` and `1 / (2 b)` to each `b` in `(n / 3, n / 2]`: a member `b > n / 2` is paid
by its own weight, a member `b ≤ n / 2` by its weight and that of `2 b`, and no integer pays
twice. -/
lemma three_mem_bound {n : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A) (h3 : 3 ∈ A) :
    ∑ b ∈ A.erase 3, (1 : ℝ) / b ≤
      ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m +
        ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
          (1 : ℝ) / (2 * b) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B = A.erase 3 := ⟨_, rfl⟩
  rw [← hB]
  have hmem : ∀ b ∈ B, b ∈ A ∧ 1 ≤ b ∧ b ≤ n ∧ b % 3 ≠ 0 ∧ n < 3 * b := by
    intro b hb
    rw [hB] at hb
    obtain ⟨hb3, hbA⟩ := Finset.mem_erase.mp hb
    have hbI := Finset.mem_Icc.mp (hA.1 hbA)
    have hl : n < Nat.lcm 3 b := hA.2 h3 hbA (Ne.symm hb3)
    have hnd : b % 3 ≠ 0 := by
      intro h0
      have hd : 3 ∣ b := Nat.dvd_of_mod_eq_zero h0
      have hle : Nat.lcm 3 b ≤ b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd hd (dvd_refl b))
      omega
    have hle : Nat.lcm 3 b ≤ 3 * b := Nat.le_of_dvd (by omega) (Nat.lcm_dvd_mul 3 b)
    exact ⟨hbA, hbI.1, hbI.2, hnd, by omega⟩
  have hnodouble : ∀ b ∈ B, 2 * b ∉ B := by
    intro b hb h2b
    have hb' := hmem b hb
    have h2b' := hmem (2 * b) h2b
    have hne : b ≠ 2 * b := by omega
    have hl : n < Nat.lcm b (2 * b) := hA.2 hb'.1 h2b'.1 hne
    have hle : Nat.lcm b (2 * b) ≤ 2 * b :=
      Nat.le_of_dvd (by omega) (Nat.lcm_dvd (Dvd.intro_left 2 rfl) (dvd_refl _))
    omega
  obtain ⟨Bh, hBh⟩ : ∃ Bh : Finset ℕ, Bh = B.filter (fun b => n < 2 * b) := ⟨_, rfl⟩
  obtain ⟨Bl, hBl⟩ : ∃ Bl : Finset ℕ, Bl = B.filter (fun b => ¬ n < 2 * b) := ⟨_, rfl⟩
  have hsplit : ∑ b ∈ Bh, (1 : ℝ) / b + ∑ b ∈ Bl, (1 : ℝ) / b = ∑ b ∈ B, (1 : ℝ) / b := by
    rw [hBh, hBl]
    exact Finset.sum_filter_add_sum_filter_not B (fun b => n < 2 * b) (fun b => (1 : ℝ) / b)
  have hBlmem : ∀ b ∈ Bl, b ∈ B ∧ 2 * b ≤ n := by
    intro b hb
    rw [hBl, Finset.mem_filter] at hb
    exact ⟨hb.1, by omega⟩
  have hBhmem : ∀ b ∈ Bh, b ∈ B ∧ n < 2 * b := by
    intro b hb
    rw [hBh, Finset.mem_filter] at hb
    exact hb
  obtain ⟨D, hD⟩ : ∃ D : Finset ℕ, D = Bl.image (fun b : ℕ => 2 * b) := ⟨_, rfl⟩
  have hlow : ∑ b ∈ Bl, (1 : ℝ) / b =
      ∑ m ∈ D, (1 : ℝ) / (m : ℝ) + ∑ b ∈ Bl, (1 : ℝ) / (2 * b) := by
    rw [hD, Finset.sum_image (fun x _ y _ (h : 2 * x = 2 * y) => by omega),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' := hmem b (hBlmem b hb).1
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    push_cast
    field_simp
    ring
  have hDmem : ∀ m ∈ D, ∃ b ∈ Bl, m = 2 * b := by
    intro m hm
    rw [hD] at hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨b, hb, rfl⟩
  have hdisj : Disjoint Bh D := by
    rw [Finset.disjoint_left]
    intro m hm hm2
    obtain ⟨b, hb, rfl⟩ := hDmem m hm2
    exact hnodouble b (hBlmem b hb).1 (hBhmem _ hm).1
  have hsub1 : Bh ∪ D ⊆ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0) := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · have h1 := hBhmem m hm
      have h2 := hmem m h1.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h2.2.1, h2.2.2.1⟩, h1.2, h2.2.2.2.1⟩
    · obtain ⟨b, hb, rfl⟩ := hDmem m hm
      have h1 := hBlmem b hb
      have h2 := hmem b h1.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2⟩, by omega, by omega⟩
  have hsub2 : Bl ⊆ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0) := by
    intro b hb
    have h1 := hBlmem b hb
    have h2 := hmem b h1.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h2.2.1, h2.2.2.1⟩, h2.2.2.2.2, h1.2, h2.2.2.2.1⟩
  have hle1 : ∑ m ∈ Bh, (1 : ℝ) / (m : ℝ) + ∑ m ∈ D, (1 : ℝ) / (m : ℝ) ≤
      ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun m _ _ => by positivity)
  have hle2 : ∑ b ∈ Bl, (1 : ℝ) / (2 * b) ≤
      ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun b _ _ => by positivity)
  linarith

theorem main : H1 → H2 → H3 → type_of% @Erdos542.erdos_542.variants.only_two := by
  intro h1 h2 h3 n A hA hsum
  by_cases hn : n ≤ 11
  · exact small hn hA hsum
  · exfalso
    have hn12 : 12 ≤ n := by omega
    have hle : ∑ a ∈ A, (1 : ℝ) / a ≤ 1 := by
      by_cases h2A : 2 ∈ A
      · exact two_mem (by omega) hA h2A
      · by_cases h3A : 3 ∈ A
        · have hb := three_mem_bound hA h3A
          have hnum := h1 n hn12
          rw [← Finset.add_sum_erase A _ h3A]
          have e : (1 : ℝ) / ((3 : ℕ) : ℝ) = 1 / 3 := by norm_num
          rw [e]
          linarith
        · apply sum_le_one_of_loss hA (by omega)
          by_cases hs : ∃ a ∈ A, a * a ≤ n
          · exact h2 n A hn12 hA h2A h3A hs
          · have hs' : ∀ a ∈ A, n < a * a := by
              intro a ha
              by_contra hc
              exact hs ⟨a, ha, by omega⟩
            exact h3 n A hn12 hA hs'
    linarith

end OMA.R_Erdos542_erdos_542_variants_only_two_R1
