import FormalConjectures.ErdosProblems.«688»
import Mathlib

section R1Section
-- Reduction Erdos688.erdos_688.variants.lglglg_over_lglg_is_big_o.R1 of Erdős Problem 688 — lglglg over lglg is big o
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
Rankin-type covering reduction of `ε_n ≫ logloglog n / loglog n`

Erdős [Er80, p. 106] says that `ε_n ≫ log log log n / log log n` is not difficult. We prove the
covering construction behind it and isolate its three analytic inputs as hypotheses:

1. `H1` (Mertens-type): `∑_{t < p ≤ t²} 1/p ≥ 1/20` for all large `t`
   (the truth is `→ log 2`).
2. `H2` (Rankin / de Bruijn smooth-number bound): for some `A > 0`, the number of
   `n^{logloglog n / (A loglog n)}`-smooth integers in `[1, n]` is at most `n / (16 log n)`
   for large `n` (the truth is `n (log n)^{-A(1+o(1))}`).
3. `H3` (Chebyshev-type): `[n/4, n]` contains at least `n / (4 log n)` primes for large `n`.

The construction (proved here, unconditionally): put `δ = logloglog n / (A' loglog n)`,
`ε = δ / 2^60`, `z = ⌊n^ε⌋`, `w = z^(2^60) ≤ n^δ`.
* every prime `p ∈ (w, n/4]` takes the class `0`; the integers of `[1, n]` left over are
  `w`-smooth or are multiples of a prime `q ∈ (n/4, n]` (at most `3` per `q`);
* the primes `p ∈ (z, w]` take greedy classes (pigeonhole), which multiplies the number of
  survivors by at most `∏ (1 - 1/p) ≤ exp (-∑ 1/p) ≤ exp (-3) ≤ 1/8` (by `H1`, iterated 60 times);
* each remaining survivor is matched injectively with its own prime `q ∈ (n/4, n]` (by `H2`, `H3`).
All primes used exceed `z ≥ n^ε - 1`, so `ε_n ≥ ε`, which gives the bound.
-/

namespace OMA.Erdos688R1

open Real Filter Finset

/-- Mertens-type lower bound: the reciprocals of the primes in `(t, t²]` sum to at least `1/20`
for every sufficiently large `t`. -/
def H1 : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
    (1 : ℝ) / 20 ≤ ∑ p ∈ (Finset.Ioc t (t ^ 2)).filter Nat.Prime, ((p : ℝ))⁻¹

/-- Rankin-type smooth-number bound: for some `A > 0` and all large `n`, at most
`n / (16 log n)` integers `m ∈ [1, n]` have all their prime factors `≤ n ^ (logloglog n / (A loglog n))`. -/
def H2 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
    ((((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors,
        ((p : ℕ) : ℝ) ≤ (n : ℝ) ^ (Real.log (Real.log (Real.log (n : ℝ))) /
          (A * Real.log (Real.log (n : ℝ))))).card : ℕ) : ℝ) ≤
      (n : ℝ) / (16 * Real.log (n : ℝ))

/-- Chebyshev-type lower bound: for all large `n` there are at least `n / (4 log n)` primes in
`(⌊n/4⌋, n]`. -/
def H3 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (n : ℝ) / (4 * Real.log (n : ℝ)) ≤ (((Finset.Ioc (n / 4) n).filter Nat.Prime).card : ℝ)

/-- Greedy (pigeonhole) choice of classes: one class per modulus in `P` can be chosen so that the
survivors in `S` are at most `|S| ∏_{p ∈ P} (1 - 1/p)`. -/
lemma greedy (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (S : Finset ℕ) :
    ∃ a : ℕ → ℕ, (((S.filter fun m : ℕ => ∀ p ∈ P, ¬ (a p ≡ m [MOD p])).card : ℕ) : ℝ) ≤
      (S.card : ℝ) * ∏ p ∈ P, (1 - ((p : ℝ))⁻¹) := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert p P hpP ih =>
    obtain ⟨a, ha⟩ := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
    have hp : 0 < p := hP p (Finset.mem_insert_self p P)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    set T := S.filter fun m : ℕ => ∀ q ∈ P, ¬ (a q ≡ m [MOD q]) with hT
    obtain ⟨r, hr, hrT⟩ : ∃ r ∈ Finset.range p,
        (T.card : ℝ) / p ≤ (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ) := by
      apply Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      · intro m _
        exact Finset.mem_range.2 (Nat.mod_lt _ hp)
      · exact ⟨0, Finset.mem_range.2 hp⟩
      · rw [Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hpR.ne']
    have hrp : r < p := Finset.mem_range.1 hr
    refine ⟨Function.update a p r, ?_⟩
    have key : (S.filter fun m : ℕ => ∀ q ∈ insert p P, ¬ (Function.update a p r q ≡ m [MOD q])) =
        T.filter fun m : ℕ => ¬ (m % p = r) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp, hT,
        Function.update_self]
      have hrr : r % p = r := Nat.mod_eq_of_lt hrp
      constructor
      · rintro ⟨hmS, h1, h2⟩
        refine ⟨⟨hmS, fun q hq => ?_⟩, ?_⟩
        · have hqp : q ≠ p := fun h => hpP (h ▸ hq)
          simpa [Function.update_of_ne hqp] using h2 q hq
        · intro hm
          apply h1
          show r % p = m % p
          rw [hrr, hm]
      · rintro ⟨⟨hmS, h2⟩, h1⟩
        refine ⟨hmS, ?_, fun q hq => ?_⟩
        · intro h
          apply h1
          have : r % p = m % p := h
          rw [hrr] at this
          exact this.symm
        · have hqp : q ≠ p := fun h => hpP (h ▸ hq)
          simpa [Function.update_of_ne hqp] using h2 q hq
    rw [key]
    have hsub : T.filter (fun m : ℕ => m % p = r) ⊆ T := Finset.filter_subset _ _
    have hcard : (((T.filter fun m : ℕ => ¬ (m % p = r)).card : ℕ) : ℝ) =
        (T.card : ℝ) - (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not (s := T) (fun m : ℕ => m % p = r)
      have h' : (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ) +
          (((T.filter fun m : ℕ => ¬ (m % p = r)).card : ℕ) : ℝ) = (T.card : ℝ) := by
        exact_mod_cast h
      linarith
    rw [hcard, Finset.prod_insert hpP]
    have h1p : 0 ≤ 1 - ((p : ℝ))⁻¹ := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ this
    calc (T.card : ℝ) - (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ)
        ≤ T.card - T.card / p := by linarith
      _ = T.card * (1 - ((p : ℝ))⁻¹) := by ring
      _ ≤ (S.card * ∏ q ∈ P, (1 - ((q : ℝ))⁻¹)) * (1 - ((p : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_right ha h1p
      _ = S.card * ((1 - ((p : ℝ))⁻¹) * ∏ q ∈ P, (1 - ((q : ℝ))⁻¹)) := by ring

/-- `∏ (1 - 1/p) ≤ exp (-∑ 1/p)`. -/
lemma prod_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    ∏ p ∈ P, (1 - ((p : ℝ))⁻¹) ≤ Real.exp (-∑ p ∈ P, ((p : ℝ))⁻¹) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hP p hp
    rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ this
  · intro p _
    have := Real.add_one_le_exp (-((p : ℝ))⁻¹)
    linarith

/-- Iterating `H1` along `z, z², z⁴, …`. -/
lemma sum_recip_iter (T : ℕ)
    (hH1 : ∀ t : ℕ, T ≤ t → (1 : ℝ) / 20 ≤ ∑ p ∈ (Finset.Ioc t (t ^ 2)).filter Nat.Prime, ((p : ℝ))⁻¹)
    (z : ℕ) (hz : T ≤ z) (hz1 : 1 ≤ z) : ∀ k : ℕ,
    (k : ℝ) / 20 ≤ ∑ p ∈ (Finset.Ioc z (z ^ (2 ^ k))).filter Nat.Prime, ((p : ℝ))⁻¹
  | 0 => by simp
  | k + 1 => by
    have ih := sum_recip_iter T hH1 z hz hz1 k
    have hzk : z ≤ z ^ (2 ^ k) := Nat.le_self_pow (by positivity) z
    have hzk2 : z ^ (2 ^ k) ≤ (z ^ (2 ^ k)) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hpow : (z ^ (2 ^ k)) ^ 2 = z ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    have hsplit : Finset.Ioc z (z ^ (2 ^ (k + 1))) =
        Finset.Ioc z (z ^ (2 ^ k)) ∪ Finset.Ioc (z ^ (2 ^ k)) ((z ^ (2 ^ k)) ^ 2) := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc hzk hzk2, hpow]
    have hdisj : Disjoint (Finset.Ioc z (z ^ (2 ^ k))) (Finset.Ioc (z ^ (2 ^ k)) ((z ^ (2 ^ k)) ^ 2)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Ioc] at hx1 hx2
      omega
    rw [hsplit, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]
    have h2 := hH1 (z ^ (2 ^ k)) (le_trans hz hzk)
    push_cast
    linarith

/-- If `ε` is admissible then `ε ≤ ε_n`. -/
lemma le_epsilonFunction {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (h : Erdos688.Erdos688Prop n ε) :
    ε ≤ Erdos688.epsilonFunction n := by
  unfold Erdos688.epsilonFunction
  refine le_csSup ⟨1, fun ε' hε' => ?_⟩ h
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha⟩ := hε'
  obtain ⟨p, _, hlt', hpn, _⟩ := ha 1 le_rfl hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) ≤ (n : ℝ) ^ ε' := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ ε' := Real.rpow_le_rpow_of_exponent_le hn1 hlt.le
  have h2 : (p : ℝ) ≤ n := by exact_mod_cast hpn
  linarith

/-- The covering construction: classes `0` on `(w, n/4]`, given classes `a₁` on `(z, w]`, and an
injective matching of the remaining survivors with the primes of `(n/4, n]`. -/
lemma cover (n z w u : ℕ) (ε : ℝ) (hzw : z ≤ w) (hw : w ≤ u) (hun : u ≤ n)
    (hz : (n : ℝ) ^ ε < (z : ℝ) + 1) (a₁ : ℕ → ℕ)
    (hS : (((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p])).card ≤
      ((Finset.Ioc u n).filter Nat.Prime).card) :
    Erdos688.Erdos688Prop n ε := by
  classical
  set S₂ := ((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p]) with hS₂
  set B := (Finset.Ioc u n).filter Nat.Prime with hB
  have hcardT : Fintype.card S₂ ≤ Fintype.card B := by
    simpa only [Fintype.card_coe] using hS
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardT
  let a₂ : ℕ → ℕ := fun q => if h : ∃ m : S₂, ((e m : B) : ℕ) = q then ((Classical.choose h : S₂) : ℕ) else 0
  have ha₂ : ∀ m (hm : m ∈ S₂), a₂ ((e ⟨m, hm⟩ : B) : ℕ) = m := by
    intro m hm
    have h : ∃ m' : S₂, ((e m' : B) : ℕ) = ((e ⟨m, hm⟩ : B) : ℕ) := ⟨⟨m, hm⟩, rfl⟩
    simp only [a₂, dif_pos h]
    have hc := Classical.choose_spec h
    have : Classical.choose h = (⟨m, hm⟩ : S₂) := e.injective (Subtype.ext hc)
    rw [this]
  refine ⟨fun p => if p ≤ w then a₁ p else if p ≤ u then 0 else a₂ p, ?_⟩
  have hbig : ∀ p : ℕ, z < p → (n : ℝ) ^ ε < p := by
    intro p hp
    have : (z : ℝ) + 1 ≤ p := by exact_mod_cast hp
    linarith
  have hn4 : u ≤ n := hun
  intro m hm1 hmn
  by_cases h1 : ∃ p ∈ (Finset.Ioc w u).filter Nat.Prime, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := h1
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    refine ⟨p, hp.2, hbig p (by omega), by omega, ?_⟩
    have hnw : ¬ p ≤ w := by omega
    simp only [hnw, if_false, hp.1.2, if_true]
    exact (Nat.modEq_zero_iff_dvd.2 hpm).symm
  · by_cases h2 : ∃ p ∈ (Finset.Ioc z w).filter Nat.Prime, a₁ p ≡ m [MOD p]
    · obtain ⟨p, hp, hpm⟩ := h2
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      refine ⟨p, hp.2, hbig p hp.1.1, by omega, ?_⟩
      simp only [hp.1.2, if_true]
      exact hpm
    · have hmS : m ∈ S₂ := by
        rw [hS₂, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        push_neg at h1 h2
        exact ⟨⟨⟨hm1, hmn⟩, fun p hp => h1 p hp⟩, fun p hp => h2 p hp⟩
      set q : ℕ := ((e ⟨m, hmS⟩ : B) : ℕ) with hq
      have hqB : q ∈ B := (e ⟨m, hmS⟩ : B).2
      rw [hB, Finset.mem_filter, Finset.mem_Ioc] at hqB
      refine ⟨q, hqB.2, hbig q (by omega), hqB.1.2, ?_⟩
      have hnw : ¬ q ≤ w := by omega
      have hn4' : ¬ q ≤ u := by omega
      simp only [hnw, hn4', if_false]
      rw [hq, ha₂ m hmS]

/-- Survivors of the classes `0` on `(w, n/4]` are `w`-smooth or multiples of a prime of `(n/4, n]`. -/
lemma card_survivors_le (n w u : ℕ) (_hw : w ≤ u) (hu4 : n < 4 * (u + 1)) :
    (((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card : ℝ) ≤
      (((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card : ℝ) +
        3 * (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := by
  classical
  set B := (Finset.Ioc u n).filter Nat.Prime with hB
  have hsub : ((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m) ⊆
      ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w) ∪
        B.biUnion (fun q => (Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    by_cases hs : ∀ p ∈ m.primeFactors, p ≤ w
    · exact Or.inl ⟨Finset.mem_Icc.2 hm.1, hs⟩
    · push_neg at hs
      obtain ⟨p, hpf, hpw⟩ := hs
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpf
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hpf
      right
      have hpn : p ≤ n := le_trans (Nat.le_of_dvd (by omega) hpm) hm.1.2
      have hp4 : u < p := by
        by_contra hle
        push_neg at hle
        exact hm.2 p (by rw [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hpw, hle⟩, hp⟩) hpm
      refine ⟨p, ?_, ?_⟩
      · rw [hB, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hp4, hpn⟩, hp⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨hm.1, hpm⟩
  have hmult : ∀ q ∈ B, ((Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)).card ≤ 3 := by
    intro q hq
    rw [hB, Finset.mem_filter, Finset.mem_Ioc] at hq
    have hq0 : 0 < q := hq.2.pos
    have hnq : n / q ≤ 3 := by
      rw [Nat.div_le_iff_le_mul_add_pred hq0]
      omega
    calc ((Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)).card ≤ (Finset.Icc 1 (n / q)).card := by
          apply Finset.card_le_card_of_injOn (fun m : ℕ => m / q)
          · intro m hm
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
            rw [Finset.mem_coe, Finset.mem_Icc]
            obtain ⟨⟨hm1, hmn⟩, hqm⟩ := hm
            refine ⟨?_, Nat.div_le_div_right hmn⟩
            have : q ≤ m := Nat.le_of_dvd (by omega) hqm
            exact (Nat.one_le_div_iff hq0).2 this
          · intro m₁ hm₁ m₂ hm₂ h
            rw [Finset.mem_coe, Finset.mem_filter] at hm₁ hm₂
            have e1 := Nat.mul_div_cancel' hm₁.2
            have e2 := Nat.mul_div_cancel' hm₂.2
            simp only at h
            rw [← e1, ← e2, h]
      _ = n / q := by simp
      _ ≤ 3 := hnq
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w)
    (B.biUnion (fun q => (Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)))
  have h3 := Finset.card_biUnion_le (s := B) (t := fun q => (Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m))
  have h4 : ∑ q ∈ B, ((Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)).card ≤ ∑ q ∈ B, 3 :=
    Finset.sum_le_sum hmult
  rw [Finset.sum_const, smul_eq_mul] at h4
  have : ((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card ≤
      ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card + 3 * B.card := by
    omega
  exact_mod_cast this

/-- Counting step: greedy classes on `(z, w]` leave at most as many survivors as there are primes
in `(u, n]`, provided `∏_{z < p ≤ w} (1 - 1/p) ≤ 1/8` and the `w`-smooth numbers are few. -/
lemma count_step (n z w u : ℕ) (hw : w ≤ u) (hu4 : n < 4 * (u + 1))
    (hprod : ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹) ≤ 1 / 8)
    (hsm : ((((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card : ℕ) : ℝ) ≤
      (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4) :
    ∃ a₁ : ℕ → ℕ, (((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p])).card ≤
      ((Finset.Ioc u n).filter Nat.Prime).card := by
  obtain ⟨a₁, ha₁⟩ := greedy ((Finset.Ioc z w).filter Nat.Prime)
    (fun p hp => (Finset.mem_filter.1 hp).2.pos)
    ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m)
  refine ⟨a₁, ?_⟩
  have hsurv := card_survivors_le n w u hw hu4
  have hB0 : (0 : ℝ) ≤ (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := Nat.cast_nonneg _
  have key : (((((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p])).card : ℕ) : ℝ) ≤
      (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := by
    refine le_trans ha₁ ?_
    calc ((((Finset.Icc 1 n).filter fun m : ℕ =>
          ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card : ℕ) : ℝ) *
          ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹)
        ≤ ((((Finset.Icc 1 n).filter fun m : ℕ =>
          ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card : ℕ) : ℝ) * (1 / 8) :=
          mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
      _ ≤ ((((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4 +
            3 * (((Finset.Ioc u n).filter Nat.Prime).card : ℝ)) * (1 / 8) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          linarith
      _ ≤ (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := by nlinarith
  exact_mod_cast key

theorem main : H1 → H2 → H3 → type_of% @Erdos688.erdos_688.variants.lglglg_over_lglg_is_big_o := by
  rintro ⟨T, hT⟩ ⟨A, hA, hH2⟩ hH3
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 60 := ⟨60, rfl⟩
  set A' : ℝ := max A 2 with hA'
  have hA'2 : (2 : ℝ) ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  have hA'pos : 0 < A' := by linarith
  set K : ℝ := ((2 ^ k : ℕ) : ℝ) with hK
  have hKpos : 0 < K := by positivity
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlog3 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog2
  have hT1 : (0 : ℝ) ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  set C : ℝ := K * A' * (Real.log ((T : ℝ) + 1) + 1) with hC
  have hCpos : 0 < C := by positivity
  have hlo : ∀ᶠ n : ℕ in atTop, C * Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    have hb := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / C by positivity)
    filter_upwards [hlog.eventually hb, hlog.eventually_ge_atTop 0] with n h1 h2
    simp only [Real.norm_eq_abs, id] at h1
    rw [abs_of_nonneg h2] at h1
    have h3 : Real.log (Real.log n) ≤ 1 / C * Real.log n :=
      le_trans (le_abs_self _) h1
    calc C * Real.log (Real.log n) ≤ C * (1 / C * Real.log n) :=
          mul_le_mul_of_nonneg_left h3 hCpos.le
      _ = Real.log n := by field_simp
  refine Asymptotics.IsBigO.of_bound (K * A') ?_
  filter_upwards [hlo, hlog3.eventually_ge_atTop 1, hlog2.eventually_ge_atTop 1,
    eventually_ge_atTop 25, hH2, hH3] with n hlo' hL3 hL2 hn25 hH2n hH3n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  set L2 := Real.log (Real.log (n : ℝ)) with hL2def
  set L3 := Real.log L2 with hL3def
  have hL2pos : 0 < L2 := by linarith
  have hL3nn : 0 ≤ L3 := by linarith
  have hL3L2 : L3 ≤ L2 := by
    have := Real.log_le_sub_one_of_pos hL2pos
    linarith
  set δ := L3 / (A' * L2) with hδ
  have hδnn : 0 ≤ δ := by positivity
  have hδle : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith
  have hδA : δ ≤ L3 / (A * L2) := by
    apply div_le_div_of_nonneg_left hL3nn (by positivity)
    exact mul_le_mul_of_nonneg_right hAA' hL2pos.le
  set ε := δ / K with hε
  have hεnn : 0 ≤ ε := by positivity
  -- `n ^ ε ≥ T + 1`
  have key : Real.log ((T : ℝ) + 1) ≤ Real.log n * ε := by
    have e1 : Real.log n * ε = L3 * Real.log n / (A' * L2 * K) := by
      rw [hε, hδ]; field_simp
    rw [e1, le_div_iff₀ (by positivity)]
    have h1 : Real.log n ≤ L3 * Real.log n := by nlinarith
    have h2 : Real.log ((T : ℝ) + 1) * (A' * L2 * K) ≤ C * L2 := by
      rw [hC]; nlinarith [mul_pos hA'pos hKpos]
    linarith
  have hzT' : ((T + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos hnpos]
    push_cast
    calc (T : ℝ) + 1 = Real.exp (Real.log ((T : ℝ) + 1)) := by
          rw [Real.exp_log (by positivity)]
      _ ≤ Real.exp (Real.log n * ε) := Real.exp_le_exp.2 key
  set z := ⌊(n : ℝ) ^ ε⌋₊ with hz
  have hzT : T + 1 ≤ z := Nat.le_floor hzT'
  have hz1 : 1 ≤ z := by omega
  set w := z ^ (2 ^ k) with hw
  have hzw : z ≤ w := Nat.le_self_pow (by positivity) z
  have hwR : (w : ℝ) ≤ (n : ℝ) ^ δ := by
    have hfl : (z : ℝ) ≤ (n : ℝ) ^ ε := Nat.floor_le (by positivity)
    calc (w : ℝ) = (z : ℝ) ^ (2 ^ k : ℕ) := by rw [hw]; push_cast; ring
      _ ≤ ((n : ℝ) ^ ε) ^ (2 ^ k : ℕ) := pow_le_pow_left₀ (by positivity) hfl _
      _ = (n : ℝ) ^ (ε * ((2 ^ k : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      _ = (n : ℝ) ^ δ := by
          congr 1
          rw [hε, ← hK]; field_simp
  have hw4 : w ≤ n / 4 := by
    have hs : Real.sqrt n ≥ 5 := by
      rw [ge_iff_le, Real.le_sqrt (by norm_num) hnpos.le]
      have : (25 : ℝ) ≤ n := by exact_mod_cast hn25
      linarith
    have hsq := Real.sq_sqrt hnpos.le
    have h1 : (n : ℝ) ^ δ ≤ Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hn1 hδle
    have h2 : (w : ℝ) * 4 + 4 ≤ n := by nlinarith
    have h3 : w * 4 + 4 ≤ n := by exact_mod_cast h2
    omega
  set u := n / 4 with hu
  have hu4 : n < 4 * (u + 1) := by omega
  have hun : u ≤ n := by omega
  have hP₁pos : ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, 0 < p :=
    fun p hp => (Finset.mem_filter.1 hp).2.pos
  -- the product over `(z, w]` is at most `1/8`
  have hsum : (3 : ℝ) ≤ ∑ p ∈ (Finset.Ioc z w).filter Nat.Prime, ((p : ℝ))⁻¹ := by
    have := sum_recip_iter T hT z (by omega) hz1 k
    rw [hw]
    have hk3 : (3 : ℝ) ≤ (k : ℝ) / 20 := by rw [hk]; norm_num
    linarith
  have hprod : ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹) ≤ 1 / 8 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have he3 : (8 : ℝ) ≤ Real.exp 3 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
    calc ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹)
        ≤ Real.exp (-∑ p ∈ (Finset.Ioc z w).filter Nat.Prime, ((p : ℝ))⁻¹) := prod_le_exp _ hP₁pos
      _ ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / Real.exp 3 := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / 8 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- smooth numbers
  have hsm : ((((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card : ℕ) : ℝ) ≤
      (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4 := by
    have hBn : (n : ℝ) / (16 * Real.log (n : ℝ)) ≤ (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4 := by
      have : (n : ℝ) / (16 * Real.log (n : ℝ)) = ((n : ℝ) / (4 * Real.log (n : ℝ))) / 4 := by
        rw [div_div]; congr 1; ring
      rw [this]; linarith
    refine le_trans (le_trans ?_ hH2n) hBn
    exact_mod_cast Finset.card_le_card (by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      refine ⟨hm.1, fun p hpf => ?_⟩
      have h1 : (p : ℝ) ≤ w := by exact_mod_cast hm.2 p hpf
      calc (p : ℝ) ≤ w := h1
        _ ≤ (n : ℝ) ^ δ := hwR
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hδA)
  obtain ⟨a₁, hS2⟩ := count_step n z w u hw4 hu4 hprod hsm
  have hcov := cover n z w u ε hzw hw4 hun (Nat.lt_floor_add_one _) a₁ hS2
  have hle := le_epsilonFunction (show 1 ≤ n by omega) hcov
  have hfn : L3 / L2 = K * A' * ε := by
    rw [hε, hδ]; field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L3 / L2), hfn]
  have : ε ≤ |Erdos688.epsilonFunction n| := le_trans hle (le_abs_self _)
  exact mul_le_mul_of_nonneg_left this (by positivity)

end OMA.Erdos688R1
end R1Section

section H1Section
/- The proof of the first Mertens estimate below is from @senamakel's
merged proof of the Romanoff variant of Erdős 851 (PR 2394). Applying the
estimate at t and t² and bounding the interval weights gives H1. -/
open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

end OMALib.Mertens

open Filter Finset Real OMALib.Mertens

theorem h1_proof : OMA.Erdos688R1.H1 := by
  classical
  apply eventually_atTop.mp
  have grow : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop (4*mertens1Const), eventually_ge_atTop (2 : ℕ)]
    with t hbig ht
  have htpos : (0 : ℝ) < log (t : ℝ) := log_pos (by exact_mod_cast (show 1 < t by omega))
  have htsq : t ≤ t^2 := by nlinarith
  let W := (Ioc t (t^2)).filter Nat.Prime
  have hsub : Nat.primesLE t ⊆ Nat.primesLE (t^2) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans htsq,(Nat.mem_primesLE.mp hp).2⟩
  have diff : Nat.primesLE (t^2) \ Nat.primesLE t = W := by
    apply Finset.ext
    intro p
    constructor
    · intro h
      obtain ⟨ha,hb⟩ := Finset.mem_sdiff.mp h
      obtain ⟨hc,hp⟩ := Nat.mem_primesLE.mp ha
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge (fun hpt => hb (Nat.mem_primesLE.mpr ⟨hpt,hp⟩)),hc⟩,hp⟩
    · intro h
      obtain ⟨hi,hp⟩ := mem_filter.mp h
      obtain ⟨hlt,hle⟩ := mem_Ioc.mp hi
      exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hle,hp⟩,
        fun he => (not_le_of_gt hlt) (Nat.mem_primesLE.mp he).1⟩
  have hsum := sum_sdiff hsub (f := fun p : ℕ => log (p : ℝ)/(p : ℝ))
  rw [diff] at hsum
  have low := (abs_le.mp (abs_sum_log_div_sub_log_le_nat (t^2))).1
  have high := (abs_le.mp (abs_sum_log_div_sub_log_le_nat t)).2
  rw [Nat.cast_pow, log_pow] at low
  have upper : (∑ p ∈ W, log (p : ℝ) / p) ≤ (2*log (t : ℝ))*(∑ p ∈ W, ((p : ℝ))⁻¹) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨h₁,h₂⟩ := mem_Ioc.mp (mem_filter.mp hp).1
    have hpl : log (p : ℝ) ≤ 2*log (t : ℝ) := by
      rw [← show ((2 : ℕ) : ℝ) = 2 by norm_num, ← log_pow]
      apply log_le_log (by exact_mod_cast (show 0 < p by omega))
      exact_mod_cast h₂
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hpl (by positivity)
  change (1 : ℝ)/20 ≤ ∑ p ∈ W, ((p : ℝ))⁻¹
  apply le_of_mul_le_mul_left (a := 2*log (t : ℝ)) _ (by positivity)
  norm_num only [Nat.cast_ofNat] at low
  linarith
end H1Section

section H2Section
/- The smooth-number estimates below are excerpted from OpenAI's
LongGapsBetweenPrimes.lean, commit 03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b,
via @marcusbuffett's merged Rankin proof (PR 2593). Used under Apache-2.0.
Upstream source: https://github.com/openai/LongGapsBetweenPrimes
SPDX-License-Identifier: Apache-2.0

The final step uses the estimate at x = H = n. -/

namespace LongGapsBetweenPrimes
noncomputable section
/-- The logarithms of distinct prime divisors sum to at most `log n`. -/
lemma sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by
  have hfilter : N.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1.2, h.2, hn.ne'⟩,
      fun h => ⟨⟨(Nat.le_of_dvd hn h.2.1).trans hnN, h.1⟩, h.2.1⟩⟩
  rw [← Finset.sum_filter, hfilter, ← Real.log_prod (fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp =>
      Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hp).1.pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- An elementary upper bound for the logarithmically weighted prime harmonic sum. -/
theorem sum_prime_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount (p : ℕ) (_hp : p ∈ N.primesLE) :
      (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
      (Nat.sub_one_lt_floor ((N : ℝ) / p)).le
  have hsum : (∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.range N,
          if p ∣ n + 1 then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Nat.card_multiples N p, ← Finset.sum_boole]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = ∑ n ∈ Finset.range N, ∑ p ∈ N.primesLE,
          if p ∣ n + 1 then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
        exact (sum_log_prime_divisors_le_log (by omega : 0 < n + 1) hnN).trans
          (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log N := by simp
  have hlower : (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / p) -
      Chebyshev.theta N ≤ (N : ℝ) * Real.log N := by
    apply le_trans _ hsum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_right (hcount p hp)
      (Nat.mem_primesLE.mp hp).2.log_pos.le
    calc
      (N : ℝ) * (Real.log p / p) - Real.log p =
        ((N : ℝ) / p - 1) * Real.log p := by ring
      _ ≤ _ := h
  have htheta := Chebyshev.theta_le_log4_mul_x hNr.le
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/-- The finite Euler product over primes at most N. -/
def eulerProduct (N : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹

/-- The multiplicative weight `n ↦ n ^ (-σ)`. -/
def natPowerHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The weighted sum over smooth numbers is bounded by the finite Euler product. -/
lemma sum_smooth_le_eulerProduct {N : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ eulerProduct N σ := by
  classical
  have hprime {p : ℕ} (hp : p.Prime) : ‖natPowerHom σ p‖ < 1 := by
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)
  have hsum :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := natPowerHom σ) hprime (N + 1)).2
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum

/-- The elementary zeta-function bound obtained by integrating t^(-σ). -/
theorem tsum_succ_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hexp : -σ < -1 := neg_lt_neg hσ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num) hx)) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num), Nat.cast_one, Real.one_rpow,
    show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq] at htail
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hexp)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  apply add_le_add le_rfl
  simpa only [Nat.cast_add, Nat.cast_one] using htail

/-- For `σ > 1`, the finite Euler product is at most `1 + 1 / (σ - 1)`. -/
lemma eulerProduct_le_zeta_bound {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    eulerProduct N σ ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ))
    ((N + 1).smoothNumbers) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
  have hseries := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natPowerHom σ) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-σ)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
        (by linarith)) (N + 1)).2
  change HasSum (fun n : (N + 1).smoothNumbers => (n.val : ℝ) ^ (-σ))
    (eulerProduct N σ) at hseries
  rw [hseries.tsum_eq] at ht
  rw [hs.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add] at ht
  simp only [Nat.cast_add, Nat.cast_one] at ht
  exact ht.trans (tsum_succ_rpow_le hσ)

/-- Compare an Euler factor at exponent one with its shift by `r`. -/
lemma euler_factor_comparison {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    (1 - p ^ (-(1 : ℝ)))⁻¹ ≤
      (1 - p ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hden : 0 < 1 - p ^ (-(1 + r)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  have hlog : 0 ≤ r * Real.log p := mul_nonneg hr (Real.log_pos hp1).le
  have hpow : 1 - p ^ (-r) ≤ r * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * -r)
    nlinarith
  rw [Real.rpow_neg_one, ← div_eq_inv_mul]
  apply (le_div_iff₀ hden).mpr
  rw [← div_eq_inv_mul]
  calc
    (1 - p ^ (-(1 + r))) / (1 - p⁻¹) =
        1 + (1 - p ^ (-r)) / (p - 1) := by
      rw [neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
      field_simp
      ring
    _ ≤ 1 + (r * Real.log p) / (p - 1) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hpow hpm.le)
    _ ≤ 1 + 2 * r * Real.log p / p := by
      apply add_le_add le_rfl
      apply (div_le_div_iff₀ hpm hp0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hlog]
    _ ≤ Real.exp (2 * r * Real.log p / p) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * r * Real.log p / p)

/-- Moving the Euler product to the right of its pole has bounded cost. -/
theorem eulerProduct_comparison (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    eulerProduct N 1 ≤ eulerProduct N (1 + r) *
      Real.exp (2 * r * ∑ p ∈ N.primesLE, Real.log p / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE,
        (1 - (p : ℝ) ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt)
          (by norm_num : -(1 : ℝ) < 0)).le
      · intro p hp
        exact euler_factor_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) hr
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- An explicit weak Mertens upper bound, sufficient throughout the proof. -/
theorem eulerProduct_one_le {N : ℕ} (hN : 2 ≤ N) :
    eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ 2 * Real.log N := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log N := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hcost : 2 * (Real.log N)⁻¹ * (∑ p ∈ N.primesLE, Real.log p / p) ≤ 6 := by
    calc
      _ ≤ 2 * (Real.log N)⁻¹ * (3 * Real.log N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 6 := by field_simp; norm_num
  have hzeta : eulerProduct N (1 + (Real.log N)⁻¹) ≤ 1 + Real.log N := by
    simpa using eulerProduct_le_zeta_bound
      (lt_add_of_pos_right 1 (inv_pos.mpr hlog)) N
  calc
    _ ≤ eulerProduct N (1 + (Real.log N)⁻¹) *
        Real.exp (2 * (Real.log N)⁻¹ * ∑ p ∈ N.primesLE, Real.log p / p) :=
      eulerProduct_comparison N (inv_nonneg.mpr hlog.le)
    _ ≤ (1 + Real.log N) * Real.exp 6 :=
      mul_le_mul hzeta (Real.exp_le_exp.mpr hcost) (Real.exp_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

/-- The finite Euler product is positive at every positive exponent. -/
lemma eulerProduct_pos (N : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < eulerProduct N σ := by
  apply Finset.prod_pos
  intro p hp
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)))

/-- A uniform geometric factor for the smooth-number estimate. -/
def smoothEulerConstant : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

/-- The smooth Euler constant is positive. -/
lemma smoothEulerConstant_pos : 0 < smoothEulerConstant := by
  exact inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))

/-- The scale constant used to choose the smoothness cutoff and tilt. -/
def smoothScaleConstant : ℝ := 3 * smoothEulerConstant + 10

/-- The smoothness scale constant is positive. -/
lemma smoothScaleConstant_pos : 0 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- Bound the cost of shifting an Euler factor to exponent `1 - t`. -/
lemma euler_factor_left_comparison {p t : ℝ} (hp : 2 ≤ p) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 - p ^ (-(1 - t)))⁻¹ ≤ (1 - p ^ (-(1 : ℝ)))⁻¹ *
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hpow : p ^ (-(1 - t)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ p ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by norm_num)
  have hcden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hden : 0 < 1 - p ^ (-(1 - t)) := by linarith
  have hnum : 0 ≤ p ^ t - 1 := sub_nonneg.mpr (Real.one_le_rpow hp1 ht)
  have hsplit : p ^ (-(1 - t)) = p ^ t / p := by
    rw [show -(1 - t) = t + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one,
      div_eq_mul_inv]
  have he : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ =
      1 + ((p ^ t - 1) / p) / (1 - p ^ (-(1 - t))) := by
    have hpt : p ^ t < p := (div_lt_one hp0).mp (by rw [← hsplit]; linarith)
    rw [hsplit]
    field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hpt)]
    ring
  have hratio : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ ≤
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
    rw [he]
    calc
      _ ≤ 1 + ((p ^ t - 1) / p) / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
        exact add_le_add le_rfl
          (div_le_div_of_nonneg_left (div_nonneg hnum hp0.le) hcden (by linarith))
      _ = 1 + smoothEulerConstant * (p ^ t - 1) / p := by
        unfold smoothEulerConstant
        ring
      _ ≤ _ := by simpa only [add_comm] using
        Real.add_one_le_exp (smoothEulerConstant * (p ^ t - 1) / p)
  rw [Real.rpow_neg_one, inv_mul_eq_div]
  apply (le_div_iff₀ (show 0 < 1 - p⁻¹ by
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith)))).mpr
  simpa only [mul_comm] using hratio

/-- Bound the cost of shifting the Euler product to exponent `1 - t`. -/
lemma eulerProduct_left_comparison (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (smoothEulerConstant * ∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ *
        Real.exp (smoothEulerConstant * ((p : ℝ) ^ t - 1) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)).le)
      · intro p hp
        exact euler_factor_left_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) ht ht'
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- A secant bound controls `p ^ t - 1` using the ratio `log p / log z`. -/
lemma rpow_secant_log {p z t : ℝ} (hp : 1 ≤ p) (hpz : p ≤ z) (hz : 1 < z)
    (ht : 0 ≤ t) : p ^ t - 1 ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) := by
  rcases ht.eq_or_lt with rfl | _
  · simp
  have hlogz := Real.log_pos hz
  have hratio : Real.log p / Real.log z ≤ 1 :=
    (div_le_one hlogz).mpr (Real.log_le_log (zero_lt_one.trans_le hp) hpz)
  have h := convexOn_exp.2 (Set.mem_univ (t * Real.log z)) (Set.mem_univ 0)
    (div_nonneg (Real.log_nonneg hp) hlogz.le) (sub_nonneg.mpr hratio)
    (show Real.log p / Real.log z + (1 - Real.log p / Real.log z) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have harg : Real.log p / Real.log z * (t * Real.log z) = Real.log p * t := by
    field_simp
  rw [harg, ← Real.rpow_def_of_pos (zero_lt_one.trans_le hp)] at h
  linarith

/-- Bound the shifted Euler product using the tilt and the largest prime cutoff. -/
lemma eulerProduct_left_bound {N : ℕ} {z t : ℝ} (hN : 2 ≤ N) (hNz : (N : ℝ) ≤ z)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (3 * smoothEulerConstant * Real.exp (t * Real.log z)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 1 < z := by linarith
  have hlogz := Real.log_pos hz
  have hlogN : Real.log N ≤ Real.log z :=
    Real.log_le_log (by linarith) hNz
  have hlog4 : Real.log 4 ≤ 2 * Real.log z := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ z ^ 2 by nlinarith)
  have hlogs : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log z := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hsum : (∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) ≤
      3 * Real.exp (t * Real.log z) := by
    calc
      _ ≤ ∑ p ∈ N.primesLE,
          (Real.log p / p) * (Real.exp (t * Real.log z) / Real.log z) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
        calc
          _ ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) / p :=
            div_le_div_of_nonneg_right
              (rpow_secant_log (by exact_mod_cast hp.one_lt.le)
                ((by exact_mod_cast hpN : (p : ℝ) ≤ N).trans hNz) hz ht)
              (Nat.cast_nonneg p)
          _ ≤ (Real.log p / Real.log z) * Real.exp (t * Real.log z) / p := by
            gcongr
            exact sub_le_self _ zero_le_one
          _ = _ := by ring
      _ = (∑ p ∈ N.primesLE, Real.log p / p) *
          (Real.exp (t * Real.log z) / Real.log z) := (Finset.sum_mul ..).symm
      _ ≤ (3 * Real.log z) * (Real.exp (t * Real.log z) / Real.log z) :=
        mul_le_mul_of_nonneg_right hlogs (by positivity)
      _ = 3 * Real.exp (t * Real.log z) := by field_simp
  apply (eulerProduct_left_comparison N ht ht').trans
  apply mul_le_mul_of_nonneg_left _ (eulerProduct_pos N (by norm_num)).le
  apply Real.exp_le_exp.mpr
  simpa [mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hsum smoothEulerConstant_pos.le

/-- A finite Euler-product bound for the count of smooth integers up to `H`. -/
lemma smooth_count_rankin {N H : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 H)
    (hsmooth : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (S.card : ℝ) ≤ (H : ℝ) ^ σ * eulerProduct N σ := by
  have hsum := sum_smooth_le_eulerProduct hσ S hsmooth
  have hpoint (n : ℕ) (hn : n ∈ S) : (1 : ℝ) ≤ (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
    have hnI := Finset.mem_Icc.mp (hS hn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnH : (n : ℝ) ≤ H := by exact_mod_cast hnI.2
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hn0 σ)).mpr
      (by simpa only [one_mul] using Real.rpow_le_rpow hn0.le hnH hσ.le)
  calc
    (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := Finset.sum_le_sum hpoint
    _ = (H : ℝ) ^ σ * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg H) σ)

/-- The logarithmic smoothness cutoff in the covering construction. -/
def coverLogZ (x : ℝ) : ℝ :=
  Real.log x * Real.log (Real.log (Real.log x)) /
    (smoothScaleConstant * Real.log (Real.log x))

/-- The smoothness cutoff in the covering construction, rounded down to an integer. -/
def coverZ (x : ℝ) : ℕ := ⌊Real.exp (coverLogZ x)⌋₊

/-- The small-prime cutoff, given by the integer part of `(log x)^4`. -/
def coverW (x : ℝ) : ℕ := ⌊(Real.log x) ^ 4⌋₊

/-- The Rankin tilt used to count smooth integers. -/
def coverTilt (x : ℝ) : ℝ := smoothScaleConstant * Real.log (Real.log x) / Real.log x

/-- The smoothness scale constant exceeds ten. -/
lemma smoothScaleConstant_gt_ten : 10 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- The covering tilt times the logarithmic cutoff equals the third iterated logarithm. -/
lemma coverTilt_mul_coverLogZ {x : ℝ} (hx : 1 < x) (hlog : 1 < Real.log x) :
    coverTilt x * coverLogZ x = Real.log (Real.log (Real.log x)) := by
  have hl1 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hl2 : Real.log (Real.log x) ≠ 0 := (Real.log_pos hlog).ne'
  unfold coverTilt coverLogZ
  field_simp [hl1, hl2, smoothScaleConstant_pos.ne']

/-- The size, ordering, and tilt bounds for the covering parameters hold eventually. -/
lemma eventually_cover_parameters : ∀ᶠ x : ℝ in Filter.atTop,
    2 ≤ x ∧ 2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) ∧ 1 ≤ Real.log (Real.log (Real.log x)) ∧
    4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x ∧
    0 ≤ coverTilt x ∧ coverTilt x ≤ 1 / 2 ∧
    4 * Real.log (Real.log x) ≤ coverLogZ x ∧ coverLogZ x ≤ Real.log x := by
  have hlog := Real.tendsto_log_atTop
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := hlog.comp hlog
  have hlogloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x)))
      Filter.atTop Filter.atTop := hlog.comp hloglog
  have hsmall : Filter.Tendsto
      (fun x : ℝ => 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [mul_div_assoc] using ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      hlog).const_mul (4 * smoothScaleConstant)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hlog.eventually_ge_atTop 2,
    hloglog.eventually_ge_atTop 1, hlogloglog.eventually_ge_atTop 1,
    hsmall.eventually_le_const zero_lt_one] with x hx hl hll hlll hsmall
  have hl0 : 0 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hquad : 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x :=
    (div_le_one hl0).mp hsmall
  have hlinear : 4 * smoothScaleConstant * Real.log (Real.log x) ≤ Real.log x := by
    calc
      _ ≤ 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith)
          (mul_nonneg (by norm_num) smoothScaleConstant_pos.le)
      _ ≤ _ := hquad
  refine ⟨hx, hl, hll, hlll, hquad, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg smoothScaleConstant_pos.le hll0.le) hl0.le
  · unfold coverTilt
    apply (div_le_iff₀ hl0).mpr
    nlinarith
  · unfold coverLogZ
    apply (le_div_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    calc
      _ = 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 := by ring
      _ ≤ Real.log x := hquad
      _ ≤ Real.log x * Real.log (Real.log (Real.log x)) :=
        le_mul_of_one_le_right hl0.le hlll
  · unfold coverLogZ
    apply (div_le_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    apply mul_le_mul_of_nonneg_left _ hl0.le
    calc
      _ ≤ Real.log (Real.log x) := by
        linarith [Real.log_le_sub_one_of_pos hll0]
      _ ≤ smoothScaleConstant * Real.log (Real.log x) :=
        le_mul_of_one_le_left hll0.le (by linarith [smoothScaleConstant_gt_ten])

/-- The small-prime cutoff does not exceed the smoothness cutoff. -/
lemma coverW_le_coverZ {x : ℝ} (hx : 1 < x)
    (hz : 4 * Real.log (Real.log x) ≤ coverLogZ x) : coverW x ≤ coverZ x := by
  apply Nat.floor_mono
  calc
    (Real.log x) ^ 4 = Real.exp ((4 : ℕ) * Real.log (Real.log x)) := by
      rw [Real.exp_nat_mul, Real.exp_log (Real.log_pos hx)]
    _ ≤ Real.exp (coverLogZ x) := Real.exp_le_exp.mpr hz

/-- The smoothness cutoff is at most the integer part of `x`. -/
lemma coverZ_le_floor {x : ℝ} (hx : 0 < x) (hz : coverLogZ x ≤ Real.log x) : coverZ x ≤ ⌊x⌋₊ := by
  exact Nat.floor_mono ((Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hx))

/-- The small-prime cutoff is at least two when `log x ≥ 2`. -/
lemma coverW_ge_two {x : ℝ} (hL : 2 ≤ Real.log x) : 2 ≤ coverW x := by
  apply Nat.le_floor
  exact (by norm_num : (2 : ℝ) ≤ 2 ^ 4).trans
    (pow_le_pow_left₀ (by norm_num) hL 4)

/-- Eventually, at most `H / (log x)^3` integers up to `H` are `coverZ x`-smooth. -/
lemma eventually_smooth_count : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H →
    (∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x) →
    (S.card : ℝ) ≤ (H : ℝ) / Real.log x ^ 3 := by
  filter_upwards [eventually_cover_parameters,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2]
    with x hparameters hlarge
  simp only [Function.comp_apply] at hlarge
  obtain ⟨hx, hl, hll, _, _, ht, ht', hZlow, hZhigh⟩ := hparameters
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hl1 : 1 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hZ : 2 ≤ coverZ x :=
    (coverW_ge_two hl).trans (coverW_le_coverZ hx1 hZlow)
  have hlogZ : Real.log (coverZ x) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < coverZ x))
      ((by exact_mod_cast coverZ_le_floor hx0 hZhigh : (coverZ x : ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le hx0.le))
  have hEulerOne : eulerProduct (coverZ x) 1 ≤
      Real.exp (7 * Real.log (Real.log x)) := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log (coverZ x)) := eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * Real.log x ^ 2 := by
        gcongr
        nlinarith
      _ = Real.exp (6 + 2 * Real.log (Real.log x)) := by
        rw [Real.exp_add, show Real.exp (2 * Real.log (Real.log x)) =
          Real.log x ^ 2 by
            simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 2]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hEuler : eulerProduct (coverZ x) (1 - coverTilt x) ≤
      Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) := by
    have hbound := eulerProduct_left_bound hZ
      (Nat.floor_le (Real.exp_pos (coverLogZ x)).le) ht ht'
    rw [Real.log_exp, coverTilt_mul_coverLogZ hx1 hl1, Real.exp_log hll0] at hbound
    calc
      _ ≤ eulerProduct (coverZ x) 1 *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := hbound
      _ ≤ Real.exp (7 * Real.log (Real.log x)) *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        unfold smoothScaleConstant
        ring
  intro H hxH S hS hsmooth
  have hH0 : 0 < (H : ℝ) := hx0.trans_le hxH
  have hpower : (H : ℝ) ^ (1 - coverTilt x) ≤
      H * Real.exp (-smoothScaleConstant * Real.log (Real.log x)) := by
    rw [sub_eq_add_neg, Real.rpow_add hH0, Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ hH0.le
    calc
      _ ≤ x ^ (-coverTilt x) := Real.rpow_le_rpow_of_nonpos hx0 hxH (neg_nonpos.mpr ht)
      _ = _ := by
        rw [Real.rpow_def_of_pos hx0]
        congr 1
        unfold coverTilt
        field_simp
  calc
    (S.card : ℝ) ≤ (H : ℝ) ^ (1 - coverTilt x) *
        eulerProduct (coverZ x) (1 - coverTilt x) := by
      apply smooth_count_rankin (by linarith) S hS
      intro n hn
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp (hS hn)).1; omega
      apply Nat.mem_smoothNumbers.mpr
      refine ⟨hn0, ?_⟩
      intro p hp
      obtain ⟨hp, hpn⟩ := (Nat.mem_primeFactorsList hn0).mp hp
      exact Nat.lt_succ_of_le (hsmooth n hn p hp hpn)
    _ ≤ (H * Real.exp (-smoothScaleConstant * Real.log (Real.log x))) *
        Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) :=
      mul_le_mul hpower hEuler (eulerProduct_pos _ (by linarith)).le (by positivity)
    _ = (H : ℝ) / Real.log x ^ 3 := by
      rw [mul_assoc, ← Real.exp_add,
        show -smoothScaleConstant * Real.log (Real.log x) +
          (smoothScaleConstant - 3) * Real.log (Real.log x) =
          -(3 * Real.log (Real.log x)) by ring,
        Real.exp_neg, show Real.exp (3 * Real.log (Real.log x)) = Real.log x ^ 3 by
          simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 3,
        div_eq_mul_inv]

end
end LongGapsBetweenPrimes

open Filter Finset Real LongGapsBetweenPrimes

theorem h2_proof : OMA.Erdos688R1.H2 := by
  classical
  refine ⟨smoothScaleConstant, smoothScaleConstant_pos, ?_⟩
  have hx := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hx.eventually eventually_smooth_count,
    (tendsto_log_atTop.comp hx).eventually_ge_atTop 4, eventually_ge_atTop (1 : ℕ)]
    with n hcount hlog hn
  change 4 ≤ log (n : ℝ) at hlog
  let S := (Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors,
    (p : ℝ) ≤ (n : ℝ) ^ (log (log (log n)) / (smoothScaleConstant*log (log n)))
  change (S.card : ℝ) ≤ (n : ℝ)/(16*log n)
  have hc := hcount n le_rfl S (filter_subset _ _) (by
    intro m hm p hp hd
    have hmn := mem_Icc.mp (mem_filter.mp hm).1
    have h : (p : ℝ) ≤ (n : ℝ) ^ (log (log (log n)) / (smoothScaleConstant*log (log n))) :=
      (mem_filter.mp hm).2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)
    apply Nat.le_floor
    rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega))] at h
    simpa [coverLogZ, mul_div_assoc] using h)
  apply hc.trans
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  nlinarith [mul_nonneg (show 0 ≤ log (n : ℝ)-4 by linarith) (sq_nonneg (log (n : ℝ))),
    sq_nonneg (log (n : ℝ)-4)]
end H2Section

section H3Section
open Filter Finset

namespace OMACheb

lemma count_add (m n : ℕ) (hmn : m ≤ n) :
    ((Finset.Ioc m n).filter Nat.Prime).card + Nat.primeCounting m = Nat.primeCounting n := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  have hdisj : Disjoint ((Finset.Ioc m n).filter Nat.Prime) (Nat.primesLE m) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have := Nat.le_of_mem_primesLE hq
    omega
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  constructor
  · rintro (⟨⟨_, h2⟩, h3⟩ | ⟨h1, h2⟩)
    · exact ⟨h2, h3⟩
    · exact ⟨h1.trans hmn, h2⟩
  · rintro ⟨h1, h2⟩
    by_cases h : p ≤ m
    · right; exact ⟨h, h2⟩
    · left; exact ⟨⟨by omega, h1⟩, h2⟩

end OMACheb

theorem h3_proof : OMA.Erdos688R1.H3 := by
  have ht : Tendsto (fun n : ℕ => ((n / 4 : ℕ) : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨4 * ⌈b⌉₊, fun n hn => ?_⟩
    have h1 : ⌈b⌉₊ ≤ n / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      omega
    exact (Nat.le_ceil b).trans (by exact_mod_cast h1)
  have hB := ht.eventually (Chebyshev.eventually_primeCounting_le (ε := 1 / 100) (by norm_num))
  have hL : ∀ᶠ n : ℕ in atTop, 44 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 44
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ 1 / 200 * (n : ℝ) := by
    have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 200 by norm_num)
    have hb' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually hb
    filter_upwards [hb'] with n hn
    have h1 : Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := Real.le_norm_self _
    have h2 : ‖(id (n : ℝ))‖ = n := by simp
    rw [h2] at hn
    linarith
  filter_upwards [hB, hL, hsmall, eventually_ge_atTop 8] with n hBn hLn hsm hn8
  simp only [Nat.floor_natCast] at hBn
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < (0.6932 : ℝ) := by
    have := Real.log_two_lt_d9; linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (n : ℝ) := ⟨_, rfl⟩
  rw [← hLdef] at hLn hsm ⊢
  have hLpos : 0 < L := by linarith
  -- lower bound for π n
  have hA := Chebyshev.pi_ge n
  rw [← hLdef, div_le_iff₀ hLpos] at hA
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + L := by
    rw [hLdef, ← Real.log_mul (by norm_num) hn0.ne']
    apply Real.log_le_log (by linarith)
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  -- upper bound for π (n / 4)
  obtain ⟨m, hm⟩ : ∃ m, m = n / 4 := ⟨_, rfl⟩
  rw [← hm] at hBn ⊢
  have hm1 : (m : ℝ) ≤ (n : ℝ) / 4 := by
    rw [hm]; exact Nat.cast_div_le
  have hm2 : (n : ℝ) / 8 ≤ (m : ℝ) := by
    have h : n ≤ 8 * m := by omega
    have h' : (n : ℝ) ≤ 8 * (m : ℝ) := by exact_mod_cast h
    linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hlogm : L / 1.05 ≤ Real.log (m : ℝ) := by
    have h1 : Real.log ((n : ℝ) / 8) ≤ Real.log (m : ℝ) := Real.log_le_log (by positivity) hm2
    rw [Real.log_div hn0.ne' (by norm_num), ← hLdef, hl8] at h1
    have h2 : L / 1.05 ≤ L - 3 * Real.log 2 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  have hlogm0 : 0 < L / 1.05 := by positivity
  have hpm : (Nat.primeCounting m : ℝ) ≤ 0.366555 * (n : ℝ) / L := by
    have h1 : (Real.log 4 + 1 / 100) * (m : ℝ) / Real.log (m : ℝ) ≤
        1.3964 * ((n : ℝ) / 4) / (L / 1.05) := by
      apply div_le_div₀ (by positivity) _ hlogm0 hlogm
      rw [hl4]
      have : (2 * Real.log 2 + 1 / 100) * (m : ℝ) ≤ 1.3964 * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hm0.le
      nlinarith
    have h2 : (1.3964 : ℝ) * ((n : ℝ) / 4) / (L / 1.05) = 0.366555 * (n : ℝ) / L := by
      field_simp
      ring
    linarith
  have hpmL : (Nat.primeCounting m : ℝ) * L ≤ 0.366555 * (n : ℝ) := by
    rwa [le_div_iff₀ hLpos] at hpm
  -- combine
  have hcount := OMACheb.count_add m n (by omega)
  have hcountR : (((Finset.Ioc m n).filter Nat.Prime).card : ℝ) + (Nat.primeCounting m : ℝ) =
      (Nat.primeCounting n : ℝ) := by exact_mod_cast hcount
  rw [div_le_iff₀ (by positivity)]
  have hn44 : (44 : ℝ) ≤ 1 / 200 * (n : ℝ) := by linarith
  have key : (n : ℝ) / 4 ≤ (((Finset.Ioc m n).filter Nat.Prime).card : ℝ) * L := by
    have h3 : (((Finset.Ioc m n).filter Nat.Prime).card : ℝ) * L =
        (Nat.primeCounting n : ℝ) * L - (Nat.primeCounting m : ℝ) * L := by
      rw [← hcountR]; ring
    have h4 : 0.6931 * (n : ℝ) ≤ (n : ℝ) * Real.log 2 :=
      by nlinarith
    rw [h3]
    linarith
  linarith
end H3Section

theorem OMA.solution : type_of% @Erdos688.erdos_688.variants.lglglg_over_lglg_is_big_o :=
  OMA.Erdos688R1.main h1_proof h2_proof h3_proof
