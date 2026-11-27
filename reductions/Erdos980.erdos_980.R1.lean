import FormalConjectures.ErdosProblems.«980»
import Mathlib

-- Reduction Erdos980.erdos_980.R1 of Erdős 980 (Elliott's theorem, all k ≥ 2)
-- Source: P. D. T. A. Elliott, A problem of Erdős concerning power residue sums,
--   Acta Arith. 13 (1967/68), 131-149.
-- Credit: @LordMike
-- The shape (pattern densities plus a uniform tail) follows @marcusbuffett's merged reduction
-- Erdos980.erdos_980.variants.erdos_two.R1 of the quadratic case, generalised to every k.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 980 from Chebotarev densities and Elliott's tail estimate

Write `q 0 < q 1 < …` for the primes and `n_k(p)` for the least `k`-th power nonresidue mod `p`.
The least nonresidue is always a prime, and `n_k(p) = q i` exactly when `q 0, …, q (i-1)` are
`k`-th power residues mod `p` and `q i` is not.

* `H1` (Chebotarev density theorem, natural-density form, for the Kummer fields
  `ℚ(ζ_k, q_0^(1/k), …, q_i^(1/k))`): for every `k ≥ 2` and every `i` the primes `p ≡ 1 (mod k)`
  with that residue pattern have a natural density `δ i` relative to `x / log x`, and `δ 0 > 0`
  (because `2^(1/k) ∉ ℚ(ζ_k)`). This is the deep input giving the main term. For `k = 2` it is
  `H1` of `Erdos980.erdos_980.variants.erdos_two.R1` (there with the explicit value `2^-(i+1)`).
* `H2` (Elliott's tail estimate, from the Linnik large sieve and a Brun–Titchmarsh bound), only
  for prime exponents `l`: the primes `p ≡ 1 (mod l)` with `n_l(p) ≥ q K` contribute at most
  `ε x / log x` to the sum, uniformly in `x`, once `K` is large. For `l = 2` this is exactly `H2`
  of the quadratic reduction, whose parent is proved upstream.

The prime case of `H2` suffices: if the prime `l` divides `k` and `p ≡ 1 (mod k)`, then a
non-`l`-th power mod `p` is a non-`k`-th power, so `n_k(p) ≤ n_l(p)` (`least_le_of_dvd`).

`main` splits the sum at `q K`, shows from `H2` that the partial sums of `∑ q i * δ i` are
bounded (so the series converges, to `c` say), and that `c ≥ 2 δ 0 > 0`; an `ε/3` argument
then gives `residueSum k x * (log x / x) → c`.
-/

namespace OMA.R_Erdos980_erdos_980_R1
open Filter Asymptotics Erdos980
open scoped Classical Topology BigOperators

lemma leastFacts (k p : ℕ) (hk : k ≠ 0)
    (hn : {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y ^ k = (a : ZMod p)}.Nonempty) :
    (leastNonresidue k p).Prime ∧
    (¬∃ y : ZMod p, y ^ k = (leastNonresidue k p : ZMod p)) ∧
    ∀ a < leastNonresidue k p, ∃ y : ZMod p, y ^ k = (a : ZMod p) := by
  have hm : 0 < leastNonresidue k p ∧ ¬∃ y : ZMod p, y ^ k = (leastNonresidue k p : ZMod p) :=
    Nat.sInf_mem hn
  have hs : ∀ a < leastNonresidue k p, ∃ y : ZMod p, y ^ k = (a : ZMod p) := by
    intro a ha
    by_cases hz : a = 0
    · subst a; exact ⟨0, by simp [hk]⟩
    by_contra h
    have hh : leastNonresidue k p ≤ a :=
      Nat.sInf_le (s := {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y ^ k = (a : ZMod p)}) ⟨by omega, h⟩
    omega
  refine ⟨?_, hm.2, hs⟩
  have h1 : leastNonresidue k p ≠ 1 := fun e ↦ hm.2 ⟨1, by rw [e]; simp⟩
  by_contra h
  obtain ⟨a, b, ha, hb, e⟩ :=
    (Nat.not_prime_iff_exists_mul_eq (n := leastNonresidue k p) (by omega)).mp h
  obtain ⟨u, hu⟩ := hs a ha
  obtain ⟨v, hv⟩ := hs b hb
  exact hm.2 ⟨u * v, by rw [mul_pow, hu, hv, ← Nat.cast_mul, e]⟩

lemma least_eq_pattern (k p i : ℕ) (hk : k ≠ 0) :
    leastNonresidue k p = Nat.nth Nat.Prime i ↔
    (∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ∧
      ¬ ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime i : ZMod p) := by
  have hq : ∀ j, 0 < Nat.nth Nat.Prime j := fun j ↦ (Nat.prime_nth_prime j).pos
  constructor
  · intro e
    have hn : {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y ^ k = (a : ZMod p)}.Nonempty := by
      by_contra! hempty
      have hz : leastNonresidue k p = 0 := by simp [leastNonresidue, hempty]
      have := hq i
      omega
    obtain ⟨_, hbad, hsmall⟩ := leastFacts k p hk hn
    rw [e] at hbad hsmall
    exact ⟨fun j hj ↦ hsmall _ ((Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr hj), hbad⟩
  · rintro ⟨hprev, hbad⟩
    have hi : Nat.nth Nat.Prime i ∈ {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y ^ k = (a : ZMod p)} :=
      ⟨hq i, hbad⟩
    have hle : leastNonresidue k p ≤ Nat.nth Nat.Prime i := Nat.sInf_le hi
    obtain ⟨hp, hnot, _⟩ := leastFacts k p hk ⟨_, hi⟩
    apply le_antisymm hle
    by_contra! hlt
    have he := Nat.nth_count hp
    have hj := (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp (he.trans_lt hlt)
    exact hnot (he ▸ hprev _ hj)

lemma cutoff (k K p : ℕ) (hk : k ≠ 0) :
    (leastNonresidue k p : ℝ) =
      (∑ i ∈ Finset.range K,
        if leastNonresidue k p = Nat.nth Nat.Prime i then (Nat.nth Nat.Prime i : ℝ) else 0) +
      (if Nat.nth Nat.Prime K ≤ leastNonresidue k p then (leastNonresidue k p : ℝ) else 0) := by
  classical
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  by_cases h : Nat.nth Nat.Prime K ≤ leastNonresidue k p
  · rw [if_pos h, Finset.sum_eq_zero, zero_add]
    intro i hi
    have hlt := hmono (Finset.mem_range.mp hi)
    exact if_neg (by omega)
  rw [if_neg h, add_zero]
  by_cases hn : leastNonresidue k p = 0
  · have hall (i : ℕ) : leastNonresidue k p ≠ Nat.nth Nat.Prime i := by
      have := (Nat.prime_nth_prime i).pos
      omega
    rw [Finset.sum_eq_zero (fun i _ ↦ if_neg (hall i))]
    exact_mod_cast hn
  have hne : {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y ^ k = (a : ZMod p)}.Nonempty := by
    by_contra! he
    exact hn (by simp [leastNonresidue, he])
  have hp := (leastFacts k p hk hne).1
  have hj : Nat.nth Nat.Prime (Nat.count Nat.Prime (leastNonresidue k p)) = leastNonresidue k p :=
    Nat.nth_count hp
  have hjk : Nat.count Nat.Prime (leastNonresidue k p) < K :=
    hmono.lt_iff_lt.mp (hj.trans_lt (by omega))
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_range.mpr hjk)]
  · rw [if_pos hj.symm, hj]
  · intro i hi hij
    exact if_neg fun he ↦ hij (hmono.injective (he.symm.trans hj.symm))

/-- Chebotarev density theorem for the Kummer fields `ℚ(ζ_k, q_0^(1/k), …, q_i^(1/k))`: among the
primes `p ≡ 1 (mod k)`, those for which the first `i` primes are `k`-th power residues and the
next prime is not have a natural density `δ i` relative to `x / log x`; and `δ 0 > 0`. -/
def H1 : Prop := ∀ k : ℕ, 2 ≤ k → ∃ δ : ℕ → ℝ, 0 < δ 0 ∧ ∀ i : ℕ, Tendsto (fun x : ℝ ↦
    (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
      (∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ∧
      ¬ ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime i : ZMod p)).card : ℝ) *
        (Real.log x / x)) atTop (𝓝 (δ i))

/-- Elliott's tail estimate, for prime exponents: for a prime `l`, the mean contribution of the
primes `p ≡ 1 (mod l)` whose least `l`-th power nonresidue is at least the `K`-th prime tends to
zero as `K → ∞`, uniformly in `x`. -/
def H2 : Prop := ∀ l : ℕ, l.Prime → ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    (∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % l = 1 ∧
      Nat.nth Nat.Prime K ≤ leastNonresidue l p), (leastNonresidue l p : ℝ)) *
        (Real.log x / x) ≤ ε

/-- For a prime `p ≡ 1 (mod l)` with `l` prime, some positive integer is not an `l`-th power
mod `p`: otherwise `u ↦ u ^ l` would be a bijection of the units, which have an element of
order `l`. -/
lemma exists_nonresidue (l p : ℕ) (hl : l.Prime) (hp : p.Prime) (h : p % l = 1) :
    {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y ^ l = (a : ZMod p)}.Nonempty := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact l.Prime := ⟨hl⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hne
  have hall : ∀ a : ℕ, 0 < a → ∃ y : ZMod p, y ^ l = (a : ZMod p) := by
    intro a ha
    by_contra hcon
    exact hne a ⟨ha, hcon⟩
  have hdvd : l ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]
    exact (Nat.modEq_iff_dvd' hp.one_lt.le).mp (by rw [Nat.ModEq, h, Nat.mod_eq_of_lt hl.one_lt])
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card l hdvd
  have hsurj : Function.Surjective (fun u : (ZMod p)ˣ ↦ u ^ l) := by
    intro u
    have hu0 : (u : ZMod p) ≠ 0 := u.ne_zero
    obtain ⟨y, hy⟩ := hall (u : ZMod p).val (ZMod.val_pos.mpr hu0)
    rw [ZMod.natCast_zmod_val] at hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hl.ne_zero] at hy
      exact hu0 hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  have hg1 : g = 1 := hinj (by
    change g ^ l = 1 ^ l
    rw [one_pow, ← hg, pow_orderOf_eq_one])
  rw [hg1, orderOf_one] at hg
  exact hl.one_lt.ne hg

/-- If the prime `l` divides `k` then, for primes `p ≡ 1 (mod k)`, a non-`l`-th power is a
non-`k`-th power, so `n_k(p) ≤ n_l(p)`. -/
lemma least_le_of_dvd (k l p : ℕ) (hl : l.Prime) (hlk : l ∣ k) (hp : p.Prime)
    (h : p % k = 1) : p % l = 1 ∧ leastNonresidue k p ≤ leastNonresidue l p := by
  have hpl : p % l = 1 := by
    rw [← Nat.mod_mod_of_dvd p hlk, h, Nat.mod_eq_of_lt hl.one_lt]
  refine ⟨hpl, ?_⟩
  have hm : 0 < leastNonresidue l p ∧ ¬∃ y : ZMod p, y ^ l = (leastNonresidue l p : ZMod p) :=
    Nat.sInf_mem (exists_nonresidue l p hl hp hpl)
  refine Nat.sInf_le (s := {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y ^ k = (a : ZMod p)}) ⟨hm.1, ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨d, rfl⟩ := hlk
  exact hm.2 ⟨y ^ d, by rw [← pow_mul, mul_comm d l, hy]⟩

/-- The tail estimate for every `k ≥ 2`, from the prime case `l = minFac k`. -/
lemma tail_all (h2 : H2) (k : ℕ) (hk : 2 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    (∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % k = 1 ∧
      Nat.nth Nat.Prime K ≤ leastNonresidue k p), (leastNonresidue k p : ℝ)) *
        (Real.log x / x) ≤ ε := by
  intro ε hε
  have hl : (Nat.minFac k).Prime := Nat.minFac_prime (by omega)
  have hlk : Nat.minFac k ∣ k := Nat.minFac_dvd k
  filter_upwards [h2 _ hl ε hε] with K hK
  filter_upwards [hK, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  refine le_trans (mul_le_mul_of_nonneg_right ?_
    (div_nonneg (Real.log_nonneg hx1.le) (by linarith))) hx
  have key : ∀ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % k = 1 ∧
      Nat.nth Nat.Prime K ≤ leastNonresidue k p),
      p % Nat.minFac k = 1 ∧ leastNonresidue k p ≤ leastNonresidue (Nat.minFac k) p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact least_le_of_dvd k _ p hl hlk (Nat.prime_of_mem_primesBelow hp.1) hp.2.1
  calc (∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % k = 1 ∧
          Nat.nth Nat.Prime K ≤ leastNonresidue k p), (leastNonresidue k p : ℝ))
      ≤ ∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % k = 1 ∧
          Nat.nth Nat.Prime K ≤ leastNonresidue k p),
            (leastNonresidue (Nat.minFac k) p : ℝ) :=
        Finset.sum_le_sum fun p hp ↦ by exact_mod_cast (key p hp).2
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ Nat.cast_nonneg _)
        intro p hp
        have hk' := key p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hk'.1, hp.2.2.trans hk'.2⟩

theorem main : H1 → H2 → type_of% @Erdos980.erdos_980 := by
  classical
  intro h1 h2 k hk
  have hk0 : k ≠ 0 := by omega
  obtain ⟨δ, hδ0, hfreq⟩ := h1 k hk
  have htail := tail_all h2 k hk
  let q := Nat.nth Nat.Prime
  let a := fun i : ℕ ↦ (q i : ℝ) * δ i
  let w := fun x : ℝ ↦ Real.log x / x
  let A := fun x : ℝ ↦ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % k = 1)
  let B := fun i (x : ℝ) ↦ ((A x).filter (fun p ↦ leastNonresidue k p = q i)).card
  let T := fun K (x : ℝ) ↦
    ∑ p ∈ (A x).filter (fun p ↦ q K ≤ leastNonresidue k p), (leastNonresidue k p : ℝ)
  have hw : ∀ x : ℝ, 1 < x → 0 ≤ w x := fun x hx ↦
    div_nonneg (Real.log_nonneg hx.le) (by linarith)
  have hT : ∀ K x, 0 ≤ T K x := fun K x ↦ Finset.sum_nonneg fun _ _ ↦ by positivity
  have hb (i) : Tendsto (fun x ↦ (B i x : ℝ) * w x) atTop (𝓝 (δ i)) := by
    simpa only [B, A, w, q, Finset.filter_filter, least_eq_pattern k _ _ hk0] using hfreq i
  have ht (ε) (he : 0 < ε) : ∀ᶠ K in atTop, ∀ᶠ x in atTop, T K x * w x ≤ ε := by
    simpa only [T, A, q, w, Finset.filter_filter] using htail ε he
  have hδ (i) : 0 ≤ δ i := by
    refine ge_of_tendsto (hb i) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (Nat.cast_nonneg _) (hw x hx)
  have ha (i) : 0 ≤ a i := mul_nonneg (Nat.cast_nonneg _) (hδ i)
  have splitSum (K) (x) : residueSum k x =
      (∑ i ∈ Finset.range K, (q i : ℝ) * B i x) + T K x := by
    change ∑ p ∈ A x, (leastNonresidue k p : ℝ) = _
    calc
      _ = ∑ p ∈ A x, ((∑ i ∈ Finset.range K,
        if leastNonresidue k p = q i then (q i : ℝ) else 0) +
        if q K ≤ leastNonresidue k p then (leastNonresidue k p : ℝ) else 0) :=
          Finset.sum_congr rfl fun p _ ↦ cutoff k K p hk0
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_filter]
          simp [B, mul_comm]
        · simp [T, Finset.sum_filter]
  have hbfin (K : ℕ) : Tendsto (fun x ↦
      (∑ i ∈ Finset.range K, (q i : ℝ) * B i x) * w x)
      atTop (𝓝 (∑ i ∈ Finset.range K, a i)) := by
    simp only [Finset.sum_mul, mul_assoc]
    apply tendsto_finsetSum
    intro i _
    exact (hb i).const_mul (q i : ℝ)
  -- the partial sums of `a` are bounded, by the tail estimate with `ε = 1`
  obtain ⟨K₀, hK₀⟩ := (ht 1 one_pos).exists
  have hbound (K : ℕ) : ∑ i ∈ Finset.range K, a i ≤ ∑ i ∈ Finset.range K₀, a i + 1 := by
    refine le_of_tendsto_of_tendsto (hbfin K) ((hbfin K₀).add_const 1) ?_
    filter_upwards [hK₀, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have e1 := splitSum K x
    have e2 := splitSum K₀ x
    have h3 : (∑ i ∈ Finset.range K, (q i : ℝ) * B i x) * w x ≤ residueSum k x * w x := by
      apply mul_le_mul_of_nonneg_right _ (hw x hx1)
      rw [e1]; linarith [hT K x]
    have h4 : residueSum k x * w x =
        (∑ i ∈ Finset.range K₀, (q i : ℝ) * B i x) * w x + T K₀ x * w x := by
      rw [e2, add_mul]
    change (∑ i ∈ Finset.range K, (q i : ℝ) * B i x) * w x ≤
      (∑ i ∈ Finset.range K₀, (q i : ℝ) * B i x) * w x + 1
    linarith
  have hsum : Summable a := summable_of_sum_range_le ha hbound
  have hC : 0 < ∑' i, a i :=
    hsum.tsum_pos ha 0 (mul_pos (by exact_mod_cast (Nat.prime_nth_prime 0).pos) hδ0)
  have hlim : Tendsto (fun x ↦ residueSum k x * w x) atTop (𝓝 (∑' i, a i)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have he : 0 < ε / 3 := by positivity
    obtain ⟨K, hK, htK⟩ :=
      ((Metric.tendsto_nhds.mp hsum.hasSum.tendsto_sum_nat _ he).and (ht _ he)).exists
    filter_upwards [Metric.tendsto_nhds.mp (hbfin K) _ he, htK, eventually_gt_atTop (1 : ℝ)]
      with x hx tx hxp
    have hnn : 0 ≤ T K x * w x := mul_nonneg (hT K x) (hw x hxp)
    rw [Real.dist_eq, abs_lt] at hK hx ⊢
    rw [splitSum K x, add_mul]
    constructor <;> linarith
  refine ⟨∑' i, a i, hC, ?_⟩
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hd := hlim.div_const (∑' i, a i)
  rw [div_self hC.ne'] at hd
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  change (residueSum k x * (Real.log x / x)) / (∑' i, a i) =
    residueSum k x / ((∑' i, a i) * x / Real.log x)
  field_simp [hC.ne', (Real.log_pos hx).ne', show x ≠ 0 by linarith]

end OMA.R_Erdos980_erdos_980_R1
