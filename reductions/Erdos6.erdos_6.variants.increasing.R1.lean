import FormalConjectures.ErdosProblems.«6»
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic

-- Reduction Erdos6.erdos_6.variants.increasing.R1 of Erdős Problem 6 — increasing
-- Credit: @Need17Bread
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- H1: Bombieri–Vinogradov theorem (theta version, arbitrary coprime residues).
-- H2: Bombieri–Vinogradov implies Maynard–Tao for admissible affine forms with a common slope
--     (Maynard, Dense clusters of primes in subsets, Theorem 3.1).
-- main:
--   * m = 0 is trivial (every natural number satisfies the vacuous condition).
--   * m = 1 is proved unconditionally via unbounded prime gaps from factorial intervals.
--   * m ≥ 2 is proved via the Banks–Freiberg–Turnage-Butterbaugh (2015) covering construction
--     using exponentially spaced offsets k! * 2^i and Chinese Remainder Theorem sieving.

open Erdos6
open scoped BigOperators

namespace OMA.R_Erdos6_erdos_6_variants_increasing_R1

/-- The case `m = 0`: the range is empty so every `n` qualifies. -/
lemma inc_zero :
    {n | ∀ i ∈ Finset.range 0, primeGap (n + i) < primeGap (n + i + 1)}.Infinite := by
  simp only [Finset.range_zero, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    Set.setOf_true]
  exact Set.infinite_univ

/-- Prime gaps are arbitrarily large: the interval `[(B + 3)! + 2, (B + 3)! + B + 3]`
contains no primes. -/
lemma exists_large_primeGap (B : ℕ) : ∃ n : ℕ, B < primeGap n := by
  let K := B + 2
  let M := (K + 1).factorial
  have hcomp : ∀ j : ℕ, 2 ≤ j → j ≤ K + 1 → ¬ (M + j).Prime := by
    intro j hj2 hjK hp
    have hdvdM : j ∣ M := Nat.dvd_factorial (by omega) hjK
    have hdvd : j ∣ M + j := Nat.dvd_add hdvdM (dvd_refl j)
    have hMpos : 0 < M := Nat.factorial_pos (K + 1)
    rcases hp.eq_one_or_self_of_dvd j hdvd with h1 | hself
    · omega
    · omega
  have h2lt : 2 < M + 2 := by
    have : 0 < M := Nat.factorial_pos (K + 1)
    omega
  have hidx_pos : 0 < Nat.count Nat.Prime (M + 2) := by
    have h2c : 1 ≤ Nat.count Nat.Prime 3 := by
      have : Nat.count Nat.Prime 3 = Nat.count Nat.Prime 2 + 1 := by
        rw [Nat.count_succ, if_pos Nat.prime_two]
      omega
    have hmono : Nat.count Nat.Prime 3 ≤ Nat.count Nat.Prime (M + 2) :=
      Nat.count_monotone Nat.Prime (by omega)
    omega
  let n := Nat.count Nat.Prime (M + 2) - 1
  have hn1 : n + 1 = Nat.count Nat.Prime (M + 2) := by omega
  have hinf := Nat.infinite_setOfPred_prime
  have hpn_lt : Nat.nth Nat.Prime n < M + 2 :=
    Nat.nth_lt_of_lt_count (by omega)
  have hpn1_ge : M + 2 ≤ Nat.nth Nat.Prime (n + 1) := by
    rw [hn1]
    exact Nat.le_nth_count hinf (M + 2)
  have hpn1_prime : (Nat.nth Nat.Prime (n + 1)).Prime :=
    Nat.nth_mem_of_infinite hinf (n + 1)
  have hpn1_gt : M + K + 1 < Nat.nth Nat.Prime (n + 1) := by
    by_contra hle
    have hle' : Nat.nth Nat.Prime (n + 1) ≤ M + K + 1 := by omega
    let j := Nat.nth Nat.Prime (n + 1) - M
    have hj_eq : M + j = Nat.nth Nat.Prime (n + 1) := by omega
    exact hcomp j (by omega) (by omega) (hj_eq ▸ hpn1_prime)
  refine ⟨n, ?_⟩
  unfold primeGap
  omega

/-- Elementary case `m = 1`: there are infinitely many `n` with `primeGap n < primeGap (n + 1)`.
Otherwise the prime gaps would be eventually non-increasing and hence bounded. -/
lemma inc_one : {n | primeGap n < primeGap (n + 1)}.Infinite := by
  by_contra hf
  obtain ⟨N, hN⟩ := (Set.not_infinite.mp hf).bddAbove
  have hanti : ∀ t : ℕ, primeGap (N + 1 + t) ≤ primeGap (N + 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep : primeGap (N + 1 + t + 1) ≤ primeGap (N + 1 + t) := by
        by_contra hlt
        have hlt' : primeGap (N + 1 + t) < primeGap (N + 1 + t + 1) := by omega
        have hle : N + 1 + t ≤ N := hN hlt'
        omega
      rw [← add_assoc]
      exact hstep.trans ih
  let B := max ((Finset.range (N + 2)).sup primeGap) (primeGap (N + 1))
  obtain ⟨n, hn⟩ := exists_large_primeGap B
  have hbound : primeGap n ≤ B := by
    by_cases hlt : n < N + 2
    · exact (Finset.le_sup (f := primeGap) (Finset.mem_range.mpr hlt)).trans (le_max_left _ _)
    · have heq : n = N + 1 + (n - (N + 1)) := by omega
      rw [heq]
      exact (hanti (n - (N + 1))).trans (le_max_right _ _)
  omega

/-- If a window `[x, x + w]` contains at least `m + 2` primes and every ordered triple of primes
in the window has strictly increasing gaps, then the primes starting at `count Prime x` form a
length-`m` increasing gap run. -/
lemma inc_run_of_window {x w m : ℕ}
    (hcard : m + 2 ≤ ((Finset.Icc x (x + w)).filter Nat.Prime).card)
    (hgap : ∀ {a b c}, x ≤ a → c ≤ x + w → a < b → b < c →
      a.Prime → b.Prime → c.Prime → b - a < c - b) :
    ∃ n, x ≤ Nat.nth Nat.Prime n ∧
      ∀ i ∈ Finset.range m, primeGap (n + i) < primeGap (n + i + 1) := by
  let l := Nat.count Nat.Prime x
  let u := Nat.count Nat.Prime (x + w + 1)
  have hsize : ((Finset.Icc x (x + w)).filter Nat.Prime).card ≤ u - l := by
    rw [← Nat.card_Ico]
    apply Finset.card_le_card_of_injOn (Nat.count Nat.Prime)
    · intro a ha
      obtain ⟨ha, hp⟩ := Finset.mem_filter.mp ha
      obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp ha
      exact Finset.mem_Ico.mpr
        ⟨Nat.count_monotone _ hl, Nat.count_strict_mono hp (by omega)⟩
    · intro a ha b hb hab
      exact Nat.count_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hinf := Nat.infinite_setOfPred_prime
  refine ⟨l, Nat.le_nth_count hinf x, ?_⟩
  intro i hi
  have hi := Finset.mem_range.mp hi
  have hleft : x ≤ Nat.nth Nat.Prime (l + i) :=
    (Nat.le_nth_count hinf x).trans (Nat.nth_monotone hinf (Nat.le_add_right l i))
  have hright : Nat.nth Nat.Prime (l + i + 1 + 1) ≤ x + w := by
    apply Nat.lt_succ_iff.mp
    have hil : l + i + 1 + 1 < u := by omega
    exact Nat.nth_lt_of_lt_count hil
  unfold primeGap
  exact hgap hleft hright
    (Nat.nth_strictMono hinf (by omega)) (Nat.nth_strictMono hinf (by omega))
    (Nat.nth_mem_of_infinite hinf _) (Nat.nth_mem_of_infinite hinf _)
    (Nat.nth_mem_of_infinite hinf _)

/-- Exponentially spaced multiples of `k!` ensure that every ordered triple has strictly
increasing gaps. -/
lemma exists_inc_offsets (k : ℕ) :
    ∃ w : ℕ, ∃ H : Finset ℕ, H.card = k ∧
      (∀ a ∈ H, a ≤ w ∧ k.factorial ∣ a) ∧
      (∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, a < b → b < c → b - a < c - b) := by
  let f : ℕ → ℕ := fun i => k.factorial * 2 ^ i
  have hpos := Nat.factorial_pos k
  have hmono : ∀ {i j}, i < j → f i < f j := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by decide) hij) hpos
  have hord : ∀ {i j}, f i < f j → i < j := by
    intro i j hlt
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact hij
    · exact (lt_irrefl _ hlt).elim
    · exact ((hmono hij).not_gt hlt).elim
  refine ⟨k.factorial * 2 ^ k, (Finset.range k).image f, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i _ j _ heq
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ((hmono hij).ne heq).elim
    · exact hij
    · exact ((hmono hij).ne heq.symm).elim
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hik : i ≤ k := (Finset.mem_range.mp hi).le
    exact ⟨Nat.mul_le_mul_left _ (pow_le_pow_right' (by decide) hik), dvd_mul_right _ _⟩
  · intro a ha b hb c hc hab hbc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hc
    have hij := hord hab
    have hjl := hord hbc
    have h2i_pos : 0 < (2 : ℕ) ^ i := by positivity
    have h2ij : (2 : ℕ) ^ i < 2 ^ j := pow_lt_pow_right₀ (by decide) hij
    have h2jl : 2 ^ j * 2 ≤ (2 : ℕ) ^ l := by
      rw [← pow_succ]
      exact pow_le_pow_right' (by decide) hjl
    dsimp only [f]
    rw [← Nat.mul_sub_left_distrib, ← Nat.mul_sub_left_distrib]
    exact Nat.mul_lt_mul_of_pos_left (by omega) hpos

/-- Chinese Remainder Theorem covering system excluding every offset outside `H` in `[0, w]`. -/
lemma inc_cover {w : ℕ} {H : Finset ℕ} (hH : ∀ a ∈ H, a ≤ w) :
    ∃ M b : ℕ, 0 < M ∧
      (∀ x, M < x → ∀ a ≤ w, (M * x + b + a).Prime → a ∈ H) ∧
      (∀ p, p.Prime → p ∣ M → ∀ a ∈ H, ¬ p ∣ b + a) := by
  let S := Finset.Icc 0 w \ H
  let q (a : ℕ) := Nat.nth Nat.Prime (w + 1 + a)
  have hinf := Nat.infinite_setOfPred_prime
  have hqp (a : ℕ) : (q a).Prime := Nat.nth_mem_of_infinite hinf _
  have hqw (a : ℕ) : w < q a :=
    (Nat.lt_succ_self w).trans_le ((Nat.le_add_right (w + 1) a).trans ((Nat.nth_strictMono hinf).id_le _))
  have hqi : Function.Injective q := fun a b hab =>
    Nat.add_left_cancel (Nat.nth_injective hinf hab)
  have hpair : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime q) := by
    intro a ha b hb hab
    exact (Nat.coprime_primes (hqp a) (hqp b)).2 (fun h => hab (hqi h))
  let M := ∏ a ∈ S, q a
  let b := Nat.chineseRemainderOfFinset (fun a => q a - a) q S
    (fun a _ => (hqp a).ne_zero) hpair
  have hM : 0 < M := Finset.prod_pos fun a _ => (hqp a).pos
  have hd (a : ℕ) (ha : a ∈ S) : q a ∣ (b : ℕ) + a := by
    have ha' := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).2
    have hc := (b.property a ha).add_right a
    rw [Nat.sub_add_cancel (ha'.trans (hqw a).le)] at hc
    exact Nat.modEq_zero_iff_dvd.mp (hc.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  refine ⟨M, b, hM, ?_, ?_⟩
  · intro x hx a haw hp
    by_contra ha
    have hs : a ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, haw⟩, ha⟩
    have hqM : q a ∣ M := Finset.dvd_prod_of_mem q hs
    have hqx : q a < M * x + (b : ℕ) + a := by
      have hle := Nat.le_of_dvd hM hqM
      have hmx : x ≤ M * x := by
        calc
          x = 1 * x := (Nat.one_mul x).symm
          _ ≤ M * x := Nat.mul_le_mul_right x hM
      omega
    have hd' : q a ∣ M * x + (b : ℕ) + a := by
      rw [add_assoc]
      exact (dvd_mul_of_dvd_left hqM x).add (hd a hs)
    rcases hp.eq_one_or_self_of_dvd (q a) hd' with h | h
    · exact (hqp a).ne_one h
    · exact hqx.ne h
  · intro p hp hpM a ha hpa
    obtain ⟨u, hu, hpu⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff q).mp hpM
    have heq : p = q u := (Nat.prime_dvd_prime_iff_eq hp (hqp u)).mp hpu
    subst p
    have hcong := (Nat.modEq_zero_iff_dvd.mpr hpa).trans
      (Nat.modEq_zero_iff_dvd.mpr (hd u hu)).symm
    have hmod := Nat.ModEq.add_left_cancel' (b : ℕ) hcong
    have hua := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hu).1).2
    have hau := hmod.eq_of_lt_of_lt ((hH a ha).trans_lt (hqw u)) (hua.trans_lt (hqw u))
    exact (Finset.mem_sdiff.mp hu).2 (hau ▸ ha)

/-- Admissibility of the sieved affine family `{M * x + b + a | a ∈ H}`. -/
lemma inc_admissible {k M b : ℕ} {H : Finset ℕ}
    (hcard : H.card = k) (hfac : ∀ a ∈ H, k.factorial ∣ a)
    (hcop : ∀ p, p.Prime → p ∣ M → ∀ a ∈ H, ¬ p ∣ b + a) :
    ∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a := by
  classical
  intro p hp
  by_cases hM : p ∣ M
  · refine ⟨0, ?_⟩
    simpa using hcop p hp hM
  let : Fact p.Prime := ⟨hp⟩
  have hM' : (M : ZMod p) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff M p).mp h)
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, ∀ a ∈ H, r + (a : ZMod p) ≠ 0 := by
    by_cases hpk : p ≤ k
    · refine ⟨1, ?_⟩
      intro a ha
      have hd := (Nat.dvd_factorial hp.pos hpk).trans (hfac a ha)
      rw [(ZMod.natCast_eq_zero_iff a p).mpr hd, add_zero]
      exact one_ne_zero
    · let T : Finset (ZMod p) := H.image (fun a : ℕ => -(a : ZMod p))
      have hT : T.card < Fintype.card (ZMod p) := by
        rw [ZMod.card p]
        exact Finset.card_image_le.trans_lt (hcard.symm ▸ Nat.lt_of_not_ge hpk)
      obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ T := by
        by_contra h
        push Not at h
        have heq : T = Finset.univ := Finset.eq_univ_of_forall h
        rw [heq, Finset.card_univ] at hT
        exact (lt_irrefl _ hT)
      refine ⟨r, fun a ha h => hr ?_⟩
      exact Finset.mem_image.mpr ⟨a, ha, (eq_neg_of_add_eq_zero_left h).symm⟩
  let t : ZMod p := (M : ZMod p)⁻¹ * (r - (b : ZMod p))
  refine ⟨t.val, ?_⟩
  intro a ha hd
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  push_cast at hz
  rw [ZMod.natCast_zmod_val] at hz
  have heq : (M : ZMod p) * t + (b : ZMod p) = r := by
    dsimp [t]
    rw [← mul_assoc, mul_inv_cancel₀ hM', one_mul, sub_add_cancel]
  rw [heq] at hz
  exact hr a ha hz

/-- Banks–Freiberg–Turnage-Butterbaugh deduction of arbitrarily long increasing prime gap runs
from the Maynard–Tao prime cluster theorem for admissible affine forms. -/
lemma inc_core
    (hmay : ∀ r : ℕ, ∃ k : ℕ, ∀ (H : Finset ℕ) (M b : ℕ), k ≤ H.card → 0 < M →
      (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) →
      ∀ N : ℕ, ∃ x, N < x ∧ r ≤ (H.filter fun a => (M * x + b + a).Prime).card)
    (m : ℕ) :
    {n | ∀ i ∈ Finset.range m, primeGap (n + i) < primeGap (n + i + 1)}.Infinite := by
  obtain ⟨k, hk⟩ := hmay (m + 2)
  obtain ⟨w, H, hcard, hH, hgap⟩ := exists_inc_offsets k
  obtain ⟨M, b, hM, hcover, hcop⟩ := inc_cover (fun a ha => (hH a ha).1)
  have hadm := inc_admissible hcard (fun a ha => (hH a ha).2) hcop
  apply Set.infinite_of_forall_exists_gt
  intro N
  let pN := Nat.nth Nat.Prime N
  obtain ⟨x, hx, hsize⟩ := hk H M b hcard.ge hM hadm (max M pN)
  let y := M * x + b
  have hxy : x ≤ y := by
    calc
      x = 1 * x := (Nat.one_mul x).symm
      _ ≤ M * x := Nat.mul_le_mul_right x hM
      _ ≤ y := Nat.le_add_right _ _
  have hwindow : m + 2 ≤ ((Finset.Icc y (y + w)).filter Nat.Prime).card := by
    refine hsize.trans (Finset.card_le_card_of_injOn (fun a => y + a) ?_ ?_)
    · intro a ha
      obtain ⟨haH, hap⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.le_add_right _ _, Nat.add_le_add_left (hH a haH).1 y⟩, hap⟩
    · intro a _ c _ hac
      exact Nat.add_left_cancel hac
  have hwindow_gap : ∀ {a c d}, y ≤ a → d ≤ y + w → a < c → c < d →
      a.Prime → c.Prime → d.Prime → c - a < d - c := by
    intro a c d hya hdw hac hcd hpa hpc hpd
    have hMx := (le_max_left M pN).trans_lt hx
    have help (z : ℕ) (hl : y ≤ z) (hu : z ≤ y + w) (hp : z.Prime) : z - y ∈ H := by
      exact hcover x hMx (z - y) (by omega) (by
        change (y + (z - y)).Prime
        rwa [Nat.add_sub_of_le hl])
    have hinc := hgap (a - y) (help a hya (by omega) hpa)
      (c - y) (help c (by omega) (by omega) hpc) (d - y) (help d (by omega) hdw hpd)
      (by omega) (by omega)
    omega
  obtain ⟨n, hn, hrun⟩ := inc_run_of_window hwindow hwindow_gap
  have hlt : pN < Nat.nth Nat.Prime n :=
    ((le_max_right M pN).trans_lt hx).trans_le (hxy.trans hn)
  exact ⟨n, hrun, (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hlt⟩

/-- Bombieri–Vinogradov theorem (theta version, arbitrary coprime residues). -/
def H1 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
    ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
      |∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a q % q),
          Real.log p - x / (Nat.totient q : ℝ)| ≤ C * x / Real.log x ^ A

/-- Bombieri–Vinogradov implies Maynard–Tao for admissible affine forms with a common slope. -/
def H2 : Prop :=
  (∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
    ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
      |∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a q % q),
          Real.log p - x / (Nat.totient q : ℝ)| ≤ C * x / Real.log x ^ A) →
  ∀ r : ℕ, ∃ k : ℕ, ∀ (H : Finset ℕ) (M b : ℕ), k ≤ H.card → 0 < M →
    (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) →
    ∀ N : ℕ, ∃ x, N < x ∧ r ≤ (H.filter fun a => (M * x + b + a).Prime).card

theorem main : H1 → H2 → type_of% @Erdos6.erdos_6.variants.increasing := by
  intro h1 h2
  have hmay := h2 h1
  intro m
  rcases m with _ | m
  · exact inc_zero
  rcases m with _ | m
  · simpa [Finset.range_one] using inc_one
  · exact inc_core hmay (m + 2)

end OMA.R_Erdos6_erdos_6_variants_increasing_R1
