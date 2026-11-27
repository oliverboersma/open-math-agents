import FormalConjectures.ErdosProblems.«40»
import Mathlib.NumberTheory.Bertrand

/-!
# Finite tests for individual denominators in Erdős problem 40

At a fixed representation bound and cutoff, `survivors` enumerates the subsets
of a finite interval meeting prescribed integer lower bounds on their prefixes.
The test counts ordered representations and allows zero in a set, as in the
upstream statement. Only positive elements count toward the density.

The numerical answer uses tables of maximal count vectors that can be computed
before a denominator is supplied. The criterion does not settle whether there
is any divergent denominator satisfying it.

The compactness argument is related to the project reduction for the existential
variant by Nicholas Wierenga. Here the lower bounds may vary at every integer.

A separate Sidon construction rules out fourth-root denominators even when
they drop to a logarithm on each fixed band [s, 2s], with s ranging through
the scales defined below. It also gives a failed denominator agreeing with any
prescribed divergent function on arbitrarily late intervals [M, dM] for every
d. The finite Sidon blocks and their gluing lemma are from @Dugongue's proof
of Erdos329.exists_sidon_pos_density, building on the project's proof of
Erdos44.sidon_set_lower_bound.

Credit: @ubuwaits
-/

namespace Erdos40Windows

open AdditiveCombinatorics Filter Real Set

/-- Number of ordered representations inside a finite set. -/
def pairCount (B : Finset ℕ) (s : ℕ) : ℕ :=
  ((Finset.HasAntidiagonal.antidiagonal s).filter
    (fun p : ℕ × ℕ ↦ p.1 ∈ B ∧ p.2 ∈ B)).card

def prefixCount (B : Finset ℕ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (· ∈ B)).card

/-- The cap and the first density index are both `k`. A sum of size at most
`T` has both summands in the prefix, so these tests persist under restriction. -/
def survivors (q : ℕ → ℕ) (k T : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (T + 1)).powerset.filter fun B ↦
    (List.range (T + 1)).all (fun s ↦ decide (pairCount B s ≤ k)) &&
    (List.range (T + 1)).all (fun n ↦ decide (k ≤ n → q n ≤ prefixCount B n))

private theorem mem_survivors {q : ℕ → ℕ} {k T : ℕ} {B : Finset ℕ} :
    B ∈ survivors q k T ↔ B ⊆ Finset.range (T + 1) ∧
      (∀ s ≤ T, pairCount B s ≤ k) ∧
      (∀ n ≤ T, k ≤ n → q n ≤ prefixCount B n) := by
  simp only [survivors, Finset.mem_filter, Finset.mem_powerset, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq, List.mem_range, Nat.lt_succ_iff]

private noncomputable def truncation (A : Set ℕ) (T : ℕ) : Finset ℕ :=
  by classical exact (Finset.range (T + 1)).filter (fun n ↦ n ∈ A)

private theorem mem_truncation {A : Set ℕ} {i T : ℕ} :
    i ∈ truncation A T ↔ i ∈ Finset.range (T + 1) ∧ i ∈ A := by
  classical exact Finset.mem_filter

private theorem pairCount_truncation (A : Set ℕ) {s T : ℕ} (hs : s ≤ T) :
    pairCount (truncation A T) s = sumRep A s := by
  classical
  rw [pairCount, sumRep_def]
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h₁ : p.1 < T + 1 := by omega
  have h₂ : p.2 < T + 1 := by omega
  simp [truncation, h₁, h₂]

private theorem prefixCount_truncation (A : Set ℕ) {n T : ℕ} (hn : n ≤ T) :
    prefixCount (truncation A T) n = (A ∩ Icc 1 n).ncard := by
  classical
  have heq : ↑((Finset.Icc 1 n).filter (· ∈ truncation A T)) = A ∩ Icc 1 n := by
    ext i
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, truncation,
      Finset.mem_range, Set.mem_inter_iff, Set.mem_Icc]
    exact ⟨fun ⟨hi, _, ha⟩ ↦ ⟨ha, hi⟩,
      fun ⟨ha, hi⟩ ↦ ⟨hi, by omega, ha⟩⟩
  rw [← heq, Set.ncard_coe_finset, prefixCount]

private def Fits (q : ℕ → ℕ) (k T : ℕ) (A : Set ℕ) : Prop :=
  (∀ s ≤ T, sumRep A s ≤ k) ∧
  (∀ n, k ≤ n → n ≤ T → q n ≤ (A ∩ Icc 1 n).ncard)

private theorem truncation_mem (q : ℕ → ℕ) (k T : ℕ) (A : Set ℕ) :
    truncation A T ∈ survivors q k T ↔ Fits q k T A := by
  classical
  have hsub : truncation A T ⊆ Finset.range (T + 1) := Finset.filter_subset _ _
  rw [mem_survivors, and_iff_right hsub]
  constructor
  · rintro ⟨hr, hd⟩
    exact ⟨fun s hs ↦ pairCount_truncation A hs ▸ hr s hs,
      fun n hk hn ↦ prefixCount_truncation A hn ▸ hd n hn hk⟩
  · rintro ⟨hr, hd⟩
    exact ⟨fun s hs ↦ (pairCount_truncation A hs).symm ▸ hr s hs,
      fun n hn hk ↦ (prefixCount_truncation A hn).symm ▸ hd n hk hn⟩

private def decode (f : ℕ → Bool) : Set ℕ := {n | f n = true}

private theorem closed_prefix_test (q : ℕ → ℕ) (k T : ℕ) :
    IsClosed {f : ℕ → Bool | truncation (decode f) T ∈ survivors q k T} := by
  classical
  apply isOpen_compl_iff.mp
  refine isOpen_pi_iff.mpr ?_
  intro f hf
  refine ⟨Finset.range (T + 1), fun i ↦ {f i}, fun i _ ↦ ⟨isOpen_discrete _, by simp⟩, ?_⟩
  intro g hg
  have heq : truncation (decode g) T = truncation (decode f) T := by
    ext i
    simp only [mem_truncation, decode, Set.mem_ofPred_eq]
    by_cases hi : i ∈ Finset.range (T + 1)
    · have hgi : g i = f i := Set.mem_pi.mp hg i hi
      rw [hgi]
    · simp only [hi, false_and]
  change truncation (decode g) T ∉ survivors q k T
  exact heq ▸ hf

/-- Compatible finite witnesses exist whenever every finite test has a survivor. -/
theorem finite_to_infinite (q : ℕ → ℕ) (k : ℕ)
    (h : ∀ T, (survivors q k T).Nonempty) :
    ∃ A : Set ℕ, (∀ s, sumRep A s ≤ k) ∧
      ∀ n, k ≤ n → q n ≤ (A ∩ Icc 1 n).ncard := by
  classical
  let K (T : ℕ) : Set (ℕ → Bool) := {f | truncation (decode f) T ∈ survivors q k T}
  have nested (T : ℕ) : K (T + 1) ⊆ K T := by
    intro f hf
    change truncation (decode f) (T + 1) ∈ survivors q k (T + 1) at hf
    obtain ⟨hr, hd⟩ := (truncation_mem q k (T + 1) (decode f)).mp hf
    exact (truncation_mem q k T (decode f)).mpr
      ⟨fun s hs ↦ hr s (Nat.le_succ_of_le hs),
        fun n hk hn ↦ hd n hk (Nat.le_succ_of_le hn)⟩
  have inhabited (T : ℕ) : (K T).Nonempty := by
    obtain ⟨B, hB⟩ := h T
    refine ⟨fun n ↦ decide (n ∈ B), ?_⟩
    have hsub := (mem_survivors.mp hB).1
    have heq : truncation (decode (fun n ↦ decide (n ∈ B))) T = B := by
      ext i
      simp only [truncation, Finset.mem_filter, decode, Set.mem_ofPred_eq, decide_eq_true_eq]
      exact ⟨And.right, fun hi ↦ ⟨hsub hi, hi⟩⟩
    change truncation (decode (fun n ↦ decide (n ∈ B))) T ∈ survivors q k T
    rwa [heq]
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K nested inhabited (closed_prefix_test q k 0).isCompact (closed_prefix_test q k)
  have allFits (T : ℕ) := (truncation_mem q k T (decode f)).mp (Set.mem_iInter.mp hf T)
  exact ⟨decode f, fun s ↦ (allFits s).1 s le_rfl,
    fun n hn ↦ (allFits n).2 n hn le_rfl⟩

/-- The least integer count meeting the density inequality with multiplier `k + 1`. -/
noncomputable def quota (g : ℕ → ℝ) (k n : ℕ) : ℕ :=
  ⌈‖√(n : ℝ) / g n‖ / (↑(k + 1) : ℝ)⌉₊

private theorem quota_le (g : ℕ → ℝ) (k n c : ℕ) :
    quota g k n ≤ c ↔ ‖√(n : ℝ) / g n‖ ≤ (↑(k + 1) : ℝ) * (c : ℝ) := by
  rw [quota, Nat.ceil_le, div_le_iff₀ (by positivity), mul_comm]

private theorem cap_of_limsup_ne_top {A : Set ℕ}
    (h : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤) :
    ∃ k : ℕ, ∀ n, sumRep A n ≤ k := by
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp h
  have hlt : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop < (↑(b + 1) : ℕ∞) := by
    rw [← hb]
    exact_mod_cast Nat.lt_succ_self b
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
  refine ⟨max b ((Finset.range N).sup (sumRep A)), fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · have hh : sumRep A n < b + 1 := by exact_mod_cast hN n hn
    exact (Nat.le_of_lt_succ hh).trans (le_max_left ..)
  · exact (Finset.le_sup (f := sumRep A) (Finset.mem_range.mpr (by omega : n < N))).trans
      (le_max_right ..)

private theorem ne_limsup_top_of_cap {A : Set ℕ} {k : ℕ} (h : ∀ s, sumRep A s ≤ k) :
    limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤ := by
  have hle : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≤ (k : ℕ∞) :=
    limsup_le_of_le (h := Eventually.of_forall (fun n ↦ by exact_mod_cast h n))
  exact (hle.trans_lt (ENat.natCast_lt_top k)).ne

/-- A single finite cutoff must rule out each combination of a fixed cap,
density constant and starting index. Enlarging `k` covers any such triple. -/
theorem erdos40For_iff_finite (g : ℕ → ℝ) :
    Erdos40.Erdos40For g ↔ ∀ k : ℕ, ∃ T ≥ k, survivors (quota g k) k T = ∅ := by
  classical
  constructor
  · intro h k
    by_contra! hnone
    have hne (T : ℕ) : (survivors (quota g k) k T).Nonempty := by
      by_cases hk : k ≤ T
      · exact hnone T hk
      · refine ⟨truncation ∅ T, (truncation_mem _ _ _ _).mpr ⟨?_, ?_⟩⟩
        · simp [sumRep_def]
        · intro n hn hn'
          omega
    obtain ⟨A, hr, hd⟩ := finite_to_infinite _ k hne
    apply ne_limsup_top_of_cap hr
    apply h A
    apply Asymptotics.IsBigO.of_bound (↑(k + 1) : ℝ)
    filter_upwards [eventually_ge_atTop k] with n hn
    simpa only [Real.norm_natCast] using (quota_le g k n _).mp (hd n hn)
  · intro h A hdense
    by_contra hlim
    obtain ⟨r, hr⟩ := cap_of_limsup_ne_top hlim
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hdense
    obtain ⟨L, hL⟩ := eventually_atTop.mp hC
    obtain ⟨c, hc⟩ := exists_nat_ge C
    let k := max r (max c L)
    have hrk : r ≤ k := le_max_left ..
    have hck : c ≤ k := (le_max_left c L).trans (le_max_right ..)
    have hLk : L ≤ k := (le_max_right c L).trans (le_max_right ..)
    have hCk : C ≤ (↑(k + 1) : ℝ) := hc.trans (by exact_mod_cast Nat.le_succ_of_le hck)
    obtain ⟨T, _, hT⟩ := h k
    have hmem : truncation A T ∈ survivors (quota g k) k T := by
      apply (truncation_mem ..).mpr
      refine ⟨fun s _ ↦ (hr s).trans hrk, fun n hn _ ↦ ?_⟩
      apply (quota_le ..).mpr
      have hb := hL n (hLk.trans hn)
      simp only [Real.norm_natCast] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hCk (Nat.cast_nonneg _))
    simp only [hT, Finset.notMem_empty] at hmem

/-- An increasing multiplier can be kept below any specified level on a
prescribed finite window, while still tending to infinity. -/
private theorem slow_multiplier (T : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧ Monotone b ∧ Tendsto b atTop atTop ∧
      ∀ j n, n ≤ T j → b n ≤ j + 1 := by
  classical
  let endpoint (j : ℕ) := max j (T j)
  have reaches (n : ℕ) : ∃ j, n ≤ endpoint j := ⟨n, le_max_left ..⟩
  let b (n : ℕ) := Nat.find (reaches n) + 1
  refine ⟨b, fun n ↦ Nat.succ_pos _, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Nat.succ_le_succ (Nat.find_min' (reaches m)
      (hmn.trans (Nat.find_spec (reaches n))))
  · refine tendsto_atTop.2 fun j ↦ ?_
    filter_upwards [eventually_ge_atTop ((Finset.range j).sup endpoint + 1)] with n hn
    by_contra! hj
    have hi : Nat.find (reaches n) < j := (Nat.lt_succ_self _).trans (show b n < j from hj)
    have hupper := Finset.le_sup (f := endpoint) (Finset.mem_range.mpr hi)
    have hlower := Nat.find_spec (reaches n)
    omega
  · intro j n hn
    exact Nat.succ_le_succ (Nat.find_min' (reaches n) (hn.trans (le_max_right ..)))

/-- If an individual denominator works, it can be multiplied by a positive,
nondecreasing function tending to infinity and the new denominator still works. -/
theorem exists_unbounded_multiplier {g : ℕ → ℝ} (h : Erdos40.Erdos40For g) :
    ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧ Monotone b ∧ Tendsto b atTop atTop ∧
      Erdos40.Erdos40For (fun n ↦ g n * (b n : ℝ)) := by
  classical
  let k (r : ℕ) := (r + 1)^2
  choose T hlarge hempty using fun r : ℕ ↦ (erdos40For_iff_finite g).mp h (k r)
  obtain ⟨b, hpos, hmono, hlim, hsmall⟩ := slow_multiplier T
  refine ⟨b, hpos, hmono, hlim, (erdos40For_iff_finite _).mpr ?_⟩
  intro r
  have hr : r ≤ k r := by dsimp [k]; nlinarith
  refine ⟨T r, hr.trans (hlarge r), Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro B hB
  obtain ⟨hsub, hrep, hdense⟩ := mem_survivors.mp hB
  have hmem : B ∈ survivors (quota g (k r)) (k r) (T r) := by
    apply mem_survivors.mpr
    refine ⟨hsub, fun s hs ↦ (hrep s hs).trans hr, fun n hn hkn ↦ ?_⟩
    apply le_trans _ (hdense n hn (hr.trans hkn))
    apply Nat.ceil_mono
    change ‖√(n : ℝ) / g n‖ / (↑(k r + 1) : ℝ) ≤
      ‖√(n : ℝ) / (g n * (b n : ℝ))‖ / (↑(r + 1) : ℝ)
    rw [← div_div, norm_div (√(n : ℝ) / g n), Real.norm_natCast, div_div]
    have hprod : b n * (r + 1) ≤ k r + 1 := by
      have hp := Nat.mul_le_mul_right (r + 1) (hsmall r n hn)
      simpa only [k, pow_two] using hp.trans (Nat.le_succ _)
    apply div_le_div_of_nonneg_left (norm_nonneg _) _ (by exact_mod_cast hprod)
    have hb := hpos n
    positivity
  simp only [hempty r, Finset.notMem_empty] at hmem

/-- In the class from the original question, every member admits another
member whose ratio to it tends to infinity. -/
theorem no_maximal_growth_rate {g : ℕ → ℝ} (hg : Tendsto g atTop atTop)
    (h : Erdos40.Erdos40For g) :
    ∃ G : ℕ → ℝ, Tendsto G atTop atTop ∧ Erdos40.Erdos40For G ∧
      Tendsto (fun n ↦ G n / g n) atTop atTop := by
  obtain ⟨b, _, _, hlim, hmul⟩ := exists_unbounded_multiplier h
  have hb : Tendsto (fun n ↦ (b n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hlim
  refine ⟨fun n ↦ g n * (b n : ℝ), hg.atTop_mul_atTop₀ hb, hmul, hb.congr' ?_⟩
  filter_upwards [hg.eventually_ge_atTop 1] with n hn
  exact (mul_div_cancel_left₀ _ (by linarith : g n ≠ 0)).symm

/-- Each row is the counting function of a prefix satisfying the cap. -/
def profiles (k T : ℕ) : Finset (Fin (T + 1) → ℕ) :=
  (survivors (fun _ ↦ 0) k T).image fun B i ↦ prefixCount B i.val

private def dominated {d : ℕ} (p v : Fin d → ℕ) : Bool :=
  decide (∀ i, p i ≤ v i) && !decide (∀ i, v i ≤ p i)

private theorem dominated_iff {d : ℕ} {p v : Fin d → ℕ} :
    dominated p v = true ↔ p < v := by
  rw [lt_iff_le_not_ge]
  simp only [dominated, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, Pi.le_def]

/-- Delete each row dominated coordinatewise by another row. The remaining
table is independent of the denominator and can be shared between tests. -/
def maximalProfiles (k T : ℕ) : Finset (Fin (T + 1) → ℕ) :=
  (profiles k T).filter fun p ↦ ((profiles k T).filter (fun v ↦ dominated p v)) = ∅

private theorem survives_iff_profile (q : ℕ → ℕ) (k T : ℕ) :
    (survivors q k T).Nonempty ↔ ∃ p ∈ maximalProfiles k T,
      ∀ i : Fin (T + 1), k ≤ i.val → q i.val ≤ p i := by
  classical
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨hsub, hrep, hd⟩ := mem_survivors.mp hB
    have hB0 : B ∈ survivors (fun _ ↦ 0) k T :=
      mem_survivors.mpr ⟨hsub, hrep, fun _ _ _ ↦ Nat.zero_le _⟩
    let p (i : Fin (T + 1)) := prefixCount B i.val
    have hp : p ∈ profiles k T := Finset.mem_image.mpr ⟨B, hB0, rfl⟩
    obtain ⟨v, hpv, hv⟩ := (profiles k T).exists_le_maximal hp
    refine ⟨v, Finset.mem_filter.mpr ⟨hv.1, ?_⟩,
      fun i hi ↦ (hd i.val (Nat.le_of_lt_succ i.isLt) hi).trans (hpv i)⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwmem, hlt⟩ := Finset.mem_filter.mp hw
    have hpw := dominated_iff.mp hlt
    exact hpw.not_ge (hv.2 hwmem hpw.le)
  · rintro ⟨p, hp, hd⟩
    have hp' : p ∈ profiles k T := (Finset.mem_filter.mp hp).1
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨hsub, hrep, _⟩ := mem_survivors.mp hB
    exact ⟨B, mem_survivors.mpr ⟨hsub, hrep,
      fun n hn hk ↦ hd ⟨n, Nat.lt_succ_of_le hn⟩ hk⟩⟩

/-- In each row, a large enough density demand at one coordinate excludes
that whole row and all profiles below it. -/
theorem finite_iff_profile_obstruction (g : ℕ → ℝ) (k T : ℕ) :
    survivors (quota g k) k T = ∅ ↔ ∀ p ∈ maximalProfiles k T,
      ∃ i : Fin (T + 1), k ≤ i.val ∧
        (↑(k + 1) : ℝ) * (p i : ℝ) < ‖√(i.val : ℝ) / g i.val‖ := by
  classical
  rw [← Finset.not_nonempty_iff_eq_empty, survives_iff_profile]
  push Not
  simp only [← not_le, quota_le]

end Erdos40Windows

/-
Sidon counterexamples for oscillating denominators

Choose a prime between each scale s and 2s. Its block has at least s elements
and finishes before the next scale 32s². These inequalities give square-root
density at the specified peaks and fourth-root density in every sufficiently
large prefix.
-/

namespace Erdos40Peaks

-- Adapted from the accepted open-math-agents proof proofs/Erdos44.sidon_set_lower_bound.lean
-- (lemma bosePrefix_sidon), generalised from the shift 1 to an arbitrary shift t.
lemma bose_sidon {p k t : ℕ} (hp : Nat.Prime p) (hk : k < p) (hp2 : p ≠ 2) :
    IsSidon
      (((Finset.range (k + 1)).image (fun a => 2 * p * a + (a * a) % p + t) : Finset ℕ) :
        Set ℕ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  rw [Finset.mem_coe, Finset.mem_image] at hi₁ hj₁ hi₂ hj₂
  obtain ⟨a, ha, rfl⟩ := hi₁
  obtain ⟨c, hc, rfl⟩ := hj₁
  obtain ⟨b, hb, rfl⟩ := hi₂
  obtain ⟨d, hd, rfl⟩ := hj₂
  have ha_lt : a < p := by rw [Finset.mem_range] at ha; omega
  have hb_lt : b < p := by rw [Finset.mem_range] at hb; omega
  have hc_lt : c < p := by rw [Finset.mem_range] at hc; omega
  have hd_lt : d < p := by rw [Finset.mem_range] at hd; omega
  have hpos : 0 < p := hp.pos
  have hsum' :
      2 * p * (a + b) + ((a * a) % p + (b * b) % p) =
        2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by
    have hcancel :
        2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) =
          2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := by
      omega
    calc
      2 * p * (a + b) + ((a * a) % p + (b * b) % p)
          = 2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) := by ring
      _ = 2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := hcancel
      _ = 2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by ring
  have hσ : (a * a) % p + (b * b) % p < 2 * p := by
    have haσ : (a * a) % p < p := Nat.mod_lt _ hpos
    have hbσ : (b * b) % p < p := Nat.mod_lt _ hpos
    omega
  have hτ : (c * c) % p + (d * d) % p < 2 * p := by
    have hcτ : (c * c) % p < p := Nat.mod_lt _ hpos
    have hdτ : (d * d) % p < p := Nat.mod_lt _ hpos
    omega
  have htwo : 0 < 2 * p := by omega
  have hquot (q r : ℕ) (hr : r < 2 * p) :
      (r + (2 * p) * q) / (2 * p) = q := by
    rw [Nat.add_mul_div_left _ _ htwo, Nat.div_eq_of_lt hr, zero_add]
  have hidx : a + b = c + d := by
    have hleft := hquot (a + b) ((a * a) % p + (b * b) % p) hσ
    have hright := hquot (c + d) ((c * c) % p + (d * d) % p) hτ
    have hcomm :
        (a * a) % p + (b * b) % p + (2 * p) * (a + b) =
          (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by
      calc
        (a * a) % p + (b * b) % p + (2 * p) * (a + b)
            = (2 * p) * (a + b) + ((a * a) % p + (b * b) % p) := by ac_rfl
        _ = (2 * p) * (c + d) + ((c * c) % p + (d * d) % p) := hsum'
        _ = (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by ac_rfl
    rw [← hleft, ← hright, hcomm]
  have hres :
      (a * a) % p + (b * b) % p = (c * c) % p + (d * d) % p :=
    Nat.add_left_cancel (n := 2 * p * (a + b)) (by simpa [hidx] using hsum')
  have hsq :
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
    calc
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2
          = (((a * a) % p : ℕ) : ZMod p) + (((b * b) % p : ℕ) : ZMod p) := by
            simp [pow_two, ZMod.natCast_mod]
      _ = ((((a * a) % p + (b * b) % p : ℕ) : ZMod p)) := by
            push_cast
            rfl
      _ = ((((c * c) % p + (d * d) % p : ℕ) : ZMod p)) := by
            exact congr_arg (Nat.cast : ℕ → ZMod p) hres
      _ = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
            simp [pow_two, ZMod.natCast_mod]
  have hsumZ : (a : ZMod p) + b = (c : ZMod p) + d := by
    have : ((a + b : ℕ) : ZMod p) = (c + d : ℕ) := congr_arg (Nat.cast : ℕ → ZMod p) hidx
    simpa [Nat.cast_add] using this
  have htwo_mul :
      (2 : ZMod p) * (a : ZMod p) * b = (2 : ZMod p) * (c : ZMod p) * d := by
    have hleft : (2 : ZMod p) * a * b = ((a : ZMod p) + b) ^ 2 - ((a : ZMod p) ^ 2 + b ^ 2) := by
      ring
    have hright : (2 : ZMod p) * c * d = ((c : ZMod p) + d) ^ 2 - ((c : ZMod p) ^ 2 + d ^ 2) := by
      ring
    rw [hleft, hright, hsumZ, hsq]
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    rw [ne_eq, ← Nat.cast_two, ZMod.natCast_eq_zero_iff]
    intro hdiv
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have : 2 ≤ p := hp.two_le
    omega
  have hprod : (a : ZMod p) * b = (c : ZMod p) * d := by
    apply mul_left_cancel₀ htwo_ne
    simpa [mul_assoc, mul_left_comm, mul_comm] using htwo_mul
  have hfactor : ((c : ZMod p) - a) * ((c : ZMod p) - b) = 0 := by
    calc
      ((c : ZMod p) - a) * (c - b)
          = (c : ZMod p) ^ 2 - ((a : ZMod p) + b) * c + a * b := by ring
      _ = (c : ZMod p) ^ 2 - ((c : ZMod p) + d) * c + c * d := by rw [hsumZ, hprod]
      _ = 0 := by ring
  have hc_eq : (c : ZMod p) = a ∨ (c : ZMod p) = b := by
    rcases mul_eq_zero.mp hfactor with hca | hcb
    · left
      exact sub_eq_zero.mp hca
    · right
      exact sub_eq_zero.mp hcb
  have lift {x y : ℕ} (hx : x < p) (hy : y < p) (hxy : (x : ZMod p) = y) : x = y := by
    have hmod : x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod
  rcases hc_eq with hca | hcb
  · have hac : a = c := lift ha_lt hc_lt hca.symm
    have hbd : b = d := by omega
    left
    subst hac
    subst hbd
    exact ⟨rfl, rfl⟩
  · have hab : b = c := lift hb_lt hc_lt hcb.symm
    have had : a = d := by omega
    right
    subst hab
    subst had
    exact ⟨rfl, rfl⟩

/-- Gluing a Sidon block `C`, sitting high above a Sidon set `B` and with gaps at least `s`,
keeps the Sidon property. -/
lemma union_sidon (B C : Set ℕ) (s M W : ℕ) (hB : IsSidon B) (hC : IsSidon C)
    (hBs : ∀ b ∈ B, b < s) (hCM : ∀ c ∈ C, M ≤ c ∧ c < M + W)
    (h1 : W + s ≤ M) (h2 : 2 * s ≤ M)
    (hgap : ∀ c ∈ C, ∀ c' ∈ C, c = c' ∨ c + s ≤ c' ∨ c' + s ≤ c) :
    IsSidon (B ∪ C) := by
  have key : ∀ x ∈ B ∪ C, (x ∈ B ∧ x < s) ∨ (x ∈ C ∧ M ≤ x ∧ x < M + W) := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, hBs x hx⟩
    · exact Or.inr ⟨hx, hCM x hx⟩
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs
  rcases key _ hi₁ with ⟨m1, b1⟩ | ⟨m1, b1, b1'⟩ <;>
  rcases key _ hj₁ with ⟨m2, b2⟩ | ⟨m2, b2, b2'⟩ <;>
  rcases key _ hi₂ with ⟨m3, b3⟩ | ⟨m3, b3, b3'⟩ <;>
  rcases key _ hj₂ with ⟨m4, b4⟩ | ⟨m4, b4, b4'⟩ <;>
  first
  | exact hB _ m1 _ m2 _ m3 _ m4 hs
  | exact hC _ m1 _ m2 _ m3 _ m4 hs
  | omega
  | (have g := hgap _ m1 _ m2; omega)
  | (have g := hgap _ m1 _ m4; omega)
  | (have g := hgap _ m3 _ m2; omega)
  | (have g := hgap _ m3 _ m4; omega)

/-- The block used for the prime `p`. -/
def blk (p : ℕ) : Finset ℕ :=
  (Finset.range (p - 1 + 1)).image (fun a => 2 * p * a + (a * a) % p + (4 * p * p + 1))

lemma blk_gap (p a b : ℕ) (hp : 0 < p) (hab : a < b) :
    2 * p * a + (a * a) % p + (4 * p * p + 1) + p ≤ 2 * p * b + (b * b) % p + (4 * p * p + 1) := by
  have h1 : 2 * p * (a + 1) ≤ 2 * p * b := Nat.mul_le_mul_left _ hab
  have h2 : (a * a) % p < p := Nat.mod_lt _ hp
  have h3 : 2 * p * (a + 1) = 2 * p * a + 2 * p := by ring
  omega

lemma blk_mem (p x : ℕ) (hp : 0 < p) (hx : x ∈ blk p) :
    4 * p * p + 1 ≤ x ∧ x < 4 * p * p + 1 + 2 * p * p := by
  unfold blk at hx
  rw [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [Finset.mem_range] at ha
  have h1 : 2 * p * (a + 1) ≤ 2 * p * p := Nat.mul_le_mul_left _ (by omega)
  have h2 : (a * a) % p < p := Nat.mod_lt _ hp
  have h3 : 2 * p * (a + 1) = 2 * p * a + 2 * p := by ring
  omega

lemma blk_sidon (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : IsSidon (blk p : Set ℕ) :=
  bose_sidon hp (by have := hp.pos; omega) hp2

lemma blk_card (p : ℕ) (hp : 0 < p) : (blk p).card = p := by
  unfold blk
  rw [Finset.card_image_of_injOn, Finset.card_range]
  · omega
  · intro a _ b _ hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := blk_gap p a b hp h
      simp only at hab
      omega
    · have := blk_gap p b a hp h
      simp only at hab
      omega

lemma blk_gaps (p : ℕ) (hp : 0 < p) :
    ∀ c ∈ (blk p : Set ℕ), ∀ c' ∈ (blk p : Set ℕ), c = c' ∨ c + p ≤ c' ∨ c' + p ≤ c := by
  intro c hc c' hc'
  rw [Finset.mem_coe] at hc hc'
  unfold blk at hc hc'
  rw [Finset.mem_image] at hc hc'
  obtain ⟨a, _, rfl⟩ := hc
  obtain ⟨b, _, rfl⟩ := hc'
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inr (Or.inl (blk_gap p a b hp h))
  · exact Or.inl (by rw [h])
  · exact Or.inr (Or.inr (blk_gap p b a hp h))

/-- The index of each peak is fixed before the primes or the denominator are chosen. -/
def scale : ℕ → ℕ
  | 0 => 2
  | j + 1 => 32 * scale j ^ 2

private theorem scale_large (j : ℕ) : j + 2 ≤ scale j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [scale]
    nlinarith [Nat.le_mul_self (scale j)]

private theorem scale_mono : StrictMono scale := by
  apply strictMono_nat_of_lt_succ
  intro j
  have := scale_large j
  rw [scale]
  nlinarith [Nat.le_mul_self (scale j)]

private theorem has_prime (j : ℕ) : ∃ p : ℕ, p.Prime ∧ scale j < p ∧ p ≤ 2 * scale j :=
  Nat.exists_prime_lt_and_le_two_mul _ (by have := scale_large j; omega)

private noncomputable def prime (j : ℕ) := (has_prime j).choose

private theorem prime_spec (j : ℕ) :
    (prime j).Prime ∧ scale j < prime j ∧ prime j ≤ 2 * scale j :=
  (has_prime j).choose_spec

private noncomputable def stage : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => stage j ∪ blk (prime j)

private theorem stage_mono : Monotone stage :=
  monotone_nat_of_le_succ fun _ ↦ Finset.subset_union_left

private theorem block_high (j : ℕ) {x : ℕ} (hx : x ∈ blk (prime j)) :
    1 ≤ x ∧ x < scale (j + 1) := by
  obtain ⟨hp, _, hupper⟩ := prime_spec j
  have hsq := Nat.mul_le_mul hupper hupper
  have ⟨hlo, hhi⟩ := blk_mem _ _ hp.pos hx
  have hs := scale_large j
  rw [scale]
  constructor <;> nlinarith

private theorem stage_below (j : ℕ) {x : ℕ} (hx : x ∈ stage j) : x < scale j := by
  induction j with
  | zero => simp [stage] at hx
  | succ j ih =>
    rcases Finset.mem_union.mp hx with h | h
    · exact (ih h).trans (scale_mono (Nat.lt_succ_self _))
    · exact (block_high j h).2

private theorem stage_sidon (j : ℕ) : IsSidon (stage j : Set ℕ) := by
  induction j with
  | zero => intro i hi; simp [stage] at hi
  | succ j ih =>
    obtain ⟨hp, hlow, _⟩ := prime_spec j
    have hs := scale_large j
    have hp0 := hp.pos
    have hpp := Nat.le_mul_self (prime j)
    change IsSidon (↑(stage j ∪ blk (prime j)) : Set ℕ)
    rw [Finset.coe_union]
    exact union_sidon _ _ (prime j) (4 * prime j * prime j + 1) (2 * prime j * prime j)
      ih (blk_sidon _ hp (by omega)) (fun _ hx ↦ (stage_below j hx).trans hlow)
      (fun x hx ↦ blk_mem _ x hp0 hx) (by nlinarith) (by nlinarith) (blk_gaps _ hp0)

private def peakSet : Set ℕ := ⋃ j, (stage j : Set ℕ)

private theorem peakSet_sidon : IsSidon peakSet := by
  intro a ha b hb c hc d hd h
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hc
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hd
  let t := max (max i j) (max k l)
  have sub (m : ℕ) (hm : m ≤ t) : (stage m : Set ℕ) ⊆ (stage t : Set ℕ) := stage_mono hm
  exact stage_sidon t _ (sub i (by dsimp [t]; omega) hi) _ (sub j (by dsimp [t]; omega) hj)
    _ (sub k (by dsimp [t]; omega) hk) _ (sub l (by dsimp [t]; omega) hl) h

open Filter Real Set AdditiveCombinatorics

private theorem bounded_pairs {A : Set ℕ} (hA : IsSidon A) (s : ℕ) : sumRep A s ≤ 2 := by
  classical
  rw [sumRep_def]
  let pairs := (Finset.HasAntidiagonal.antidiagonal s).filter (fun p : ℕ × ℕ ↦ p.1 ∈ A ∧ p.2 ∈ A)
  change pairs.card ≤ 2
  by_cases h : pairs.Nonempty
  · obtain ⟨p, hp⟩ := h
    have hsub : pairs ⊆ {p, p.swap} := by
      intro q hq
      obtain ⟨hs, ha, hb⟩ := Finset.mem_filter.mp hp
      obtain ⟨ht, hc, hd⟩ := Finset.mem_filter.mp hq
      have heq := (Finset.HasAntidiagonal.mem_antidiagonal.mp ht).trans
        (Finset.HasAntidiagonal.mem_antidiagonal.mp hs).symm
      rcases hA _ hc _ ha _ hd _ hb heq with h | h
      · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h.1 h.2))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Prod.ext h.1 h.2))
    exact (Finset.card_le_card hsub).trans (by
      simpa only [Finset.card_singleton] using Finset.card_insert_le p {p.swap})
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]
    decide

private noncomputable abbrev count (n : ℕ) := (peakSet ∩ Icc 1 n).ncard

private theorem count_after (j : ℕ) {n : ℕ} (hn : scale (j+1) ≤ n) : scale j ≤ count n := by
  have hsub : (blk (prime j) : Set ℕ) ⊆ peakSet ∩ Icc 1 n := by
    intro x hx
    have h := block_high j hx
    exact ⟨Set.mem_iUnion.mpr ⟨j+1, Finset.mem_union_right _ hx⟩, h.1, h.2.le.trans hn⟩
  have h := Set.ncard_le_ncard hsub ((Set.finite_Icc 1 n).inter_of_right peakSet)
  rw [Set.ncard_coe_finset, blk_card _ (prime_spec j).1.pos] at h
  exact (prime_spec j).2.1.le.trans h

private theorem between {n : ℕ} (hn : scale 1 ≤ n) :
    ∃ j, scale (j+1) ≤ n ∧ n < scale (j+2) := by
  have ex : ∃ j, n < scale (j+2) := ⟨n, by have := scale_large (n+2); omega⟩
  refine ⟨Nat.find ex, ?_, Nat.find_spec ex⟩
  cases he : Nat.find ex with
  | zero => exact hn
  | succ i =>
    have hi : i < Nat.find ex := by omega
    exact Nat.le_of_not_gt (Nat.find_min ex hi)

private theorem quarter_bound {n : ℕ} (hn : scale 1 ≤ n) :
    √(√(n : ℝ)) ≤ 16 * (count n : ℝ) := by
  obtain ⟨j, hlow, hhigh⟩ := between hn
  have hc : (scale j : ℝ) ≤ (count n : ℝ) := by exact_mod_cast count_after j hlow
  have hscale : scale (j+2) = 32^3 * (scale j)^4 := by
    rw [scale, scale]
    ring
  have hnle : (n : ℝ) ≤ 32^3 * (scale j : ℝ)^4 := by
    rw [hscale] at hhigh
    exact_mod_cast hhigh.le
  apply le_trans _ (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 16))
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [sq_nonneg ((scale j : ℝ)^2)]

/-- At all sufficiently large indices a fourth-root denominator suffices,
except that the explicit previous block can cover the entire density demand
on its own. Either alternative supplies the same fixed Sidon counterexample. -/
theorem excluded_by_peaks {g : ℕ → ℝ} (hg : Tendsto g atTop atTop)
    (hshape : ∀ᶠ n : ℕ in atTop, √(√(n : ℝ)) ≤ g n ∨
      ∃ j, scale (j+1) ≤ n ∧ √(n : ℝ) ≤ (scale j : ℝ) * g n) :
    ¬ Erdos40.Erdos40For g := by
  intro h
  have hd : (fun n : ℕ ↦ √(n : ℝ) / g n) =O[atTop] (fun n ↦ (count n : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 16
    filter_upwards [hshape, hg.eventually_ge_atTop 1, eventually_ge_atTop (scale 1)] with n hn hp hlarge
    have hpos : 0 < g n := lt_of_lt_of_le zero_lt_one hp
    rw [Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hpos.le), Real.norm_natCast]
    rcases hn with hq | ⟨j, hj, hq⟩
    · apply le_trans _ (quarter_bound hlarge)
      apply (div_le_iff₀ hpos).mpr
      calc
        √(n : ℝ) = √(√(n : ℝ)) * √(√(n : ℝ)) := (Real.mul_self_sqrt (Real.sqrt_nonneg _)).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
    · have hcnt : (scale j : ℝ) ≤ (count n : ℝ) := by exact_mod_cast count_after j hj
      exact ((div_le_iff₀ hpos).mpr hq).trans (by linarith [Nat.cast_nonneg (α := ℝ) (count n)])
  have hle : limsup (fun n ↦ (sumRep peakSet n : ℕ∞)) atTop ≤ (2 : ℕ∞) :=
    limsup_le_of_le (h := Eventually.of_forall (fun n ↦ by exact_mod_cast bounded_pairs peakSet_sidon n))
  rw [h peakSet hd] at hle
  exact (ENat.natCast_lt_top 2).not_ge hle

private theorem sqrt_on_band {j n d : ℕ} (hn : n ≤ d * scale (j+1)) :
    √(n : ℝ) ≤ (scale j : ℝ) * √(32 * (d : ℝ)) := by
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 32 * (d : ℝ))]
  have hle : (n : ℝ) ≤ (d : ℝ) * (32 * (scale j : ℝ)^2) := by
    rw [scale] at hn
    exact_mod_cast hn
  linarith

/-- The denominator may grow arbitrarily slowly on the specified bands.
Only its divergence there and the fourth-root bound elsewhere are needed. -/
theorem excluded_off_bands {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) (d : ℕ)
    (hoff : ∀ᶠ n : ℕ in atTop,
      (¬ ∃ j, scale (j+1) ≤ n ∧ n ≤ d * scale (j+1)) → √(√(n : ℝ)) ≤ g n) :
    ¬ Erdos40.Erdos40For g := by
  apply excluded_by_peaks hg
  filter_upwards [hoff, hg.eventually_ge_atTop (√(32 * (d : ℝ)))] with n hout hn
  by_cases hb : ∃ j, scale (j+1) ≤ n ∧ n ≤ d * scale (j+1)
  · obtain ⟨j, hj, htop⟩ := hb
    exact Or.inr ⟨j, hj, (sqrt_on_band htop).trans (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _))⟩
  · exact Or.inl (hout hb)

/-- Follow an arbitrary divergent function on the fixed bands and use the
fourth root between them. For example, the input can be a logarithm. -/
noncomputable def onBands (h : ℕ → ℝ) (d n : ℕ) : ℝ := by
  classical
  exact if ∃ j, scale (j+1) ≤ n ∧ n ≤ d * scale (j+1) then h n else √(√(n : ℝ))

theorem onBands_counterexample {h : ℕ → ℝ} (hh : Tendsto h atTop atTop) (d : ℕ) :
    Tendsto (onBands h d) atTop atTop ∧ ¬ Erdos40.Erdos40For (onBands h d) := by
  classical
  have hquarter : Tendsto (fun n : ℕ ↦ √(√(n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hg : Tendsto (onBands h d) atTop atTop := by
    refine tendsto_atTop.2 fun x ↦ ?_
    filter_upwards [hh.eventually_ge_atTop x, hquarter.eventually_ge_atTop x] with n hn hn'
    unfold onBands
    split <;> assumption
  exact ⟨hg, excluded_off_bands hg d (Eventually.of_forall fun n hout ↦ by
    simp only [onBands, if_neg hout, le_rfl])⟩

theorem logarithmic_bands_counterexample :
    ¬ Erdos40.Erdos40For (onBands (fun n ↦ Real.log ((n : ℝ) + 2)) 2) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith : ∀ n : ℕ, (n : ℝ) ≤ n + 2) tendsto_natCast_atTop_atTop
  exact (onBands_counterexample (Real.tendsto_log_atTop.comp hn) 2).2

private theorem admissible_const_mul {g : ℕ → ℝ} (h : Erdos40.Erdos40For g) {c : ℝ}
    (hc : 0 < c) : Erdos40.Erdos40For (fun n ↦ c * g n) := by
  intro A hA
  apply h A
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hA
  apply Asymptotics.IsBigO.of_bound (C * c)
  filter_upwards [hC] with n hn
  have he : ‖√(n : ℝ) / (c * g n)‖ = ‖√(n : ℝ) / g n‖ / c := by
    rw [mul_comm c, ← div_div, norm_div (√(n : ℝ) / g n), Real.norm_of_nonneg hc.le]
  change ‖√(n : ℝ) / (c * g n)‖ ≤ _ at hn
  rw [he] at hn
  exact ((div_le_iff₀ hc).mp hn).trans_eq (by ring)

/-- Arbitrarily far outside any fixed family of bands, an admissible
denominator must fall below every constant multiple of the fourth root. -/
theorem dips_off_bands {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) (h : Erdos40.Erdos40For g)
    (d m L : ℕ) : ∃ n ≥ L, (¬ ∃ j, scale (j+1) ≤ n ∧ n ≤ d * scale (j+1)) ∧
      (↑(m+1) : ℝ) * g n < √(√(n : ℝ)) := by
  have hm : 0 < (↑(m+1) : ℝ) := by positivity
  have hscaled := admissible_const_mul h hm
  by_contra hnone
  apply (excluded_off_bands (hg.const_mul_atTop hm) d ?_) hscaled
  filter_upwards [eventually_ge_atTop L] with n hn hout
  exact le_of_not_gt (fun hlt ↦ hnone ⟨n, hn, hout, hlt⟩)

/-- Keep the prescribed denominator wherever one of the completed blocks
already covers the demand. Elsewhere enforce the fourth-root lower bound. -/
noncomputable def modified (h : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if ∃ j, scale (j+1) ≤ n ∧ √(n : ℝ) ≤ (scale j : ℝ) * h n then h n
    else max (h n) (√(√(n : ℝ)))

theorem modified_bounds (h : ℕ → ℝ) (n : ℕ) :
    h n ≤ modified h n ∧ modified h n ≤ max (h n) (√(√(n : ℝ))) := by
  classical
  unfold modified
  split
  · exact ⟨le_rfl, le_max_left ..⟩
  · exact ⟨le_max_left .., le_rfl⟩

theorem modified_excluded {h : ℕ → ℝ} (hh : Tendsto h atTop atTop) :
    Tendsto (modified h) atTop atTop ∧ ¬ Erdos40.Erdos40For (modified h) := by
  classical
  have hg := tendsto_atTop_mono (fun n ↦ (modified_bounds h n).1) hh
  refine ⟨hg, excluded_by_peaks hg (Eventually.of_forall fun n ↦ ?_)⟩
  by_cases ht : ∃ j, scale (j+1) ≤ n ∧ √(n : ℝ) ≤ (scale j : ℝ) * h n
  · exact Or.inr (by simpa only [modified, if_pos ht] using ht)
  · exact Or.inl (by simpa only [modified, if_neg ht] using (le_max_right (h n) (√(√(n : ℝ)))))

/-- The counterexample denominator agrees with any prescribed divergent one
on arbitrarily late intervals of arbitrarily large multiplicative length. -/
theorem agreement_intervals {h : ℕ → ℝ} (hh : Tendsto h atTop atTop) (d L : ℕ) :
    ∃ M ≥ L, 0 < M ∧ ∀ n, M ≤ n → n ≤ d * M → modified h n = h n := by
  classical
  obtain ⟨U, hU⟩ := eventually_atTop.mp (hh.eventually_ge_atTop (√(32 * (d : ℝ))))
  let j := max L U
  have hM := scale_large (j+1)
  have hLj : L ≤ j := le_max_left ..
  have hUj : U ≤ j := le_max_right ..
  refine ⟨scale (j+1), by omega, by omega, fun n hn hn' ↦ ?_⟩
  have hf := hU n (by omega)
  have ht := (sqrt_on_band hn').trans (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _))
  exact if_pos (c := ∃ j, scale (j+1) ≤ n ∧ √(n : ℝ) ≤ (scale j : ℝ) * h n)
    ⟨j, hn, ht⟩

end Erdos40Peaks

open Filter Real Erdos40Windows

/-- A class defined by inequalities against precomputed finite tables. -/
def OMA.answer : Set (ℕ → ℝ) :=
  {g | Tendsto g atTop atTop ∧ ∀ k : ℕ, ∃ T ≥ k, ∀ p ∈ maximalProfiles k T,
    ∃ i : Fin (T + 1), k ≤ i.val ∧
      (↑(k + 1) : ℝ) * (p i : ℝ) < ‖√(i.val : ℝ) / g i.val‖}

theorem OMA.solution : Erdos40.erdos_40.answer = OMA.answer → type_of% @Erdos40.erdos_40 := by
  intro h
  rw [h]
  ext g
  change (_ ∧ Erdos40.Erdos40For g) ↔ (_ ∧ _)
  simp only [erdos40For_iff_finite, finite_iff_profile_obstruction]
