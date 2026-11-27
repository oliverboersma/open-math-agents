import OMAReductions.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2
import Mathlib

/- This step uses the positive-upper-density proof and the colour-class argument from @marcusbuffett, PR 5170. The original library notices follow. -/
namespace OMA.R_Erdos298_erdos_298_variants_natural_density_R1

open Filter

/-- Bounded-denominator extraction step of Bloom's unit fraction argument (arXiv:2112.03726),
in rational form. -/
def H1 : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → 0 < A.upperDensity →
    ∃ D : Finset ℕ, (∀ d ∈ D, 0 < d) ∧ ∀ N : ℕ, ∃ d ∈ D, ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ A ∩ Set.Ici N ∧ ∑ n ∈ S, (1 / n : ℚ) = 1 / d

/-- A finite rational sum obtainable arbitrarily far out can be repeated any finite
number of times. -/
def H2 : Prop :=
  ∀ (A : Set ℕ) (w : ℕ → ℚ) (r : ℚ),
    (∃ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ A ∩ Set.Ici N ∧ ∑ n ∈ S, w n = r) →
    ∀ k : ℕ, ∃ T : Finset ℕ, (↑T : Set ℕ) ⊆ A ∧ ∑ n ∈ T, w n = k * r

end OMA.R_Erdos298_erdos_298_variants_natural_density_R1
/-!
# Rational reciprocal extraction from positive upper density

This is the bounded-denominator form of Thomas Bloom's density theorem.
The regularity, pruning, concentration and Fourier arguments below assemble
@marcusbuffett's Erdős 299 reductions and proofs. The sparse-interval
extraction follows Bhavik Mehta and Thomas Bloom, b-mehta/unit-fractions,
commit 10ef71a300cf29e5f19beb2bbc723a035a0678de, under Apache-2.0.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. Other source notices
are retained at the corresponding arithmetic and Fourier arguments.
We keep the finite reciprocal identity in the rationals at extraction.
-/

section

/-! The regularity conditions and the finite extraction argument are from
Bhavik Mehta and Thomas Bloom, b-mehta/unit-fractions, src/final_results.lean,
commit 10ef71a300cf29e5f19beb2bbc723a035a0678de.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Used under Apache-2.0. The density-to-finite-set argument below is written
for the definition of upper density in Formal Conjectures. -/

namespace OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1
open Filter Finset

/-- The integers failing the prime-power, prime-factor count, or divisor
conditions occupy an arbitrarily small proportion of a long interval. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ y z : ℕ, 0 < y ∧ 4*y+4 ≤ z ∧ 4 / (y : ℝ) < ε ∧
    ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ, (E.card : ℝ) ≤ ε * N ∧
      ∀ n : ℕ, n < N → n ∉ E →
        (N : ℝ) ^ (1 - 1 / Real.log (Real.log N)) ≤ n ∧
        (∀ q : ℕ, IsPrimePow q → q ∣ n →
          (q : ℝ) ≤ (N : ℝ) ^ (1 - 8 / Real.log (Real.log N))) ∧
        (99 / 100 : ℝ) * Real.log (Real.log N) ≤ n.primeFactors.card ∧
        (n.primeFactors.card : ℝ) ≤ 2 * Real.log (Real.log N) ∧
        ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4 * u ≤ v ∧ v ≤ z

/-- Extraction of a reciprocal from a finite arithmetically regular set
with sufficient reciprocal mass. -/
def H2 : Prop :=
  ∀ y z : ℕ, 0 < y → 4*y+4 ≤ z →
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ, 0 ∉ B → B ⊆ range N →
      (∀ n ∈ B, (N : ℝ) ^ (1 - 1 / Real.log (Real.log N)) ≤ n ∧
        (∀ q : ℕ, IsPrimePow q → q ∣ n →
          (q : ℝ) ≤ (N : ℝ) ^ (1 - 8 / Real.log (Real.log N))) ∧
        (99 / 100 : ℝ) * Real.log (Real.log N) ≤ n.primeFactors.card ∧
        (n.primeFactors.card : ℝ) ≤ 2 * Real.log (Real.log N) ∧
        ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4 * u ≤ v ∧ v ≤ z) →
      4 / (y : ℝ) ≤ ∑ n ∈ B, (1 : ℝ) / n →
      ∃ d ∈ Icc y z, ∃ S ⊆ B, ∑ n ∈ S, (1 : ℚ) / n = 1 / d

theorem main : H1 → H2 → OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H1 := by
  classical
  intro sieve extract A hzero hdens
  let ε := A.upperDensity / 4
  have he : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨y,z,hy,hyz,hyε,hsieve⟩ := sieve ε he
  refine ⟨Icc y z, fun d hd => hy.trans_le (mem_Icc.mp hd).1, ?_⟩
  intro M
  have hf : ∃ᶠ N : ℕ in atTop, 3*ε < A.partialDensity Set.univ N := by
    apply frequently_lt_of_lt_limsup
    · exact isCoboundedUnder_le_of_eventually_le _ (Eventually.of_forall fun n =>
        show 0 ≤ A.partialDensity Set.univ n from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · change 3*ε < A.upperDensity
      dsimp [ε]
      linarith
  have hm : ∀ᶠ N : ℕ in atTop, (M : ℝ) ≤ ε * N := by
    obtain ⟨T, hT⟩ := exists_nat_ge ((M : ℝ) / ε)
    filter_upwards [eventually_ge_atTop T] with N hN
    have hh := (div_le_iff₀ he).mp (hT.trans (Nat.cast_le.mpr hN))
    linarith
  obtain ⟨N, hprop⟩ := (hf.and_eventually
    (hsieve.and ((extract y z hy hyz).and (hm.and (eventually_gt_atTop 0))))).exists
  obtain ⟨hd, ⟨E,hE,hgood⟩, hrec, hM, hN⟩ := hprop
  let U := (range N).filter (· ∈ A)
  have hc : (↑U : Set ℕ) = A ∩ Set.Iio N := by
    ext k
    simp [U, and_comm]
  have hd' : 3 * ε * N < U.card := by
    apply (lt_div_iff₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mp
    simpa [Set.partialDensity, Nat.ncard_Iio, ← hc] using hd
  let B := U \ (E ∪ range M)
  have hb (n) (hn : n ∈ B) := mem_sdiff.mp hn
  have hU (n) (hn : n ∈ B) := mem_filter.mp (hb n hn).1
  have hBN : B ⊆ range N := fun n hn => (hU n hn).1
  have hsub : (↑B : Set ℕ) ⊆ A ∩ Set.Ici M := by
    intro n hn
    refine ⟨(hU n hn).2, ?_⟩
    have h := (hb n hn).2
    simpa [not_or] using (show n ∉ range M from fun hh => h (mem_union_right _ hh))
  have hsize : ε * N ≤ B.card := by
    have h₁ := le_card_sdiff (E ∪ range M) U
    have h₂ := card_union_le E (range M)
    simp only [card_range] at h₂
    have h₃ : U.card ≤ B.card + E.card + M := by dsimp [B]; omega
    have h₄ : (U.card : ℝ) ≤ B.card + E.card + M := by exact_mod_cast h₃
    linarith
  have hmass : 4 / (y : ℝ) ≤ ∑ n ∈ B, (1 : ℝ)/n := by
    calc
      4 / (y : ℝ) ≤ (B.card : ℝ)/N :=
        hyε.le.trans ((le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr hsize)
      _ = ∑ _n ∈ B, (1 : ℝ)/N := by simp [div_eq_mul_inv]
      _ ≤ _ := sum_le_sum fun n hn => by
        have hp : 0 < n := Nat.pos_of_ne_zero fun hz => hzero (hz ▸ (hU n hn).2)
        exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hp)
          (Nat.cast_le.mpr (mem_range.mp (hBN hn)).le)
  obtain ⟨d,hd,S,hSB,hS⟩ := hrec B (fun h => hzero (hU 0 h).2) hBN
    (fun n hn => hgood n (mem_range.mp (hBN hn))
      (fun h => (hb n hn).2 (mem_union_left _ h))) hmass
  refine ⟨d,hd,S,fun _ hn => hsub (hSB hn), ?_⟩
  exact hS

end OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1

end

section
/-!
Adapted from Bhavik Mehta and Thomas Bloom, b-mehta/unit-fractions,
commit 10ef71a300cf29e5f19beb2bbc723a035a0678de, src/defs.lean,
src/main_results.lean and src/fourier.lean.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Copyright (c) 2022 Bhavik Mehta, Thomas Bloom. All rights reserved.
Used under Apache-2.0.

The pruning lemma fixes a target divisor and tunes the reciprocal mass to
just below twice its reciprocal. If the first pruned set fails the interval
condition for the circle method, it has a subset with low prime-power mass.
The separated second divisor makes one more pruning possible, after which
the low-mass forcing lemma gives the interval condition.
-/
namespace OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1
open Filter Finset Real
open scoped Classical Topology
/-- The mass-pruning lemma with a fixed upper bound on the target divisor. -/
def H1 : Prop := 
  let M (N : ℕ) := (N:ℝ)^(1-1/log (log N))
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  let localPart (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/log (log N))) ∧
    (99/100:ℝ)*log (log N) ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*log (log N)
  let Balanced (N d : ℕ) (A : Finset ℕ) : Prop :=
    mass A < 2/(d:ℝ) ∧ 2/(d:ℝ)-1/M N ≤ mass A ∧ d ∣ A.lcm id ∧
    ∀ q ∈ powers A, (log N)^(-(1/100:ℝ)) ≤ ∑ n ∈ localPart A q, (q:ℝ)/n
  ∀ z : ℕ, ∀ᶠ N : ℕ in atTop,
  ∀ (A : Finset ℕ) (u v : ℕ), 1≤u → u≤v → 2≤v → v≤z → 0∉A → A ⊆ range N →
  (∀ n ∈ A, Regular N n) → 2/(u:ℝ) + 1/(10*(z:ℝ)) ≤ mass A →
  (∀ n ∈ A, ∃ d ∈ Icc u v, d∣n) →
  ∃ B ⊆ A, ∃ d ∈ Icc u v, Balanced N d B ∧ ∀ n ∈ B, ∀ j : ℕ, j∣n → u≤j → d≤j

/-- First forcing alternative, specialised to a balanced set. -/
def H2 : Prop := 
  let M (N : ℕ) := (N:ℝ)^(1-1/log (log N))
  let K (N : ℕ) := M N * (N:ℝ)^(-2/log (log N))
  let T (N : ℕ) := M N / log N
  let L (N : ℕ) := M N / (2*(log N)^(1/100:ℝ))
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  let localPart (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let primeMass (A : Finset ℕ) := mass (powers A)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/log (log N))) ∧
    (99/100:ℝ)*log (log N) ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*log (log N)
  let Balanced (N d : ℕ) (A : Finset ℕ) : Prop :=
    mass A < 2/(d:ℝ) ∧ 2/(d:ℝ)-1/M N ≤ mass A ∧ d ∣ A.lcm id ∧
    ∀ q ∈ powers A, (log N)^(-(1/100:ℝ)) ≤ ∑ n ∈ localPart A q, (q:ℝ)/n
  let Good (N : ℕ) (A : Finset ℕ) : Prop :=
    ∀ t : ℝ, let I := Icc (⌈t-K N/2⌉:ℤ) ⌊t+K N/2⌋
      T N ≤ ((A.filter fun (n : ℕ) => ∀ x ∈ I, ¬(n:ℤ) ∣ x).card:ℝ) ∨
      ∃ x ∈ I, ∀ q ∈ powers A,
        (((localPart A q).filter fun (n : ℕ) => ∀ v ∈ I, ¬(n:ℤ) ∣ v).card:ℝ) < L N/q → (q:ℤ) ∣ x
  ∀ z : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (d : ℕ),
  0<d → d≤z → 0∉A → A ⊆ range N → (∀ n ∈ A, Regular N n) → Balanced N d A →
  Good N A ∨ ∃ B ⊆ A, mass A ≤ 3*mass B ∧ primeMass B ≤ (2/3:ℝ)*log (log N)

/-- Low prime-power reciprocal mass forces the interval condition. -/
def H3 : Prop := 
  let M (N : ℕ) := (N:ℝ)^(1-1/log (log N))
  let K (N : ℕ) := M N * (N:ℝ)^(-2/log (log N))
  let T (N : ℕ) := M N / log N
  let L (N : ℕ) := M N / (2*(log N)^(1/100:ℝ))
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  let localPart (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let primeMass (A : Finset ℕ) := mass (powers A)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/log (log N))) ∧
    (99/100:ℝ)*log (log N) ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*log (log N)
  let Balanced (N d : ℕ) (A : Finset ℕ) : Prop :=
    mass A < 2/(d:ℝ) ∧ 2/(d:ℝ)-1/M N ≤ mass A ∧ d ∣ A.lcm id ∧
    ∀ q ∈ powers A, (log N)^(-(1/100:ℝ)) ≤ ∑ n ∈ localPart A q, (q:ℝ)/n
  let Good (N : ℕ) (A : Finset ℕ) : Prop :=
    ∀ t : ℝ, let I := Icc (⌈t-K N/2⌉:ℤ) ⌊t+K N/2⌋
      T N ≤ ((A.filter fun (n : ℕ) => ∀ x ∈ I, ¬(n:ℤ) ∣ x).card:ℝ) ∨
      ∃ x ∈ I, ∀ q ∈ powers A,
        (((localPart A q).filter fun (n : ℕ) => ∀ v ∈ I, ¬(n:ℤ) ∣ v).card:ℝ) < L N/q → (q:ℤ) ∣ x
  ∀ z : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (d : ℕ),
  0<d → d≤z → 0∉A → A ⊆ range N → (∀ n ∈ A, Regular N n) → Balanced N d A →
  primeMass A ≤ (2/3:ℝ)*log (log N) → Good N A

/-- The circle-method extraction from a balanced set with good short intervals. -/
def H4 : Prop := 
  let M (N : ℕ) := (N:ℝ)^(1-1/log (log N))
  let K (N : ℕ) := M N * (N:ℝ)^(-2/log (log N))
  let T (N : ℕ) := M N / log N
  let L (N : ℕ) := M N / (2*(log N)^(1/100:ℝ))
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  let localPart (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/log (log N))) ∧
    (99/100:ℝ)*log (log N) ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*log (log N)
  let Balanced (N d : ℕ) (A : Finset ℕ) : Prop :=
    mass A < 2/(d:ℝ) ∧ 2/(d:ℝ)-1/M N ≤ mass A ∧ d ∣ A.lcm id ∧
    ∀ q ∈ powers A, (log N)^(-(1/100:ℝ)) ≤ ∑ n ∈ localPart A q, (q:ℝ)/n
  let Good (N : ℕ) (A : Finset ℕ) : Prop :=
    ∀ t : ℝ, let I := Icc (⌈t-K N/2⌉:ℤ) ⌊t+K N/2⌋
      T N ≤ ((A.filter fun (n : ℕ) => ∀ x ∈ I, ¬(n:ℤ) ∣ x).card:ℝ) ∨
      ∃ x ∈ I, ∀ q ∈ powers A,
        (((localPart A q).filter fun (n : ℕ) => ∀ v ∈ I, ¬(n:ℤ) ∣ v).card:ℝ) < L N/q → (q:ℤ) ∣ x
  ∀ z : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (d : ℕ),
  0<d → d≤z → 0∉A → A ⊆ range N → (∀ n ∈ A, Regular N n) → Balanced N d A → Good N A →
  ∃ S ⊆ A, ∑ n ∈ S, (1:ℚ)/n = 1/d

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1.H2 := by
  intro prune force₁ force₂ circle y z hy hyz
  let M (N : ℕ) := (N:ℝ)^(1-1/log (log N))
  let K (N : ℕ) := M N * (N:ℝ)^(-2/log (log N))
  let T (N : ℕ) := M N / log N
  let L (N : ℕ) := M N / (2*(log N)^(1/100:ℝ))
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  let localPart (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let primeMass (A : Finset ℕ) := mass (powers A)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/log (log N))) ∧
    (99/100:ℝ)*log (log N) ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*log (log N)
  let Balanced (N d : ℕ) (A : Finset ℕ) : Prop :=
    mass A < 2/(d:ℝ) ∧ 2/(d:ℝ)-1/M N ≤ mass A ∧ d ∣ A.lcm id ∧
    ∀ q ∈ powers A, (log N)^(-(1/100:ℝ)) ≤ ∑ n ∈ localPart A q, (q:ℝ)/n
  let Good (N : ℕ) (A : Finset ℕ) : Prop :=
    ∀ t : ℝ, let I := Icc (⌈t-K N/2⌉:ℤ) ⌊t+K N/2⌋
      T N ≤ ((A.filter fun (n : ℕ) => ∀ x ∈ I, ¬(n:ℤ) ∣ x).card:ℝ) ∨
      ∃ x ∈ I, ∀ q ∈ powers A,
        (((localPart A q).filter fun (n : ℕ) => ∀ v ∈ I, ¬(n:ℤ) ∣ v).card:ℝ) < L N/q → (q:ℤ) ∣ x
  have primeMass_mono {A B : Finset ℕ} (h : A⊆B) : primeMass A ≤ primeMass B := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
    intro q hq
    obtain ⟨n,hn,hh⟩ := mem_biUnion.mp hq
    exact mem_biUnion.mpr ⟨n,h hn,hh⟩

  have Mtop : Tendsto M atTop atTop := by
    have h := (tendsto_rpow_atTop (by norm_num : 0<(1/2:ℝ))).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    apply tendsto_atTop_mono' _ _ h
    filter_upwards [(tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))).eventually_ge_atTop 2,
      eventually_ge_atTop 1] with N hw hn
    apply rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    change 2 ≤ log (log N) at hw
    linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hw]
  filter_upwards [prune z,force₁ z,force₂ z,circle z,Mtop.eventually_ge_atTop (10*z)] with N hp hf hg hc hM
  intro B hzero hsub hdata hmass
  have yr := Nat.cast_pos (α:=ℝ).mpr hy
  have hz : 0<z := by omega
  have zr := Nat.cast_pos (α:=ℝ).mpr hz
  have reg (n) (hn : n∈B) : Regular N n :=
    ⟨(hdata n hn).1,(hdata n hn).2.1,(hdata n hn).2.2.1,(hdata n hn).2.2.2.1⟩
  have divis (n) (hn : n∈B) := (hdata n hn).2.2.2.2
  have firstdiv (n) (hn : n∈B) : ∃ d ∈ Icc y (z/4), d∣n := by
    obtain ⟨u,v,hu,hv,huy,huv,hvz⟩ := divis n hn
    exact ⟨u,mem_Icc.mpr ⟨huy,by omega⟩,hu⟩
  have small : 1/(10*(z:ℝ)) ≤ 1/(y:ℝ) := one_div_le_one_div_of_le yr (by exact_mod_cast (show y≤10*z by omega))
  obtain ⟨A,hAB,d,hd,bal,least⟩ := hp B y (z/4) hy (by omega) (by omega) (by omega) hzero hsub reg (by
    change 2/(y:ℝ)+1/(10*(z:ℝ)) ≤ mass B
    change 4/(y:ℝ) ≤ mass B at hmass
    have invpos : 0 ≤ (y:ℝ)⁻¹ := by positivity
    simp only [div_eq_mul_inv,one_mul] at small hmass ⊢
    linarith only [small,hmass,invpos]) firstdiv
  obtain ⟨hyd,hdz₄⟩ := mem_Icc.mp hd
  have hd0 := hy.trans_le hyd
  have hdz : d ≤ z := by omega
  have subzero {F : Finset ℕ} (hF : F⊆B) : 0∉F := fun hx => hzero (hF hx)
  have subreg {F : Finset ℕ} (hF : F⊆B) : ∀ n ∈ F, Regular N n := fun n hn => reg n (hF hn)
  have finish (F : Finset ℕ) (hF : F⊆B) (j : ℕ) (hyj : y≤j) (hjz : j≤z)
      (tuned : Balanced N j F) (good : Good N F) :
      ∃ d ∈ Icc y z, ∃ S ⊆ B, ∑ n ∈ S, (1:ℚ)/n = 1/d := by
    obtain ⟨S,hS,hr⟩ := hc F j (hy.trans_le hyj) hjz (subzero hF) (hF.trans hsub) (subreg hF) tuned good
    exact ⟨j,mem_Icc.mpr ⟨hyj,hjz⟩,S,hS.trans hF,hr⟩
  rcases hf A d hd0 hdz (subzero hAB) (hAB.trans hsub) (subreg hAB) bal with good | ⟨D,hDA,hweight,hprime⟩
  · exact finish A hAB d hyd hdz bal good
  change Balanced N d A at bal
  change mass A ≤ 3*mass D at hweight
  have hDB := hDA.trans hAB
  have nextdiv (n) (hn : n∈D) : ∃ e ∈ Icc (4*d) z, e∣n := by
    obtain ⟨u,v,hu,hv,huy,huv,hvz⟩ := divis n (hDB hn)
    have hdu := least n (hDA hn) u hu huy
    exact ⟨v,mem_Icc.mpr ⟨by omega,hvz⟩,hv⟩
  have dt : 0<(d:ℝ) := Nat.cast_pos.mpr hd0
  have hz10 : 0 < 10*(z:ℝ) := by positivity
  have einv := one_div_le_one_div_of_le hz10 hM
  have dzinv : 1/(z:ℝ) ≤ 1/(d:ℝ) := one_div_le_one_div_of_le dt (Nat.cast_le.mpr hdz)
  have enough : 2/(4*d:ℕ)+1/(10*(z:ℝ)) ≤ mass D := by
    push_cast
    have low : 2/(d:ℝ)-1/M N ≤ mass A := bal.2.1
    have e1 : (1:ℝ)/(10*z) = (1/10)*(1/z) := by ring
    have e2 : (2:ℝ)/(4*d) = (1/2)*(1/d) := by ring
    rw [e1] at einv ⊢
    rw [e2]
    have invpos : 0 ≤ (d:ℝ)⁻¹ := by positivity
    simp only [div_eq_mul_inv,one_mul] at einv dzinv low ⊢
    norm_num at einv ⊢
    linarith only [einv,dzinv,hweight,low,invpos]
  obtain ⟨F,hFD,j,hj,bal',_⟩ := hp D (4*d) z (by omega) (by omega) (by omega) le_rfl
    (subzero hDB) (hDB.trans hsub) (subreg hDB) enough nextdiv
  have hFB := hFD.trans hDB
  have jprop := mem_Icc.mp hj
  exact finish F hFB j (by omega) jprop.2 bal'
    (hg F j (by omega) jprop.2 (subzero hFB) (hFB.trans hsub) (subreg hFB) bal' ((primeMass_mono hFD).trans hprime))
end OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1

end

section
/-!
This adapts the common-divisor and cofactor argument for Lemma 5.4 in the
Bloom formalization by Bhavik Mehta and Thomas Bloom, with Eric Rodriguez
on src/aux_lemmas.lean, b-mehta/unit-fractions at commit
10ef71a300cf29e5f19beb2bbc723a035a0678de, src/aux_lemmas.lean and
src/main_results.lean. Copyright (c) 2021 Bhavik Mehta, Thomas Bloom.
All rights reserved. Used under Apache-2.0.

The bound on the number of distinct prime factors is adapted from Will Howe,
H0W4RD-dev/croot-unit-fractions at c58a7d45114c3af27e6abb19dcfca9d82b49b4a1,
Prop1.lean, under Apache-2.0. The Mertens bounds are from the merged Erdős
377 argument by @marcusbuffett, with the first estimate by @senamakel.

The common prime-power mass at two distinct interval points is negligible:
their difference is at most N, its large prime factors are few, and Mertens
bounds the small ones. A cofactor family supplies a heavy point for each
rare prime power. Its common divisor exceeds the interval width, hence
every denominator from the family hits the same point. The total prime-power
mass bound forces these heavy points to coincide.
-/
open Filter Finset Real Asymptotics
open scoped Classical Topology
namespace OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
/-- Extract a common divisor larger than the interval from a local family.
The coprime cofactors carry enough reciprocal mass and retain most prime factors. -/
def H1 : Prop := 
  let w (N : ℕ) := log (log N)
  let e (N : ℕ) := (log N)^(-(1/100:ℝ))
  let M (N : ℕ) := (N:ℝ)^(1-1/w N)
  let K (N : ℕ) := M N*(N:ℝ)^(-2/w N)
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧
    (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N
  ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (q : ℕ), 0∉A → A⊆range N →
  (∀ n ∈ A, Regular N n) → IsPrimePow q → e N/2 ≤ ∑ n ∈ part A q,(q:ℝ)/n →
  ∃ (D : ℕ) (C : Finset ℕ), K N < D ∧ q∣D ∧
    (log N)^(-(1/99:ℝ)) ≤ mass C ∧
    (∀ m ∈ C, D*m ∈ A ∧ Nat.Coprime m D ∧
      (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N)

/-- A family of cofactors of sufficient mass and with almost the normal
number of distinct prime factors has large prime-power reciprocal mass. -/
def H2 : Prop := 
  let w (N : ℕ) := log (log N)
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,
  (log N)^(-(1/99:ℝ)) ≤ mass C →
  (∀ m ∈ C, (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N) →
  (35/100:ℝ)*w N ≤ mass (powers C)

lemma common_prime_powers : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m≤N → ∀ P : Finset ℕ,
    (∀ q ∈ P, IsPrimePow q ∧ q∣m) → (∑ q ∈ P,(1:ℝ)/q) < (1/30:ℝ)*log (log N) := by
  classical
  have log_factorial_eq_sum (N : ℕ) :
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

  have div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
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

  have real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
      (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := N) hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
    rw [div_sub_one hp'.ne', div_le_iff₀ hp']
    linarith

  have log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
    exact_mod_cast Nat.factorial_le_pow N

  have log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
    linarith


  have summable_log_div_mul_sub_one :
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


  have sum_log_div_le_nat (N : ℕ) :
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


  let primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

  have sum_log_div_mul_sub_one_le (s : Finset ℕ) :
      ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
    apply summable_log_div_mul_sub_one.sum_le_tsum s
    intro n _
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith


  have sum_log_div_ge_nat (N : ℕ) :
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


  have primePowerConst_nonneg : 0 ≤ primePowerConst := by
    have := sum_log_div_mul_sub_one_le ∅
    simpa using this


  let mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

  have abs_sum_log_div_sub_log_le_nat (N : ℕ) :
      |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
    have h1 := sum_log_div_le_nat N
    have h2 := sum_log_div_ge_nat N
    have h3 := primePowerConst_nonneg
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [abs_le]; unfold mertens1Const; constructor <;> linarith

  have log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
      Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
    have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
    have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
    have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    constructor
    · exact Real.log_le_log (by linarith) hle
    · rw [← Real.log_mul (by linarith) (by norm_num)]
      apply Real.log_le_log (by linarith)
      linarith


  have abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
    have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
    obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
    have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]


  have mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
    ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

  have sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
      ∑ p ∈ Nat.primesLE (N + 1), f p =
        (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
    rw [Nat.primesLE_succ]
    split_ifs with h
    · rw [Finset.sum_insert, add_comm]
      intro hm
      have := (Nat.mem_primesLE.mp hm).1
      omega
    · simp

  have recip_step (N : ℕ) :
      (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
        ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
          Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [sum_succ_eq, sum_succ_eq]
    split_ifs with h
    · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast h.one_lt)
      field_simp
      ring
    · simp



  have abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
      |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
    have hb : 0 < b := by linarith
    have hq : 0 < b / a := div_pos hb ha
    have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
    have hup := Real.log_le_sub_one_of_pos hq
    have hlo := Real.one_sub_inv_le_log_of_pos hq
    rw [inv_div] at hlo
    rw [hlog]
    have e1 : (b - a) / b = 1 - a / b := by field_simp
    have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
    have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
    have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
    have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
      have : b - a ≤ 1 := by linarith
      nlinarith
    rw [abs_le, e2, e1]
    constructor <;> nlinarith


  let mertensG (N : ℕ) : ℝ :=
    (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
      ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

  have mertensG_step (N : ℕ) (hN : 2 ≤ N) :
      |mertensG (N + 1) - mertensG N| ≤
        (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
    set a := Real.log N with ha_def
    set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have ha : 0 < a := Real.log_pos (by linarith)
    have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
    have hb : 0 < b := by linarith
    have hb1 : b ≤ a + 1 := by
      have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
        (Real.log_div (by positivity) (by positivity)).symm
      have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
      have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
        push_cast
        rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
        linarith
      linarith
    set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
    set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
    set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
    set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
    have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
    have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
    have hdiff : mertensG (N + 1) - mertensG N =
        (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
      have e : mertensG (N + 1) - mertensG N =
          (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
        simp only [mertensG]
        ring
      rw [e, hstep]
      field_simp
      ring
    have hE := abs_log_sub_log_sub_le ha hab hb1
    have hpos : 0 ≤ 1 / a - 1 / b := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
    rw [hdiff]
    calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
        ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
      _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
        rw [abs_mul, abs_of_nonneg hpos]
        gcongr
      _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring


  let S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
  have Cpos : 0 ≤ mertens1Const := by
    exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
  have Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
      |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      calc |mertensG (n+1)-mertensG m| =
          |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
        _ = _ := by ring
  have logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
      log (log n)) atTop (𝓝 b) := by
    have hC : CauchySeq mertensG := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop logTop
      obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
      refine ⟨m,fun n hn => ?_⟩
      rw [Real.dist_eq]
      apply (Gdiff m n hm hn).trans_lt
      have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
      have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
      rw [mul_sub,←div_eq_mul_one_div]
      linarith
    obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
    let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
    have hR : Tendsto R atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
        (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
      filter_upwards [logTop.eventually_gt_atTop 0] with n hn
      dsimp only [R]
      rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
      exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
    refine ⟨b,?_⟩
    simpa [R,mertensG] using hb.add hR
  have realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
    obtain ⟨b,hb⟩ := natMertens
    have he := (isEquivalent_nat_floor (R:=ℝ)).log tendsto_id
    have hz := tendsto_log_atTop.eventually_ne_atTop 0
    have ht := ((isEquivalent_iff_tendsto_one hz).1 he).log (by norm_num)
    have hfloor : Tendsto (fun x : ℝ => log (⌊x⌋₊:ℝ)) atTop atTop := logTop.comp tendsto_nat_floor_atTop
    have hdiff : Tendsto (fun x : ℝ => log (log (⌊x⌋₊:ℝ)) - log (log x)) atTop (𝓝 0) := by
      rw [Real.log_one] at ht
      apply ht.congr'
      filter_upwards [hz,hfloor.eventually_ne_atTop 0] with x hx hf
      exact log_div hf hx
    refine ⟨b,?_⟩
    have h := (hb.comp tendsto_nat_floor_atTop).add hdiff
    simpa [S,Function.comp_def,sub_add_sub_cancel] using h
  let w (N : ℕ) := log (log N)
  have wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp logTop
  have geom (p : ℕ) (hp : 2≤p) (N : ℕ) :
      (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1)) ≤ 2/(p:ℝ) := by
    have h : (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(N+1) ≤ 2/(p:ℝ) := by
      induction N with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ]
        have hpos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
        have htwo : (2:ℝ)≤p := by exact_mod_cast hp
        have hh : 2/(p:ℝ)^(n+1+1) ≤ 1/(p:ℝ)^(n+1) := by
          rw [pow_succ _ (n+1),div_mul_eq_div_div]
          apply (div_le_iff₀ hpos).mpr
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
        calc _ ≤ ((∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+1/(p:ℝ)^(n+1))+1/(p:ℝ)^(n+1) := add_le_add le_rfl hh
             _ = (∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(n+1) := by ring
             _ ≤ _ := ih
    linarith [show 0≤2/(p:ℝ)^(N+1) by positivity]
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  have pp_bound (m : ℕ) (hm : 0 < m) (P : Finset ℕ) (hP : ∀ q ∈ P, IsPrimePow q ∧ q∣m) :
      mass P ≤ 2*mass m.primeFactors := by
    let U := m.primeFactors ×ˢ range m
    let f (p : ℕ×ℕ) := p.1^(p.2+1)
    have sub : P⊆U.image f := by
      intro q hq
      obtain ⟨pp,dvd⟩ := hP q hq
      obtain ⟨p,hp,k,hk,pr,hk0,eq⟩ := (isPrimePow_nat_iff_bounded q).mp pp
      have pd := (dvd_pow_self p hk0.ne').trans (eq ▸ dvd : p^k ∣ m)
      have le := Nat.le_of_dvd hm dvd
      cases k with
      | zero => omega
      | succ j => exact mem_image.mpr ⟨(p,j),mem_product.mpr ⟨Nat.mem_primeFactors.mpr ⟨pr,pd,hm.ne'⟩,
                      mem_range.mpr (by omega)⟩,eq⟩
    calc _ ≤ ∑ q ∈ U.image f, (1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
         _ ≤ ∑ a ∈ U, (1:ℝ)/(f a) := sum_image_le_of_nonneg (fun _ _ => by positivity)
         _ = ∑ p ∈ m.primeFactors, ∑ k ∈ range m, (1:ℝ)/(p:ℝ)^(k+1) := by simp [U,f,sum_product]
         _ ≤ ∑ p ∈ m.primeFactors, 2/(p:ℝ) := sum_le_sum fun p hp =>
            geom p (Nat.prime_of_mem_primeFactors hp).two_le m
         _ = _ := by simp only [mass,mul_sum]; congr 1; ext; ring
  have card_le_log {s : ℕ} (hs : 0 < s) :
      (s.primeFactors.card : ℝ) ≤ log s / log 2 := by
    have h1 : 2 ^ s.primeFactors.card ≤ ∏ p ∈ s.primeFactors, p :=
      pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have h2 := Nat.le_of_dvd hs (Nat.prod_primeFactors_dvd s)
    have h3 : ((2 : ℝ) ^ s.primeFactors.card) ≤ s := by exact_mod_cast h1.trans h2
    rw [le_div_iff₀ (log_pos one_lt_two)]
    have := log_le_log (by positivity) h3
    rwa [log_pow] at this
  have overlap : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m≤N → ∀ P : Finset ℕ,
      (∀ q ∈ P, IsPrimePow q ∧ q∣m) → mass P < (1/30:ℝ)*w N := by
    obtain ⟨b,hb⟩ := realMertens
    have hg := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp wtop
    filter_upwards [(hb.comp logTop).eventually_lt_const (show b<b+1 by linarith),
      hg.eventually_lt_const (by norm_num : (0:ℝ)<1/200),
      wtop.eventually_gt_atTop (200*(|b|+1+1/log 2)),
      logTop.eventually_gt_atTop 1] with N hprime hratio hw hN
    intro m hm hmN P hP
    let X := log (N:ℝ)
    let Q := m.primeFactors.filter fun p : ℕ => (p:ℝ)≤X
    let R := m.primeFactors \ Q
    have xp : 0<X := by dsimp [X]; linarith
    have p2 : 0<log 2 := log_pos one_lt_two
    have wpos : 0<w N := by linarith [abs_nonneg b,one_div_pos.mpr p2]
    change S X - log (w N) < b+1 at hprime
    simp only [Function.comp_apply,pow_one,one_mul,add_zero] at hratio
    have small := (div_lt_iff₀ wpos).mp hratio
    have sub : Q ⊆ Nat.primesLE ⌊X⌋₊ := by
      intro p hp
      obtain ⟨hp,le⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor le,Nat.prime_of_mem_primeFactors hp⟩
    have lo : mass Q ≤ S X := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
    have hi : mass R ≤ 1/log 2 := by
      have hh : mass R ≤ (R.card:ℝ)*(1/X) := by
        simpa [mass,nsmul_eq_mul] using sum_le_card_nsmul R (fun p : ℕ => (1:ℝ)/p) (1/X) (by
          intro p hp
          obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
          exact one_div_le_one_div_of_le xp (le_of_not_ge (fun le => h2 (mem_filter.mpr ⟨h1,le⟩))))
      have size : (R.card:ℝ)≤ m.primeFactors.card := by exact_mod_cast card_le_card (sdiff_subset : R⊆m.primeFactors)
      have logle : log (m:ℝ) ≤ X := log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN)
      have cm := size.trans ((card_le_log hm).trans (div_le_div_of_nonneg_right logle p2.le))
      calc mass R ≤ (R.card:ℝ)*(1/X) := hh
           _ ≤ (X/log 2)*(1/X) := mul_le_mul_of_nonneg_right cm (by positivity)
           _ = _ := by field_simp
    have eq := sum_sdiff (filter_subset (fun p : ℕ => (p:ℝ)≤X) m.primeFactors) (f:=fun p : ℕ => (1:ℝ)/p)
    change mass R + mass Q = mass m.primeFactors at eq
    have pp := pp_bound m hm P hP
    linarith [le_abs_self b]
  exact overlap

theorem main : H1 → H2 → OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H3 := by
  classical
  intro cof entropy
  let w (N : ℕ) := log (log N)
  let e (N : ℕ) := (log N)^(-(1/100:ℝ))
  let M (N : ℕ) := (N:ℝ)^(1-1/w N)
  let K (N : ℕ) := M N*(N:ℝ)^(-2/w N)
  let L (N : ℕ) := M N/(2*(log N)^(1/100:ℝ))
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  let part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧
    (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N
  have power_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
      IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ q∣n ∧ Nat.Coprime q (n/q) := by
    obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
    obtain ⟨dv,pp,cp⟩ := mem_filter.mp hq
    obtain ⟨hd,h0⟩ := Nat.mem_divisors.mp dv
    exact ⟨pp,n,hn,h0,hd,cp⟩
  intro z
  filter_upwards [cof,entropy,common_prime_powers,
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))).eventually_ge_atTop 4,
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop 0,
    eventually_ge_atTop 1] with N co en ov hw hlog hN
  change 0 < log (N:ℝ) at hlog
  intro A d hd hdz a0 aN reg bal total t
  let I := Icc (⌈t-K N/2⌉:ℤ) ⌊t+K N/2⌋
  let hit (n : ℕ) := ∃ x ∈ I, (n:ℤ)∣x
  let U := A.filter hit
  let rare (q : ℕ) := ((((part A q).filter fun n => ¬hit n).card):ℝ)<L N/q
  let Q := powers A
  let F (x : ℤ) := Q.filter fun r : ℕ => (r:ℤ)∣x
  have mpos : 0<M N := rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
  have ep : 0<e N := rpow_pos_of_pos hlog _
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith
  change 4≤w N at hw
  have keq : K N = (N:ℝ)^(1-3/w N) := by dsimp only [K,M]; rw [←rpow_add hnp]; congr 1; ring
  have k1 : 1≤K N := by rw [keq]; apply one_le_rpow hn; have := (div_le_one (by linarith : 0<w N)).mpr (by linarith : 3≤w N); linarith
  have kN : K N≤N := by
    rw [keq]; conv_rhs => rw [← rpow_one (N:ℝ)]
    apply rpow_le_rpow_of_exponent_le hn
    have : 0≤3/w N := div_nonneg (by norm_num) (by linarith); linarith
  have ine : I.Nonempty := by
    refine ⟨⌈t-K N/2⌉,mem_Icc.mpr ⟨le_rfl,Int.le_floor.mpr ?_⟩⟩
    have := Int.ceil_lt_add_one (t-K N/2)
    linarith
  have dist (x y : ℤ) (hx : x∈I) (hy : y∈I) : |(x:ℝ)-y| ≤ K N := by
    have bound (a : ℤ) (ha : a∈I) : t-K N/2 ≤ a ∧ (a:ℝ) ≤ t+K N/2 :=
      ⟨Int.ceil_le.mp (mem_Icc.mp ha).1,Int.le_floor.mp (mem_Icc.mp ha).2⟩
    obtain ⟨xl,xu⟩ := bound x hx
    obtain ⟨yl,yu⟩ := bound y hy
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have balanced : ∀ q ∈ Q, e N ≤ ∑ n ∈ part A q,(q:ℝ)/n := bal.2.2.2
  have heavy (q : ℕ) (hq : q∈Q) (hr : rare q) : ∃ x∈I, (q:ℤ)∣x ∧ (35/100:ℝ)*w N ≤ mass (F x) := by
    obtain ⟨pp,b,hb,hb0,hqb,hbc⟩ := power_mem hq
    have qp : (0:ℝ)<q := by exact_mod_cast pp.pos
    let B := (part A q).filter fun n => ¬hit n
    have small : (∑ n ∈ B,(q:ℝ)/n) ≤ e N/2 := by
      have rem := sum_le_card_nsmul B (fun n : ℕ => (q:ℝ)/n) ((q:ℝ)/M N) (by
        intro n hn
        exact div_le_div_of_nonneg_left qp.le mpos (reg n (mem_filter.mp (mem_filter.mp hn).1).1).1)
      rw [nsmul_eq_mul] at rem
      change (B.card:ℝ)<L N/q at hr
      calc _ ≤ (B.card:ℝ)*((q:ℝ)/M N) := rem
           _ ≤ (L N/q)*((q:ℝ)/M N) := mul_le_mul_of_nonneg_right hr.le (by positivity)
           _ = _ := by
             dsimp only [L,e]
             rw [Real.rpow_neg (by linarith : 0≤log N)]
             field_simp [mpos.ne',qp.ne', (rpow_pos_of_pos hlog (1/100:ℝ)).ne']
    have split : ((part A q).filter hit) = part U q := by ext n; simp [part,U,and_comm,and_left_comm,and_assoc]
    have splitSum := sum_filter_add_sum_filter_not (s:=part A q) (f:=fun n : ℕ => (q:ℝ)/n) hit
    rw [split] at splitSum
    change (∑ n ∈ part U q, (q:ℝ)/n)+(∑ n ∈ B,(q:ℝ)/n)=_ at splitSum
    have bulk : e N/2 ≤ ∑ n ∈ part U q,(q:ℝ)/n := by linarith [balanced q hq]
    have ua : U⊆A := filter_subset _ _
    obtain ⟨D,C,big,qd,cm,cf⟩ := co U q (fun h => a0 (ua h)) (ua.trans aN)
      (fun n hn => reg n (ua hn)) pp bulk
    have cd := en C cm (fun m hm => (cf m hm).2.2)
    obtain ⟨m,hm⟩ := nonempty_of_ne_empty (s:=C) (fun eq => by
      have p := rpow_pos_of_pos hlog (-(1/99:ℝ))
      rw [eq] at cm
      exact p.not_ge (by simpa only [mass,sum_empty] using cm))
    obtain ⟨x,hx,dx⟩ := (mem_filter.mp (cf m hm).1).2
    have Dvd (m : ℕ) {y : ℤ} (hy : ((D*m:ℕ):ℤ)∣y) : (D:ℤ)∣y :=
      (show (D:ℤ) ∣ ((D*m:ℕ):ℤ) by exact_mod_cast (dvd_mul_right D m)).trans hy
    have uniq (y : ℤ) (hy : y∈I) (dy : (D:ℤ)∣y) : x=y := by
      have h : |x-y|<(D:ℤ) := by exact_mod_cast (dist x y hx hy).trans_lt big
      exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (dvd_sub (Dvd m dx) dy) h)
    have inc : powers C ⊆ F x := by
      intro r hr
      obtain ⟨pr,j,hj,j0,rj,cp⟩ := power_mem hr
      obtain ⟨inU,cop,_⟩ := cf j hj
      obtain ⟨inA,y,hy,divy⟩ := mem_filter.mp inU
      have rDj := rj.trans (dvd_mul_left j D)
      have prA : r ∈ Q := by
        apply mem_biUnion.mpr
        refine ⟨D*j,inA,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨rDj,fun eq => a0 (eq ▸ inA)⟩,pr,?_⟩⟩
        rw [Nat.mul_div_assoc D rj]
        exact (cop.coprime_dvd_left rj).mul_right cp
      refine mem_filter.mpr ⟨prA,?_⟩
      rw [uniq y hy (Dvd j divy)]
      exact (show (r:ℤ) ∣ ((D*j:ℕ):ℤ) by exact_mod_cast rDj).trans divy
    exact ⟨x,hx,(show (q:ℤ)∣D by exact_mod_cast qd).trans (Dvd m dx),cd.trans
      (sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => by positivity))⟩
  right
  by_cases existsRare : ∃ q∈Q, rare q
  · obtain ⟨q,hq,hr⟩ := existsRare
    obtain ⟨x,hx,qx,hX⟩ := heavy q hq hr
    refine ⟨x,hx,?_⟩
    intro r hr hrr
    have hrare : rare r := by simpa [rare,hit,I,K,M,w,L,part,not_exists] using hrr
    obtain ⟨y,hy,ry,hY⟩ := heavy r hr hrare
    suffices x=y by simpa [this] using ry
    by_contra ne
    let P := F x ∩ F y
    have sub : F x ∪ F y ⊆ Q := union_subset (filter_subset _ _) (filter_subset _ _)
    have upper : mass (F x ∪ F y) ≤ mass Q := sum_le_sum_of_subset_of_nonneg sub fun _ _ _ => by positivity
    have sums : mass (F x ∪ F y)+mass P = mass (F x)+mass (F y) := sum_union_inter
    have rhs : mass Q ≤ (2/3:ℝ)*w N := total
    have nz : 0<(x-y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr ne)
    have le : (x-y).natAbs ≤ N := by
      have h := (dist x y hx hy).trans kN
      exact_mod_cast (show ((x-y).natAbs:ℝ)≤N by simpa using h)
    have low := ov (x-y).natAbs nz le P (by
      intro s hs
      obtain ⟨a,b⟩ := mem_inter.mp hs
      have d := dvd_sub (mem_filter.mp a).2 (mem_filter.mp b).2
      exact ⟨(power_mem (mem_filter.mp a).1).1,by simpa using (Int.natAbs_dvd_natAbs.mpr d)⟩)
    change mass P<(1/30:ℝ)*w N at low
    change mass (F x ∪ F y)+mass P = mass (F x)+mass (F y) at sums
    linarith
  · obtain ⟨x,hx⟩ := ine
    refine ⟨x,hx,?_⟩
    intro r hr hrr
    exact False.elim (existsRare ⟨r,hr,by simpa [rare,hit,I,K,M,w,L,part,not_exists] using hrr⟩)
end OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1

end

section

/-!
The first and second Mertens estimates are adapted from the merged Erdős 377 proof
by @marcusbuffett, which credits @senamakel for the elementary first Mertens
estimate and the bound for successive errors. The variance proof below counts
positive multiples of one or two primes by integer division. The same estimate
controls both the number of distinct prime factors and gaps between divisors.
Large prime powers of exponent at least two yield large square divisors.
-/

section
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

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring


end OMALib.Mertens
end

section
open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMALib.Mertens
namespace Mass377
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
lemma realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
  obtain ⟨b,hb⟩ := natMertens
  have he := (isEquivalent_nat_floor (R:=ℝ)).log tendsto_id
  have hz := tendsto_log_atTop.eventually_ne_atTop 0
  have ht := ((isEquivalent_iff_tendsto_one hz).1 he).log (by norm_num)
  have hfloor : Tendsto (fun x : ℝ => log (⌊x⌋₊:ℝ)) atTop atTop := logTop.comp tendsto_nat_floor_atTop
  have hdiff : Tendsto (fun x : ℝ => log (log (⌊x⌋₊:ℝ)) - log (log x)) atTop (𝓝 0) := by
    rw [Real.log_one] at ht
    apply ht.congr'
    filter_upwards [hz,hfloor.eventually_ne_atTop 0] with x hx hf
    exact log_div hf hx
  refine ⟨b,?_⟩
  have h := (hb.comp tendsto_nat_floor_atTop).add hdiff
  simpa [S,Function.comp_def,sub_add_sub_cancel] using h
end Mass377
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
noncomputable abbrev mass (P : Finset ℕ) := ∑ p ∈ P, (1:ℝ)/p
def cnt (P : Finset ℕ) (n : ℕ) := (P.filter (· ∣ n)).card
def hit (p n : ℕ) : ℝ := if p ∣ n then 1 else 0
lemma sum_hit (N p : ℕ) : ∑ n ∈ Ioc 0 N, hit p n = (N/p:ℕ) := by
  simp [hit, ← Nat.Ioc_filter_dvd_card_eq_div]
lemma cnt_sum (P : Finset ℕ) (n : ℕ) : (cnt P n : ℝ) = ∑ p ∈ P, hit p n := by
  simp [cnt,hit]
lemma first (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    N*mass P - P.card ≤ ∑ n ∈ Ioc 0 N, (cnt P n:ℝ) := by
  simp_rw [cnt_sum]
  rw [sum_comm]
  simp_rw [sum_hit]
  calc _ = ∑ p ∈ P, ((N:ℝ)/p-1) := by simp [mass,mul_sum,sum_sub_distrib,div_eq_mul_inv]
       _ ≤ _ := sum_le_sum fun p hp => OMALib.Mertens.real_div_sub_one_le_nat_div N p (hP p hp).pos

lemma pair_sum (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ∑ n ∈ Ioc 0 N, hit p n * hit q n ≤
      (N:ℝ)*((1/(p:ℝ))*(1/q)) + (if p=q then (N:ℝ)/p else 0) := by
  by_cases he : p=q
  · subst q
    simp only [if_pos rfl]
    have h : ∀ n, hit p n * hit p n = hit p n := fun n => by unfold hit; split_ifs <;> norm_num
    simp_rw [h,sum_hit]
    exact (Nat.cast_div_le (α:=ℝ)).trans (le_add_of_nonneg_left (by positivity))
  · have hc := (Nat.coprime_primes hp hq).mpr he
    have h (n) : hit p n * hit q n = hit (p*q) n := by
      have eq : p*q ∣ n ↔ p∣n ∧ q∣n := ⟨fun h => ⟨(dvd_mul_right p q).trans h,(dvd_mul_left q p).trans h⟩, fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      simp only [hit,eq]
      split_ifs <;> simp_all
    simp_rw [h,sum_hit,if_neg he,add_zero]
    calc _ ≤ (N:ℝ)/(p*q:ℕ) := Nat.cast_div_le
         _ = _ := by push_cast; ring

lemma second (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ n ∈ Ioc 0 N, (cnt P n:ℝ)^2 ≤ (N:ℝ) * (mass P)^2 + N * mass P := by
  have eq (n) : (cnt P n:ℝ)^2 = ∑ p ∈ P, ∑ q ∈ P, hit p n * hit q n := by
    rw [cnt_sum,pow_two,sum_mul]
    exact sum_congr rfl fun p _ => mul_sum ..
  simp_rw [eq]
  rw [sum_comm]
  simp_rw [sum_comm (s := Ioc 0 N) (t := P)]
  calc _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((N:ℝ)*((1/(p:ℝ))*(1/q)) + (if p=q then (N:ℝ)/p else 0)) :=
            sum_le_sum fun p hp => sum_le_sum fun q hq => pair_sum N p q (hP p hp) (hP q hq)
       _ = _ := by
         simp only [sum_add_distrib, ←mul_sum, ←sum_mul, sum_ite_eq, mass]
         simp only [sum_ite_mem, inter_self]
         simp [mul_sum, sum_mul, pow_two, mul_assoc, div_eq_mul_inv]

lemma variance (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N) :
    ∑ n ∈ Ioc 0 N, ((cnt P n:ℝ)-mass P)^2 ≤ 3*N*mass P := by
  have hm : 0 ≤ mass P := sum_nonneg fun _ _ => by positivity
  have e (n) : ((cnt P n:ℝ)-mass P)^2 =
      (cnt P n:ℝ)^2 - 2*mass P*(cnt P n:ℝ) + (mass P)^2 := by ring
  simp_rw [e]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum]
  simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hcr : (P.card:ℝ) ≤ N := by exact_mod_cast hc
  nlinarith only [first P N hP,second P N hP,
    mul_nonneg hm (sub_nonneg.mpr (first P N hP)), mul_nonneg hm (sub_nonneg.mpr hcr)]

lemma cheb (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    (((Ioc 0 N).filter (fun n => t ≤ |(cnt P n:ℝ)-mass P|)).card:ℝ)*t^2 ≤ 3*N*mass P := by
  classical
  let E := (Ioc 0 N).filter (fun n => t ≤ |(cnt P n:ℝ)-mass P|)
  calc (E.card:ℝ)*t^2 = ∑ _n ∈ E, t^2 := by simp
         _ ≤ ∑ n ∈ E, ((cnt P n:ℝ)-mass P)^2 := sum_le_sum fun n hn => by
           have h := (mem_filter.mp hn).2
           simpa using (sq_le_sq' (by linarith [abs_nonneg ((cnt P n:ℝ)-mass P)] : -|(cnt P n:ℝ)-mass P| ≤ t) h)
         _ ≤ _ := (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)).trans (variance P N hP hc)
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
lemma bad_count (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N)
    (δ t : ℝ) (ht : 0 < t) (hd : 3*mass P ≤ δ*t^2) :
    ∃ E : Finset ℕ, (E.card:ℝ) ≤ δ*N ∧
      ∀ n ∈ Ioc 0 N, n ∉ E → |(cnt P n:ℝ)-mass P| < t := by
  classical
  let E := (Ioc 0 N).filter fun n => t ≤ |(cnt P n:ℝ)-mass P|
  refine ⟨E, (le_of_mul_le_mul_right ?_ (sq_pos_of_pos ht)), fun n hn he => ?_⟩
  · calc (E.card:ℝ)*t^2 ≤ 3*N*mass P := cheb P N hP hc t ht.le
         _ ≤ (δ*N)*t^2 := by nlinarith only [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N)]
  · exact lt_of_not_ge (fun h => he (mem_filter.mpr ⟨hn,h⟩))

lemma primes_card (N : ℕ) : (Nat.primesLE N).card ≤ N := by
  calc _ ≤ (Ioc 0 N).card := card_le_card fun p h => by
          obtain ⟨hle, hp⟩ := Nat.mem_primesLE.mp h
          exact mem_Ioc.mpr ⟨hp.pos,hle⟩
       _ = _ := by simp

noncomputable abbrev w (N : ℕ) := log (log N)
lemma wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp Mass377.logTop

lemma normal (δ : ℝ) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop,
    ∃ E : Finset ℕ, (E.card:ℝ) ≤ δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E →
      (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N := by
  obtain ⟨b,hb⟩ := Mass377.natMertens
  filter_upwards [hb.eventually_lt_const (show b < b+1 by linarith),
    hb.eventually_const_lt (show b-1 < b by linarith),
    wtop.eventually_gt_atTop (200*(|b|+1)), wtop.eventually_gt_atTop (240000/δ)] with N hu hl hw hf
  let P := Nat.primesLE N
  change mass P - w N < _ at hu
  change _ < mass P - w N at hl
  have hw0 : 0<w N := by linarith [abs_nonneg b]
  have hm : mass P ≤ 2*w N := by linarith [le_abs_self b]
  have hh : 240000 < w N * δ := (div_lt_iff₀ hδ).mp hf
  obtain ⟨E,hE,he⟩ := bad_count P N (fun p hp => (Nat.mem_primesLE.mp hp).2) (primes_card N)
    δ (w N/200) (by positivity) (by nlinarith only [hm, mul_lt_mul_of_pos_right hh hw0])
  refine ⟨E,hE,fun n hn hx => ?_⟩
  have hn' := mem_Ioc.mp hn
  have eq : P.filter (· ∣ n) = n.primeFactors := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE,Nat.mem_primeFactors,P]
    exact ⟨fun h => ⟨h.1.2,h.2,hn'.1.ne'⟩,fun h => ⟨⟨(Nat.le_of_dvd hn'.1 h.2.1).trans hn'.2,h.1⟩,h.2.1⟩⟩
  have h := abs_lt.mp (he n hn hx)
  simp only [cnt,eq] at h
  constructor <;> linarith [h.1,h.2,le_abs_self b,neg_abs_le b]

lemma prime_band (a : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ b : ℕ, a ≤ b ∧ ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ, (E.card:ℝ) ≤ δ*N ∧
      ∀ n ∈ Ioc 0 N, n ∉ E → ∃ p, p ∣ n ∧ a ≤ p ∧ p ≤ b := by
  obtain ⟨c,hc⟩ := Mass377.natMertens
  obtain ⟨b,hb,hh,hw⟩ := ((eventually_ge_atTop a).and
    ((hc.eventually_const_lt (show c-1<c by linarith)).and
    (wtop.eventually_gt_atTop (mass (Nat.primesLE a)+3/δ-c+1)))).exists
  let P := Nat.primesLE b \ Nat.primesLE a
  have hs : Nat.primesLE a ⊆ Nat.primesLE b := fun p hp => Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp hp).1.trans hb,(Nat.mem_primesLE.mp hp).2⟩
  have heq := sum_sdiff hs (f := fun p : ℕ => (1:ℝ)/p)
  change mass P + mass (Nat.primesLE a) = mass (Nat.primesLE b) at heq
  change c-1 < mass (Nat.primesLE b) - w b at hh
  have hm : 3/δ < mass P := by linarith
  have hm0 : 0 < mass P := lt_trans (by positivity) hm
  refine ⟨b,hb,?_⟩
  filter_upwards [eventually_ge_atTop P.card] with N hN
  obtain ⟨E,hE,he⟩ := bad_count P N (fun p hp => (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2)
    hN δ (mass P) hm0 (by nlinarith only [mul_lt_mul_of_pos_right ((div_lt_iff₀ hδ).mp hm) hm0])
  refine ⟨E,hE,fun n hn hx => ?_⟩
  have h := (abs_lt.mp (he n hn hx)).1
  have pos : 0 < (cnt P n:ℝ) := by linarith
  obtain ⟨p,hp⟩ := card_pos.mp (show 0<(P.filter (· ∣ n)).card by exact_mod_cast pos)
  obtain ⟨hP,hd⟩ := mem_filter.mp hp
  obtain ⟨hin,hout⟩ := mem_sdiff.mp hP
  obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hin
  exact ⟨p,hd,le_of_not_ge fun h => hout (Nat.mem_primesLE.mpr ⟨h,hpr⟩),hle⟩
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
noncomputable abbrev cutoff (N : ℕ) (c : ℝ) := (N:ℝ)^c
lemma cut_top {c : ℝ} (hc : 0<c) : Tendsto (fun N : ℕ => cutoff N c) atTop atTop :=
  (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
lemma prime_window (δ : ℝ) (hδ : 0<δ) : ∃ c : ℝ, 0<c ∧ c<1 ∧ ∀ᶠ N : ℕ in atTop,
    (∑ p ∈ Nat.primesLE N \ Nat.primesLE ⌊cutoff N c⌋₊, (1:ℝ)/p) ≤ δ := by
  let c := exp (-δ/2)
  have hc : 0<c := exp_pos _
  have hc1 : c < 1 := exp_lt_one_iff.mpr (by linarith)
  obtain ⟨b,hb⟩ := Mass377.realMertens
  have hN := hb.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hY := hb.comp (cut_top hc)
  have lim := (hN.sub hY).sub (tendsto_const_nhds (x := log c))
  have goal : Tendsto (fun N : ℕ => Mass377.S N - Mass377.S (cutoff N c)) atTop (𝓝 (-log c)) := by
    simp only [sub_self,zero_sub] at lim
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 2] with N h
    have hr : (1:ℝ) < N := by exact_mod_cast (show 1<N by omega)
    dsimp only [Function.comp_apply,Function.comp_def, Pi.sub_apply, cutoff]
    rw [Real.log_rpow (by linarith),Real.log_mul hc.ne' (Real.log_pos hr).ne']
    ring
  have he : -log c < δ := by dsimp [c]; rw [log_exp]; linarith
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [goal.eventually_lt_const he,eventually_ge_atTop 1] with N h hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hy : cutoff N c ≤ N := by simpa using rpow_le_rpow_of_exponent_le hNr hc1.le
  have sub : Nat.primesLE ⌊cutoff N c⌋₊ ⊆ Nat.primesLE N := by
    intro p hp
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_le_of_le hy),hpr⟩
  have eq := sum_sdiff sub (f:=fun p : ℕ => (1:ℝ)/p)
  simp only [Mass377.S,Nat.floor_natCast] at h
  linarith

lemma mult_union (N : ℕ) (D : Finset ℕ) :
    (((D.biUnion fun d => (Ioc 0 N).filter (d ∣ ·)).card):ℝ) ≤
      N * ∑ d ∈ D, (1:ℝ)/d := by
  calc _ ≤ ((∑ d ∈ D, ((Ioc 0 N).filter (d ∣ ·)).card : ℕ):ℝ) := by exact_mod_cast card_biUnion_le
       _ = ∑ d ∈ D, ((N/d:ℕ):ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
       _ ≤ ∑ d ∈ D, (N:ℝ)/d := sum_le_sum fun _ _ => Nat.cast_div_le
       _ = _ := by simp [mul_sum, div_eq_mul_inv]

lemma square_tail (δ : ℝ) (hδ : 0<δ) : ∃ A : ℕ, ∀ N : ℕ,
    (∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2) ≤ δ := by
  have hs : Summable (fun a : ℕ => (1:ℝ)/(a:ℝ)^2) := by
    simpa only [one_div] using (Real.summable_nat_pow_inv.mpr (by decide : 1<2))
  let s := ∑' a : ℕ, (1:ℝ)/(a:ℝ)^2
  obtain ⟨A,hA⟩ := (hs.hasSum.tendsto_sum_nat.eventually_const_lt (show s-δ < s by linarith)).exists
  refine ⟨A,fun N => ?_⟩
  have hd : Disjoint (range A) (Icc A N) := by
    rw [Finset.disjoint_left]; intro x hx hy
    exact (mem_range.mp hx).not_ge (mem_Icc.mp hy).1
  have h := hs.sum_le_tsum (range A ∪ Icc A N) (fun a _ => by positivity)
  rw [sum_union hd] at h
  change _ ≤ s at h
  linarith

lemma square_mult (N A : ℕ) :
    ((((Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)).card):ℝ) ≤
      N * ∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2 := by
  calc _ ≤ ((∑ a ∈ Icc A N, ((Ioc 0 N).filter (a^2 ∣ ·)).card:ℕ):ℝ) := by exact_mod_cast card_biUnion_le
       _ = ∑ a ∈ Icc A N, ((N/a^2:ℕ):ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
       _ ≤ ∑ a ∈ Icc A N, (N:ℝ)/(a^2:ℕ) := sum_le_sum fun _ _ => Nat.cast_div_le
       _ = _ := by simp [mul_sum, div_eq_mul_inv]
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299

lemma smooth (δ : ℝ) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ 2*δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E → ∀ q : ℕ, IsPrimePow q → q ∣ n →
    (q:ℝ) ≤ (N:ℝ)^(1-8/w N) := by
  classical
  obtain ⟨c,hc,hc1,hwin⟩ := prime_window δ hδ
  obtain ⟨A,hA⟩ := square_tail δ hδ
  filter_upwards [hwin,wtop.eventually_gt_atTop (8/(1-c)),(cut_top hc).eventually_ge_atTop ((A:ℝ)^3),
    eventually_ge_atTop 1] with N hwin hw hcut hN
  let P := Nat.primesLE N \ Nat.primesLE ⌊cutoff N c⌋₊
  let U := P.biUnion fun p => (Ioc 0 N).filter (p ∣ ·)
  let V := (Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)
  have hd1 := (mult_union N P).trans (mul_le_mul_of_nonneg_left hwin (Nat.cast_nonneg N))
  have hd2 := (square_mult N A).trans (mul_le_mul_of_nonneg_left (hA N) (Nat.cast_nonneg N))
  have hw0 : 0 < w N := lt_trans (div_pos (by norm_num) (sub_pos.mpr hc1)) hw
  have hscale : cutoff N c ≤ (N:ℝ)^(1-8/w N) := by
    apply rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    have hh := (div_lt_iff₀ (sub_pos.mpr hc1)).mp hw
    have : 8 / w N < 1-c := (div_lt_iff₀ hw0).mpr (by linarith)
    linarith
  refine ⟨U ∪ V, ?_, fun n hn hex q hq hqn => ?_⟩
  · have h : ((U ∪ V).card:ℝ) ≤ U.card + V.card := by exact_mod_cast card_union_le U V
    change (U.card:ℝ) ≤ _ at hd1
    change (V.card:ℝ) ≤ _ at hd2
    linarith
  apply le_of_not_gt
  intro hgt
  have hqbig := hscale.trans_lt hgt
  have hqN := (Nat.le_of_dvd (mem_Ioc.mp hn).1 hqn).trans (mem_Ioc.mp hn).2
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff q).mp hq
  by_cases hk1 : k=1
  · subst k
    simp only [pow_one] at *
    apply hex (mem_union_left _ (mem_biUnion.mpr ?_))
    refine ⟨p,mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hqN,hp⟩,?_⟩,mem_filter.mpr ⟨hn,hqn⟩⟩
    intro hh
    have hl := (Nat.mem_primesLE.mp hh).1
    exact hqbig.not_ge ((Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) c)).mp hl)
  · let a := p^(k/2)
    have ha2 : a^2 ∣ p^k := by
      dsimp [a]; rw [← pow_mul]; exact pow_dvd_pow p (by omega)
    have h3 : p^k ≤ a^3 := by
      dsimp [a]; rw [← pow_mul]; exact Nat.pow_le_pow_right hp.pos (by omega)
    have haA : A ≤ a := by
      by_contra! h
      have : a^3 ≤ A^3 := Nat.pow_le_pow_left h.le 3
      have hh : ((p^k:ℕ):ℝ) ≤ (A:ℝ)^3 := by exact_mod_cast h3.trans this
      linarith
    have haN : a ≤ N := (Nat.le_of_dvd (mem_Ioc.mp hn).1 ((dvd_pow_self a (by decide : 2≠0)).trans (ha2.trans hqn))).trans (mem_Ioc.mp hn).2
    exact hex (mem_union_right _ (mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨haA,haN⟩,
      mem_filter.mpr ⟨hn,ha2.trans hqn⟩⟩))

lemma small (δ : ℝ) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ 2*δ*N ∧ ∀ n : ℕ, n ∉ E → 0<n ∧ (N:ℝ)^(1-1/w N) ≤ n := by
  have hg := (tendsto_exp_div_pow_atTop 1).comp wtop
  filter_upwards [hg.eventually_gt_atTop (-log δ), Mass377.logTop.eventually_gt_atTop 0,
    eventually_ge_atTop 1, (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/δ)] with N hh hl hN hbig
  change -log δ < exp (w N)/(w N)^1 at hh
  rw [pow_one, show exp (w N) = log N from exp_log hl] at hh
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have h1 := (div_le_iff₀ hδ).mp hbig
  let E := range (⌊δ*N⌋₊+1)
  refine ⟨E,?_,fun n hn => ?_⟩
  · simp only [E,card_range,Nat.cast_add,Nat.cast_one]
    have hf := Nat.floor_le (mul_nonneg hδ.le hNr.le)
    nlinarith
  · have hfn : ⌊δ*N⌋₊ < n := by simpa [E, Nat.succ_le_iff] using hn
    have hsmall : (N:ℝ)^(1-1/w N) ≤ δ*N := by
      rw [Real.rpow_def_of_pos hNr, show log (N:ℝ)*(1-1/w N) = log N + -(log N/w N) by ring,exp_add,exp_log hNr]
      have he : exp (-(log N/w N)) ≤ δ := by rw [←Real.exp_log hδ]; exact exp_le_exp.mpr (by linarith)
      linarith only [mul_le_mul_of_nonneg_left he hNr.le]
    exact ⟨by omega,hsmall.trans (Nat.lt_of_floor_lt hfn).le⟩

lemma regularity (ε : ℝ) (hε : 0<ε) : ∃ y z : ℕ, 0<y ∧ 4*y+4≤z ∧ 4/(y:ℝ)<ε ∧
    ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ, (E.card:ℝ)≤ε*N ∧ ∀ n : ℕ, n<N → n∉E →
    (N:ℝ)^(1-1/w N) ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q ∣ n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧
    (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N ∧
    ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4*u ≤ v ∧ v ≤ z := by
  let δ := ε/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨y,hy⟩ := exists_nat_gt (4/ε)
  have hyr : (0:ℝ)<y := lt_trans (by positivity) hy
  obtain ⟨b,hb,hU⟩ := prime_band y δ hδ
  obtain ⟨z,hz,hV⟩ := prime_band (4*b+4) δ hδ
  refine ⟨y,z,by exact_mod_cast hyr,by omega,(div_lt_iff₀ hyr).mpr (by linarith only [(div_lt_iff₀ hε).mp hy]),?_⟩
  filter_upwards [small δ hδ,smooth δ hδ,normal δ hδ,hU,hV] with N hs hp ho hu hv
  obtain ⟨S,hS,ss⟩ := hs
  obtain ⟨P,hP,pp⟩ := hp
  obtain ⟨O,hO,oo⟩ := ho
  obtain ⟨U,hU,uu⟩ := hu
  obtain ⟨V,hV,vv⟩ := hv
  refine ⟨S∪P∪O∪U∪V,?_,fun n hn hex => ?_⟩
  · have upper (A B : Finset ℕ) : ((A∪B).card:ℝ) ≤ A.card + B.card := by exact_mod_cast card_union_le A B
    dsimp [δ] at hS hP hO hU hV
    linarith [upper S P,upper (S∪P) O,upper (S∪P∪O) U,upper (S∪P∪O∪U) V, mul_nonneg hε.le (Nat.cast_nonneg N)]
  · simp only [mem_union,not_or] at hex
    obtain ⟨⟨⟨⟨ns,np⟩,no⟩,nu⟩,nv⟩ := hex
    obtain ⟨hn0,hsize⟩ := ss n ns
    have hi : n ∈ Ioc 0 N := mem_Ioc.mpr ⟨hn0,hn.le⟩
    obtain ⟨u,hu,huy,hub⟩ := uu n hi nu
    obtain ⟨v,hv,hvb,hvz⟩ := vv n hi nv
    exact ⟨hsize,pp n hi np,(oo n hi no).1,(oo n hi no).2,u,v,hu,hv,huy,by omega,hvz⟩
end Regular299
end

theorem Bloom298.regularity : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1.H1 := Regular299.regularity

end

section

/-!
The pruning argument adapts Lemmas 5.5 and 5.6 and the main technical lemma
from Bhavik Mehta and Thomas Bloom, b-mehta/unit-fractions, src/main_results.lean,
commit 10ef71a300cf29e5f19beb2bbc723a035a0678de.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Copyright (c) 2022 Bhavik Mehta, Thomas Bloom. All rights reserved.
Used under Apache-2.0.

The proof maximizes a penalized mass to clean the set, erases one safe element
at a time to tune the mass, and maximizes the target divisor. The Mertens
estimates are adapted from the merged Erdős 377 proof by @marcusbuffett,
which credits @senamakel for the first estimate and successive-error bounds.
-/

section
open Filter Finset Real
open scoped Classical Topology
namespace Prune299
noncomputable abbrev mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
def rel (q n : ℕ) : Prop := q ∣ n ∧ Nat.Coprime q (n/q)
noncomputable def part (A : Finset ℕ) (q : ℕ) := A.filter (rel q)
noncomputable def active (P A : Finset ℕ) := P.filter fun q => (part A q).Nonempty
def stable (P A : Finset ℕ) (e : ℝ) : Prop :=
  ∀ q ∈ active P A, e/(q:ℝ) ≤ mass (part A q)
lemma mass_nn (A : Finset ℕ) : 0 ≤ mass A := sum_nonneg fun n _ => by positivity
lemma mass_mono {A B : Finset ℕ} (h : A⊆B) : mass A ≤ mass B :=
  sum_le_sum_of_subset_of_nonneg h (fun n _ _ => by positivity)
lemma part_mono {A B : Finset ℕ} (h : A⊆B) (q : ℕ) : part A q ⊆ part B q :=
  filter_subset_filter _ h
lemma active_mono (P : Finset ℕ) {A B : Finset ℕ} (h : A⊆B) : active P A ⊆ active P B := by
  intro q hq
  obtain ⟨hp,hn⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨hp,hn.mono (part_mono h q)⟩
lemma cleanup (P A : Finset ℕ) (e : ℝ) (he : 0≤e) :
    ∃ B⊆A, stable P B e ∧ mass A-e*mass P ≤ mass B := by
  classical
  let score (S : Finset ℕ) := mass S - e*mass (active P S)
  obtain ⟨B,hB,hmax⟩ := exists_max_image A.powerset score ⟨A,mem_powerset.mpr (Subset.refl A)⟩
  have sub := mem_powerset.mp hB
  have best := hmax A (mem_powerset.mpr (Subset.refl A))
  have lower : mass A-e*mass P ≤ mass B := by
    dsimp [score] at best
    have hP := mass_mono (filter_subset (fun q => (part A q).Nonempty) P)
    change mass (active P A) ≤ mass P at hP
    linarith only [best,mul_le_mul_of_nonneg_left hP he,mul_nonneg he (mass_nn (active P B))]
  refine ⟨B,sub,?_,lower⟩
  intro q hq
  let C := B \ part B q
  have cb : C ⊆ B := sdiff_subset
  have eq := sum_sdiff (filter_subset (rel q) B) (f:=fun n : ℕ => (1:ℝ)/n)
  change mass C + mass (part B q) = mass B at eq
  have qC : q ∉ active P C := by
    intro h
    obtain ⟨n,hn⟩ := (mem_filter.mp h).2
    obtain ⟨hc,hr⟩ := mem_filter.mp hn
    exact (mem_sdiff.mp hc).2 (mem_filter.mpr ⟨(mem_sdiff.mp hc).1,hr⟩)
  have inc : insert q (active P C) ⊆ active P B := insert_subset hq (active_mono P cb)
  have cost := mass_mono inc
  rw [mass,sum_insert qC] at cost
  have bound := hmax C (mem_powerset.mpr (cb.trans sub))
  change mass C - e*mass (active P C) ≤ mass B-e*mass (active P B) at bound
  change 1/(q:ℝ)+mass (active P C) ≤ mass (active P B) at cost
  have hc := mul_le_mul_of_nonneg_left cost he
  rw [mul_add,mul_one_div] at hc
  linarith
lemma trim (P A : Finset ℕ) (e M t : ℝ) (he : 0≤e) (hM : 0<M)
    (hP : ∀ q ∈ P, 0<q ∧ (q:ℝ)≤e*M)
    (small : ∀ n ∈ A, M≤n) (heavy : 2*e*mass P < t)
    (start : t+e*mass P ≤ mass A) :
    ∃ B⊆A, stable P B e ∧ mass B<t ∧ t-1/M≤ mass B := by
  classical
  obtain ⟨S,sub,hgood,hm⟩ := cleanup P A e he
  have descend (V : Finset ℕ) (hV : V⊆A) (good : stable P V e) (hv : t-1/M≤ mass V) :
      ∃ B⊆V, stable P B e ∧ mass B<t ∧ t-1/M≤ mass B := by
    induction V using Finset.strongInductionOn with
    | _ V ih =>
      by_cases done : mass V<t
      · exact ⟨V,Subset.rfl,good,done,hv⟩
      obtain ⟨W,hw,gw,mw⟩ := cleanup P V (2*e) (by positivity)
      have posW : 0 < mass W := by linarith
      obtain ⟨x,hx⟩ := nonempty_of_ne_empty (s:=W) (fun eq => by simp [eq,mass] at posW)
      have xv := hw hx
      let D := V.erase x
      have subD : D ⊆ V := erase_subset _ _
      have proper : D ⊂ V := erase_ssubset xv
      have xM := small x (hV xv)
      have xm : (1:ℝ)/x ≤ 1/M := one_div_le_one_div_of_le hM xM
      have mD := sum_erase_add V (fun n : ℕ => (1:ℝ)/n) xv
      change mass D + 1/(x:ℝ) = mass V at mD
      have next : stable P D e := by
        intro q hq
        have old := good q (active_mono P subD hq)
        have qp := (mem_filter.mp hq).1
        have eq : part D q = (part V q).erase x := by
          ext n
          simp [D,part,and_assoc,and_left_comm,and_comm]
        by_cases hr : rel q x
        · have wq : q ∈ active P W := mem_filter.mpr ⟨qp,⟨x,mem_filter.mpr ⟨hx,hr⟩⟩⟩
          have better := (gw q wq).trans (mass_mono (part_mono hw q))
          have delta := sum_erase_add (part V q) (fun n : ℕ => (1:ℝ)/n) (mem_filter.mpr ⟨xv,hr⟩)
          rw [←eq] at delta
          have qpos : (0:ℝ)<q := by exact_mod_cast (hP q qp).1
          have xcost : (1:ℝ)/x ≤ e/q := by
            apply (div_le_div_iff₀ (hM.trans_le xM) qpos).mpr
            simpa using ((hP q qp).2.trans (mul_le_mul_of_nonneg_left xM he))
          rw [mul_div_assoc] at better
          change mass (part D q) + 1/(x:ℝ) = mass (part V q) at delta
          linarith
        · have absent : x ∉ part V q := fun hn => hr (mem_filter.mp hn).2
          rw [eq,erase_eq_of_notMem absent]
          exact old
      obtain ⟨B,hB,gb,mb,mB⟩ := ih D proper (subD.trans hV) next (by linarith)
      exact ⟨B,hB.trans subD,gb,mb,mB⟩
  obtain ⟨B,hB,gb,mb,mB⟩ := descend S sub hgood (by linarith [one_div_pos.mpr hM])
  exact ⟨B,hB.trans sub,gb,mb,mB⟩
end Prune299
end

section
open Filter Finset Real
open scoped Classical Topology
namespace Param299
noncomputable abbrev w (N : ℕ) := log (log N)
noncomputable abbrev e (N : ℕ) := (log N)^(-(1/100:ℝ))
noncomputable abbrev M (N : ℕ) := (N:ℝ)^(1-1/w N)
lemma wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp Mass377.logTop
lemma Mtop : Tendsto M atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : 0<(1/2:ℝ))).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply tendsto_atTop_mono' _ _ h
  filter_upwards [wtop.eventually_ge_atTop 2,eventually_ge_atTop 1] with N hw hn
  apply rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hw]
lemma geom (p : ℕ) (hp : 2≤p) (N : ℕ) :
    (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1)) ≤ 2/(p:ℝ) := by
  have h : (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(N+1) ≤ 2/(p:ℝ) := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have hpos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
      have htwo : (2:ℝ)≤p := by exact_mod_cast hp
      have hh : 2/(p:ℝ)^(n+1+1) ≤ 1/(p:ℝ)^(n+1) := by
        rw [pow_succ _ (n+1),div_mul_eq_div_div]
        apply (div_le_iff₀ hpos).mpr
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      calc _ ≤ ((∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+1/(p:ℝ)^(n+1))+1/(p:ℝ)^(n+1) := add_le_add le_rfl hh
           _ = (∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(n+1) := by ring
           _ ≤ _ := ih
  linarith [show 0≤2/(p:ℝ)^(N+1) by positivity]
lemma prime_mass (N : ℕ) (P : Finset ℕ) (hb : ∀ q ∈ P, IsPrimePow q ∧ q≤N) :
    (∑ q ∈ P, (1:ℝ)/q) ≤ 2*∑ p ∈ Nat.primesLE N,(1:ℝ)/p := by
  let U := Nat.primesLE N ×ˢ range N
  let f (p : ℕ×ℕ) := p.1^(p.2+1)
  have sub : P ⊆ U.image f := by
    intro q hq
    obtain ⟨pp,le⟩ := hb q hq
    obtain ⟨p,hp,k,hk,pr,hk0,eq⟩ := (isPrimePow_nat_iff_bounded q).mp pp
    cases k with
    | zero => omega
    | succ j =>
      exact mem_image.mpr ⟨(p,j),mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨hp.trans le,pr⟩,
        mem_range.mpr (by omega)⟩,eq⟩
  calc _ ≤ ∑ q ∈ U.image f, (1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
       _ ≤ ∑ a ∈ U, (1:ℝ)/(f a) := sum_image_le_of_nonneg (fun _ _ => by positivity)
       _ = ∑ p ∈ Nat.primesLE N, ∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1) := by
         simp [U,f,sum_product]
       _ ≤ ∑ p ∈ Nat.primesLE N, 2/(p:ℝ) := sum_le_sum fun p hp => geom p (Nat.mem_primesLE.mp hp).2.two_le N
       _ = _ := by rw [mul_sum]; congr 1; ext; ring
lemma eMass : Tendsto (fun N => e N*w N) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/100:ℝ) (by norm_num)).comp wtop
  apply h.congr'
  filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hN
  simp only [Function.comp_apply,Real.rpow_one,e,Real.rpow_def_of_pos hN]
  dsimp only [w]
  ring_nf
lemma params (δ : ℝ) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop,
    0<e N ∧ 0<M N ∧ 1/M N<δ ∧ (N:ℝ)^(1-8/w N) ≤ e N*M N ∧
    ∀ P : Finset ℕ, (∀ q ∈ P, IsPrimePow q ∧ q≤N) → e N*(∑ q ∈ P,(1:ℝ)/q)<δ := by
  obtain ⟨b,hb⟩ := Mass377.natMertens
  filter_upwards [eMass.eventually_lt_const (show 0<δ/4 by positivity),
    hb.eventually_lt_const (show b<b+1 by linarith),wtop.eventually_gt_atTop (|b|+2),
    (tendsto_exp_div_pow_atTop 2 |>.comp wtop).eventually_ge_atTop 1,
    (tendsto_inv_atTop_zero.comp Mtop).eventually_lt_const hδ,
    Mass377.logTop.eventually_gt_atTop 0,eventually_ge_atTop 1] with N het hb hw hex hM hl hN
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have pos : 0<e N := Real.rpow_pos_of_pos hl _
  have hw0 : 0<w N := by linarith [abs_nonneg b]
  refine ⟨pos,Real.rpow_pos_of_pos hn _,by simpa [one_div] using hM,?_,?_⟩
  · change 1≤exp (w N)/(w N)^2 at hex
    rw [show exp (w N)=log N from exp_log hl] at hex
    have hw2 := (le_div_iff₀ (sq_pos_of_pos hw0)).mp hex
    rw [e,M,Real.rpow_def_of_pos hl,Real.rpow_def_of_pos hn,Real.rpow_def_of_pos hn,←exp_add]
    apply exp_le_exp.mpr
    change log N*(1-8/w N) ≤ w N * -(1/100:ℝ)+log N*(1-1/w N)
    field_simp [hw0.ne']
    nlinarith
  · intro P hP
    change (∑ p ∈ Nat.primesLE N,(1:ℝ)/p)-w N < b+1 at hb
    have s : (∑ p ∈ Nat.primesLE N,(1:ℝ)/p) ≤ 2*w N := by linarith [le_abs_self b]
    have bound := mul_le_mul_of_nonneg_left ((prime_mass N P hP).trans (mul_le_mul_of_nonneg_left s (by norm_num))) pos.le
    change e N*w N < δ/4 at het
    linarith
end Param299
end

section
open Filter Finset Real
open scoped Classical Topology
namespace Prune299
noncomputable def powers (A : Finset ℕ) := A.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
lemma powers_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
    IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ rel q n := by
  obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
  obtain ⟨div,pp,copr⟩ := mem_filter.mp hq
  obtain ⟨hd,hpos⟩ := Nat.mem_divisors.mp div
  exact ⟨pp,n,hn,hpos,hd,copr⟩
lemma solve (z : ℕ) : ∀ᶠ N : ℕ in atTop,
  ∀ (A : Finset ℕ) (u v : ℕ), 1≤u → u≤v → 2≤v → v≤z → 0∉A → A ⊆ range N →
  (∀ n ∈ A, Param299.M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/Param299.w N)) ∧
    (99/100:ℝ)*Param299.w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*Param299.w N) →
  2/(u:ℝ) + 1/(10*(z:ℝ)) ≤ mass A →
  (∀ n ∈ A, ∃ d ∈ Icc u v, d∣n) →
  ∃ B⊆A, ∃ d ∈ Icc u v,
    (mass B < 2/(d:ℝ) ∧ 2/(d:ℝ)-1/Param299.M N ≤ mass B ∧ d∣B.lcm id ∧
      ∀ q ∈ powers B, Param299.e N ≤ ∑ n ∈ part B q, (q:ℝ)/n) ∧
    ∀ n ∈ B, ∀ j : ℕ, j∣n → u≤j → d≤j := by
  classical
  let δ : ℝ := 1/(100*((z:ℝ)+1)^2)
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [Param299.params δ hδ] with N hN
  intro A u v hu huv hv hvz h0 hAN reg massA divs
  obtain ⟨he,hM,inv,scale,cost⟩ := hN
  let P := powers A
  let e := Param299.e N
  let M := Param299.M N
  have zr : (2:ℝ)≤z := by exact_mod_cast hv.trans hvz
  have zp : (0:ℝ)<z := by linarith
  have sep : δ≤1/(10*(z:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg (z:ℝ)]
  have powersP (q : ℕ) (hq : q∈P) : IsPrimePow q ∧ q≤N ∧ (q:ℝ)≤e*M := by
    obtain ⟨pp,n,hn,hn0,hr⟩ := powers_mem hq
    exact ⟨pp,(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hr.1).trans (mem_range.mp (hAN hn)).le,
      ((reg n hn).2.1 q pp hr.1).trans scale⟩
  have hcost := cost P fun q hq => ⟨(powersP q hq).1,(powersP q hq).2.1⟩
  change e*mass P<δ at hcost
  have hP (q : ℕ) (hq : q∈P) : 0<q ∧ (q:ℝ)≤e*M :=
    ⟨(powersP q hq).1.pos,(powersP q hq).2.2⟩
  have target (d : ℕ) (hd : d ∈ Icc u v) : 2*δ<2/(d:ℝ) := by
    have dp : (0:ℝ)<d := by exact_mod_cast (show 0<d from Nat.lt_of_lt_of_le (by omega) (mem_Icc.mp hd).1)
    have dz : (d:ℝ)≤z := by exact_mod_cast (mem_Icc.mp hd).2.trans hvz
    have tmp : δ<1/(d:ℝ) := by
      apply one_div_lt_one_div_of_lt dp
      nlinarith [sq_nonneg (z:ℝ)]
    calc 2*δ < 2*(1/(d:ℝ)) := mul_lt_mul_of_pos_left tmp (by norm_num)
         _ = 2/d := by ring
  let can (d : ℕ) : Prop := ∃ B⊆A, stable P B e ∧ mass B<2/(d:ℝ) ∧
    2/(d:ℝ)-1/M≤ mass B ∧ ∀ n ∈ B, ∀ j : ℕ, j∣n → u≤j → d≤j
  let D := (Icc u v).filter can
  have huI := mem_Icc.mpr (show u≤u ∧ u≤v from ⟨le_rfl,huv⟩)
  obtain ⟨S,hS,gs,ms,mS⟩ := trim P A e M (2/u) he.le hM hP (fun n hn => (reg n hn).1)
    (by linarith [target u huI]) (by linarith)
  have ud : u∈D := mem_filter.mpr ⟨huI,S,hS,gs,ms,mS,fun n hn j hj hju => hju⟩
  let d := D.max' ⟨u,ud⟩
  have hd : d∈D := max'_mem _ _
  obtain ⟨hdi,B,hB,gb,mb,mB,minB⟩ := mem_filter.mp hd
  have dr : (0:ℝ)<d := by exact_mod_cast (show 0<d by have := (mem_Icc.mp hdi).1; omega)
  have exist : ∃ n ∈ B, d∣n := by
    by_contra! none
    have Bpos : 0 < mass B := by
      change 1/M<δ at inv
      linarith [target d hdi]
    obtain ⟨n,hn⟩ := nonempty_of_ne_empty (s:=B) (fun eq => by simp [eq,mass] at Bpos)
    obtain ⟨j,hj,hjn⟩ := divs n (hB hn)
    have jmin := minB n hn j hjn (mem_Icc.mp hj).1
    have jne : j≠d := by rintro rfl; exact none n hn hjn
    have hs : d+1 ∈ Icc u v := mem_Icc.mpr ⟨by have := (mem_Icc.mp hdi).1; omega,
      by have := (mem_Icc.mp hj).2; omega⟩
    have ds : (0:ℝ)<(d:ℝ)+1 := by linarith
    have dz : (d:ℝ)+1≤z := by exact_mod_cast (mem_Icc.mp hs).2.trans hvz
    have gap : 2*δ ≤ 2/(d:ℝ)-2/((d:ℝ)+1) := by
      have big : (d:ℝ)*((d:ℝ)+1) ≤ 100*((z:ℝ)+1)^2 := by
        nlinarith [mul_le_mul (show (d:ℝ)≤(z:ℝ)+1 by linarith) (show (d:ℝ)+1≤(z:ℝ)+1 by linarith) ds.le (by positivity : 0≤(z:ℝ)+1),sq_nonneg ((z:ℝ)+1)]
      have u' := one_div_le_one_div_of_le (mul_pos dr ds) big
      change δ≤1/((d:ℝ)*((d:ℝ)+1)) at u'
      calc 2*δ ≤ 2*(1/((d:ℝ)*((d:ℝ)+1))) := by linarith
           _ = _ := by field_simp; ring
    obtain ⟨C,hC,gC,mc,mC⟩ := trim P B e M (2/((d+1:ℕ):ℝ)) he.le hM hP
      (fun n hn => (reg n (hB hn)).1) (by linarith [target (d+1) hs])
      (by push_cast; change 1/M<δ at inv; linarith)
    have next : d+1 ∈ D := mem_filter.mpr ⟨hs,C,hC.trans hB,gC,mc,mC,by
      intro n hn j hj hju
      have le := minB n (hC hn) j hj hju
      have ne : j≠d := by rintro rfl; exact none n (hC hn) hj
      omega⟩
    have le := le_max' D (d+1) next
    change d+1≤d at le
    omega
  obtain ⟨x,hx,hdx⟩ := exist
  refine ⟨B,hB,d,hdi,⟨mb,mB,hdx.trans (dvd_lcm hx),?_⟩,minB⟩
  intro q hq
  obtain ⟨pp,n,hn,h0,hr⟩ := powers_mem hq
  have qp : q∈P := mem_biUnion.mpr ⟨n,hB hn,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hr.1,h0⟩,pp,hr.2⟩⟩
  have h := gb q (mem_filter.mpr ⟨qp,⟨n,mem_filter.mpr ⟨hn,hr⟩⟩⟩)
  have qr : (0:ℝ)<q := by exact_mod_cast (hP q qp).1
  have hh := (div_le_iff₀ qr).mp h
  calc e ≤ mass (part B q)*(q:ℝ) := hh
       _ = ∑ n ∈ part B q, (q:ℝ)/n := by rw [mass,sum_mul]; apply sum_congr rfl; intro n hn; ring
end Prune299
end

theorem Bloom298.pruning : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H1 := by
  classical
  intro z
  filter_upwards [Prune299.solve z] with N hN
  intro A u v hu huv hv hvz h0 hAN reg massA divs
  obtain ⟨B,hB,d,hd,⟨lo,hi,dvd,localSum⟩,minimal⟩ :=
    hN A u v hu huv hv hvz h0 hAN reg massA divs
  refine ⟨B,hB,d,hd,⟨lo,hi,dvd,?_⟩,minimal⟩
  intro q hq
  have hp : q ∈ Prune299.powers B := by simpa [Prune299.powers] using hq
  have eq : Prune299.part B q = B.filter (fun n => q∣n ∧ Nat.Coprime q (n/q)) := by
    ext n
    simp [Prune299.part,Prune299.rel]
  simpa only [eq] using localSum q hp

end

section

/-!
# The first forcing alternative for dense sets of denominators

This follows Proposition 6.3 of the Bloom formalization by Bhavik Mehta and
Thomas Bloom, b-mehta/unit-fractions, src/main_results.lean and
src/aux_lemmas.lean at commit 10ef71a300cf29e5f19beb2bbc723a035a0678de,
including contributions by Eric Rodriguez. Copyright (c) 2021 Bhavik Mehta,
Thomas Bloom. Used under Apache-2.0.

The common-divisor argument and Euler bound for the cofactor prime-power
mass use @marcusbuffett's Erdős 299 proofs. Their Mertens input was developed
in the merged Erdős 377 proof, starting with @senamakel's Erdős 962 proof
at d757b84b7870c7b80a9e62d5e93a293328aee0d4. The elementary bound on the
number of distinct prime factors below is adapted from Will Howe,
H0W4RD-dev/croot-unit-fractions, Prop1.lean at
c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, used under Apache-2.0.

Each prime power whose multiples carry sufficient mass has a heavy interval
point. Three such points would carry more prime-power mass than is available.
If two distinct points x and y occur, an exceptional denominator hitting h
divides the nonzero product (x-h)(y-h). A uniform divisor bound controls
these exceptions, so one of the two points captures a third of the mass.
-/
open Filter Finset Real
open scoped Classical Topology
namespace Bloom298.Setup
noncomputable abbrev w (N : ℕ) := log (log N)
noncomputable abbrev e (N : ℕ) := (log N)^(-(1/100:ℝ))
noncomputable abbrev M (N : ℕ) := (N:ℝ)^(1-1/w N)
noncomputable abbrev K (N : ℕ) := M N*(N:ℝ)^(-2/w N)
noncomputable abbrev L (N : ℕ) := M N/(2*(log N)^(1/100:ℝ))
noncomputable abbrev mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
noncomputable def powers (A : Finset ℕ) := A.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
noncomputable def part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
def Regular (N n : ℕ) : Prop := M N ≤ n ∧
  (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧
  (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N

/-- Extract a common divisor larger than the interval from a local family.
The coprime cofactors carry enough reciprocal mass and retain most prime factors. -/
def H1 : Prop := ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (q : ℕ), 0∉A → A⊆range N →
  (∀ n ∈ A, Regular N n) → IsPrimePow q → e N/2 ≤ ∑ n ∈ part A q,(q:ℝ)/n →
  ∃ (D : ℕ) (C : Finset ℕ), K N < D ∧ q∣D ∧
    (log N)^(-(1/99:ℝ)) ≤ mass C ∧
    (∀ m ∈ C, D*m ∈ A ∧ Nat.Coprime m D ∧
      (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N)

/-- A family of cofactors of sufficient mass and with almost the normal
number of distinct prime factors has large prime-power reciprocal mass. -/
def H2 : Prop := ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,
  (log N)^(-(1/99:ℝ)) ≤ mass C →
  (∀ m ∈ C, (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N) →
  (35/100:ℝ)*w N ≤ mass (powers C)

lemma power_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
    IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ q∣n ∧ Nat.Coprime q (n/q) := by
  obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
  obtain ⟨dv,pp,cp⟩ := mem_filter.mp hq
  obtain ⟨hd,h0⟩ := Nat.mem_divisors.mp dv
  exact ⟨pp,n,hn,h0,hd,cp⟩
end Bloom298.Setup

open Filter Real Finset
open scoped Classical Topology
namespace Rough299
noncomputable abbrev w (N:ℕ) := log (log (N:ℝ))
noncomputable abbrev X (N:ℕ) := exp (log N/(2*(w N)^2))
noncomputable abbrev G (N:ℕ) := (range N).filter fun q : ℕ => IsPrimePow q ∧ X N < q
noncomputable abbrev R (N:ℕ) := (range N).filter fun d => 0<d ∧
  ∀ p : ℕ, p∈d.primeFactors → X N < (p:ℝ)^d.factorization p
lemma nonsimple : ∃ C : ℝ, ∀ (N : ℕ) (Q : Finset ℕ),
    (∀ q ∈ Q, IsPrimePow q ∧ ¬q.Prime ∧ q≤N) → ∑ q∈Q,(1:ℝ)/q ≤ C := by
  let C := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
  refine ⟨2*C,?_⟩
  intro N Q hQ
  let U := Nat.primesLE N ×ˢ range N
  let f (z : ℕ×ℕ) := z.1^(z.2+2)
  have sub : Q⊆U.image f := by
    intro q hq
    obtain ⟨pp,no,le⟩ := hQ q hq
    obtain ⟨p,lp,k,lk,pr,pk,e⟩ := (isPrimePow_nat_iff_bounded q).mp pp
    have g : k≠1 := by rintro rfl; simp_all
    exact mem_image.mpr ⟨(p,k-2),mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨lp.trans le,pr⟩,mem_range.mpr (by omega)⟩,
      by dsimp [f]; rwa [show k-2+2=k by omega]⟩
  calc _ ≤ ∑ q∈U.image f,(1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
       _ ≤ ∑ z∈U,(1:ℝ)/(f z) := sum_image_le_of_nonneg (fun _ _ => by positivity)
       _ = ∑ p∈Nat.primesLE N, ∑ k∈ range N, (1:ℝ)/(p:ℝ)^(k+2) := by simp [U,f,sum_product]
       _ ≤ ∑ p∈Nat.primesLE N, 2*((p:ℝ)^2)⁻¹ := by
         apply sum_le_sum
         intro p hp
         have g := Param299.geom p (Nat.mem_primesLE.mp hp).2.two_le N
         have pp : (0:ℝ)<p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
         simp_rw [show ∀ k : ℕ, (1:ℝ)/(p:ℝ)^(k+2)=(1/(p:ℝ)^(k+1))/p by intro k; rw [pow_succ,div_div]]
         rw [←sum_div]
         calc _ ≤ ((2:ℝ)/p)/p := div_le_div_of_nonneg_right g pp.le
              _ = _ := by ring
       _ ≤ _ := by
         rw [←mul_sum]
         exact mul_le_mul_of_nonneg_left ((Real.summable_nat_pow_inv.mpr (by norm_num : 1<2)).sum_le_tsum _ (fun _ _ => by positivity)) (by norm_num)
lemma small_mass (c : ℝ) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, ∑ q∈G N,(1:ℝ)/q ≤ c*w N := by
  have wt : Tendsto w atTop atTop := Param299.wtop
  have xt : Tendsto X atTop atTop := by
    have ht := (tendsto_exp_div_pow_atTop 2).comp wt
    have h2 := ht.atTop_div_const (by norm_num : (0:ℝ)<2)
    apply tendsto_exp_atTop.comp
    apply h2.congr'
    filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hN
    simp only [Function.comp_apply,w,exp_log hN,div_div]
    ring
  obtain ⟨b,hb⟩ := Mass377.realMertens
  obtain ⟨C,cc⟩ := nonsimple
  have little := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp wt).eventually_lt_const (show 0<c/4 by positivity)
  filter_upwards [(hb.comp xt).eventually_const_lt (show b-1<b by linarith),
    (hb.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_lt_const (show b<b+1 by linarith),
    little, wt.eventually_gt_atTop 2, wt.eventually_gt_atTop (2*(2+log 2+C)/c),
    Mass377.logTop.eventually_gt_atTop 0,eventually_ge_atTop 2] with N lower upper small hw huge nlog hn
  have wp : 0<w N := by linarith
  have xp : X N≤N := by
    apply (le_log_iff_exp_le (by positivity : (0:ℝ)<N)).mp
    exact div_le_self nlog.le (by nlinarith [sq_nonneg (w N-1)])
  have lt : log (log (X N)) = w N-log 2-2*log (w N) := by
    rw [X,log_exp,log_div nlog.ne' (by positivity),log_mul (by norm_num) (by positivity),log_pow]
    dsimp only [w]; ring
  let P := (G N).filter Nat.Prime
  let Q := G N \ P
  have sub : P ⊆ Nat.primesLE N \ Nat.primesLE ⌊X N⌋₊ := by
    intro q hq
    obtain ⟨qG,pr⟩ := mem_filter.mp hq
    obtain ⟨qr,_,gt⟩ := mem_filter.mp qG
    exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨(mem_range.mp qr).le,pr⟩,
      fun h => (not_le_of_gt gt) ((Nat.le_floor_iff (exp_pos _).le).mp (Nat.mem_primesLE.mp h).1)⟩
  have incl : Nat.primesLE ⌊X N⌋₊ ⊆ Nat.primesLE N := by
    intro p hp
    have le : ⌊X N⌋₊ ≤ N := Nat.floor_le_of_le (by exact_mod_cast xp)
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans le,(Nat.mem_primesLE.mp hp).2⟩
  have prim := sum_le_sum_of_subset_of_nonneg (f:=fun q : ℕ => (1:ℝ)/q) sub (fun _ _ _ => by positivity)
  have sumP := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) incl
  have sP : ∑ q∈P,(1:ℝ)/q ≤ Mass377.S N-Mass377.S (X N) := by
    simp only [Mass377.S,Nat.floor_natCast]
    linarith
  have ns := cc N Q (fun q hq => by
    obtain ⟨qG,no⟩ := mem_sdiff.mp hq
    obtain ⟨qr,pr,_⟩ := mem_filter.mp qG
    exact ⟨pr,fun p => no (mem_filter.mpr ⟨qG,p⟩),(mem_range.mp qr).le⟩)
  have tot := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) (show P⊆G N from filter_subset _ _)
  change (∑ q∈Q, _)+(∑ q∈P, _) = _ at tot
  change b-1 < Mass377.S (X N)-log (log (X N)) at lower
  change Mass377.S N-w N<b+1 at upper
  change log (w N)/w N<c/4 at small
  rw [div_lt_iff₀ wp] at small
  rw [div_lt_iff₀ hc] at huge
  rw [lt] at lower
  linarith
end Rough299

namespace Rough299
open Finset Real
open scoped BigOperators
def factors (n : ℕ) := n.primeFactors.image (fun p => p ^ n.factorization p)
lemma distinct (n : ℕ) : Set.InjOn (fun p => p ^ n.factorization p) (↑n.primeFactors) := by
  intro p hp q hq he
  have h (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p^n.factorization p).primeFactors = {p} :=
    Nat.primeFactors_prime_pow (Finsupp.mem_support_iff.mp hp) (Nat.prime_of_mem_primeFactors hp)
  have eq := congrArg Nat.primeFactors he
  exact Finset.singleton_inj.mp ((h p hp).symm.trans (eq.trans (h q hq)))
lemma recover {n : ℕ} (hn : n ≠ 0) : ∏ q ∈ factors n, q = n := by
  rw [factors,prod_image (distinct n)]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm
lemma exponential_bound (N : ℕ) (u : ℝ) :
    (∑ n ∈ R N, exp (u*(n.primeFactors.card:ℝ))/n) ≤
      exp (exp u*∑ q ∈ G N,(1:ℝ)/q) := by
  let C := R N
  have hz : 0∉C := fun h => (mem_filter.mp h).2.1.false
  classical
  let w (q : ℕ) := exp u / (q : ℝ)
  have reconstruct (n : ℕ) (hn : n ∈ C) : ∏ q ∈ factors n, w q = exp (u*(n.primeFactors.card:ℝ)) / n := by
    have hne : n ≠ 0 := fun e => hz (e ▸ hn)
    have den : (∏ q ∈ factors n, (q : ℝ)) = n := by
      change (∏ x ∈ factors n, (Nat.castRingHom ℝ) x) = (Nat.castRingHom ℝ) n
      rw [← map_prod,recover hne]
    simp only [w,prod_div_distrib,prod_const,den]
    rw [factors,card_image_of_injOn (distinct n),← exp_nat_mul,mul_comm]
  have inject : Set.InjOn factors (↑C) := by
    intro n hn m hm heq
    have h := congrArg (fun s : Finset ℕ => ∏ q ∈ s, q) heq
    simpa only [recover (show n≠0 from fun e => hz (e ▸ hn)),recover (show m≠0 from fun e => hz (e ▸ hm))] using h
  have included : C.image factors ⊆ (G N).powerset := by
    intro s hs
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hs
    apply mem_powerset.mpr
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨ng,pos,rough⟩ := mem_filter.mp hn
    have pr := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd pos (Nat.ordProj_dvd n p)).trans_lt (mem_range.mp ng)),
      pr.isPrimePow.pow (Finsupp.mem_support_iff.mp hp),by exact_mod_cast rough p hp⟩
  calc
    _ = ∑ s ∈ C.image factors, ∏ q ∈ s, w q := by
      rw [sum_image inject]
      exact sum_congr rfl (fun n hn => (reconstruct n hn).symm)
    _ ≤ ∑ s ∈ (G N).powerset, ∏ q ∈ s, w q :=
      sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => prod_nonneg fun _ _ => by dsimp [w]; positivity)
    _ = ∏ q ∈ G N, (1+w q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ G N, exp (w q) := prod_le_prod
      (fun q _ => by dsimp [w]; positivity) (fun q _ => by linarith [add_one_le_exp (w q)])
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro q hq; dsimp [w]; ring
end Rough299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
lemma budget : ∀ᶠ N : ℕ in atTop,
    ∑ d∈R N, (if (d.primeFactors.card:ℝ)≤w N/110 then (log N)^(-(1/99:ℝ))
      else 1+log N)/d < (log N)^(-(1/100:ℝ))/2 := by
  let δ : ℝ := 1/30000
  have dil : 0<δ/exp 330 := by dsimp [δ]; positivity
  filter_upwards [small_mass _ dil,Param299.wtop.eventually_gt_atTop 0,
    Mass377.logTop.eventually_gt_atTop 2,Param299.wtop.eventually_gt_atTop (20000*log 2)]
    with N small hw hb big
  let b := log (N:ℝ)
  let a := b^(-(1/99:ℝ))
  have bp : 0<b := by dsimp [b]; linarith
  have ap : 0<a := rpow_pos_of_pos bp _
  have form : a=exp (-(1/99:ℝ)*w N) := by rw [show a=b^(-(1/99:ℝ)) by rfl,rpow_def_of_pos bp]; congr 1; ring
  have est := exponential_bound N 330
  have em : exp 330*(∑ q∈G N,(1:ℝ)/q) ≤ δ*w N := by
    calc _ ≤ exp 330*((δ/exp 330)*w N) := mul_le_mul_of_nonneg_left small (exp_pos 330).le
         _ = _ := by field_simp
  have point (d : ℕ) : (if (d.primeFactors.card:ℝ)≤w N/110 then a else 1+b) ≤
      a*exp (330*(d.primeFactors.card:ℝ)) := by
    split_ifs with h
    · have one : 1 ≤ exp (330*(d.primeFactors.card:ℝ)) := one_le_exp (by positivity)
      simpa using mul_le_mul_of_nonneg_left one ap.le
    · have lt := lt_of_not_ge h
      rw [form,←exp_add]
      have high : 2*w N < -(1/99:ℝ)*w N+330*d.primeFactors.card := by linarith
      have eq : exp (2*w N)=b^2 := by rw [show 2*w N=w N*2 by ring,Real.exp_mul]; norm_cast; rw [exp_log bp]
      have ge : 1+b ≤ b^2 := by change 2<b at hb; nlinarith [sq_nonneg (b-2)]
      exact ge.trans (eq ▸ (exp_le_exp.mpr high.le))
  calc
    _ ≤ ∑ d∈R N, a*(exp (330*(d.primeFactors.card:ℝ))/d) := by
      apply sum_le_sum
      intro d hd
      simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right (point d) (Nat.cast_nonneg d : (0:ℝ)≤d))
    _ ≤ a*exp (δ*w N) := by
      rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (est.trans (exp_le_exp.mpr em)) ap.le
    _ < _ := by
      rw [form,←exp_add,lt_div_iff₀ (by norm_num : (0:ℝ)<2),
        show (2:ℝ)=exp (log 2) from (exp_log (by norm_num)).symm,←exp_add,rpow_def_of_pos bp,exp_lt_exp]
      change _ < w N * (-(1/100:ℝ))
      dsimp only [δ]
      linarith
end Rough299

open Real Finset Filter
open scoped Classical Topology
namespace Rough299
lemma select : ∀ᶠ N : ℕ in atTop,
  let M := (N:ℝ)^(1-1/w N)
  ∀ n q : ℕ, 0<n → n<N → M≤n → (n.primeFactors.card:ℝ)≤2*w N →
    IsPrimePow q → q∣n → Nat.Coprime q (n/q) → ∃ d∈R N,
    M*(N:ℝ)^(-2/w N) < q*(d:ℝ) ∧ q*d∣n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
  filter_upwards [Param299.wtop.eventually_gt_atTop 1,Mass377.logTop.eventually_gt_atTop 0,eventually_gt_atTop 1]
    with N hw hb hn
  intro M n q nz nb nM count qp qn cp
  let m := n/q
  have mpos : 0 < m := Nat.div_pos (Nat.le_of_dvd nz qn) qp.pos
  have eqn : q*m=n := Nat.mul_div_cancel' qn
  let S := m.primeFactors.filter fun p : ℕ => X N < (p:ℝ)^m.factorization p
  let V := m.primeFactors \ S
  let F (p : ℕ) := p^m.factorization p
  let d := ∏ p∈S, F p
  let t := ∏ p∈V, F p
  have prod : d*t=m := by
    rw [mul_comm,show t*d = ∏ p∈m.primeFactors, F p from prod_sdiff (filter_subset _ _)]
    exact (Nat.prod_primeFactors_pow_factorization mpos.ne').symm
  have posprod : 0<d*t := prod.symm ▸ mpos
  have dpos : 0<d := by
    by_contra! he
    rw [show d=0 by omega,zero_mul] at posprod
    omega
  have tpos : 0<t := by
    by_contra! he
    rw [show t=0 by omega,mul_zero] at posprod
    omega
  have ddiv : d∣m := ⟨t,prod.symm⟩
  have mdiv : m∣n := ⟨q,by simpa [mul_comm] using eqn.symm⟩
  have split : Nat.Coprime d t := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro a ha
    exact (((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (mem_sdiff.mp ha).1)).mpr (by rintro rfl; exact (mem_sdiff.mp ha).2 hp)).pow_left _).pow_right _
  have dR : d∈R N := by
    refine mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd nz (ddiv.trans mdiv)).trans_lt nb),dpos,?_⟩
    intro p pd
    have pm := Nat.primeFactors_mono ddiv mpos.ne' pd
    have pp := Nat.prime_of_mem_primeFactors pd
    have pds := Nat.dvd_of_mem_primeFactors pd
    have npt := (pp.coprime_iff_not_dvd).mp (split.coprime_dvd_left pds)
    have e : m.factorization p=d.factorization p := by
      rw [←prod,Nat.factorization_mul_apply_of_coprime split,Nat.factorization_eq_zero_of_not_dvd npt,add_zero]
    rw [←e]
    by_contra! fail
    have pv : p∈V := mem_sdiff.mpr ⟨pm,by simpa [S,pm] using fail⟩
    exact npt ((dvd_pow_self _ (Finsupp.mem_support_iff.mp pm)).trans (dvd_prod_of_mem F pv))
  have nrep : (q*d)*t=n := by rw [mul_assoc,prod,eqn]
  have cop : Nat.Coprime (q*d) t := Nat.Coprime.mul_left (cp.coprime_dvd_right (show t∣m from ⟨d,by rw [mul_comm,prod]⟩)) split
  have divt : n/(q*d)=t := by rw [←nrep,Nat.mul_div_cancel_left _ (Nat.mul_pos qp.pos dpos)]
  refine ⟨d,dR,?_,⟨t,nrep.symm⟩,divt ▸ cop⟩
  have logt : log (t:ℝ) ≤ log N / w N := by
    have vp (p : ℕ) (hp : p∈V) : 0<(F p:ℝ) := by
      dsimp [F]
      positivity [(Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1).pos]
    have val (p : ℕ) (hp : p∈V) : log (F p:ℝ)≤log N/(2*(w N)^2) := by
      have ne := (mem_sdiff.mp hp).2
      have h : (F p:ℝ)≤X N := by
        by_contra! no
        apply ne
        apply mem_filter.mpr
        exact ⟨(mem_sdiff.mp hp).1,by simpa [F] using no⟩
      exact (log_le_log (vp p hp) h).trans_eq (log_exp _)
    have vsub : V⊆n.primeFactors := (sdiff_subset).trans (Nat.primeFactors_mono mdiv nz.ne')
    have card : (V.card:ℝ)≤2*w N := (by exact_mod_cast card_le_card vsub : (V.card:ℝ)≤n.primeFactors.card).trans count
    have eval : log (t:ℝ)=∑ p∈V, log (F p:ℝ) := by
      simp only [t,Nat.cast_prod]
      exact log_prod (fun p hp => (vp p hp).ne')
    rw [eval]
    calc _ ≤ ∑ _p∈V, log N/(2*(w N)^2) := sum_le_sum val
         _ ≤ 2*w N*(log N/(2*(w N)^2)) := by
           simp only [sum_const,nsmul_eq_mul]
           exact mul_le_mul_of_nonneg_right card (by positivity)
         _ = _ := by field_simp <;> ring
  have nr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have tr : (0:ℝ)<t := by exact_mod_cast tpos
  have upper : (t:ℝ)<(N:ℝ)^(2/w N) := by
    apply (log_lt_log_iff tr (rpow_pos_of_pos nr _)).mp
    rw [log_rpow nr]
    have bpos : 0<log N/w N := by positivity
    linarith [show 2/w N*log N=2*(log N/w N) by ring]
  have rho := rpow_pos_of_pos nr (2/w N)
  rw [show (-2:ℝ)/w N=-(2/w N) by ring,rpow_neg nr.le,←div_eq_mul_inv,div_lt_iff₀ rho]
  have eqr : (q:ℝ)*d*t=n := by exact_mod_cast nrep
  exact nM.trans_lt (eqr ▸ (mul_lt_mul_of_pos_left upper (by exact_mod_cast Nat.mul_pos qp.pos dpos : 0<(q:ℝ)*d)))
end Rough299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
lemma divisor_sample {N : ℕ} {S : Finset ℕ} (hN : 0<N) (sm : S⊆Icc 1 N) :
    (∑ n∈S,(1:ℝ)/n) ≤ 1+log N := by
  have e := harmonic_floor_le_one_add_log (N:ℝ) (by exact_mod_cast hN)
  rw [Nat.floor_natCast,harmonic_eq_sum_Icc,Rat.cast_sum] at e
  push_cast at e
  simpa [one_div] using (sum_le_sum_of_subset_of_nonneg (f:=fun n : ℕ => (n:ℝ)⁻¹) sm (fun _ _ _ => by positivity)).trans e
theorem result : Bloom298.Setup.H1 := by
  classical
  filter_upwards [select,budget,Param299.wtop.eventually_gt_atTop 1000,eventually_gt_atTop 2,
    Mass377.logTop.eventually_gt_atTop 0] with N hsel estimate hw hn hb
  intro A q ha an reg qp mass
  let J := A.filter (fun n => q∣n ∧ Nat.Coprime q (n/q))
  let M := (N:ℝ)^(1-1/w N)
  let K := M*(N:ℝ)^(-2/w N)
  let b := log (N:ℝ)
  let v (d : ℕ) := if (d.primeFactors.card:ℝ)≤w N/110 then b^(-(1/99:ℝ)) else 1+b
  let a := b^(-(1/99:ℝ))
  have ap : 0<a := rpow_pos_of_pos hb _
  have qp0 : 0<q := qp.pos
  have haveD {n : ℕ} (hn : n∈J) := hsel n q
    (Nat.pos_of_ne_zero (fun e => ha (e ▸ (mem_filter.mp hn).1))) (mem_range.mp (an (mem_filter.mp hn).1))
    (reg n (mem_filter.mp hn).1).1 (reg n (mem_filter.mp hn).1).2.2.2 qp (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2
  let f (n : ℕ) := if hn : n∈J then (haveD hn).choose else 1
  have spec {n : ℕ} (hn : n∈J) : f n∈R N ∧ K<q*(f n:ℝ) ∧ q*f n∣n ∧ Nat.Coprime (q*f n) (n/(q*f n)) := by
    simpa [f,hn,K,M] using (haveD hn).choose_spec
  let F (d : ℕ) := J.filter fun n => f n=d
  let C (d : ℕ) := (F d).image (fun n => n/(q*d))
  let m (S : Finset ℕ) := ∑ n∈S,(1:ℝ)/n
  have Dspec {d n : ℕ} (hn : n∈F d) : n∈A ∧ K<q*(d:ℝ) ∧ q*d∣n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
    obtain ⟨j,e⟩ := mem_filter.mp hn
    exact ⟨(mem_filter.mp j).1,e ▸ (spec j).2⟩
  have factor {d n : ℕ} (hn : n∈F d) : q*d*(n/(q*d))=n := Nat.mul_div_cancel' (Dspec hn).2.2.1
  have fiber (d : ℕ) (hd : d∈R N) : m (C d)/d=∑ n∈F d,(q:ℝ)/n := by
    have dp := (mem_filter.mp hd).2.1
    dsimp only [m,C]
    rw [sum_image,sum_div]
    · apply sum_congr rfl
      intro n hn
      have pos : 0<n := Nat.pos_of_ne_zero (fun e => ha (e ▸ (Dspec hn).1))
      have rn : (0:ℝ)<n := by exact_mod_cast pos
      have rd : (0:ℝ)<d := by exact_mod_cast dp
      have rm : (0:ℝ)<(n/(q*d):ℕ) := by exact_mod_cast Nat.div_pos (Nat.le_of_dvd pos (Dspec hn).2.2.1) (Nat.mul_pos qp0 dp)
      have re : (q:ℝ)*d*(n/(q*d):ℕ)=n := by exact_mod_cast factor hn
      field_simp
      linarith
    · intro n h m hm eq
      exact (factor h).symm.trans ((congrArg (q*d*·) eq).trans (factor hm))
  have total := sum_fiberwise_of_maps_to (s:=J) (t:=R N) (g:=f) (fun n hn => (spec hn).1) (fun n => (q:ℝ)/n)
  have win : ∃ d∈R N, v d < m (C d) := by
    by_contra! fail
    have le := sum_le_sum (s:=R N) (fun d hd => div_le_div_of_nonneg_right (fail d hd) (Nat.cast_nonneg d : (0:ℝ)≤d))
    change ∑ d∈R N, v d / d < b^(-(1/100:ℝ))/2 at estimate
    change b^(-(1/100:ℝ))/2≤∑ n∈J,(q:ℝ)/n at mass
    have eq : ∑ d∈R N, m (C d)/d = ∑ n∈J,(q:ℝ)/n := (sum_congr rfl fiber).trans total
    linarith
  obtain ⟨d,hd,win⟩ := win
  have dp := (mem_filter.mp hd).2.1
  have hbnd : C d ⊆ Icc 1 N := by
    intro s hs
    obtain ⟨n,h,rfl⟩ := mem_image.mp hs
    have pos : 0<n := Nat.pos_of_ne_zero (fun e => ha (e ▸ (Dspec h).1))
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pos (Dspec h).2.2.1) (Nat.mul_pos qp0 dp),
      (Nat.div_le_self _ _).trans (mem_range.mp (an (Dspec h).1)).le⟩
  have low : (d.primeFactors.card:ℝ)≤w N/110 := by
    by_contra no
    have h := divisor_sample (by omega : 0<N) hbnd
    change m (C d) ≤ 1+b at h
    exact (not_lt_of_ge h) (by simpa only [v,if_neg no] using win)
  change (if _ then _ else _) < m (C d) at win
  rw [if_pos low] at win
  have non : (F d).Nonempty := by
    by_contra! empty
    have e : C d=∅ := by simp [C,empty]
    rw [e] at win
    change a < ∑ n∈(∅:Finset ℕ), (1:ℝ)/n at win
    simp at win
    linarith
  obtain ⟨n,hnF⟩ := non
  refine ⟨q*d,C d,by change K < ((q*d:ℕ):ℝ); rw [Nat.cast_mul]; exact (Dspec hnF).2.1,dvd_mul_right _ _,win.le,?_⟩
  intro s hs
  obtain ⟨n,h,rfl⟩ := mem_image.mp hs
  have e := factor h
  have data := Dspec h
  refine ⟨by rw [e]; exact data.1,data.2.2.2.symm,?_,?_⟩
  · let s := n/(q*d)
    have spos : 0<s := (mem_Icc.mp (hbnd (mem_image.mpr ⟨n,h,rfl⟩))).1
    have qc : q.primeFactors.card=1 := by
      obtain ⟨p,k,pr,pk,eq⟩ := (isPrimePow_nat_iff q).mp qp
      rw [←eq,Nat.primeFactors_prime_pow (by omega) pr,card_singleton]
    have card : n.primeFactors.card ≤ 1+d.primeFactors.card+s.primeFactors.card := by
      rw [←e,Nat.primeFactors_mul (Nat.mul_pos qp0 dp).ne' spos.ne']
      have ab := card_union_le (q*d).primeFactors s.primeFactors
      have first := card_union_le q.primeFactors d.primeFactors
      rw [Nat.primeFactors_mul qp0.ne' dp.ne'] at ab ⊢
      omega
    have realc : (n.primeFactors.card:ℝ) ≤ 1+d.primeFactors.card+s.primeFactors.card := by exact_mod_cast card
    have lower := (reg n data.1).2.2.1
    change 99/100*w N ≤ n.primeFactors.card at lower
    change (1-2/99)*w N ≤ s.primeFactors.card
    change 1000<w N at hw
    linarith
  · have sub := Nat.primeFactors_mono (show n/(q*d)∣n from ⟨_,e.symm.trans (Nat.mul_comm _ _)⟩) (fun eq => ha (eq ▸ data.1))
    exact (show ((n/(q*d)).primeFactors.card:ℝ) ≤ n.primeFactors.card by exact_mod_cast card_le_card sub).trans (reg n data.1).2.2.2
end Rough299



/-!
The set of maximal prime powers of a positive integer determines it by multiplication. Expanding a product of factors 1 + exp(1)/q bounds the weighted reciprocal sum of the cofactor family. Taking logarithms gives the required prime-power mass.
-/
namespace OMA.FactorMass
open Finset Real
open scoped BigOperators
def powers (C : Finset ℕ) := C.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
def factors (n : ℕ) := n.primeFactors.image (fun p => p ^ n.factorization p)
lemma distinct (n : ℕ) : Set.InjOn (fun p => p ^ n.factorization p) (↑n.primeFactors) := by
  intro p hp q hq he
  have h (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p^n.factorization p).primeFactors = {p} :=
    Nat.primeFactors_prime_pow (Finsupp.mem_support_iff.mp hp) (Nat.prime_of_mem_primeFactors hp)
  have eq := congrArg Nat.primeFactors he
  exact Finset.singleton_inj.mp ((h p hp).symm.trans (eq.trans (h q hq)))
lemma recover {n : ℕ} (hn : n ≠ 0) : ∏ q ∈ factors n, q = n := by
  rw [factors,prod_image (distinct n)]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm
lemma subset_powers {C : Finset ℕ} {n : ℕ} (hn : n ∈ C) (hz : n ≠ 0) :
    factors n ⊆ powers C := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  have prime := Nat.prime_of_mem_primeFactors hp
  exact mem_biUnion.mpr ⟨n,hn,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd n p,hz⟩,
    prime.isPrimePow.pow (Finsupp.mem_support_iff.mp hp),(Nat.coprime_ordCompl prime hz).pow_left _⟩⟩
lemma exponential_bound (C : Finset ℕ) (hz : 0 ∉ C) :
    (∑ n ∈ C, exp (n.primeFactors.card : ℝ) / n) ≤
      exp (exp 1 * ∑ q ∈ powers C, (1:ℝ)/q) := by
  classical
  let w (q : ℕ) := exp 1 / (q : ℝ)
  have reconstruct (n : ℕ) (hn : n ∈ C) : ∏ q ∈ factors n, w q = exp (n.primeFactors.card : ℝ) / n := by
    have hne : n ≠ 0 := fun e => hz (e ▸ hn)
    have den : (∏ q ∈ factors n, (q : ℝ)) = n := by
      change (∏ x ∈ factors n, (Nat.castRingHom ℝ) x) = (Nat.castRingHom ℝ) n
      rw [← map_prod,recover hne]
    simp only [w,prod_div_distrib,prod_const,den]
    rw [factors,card_image_of_injOn (distinct n),← exp_nat_mul,mul_one]
  have inject : Set.InjOn factors (↑C) := by
    intro n hn m hm heq
    have h := congrArg (fun s : Finset ℕ => ∏ q ∈ s, q) heq
    simpa only [recover (show n≠0 from fun e => hz (e ▸ hn)),recover (show m≠0 from fun e => hz (e ▸ hm))] using h
  have included : C.image factors ⊆ (powers C).powerset := by
    intro s hs
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hs
    exact mem_powerset.mpr (subset_powers hn (fun e => hz (e ▸ hn)))
  calc
    _ = ∑ s ∈ C.image factors, ∏ q ∈ s, w q := by
      rw [sum_image inject]
      exact sum_congr rfl (fun n hn => (reconstruct n hn).symm)
    _ ≤ ∑ s ∈ (powers C).powerset, ∏ q ∈ s, w q :=
      sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => prod_nonneg fun _ _ => by dsimp [w]; positivity)
    _ = ∏ q ∈ powers C, (1+w q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ powers C, exp (w q) := prod_le_prod
      (fun q _ => by dsimp [w]; positivity) (fun q _ => by linarith [add_one_le_exp (w q)])
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro q hq; dsimp [w]; ring
end OMA.FactorMass

namespace OMA.FactorMass
open Filter Finset Real

theorem density : ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,
    (log N)^(-(1/99:ℝ)) ≤ ∑ n ∈ C, (1:ℝ)/n →
    (∀ m ∈ C, (1-2/99:ℝ)*log (log N) ≤ m.primeFactors.card ∧
      (m.primeFactors.card:ℝ) ≤ 2*log (log N)) →
    (35/100:ℝ)*log (log N) ≤ ∑ q ∈ powers C, (1:ℝ)/q := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  intro C hm hc
  let w := log (log N)
  have e := exp_one_lt_d9
  have hn : (4:ℝ) ≤ N := by exact_mod_cast hN
  have logbig : 1 < log N := (lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
  have hw : 0 < w := log_pos logbig
  have hz : 0 ∉ C := by
    intro h
    have := (hc 0 h).1
    simp only [Nat.primeFactors_zero,card_empty,Nat.cast_zero] at this
    change (1-2/99:ℝ)*w ≤ 0 at this
    linarith
  have bound := exponential_bound C hz
  have mass : exp (-(1/99:ℝ)*w) ≤ ∑ n ∈ C, (1:ℝ)/n := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < log N)] at hm
    simpa only [w,mul_comm] using hm
  have lower : exp ((1-3/99:ℝ)*w) ≤ exp (exp 1 * ∑ q ∈ powers C, (1:ℝ)/q) := calc
    _ = exp ((1-2/99:ℝ)*w) * exp (-(1/99:ℝ)*w) := by rw [← exp_add]; congr 1; ring
    _ ≤ exp ((1-2/99:ℝ)*w) * ∑ n ∈ C, (1:ℝ)/n := mul_le_mul_of_nonneg_left mass (exp_pos _).le
    _ ≤ ∑ n ∈ C, exp (n.primeFactors.card : ℝ)/n := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right (exp_le_exp.mpr (hc n hn).1) (by positivity)
    _ ≤ _ := bound
  have logbound := exp_le_exp.mp lower
  change 35/100*w ≤ _
  by_contra! bad
  have bad' := mul_lt_mul_of_pos_left bad (exp_pos 1)
  nlinarith only [bad', logbound, hw, mul_lt_mul_of_pos_right e hw]
end OMA.FactorMass


open Real Finset Filter
open scoped Classical Topology
namespace Wigert299
lemma divisor_bound : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ N^2 →
    (m.divisors.card:ℝ) ≤ exp ((9/5:ℝ)*log N/log (log N)) := by
  let B (N:ℕ) := log (N:ℝ)
  let W (N:ℕ) := log (B N)
  have bt : Tendsto B atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have l := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/10)).tendsto_div_nhds_zero.comp bt
  filter_upwards [l.eventually_lt_const (by norm_num : (0:ℝ)<1/10),
    bt.eventually_gt_atTop 10,(tendsto_log_atTop.comp bt).eventually_gt_atTop 1,
    eventually_gt_atTop 1] with N small hb hw hn
  intro m mp mN
  have bp : 0<B N := by linarith
  have wp : 0<W N := by exact hw.trans' zero_lt_one
  have nr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  let Y := (B N)^(9/10:ℝ)
  let S := m.primeFactors.filter fun p : ℕ => (p:ℝ)≤Y
  let T := m.primeFactors \ S
  let k (p : ℕ) := m.factorization p
  let f (p : ℕ) := log ((k p:ℝ)+1)
  let g (p : ℕ) := (k p:ℝ)*log p
  have gsum : ∑ p∈m.primeFactors,g p ≤ 2*B N := by
    have cast : (m:ℝ)=∏ p∈m.primeFactors,(p:ℝ)^(k p) := by exact_mod_cast Nat.prod_primeFactors_pow_factorization mp.ne'
    have eq : log (m:ℝ)=∑ p∈m.primeFactors,g p := by
      conv_lhs => rw [cast]
      rw [log_prod (s:=m.primeFactors) (f:=fun p : ℕ => (p:ℝ)^(k p)) (fun p hp => (pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos : (0:ℝ)<p) _).ne')]
      simp only [g,log_pow]
    rw [←eq]
    have e := log_le_log (by exact_mod_cast mp : 0<(m:ℝ)) (by exact_mod_cast mN : (m:ℝ)≤(N:ℝ)^2)
    simpa [log_pow,B] using e
  have gn (p : ℕ) (hp : p∈m.primeFactors) : 0≤g p := mul_nonneg (Nat.cast_nonneg _) (log_nonneg
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
  have l2 : 1/2≤log (2:ℝ) := by linarith [Real.log_two_gt_d9]
  have smallp (p : ℕ) (hp : p∈S) : f p≤2*W N := by
    have pr := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have lp : log 2≤log (p:ℝ) := log_le_log (by norm_num) (by exact_mod_cast pr.two_le)
    have bound := (single_le_sum gn (mem_filter.mp hp).1).trans gsum
    have kk := mul_le_mul_of_nonneg_left (l2.trans lp) (Nat.cast_nonneg (k p) : (0:ℝ)≤k p)
    change (k p:ℝ)*log p≤2*B N at bound
    have pwr : (k p:ℝ)+1≤(B N)^2 := by nlinarith [sq_nonneg (B N-5)]
    have est := log_le_log (by positivity : 0<(k p:ℝ)+1) pwr
    simpa [f,log_pow,W] using est
  have largep (p : ℕ) (hp : p∈T) : f p*W N≤(4/5:ℝ)*g p := by
    obtain ⟨pm,ns⟩ := mem_sdiff.mp hp
    have yp : Y < (p:ℝ) := lt_of_not_ge (fun le => ns (mem_filter.mpr ⟨pm,le⟩))
    have lp := log_lt_log (rpow_pos_of_pos bp (9/10:ℝ)) yp
    rw [log_rpow bp] at lp
    change (9/10:ℝ)*W N < log p at lp
    have ke : k p+1≤2^k p := Nat.lt_two_pow_self
    have le := log_le_log (by positivity : 0<(k p:ℝ)+1) (by exact_mod_cast ke : (k p:ℝ)+1≤(2:ℝ)^k p)
    rw [log_pow] at le
    have l2' : log 2≤(7/10:ℝ) := by linarith [Real.log_two_lt_d9]
    have c := mul_le_mul_of_nonneg_left l2' (Nat.cast_nonneg (k p) : (0:ℝ)≤k p)
    have d := mul_le_mul_of_nonneg_left lp.le (Nat.cast_nonneg (k p) : (0:ℝ)≤k p)
    have e := mul_le_mul_of_nonneg_right (le.trans c) wp.le
    dsimp [f,g]
    nlinarith only [d,e,mul_nonneg (Nat.cast_nonneg (k p) : (0:ℝ)≤k p) wp.le]
  have sc : (S.card:ℝ) ≤ Y := by
    have sub : S⊆Icc 1 ⌊Y⌋₊ := by
      intro p hp
      obtain ⟨pm,le⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors pm).one_le,Nat.le_floor le⟩
    have e : S.card≤⌊Y⌋₊ := by simpa using card_le_card sub
    exact (show (S.card:ℝ)≤⌊Y⌋₊ by exact_mod_cast e).trans (Nat.floor_le (rpow_pos_of_pos bp _).le)
  have upperS : (∑ p∈S, f p)*W N ≤ (1/5:ℝ)*B N := by
    have h := sum_le_sum smallp
    simp only [sum_const,nsmul_eq_mul] at h
    have m := mul_le_mul_of_nonneg_right (h.trans (mul_le_mul_of_nonneg_right sc (by positivity))) wp.le
    change (log (B N))^(2:ℝ)/(B N)^(1/10:ℝ)<1/10 at small
    rw [rpow_two,div_lt_iff₀ (rpow_pos_of_pos bp _)] at small
    change W N^2<_ at small
    have rc := mul_lt_mul_of_pos_right small (rpow_pos_of_pos bp (9/10:ℝ))
    have eq : (B N)^(1/10:ℝ)*Y=B N := by rw [←rpow_add bp]; norm_num
    change W N^2*Y < 1/10*(B N)^(1/10:ℝ)*Y at rc
    rw [mul_assoc,eq] at rc
    nlinarith only [rc,m]
  have upperT : (∑ p∈T,f p)*W N≤(4/5:ℝ)*(2*B N) := by
    rw [sum_mul]
    apply (sum_le_sum largep).trans
    rw [←mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (sum_le_sum_of_subset_of_nonneg (sdiff_subset : T⊆m.primeFactors) (fun p hp _ => gn p hp)).trans gsum
  have sp := sum_sdiff (f:=f) (show S⊆m.primeFactors from filter_subset _ _)
  change (∑ p∈T,f p)+(∑ p∈S,f p)=_ at sp
  have coeff : (∑ p∈m.primeFactors, f p) ≤ (9/5:ℝ)*B N/W N := by
    rw [le_div_iff₀ wp,←sp,add_mul]
    linarith
  have card : (m.divisors.card:ℝ)=∏ p∈m.primeFactors, ((k p:ℝ)+1) := by exact_mod_cast Nat.card_divisors mp.ne'
  have e : 0<(m.divisors.card:ℝ) := by rw [card]; positivity
  apply (log_le_iff_le_exp e).mp
  rw [card,log_prod (fun p _ => by positivity)]
  exact coeff
end Wigert299

open Filter Finset Real
open scoped Classical Topology
namespace TinyOverlap299
noncomputable abbrev mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
lemma pp_bound (m : ℕ) (hm : 0 < m) (P : Finset ℕ) (hP : ∀ q ∈ P, IsPrimePow q ∧ q∣m) :
    mass P ≤ 2*mass m.primeFactors := by
  let U := m.primeFactors ×ˢ range m
  let f (p : ℕ×ℕ) := p.1^(p.2+1)
  have sub : P⊆U.image f := by
    intro q hq
    obtain ⟨pp,dvd⟩ := hP q hq
    obtain ⟨p,hp,k,hk,pr,hk0,eq⟩ := (isPrimePow_nat_iff_bounded q).mp pp
    have pd := (dvd_pow_self p hk0.ne').trans (eq ▸ dvd : p^k ∣ m)
    have le := Nat.le_of_dvd hm dvd
    cases k with
    | zero => omega
    | succ j => exact mem_image.mpr ⟨(p,j),mem_product.mpr ⟨Nat.mem_primeFactors.mpr ⟨pr,pd,hm.ne'⟩,
                    mem_range.mpr (by omega)⟩,eq⟩
  calc _ ≤ ∑ q ∈ U.image f, (1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
       _ ≤ ∑ a ∈ U, (1:ℝ)/(f a) := sum_image_le_of_nonneg (fun _ _ => by positivity)
       _ = ∑ p ∈ m.primeFactors, ∑ k ∈ range m, (1:ℝ)/(p:ℝ)^(k+1) := by simp [U,f,sum_product]
       _ ≤ ∑ p ∈ m.primeFactors, 2/(p:ℝ) := sum_le_sum fun p hp =>
          Param299.geom p (Nat.prime_of_mem_primeFactors hp).two_le m
       _ = _ := by simp only [mass,mul_sum]; congr 1; ext; ring
lemma card_le_log {s : ℕ} (hs : 0 < s) :
    (s.primeFactors.card : ℝ) ≤ log s / log 2 := by
  have h1 : 2 ^ s.primeFactors.card ≤ ∏ p ∈ s.primeFactors, p :=
    pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 := Nat.le_of_dvd hs (Nat.prod_primeFactors_dvd s)
  have h3 : ((2 : ℝ) ^ s.primeFactors.card) ≤ s := by exact_mod_cast h1.trans h2
  rw [le_div_iff₀ (log_pos one_lt_two)]
  have := log_le_log (by positivity) h3
  rwa [log_pow] at this
lemma overlap : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m≤N → ∀ P : Finset ℕ,
    (∀ q ∈ P, IsPrimePow q ∧ q∣m) → mass P < (1/500:ℝ)*Param299.w N := by
  obtain ⟨b,hb⟩ := Mass377.realMertens
  have hg := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp Param299.wtop
  filter_upwards [(hb.comp Mass377.logTop).eventually_lt_const (show b<b+1 by linarith),
    hg.eventually_lt_const (by norm_num : (0:ℝ)<1/10000),
    Param299.wtop.eventually_gt_atTop (10000*(|b|+1+1/log 2)),
    Mass377.logTop.eventually_gt_atTop 1] with N hprime hratio hw hN
  intro m hm hmN P hP
  let X := log (N:ℝ)
  let Q := m.primeFactors.filter fun p : ℕ => (p:ℝ)≤X
  let R := m.primeFactors \ Q
  have xp : 0<X := by dsimp [X]; linarith
  have p2 : 0<log 2 := log_pos one_lt_two
  have wpos : 0<Param299.w N := by linarith [abs_nonneg b,one_div_pos.mpr p2]
  change Mass377.S X - log (Param299.w N) < b+1 at hprime
  simp only [Function.comp_apply,pow_one,one_mul,add_zero] at hratio
  have small := (div_lt_iff₀ wpos).mp hratio
  have sub : Q ⊆ Nat.primesLE ⌊X⌋₊ := by
    intro p hp
    obtain ⟨hp,le⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor le,Nat.prime_of_mem_primeFactors hp⟩
  have lo : mass Q ≤ Mass377.S X := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  have hi : mass R ≤ 1/log 2 := by
    have hh : mass R ≤ (R.card:ℝ)*(1/X) := by
      simpa [mass,nsmul_eq_mul] using sum_le_card_nsmul R (fun p : ℕ => (1:ℝ)/p) (1/X) (by
        intro p hp
        obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
        exact one_div_le_one_div_of_le xp (le_of_not_ge (fun le => h2 (mem_filter.mpr ⟨h1,le⟩))))
    have size : (R.card:ℝ)≤ m.primeFactors.card := by exact_mod_cast card_le_card (sdiff_subset : R⊆m.primeFactors)
    have logle : log (m:ℝ) ≤ X := log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN)
    have cm := size.trans ((card_le_log hm).trans (div_le_div_of_nonneg_right logle p2.le))
    calc mass R ≤ (R.card:ℝ)*(1/X) := hh
         _ ≤ (X/log 2)*(1/X) := mul_le_mul_of_nonneg_right cm (by positivity)
         _ = _ := by field_simp
  have eq := sum_sdiff (filter_subset (fun p : ℕ => (p:ℝ)≤X) m.primeFactors) (f:=fun p : ℕ => (1:ℝ)/p)
  change mass R + mass Q = mass m.primeFactors at eq
  have pp := pp_bound m hm P hP
  linarith [le_abs_self b]
end TinyOverlap299

open Filter Real Finset
open scoped Classical Topology
namespace FirstForce299
open Bloom298.Setup
noncomputable abbrev I (t K : ℝ) := Icc (⌈t-K/2⌉:ℤ) ⌊t+K/2⌋
def hits (J : Finset ℤ) (n : ℕ) := ∃ x∈J,(n:ℤ)∣x
noncomputable abbrev pix (Q : Finset ℕ) (x : ℤ) := Q.filter fun q : ℕ => (q:ℤ)∣x
def regular (N n : ℕ) : Prop := Regular N n
noncomputable abbrev E (N : ℕ) (A U : Finset ℕ) := (powers A).filter fun q =>
  e N/2 ≤ ∑ n∈part U q,(q:ℝ)/n
lemma distance (x y : ℤ) {t K : ℝ} (hx : x∈I t K) (hy : y∈I t K) : |(x:ℝ)-y|≤K := by
  have bounds (j : ℤ) (hj : j∈I t K) : t-K/2≤j ∧ (j:ℝ)≤t+K/2 :=
    ⟨Int.ceil_le.mp (mem_Icc.mp hj).1,Int.le_floor.mp (mem_Icc.mp hj).2⟩
  obtain ⟨xl,xu⟩ := bounds x hx
  obtain ⟨yl,yu⟩ := bounds y hy
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma heavy : ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (t : ℝ), 0∉A → A⊆range N →
    (∀ n∈A, regular N n) → let J := I t (K N)
    let U := A.filter (hits J)
    ∀ q∈E N A U, ∃ x∈J,(q:ℤ)∣x ∧ (35/100:ℝ)*w N ≤ mass (pix (powers A) x) := by
  filter_upwards [Rough299.result, OMA.FactorMass.density,Mass377.logTop.eventually_gt_atTop 0] with N co en hlog
  intro A t a0 aN reg J U q qe
  have ua : U⊆A := filter_subset _ _
  have pp := (power_mem (mem_filter.mp qe).1).1
  have bulk := (mem_filter.mp qe).2
  let F (x : ℤ) := pix (powers A) x
  have dist (x y : ℤ) (hx : x∈J) (hy : y∈J) := distance x y hx hy
  obtain ⟨D,C,big,qd,cm,cf⟩ := co U q (fun h => a0 (ua h)) (ua.trans aN)
    (fun n hn => reg n (ua hn)) pp bulk
  have cd := en C cm (fun m hm => (cf m hm).2.2)
  obtain ⟨m,hm⟩ := nonempty_of_ne_empty (s:=C) (fun eq => by
    have p := rpow_pos_of_pos hlog (-(1/99:ℝ))
    rw [eq] at cm
    exact p.not_ge (by simpa only [mass,sum_empty] using cm))
  obtain ⟨x,hx,dx⟩ := (mem_filter.mp (cf m hm).1).2
  have Dvd (m : ℕ) {y : ℤ} (hy : ((D*m:ℕ):ℤ)∣y) : (D:ℤ)∣y :=
    (show (D:ℤ) ∣ ((D*m:ℕ):ℤ) by exact_mod_cast (dvd_mul_right D m)).trans hy
  have uniq (y : ℤ) (hy : y∈J) (dy : (D:ℤ)∣y) : x=y := by
    have h : |x-y|<(D:ℤ) := by exact_mod_cast (dist x y hx hy).trans_lt big
    exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (dvd_sub (Dvd m dx) dy) h)
  have inc : powers C ⊆ F x := by
    intro r hr
    obtain ⟨pr,j,hj,j0,rj,cp⟩ := power_mem hr
    obtain ⟨inU,cop,_⟩ := cf j hj
    obtain ⟨inA,y,hy,divy⟩ := mem_filter.mp inU
    have rDj := rj.trans (dvd_mul_left j D)
    have prA : r ∈ powers A := by
      apply mem_biUnion.mpr
      refine ⟨D*j,inA,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨rDj,fun eq => a0 (eq ▸ inA)⟩,pr,?_⟩⟩
      rw [Nat.mul_div_assoc D rj]
      exact (cop.coprime_dvd_left rj).mul_right cp
    refine mem_filter.mpr ⟨prA,?_⟩
    rw [uniq y hy (Dvd j divy)]
    exact (show (r:ℤ) ∣ ((D*j:ℕ):ℤ) by exact_mod_cast rDj).trans divy
  exact ⟨x,hx,(show (q:ℤ)∣D by exact_mod_cast qd).trans (Dvd m dx),cd.trans
    (sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => by positivity))⟩
end FirstForce299

open Real Finset
open scoped Classical
namespace Trapped299
lemma product_dvd {n : ℕ} {x y : ℤ} (nz : 0<n)
    (split : ∀ p∈n.primeFactors, let q := p^n.factorization p
      (q:ℤ)∣x ∨ (q:ℤ)∣y) : (n:ℤ)∣x*y := by
  apply Int.natAbs_dvd_natAbs.mp
  rw [Int.natAbs_natCast,Int.natAbs_mul]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k pr pk
  by_cases zero : k=0
  · simp [zero]
  have pd := (dvd_pow_self p zero).trans pk
  have h := split p (Nat.mem_primeFactors.mpr ⟨pr,pd,nz.ne'⟩)
  have kf := (pr.pow_dvd_iff_le_factorization nz.ne').mp pk
  apply (pow_dvd_pow p kf).trans
  rcases h with hx|hy
  · exact dvd_mul_of_dvd_left (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hx) _
  · exact dvd_mul_of_dvd_right (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hy) _
lemma trapped (V : Finset ℕ) (J : Finset ℤ) {x y : ℤ} {N : ℕ} {C : ℝ} (cp : 0≤C)
    (width : ∀ h∈J,(x-h).natAbs≤N ∧ (y-h).natAbs≤N)
    (divs : ∀ m : ℕ, 0 < m → m≤N^2 → (m.divisors.card:ℝ)≤C)
    (membership : ∀ n∈V, (n:ℤ)∣x*y ∧ ¬(n:ℤ)∣x ∧ ¬(n:ℤ)∣y ∧ ∃ h∈J,(n:ℤ)∣h) :
    (V.card:ℝ)≤J.card*C := by
  let m (h : ℤ) := (x-h).natAbs*(y-h).natAbs
  have sub : V ⊆ J.biUnion (fun h => (m h).divisors) := by
    intro n hn
    obtain ⟨prod,xn,yn,h,hJ,hd⟩ := membership n hn
    have div : (n:ℤ) ∣ (x-h)*(y-h) := by
      rw [show (x-h)*(y-h)=x*y-h*(x+y-h) by ring]
      exact dvd_sub prod (hd.trans (dvd_mul_right _ _))
    have nz : m h≠0 := by
      apply Nat.mul_ne_zero
      · apply Int.natAbs_ne_zero.mpr
        exact sub_ne_zero.mpr (fun e => xn (e ▸ hd))
      · apply Int.natAbs_ne_zero.mpr
        exact sub_ne_zero.mpr (fun e => yn (e ▸ hd))
    exact mem_biUnion.mpr ⟨h,hJ,Nat.mem_divisors.mpr ⟨by simpa only [m,Int.natAbs_natCast,Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr div,nz⟩⟩
  have count := (card_le_card sub).trans card_biUnion_le
  calc _ ≤ ∑ h∈J, ((m h).divisors.card:ℝ) := by exact_mod_cast count
       _ ≤ ∑ _h∈J, C := by
         apply sum_le_sum
         intro h hJ
         by_cases z : m h=0
         · simpa [z] using cp
         exact divs _ (Nat.pos_of_ne_zero z) (by simpa [m,pow_two] using Nat.mul_le_mul (width h hJ).1 (width h hJ).2)
       _ = _ := by simp
end Trapped299

open Real Filter Finset
open scoped Classical Topology
namespace FirstForce299
open Bloom298.Setup
noncomputable abbrev H (N:ℕ) := exp ((9/5:ℝ)*log N/w N)
lemma qmass : ∀ᶠ N : ℕ in atTop, ∀ Q : Finset ℕ,
    (∀ q∈Q, IsPrimePow q ∧ q≤N) → mass Q≤501/500*w N := by
  obtain ⟨b,hb⟩ := Mass377.natMertens
  obtain ⟨C,hC⟩ := Rough299.nonsimple
  filter_upwards [hb.eventually_lt_const (show b<b+1 by linarith),Param299.wtop.eventually_gt_atTop (500*(b+1+C))] with N pr big
  intro Q qQ
  let P := Q.filter Nat.Prime
  have sub : P ⊆ Nat.primesLE N := fun q hq => Nat.mem_primesLE.mpr ⟨(qQ q (mem_filter.mp hq).1).2,(mem_filter.mp hq).2⟩
  have p := sum_le_sum_of_subset_of_nonneg (f:=fun q : ℕ => (1:ℝ)/q) sub (fun _ _ _ => by positivity)
  have c := hC N (Q \ P) (fun q hq => ⟨(qQ q (mem_sdiff.mp hq).1).1,
    fun pp => (mem_sdiff.mp hq).2 (mem_filter.mpr ⟨(mem_sdiff.mp hq).1,pp⟩),(qQ q (mem_sdiff.mp hq).1).2⟩)
  have eq := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) (show P⊆Q from filter_subset _ _)
  dsimp only [mass,w,Param299.w] at *
  linarith
lemma small_errors (z : ℕ) : ∀ᶠ N : ℕ in atTop,
    0<log (N:ℝ) ∧ 4≤w N ∧ 1≤K N ∧ K N≤N ∧ 0<M N ∧
    1/M N ≤ 1/(z+1:ℝ) ∧
    1/log N + (e N/2)*(501/500*w N) + 2*K N*H N/M N < (1/(z+1:ℝ))/3 := by
  have et := (tendsto_exp_div_pow_atTop 1).comp Param299.wtop
  have ht : Tendsto (fun N : ℕ => log N/w N) atTop atTop := by
    apply et.congr'
    filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hp
    simp [w,Param299.w,hp,exp_log]
  have neg := tendsto_exp_neg_atTop_nhds_zero.comp (ht.const_mul_atTop (by norm_num : (0:ℝ)<1/5))
  have short : Tendsto (fun N : ℕ => 2*K N*H N/M N) atTop (𝓝 0) := by
    have f := neg.const_mul 2
    rw [mul_zero] at f
    apply f.congr'
    filter_upwards [eventually_gt_atTop 0] with N hn
    have np : (0:ℝ)<N := by exact_mod_cast hn
    have mp : 0<M N := rpow_pos_of_pos np _
    dsimp only [Function.comp_apply,K,H]
    rw [rpow_def_of_pos np]
    have eq : -(1/5*(log (N:ℝ)/w N)) = log N*(-2/w N)+(9/5:ℝ)*log N/w N := by ring
    rw [eq,exp_add]
    field_simp
  have lo : Tendsto (fun N : ℕ => 1/log (N:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Mass377.logTop
  have mid : Tendsto (fun N : ℕ => e N/2*(501/500*w N)) atTop (𝓝 0) := by
    have t := Param299.eMass.const_mul (501/1000:ℝ)
    rw [mul_zero] at t
    apply t.congr (fun N => ?_)
    change 501/1000*(e N*w N)=_
    ring
  have err := (lo.add mid).add short
  simp only [zero_add] at err
  have mt : Tendsto (fun N => 1/M N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Param299.Mtop
  filter_upwards [eventually_ge_atTop 1,Mass377.logTop.eventually_gt_atTop 0,
    Param299.wtop.eventually_ge_atTop 4,mt.eventually_lt_const (show 0<1/(z+1:ℝ) by positivity),
    err.eventually_lt_const (show 0<(1/(z+1:ℝ))/3 by positivity)] with N hn hb hw hM small
  have nr : (1:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have keq : K N = (N:ℝ)^(1-3/w N) := by rw [K,M,←rpow_add np]; congr 1; ring
  change 4≤w N at hw
  have wp : 0<w N := by linarith
  have lower : 1≤K N := by rw [keq]; apply one_le_rpow nr; have := (div_le_one wp).mpr (by linarith : 3≤w N); linarith
  have upper : K N≤N := by
    rw [keq]; conv_rhs => rw [← rpow_one (N:ℝ)]
    exact rpow_le_rpow_of_exponent_le nr (by linarith [div_nonneg (by norm_num : (0:ℝ)≤3) wp.le])
  exact ⟨hb,hw,lower,upper,rpow_pos_of_pos np _,hM.le,small⟩
end FirstForce299

open Real Finset Filter
open scoped Classical Topology
namespace FirstForce299
open Bloom298.Setup
lemma mono_mass {A B : Finset ℕ} (h : A⊆B) : mass A≤ mass B :=
  sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => by positivity)
lemma union_mass (A B : Finset ℕ) : mass (A∪B) ≤ mass A+mass B := by
  have e : mass (A∪B)+mass (A∩B)=mass A+mass B := sum_union_inter
  have pos : 0≤ mass (A∩B) := sum_nonneg (fun _ _ => by positivity)
  linarith
lemma biMass {α : Type*} (s : Finset α) (f : α→Finset ℕ) :
    mass (s.biUnion f) ≤ ∑ a∈s,mass (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | insert a s ha ih =>
    rw [biUnion_insert,sum_insert ha]
    exact (union_mass _ _).trans (add_le_add_right ih _)
lemma pair_overlap : ∀ᶠ N : ℕ in atTop, ∀ (Q : Finset ℕ), (∀ q∈Q, IsPrimePow q) →
    ∀ x y : ℤ, x≠y → |(x:ℝ)-y|≤N → mass (pix Q x ∩ pix Q y)<w N/500 := by
  filter_upwards [TinyOverlap299.overlap] with N ov
  intro Q qQ x y ne dist
  have nz : 0<(x-y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr ne)
  have le : (x-y).natAbs≤N := by exact_mod_cast (show ((x-y).natAbs:ℝ)≤N by simpa using dist)
  have e := ov (x-y).natAbs nz le (pix Q x∩pix Q y) (by
    intro q hq
    obtain ⟨a,b⟩ := mem_inter.mp hq
    have dvd := dvd_sub (mem_filter.mp a).2 (mem_filter.mp b).2
    exact ⟨qQ q (mem_filter.mp a).1,by simpa using (Int.natAbs_dvd_natAbs.mpr dvd)⟩)
  change mass _ < (1/500:ℝ)*w N at e
  linarith
lemma two_heavy {Q : Finset ℕ} {W : ℝ} {f : ℤ→Finset ℕ} (wp : 0<W)
    (J : Finset ℤ) (cap : mass Q≤501/500*W) (sub : ∀ z, f z⊆Q)
    (overlapBound : ∀ x∈J, ∀ y∈J, x≠y → mass (f x∩f y) < W/500)
    {x y : ℤ} (xJ : x∈J) (yJ : y∈J) (xy : x≠y)
    (xh : 35/100*W≤ mass (f x)) (yh : 35/100*W≤ mass (f y)) :
    mass (f x)≤2/3*W ∧ mass (f y)≤2/3*W ∧
      ∀ z∈J, 35/100*W≤ mass (f z) → z=x ∨ z=y := by
  have ux := mono_mass (union_subset (sub x) (sub y))
  have e : mass (f x∪f y)+mass (f x∩f y)=mass (f x)+mass (f y) := sum_union_inter
  have ov := overlapBound x xJ y yJ xy
  refine ⟨by linarith,by linarith,?_⟩
  intro z zJ zh
  by_contra! both
  have a := overlapBound z zJ x xJ both.1
  have b := overlapBound z zJ y yJ both.2
  have e2 : mass (f z ∪ (f x∪f y))+mass (f z ∩ (f x∪f y))=mass (f z)+mass (f x∪f y) := sum_union_inter
  have t := mono_mass (union_subset (sub z) (union_subset (sub x) (sub y)))
  rw [inter_union_distrib_left] at e2
  linarith [union_mass (f z∩f x) (f z∩f y)]
end FirstForce299

open Real Finset
open scoped Classical
namespace FirstForce299
open Bloom298.Setup
lemma card_interval {t K : ℝ} (hK : 1≤K) : ((I t K).card:ℝ)≤2*K := by
  have ne : ⌈t-K/2⌉ ≤ ⌊t+K/2⌋ := by
    apply Int.le_floor.mpr
    linarith [Int.ceil_lt_add_one (t-K/2)]
  rw [I,Int.card_Icc]
  have p : 0≤⌊t+K/2⌋+1-⌈t-K/2⌉ := by omega
  rw [←Int.cast_natCast (R:=ℝ),Int.toNat_of_nonneg p]
  push_cast
  linarith [Int.le_ceil (t-K/2),Int.floor_le (t+K/2)]
lemma three_parts {N : ℕ} {A : Finset ℕ} (t : ℝ) (x y : ℤ)
    (hK : 1≤K N) (kN : K N≤N) (mp : 0<M N) (bp : 0<log (N:ℝ))
    (ha : 0∉A) (reg : ∀ n∈A, regular N n)
    (xJ : x∈I t (K N)) (yJ : y∈I t (K N))
    (smooth : ∀ m : ℕ, 0 < m → m≤N^2 → (m.divisors.card:ℝ)≤H N)
    (cap : mass (powers A)≤501/500*w N)
    (bad : ((A.filter fun n => ¬hits (I t (K N)) n).card:ℝ) < M N/log N)
    (qsplit : ∀ q∈E N A (A.filter (hits (I t (K N)))), (q:ℤ)∣x ∨ (q:ℤ)∣y) :
    mass A ≤ mass (A.filter fun n : ℕ => (n:ℤ)∣x)+mass (A.filter fun n : ℕ => (n:ℤ)∣y)+
      (1/log N+(e N/2)*(501/500*w N)+2*K N*H N/M N) := by
  classical
  let J := I t (K N)
  let U := A.filter (hits J)
  let O := A.filter (fun n => ¬hits J n)
  let X := A.filter fun n : ℕ => (n:ℤ)∣x
  let Y := A.filter fun n : ℕ => (n:ℤ)∣y
  let Q := powers A
  let D := Q \ E N A U
  let B := D.biUnion (part U)
  let V := (U \ B).filter fun n : ℕ => ¬(n:ℤ)∣x ∧ ¬(n:ℤ)∣y
  have ep : 0<e N := rpow_pos_of_pos bp _
  have ua : U⊆A := filter_subset _ _
  have ua' : V⊆U := (filter_subset _ _).trans sdiff_subset
  have boundCard (s : Finset ℕ) (hs : s⊆A) : mass s ≤ s.card/M N := by
    calc _ ≤ ∑ _n∈s, 1/M N := sum_le_sum fun n hn => one_div_le_one_div_of_le mp (reg n (hs hn)).1
         _ = _ := by simp [div_eq_mul_inv]
  have outside : mass O ≤ 1/log N := by
    have eq := (div_lt_div_iff_of_pos_right mp).mpr bad
    calc _ ≤ O.card/M N := boundCard _ (filter_subset _ _)
         _ ≤ _ := by
           apply eq.le.trans
           have e : (M N/log N)/M N=1/log N := by field_simp
           exact e.le
  have low : mass B ≤ (e N/2)*(501/500*w N) := by
    apply (biMass D (part U)).trans
    calc _ ≤ ∑ q∈D, (e N/2)*((1:ℝ)/q) := by
           apply sum_le_sum
           intro q hq
           obtain ⟨qQ,no⟩ := mem_sdiff.mp hq
           have p : (0:ℝ)<q := by exact_mod_cast (power_mem qQ).1.pos
           have le : ∑ n∈part U q,(q:ℝ)/n < e N/2 := lt_of_not_ge (fun le => no (mem_filter.mpr ⟨qQ,le⟩))
           have eq : ∑ n∈part U q,(q:ℝ)/n = (q:ℝ)*mass (part U q) := by
             rw [mass,mul_sum]; apply sum_congr rfl; intro n hn; ring
           rw [eq] at le
           rw [mul_one_div,le_div_iff₀ p,mul_comm]
           exact le.le
         _ ≤ _ := by
           rw [←mul_sum]
           exact mul_le_mul_of_nonneg_left ((mono_mass (sdiff_subset : D⊆Q)).trans cap) (by positivity)
  have width (h : ℤ) (hh : h∈J) : (x-h).natAbs≤N ∧ (y-h).natAbs≤N := by
    constructor
    · exact_mod_cast (show ((x-h).natAbs:ℝ)≤N by simpa using (distance x h xJ hh).trans kN)
    · exact_mod_cast (show ((y-h).natAbs:ℝ)≤N by simpa using (distance y h yJ hh).trans kN)
  have membership (n : ℕ) (hn : n∈V) :
      (n:ℤ)∣x*y ∧ ¬(n:ℤ)∣x ∧ ¬(n:ℤ)∣y ∧ ∃ h∈J,(n:ℤ)∣h := by
    obtain ⟨inU,notB⟩ := mem_sdiff.mp (mem_filter.mp hn).1
    have nA := ua inU
    have nz : n≠0 := fun e => ha (e ▸ nA)
    refine ⟨Trapped299.product_dvd (Nat.pos_of_ne_zero nz) ?_,(mem_filter.mp hn).2.1,(mem_filter.mp hn).2.2,(mem_filter.mp inU).2⟩
    intro p pm
    let q := p^n.factorization p
    have pr := Nat.prime_of_mem_primeFactors pm
    have dv : q∣n := Nat.ordProj_dvd n p
    have cp : Nat.Coprime q (n/q) := (Nat.coprime_ordCompl pr nz).pow_left _
    have qQ : q∈Q := mem_biUnion.mpr ⟨n,nA,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dv,nz⟩,
      pr.isPrimePow.pow (Finsupp.mem_support_iff.mp pm),cp⟩⟩
    apply qsplit q
    by_contra no
    exact notB (mem_biUnion.mpr ⟨q,mem_sdiff.mpr ⟨qQ,no⟩,mem_filter.mpr ⟨inU,dv,cp⟩⟩)
  have trapped := Trapped299.trapped V J (exp_pos _).le width smooth membership
  have massV : mass V≤2*K N*H N/M N := by
    exact (boundCard V (ua'.trans ua)).trans (div_le_div_of_nonneg_right
      (trapped.trans (mul_le_mul_of_nonneg_right (card_interval (t:=t) hK) (exp_pos _).le)) mp.le)
  have sub : A⊆(((X∪Y)∪O)∪B)∪V := by
    intro n hn
    by_cases hx : (n:ℤ)∣x
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,hx⟩))))
    by_cases hy : (n:ℤ)∣y
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,hy⟩))))
    by_cases hit : hits J n
    · by_cases nb : n∈B
      · exact mem_union_left _ (mem_union_right _ nb)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨hn,hit⟩,nb⟩,hx,hy⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,hit⟩)))
  change mass A≤ mass X+mass Y+_
  linarith [mono_mass sub,union_mass X Y,union_mass (X∪Y) O,union_mass (X∪Y∪O) B,union_mass (X∪Y∪O∪B) V]
end FirstForce299

open Real Filter Finset
open scoped Classical Topology
namespace FirstForce299
open Bloom298.Setup
lemma rare_member {N : ℕ} {A : Finset ℕ} {t : ℝ} (q : ℕ) (hq : q∈powers A)
    (hp : 0<log (N:ℝ)) (mp : 0<M N) (reg : ∀ n∈A,regular N n)
    (bal : e N ≤ ∑ n∈part A q, (q:ℝ)/n)
    (rare : ((((part A q).filter (fun n => ¬hits (I t (K N)) n)).card):ℝ) < L N/q) :
    q∈E N A (A.filter (hits (I t (K N)))) := by
  let J := I t (K N)
  let B := (part A q).filter fun n => ¬hits J n
  have qp : (0:ℝ)<q := by exact_mod_cast (power_mem hq).1.pos
  have small : (∑ n∈B,(q:ℝ)/n) ≤ e N/2 := by
    have rem := sum_le_card_nsmul B (fun n : ℕ => (q:ℝ)/n) ((q:ℝ)/M N) (by
      intro n hn
      exact div_le_div_of_nonneg_left qp.le mp (reg n (mem_filter.mp (mem_filter.mp hn).1).1).1)
    rw [nsmul_eq_mul] at rem
    calc _ ≤ (B.card:ℝ)*((q:ℝ)/M N) := rem
         _ ≤ (L N/q)*((q:ℝ)/M N) := mul_le_mul_of_nonneg_right rare.le (by positivity)
         _ = _ := by
           rw [L,e,rpow_neg hp.le]
           field_simp [mp.ne',qp.ne',(rpow_pos_of_pos hp (1/100:ℝ)).ne']
  have spl := sum_filter_add_sum_filter_not (s:=part A q) (f:=fun n : ℕ => (q:ℝ)/n) (hits J)
  have eq : (part A q).filter (hits J)=part (A.filter (hits J)) q := by ext n; simp [part,and_comm,and_left_comm,and_assoc]
  rw [eq] at spl
  change _+(∑ n∈B,(q:ℝ)/n)=_ at spl
  exact mem_filter.mpr ⟨hq,by linarith⟩
lemma result : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H2 := by
  classical
  intro z
  filter_upwards [small_errors z,qmass,pair_overlap,heavy,Wigert299.divisor_bound] with N par qcap pairs heav divider
  obtain ⟨bp,wp,k1,kN,mp,mz,errs⟩ := par
  intro A d dp dz az an reg bal
  let Q := powers A
  have qQ (q : ℕ) (hq : q∈Q) : IsPrimePow q ∧ q≤N := by
    obtain ⟨p,n,hn,nz,dv,_⟩ := power_mem hq
    exact ⟨p,(Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dv).trans (mem_range.mp (an hn)).le⟩
  have cap := qcap Q qQ
  have dr : (0:ℝ)<d := by exact_mod_cast dp
  have lower : 1/(z+1:ℝ)≤ mass A := by
    have le : 1/(z+1:ℝ)≤1/(d:ℝ) := one_div_le_one_div_of_le dr (by exact_mod_cast (Nat.le_succ_of_le dz))
    have b := bal.2.1
    change 2/(d:ℝ)-1/M N≤ mass A at b
    rw [show (2:ℝ)/d=2*(1/d) by ring] at b
    linarith
  by_cases witness : ∃ B ⊆ A, mass A ≤ 3*mass B ∧ mass (powers B) ≤ (2/3:ℝ)*w N
  · exact Or.inr witness
  left
  intro t
  let J := I t (K N)
  let U := A.filter (hits J)
  let R := E N A U
  let X (x : ℤ) := A.filter fun n : ℕ => (n:ℤ)∣x
  let f := pix Q
  by_cases wide : M N/log N ≤ ((A.filter fun n => ¬hits J n).card:ℝ)
  · exact Or.inl (by simpa [hits,J,I,K,M,w,not_exists] using wide)
  right
  have ine : J.Nonempty := by
    refine ⟨⌈t-K N/2⌉,mem_Icc.mpr ⟨le_rfl,Int.le_floor.mpr ?_⟩⟩
    linarith [Int.ceil_lt_add_one (t-K N/2)]
  have rare (q : ℕ) (hq : q∈Q)
      (h : ((((part A q).filter fun n : ℕ => ∀ x∈J,¬(n:ℤ)∣x).card):ℝ)<L N/q) : q∈R :=
    rare_member q hq bp mp reg (bal.2.2.2 q hq) (by simpa [hits,J,I,not_exists] using h)
  have per (q : ℕ) (hq : q∈R) : ∃ x∈J,(q:ℤ)∣x ∧ (35/100:ℝ)*w N≤ mass (f x) := heav A t az an reg q hq
  let pick (q : ℕ) := if hq : q∈R then (per q hq).choose else 0
  have chosen (q : ℕ) (hq : q∈R) : pick q ∈ J ∧ (q:ℤ)∣pick q ∧ (35/100:ℝ)*w N≤ mass (f (pick q)) := by
    simpa only [pick,dif_pos hq] using (per q hq).choose_spec
  by_cases ex : R.Nonempty
  · obtain ⟨q,qe⟩ := ex
    let x := pick q
    have hx := chosen q qe
    refine ⟨x,hx.1,?_⟩
    intro r rq rr
    have re := rare r rq rr
    have hy := chosen r re
    let y := pick r
    by_contra no
    have xy : x≠y := fun eq => no (eq ▸ hy.2.1)
    have overB (a : ℤ) (aJ : a∈J) (b : ℤ) (bJ : b∈J) (ab : a≠b) : mass (f a∩f b)<w N/500 :=
      pairs Q (fun q h => (qQ q h).1) a b ab ((distance a b aJ bJ).trans kN)
    obtain ⟨cx,cy,all⟩ := two_heavy (Q:=Q) (f:=f) (by linarith : 0<w N) J cap (fun _ => filter_subset _ _)
       overB hx.1 hy.1 xy hx.2.2 hy.2.2
    have ps : ∀ p∈R,(p:ℤ)∣x ∨ (p:ℤ)∣y := by
      intro p pe
      have c := chosen p pe
      rcases all (pick p) c.1 c.2.2 with h|h
      · exact Or.inl (by change (p:ℤ)∣pick q; rw [←h]; exact c.2.1)
      · exact Or.inr (by change (p:ℤ)∣pick r; rw [←h]; exact c.2.1)
    have part := three_parts t x y k1 kN mp bp az reg hx.1 hy.1 divider cap (lt_of_not_ge wide) ps
    have smallMass (a : ℤ) : mass (powers (X a)) ≤ mass (f a) := by
      apply mono_mass
      intro p hp
      obtain ⟨pr,n,hn,nz,pn,cp⟩ := power_mem hp
      obtain ⟨na,ax⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨n,na,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨pn,nz⟩,pr,cp⟩⟩,?_⟩
      exact (show (p:ℤ)∣n by exact_mod_cast pn).trans ax
    have thin (a : ℤ) (ca : mass (f a)≤2/3*w N) : 3*mass (X a)< mass A := by
      apply lt_of_not_ge
      intro success
      exact witness ⟨X a,filter_subset _ _,success,(smallMass a).trans ca⟩
    change mass A ≤ mass (X x)+mass (X y)+_ at part
    linarith only [part,thin x cx,thin y cy,lower,errs]
  · obtain ⟨x,hx⟩ := ine
    exact ⟨x,hx,fun q hq hr => False.elim (ex ⟨q,rare q hq hr⟩)⟩
end FirstForce299

theorem Bloom298.forcing : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H2 := FirstForce299.result

end

section

/-!
# Fourier extraction of a unit fraction

The finite Fourier expansion, cosine estimates, and centered frequency window
are adapted from Will Howe (@H0W4RD-dev), H0W4RD-dev/croot-unit-fractions,
commit c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, Basic.lean, Fourier.lean
and Prop2.lean, under Apache-2.0, as ported in the merged Erdős 319 proof.
The two classes of minor frequencies are from Bhavik Mehta and Thomas Bloom,
b-mehta/unit-fractions, src/fourier.lean, Lemma 4.22, commit
10ef71a300cf29e5f19beb2bbc723a035a0678de.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. Used under Apache-2.0.

For each sparse minor frequency choose a nearby integer x supplied by the
interval hypothesis. The prime powers that do not divide x form a nonempty
set D. Each denominator accounts for at most its number of distinct prime
factors in the incidence count. A frequency with j missing prime powers
contributes at most N^(-6j), and the lcm divisibility confines its center to
at most 2 N^j + 1 possible values for any fixed D.
-/
section
/-!
# Basic definitions for the formalization of Croot's theorem

* `Croot.recipSum S = ∑_{n ∈ S} 1/n` as a rational number;
* `Croot.PPSmooth y n`: every prime power exactly dividing `n` is at most `y`.
-/

open Finset

namespace Croot

/-- The sum of reciprocals of a finite set of natural numbers, as a rational number. -/
def recipSum (S : Finset ℕ) : ℚ := ∑ n ∈ S, (1 : ℚ) / n

@[simp] lemma recipSum_empty : recipSum ∅ = 0 := by simp [recipSum]

lemma recipSum_union {S T : Finset ℕ} (h : Disjoint S T) :
    recipSum (S ∪ T) = recipSum S + recipSum T := by
  simp [recipSum, sum_union h]

lemma recipSum_sdiff {S T : Finset ℕ} (h : T ⊆ S) :
    recipSum (S \ T) = recipSum S - recipSum T := by
  have := sum_sdiff (f := fun n : ℕ => (1 : ℚ) / n) h
  simp only [recipSum]
  linarith

lemma recipSum_nonneg (S : Finset ℕ) : 0 ≤ recipSum S :=
  sum_nonneg fun _ _ => by positivity

lemma recipSum_mono {S T : Finset ℕ} (h : S ⊆ T) : recipSum S ≤ recipSum T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- `n` is `y`-prime-power-smooth: every prime power `p ^ v_p(n)` with `p ∣ n` is `≤ y`. -/
def PPSmooth (y n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ n.factorization p ≤ y

instance (y : ℕ) : DecidablePred (PPSmooth y) := fun n => by
  unfold PPSmooth; infer_instance

lemma ppSmooth_one (y : ℕ) : PPSmooth y 1 := by simp [PPSmooth]

lemma PPSmooth.mono {y y' n : ℕ} (h : PPSmooth y n) (hy : y ≤ y') : PPSmooth y' n :=
  fun p hp => (h p hp).trans hy

lemma PPSmooth.of_dvd {y n d : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) (hd : d ∣ n) :
    PPSmooth y d := by
  intro p hp
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  have hpn : p ∈ n.primeFactors := Nat.primeFactors_mono hd hn hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  calc p ^ d.factorization p ≤ p ^ n.factorization p :=
        Nat.pow_le_pow_right hpp.pos ((Nat.factorization_le_iff_dvd hd0 hn).2 hd p)
    _ ≤ y := h p hpn

/-- A `y`-pp-smooth positive integer divides `lcm(1, …, y)`. -/
lemma PPSmooth.dvd_lcmUpto {y n : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) :
    n ∣ Nat.lcmUpto y := by
  rw [← Nat.factorization_le_iff_dvd hn (Nat.lcmUpto_ne_zero y)]
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_lcmUpto y hpp]
    exact Nat.le_log_of_pow_le hpp.one_lt (h p hp)
  · have : n.factorization p = 0 := by
      rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [this]

end Croot
end
section
/-!
# Finite Fourier analysis for subset sums of unit fractions

`eC t = exp (2 π i t)`.  For a finite set `Y` of positive integers dividing `P` and a rational
`x` with `x P ∈ ℤ`, summing `e(-h x) ∏_{m∈Y} (1 + e(h/m))` over any `P` consecutive integers `h`
counts (times `P`) the subsets `Z ⊆ Y` with `∑_{m∈Z} 1/m - x ∈ ℤ`.  We also record the
elementary estimates on the individual terms used in Croot's Proposition 2.
-/

namespace Croot

open Real Complex Finset

/-- `e(t) = exp(2 π i t)`. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-! ### Basic properties of `eC` -/

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eC_zero : eC 0 = 1 := by
  simp [eC]

lemma eC_eq_one_iff (t : ℝ) : eC t = 1 ↔ ∃ n : ℤ, t = n := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h3 : (t : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      ring
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

lemma eC_intCast (n : ℤ) : eC n = 1 := (eC_eq_one_iff _).2 ⟨n, rfl⟩

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma eC_re (t : ℝ) : (eC t).re = Real.cos (2 * π * t) := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

lemma eC_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    eC (∑ i ∈ s, f i) = ∏ i ∈ s, eC (f i) := by
  unfold eC
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma eC_nat_mul (n : ℕ) (t : ℝ) : eC (n * t) = eC t ^ n := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `1 + e(θ) = e(θ/2) · 2 cos(π θ)`. -/
lemma one_add_eC (θ : ℝ) :
    1 + eC θ = eC (θ / 2) * ((2 * Real.cos (π * θ) : ℝ) : ℂ) := by
  have h1 : ((2 * Real.cos (π * θ) : ℝ) : ℂ) =
      Complex.exp (((π * θ : ℝ) : ℂ) * I) + Complex.exp (-((π * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.two_cos]
    push_cast
    rfl
  rw [h1, mul_add]
  unfold eC
  rw [← Complex.exp_add, ← Complex.exp_add]
  have e1 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + ((π * θ : ℝ) : ℂ) * I = 2 * π * I * θ := by
    push_cast
    ring
  have e2 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + -((π * θ : ℝ) : ℂ) * I = 0 := by
    push_cast
    ring
  rw [e1, e2, Complex.exp_zero, add_comm]

lemma norm_one_add_eC (θ : ℝ) : ‖1 + eC θ‖ = 2 * |Real.cos (π * θ)| := by
  rw [one_add_eC, norm_mul, norm_eC, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_two]

lemma norm_one_add_eC_le_two (θ : ℝ) : ‖1 + eC θ‖ ≤ 2 := by
  calc ‖1 + eC θ‖ ≤ ‖(1 : ℂ)‖ + ‖eC θ‖ := norm_add_le _ _
    _ = 2 := by rw [norm_one, norm_eC]; norm_num

/-- `cos (π u) ≤ 1 - 4 u²` for `0 ≤ u ≤ 1/2`: Taylor bound for `u ≤ 3/10`, and
`cos (π u) = sin (π (1/2 - u)) ≤ π (1/2 - u)` for `u ≥ 3/10`. -/
lemma cos_pi_mul_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.cos (π * u) ≤ 1 - 4 * u ^ 2 := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  rcases le_or_gt u (3 / 10) with hu | hu
  · have hpu : 0 ≤ π * u := by positivity
    have hx : |π * u| ≤ 1 := by
      rw [abs_of_nonneg hpu]
      nlinarith
    have hb := Real.cos_bound hx
    rw [abs_of_nonneg hpu] at hb
    have hb' := (abs_le.mp hb).2
    have hp2 : 9.85 ≤ π ^ 2 := by nlinarith
    have hp2' : π ^ 2 ≤ 9.93 := by nlinarith
    have hu2 : u ^ 2 ≤ 9 / 100 := by nlinarith
    have hu2' : 0 ≤ u ^ 2 := by positivity
    have hq1 : (u ^ 2) ^ 2 ≤ 9 / 100 * u ^ 2 := by nlinarith
    have hq2 : (π ^ 2) ^ 2 ≤ 9.93 ^ 2 := by nlinarith
    have h4 : (π * u) ^ 4 ≤ 9.93 ^ 2 * (9 / 100 * u ^ 2) := by
      have : (π * u) ^ 4 = (π ^ 2) ^ 2 * (u ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul hq2 hq1 (by positivity) (by positivity)
    have h5 : 9.85 * u ^ 2 ≤ (π * u) ^ 2 := by
      have : (π * u) ^ 2 = π ^ 2 * u ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hp2 hu2'
    nlinarith
  · have hc : Real.cos (π * u) = Real.sin (π / 2 - π * u) := (Real.sin_pi_div_two_sub _).symm
    rw [hc]
    have hs := Real.sin_le (by nlinarith : 0 ≤ π / 2 - π * u)
    have hm : 0 ≤ (1 / 2 - u) * (2 + 4 * u - π) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- If `θ` is at distance `≥ δ` from every integer, then `‖1 + e(θ)‖ ≤ 2 (1 - 4 δ²)`. -/
lemma norm_one_add_eC_le_of_far (θ δ : ℝ) (hδ : 0 ≤ δ) (hfar : ∀ j : ℤ, δ ≤ |θ - j|) :
    ‖1 + eC θ‖ ≤ 2 * (1 - 4 * δ ^ 2) := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, |θ - j| ≤ 1 / 2 := ⟨round θ, abs_sub_round θ⟩
  have hδd : δ ≤ |θ - j| := hfar j
  have heq : eC θ = eC (θ - j) := by
    conv_lhs => rw [show θ = (θ - j) + (j : ℝ) by ring]
    rw [eC_add, eC_intCast, mul_one]
  rw [heq, norm_one_add_eC]
  have hcos : |Real.cos (π * (θ - j))| = Real.cos (π * |θ - j|) := by
    rw [← Real.cos_abs (π * (θ - j)), abs_mul, abs_of_pos Real.pi_pos]
    apply abs_of_nonneg
    have hle : π * |θ - j| ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    have hge : 0 ≤ π * |θ - j| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith [Real.pi_pos]
  rw [hcos]
  have hc := cos_pi_mul_le |θ - j| (abs_nonneg _) hj
  have hsq : δ * δ ≤ |θ - j| * |θ - j| := mul_le_mul hδd hδd hδ (abs_nonneg _)
  nlinarith

/-! ### Integrality and the window sum -/

lemma recipSum_mul_natCast_int (Z : Finset ℕ) (P : ℕ) (hZ : ∀ m ∈ Z, m ∣ P) :
    ∃ z : ℤ, recipSum Z * P = z := by
  refine ⟨∑ m ∈ Z, ((P / m : ℕ) : ℤ), ?_⟩
  rw [recipSum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Int.cast_natCast, Nat.cast_div_charZero (hZ m hm)]
  ring

open scoped Classical in
/-- A complete geometric sum over a window of `P` consecutive integers. -/
lemma sum_Ico_eC (r : ℝ) (P : ℕ) (hr : eC (P * r) = 1) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      if ∃ k : ℤ, r = k then (P : ℂ) else 0 := by
  have hre : ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      ∑ k ∈ Finset.range P, eC ((h₀ : ℝ) * r) * eC r ^ k := by
    refine Finset.sum_nbij' (fun h => (h - h₀).toNat) (fun k => h₀ + k) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_Ico, Finset.mem_range] at hh ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh ⊢
      omega
    · intro k _
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh
      rw [← eC_nat_mul, ← eC_add]
      congr 1
      have h1 : (((h - h₀).toNat : ℕ) : ℝ) = (h : ℝ) - h₀ := by
        have : (((h - h₀).toNat : ℕ) : ℤ) = h - h₀ := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [h1]
      ring
  rw [hre, ← Finset.mul_sum]
  split_ifs with hk
  · obtain ⟨k, rfl⟩ := hk
    have e1 : eC (k : ℝ) = 1 := eC_intCast k
    have e2 : eC ((h₀ : ℝ) * k) = 1 := by
      rw [show ((h₀ : ℝ) * k) = ((h₀ * k : ℤ) : ℝ) by push_cast; ring]
      exact eC_intCast _
    simp [e1, e2]
  · have hne : eC r ≠ 1 := fun h1 => hk ((eC_eq_one_iff r).1 h1)
    rw [geom_sum_eq hne, ← eC_nat_mul, hr]
    simp

-- `hP` is part of the fixed statement but not needed (for `P = 0` both sides vanish).
open scoped Classical in
/-- The counting identity, over any window of `P` consecutive integers. -/
theorem fourier_count (Y : Finset ℕ) (P : ℕ) (hP : 0 < P) (hY : ∀ m ∈ Y, 0 < m ∧ m ∣ P)
    (x : ℚ) (hx : ∃ z : ℤ, x * P = z) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      (P : ℂ) * ((Y.powerset.filter (fun Z => ∃ k : ℤ, recipSum Z - x = k)).card : ℂ) := by
  -- expand the product over subsets and combine the exponentials
  have key : ∀ h : ℤ, eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      ∑ Z ∈ Y.powerset, eC ((h : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) := by
    intro h
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [← eC_sum, ← eC_add]
    congr 1
    simp only [recipSum, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    rw [mul_sub, Finset.mul_sum]
    simp only [mul_one_div]
    ring
  rw [Finset.sum_congr rfl fun h _ => key h, Finset.sum_comm, Finset.natCast_card_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z hZ => ?_
  -- for each subset `Z`, `(recipSum Z - x) * P` is an integer
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := recipSum_mul_natCast_int Z P
    (fun m hm => (hY m (Finset.mem_powerset.1 hZ hm)).2)
  have hq : (recipSum Z - x) * P = ((w - z : ℤ) : ℚ) := by
    rw [sub_mul, hw, hz, Int.cast_sub]
  have hr' : (P : ℝ) * ((recipSum Z - x : ℚ) : ℝ) = ((w - z : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at this ⊢
    linarith
  have hr : eC ((P : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) = 1 := by
    rw [hr']
    exact eC_intCast _
  rw [sum_Ico_eC _ P hr h₀]
  have hiff : (∃ k : ℤ, ((recipSum Z - x : ℚ) : ℝ) = k) ↔ (∃ k : ℤ, recipSum Z - x = k) := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by exact_mod_cast hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; push_cast; rfl⟩
  by_cases hc : ∃ k : ℤ, recipSum Z - x = k
  · rw [if_pos (hiff.2 hc), if_pos hc, mul_one]
  · rw [if_neg (fun h' => hc (hiff.1 h')), if_neg hc, mul_zero]

/-- The `h = 0` term. -/
theorem term_zero (Y : Finset ℕ) (x : ℚ) :
    eC (-(((0 : ℤ) : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC (((0 : ℤ) : ℝ) / m)) = (2 : ℂ) ^ Y.card := by
  simp only [Int.cast_zero, zero_mul, neg_zero, zero_div, eC_zero, one_mul, Finset.prod_const]
  norm_num

/-- Terms with small `|h|` have nonnegative real part. -/
theorem re_term_nonneg (Y : Finset ℕ) (x : ℚ) (h : ℤ)
    (hY : ∀ m ∈ Y, 0 < m ∧ 2 * |(h : ℝ)| ≤ m)
    (hsmall : |(h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ))| ≤ 1 / 4) :
    0 ≤ (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))).re := by
  -- the term is `e(h (recipSum Y / 2 - x)) * ∏ 2 cos (π h / m)`
  simp_rw [one_add_eC]
  rw [Finset.prod_mul_distrib, ← eC_sum, ← mul_assoc, ← eC_add, ← Complex.ofReal_prod,
    Complex.re_mul_ofReal]
  apply mul_nonneg
  · rw [eC_re]
    have hsum : ∑ m ∈ Y, (h : ℝ) / m / 2 = (h : ℝ) * (∑ m ∈ Y, (1 : ℝ) / m) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hrs : ((recipSum Y : ℚ) : ℝ) = ∑ m ∈ Y, (1 : ℝ) / m := by
      simp only [recipSum, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    have hphi : -((h : ℝ) * (x : ℝ)) + ∑ m ∈ Y, (h : ℝ) / m / 2 =
        (h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ)) := by
      rw [hsum, hrs]
      ring
    rw [hphi]
    obtain ⟨h1, h2⟩ := abs_le.mp hsmall
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  · apply Finset.prod_nonneg
    intro m hm
    obtain ⟨hm0, hm1⟩ := hY m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have habs : |(h : ℝ) / m| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
      linarith
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    apply mul_nonneg (by norm_num)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]

/-- Norm bound: factors with `h/m` at distance `≥ δ` from every integer save `1 - 4 δ²`. -/
theorem norm_term_le (Y J : Finset ℕ) (hJ : J ⊆ Y) (x : ℚ) (h : ℤ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1 / 2) (hfar : ∀ m ∈ J, ∀ j : ℤ, δ ≤ |(h : ℝ) / m - j|) :
    ‖eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))‖ ≤
      2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
  rw [norm_mul, norm_eC, one_mul, norm_prod, ← Finset.prod_sdiff hJ]
  have hc : 0 ≤ 1 - 4 * δ ^ 2 := by nlinarith
  have h1 : ∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ 2 ^ (Y \ J).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun m _ => norm_one_add_eC_le_two _)
  have h2 : ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ (2 * (1 - 4 * δ ^ 2)) ^ J.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun m hm => norm_one_add_eC_le_of_far _ _ hδ (hfar m hm))
  calc (∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖) * ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖
      ≤ 2 ^ (Y \ J).card * (2 * (1 - 4 * δ ^ 2)) ^ J.card :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = 2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Finset.card_sdiff_add_card_eq_card hJ]

end Croot
end

namespace Croot
open Finset
lemma abs_le_of_mem_window {P : ℕ} {h : ℤ} (hh : h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ))
    (-((P / 2 : ℕ) : ℤ) + P)) : |(h : ℝ)| ≤ (P : ℝ) / 2 := by
  rw [Finset.mem_Ico] at hh
  obtain ⟨h1, h2⟩ := hh
  have hP2 : ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self P 2
  have hP2' : (P : ℝ) - ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 + 1 / 2 := by
    have : (P : ℝ) ≤ 2 * ((P / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show P ≤ 2 * (P / 2) + 1 by omega)
    linarith
  have h1' : -((P / 2 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast h1
  have h2' : (h : ℝ) + 1 ≤ -((P / 2 : ℕ) : ℝ) + P := by
    have : h + 1 ≤ -((P / 2 : ℕ) : ℤ) + P := h2
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

lemma zero_mem_window {P : ℕ} (hP : 0 < P) :
    (0 : ℤ) ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P) := by
  rw [Finset.mem_Ico]
  have : P / 2 < P := Nat.div_lt_self hP (by norm_num)
  constructor <;> omega

lemma card_window (P : ℕ) :
    (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).card = P := by
  rw [Int.card_Ico]
  simp

end Croot

open Real Finset Filter
open scoped Classical Topology
namespace Circle299
noncomputable abbrev span (P : ℕ) : Finset ℤ := Ico (-((P/2:ℕ):ℤ)) (-((P/2:ℕ):ℤ)+P)
noncomputable abbrev minor (P : ℕ) (K : ℝ) : Finset ℤ := (span P).filter fun h : ℤ => K/2 < |(h:ℝ)|
noncomputable abbrev interval (h : ℤ) (K : ℝ) := Icc (⌈(h:ℝ)-K/2⌉:ℤ) ⌊(h:ℝ)+K/2⌋
noncomputable def miss (A : Finset ℕ) (K : ℝ) (h : ℤ) : Finset ℕ :=
  A.filter fun n : ℕ => ∀ v∈interval h K, ¬(n:ℤ)∣v
noncomputable abbrev damp (A : Finset ℕ) (N : ℕ) (K : ℝ) (h : ℤ) :=
  exp (-((K/N)^2)*(miss A K h).card)
noncomputable abbrev term (A : Finset ℕ) (x : ℚ) (h : ℤ) :=
  Croot.eC (-((h:ℝ)*(x:ℝ))) * ∏ n ∈ A, (1+Croot.eC ((h:ℝ)/n))
lemma bound_term {A : Finset ℕ} {N : ℕ} {K : ℝ} (hN : 0<N) (hK : 0≤K) (hKN : K≤N)
    (hp : ∀ n∈A, 0<n ∧ n≤N) (x : ℚ) (h : ℤ) :
    ‖term A x h‖ ≤ (2:ℝ)^A.card*damp A N K h := by
  have npos : (0:ℝ)<N := by exact_mod_cast hN
  let δ := K/(2*N)
  have dp : 0≤δ := by dsimp [δ]; positivity
  have du : δ≤1/2 := by dsimp [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hs : miss A K h ⊆ A := filter_subset _ _
  have far (n : ℕ) (hn : n ∈ miss A K h) (j : ℤ) : δ≤|(h:ℝ)/n-j| := by
    have pos : (0:ℝ)<n := by exact_mod_cast (hp n (hs hn)).1
    have nle : (n:ℝ)≤N := by exact_mod_cast (hp n (hs hn)).2
    have hh : K/2 < |(h:ℝ)-(n:ℝ)*j| := by
      by_contra! ne
      obtain ⟨lo,hi⟩ := abs_le.mp ne
      apply (mem_filter.mp hn).2 ((n:ℤ)*j) _ (dvd_mul_right _ _)
      apply mem_Icc.mpr
      constructor
      · apply Int.ceil_le.mpr
        push_cast
        linarith
      · apply Int.le_floor.mpr
        push_cast
        linarith
    rw [div_sub',abs_div,abs_of_pos pos,le_div_iff₀ pos] <;> try positivity
    dsimp [δ]
    have t := mul_le_mul_of_nonneg_left nle dp
    dsimp [δ] at t
    have e : K/(2*(N:ℝ))*N=K/2 := by field_simp
    rw [e] at t
    simpa [mul_comm] using t.trans hh.le
  have est := Croot.norm_term_le A (miss A K h) hs x h δ dp du far
  apply est.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have pos : 0≤1-4*δ^2 := by nlinarith [mul_nonneg dp (sub_nonneg.mpr du),sq_nonneg (δ-1/2)]
  have small : 1-4*δ^2 ≤ exp (-4*δ^2) := by linarith [Real.add_one_le_exp (-4*δ^2)]
  have pe := pow_le_pow_left₀ pos small (miss A K h).card
  rw [←Real.exp_nat_mul] at pe
  have e : 4*δ^2=(K/N)^2 := by dsimp [δ]; ring
  simpa only [damp,←neg_mul,neg_mul_eq_neg_mul, mul_comm (↑(miss A K h).card : ℝ)] using
    (pe.trans_eq (congrArg exp (show ((miss A K h).card:ℝ)*(-4*δ^2) = -((K/N)^2)*(miss A K h).card by rw [←e]; ring)))
lemma extract {A : Finset ℕ} {N d : ℕ} {K M : ℝ} (hN : 0<N) (hd : 0<d)
    (hK : 0≤K) (hKM : K≤M) (hMN : M≤N) (hM : 0<M)
    (ha : ∀ n∈A, 0<n ∧ M≤n ∧ n≤N) (hdP : d∣A.lcm id)
    (hh : (Croot.recipSum A:ℝ)<2/d) (hl : 2/(d:ℝ)-1/M≤Croot.recipSum A)
    (period : ((A.lcm id:ℕ):ℝ) < (2:ℝ)^A.card/2)
    (tail : ∑ h ∈ minor (A.lcm id) K, damp A N K h ≤ 1/2) :
    ∃ S ⊆ A, Croot.recipSum S = 1/d := by
  classical
  let P := A.lcm id
  let x : ℚ := 1/d
  have dr : (0:ℝ)<d := by exact_mod_cast hd
  have dq : 0<(d:ℚ) := by exact_mod_cast hd
  have ar (n : ℕ) (hn : n∈A) : 0<n ∧ n∣P := ⟨(ha n hn).1,dvd_lcm hn⟩
  have pp : 0<P := by
    change 0<A.lcm id
    exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr fun n hn => (ha n hn).1.ne')
  have xp : ∃ z : ℤ, x*P=z := by
    obtain ⟨j,hj⟩ := hdP
    refine ⟨j,?_⟩
    change (1/(d:ℚ))*(A.lcm id:ℕ)=_
    rw [hj]
    push_cast
    field_simp
  have count := Croot.fourier_count A P pp ar x xp (-((P/2:ℕ):ℤ))
  let Z := A.powerset.filter fun S => ∃ k : ℤ, Croot.recipSum S-x=k
  have ident : (∑ h ∈ span P, (term A x h).re) = (P:ℝ)*Z.card := by
    have e := congrArg Complex.re count
    simpa [term,span,Z,Complex.re_sum] using e
  have major {h : ℤ} (lo : |(h:ℝ)|≤K/2) : 0≤(term A x h).re := by
    apply Croot.re_term_nonneg
    · intro n hn
      exact ⟨(ha n hn).1, by linarith [(ha n hn).2.1]⟩
    · rw [show (2:ℝ)/d=2*(1/d) by ring] at hh hl
      have xval : (x:ℝ)=1/d := by simp [x]
      rw [xval,abs_mul,abs_of_nonpos (by linarith : (Croot.recipSum A:ℝ)/2-1/d≤0)]
      have h1 : -((Croot.recipSum A:ℝ)/2-1/d) ≤ 1/(2*M) := by
        have eq : 1/(2*M)=(1/M)/2 := by ring
        rw [eq]; linarith
      calc _ ≤ (M/2)*(1/(2*M)) := mul_le_mul (lo.trans (by linarith)) h1 (by linarith) (by positivity)
           _ = _ := by field_simp <;> norm_num
  have zero := Croot.term_zero A x
  have sumlow : (2:ℝ)^A.card/2 ≤ ∑ h ∈ span P, (term A x h).re := by
    let F := minor P K
    let R := span P \ F
    have zR : (0:ℤ)∈R := mem_sdiff.mpr ⟨Croot.zero_mem_window pp,by simp [F,minor,show 0≤K/2 by positivity]⟩
    have main : (2:ℝ)^A.card ≤ ∑ h ∈ R, (term A x h).re := by
      have nn (h : ℤ) (hh : h∈R) : 0≤(term A x h).re := by
        have he := mem_sdiff.mp hh
        exact major (le_of_not_gt (fun hlt => he.2 (mem_filter.mpr ⟨he.1,hlt⟩)))
      have sg := single_le_sum nn zR
      have z : (term A x 0).re=(2:ℝ)^A.card := by rw [show term A x 0=_ from zero]; norm_cast
      simpa only [z] using sg
    have err : -(∑ h ∈ F, (term A x h).re) ≤ (2:ℝ)^A.card/2 := by
      rw [←sum_neg_distrib]
      calc _ ≤ ∑ h ∈ F, (2:ℝ)^A.card*damp A N K h := by
             apply sum_le_sum
             intro h _
             exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
               (bound_term hN hK (hKM.trans hMN) (fun n hn => ⟨(ha n hn).1,(ha n hn).2.2⟩) x h))
           _ ≤ _ := by rw [←mul_sum]; nlinarith [mul_le_mul_of_nonneg_left tail (by positivity : 0≤(2:ℝ)^A.card)]
    have spl := sum_sdiff (f:=fun h => (term A x h).re) (show F⊆span P from filter_subset _ _)
    change (∑ h ∈ R, _)+(∑ h ∈ F, _) = _ at spl
    linarith
  by_contra! none
  have single : Z ⊆ {∅} := by
    intro S hS
    obtain ⟨sm,k,ek⟩ := mem_filter.mp hS
    have sa := mem_powerset.mp sm
    by_contra ne
    have sn : S.Nonempty := nonempty_iff_ne_empty.mpr (by simpa using ne)
    have positive : 0<Croot.recipSum S := sum_pos' (fun n _ => by positivity)
      (sn.imp (fun n hn => ⟨hn,one_div_pos.mpr (by exact_mod_cast (ha n (sa hn)).1)⟩))
    have b := Croot.recipSum_mono sa
    have aq : Croot.recipSum A < 2/(d:ℚ) := by
      apply (Rat.cast_lt (K:=ℝ)).mp
      push_cast
      exact hh
    rw [show (2:ℚ)/d=2*x by dsimp [x]; ring] at aq
    have x1 : x≤1 := by dsimp [x]; rw [div_le_iff₀ dq]; simpa only [one_mul] using (show (1:ℚ)≤d by exact_mod_cast hd)
    have : (k:ℚ)<1 := by linarith
    have : (-1:ℚ)<k := by linarith
    have kz : k=0 := by
      have kl : -1<k := by exact_mod_cast ‹(-1:ℚ)<k›
      have ku : k<1 := by exact_mod_cast ‹(k:ℚ)<1›
      omega
    apply none S sa
    rw [kz,Int.cast_zero] at ek
    exact sub_eq_zero.mp ek
  have card : Z.card≤1 := (card_le_card single).trans_eq (card_singleton _)
  have bound : (P:ℝ)*Z.card≤P := by simpa using mul_le_mul_of_nonneg_left (show (Z.card:ℝ)≤1 by exact_mod_cast card) (by positivity : (0:ℝ)≤P)
  change (P:ℝ)<_ at period
  linarith
end Circle299

open Finset Real Filter
open scoped Classical Topology
namespace Circle299
noncomputable def powers (A : Finset ℕ) := A.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
noncomputable def part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
noncomputable abbrev absent (A : Finset ℕ) (x : ℤ) := (powers A).filter fun q : ℕ => ¬(q:ℤ)∣x
lemma power_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
    IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ q∣n ∧ Nat.Coprime q (n/q) := by
  obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
  obtain ⟨dv,pp,cp⟩ := mem_filter.mp hq
  obtain ⟨hd,h0⟩ := Nat.mem_divisors.mp dv
  exact ⟨pp,n,hn,h0,hd,cp⟩
lemma cover (A : Finset ℕ) (ha : 0∉A) (x : ℤ) :
    (A.lcm id:ℕ) ∣ x.natAbs * ∏ q ∈ absent A x, q := by
  apply Finset.lcm_dvd
  intro n hn
  have nz : n≠0 := by rintro rfl; exact ha hn
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k pp h
  by_cases k0 : k=0
  · simp [k0]
  have ek := (pp.pow_dvd_iff_le_factorization nz).mp h
  set q := p^n.factorization p
  have qn : q∣n := Nat.ordProj_dvd n p
  have qpp : IsPrimePow q := (pp.isPrimePow.pow (by omega : n.factorization p≠0))
  have qc : Nat.Coprime q (n/q) := (Nat.coprime_ordCompl pp nz).pow_left _
  have hq : q∈powers A := mem_biUnion.mpr ⟨n,hn,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨qn,nz⟩,qpp,qc⟩⟩
  apply (pow_dvd_pow p ek).trans
  by_cases hd : (q:ℤ)∣x
  · exact dvd_mul_of_dvd_left (by simpa using Int.natAbs_dvd_natAbs.mpr hd) _
  · exact dvd_mul_of_dvd_right (dvd_prod_of_mem id (mem_filter.mpr ⟨hq,hd⟩)) _
lemma index_subset {A : Finset ℕ} {n : ℕ} (hn : n≠0) (D : Finset ℕ) (hD : D⊆powers A) :
    (D.filter (fun q => n ∈ part A q)) ⊆ n.primeFactors.image (fun p => p^n.factorization p) := by
  intro q hq
  obtain ⟨qD,mem⟩ := mem_filter.mp hq
  obtain ⟨_,qn,cp⟩ := mem_filter.mp mem
  obtain ⟨p,_,k,_,pr,kn,eq⟩ := (isPrimePow_nat_iff_bounded q).mp (power_mem (hD qD)).1
  subst q
  have pd : p∣p^k := dvd_pow_self _ (by omega)
  have pm := Nat.mem_primeFactors.mpr ⟨pr,pd.trans qn,hn⟩
  refine mem_image.mpr ⟨p,pm,?_⟩
  have cp' := cp.coprime_dvd_left pd
  have nodiv := (Nat.Prime.coprime_iff_not_dvd pr).mp cp'
  have zero := Nat.factorization_eq_zero_of_not_dvd nodiv
  have en := Nat.mul_div_cancel' qn
  have e : n.factorization p=k := by
    conv_lhs => rw [←en]
    rw [Nat.factorization_mul_apply_of_coprime cp,zero,add_zero,pr.factorization_pow]
    simp
  rw [e]
lemma missed_count {A D : Finset ℕ} {Y L W : ℝ} {h : ℤ} {K : ℝ}
    (ha : ∀ n∈A, n≠0 ∧ (n.primeFactors.card:ℝ)≤W)
    (hD : D⊆powers A) (qy : ∀ q∈D, (q:ℝ)≤Y)
    (hy : 0<Y) (hl : 0≤L) (hw : 0≤W)
    (many : ∀ q∈D, L/q ≤ (((miss A K h).filter (fun n => n ∈ part A q)).card:ℝ)) :
    D.card*(L/Y) ≤ (miss A K h).card*W := by
  let J := miss A K h
  have hq (q : ℕ) (hq : q∈D) : 0<(q:ℝ) := by exact_mod_cast (power_mem (hD hq)).1.pos
  have sumineq : ∑ q ∈ D, L/Y ≤ ∑ q ∈ D, (((J.filter (fun n => n∈part A q)).card):ℝ) := by
    apply sum_le_sum
    intro q qD
    exact (div_le_div_of_nonneg_left hl (hq q qD) (qy q qD)).trans (many q qD)
  have swap : (∑ q ∈ D, (((J.filter (fun n => n∈part A q)).card):ℝ)) =
      ∑ n ∈ J, (((D.filter (fun q => n∈part A q)).card):ℝ) := by
    simp_rw [natCast_card_filter]
    exact sum_comm
  rw [swap,sum_const,nsmul_eq_mul] at sumineq
  apply sumineq.trans
  calc _ ≤ ∑ _n ∈ J, W := by
         apply sum_le_sum
         intro n hn
         have nA := (mem_filter.mp hn).1
         have c := (card_le_card (index_subset (ha n nA).1 D hD)).trans card_image_le
         exact (show (((D.filter (fun q => n∈part A q)).card):ℝ) ≤ n.primeFactors.card by exact_mod_cast c).trans (ha n nA).2
       _ = _ := by simp [J]
end Circle299

open Finset Real
open scoped Classical
namespace Circle299
noncomputable abbrev size (D : Finset ℕ) := ∏ q ∈ D, q
noncomputable abbrev box (q : ℕ) := Icc (-(q:ℤ)) (q:ℤ)
noncomputable def candidates (P N : ℕ) (D : Finset ℕ) :=
  ((box (size D)) ×ˢ (box N)).image fun z : ℤ × ℤ => z.1*P/(size D:ℤ)+z.2
lemma box_card (q : ℕ) : (box q).card=2*q+1 := by
  rw [box,Int.card_Icc]
  omega
lemma cand_card {D : Finset ℕ} {N P : ℕ} (hn : 1≤N) (hD : ∀ q∈D, 1≤q ∧ q≤N) :
    (candidates P N D).card ≤ 9*N*N^D.card := by
  have hs : size D≤N^D.card := by
    rw [←prod_const]
    apply prod_le_prod' (fun q hq => (hD q hq).2)
  have hp : 1≤N^D.card := Nat.one_le_pow _ _ hn
  have cc := card_image_le (f:=fun z : ℤ×ℤ => z.1*P/(size D:ℤ)+z.2) (s:=(box (size D)) ×ˢ (box N))
  rw [card_product,box_card,box_card] at cc
  change (candidates P N D).card≤_ at cc
  have a : 2*size D+1≤3*N^D.card := by omega
  have b : 2*N+1≤3*N := by omega
  exact cc.trans ((Nat.mul_le_mul a b).trans_eq (by ring))
lemma distance {K : ℝ} {h x : ℤ} (hx : x∈interval h K) : |(x:ℝ)-h| ≤ K/2 := by
  obtain ⟨l,u⟩ := mem_Icc.mp hx
  have lo := Int.ceil_le.mp l
  have hi := Int.le_floor.mp u
  rw [abs_le]
  constructor <;> linarith
lemma cand_member {A : Finset ℕ} {K : ℝ} {N : ℕ} {h x : ℤ} (ha : 0∉A)
    (hK : K<((A.lcm id:ℕ):ℝ)) (hN : K≤N) (hh : h ∈ minor (A.lcm id) K)
    (hx : x ∈ interval h K) :
    (absent A x).Nonempty ∧ h∈candidates (A.lcm id) N (absent A x) := by
  let P : ℕ := A.lcm id
  let D := absent A x
  have pp : 0<P := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr (fun n hn he => ha (by simpa [id] using he ▸ hn)))
  have pr : (0:ℝ)<P := by exact_mod_cast pp
  have hd := distance hx
  have wh := Croot.abs_le_of_mem_window (mem_filter.mp hh).1
  change |(h:ℝ)|≤(P:ℝ)/2 at wh
  have ax : |(x:ℝ)| < P := by
    change K<(P:ℝ) at hK
    calc _ = |((x:ℝ)-h)+h| := by ring_nf
         _ ≤ |(x:ℝ)-h|+|(h:ℝ)| := abs_add_le _ _
         _ < _ := by linarith
  have dP : (P:ℤ)∣x*(size D:ℤ) := by
    apply Int.natAbs_dvd_natAbs.mp
    rw [Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]
    exact cover A ha x
  have qs : 0<size D := prod_pos (fun q hq => (power_mem (mem_filter.mp hq).1).1.pos)
  have az : |x|<(P:ℤ) := by exact_mod_cast ax
  have ds : D.Nonempty := by
    by_contra! empty
    have de : D=∅ := empty
    have px : (P:ℤ)∣x := by simpa [de,size] using dP
    have xz : x=0 := by
      by_contra nz
      have nb := Int.natAbs_le_of_dvd_ne_zero px nz
      have az' : x.natAbs<P := by
        exact_mod_cast (show (x.natAbs:ℤ)<P by rw [Int.natCast_natAbs]; exact az)
      simpa using (not_le_of_gt az') (by simpa using nb)
    have e := (mem_filter.mp hh).2
    subst x
    simp only [Int.cast_zero,zero_sub,abs_neg] at hd
    linarith
  refine ⟨ds,?_⟩
  obtain ⟨j,hj⟩ := dP
  have hJ : |j|≤(size D:ℤ) := by
    have eq := congrArg abs hj
    simp only [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at eq
    nlinarith only [eq,mul_le_mul_of_nonneg_right az.le (show 0≤(size D:ℤ) by positivity),
      (show 0<(P:ℤ) by exact_mod_cast pp)]
  have hZ : |h-x| ≤ (N:ℤ) := by
    have h0 : 0≤K/2 := (abs_nonneg _).trans hd
    have e : |(h:ℝ)-x|≤(N:ℝ) := by rw [abs_sub_comm]; linarith
    exact_mod_cast e
  refine mem_image.mpr ⟨(j,h-x), mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp hJ),mem_Icc.mpr (abs_le.mp hZ)⟩,?_⟩
  change j*P/(size D:ℤ)+(h-x)=h
  rw [mul_comm j,←hj,Int.mul_ediv_cancel _ (by exact_mod_cast qs.ne')]
  ring
end Circle299

open Finset Real
open scoped Classical
namespace Circle299
lemma sparse_sum {S : Finset ℤ} {Q : Finset ℕ} {N P : ℕ} {v : ℤ→ℝ}
    (hn : 36≤N) (qbound : ∀ q∈Q, 1≤q ∧ q≤N)
    (assign : ∀ h∈S, ∃ D ⊆ Q, D.Nonempty ∧ h∈candidates P N D ∧
        v h ≤ 1/((N:ℝ)^D.card)^6) :
    ∑ h ∈ S, v h ≤ 1/4 := by
  classical
  let f (h : ℤ) := if hs : h∈S then (assign h hs).choose else ∅
  have spec {h : ℤ} (hs : h∈S) : f h⊆Q ∧ (f h).Nonempty ∧ h∈candidates P N (f h) ∧
      v h ≤ 1/((N:ℝ)^(f h).card)^6 := by
    simpa [f,hs] using (assign h hs).choose_spec
  have qsmall : Q.card ≤ N := by
    have e : Q⊆Icc 1 N := fun q hq => mem_Icc.mpr (qbound q hq)
    simpa using card_le_card e
  have rpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have nn : (36:ℝ)≤N := by exact_mod_cast hn
  have maps (h : ℤ) (hs : h∈S) : (f h).card∈Icc 1 N :=
    mem_Icc.mpr ⟨card_pos.mpr (spec hs).2.1,(card_le_card (spec hs).1).trans qsmall⟩
  have partition := sum_fiberwise_of_maps_to (s:=S) (t:=Icc 1 N) (g:=fun h => (f h).card) maps v
  rw [←partition]
  have one (j : ℕ) (hj : j∈Icc 1 N) : ∑ h ∈ S.filter (fun h => (f h).card=j), v h ≤ 1/(4*N) := by
    let J := S.filter (fun h => (f h).card=j)
    let F := Q.powersetCard j
    have sub : J⊆F.biUnion (candidates P N) := by
      intro h hh
      obtain ⟨hs,e⟩ := mem_filter.mp hh
      exact mem_biUnion.mpr ⟨f h,mem_powersetCard.mpr ⟨(spec hs).1,e⟩,(spec hs).2.2.1⟩
    have fc : F.card≤N^j := by
      rw [show F.card=Q.card.choose j from card_powersetCard _ _]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left qsmall _)
    have card : J.card ≤ N^j*(9*N*N^j) := by
      apply (card_le_card sub).trans
      apply card_biUnion_le.trans
      calc _ ≤ ∑ _D ∈ F, 9*N*N^j := by
             apply sum_le_sum
             intro D hD
             have a := mem_powersetCard.mp hD
             simpa only [a.2] using (cand_card (P:=P) (by omega : 1≤N) (fun q hq => qbound q (a.1 hq)))
           _ = F.card*(9*N*N^j) := by simp
           _ ≤ _ := Nat.mul_le_mul_right _ fc
    let b := (N:ℝ)^j
    have bpos : 0<b := pow_pos rpos _
    have nb : (N:ℝ)≤b := by
      simpa using pow_le_pow_right₀ (by linarith : (1:ℝ)≤N) (mem_Icc.mp hj).1
    have B1 : 1≤b := by linarith
    have bound : 36*(N:ℝ)^2≤ b^4 := by
      have eq := mul_le_mul (show (36:ℝ)≤b^2 by nlinarith [sq_nonneg (b-1)]) (pow_le_pow_left₀ rpos.le nb 2) (sq_nonneg _) (sq_nonneg _)
      nlinarith only [eq]
    calc _ ≤ ∑ _h ∈ J, 1/b^6 := by
           apply sum_le_sum
           intro h hh
           obtain ⟨hs,e⟩ := mem_filter.mp hh
           simpa only [e] using (spec hs).2.2.2
         _ = J.card*(1/b^6) := by simp
         _ ≤ (b*(9*N*b))*(1/b^6) := by
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           dsimp [b]
           exact_mod_cast card
         _ ≤ _ := by
           rw [mul_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
           nlinarith only [mul_le_mul_of_nonneg_right bound (sq_nonneg b)]
  calc _ ≤ ∑ _j ∈ Icc 1 N, 1/(4*(N:ℝ)) := sum_le_sum one
       _ = _ := by simp; field_simp <;> ring
end Circle299

open Finset Real Filter
open scoped Classical Topology
namespace Circle299
lemma total_tail {A : Finset ℕ} {N : ℕ} {K T L Y : ℝ}
    (hn : 36≤N) (ha : 0∉A) (hK : K < ((A.lcm id:ℕ):ℝ)) (hKN : K≤N)
    (hy : 1≤Y) (hB : 2≤log (N:ℝ)) (tL : T/2≤L) (lpos : 0≤L)
    (hreg : ∀ n∈A, (n.primeFactors.card:ℝ) ≤ 2*log N)
    (hQ : ∀ q∈powers A, q≤N ∧ (q:ℝ)≤Y)
    (hP : log ((A.lcm id:ℕ):ℝ) ≤ 7*Y)
    (scale : 100*(log N)^3*Y ≤ (K/N)^2*T)
    (good : ∀ h : ℤ, T ≤ ((miss A K h).card:ℝ) ∨ ∃ x∈interval h K,
      ∀ q∈powers A, ((((miss A K h).filter (fun n => n∈part A q)).card:ℝ) < L/q) → (q:ℤ)∣x) :
    ∑ h∈minor (A.lcm id) K, damp A N K h ≤ 1/2 := by
  classical
  let P : ℕ := A.lcm id
  let F := minor P K
  let E := F.filter fun h => T ≤ ((miss A K h).card:ℝ)
  let S := F \ E
  let r := (K/N)^2
  let B := log (N:ℝ)
  have pp : 0<P := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr (fun n hn he => ha (by simpa [id] using he ▸ hn)))
  have pr : (0:ℝ)<P := by exact_mod_cast pp
  have nr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have yy : 0<Y := by linarith
  have bb : 2≤B := hB
  have rp : 0≤r := sq_nonneg _
  change 100*B^3*Y ≤ r*T at scale
  have hl4 : log 4 ≤ 3 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have big : r*T ≥ log 4+log P := by
    have z : 1≤B^3 := one_le_pow₀ (by linarith : 1≤B)
    have m := mul_le_mul_of_nonneg_right z yy.le
    change log (P:ℝ)≤7*Y at hP
    nlinarith only [m,hl4,hP,scale,hy]
  have heavy : ∑ h∈E, damp A N K h ≤ 1/4 := by
    have point (h : ℤ) (he : h∈E) : damp A N K h ≤ 1/(4*P) := by
      have e := mul_le_mul_of_nonneg_left (mem_filter.mp he).2 rp
      change exp (-r*(miss A K h).card) ≤ _
      rw [one_div,←exp_log (by positivity : (0:ℝ)<4*P),←exp_neg,exp_le_exp,log_mul (by norm_num) pr.ne']
      linarith
    calc _ ≤ ∑ _h∈E, 1/(4*(P:ℝ)) := sum_le_sum point
         _ ≤ (P:ℝ)*(1/(4*P)) := by
           simp only [sum_const,nsmul_eq_mul]
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           exact_mod_cast (card_le_card (show E⊆span P from (filter_subset _ _).trans (filter_subset _ _))).trans_eq (Croot.card_window P)
         _ = _ := by field_simp
  have dscale : 6*B*(2*B*Y) ≤ r*L := by
    have e := mul_le_mul_of_nonneg_left tL rp
    have bound := mul_le_mul_of_nonneg_right (show 24*B^2 ≤ 100*B^3 by nlinarith [mul_nonneg (sq_nonneg B) (show 0≤B-2 by linarith)]) yy.le
    nlinarith only [bound,scale,e]
  have small : ∑ h∈S, damp A N K h ≤ 1/4 := by
    apply sparse_sum (P:=P) (Q:=powers A) hn (fun q hq => ⟨(power_mem hq).1.pos,(hQ q hq).1⟩)
    intro h hs
    obtain ⟨hf,he⟩ := mem_sdiff.mp hs
    have nt : ¬ T≤((miss A K h).card:ℝ) := fun e => he (mem_filter.mpr ⟨hf,e⟩)
    obtain ⟨x,hx,prop⟩ := (good h).resolve_left nt
    let D := absent A x
    have de := cand_member ha hK hKN hf hx
    refine ⟨D,filter_subset _ _,de.1,de.2,?_⟩
    have cnt := missed_count (A:=A) (D:=D) (h:=h) (K:=K)
      (fun n hn => ⟨(by rintro rfl; exact ha hn),hreg n hn⟩)
      (filter_subset _ _) (fun q hq => (hQ q (mem_filter.mp hq).1).2) yy lpos (by positivity : 0≤2*log (N:ℝ))
      (fun q hq => le_of_not_gt (fun e => (mem_filter.mp hq).2 (prop q (mem_filter.mp hq).1 e)))
    change D.card*(L/Y) ≤ (miss A K h).card*(2*B) at cnt
    rw [←mul_div_assoc,div_le_iff₀ yy] at cnt
    have c := mul_le_mul_of_nonneg_left cnt rp
    have a := mul_le_mul_of_nonneg_right dscale (Nat.cast_nonneg D.card : (0:ℝ)≤D.card)
    have e : 6*B*D.card*(2*B*Y) ≤ (r*(miss A K h).card)*(2*B*Y) := by nlinarith only [c,a]
    have div := le_of_mul_le_mul_right e (by positivity : 0<2*B*Y)
    change exp (-r*(miss A K h).card) ≤ _
    rw [one_div,←exp_log (by positivity : 0<((N:ℝ)^D.card)^6),←exp_neg,exp_le_exp,log_pow,log_pow]
    change _ ≤ -(6*(D.card*B))
    linarith
  have e := sum_sdiff (f:=damp A N K) (show E⊆F from filter_subset _ _)
  change (∑ h∈S, damp A N K h)+(∑ h∈E, damp A N K h)=_ at e
  change (∑ h∈F, damp A N K h)≤_
  linarith
end Circle299

open Filter Real Finset
open scoped Classical Topology
namespace BloomScale
noncomputable abbrev B (N:ℕ) := log (N:ℝ)
noncomputable abbrev w (N:ℕ) := log (B N)
noncomputable abbrev M (N:ℕ) := (N:ℝ)^(1-1/w N)
noncomputable abbrev K (N:ℕ) := M N*(N:ℝ)^(-2/w N)
noncomputable abbrev Y (N:ℕ) := (N:ℝ)^(1-8/w N)
noncomputable abbrev T (N:ℕ) := M N/B N
noncomputable abbrev L (N:ℕ) := M N/(2*(B N)^(1/100:ℝ))
noncomputable abbrev U (N:ℕ) := (N:ℝ)^(1/w N)
lemma large (c : ℝ) : ∀ᶠ N : ℕ in atTop,
    1<N ∧ 8≤w N ∧ 2≤B N ∧ 0<K N ∧ K N<M N ∧ M N≤N ∧
    1≤Y N ∧ T N/2≤L N ∧ c*(B N)^3*Y N ≤ (K N/N)^2*T N := by
  have bt : Tendsto B atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have wt : Tendsto w atTop atTop := tendsto_log_atTop.comp bt
  have hs : Tendsto (fun x : ℝ => (log x)^(2:ℕ)/x) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop 2 (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  filter_upwards [eventually_gt_atTop 1,wt.eventually_ge_atTop 8,bt.eventually_ge_atTop 2,
      bt.eventually_ge_atTop c,(hs.comp bt).eventually_lt_const (show (0:ℝ)<1/8 by norm_num)]
    with N hn hw hb hbc hs
  have nr : (1:ℝ)<N := by exact_mod_cast hn
  have np : 0<(N:ℝ) := by linarith
  have bp : 0<B N := by linarith
  have wp : 0<w N := by linarith
  have up : 1<U N := one_lt_rpow nr (by positivity)
  have up0 : 0<U N := by linarith
  have h : (B N)^8 ≤ U N := by
    apply (log_le_log_iff (by positivity) up0).mp
    rw [log_pow,log_rpow np]
    change (w N)^2/B N < 1/8 at hs
    have g := (div_lt_iff₀ bp).mp hs
    change (8:ℝ)*w N ≤ 1/w N*B N
    rw [one_div_mul_eq_div,le_div_iff₀ wp]
    nlinarith only [g]
  have powU (i : ℕ) : (N:ℝ)^((i:ℝ)/w N) = U N^i := by
    rw [←Real.rpow_natCast (U N),←rpow_mul np.le]
    congr 1
    ring
  have ms : M N=(N:ℝ)/U N := by rw [M,rpow_sub np,rpow_one]
  have ks : K N=(N:ℝ)/U N^3 := by
    rw [K,ms,show (-2:ℝ)/w N=-(2/w N) by ring,rpow_neg np.le,show (N:ℝ)^(2/w N)=U N^2 by simpa using powU 2]
    field_simp
    <;> ring
  have ys : Y N=(N:ℝ)/U N^8 := by
    rw [Y,rpow_sub np,rpow_one,show (N:ℝ)^(8/w N)=U N^8 by simpa using powU 8]
  have mpos : 0<M N := rpow_pos_of_pos np _
  refine ⟨hn,hw,hb,by rw [ks]; positivity,?_,?_,?_,?_,?_⟩
  · rw [ks,ms]
    exact div_lt_div_of_pos_left np up0 (by nlinarith [sq_pos_of_pos up0,mul_pos up0 (sub_pos.mpr up),mul_pos up0 (show 0<U N^2-1 by nlinarith [sq_nonneg (U N-1)])])
  · rw [ms]
    exact div_le_self np.le up.le
  · apply one_le_rpow nr.le
    have : 8/w N≤1 := (div_le_one wp).mpr hw
    linarith
  · have le : (B N)^(1/100:ℝ) ≤ B N := by
      simpa using (rpow_le_rpow_of_exponent_le (by linarith : 1≤B N) (show (1/100:ℝ)≤1 by norm_num))
    rw [T,L,div_div]
    apply div_le_div_of_nonneg_left mpos.le (by positivity)
    linarith
  · have eq : (K N/N)^2*T N = Y N*U N/B N := by
      rw [T,ks,ms,ys]
      field_simp
      <;> ring
    rw [eq,le_div_iff₀ bp]
    have hpow : B N^5≤B N^8 := pow_le_pow_right₀ (by linarith) (by omega)
    have v : c*B N^4 ≤ U N := by
      calc _ ≤ B N^5 := by nlinarith only [mul_le_mul_of_nonneg_right hbc (pow_nonneg bp.le 4)]
           _ ≤ _ := hpow.trans h
    have := mul_le_mul_of_nonneg_right v (rpow_pos_of_pos np (1-8/w N)).le
    change c*B N^4*Y N ≤ U N*Y N at this
    nlinarith only [this]
end BloomScale

open Real Filter Finset
open scoped Classical Topology
namespace Circle299
open BloomScale
lemma lcm_est {Y : ℝ} (hy : 0≤Y) {A : Finset ℕ} (ha : 0∉A)
    (smooth : ∀ n∈A, ∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ)≤Y) :
    log ((A.lcm id:ℕ):ℝ) ≤ 7*Y := by
  have hd : A.lcm id ∣ Nat.lcmUpto ⌊Y⌋₊ := by
    apply Finset.lcm_dvd
    intro n hn
    have nz : n≠0 := by rintro rfl; exact ha hn
    apply Croot.PPSmooth.dvd_lcmUpto _ nz
    intro p hp
    have pr := Nat.prime_of_mem_primeFactors hp
    have f : 0<n.factorization p := Nat.pos_of_ne_zero (by simpa only [←Finsupp.mem_support_iff,Nat.support_factorization] using hp)
    exact Nat.le_floor (smooth n hn (p^n.factorization p) (pr.isPrimePow.pow f.ne') (Nat.ordProj_dvd n p))
  have ppos : 0<A.lcm id := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun n hn h => ha (by simpa [id] using h ▸ hn))
  have logle := log_le_log (show (0:ℝ)<(A.lcm id:ℕ) by exact_mod_cast ppos)
    (show ((A.lcm id:ℕ):ℝ)≤Nat.lcmUpto ⌊Y⌋₊ by exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos _) hd)
  rw [←Chebyshev.psi_eq_log_lcmUpto] at logle
  have hh := Chebyshev.psi_le_const_mul_self (x:=(⌊Y⌋₊:ℝ)) (by positivity)
  have l4 : log 4≤3 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have f := Nat.floor_le hy
  nlinarith only [logle,hh,mul_le_mul_of_nonneg_right l4 (Nat.cast_nonneg ⌊Y⌋₊ : (0:ℝ)≤⌊Y⌋₊),f]
theorem complete : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H4 := by
  classical
  intro z
  filter_upwards [BloomScale.large (100*(z+1)),eventually_ge_atTop 36] with N sc hn
  obtain ⟨n1,hw,hb,kpos,km,mn,hy,tl,sc⟩ := sc
  intro A d hd dz ha an reg balance good
  let P : ℕ := A.lcm id
  have pp : 0<P := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun n hn he => ha (by simpa [id] using he ▸ hn))
  have nr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have dr : (0:ℝ)<d := by exact_mod_cast hd
  have zr : (0:ℝ)≤z := by positivity
  have dzr : (d:ℝ)≤z := by exact_mod_cast dz
  have yy : 0<Y N := by linarith
  have bp : 0<B N := by linarith
  have mp : 0<M N := kpos.trans km
  have lp : 0<L N := by dsimp [L]; exact div_pos mp (mul_pos (by norm_num) (rpow_pos_of_pos bp _))
  obtain ⟨hi,lo,dp,_⟩ := balance
  have cast_sum : (Croot.recipSum A:ℝ) = ∑ n∈A,(1:ℝ)/n := by simp [Croot.recipSum]
  have lower : 2/(d:ℝ)-1/M N ≤ Croot.recipSum A := by rwa [cast_sum]
  have upper : (Croot.recipSum A:ℝ) < 2/d := by rwa [cast_sum]
  have hnr (n : ℕ) (hn : n∈A) : 0<n ∧ M N≤n ∧ n≤N :=
    ⟨Nat.pos_of_ne_zero (by rintro rfl; exact ha hn),(reg n hn).1,(mem_range.mp (an hn)).le⟩
  have smooth (n : ℕ) (hn : n∈A) := (reg n hn).2.1
  have logp := lcm_est yy.le ha smooth
  change log (P:ℝ) ≤ 7*Y N at logp
  have rat : (K N/N)^2≤1 := by
    have e := (div_le_one nr).mpr (km.le.trans mn)
    have pos : 0≤K N/(N:ℝ) := by positivity
    nlinarith [mul_nonneg pos (sub_nonneg.mpr e)]
  have rT : (K N/N)^2*T N ≤ M N := by
    have tp : 0≤T N := div_nonneg mp.le bp.le
    calc _ ≤ 1*T N := mul_le_mul_of_nonneg_right rat tp
         _ ≤ _ := by simpa [T] using (div_le_self mp.le (by linarith : 1≤B N))
  have bc : 1≤B N^3 := one_le_pow₀ (by linarith)
  have g := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bc (show 0≤100*((z:ℝ)+1) by positivity)) yy.le
  have huge : 100*((z:ℝ)+1)*Y N≤M N := by linarith only [g,sc,rT]
  have base : 100*(B N)^3*Y N≤(K N/N)^2*T N := by
    have e := mul_le_mul_of_nonneg_right (show (100:ℝ)≤100*((z:ℝ)+1) by linarith) (mul_nonneg (pow_nonneg bp.le 3) yy.le)
    nlinarith only [e,sc]
  have lowcard : 2*(M N/d)-1 ≤ (A.card:ℝ) := by
    have ess : (Croot.recipSum A:ℝ) ≤ A.card*(1/M N) := by
      rw [cast_sum]
      calc _ ≤ ∑ _n∈A, 1/M N := sum_le_sum fun n hn => one_div_le_one_div_of_le mp (hnr n hn).2.1
           _ = _ := by simp
    have e := mul_le_mul_of_nonneg_right (lower.trans ess) mp.le
    field_simp [mp.ne',dr.ne'] at e ⊢
    nlinarith
  have many : 100*Y N≤M N/d := by
    rw [le_div_iff₀ dr]
    nlinarith only [huge,mul_le_mul_of_nonneg_right dzr yy.le,hy]
  have period : (P:ℝ)<(2:ℝ)^A.card/2 := by
    have e : 1/2≤log (2:ℝ) := by have h := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at h; linarith
    apply (log_lt_log_iff (by exact_mod_cast pp) (by positivity)).mp
    rw [log_div (by positivity) (by norm_num),log_pow]
    have ec := mul_le_mul_of_nonneg_left e (show 0≤(A.card:ℝ)-1 by linarith)
    nlinarith only [ec,logp,lowcard,many,hy]
  have ne : A.Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ)<A.card by linarith))
  obtain ⟨n,hnA⟩ := ne
  have np : n≤P := Nat.le_of_dvd pp (dvd_lcm hnA)
  have kp : K N < (P:ℝ) := km.trans_le ((hnr n hnA).2.1.trans (by exact_mod_cast np))
  apply extract (N:=N) (K:=K N) (M:=M N) (by omega) hd kpos.le km.le mn mp hnr dp upper lower period
  refine total_tail hn ha kp (km.le.trans mn) hy hb tl lp.le ?_ ?_ logp base ?_
  · intro n hn
    have up := (reg n hn).2.2.2
    change (n.primeFactors.card:ℝ)≤2*w N at up
    have e := log_le_sub_one_of_pos bp
    change log (B N) ≤ B N-1 at e
    change _ ≤ 2*B N
    dsimp [w] at up
    linarith
  · intro q hq
    obtain ⟨pr,n,hn,_,dv,_⟩ := power_mem hq
    exact ⟨(Nat.le_of_dvd (hnr n hn).1 dv).trans (hnr n hn).2.2,smooth n hn q pr dv⟩
  · intro h
    have gh := good (h:ℝ)
    rcases gh with big|⟨x,hx,hxq⟩
    · exact Or.inl big
    · refine Or.inr ⟨x,hx,fun q hq e => hxq q hq ?_⟩
      have sets : (miss A (K N) h).filter (fun n => n ∈ part A q) =
          (part A q).filter (fun n : ℕ => ∀ x ∈ interval h (K N), ¬(n:ℤ)∣x) := by ext n; simp [miss,part,and_left_comm,and_assoc,and_comm]
      rw [sets] at e
      exact e
end Circle299

theorem Bloom298.fourier : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H4 := Circle299.complete

end

theorem Bloom298.extraction : OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H1 :=
  OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1.main Bloom298.regularity
    (OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.main Bloom298.pruning Bloom298.forcing
      (OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1.main Rough299.result OMA.FactorMass.density) Bloom298.fourier)

/-! The finite repetition lemma is adapted from @OrangeHeadz, and the
positive-density colour class from @marcusbuffett, PR 3593. -/

-- Step Erdos298.erdos_298.variants.natural_density.R1.H2: hypothesis H2 of reduction Erdos298.erdos_298.variants.natural_density.R1

/-!
Induction on `k`. Given `T ⊆ A` with weight `k r`, pick `N` above every element of `T`. Since sets
of weight `r` inside `A ∩ [N', ∞)` exist for arbitrarily large `N'`, there is one with `N' ≥ N`; it
is disjoint from `T`, and the union has weight `(k + 1) r`.
-/

theorem Bloom298.repeatSum : OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H2 := by
  unfold OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H2
  intro A w r hfreq k
  induction k with
  | zero =>
    exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hTA, hTsum⟩ := ih
    obtain ⟨N', hN', S, hSA, hSsum⟩ :=
      (Filter.frequently_atTop.mp hfreq) (T.sup id + 1)
    have hdisj : Disjoint T S := by
      rw [Finset.disjoint_left]
      intro x hxT hxS
      have h1 : x ≤ T.sup id := Finset.le_sup (f := id) hxT
      have h2 : N' ≤ x := (hSA (Finset.mem_coe.mpr hxS)).2
      omega
    refine ⟨T ∪ S, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
      · exact hTA (Finset.mem_coe.mpr h)
      · exact (hSA (Finset.mem_coe.mpr h)).1
    · rw [Finset.sum_union hdisj, hTsum, hSsum]
      push_cast
      ring

namespace Bloom298
open Filter

/-- A denominator occurring arbitrarily far out can be repeated on disjoint sets. -/
theorem unit (A : Set ℕ) (hzero : 0 ∉ A) (hpos : 0 < A.upperDensity) :
    ∃ T : Finset ℕ, (T : Set ℕ) ⊆ A ∧ ∑ n ∈ T, (1 / n : ℚ) = 1 := by
  obtain ⟨D, hD, h⟩ := Bloom298.extraction A hzero hpos
  obtain ⟨d, hd, hfreq⟩ :=
    (frequently_exists_finset (l := (atTop : Filter ℕ)) D).mp (Eventually.of_forall h).frequently
  obtain ⟨T, hT, heq⟩ := Bloom298.repeatSum A (fun n => (1 / n : ℚ)) (1 / d) hfreq d
  refine ⟨T, hT, ?_⟩
  rw [heq]
  have hpos : (0 : ℚ) < d := by exact_mod_cast hD d hd
  field_simp

end Bloom298

/-! If k colors occur, some color has at least n representatives in [kn,2kn)
for arbitrarily large n. Those intervals eventually lie beyond every cutoff. -/

open Filter Finset

theorem Bloom298.color : ∀ c : ℕ → ℕ, (Set.range c).Finite → ∃ j : ℕ, ∀ B : ℕ,
  0 < {n : ℕ | B < n ∧ c n = j}.upperDensity := by
  classical
  intro c hc
  let C := hc.toFinset
  have hC : C.Nonempty := ⟨c 0,hc.mem_toFinset.mpr ⟨0,rfl⟩⟩
  let k := C.card
  have hk : 0<k := card_pos.mpr hC
  let seg (n : ℕ) := Ico (k*n) (2*(k*n))
  have base (n : ℕ) : ∃ j ∈ C, n ≤ ((seg n).filter fun a => c a=j).card := by
    apply exists_le_card_fiber_of_mul_le_card_of_maps_to (fun a _ => hc.mem_toFinset.mpr ⟨a,rfl⟩) hC
    simp only [seg,Nat.card_Ico]
    change k*n ≤ 2*(k*n)-k*n
    omega
  obtain ⟨j,_,hj⟩ := (C.frequently_exists).mp ((Eventually.of_forall base).frequently (f:=atTop))
  refine ⟨j,?_⟩
  intro B
  let T : Set ℕ := {n | B<n ∧ c n=j}
  have low : 0 < (1:ℝ)/(2*k) := by positivity
  apply low.trans_le
  refine le_limsup_of_frequently_le (u:=fun n => T.partialDensity Set.univ n) ?_ ?_
  · rw [frequently_atTop] at hj ⊢
    intro N
    obtain ⟨n,hn,hfreq⟩ := hj (max N B+1)
    have hkn : n ≤ k*n := Nat.le_mul_of_pos_left _ hk
    have hN := le_max_left N B
    have hB := le_max_right N B
    refine ⟨2*(k*n),by omega,?_⟩
    let F := (seg n).filter fun a => c a=j
    have hsub : (↑F : Set ℕ) ⊆ T ∩ Set.Iio (2*(k*n)) := by
      intro a ha
      obtain ⟨hm,hc'⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha1,ha2⟩ := Finset.mem_Ico.mp hm
      exact ⟨⟨by omega,hc'⟩,ha2⟩
    have hcnt : n ≤ (T ∩ Set.Iio (2*(k*n))).ncard := hfreq.trans
      (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub
            ((Set.finite_Iio _).subset Set.inter_subset_right))
    simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Nat.ncard_Iio]
    push_cast
    have hn' : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hreal : (n:ℝ) ≤ ((T ∩ Set.Iio (2*(k*n))).ncard:ℝ) := by exact_mod_cast hcnt
    nlinarith [mul_le_mul_of_nonneg_left hreal hk'.le]
  · exact ⟨1,eventually_map.mpr (Eventually.of_forall (Set.partialDensity_le_one T Set.univ))⟩


theorem OMA.solution : OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2.H1 := by
  classical
  intro c hc
  obtain ⟨j,hj⟩ := Bloom298.color c hc
  let A : Set ℕ := {n | 1 < n ∧ c n = j}
  obtain ⟨S,hS,unit⟩ := Bloom298.unit A (by simp [A]) (hj 1)
  refine ⟨S, fun n hn => (hS hn).1, unit, ?_⟩
  rintro _ ⟨i,hi,rfl⟩ _ ⟨k,hk,rfl⟩
  exact (hS hi).2.trans (hS hk).2.symm
