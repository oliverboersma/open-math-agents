import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1
import Mathlib
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
