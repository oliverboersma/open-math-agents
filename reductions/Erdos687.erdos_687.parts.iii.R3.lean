import FormalConjectures.ErdosProblems.«687»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Bertrand

-- Reduction Erdos687.erdos_687.parts.iii.R3 of Erdős Problem 687 — iii
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Proved here: residue covers of `[1, y]` by primes `≤ x` are exactly blocks of `y`
consecutive integers without an integer coprime to `primorial x` (CRT), so
`Y x < y` iff every block of length `y` contains such an integer. Bertrand handles
offsets `b ≤ y`, reflection `n ↦ P - n` and `P ± 1` handle the second half of a period.
H1 (a classical prime-gap theorem, Ingham 1937: primes in `(n, n + n^{5/8+o(1)}]`)
handles offsets `b ≤ y^{3/2}`. H2 is the remaining core: offsets `b > y^{3/2}` in the
first half of the period.
-/

open Filter
open scoped Asymptotics

namespace OMA.R_Erdos687_erdos_687_parts_iii_R3

private lemma add_residue_complement {p : ℕ} (hp : 0 < p) (a : ℕ) :
    a + (p - a % p) ≡ 0 [MOD p] := by
  have hmod : a ≡ a % p [MOD p] := by simp [Nat.ModEq]
  have hsum : a % p + (p - a % p) = p := by
    have := Nat.mod_lt a hp
    omega
  refine (hmod.add_right _).trans ?_
  simpa only [hsum] using (Nat.modulus_modEq_zero (n := p))

/-- A residue cover is a block without any integer coprime to the primorial.
It suffices to consider starting points in one period. -/
private lemma covered_iff_shifted_nonCoprime (x y : ℕ) :
    Green46.IsCoveredByResidues x y ↔
      ∃ b < primorial x, ∀ m ∈ Finset.Icc 1 y, ¬ (b + m).Coprime (primorial x) := by
  constructor
  · rintro ⟨a, ha⟩
    let ps := (Finset.range (x + 1)).filter Nat.Prime
    have hmem (p : ℕ) : p ∈ ps ↔ p ≤ x ∧ p.Prime := by
      simp [ps]
    have hn (p : ℕ) (hp : p ∈ ps) : p ≠ 0 := ((hmem p).mp hp).2.ne_zero
    have hpair : Set.Pairwise (ps : Set ℕ) (Function.onFun Nat.Coprime id) := by
      intro p hp q hq hpq
      exact (Nat.coprime_primes ((hmem p).mp hp).2 ((hmem q).mp hq).2).mpr hpq
    let b := Nat.chineseRemainderOfFinset (fun p ↦ p - a p % p) id ps hn hpair
    refine ⟨b, Nat.chineseRemainderOfFinset_lt_prod _ _ hn hpair, ?_⟩
    intro m hm
    obtain ⟨p, hpx, hp, hma⟩ := ha m hm
    have hba := b.property p ((hmem p).mpr ⟨hpx, hp⟩)
    have hsum : (b : ℕ) + m ≡ 0 [MOD p] := by
      refine (hba.add hma).trans ?_
      rw [add_comm]
      exact add_residue_complement hp.pos (a p)
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, Nat.modEq_zero_iff_dvd.mp hsum, hp.dvd_primorial_iff.mpr hpx⟩
  · rintro ⟨b, _, hb⟩
    refine ⟨fun p ↦ p - b % p, ?_⟩
    intro m hm
    obtain ⟨p, hp, hpbm, hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp (hb m hm)
    refine ⟨p, hp.dvd_primorial_iff.mp hpx, hp, Nat.ModEq.add_left_cancel' b ?_⟩
    exact (Nat.modEq_zero_iff_dvd.mpr hpbm).trans (add_residue_complement hp.pos b).symm

private lemma covered_iff_le_Y (x y : ℕ) : Green46.IsCoveredByResidues x y ↔ y ≤ Erdos687.Y x := by
  let S : Set ℕ := {n | Green46.IsCoveredByResidues x n}
  have hbounded : BddAbove S :=
    ⟨primorial x, fun n hn ↦ (Erdos687.lt_primorial_of_isCoveredByResidues (x := x) (y := n) hn).le⟩
  have hn : (0 : ℕ) ∈ S := ⟨id, by simp⟩
  change y ∈ S ↔ y ≤ sSup S
  refine ⟨le_csSup hbounded, fun hy ↦ ?_⟩
  obtain ⟨a, ha⟩ : sSup S ∈ S := Nat.sSup_mem ⟨0, hn⟩ hbounded
  exact ⟨a, fun m hm ↦ ha m (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hy⟩)⟩

/-- The first length that guarantees a coprime integer in every block is `Erdos687.Y x + 1`. -/
private lemma Y_lt_iff_uniform_coprime (x y : ℕ) :
    Erdos687.Y x < y ↔
      ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  classical
  rw [← not_le, ← covered_iff_le_Y, covered_iff_shifted_nonCoprime]
  push Not
  rfl

private lemma target_iff_uniform_coprime :
    (∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε))) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊,
        (b + m).Coprime (primorial x) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (h (ε / 2) (half_pos hε))
    have hgrowth : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
    filter_upwards [hC, (tendsto_atTop.mp hgrowth) (C + 1), eventually_ge_atTop 1] with x hx hlarge hx1
    apply (Y_lt_iff_uniform_coprime _ _).mp
    apply Nat.lt_ceil.mpr
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx1 : 0 < x)
    have hnonneg : 0 ≤ (x : ℝ) ^ (1 + ε / 2) := Real.rpow_nonneg hxpos.le _
    have hbound : (Erdos687.Y x : ℝ) ≤ C * (x : ℝ) ^ (1 + ε / 2) := by
      simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (Erdos687.Y x)), Real.norm_of_nonneg hnonneg] using hx
    calc
      (Erdos687.Y x : ℝ) ≤ C * (x : ℝ) ^ (1 + ε / 2) := hbound
      _ < (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (1 + ε / 2) :=
        mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hxpos _)
      _ = (x : ℝ) ^ (1 + ε) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  · intro h ε hε
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [h ε hε] with x hx
    have hy := Nat.lt_ceil.mp ((Y_lt_iff_uniform_coprime _ _).mpr hx)
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (Erdos687.Y x)),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _), one_mul] using hy.le

/-- Bertrand's postulate supplies a coprime integer when the offset is at most the length. -/
private lemma coprime_of_offset_le_length {x y b : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y)
    (hby : b ≤ y) : ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (max b x)
    (Nat.ne_of_gt (hx.trans_le (le_max_right _ _)))
  have hbp : b < p := (le_max_left _ _).trans_lt hlt
  have hxp : x < p := (le_max_right _ _).trans_lt hlt
  have hupper : p ≤ b + y := by
    rcases le_total b x with hbx | hxb
    · rw [max_eq_right hbx] at hle
      omega
    · rw [max_eq_left hxb] at hle
      omega
  refine ⟨p - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (p - b) = p by omega]
  exact hp.coprime_iff_not_dvd.mpr (fun hd ↦ (not_le.mpr hxp) (hp.dvd_primorial_iff.mp hd))

/-- A block crossing the end of the period contains `P - 1` or `P + 1`. -/
private lemma coprime_of_crossing_period {P b y : ℕ} (hy : 2 ≤ y)
    (hb : b < P) (hend : P ≤ b + y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  by_cases h : b + 1 < P
  · refine ⟨P - 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [show b + (P - 1 - b) = P - 1 by omega]
    exact (Nat.coprime_self_sub_left (by omega : 1 ≤ P)).mpr (Nat.coprime_one_left P)
  · refine ⟨2, Finset.mem_Icc.mpr ⟨by decide, hy⟩, ?_⟩
    rw [show b + 2 = 1 + P by omega, Nat.coprime_add_self_left]
    exact Nat.coprime_one_left P

/-- Reflection within a period preserves coprimality and reverses a block. -/
private lemma coprime_of_reflected_offset {P b y : ℕ} (hend : b + y < P)
    (h : ∃ m ∈ Finset.Icc 1 y, (P - (b + y) - 1 + m).Coprime P) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  obtain ⟨m, hm, hc⟩ := h
  obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hm
  refine ⟨y + 1 - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (y + 1 - m) = P - (P - (b + y) - 1 + m) by omega]
  exact (Nat.coprime_self_sub_left (by omega : P - (b + y) - 1 + m ≤ P)).mpr hc

/-- For long blocks it suffices to test blocks in the first half of the period,
starting more than one block length from zero. -/
private lemma uniform_coprime_of_first_half {x y : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y)
    (h : ∀ b, y < b → 2 * b + y < primorial x →
      ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x)) :
    ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  intro b hb
  by_cases hsmall : b ≤ y
  · exact coprime_of_offset_le_length hx hxy hsmall
  by_cases hfirst : 2 * b + y < primorial x
  · exact h b (lt_of_not_ge hsmall) hfirst
  by_cases hcross : primorial x ≤ b + y
  · exact coprime_of_crossing_period (by omega) hb hcross
  apply coprime_of_reflected_offset (lt_of_not_ge hcross)
  let b' := primorial x - (b + y) - 1
  change ∃ m ∈ Finset.Icc 1 y, (b' + m).Coprime (primorial x)
  by_cases hsmall' : b' ≤ y
  · exact coprime_of_offset_le_length hx hxy hsmall'
  exact h b' (lt_of_not_ge hsmall') (by dsimp [b']; omega)

private lemma eventually_twice_le_length {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, 0 < x ∧ 2 * x ≤ ⌈(x : ℝ) ^ (1 + ε)⌉₊ := by
  have hgrowth : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, (tendsto_atTop.mp hgrowth) 2] with x hx hg
  have hx' : 0 < x := hx
  have hpos : 0 < (x : ℝ) := by exact_mod_cast hx'
  have hreal : ((2 * x : ℕ) : ℝ) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by
    calc
      ((2 * x : ℕ) : ℝ) = (x : ℝ) * 2 := by push_cast; ring
      _ ≤ (x : ℝ) * (x : ℝ) ^ ε := mul_le_mul_of_nonneg_left hg hpos.le
      _ = (x : ℝ) ^ (1 + ε) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := Nat.le_ceil _
  exact ⟨hx', by exact_mod_cast hreal⟩

private lemma target_of_first_half
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      ∀ b, L < b → 2 * b + L < primorial x →
        ∃ m ∈ Finset.Icc 1 L, (b + m).Coprime (primorial x)) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_iff_uniform_coprime.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_twice_le_length hε] with x hinner hx
  exact uniform_coprime_of_first_half hx.1 hx.2 hinner

/-- Gaps between primes: for large `n` there is a prime in `(n, n + n^{2/3}]`
(Ingham 1937 gives exponent `5/8 + o(1)`, Huxley `7/12 + o(1)`). -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n) ^ 3 ≤ n ^ 2

/-- Core: with `L = ⌈x^(1+ε)⌉`, every block `[b+1, b+L]` with `L^3 < b^2` lying in the
first half of the period of `primorial x` contains an integer coprime to `primorial x`. -/
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
    ∀ b : ℕ, ⌈(x : ℝ) ^ (1 + ε)⌉₊ ^ 3 < b ^ 2 → 2 * b + ⌈(x : ℝ) ^ (1 + ε)⌉₊ < primorial x →
      ∃ m ∈ Finset.Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊, (b + m).Coprime (primorial x)

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.parts.iii := by
  intro h1 h2
  apply target_of_first_half
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h1
  filter_upwards [h2 ε hε, eventually_twice_le_length hε, eventually_ge_atTop N]
    with x hcore hx hxN
  intro L b hLb hhalf
  by_cases hbig : L ^ 3 < b ^ 2
  · exact hcore b hbig hhalf
  · push Not at hbig
    obtain ⟨p, hp, hbp, hgap⟩ := hN b (by omega)
    have hpL : p - b ≤ L := by
      have h3 : (p - b) ^ 3 ≤ L ^ 3 := hgap.trans hbig
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3
    refine ⟨p - b, Finset.mem_Icc.mpr ⟨by omega, hpL⟩, ?_⟩
    rw [show b + (p - b) = p by omega]
    have hxp : x < p := by omega
    exact hp.coprime_iff_not_dvd.mpr (fun hd ↦ (not_le.mpr hxp) (hp.dvd_primorial_iff.mp hd))

end OMA.R_Erdos687_erdos_687_parts_iii_R3
