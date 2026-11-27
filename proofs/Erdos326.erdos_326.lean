import FormalConjectures.ErdosProblems.«326»

-- Credit: @senamakel

/-!
Adapted from github.com/davidlueng986-alt/erdos-326-lean-proof (commit 70c8cd1bad641f449a8532ea8e874e241387daca),
(c) 2026 Liang Wan Yiu David, MIT License.
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated
documentation files, to deal in the Software without restriction, subject to the MIT licence notice of the
source repository being included. The software is provided as is, without warranty of any kind.
Inlined and adapted to Lean v4.33.1 and the site Mathlib pin: module headers removed, lemma names adjusted.
The underlying result is the source author's unrefereed work.
-/

open scoped Classical

namespace OMA.Port6

-- ==== Cassels



namespace Erdos326

noncomputable section

def primeBase (s : Fin 2) (i : ℕ) : ℕ :=
  (if s = 0 then 3 else 6) * 4 ^ (i + 1)

lemma primeBase_ne_zero (s : Fin 2) (i : ℕ) : primeBase s i ≠ 0 := by
  unfold primeBase
  split <;> positivity

noncomputable def qSeq (s : Fin 2) : ℕ → ℕ
  | 0 => 1
  | i + 1 => Classical.choose (Nat.bertrand (primeBase s i) (primeBase_ne_zero s i))

lemma qSeq_prime (s : Fin 2) (i : ℕ) : Nat.Prime (qSeq s (i + 1)) :=
  (Classical.choose_spec (Nat.bertrand (primeBase s i) (primeBase_ne_zero s i))).1

lemma qSeq_bounds (s : Fin 2) (i : ℕ) :
    (if s = 0 then 3 else 6) * 4 ^ (i + 1) < qSeq s (i + 1) ∧
    qSeq s (i + 1) ≤ 2 * ((if s = 0 then 3 else 6) * 4 ^ (i + 1)) :=
  (Classical.choose_spec (Nat.bertrand (primeBase s i) (primeBase_ne_zero s i))).2

/-- All prime steps across both sequences `qSeq 0` and `qSeq 1` are pairwise distinct,
    hence pairwise coprime. -/
lemma qSeq_coprime_cross (i j : ℕ) : Nat.Coprime (qSeq 0 i) (qSeq 1 j) := by
  cases i with
  | zero => simp [qSeq]
  | succ i =>
    cases j with
    | zero => simp [qSeq]
    | succ j =>
      have hp0 := qSeq_prime 0 i
      have hp1 := qSeq_prime 1 j
      have hne : qSeq 0 (i + 1) ≠ qSeq 1 (j + 1) := by
        have hb0 := qSeq_bounds 0 i
        have hb1 := qSeq_bounds 1 j
        simp only [ite_true] at hb0
        simp only [if_neg (by decide : ¬ ((1 : Fin 2) = 0))] at hb1
        rcases lt_trichotomy i j with hij | rfl | hji
        · have hpow : 4 ^ (i + 1) * 4 ≤ 4 ^ (j + 1) := by
            have : i + 2 ≤ j + 1 := by omega
            calc 4 ^ (i + 1) * 4 = 4 ^ (i + 2) := by ring
            _ ≤ 4 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) this
          omega
        · omega
        · have hpow : 4 ^ (j + 1) * 4 ≤ 4 ^ (i + 1) := by
            have : j + 2 ≤ i + 1 := by omega
            calc 4 ^ (j + 1) * 4 = 4 ^ (j + 2) := by ring
            _ ≤ 4 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) this
          omega
      exact (Nat.coprime_primes hp0 hp1).2 hne

/-- The prime step of either sequence lies in a short interval at each scale. -/
def scale (s : Fin 2) : ℕ := if s = 0 then 3 else 6

lemma scale_cases (s : Fin 2) : scale s = 3 ∨ scale s = 6 := by
  unfold scale
  split <;> simp

lemma scale_pos (s : Fin 2) : 0 < scale s := by
  rcases scale_cases s with h | h <;> omega

lemma qSeq_bounds_of_pos (s : Fin 2) {i : ℕ} (hi : 0 < i) :
    scale s * 4 ^ i < qSeq s i ∧ qSeq s i ≤ 2 * (scale s * 4 ^ i) := by
  cases i with
  | zero => omega
  | succ i => simpa only [scale] using qSeq_bounds s i

lemma qSeq_pos (s : Fin 2) (i : ℕ) : 0 < qSeq s i := by
  cases i with
  | zero =>
    change 0 < 1
    decide
  | succ i => exact (qSeq_prime s i).pos

lemma qSeq_strictMono (s : Fin 2) : StrictMono (qSeq s) := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero => exact (qSeq_prime s 0).one_lt
  | succ i =>
    have h := (qSeq_bounds_of_pos s (i := i + 1) (by omega)).2
    have h' := (qSeq_bounds_of_pos s (i := i + 1 + 1) (by omega)).1
    rw [pow_succ (4 : ℕ) (i + 1), ← mul_assoc] at h'
    omega

lemma qSeq_coprime (s : Fin 2) {i j : ℕ} (hij : i ≠ j) :
    (qSeq s i).Coprime (qSeq s j) := by
  cases i with
  | zero => simp [qSeq]
  | succ i =>
    cases j with
    | zero => simp [qSeq]
    | succ j =>
      exact (Nat.coprime_primes (qSeq_prime s i) (qSeq_prime s j)).2
        (fun h => hij ((qSeq_strictMono s).injective h))

/-- Highest coefficient in block `i`. -/
def blockSize (s : Fin 2) (i : ℕ) : ℕ := qSeq s (i + 1) + qSeq s (i + 2)

def blockWidth (s : Fin 2) (i : ℕ) : ℕ := blockSize s i * qSeq s i

/-- The first and last terms of block `i` are `blockStart s i` and `blockStart s (i + 1)`. -/
def blockStart (s : Fin 2) : ℕ → ℕ
  | 0 => 0
  | i + 1 => blockStart s i + blockWidth s i

lemma blockStart_zero (s : Fin 2) : blockStart s 0 = 0 := rfl

lemma blockStart_succ (s : Fin 2) (i : ℕ) :
    blockStart s (i + 1) = blockStart s i + blockWidth s i := rfl

lemma blockWidth_pos (s : Fin 2) (i : ℕ) : 0 < blockWidth s i := by
  unfold blockWidth blockSize
  exact Nat.mul_pos (Nat.add_pos_left (qSeq_pos s _) _) (qSeq_pos s _)

lemma blockStart_strictMono (s : Fin 2) : StrictMono (blockStart s) :=
  strictMono_nat_of_lt_succ fun i => by
    rw [blockStart_succ]
    exact Nat.lt_add_of_pos_right (blockWidth_pos s i)

lemma blockSize_bounds (s : Fin 2) (i : ℕ) :
    20 * scale s * 4 ^ i < blockSize s i ∧
    blockSize s i ≤ 40 * scale s * 4 ^ i := by
  have h1 := qSeq_bounds_of_pos s (i := i + 1) (by omega)
  have h2 := qSeq_bounds_of_pos s (i := i + 2) (by omega)
  have hr1 : (4 : ℕ) ^ (i + 1) = 4 ^ i * 4 := pow_succ 4 i
  have hr2 : (4 : ℕ) ^ (i + 2) = 4 ^ i * 16 := by
    rw [pow_add]
    norm_num
  rw [hr1, ← mul_assoc] at h1
  rw [hr2, ← mul_assoc] at h2
  unfold blockSize
  constructor
  · calc
      _ = scale s * 4 ^ i * 4 + scale s * 4 ^ i * 16 := by ring
      _ < _ := Nat.add_lt_add h1.1 h2.1
  · calc
      _ ≤ 2 * (scale s * 4 ^ i * 4) + 2 * (scale s * 4 ^ i * 16) :=
        Nat.add_le_add h1.2 h2.2
      _ = _ := by ring

lemma blockWidth_bounds (s : Fin 2) {i : ℕ} (hi : 0 < i) :
    20 * scale s ^ 2 * 16 ^ i < blockWidth s i ∧
    blockWidth s i ≤ 80 * scale s ^ 2 * 16 ^ i := by
  have hq := qSeq_bounds_of_pos s hi
  have hm := blockSize_bounds s i
  unfold blockWidth
  constructor
  · calc
      _ = (20 * scale s * 4 ^ i) * (scale s * 4 ^ i) := by
        rw [show (16 : ℕ) = 4 * 4 by decide, mul_pow]
        ring
      _ < _ := Nat.mul_lt_mul_of_lt_of_le hm.1 hq.1.le (qSeq_pos s i)
  · calc
      _ ≤ (40 * scale s * 4 ^ i) * (2 * (scale s * 4 ^ i)) :=
        Nat.mul_le_mul hm.2 hq.2
      _ = _ := by
        rw [show (16 : ℕ) = 4 * 4 by decide, mul_pow]
        ring

lemma blockWidth_growth (s : Fin 2) (i : ℕ) :
    4 * blockWidth s i ≤ blockWidth s (i + 1) := by
  cases i with
  | zero =>
    have h0 := (blockSize_bounds s 0).2
    have h1 := (blockWidth_bounds s (i := 1) (by decide)).1
    change 4 * (blockSize s 0 * 1) ≤ blockWidth s 1
    rcases scale_cases s with h | h <;> rw [h] at h0 h1 <;> norm_num at h0 h1 <;> omega
  | succ i =>
    have h := (blockWidth_bounds s (i := i + 1) (by omega)).2
    have h' := (blockWidth_bounds s (i := i + 1 + 1) (by omega)).1
    rw [pow_succ (16 : ℕ) (i + 1), ← mul_assoc] at h'
    calc
      _ ≤ 4 * (80 * scale s ^ 2 * 16 ^ (i + 1)) := Nat.mul_le_mul_left 4 h
      _ = 20 * scale s ^ 2 * 16 ^ (i + 1) * 16 := by ring
      _ ≤ _ := h'.le

lemma blockStart_le (s : Fin 2) (i : ℕ) : blockStart s i ≤ 6 * scale s ^ 2 * 16 ^ i := by
  induction i with
  | zero => simp [blockStart_zero]
  | succ i ih =>
    have hw : blockWidth s i ≤ 80 * scale s ^ 2 * 16 ^ i := by
      by_cases hi : 0 < i
      · exact (blockWidth_bounds s hi).2
      · have hi' : i = 0 := by omega
        subst i
        have hs := (blockSize_bounds s 0).2
        change blockSize s 0 * 1 ≤ 80 * scale s ^ 2 * 16 ^ 0
        rcases scale_cases s with h | h <;> rw [h] at hs ⊢ <;> norm_num at hs ⊢ <;> omega
    rw [blockStart_succ, pow_succ]
    calc
      _ ≤ 6 * scale s ^ 2 * 16 ^ i + 80 * scale s ^ 2 * 16 ^ i := Nat.add_le_add ih hw
      _ = 86 * (scale s ^ 2 * 16 ^ i) := by ring
      _ ≤ 96 * (scale s ^ 2 * 16 ^ i) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring

lemma le_blockStart (s : Fin 2) {i : ℕ} (hi : 2 ≤ i) :
    scale s ^ 2 * 16 ^ i ≤ blockStart s i := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
  have h := (blockWidth_bounds s (i := i) (by omega)).1
  change scale s ^ 2 * 16 ^ (i + 1) ≤ blockStart s (i + 1)
  rw [blockStart_succ, pow_succ]
  calc
    _ = 16 * (scale s ^ 2 * 16 ^ i) := by ring
    _ ≤ 20 * (scale s ^ 2 * 16 ^ i) := Nat.mul_le_mul_right _ (by decide)
    _ = 20 * scale s ^ 2 * 16 ^ i := by ring
    _ ≤ _ := h.le.trans (Nat.le_add_left _ _)

/-- A Cassels block, including its shared endpoint with the next block. -/
def casselsBlock (s : Fin 2) (i : ℕ) : Set ℕ :=
  {x | ∃ t ≤ blockSize s i, x = blockStart s i + t * qSeq s i}

def casselsBasis (s : Fin 2) : Set ℕ := ⋃ i, casselsBlock s i

lemma mem_casselsBasis {s : Fin 2} {x : ℕ} :
    x ∈ casselsBasis s ↔ ∃ i, x ∈ casselsBlock s i :=
  Set.mem_iUnion

lemma mem_casselsBlock_bounds {s : Fin 2} {i x : ℕ} (hx : x ∈ casselsBlock s i) :
    blockStart s i ≤ x ∧ x ≤ blockStart s (i + 1) := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [blockStart_succ, blockWidth]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _

/-- An interval of exactly `q` coefficient choices can realize any residue. -/
private lemma residue_window (p q b n lo : ℕ) (hpq : p.Coprime q) (hq : 0 < q) :
    ∃ t, lo ≤ t ∧ t < lo + q ∧ b + t * p ≡ n [MOD q] := by
  let _ : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime p hpq
  let z : ZMod q := ((n : ZMod q) - b - lo * p) * ↑u⁻¹
  refine ⟨lo + z.val, Nat.le_add_right _ _, Nat.add_lt_add_left (ZMod.val_lt z) _, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  have hu : (p : ZMod q) = ↑u := (ZMod.coe_unitOfCoprime p hpq).symm
  have hz : z * (p : ZMod q) = (n : ZMod q) - b - lo * p := by
    rw [hu, show z = ((n : ZMod q) - b - lo * p) * ↑u⁻¹ by rfl, mul_assoc, ← Units.val_mul]
    simp [← hu]
  push_cast
  rw [ZMod.natCast_zmod_val]
  calc
    _ = (b : ZMod q) + lo * p + z * p := by ring
    _ = _ := by rw [hz]; ring

/-- Fill the second progression after matching the residue with the first. -/
private lemma block_sum_of_window (s : Fin 2) (i j lo n : ℕ)
    (hc : (qSeq s i).Coprime (qSeq s j))
    (hwin : ∀ t, lo ≤ t → t < lo + qSeq s j →
      t ≤ blockSize s i ∧
      blockStart s i + blockStart s j + t * qSeq s i ≤ n ∧
      n ≤ blockStart s i + blockStart s j + t * qSeq s i + blockWidth s j) :
    ∃ x ∈ casselsBlock s i, ∃ y ∈ casselsBlock s j, x + y = n := by
  obtain ⟨t, htl, htu, htmod⟩ := residue_window
    (qSeq s i) (qSeq s j) (blockStart s i + blockStart s j) n lo hc (qSeq_pos s j)
  obtain ⟨ht, hl, hu⟩ := hwin t htl htu
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_dvd' hl).1 htmod
  have hpv : v * qSeq s j ≤ blockSize s j * qSeq s j := by
    rw [mul_comm v, ← hv, ← blockWidth]
    omega
  refine ⟨blockStart s i + t * qSeq s i, ⟨t, ht, rfl⟩,
    blockStart s j + v * qSeq s j,
    ⟨v, Nat.le_of_mul_le_mul_right hpv (qSeq_pos s j), rfl⟩, ?_⟩
  rw [mul_comm v]
  omega

/-- The two coverage intervals used at each Cassels scale overlap. -/
lemma cassels_cover_interval (s : Fin 2) (i n : ℕ)
    (hlo : 2 * blockStart s (i + 1) ≤ n)
    (hhi : n ≤ 2 * blockStart s (i + 2)) :
    ∃ j, i ≤ j ∧ j ≤ i + 2 ∧
      ∃ x ∈ casselsBlock s i, ∃ y ∈ casselsBlock s j, x + y = n := by
  have hsize : blockSize s i = qSeq s (i + 1) + qSeq s (i + 2) := rfl
  have hstart₁ := blockStart_succ s i
  have hstart₂ : blockStart s (i + 2) = blockStart s (i + 1) + blockWidth s (i + 1) :=
    blockStart_succ s (i + 1)
  by_cases hn : n ≤ blockStart s i + blockStart s (i + 2) +
      (qSeq s (i + 2) + 1) * qSeq s i
  · refine ⟨i + 1, by omega, by omega, ?_⟩
    apply block_sum_of_window s i (i + 1) (qSeq s (i + 2) + 1) n
      (qSeq_coprime s (by omega))
    intro t htlo hthi
    have ht : t ≤ blockSize s i := by omega
    have hmul₁ := Nat.mul_le_mul_right (qSeq s i) ht
    have hmul₂ := Nat.mul_le_mul_right (qSeq s i) htlo
    rw [← blockWidth] at hmul₁
    exact ⟨ht, by omega, by omega⟩
  · refine ⟨i + 2, by omega, by omega, ?_⟩
    apply block_sum_of_window s i (i + 2) 0 n (qSeq_coprime s (by omega))
    intro t _ hthi
    have ht : t ≤ blockSize s i := by omega
    have hmul := Nat.mul_le_mul_right (qSeq s i)
      (show t ≤ qSeq s (i + 2) + 1 by omega)
    have hg₁ := blockWidth_growth s i
    have hg₂ : 4 * blockWidth s (i + 1) ≤ blockWidth s (i + 2) :=
      blockWidth_growth s (i + 1)
    exact ⟨ht, by omega, by omega⟩

/-- Every integer is a sum of two terms in blocks at distance at most two. -/
theorem cassels_nearby_representation (s : Fin 2) (n : ℕ) :
    ∃ i j, i ≤ j ∧ j ≤ i + 2 ∧
      ∃ x ∈ casselsBlock s i, ∃ y ∈ casselsBlock s j, x + y = n := by
  by_cases hn : n ≤ 2 * blockStart s 1
  · have hstart : blockStart s 1 = blockSize s 0 := by
      change 0 + blockSize s 0 * 1 = _
      omega
    rw [hstart] at hn
    refine ⟨0, 0, le_rfl, by decide, min n (blockSize s 0), ?_,
      n - min n (blockSize s 0), ?_, ?_⟩
    · refine ⟨min n (blockSize s 0), min_le_right _ _, ?_⟩
      change _ = 0 + _ * 1
      omega
    · refine ⟨n - min n (blockSize s 0), ?_, ?_⟩
      · omega
      · change _ = 0 + _ * 1
        omega
    · omega
  · have hex : ∃ j, n < 2 * blockStart s j := by
      have h : n + 1 ≤ blockStart s (n + 1) := (blockStart_strictMono s).id_le (n + 1)
      exact ⟨n + 1, by omega⟩
    let j := Nat.find hex
    have hj : n < 2 * blockStart s j := Nat.find_spec hex
    have h2 : 2 ≤ j := by
      by_contra! hl
      have h := (blockStart_strictMono s).monotone (show j ≤ 1 by omega)
      omega
    let i := j - 2
    have hir : i + 2 = j := by dsimp [i]; omega
    have hlt := Nat.find_min hex (show i + 1 < j by omega)
    obtain ⟨k, hik, hki, x, hx, y, hy, hxy⟩ :=
      cassels_cover_interval s i n (Nat.le_of_not_gt hlt) (by simpa only [hir] using hj.le)
    exact ⟨i, k, hik, hki, x, hx, y, hy, hxy⟩

theorem cassels_basis_covers (s : Fin 2) (n : ℕ) :
    ∃ x ∈ casselsBasis s, ∃ y ∈ casselsBasis s, x + y = n := by
  obtain ⟨i, j, _, _, x, hx, y, hy, hxy⟩ := cassels_nearby_representation s n
  exact ⟨x, mem_casselsBasis.2 ⟨i, hx⟩, y, mem_casselsBasis.2 ⟨j, hy⟩, hxy⟩

end

end Erdos326

-- ==== Reduction

/- Supporting lemmas for Erdős #326. The existence of the constructed basis is not proved here. -/


open scoped BigOperators
open Filter Topology


namespace Erdos326

/-- A set `S ⊆ ℕ` is an asymptotic additive basis of order 2 if every sufficiently large
    natural number is the sum of two (not necessarily distinct) elements of `S`. -/
def IsAsymptoticBasisOrder2 (S : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a ∈ S, ∃ b ∈ S, a + b = n

/-- Minimality: `S` is an asymptotic basis of order 2, and no proper subset of `S` is. -/
def IsMinimalAsymptoticBasisOrder2 (S : Set ℕ) : Prop :=
  IsAsymptoticBasisOrder2 S ∧
    ∀ a ∈ S, ¬ IsAsymptoticBasisOrder2 (S \ {a})

/-- Equivalent witness characterization of minimality: every element `a ∈ S` has infinitely
    many sums `N ∈ S + S` with no representation in `(S \ {a}) + (S \ {a})`. -/
lemma minimal_of_infinitely_many_witnesses (S : Set ℕ)
    (hbasis : IsAsymptoticBasisOrder2 S)
    (hwit : ∀ a ∈ S, ∀ M : ℕ, ∃ N ≥ M,
      (∀ x ∈ S, ∀ y ∈ S, x + y = N → x = a ∨ y = a)) :
    IsMinimalAsymptoticBasisOrder2 S := by
  refine ⟨hbasis, ?_⟩
  intro a ha hsub
  rcases hsub with ⟨N₀, hN₀⟩
  rcases hwit a ha N₀ with ⟨N, hN, huniq⟩
  rcases hN₀ N hN with ⟨x, hx, y, hy, hxy⟩
  rcases huniq x hx.1 y hy.1 hxy with rfl | rfl
  · exact hx.2 rfl
  · exact hy.2 rfl

/-- Shifting a minimal asymptotic basis of order 2 in `ℕ` by `+1` yields a minimal
    asymptotic basis of order 2 consisting strictly of positive integers. -/
def shiftOne (S : Set ℕ) : Set ℕ := (· + 1) '' S

lemma shiftOne_pos (S : Set ℕ) : ∀ x ∈ shiftOne S, 0 < x := by
  rintro x ⟨a, _, rfl⟩
  exact Nat.succ_pos a

lemma shiftOne_minimal (S : Set ℕ) (hS : IsMinimalAsymptoticBasisOrder2 S) :
    IsMinimalAsymptoticBasisOrder2 (shiftOne S) := by
  rcases hS with ⟨⟨N₀, hbasis⟩, hmin⟩
  refine ⟨⟨N₀ + 2, ?_⟩, ?_⟩
  · intro n hn
    have hge : n - 2 ≥ N₀ := by omega
    rcases hbasis (n - 2) hge with ⟨a, ha, b, hb, hab⟩
    refine ⟨a + 1, ⟨a, ha, rfl⟩, b + 1, ⟨b, hb, rfl⟩, ?_⟩
    omega
  · rintro _ ⟨a, ha, rfl⟩ ⟨N₁, hsub⟩
    apply hmin a ha
    refine ⟨N₁, ?_⟩
    intro n hn
    have hge : n + 2 ≥ N₁ := by omega
    rcases hsub (n + 2) hge with ⟨x, ⟨⟨a', ha', rfl⟩, hxne⟩, y, ⟨⟨b', hb', rfl⟩, hyne⟩, hxy⟩
    refine ⟨a', ⟨ha', ?_⟩, b', ⟨hb', ?_⟩, ?_⟩
    · intro heq; subst heq; exact hxne rfl
    · intro heq; subst heq; exact hyne rfl
    · change a' + 1 + (b' + 1) = n + 2 at hxy
      omega

/-- Quadratic bin boundary `b m = ⌊m^2 / 10000⌋`. -/
def quadBin (m : ℕ) : ℕ := m ^ 2 / 10000

private lemma quadBin_bounds (m : ℕ) :
    (m : ℝ) ^ 2 / 10000 - 1 ≤ (quadBin m : ℝ) ∧
    (quadBin m : ℝ) ≤ (m : ℝ) ^ 2 / 10000 := by
  have hlo : m ^ 2 < 10000 * (quadBin m + 1) :=
    Nat.lt_mul_div_succ _ (by decide)
  have hhi : quadBin m * 10000 ≤ m ^ 2 :=
    Nat.div_mul_le_self _ _
  constructor
  · have h : (m : ℝ) ^ 2 < 10000 * ((quadBin m : ℝ) + 1) := by exact_mod_cast hlo
    linarith
  · have h : (quadBin m : ℝ) * 10000 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hhi
    linarith

private lemma tendsto_ratio (d : ℝ) :
    Tendsto (fun k : ℕ => ((k : ℝ) + d) / (k : ℝ)) atTop (𝓝 1) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := d)).div_atTop hcast)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

/-- A bounded error in the running count implies the normalized enumeration has a limit. -/
lemma quadratic_limit_of_bin_count (C : Set ℕ) (hinf : C.Infinite)
    [DecidablePred (· ∈ C)] (m₀ E : ℕ)
    (hcount : ∀ m ≥ m₀,
      m ≤ Nat.count (· ∈ C) (quadBin m + 1) ∧
      Nat.count (· ∈ C) (quadBin m + 1) ≤ m + E) :
    Tendsto (fun k : ℕ => (Nat.nth (· ∈ C) k : ℝ) / (k : ℝ) ^ 2)
      atTop (𝓝 ((1 : ℝ) / 10000)) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have herror : Tendsto (fun k : ℕ => 1 / (k : ℝ) ^ 2) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hcast)
  have hlo := (((tendsto_ratio (-(E : ℝ) - 1)).pow 2).div_const 10000).sub herror
  have hhi := ((tendsto_ratio 1).pow 2).div_const 10000
  simp only [one_pow, sub_zero] at hlo hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (m₀ + E + 2)] with k hk
    have hpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hp := (hcount (k - (E + 1)) (by omega)).2
    have hindex : quadBin (k - (E + 1)) + 1 ≤ Nat.nth (· ∈ C) k :=
      (Nat.count_le_iff_le_nth (p := (· ∈ C)) hinf).mp (by omega)
    have hcastSub : ((k - (E + 1) : ℕ) : ℝ) = (k : ℝ) + (-(E : ℝ) - 1) := by
      rw [Nat.cast_sub (show E + 1 ≤ k by omega), Nat.cast_add, Nat.cast_one]
      ring
    have hb := (quadBin_bounds (k - (E + 1))).1
    rw [hcastSub] at hb
    have hindex' : (quadBin (k - (E + 1)) : ℝ) ≤ (Nat.nth (· ∈ C) k : ℝ) := by
      exact_mod_cast (Nat.le_of_succ_le hindex)
    calc
      _ = (((k : ℝ) + (-(E : ℝ) - 1)) ^ 2 / 10000 - 1) / (k : ℝ) ^ 2 := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (hb.trans hindex') (by positivity)
  · filter_upwards [eventually_ge_atTop (m₀ + 1)] with k hk
    have hpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hp := (hcount (k + 1) (by omega)).1
    have hindex : Nat.nth (· ∈ C) k < quadBin (k + 1) + 1 :=
      (Nat.lt_nth_iff_count_lt (p := (· ∈ C)) hinf).mp (by omega)
    have hindex' : (Nat.nth (· ∈ C) k : ℝ) ≤ (quadBin (k + 1) : ℝ) := by
      exact_mod_cast (Nat.lt_succ_iff.mp hindex)
    have hb := (quadBin_bounds (k + 1)).2
    push_cast at hb
    calc
      _ ≤ (((k : ℝ) + 1) ^ 2 / 10000) / (k : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (hindex'.trans hb) (by positivity)
      _ = _ := by field_simp

private lemma basis_mono {S T : Set ℕ} (h : S ⊆ T) :
    IsAsymptoticBasisOrder2 S → IsAsymptoticBasisOrder2 T := by
  rintro ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨a, ha, b, hb, hab⟩
  exact ⟨a, h ha, b, h hb, hab⟩

/-- A basis with unbounded indispensable sums and the stated bin counts gives
    an affirmative answer. The construction supplying these hypotheses is separate. -/
theorem exists_of_stage_properties (C : Set ℕ) (hinf : C.Infinite)
    [DecidablePred (· ∈ C)] (m₀ E : ℕ)
    (hbasis : IsAsymptoticBasisOrder2 C)
    (hwit : ∀ a ∈ C, ∀ M : ℕ, ∃ N ≥ M,
      ∀ x ∈ C, ∀ y ∈ C, x + y = N → x = a ∨ y = a)
    (hcount : ∀ m ≥ m₀,
      m ≤ Nat.count (· ∈ C) (quadBin m + 1) ∧
      Nat.count (· ∈ C) (quadBin m + 1) ≤ m + E) :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 (1 / 10000 : ℝ)) := by
  have hrange : Set.range (Nat.nth (· ∈ C)) = C := Nat.range_nth_of_infinite hinf
  refine ⟨Nat.nth (· ∈ C), Nat.nth_strictMono hinf, ?_,
    quadratic_limit_of_bin_count C hinf m₀ E hcount⟩
  rw [hrange]
  refine ⟨hbasis, ?_⟩
  intro T hT hTC a ha
  by_contra haT
  have hsub : T ⊆ C \ {a} := by
    intro t ht
    refine ⟨hTC ht, ?_⟩
    rw [Set.mem_singleton_iff]
    exact fun heq => haT (heq ▸ ht)
  exact (minimal_of_infinitely_many_witnesses C hbasis hwit).2 a ha (basis_mono hsub hT)

end Erdos326


-- ==== Assembly



open Filter Topology

namespace Erdos326

/-- A finite set with certified coverage and counting bounds through a complete bin. -/
structure FinitePrefix (m₀ E : ℕ) where
  index : ℕ
  points : Finset ℕ
  index_ge : m₀ ≤ index
  bounded : ∀ x ∈ points, x ≤ quadBin index
  coverage : ∀ n ≤ quadBin index, ∃ x ∈ points, ∃ y ∈ points, x + y = n
  counts : ∀ j, m₀ ≤ j → j ≤ index →
    j ≤ (points.filter (· ≤ quadBin j)).card ∧
    (points.filter (· ≤ quadBin j)).card ≤ j + E

variable {m₀ E : ℕ}

def FinitePrefix.Extends (p q : FinitePrefix m₀ E) : Prop :=
  p.index < q.index ∧
  ∀ x ≤ quadBin p.index, x ∈ q.points ↔ x ∈ p.points

def FinitePrefix.HasWitness (p : FinitePrefix m₀ E) (a lower : ℕ) : Prop :=
  ∃ n, lower ≤ n ∧ n ≤ quadBin p.index ∧
    ∀ x ∈ p.points, ∀ y ∈ p.points, x + y = n → x = a ∨ y = a

lemma FinitePrefix.zero_mem (p : FinitePrefix m₀ E) : 0 ∈ p.points := by
  obtain ⟨x, hx, y, _, hxy⟩ := p.coverage 0 (Nat.zero_le _)
  rwa [show x = 0 by omega] at hx

lemma FinitePrefix.Extends.subset {p q : FinitePrefix m₀ E} (h : p.Extends q) :
    p.points ⊆ q.points := by
  intro x hx
  exact (h.2 x (p.bounded x hx)).2 hx

lemma quadBin_monotone : Monotone quadBin := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.pow_le_pow_left hij 2)

lemma quadBin_cofinal (x : ℕ) : x ≤ quadBin (10000 * (x + 1)) := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2
  nlinarith

private lemma infinite_of_basis {C : Set ℕ} (h : IsAsymptoticBasisOrder2 C) : C.Infinite := by
  intro hfinite
  obtain ⟨B, hB⟩ := Set.finite_iff_bddAbove.mp hfinite
  obtain ⟨N, hN⟩ := h
  obtain ⟨x, hx, y, hy, hxy⟩ := hN (N + 2 * B + 1) (by omega)
  have hxB : x ≤ B := hB hx
  have hyB : y ≤ B := hB hy
  omega

/-- A valid finite extension at every stage suffices to construct the desired infinite set.
    The validity predicate can carry auxiliary invariants specific to the extension proof. -/
theorem exists_of_prefix_extensions (Valid : FinitePrefix m₀ E → Prop)
    (initial : FinitePrefix m₀ E) (hinit : Valid initial)
    (advance : ∀ p, Valid p → ∀ a ∈ p.points, ∃ q, Valid q ∧
      p.Extends q ∧ q.HasWitness a (quadBin p.index + 1)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 (1 / 10000 : ℝ)) := by
  classical
  let Active := {p : FinitePrefix m₀ E // Valid p}
  have chooseStep (p : Active) (a : ℕ) :
      ∃ q : Active, p.val.Extends q.val ∧
        (a ∈ p.val.points → q.val.HasWitness a (quadBin p.val.index + 1)) := by
    by_cases ha : a ∈ p.val.points
    · obtain ⟨q, hq, he, hw⟩ := advance p.val p.property a ha
      exact ⟨⟨q, hq⟩, he, fun _ => hw⟩
    · obtain ⟨q, hq, he, _⟩ := advance p.val p.property 0 p.val.zero_mem
      exact ⟨⟨q, hq⟩, he, fun h => (ha h).elim⟩
  let stages : ℕ → Active := fun k =>
    Nat.rec ⟨initial, hinit⟩
      (fun j p => (chooseStep p (Nat.unpair j).1).choose) k
  let p (k : ℕ) : FinitePrefix m₀ E := (stages k).val
  let cutoff (k : ℕ) : ℕ := quadBin (p k).index
  have hstep (k : ℕ) : (p k).Extends (p (k + 1)) ∧
      ((Nat.unpair k).1 ∈ (p k).points →
        (p (k + 1)).HasWitness (Nat.unpair k).1 (cutoff k + 1)) :=
    (chooseStep (stages k) (Nat.unpair k).1).choose_spec
  have hindex : StrictMono (fun k => (p k).index) :=
    strictMono_nat_of_lt_succ fun k => (hstep k).1.1
  have hcut : Monotone cutoff := quadBin_monotone.comp hindex.monotone
  have hlarge (x : ℕ) : x ≤ cutoff (10000 * (x + 1)) :=
    (quadBin_cofinal x).trans (quadBin_monotone (hindex.id_le _))
  have hmono : Monotone (fun k => (p k).points) :=
    monotone_nat_of_le_succ fun k => (hstep k).1.subset
  have hfreeze (i j : ℕ) (hij : i ≤ j) (x : ℕ) (hx : x ≤ cutoff i)
      (hm : x ∈ (p j).points) : x ∈ (p i).points := by
    induction j, hij using Nat.le_induction with
    | base => exact hm
    | succ j hij ih =>
      exact ih (((hstep j).1.2 x (hx.trans (hcut hij))).1 hm)
  let C : Set ℕ := ⋃ k : ℕ, (↑(p k).points : Set ℕ)
  have hmem (x k : ℕ) (hx : x ≤ cutoff k) : x ∈ C ↔ x ∈ (p k).points := by
    constructor
    · intro hxC
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxC
      by_cases hik : i ≤ k
      · exact hmono hik hi
      · exact hfreeze k i (by omega) x hx hi
    · intro hxP
      exact Set.mem_iUnion.mpr ⟨k, hxP⟩
  have hb : IsAsymptoticBasisOrder2 C := by
    refine ⟨0, fun n _ => ?_⟩
    let k := 10000 * (n + 1)
    obtain ⟨x, hx, y, hy, hxy⟩ := (p k).coverage n (hlarge n)
    exact ⟨x, (hmem x k ((p k).bounded x hx)).2 hx,
      y, (hmem y k ((p k).bounded y hy)).2 hy, hxy⟩
  have hi : C.Infinite := infinite_of_basis hb
  have hw : ∀ a ∈ C, ∀ M : ℕ, ∃ n ≥ M,
      ∀ x ∈ C, ∀ y ∈ C, x + y = n → x = a ∨ y = a := by
    intro a ha M
    obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
    let k := Nat.pair a (max i (10000 * (M + 1)))
    have hik : i ≤ k := (le_max_left _ _).trans (Nat.right_le_pair _ _)
    have hMk : 10000 * (M + 1) ≤ k := (le_max_right _ _).trans (Nat.right_le_pair _ _)
    have hk : (Nat.unpair k).1 = a := by simp [k]
    have hak : a ∈ (p k).points := hmono hik hai
    have h := (hstep k).2
    rw [hk] at h
    obtain ⟨n, hl, hu, hn⟩ := h hak
    refine ⟨n, (hlarge M).trans ((hcut hMk).trans (by omega)), ?_⟩
    intro x hx y hy hxy
    have hxc : x ≤ cutoff (k + 1) := by
      change n ≤ cutoff (k + 1) at hu
      omega
    have hyc : y ≤ cutoff (k + 1) := by
      change n ≤ cutoff (k + 1) at hu
      omega
    exact hn x ((hmem x (k + 1) hxc).1 hx) y ((hmem y (k + 1) hyc).1 hy) hxy
  have hcount (j : ℕ) (hj : m₀ ≤ j) :
      j ≤ Nat.count (· ∈ C) (quadBin j + 1) ∧
      Nat.count (· ∈ C) (quadBin j + 1) ≤ j + E := by
    have hjp : j ≤ (p j).index := hindex.id_le j
    have hf : (Finset.range (quadBin j + 1)).filter (· ∈ C) =
        (p j).points.filter (· ≤ quadBin j) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      rw [Nat.lt_succ_iff]
      constructor
      · rintro ⟨hx, hxC⟩
        exact ⟨(hmem x j (hx.trans (quadBin_monotone hjp))).1 hxC, hx⟩
      · rintro ⟨hxP, hx⟩
        exact ⟨hx, (hmem x j (hx.trans (quadBin_monotone hjp))).2 hxP⟩
    rw [Nat.count_eq_card_filter_range, hf]
    exact (p j).counts j hj hjp
  exact exists_of_stage_properties C hi m₀ E hb hw hcount

end Erdos326

-- ==== Spacing



namespace Erdos326

private lemma half_open_block {s : Fin 2} {x : ℕ} (hx : x ∈ casselsBasis s) :
    ∃ i, x ∈ casselsBlock s i ∧ x < blockStart s (i + 1) := by
  obtain ⟨i, hi⟩ := mem_casselsBasis.1 hx
  have hle := (mem_casselsBlock_bounds hi).2
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact ⟨i, hi, hlt⟩
  · refine ⟨i + 1, ⟨0, Nat.zero_le _, by simpa using heq⟩, ?_⟩
    rw [heq]
    exact blockStart_strictMono s (by omega)

private lemma blockStart_le_step_squared (s : Fin 2) {i : ℕ} (hi : 0 < i) :
    blockStart s (i + 1) ≤ 96 * qSeq s i ^ 2 := by
  have h := (qSeq_bounds_of_pos s hi).1.le
  calc
    _ ≤ 6 * scale s ^ 2 * 16 ^ (i + 1) := blockStart_le s _
    _ = 96 * (scale s * 4 ^ i) ^ 2 := by
      rw [pow_succ, show (16 : ℕ) = 4 * 4 by decide, mul_pow]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)

/-- Distinct terms of the same Cassels basis are separated at the square-root scale. -/
theorem cassels_gap {s : Fin 2} {x y : ℕ}
    (hx : x ∈ casselsBasis s) (hy : y ∈ casselsBasis s)
    (hx₀ : blockStart s 1 ≤ x) (hxy : x < y) :
    x < 96 * (y - x) ^ 2 := by
  obtain ⟨i, hix, hxi⟩ := half_open_block hx
  obtain ⟨j, hjy, hyj⟩ := half_open_block hy
  have hi : 0 < i := by
    by_contra! h
    have hi0 : i = 0 := by omega
    subst i
    exact (not_lt_of_ge hx₀) (show x < blockStart s 1 from hxi)
  have hij : i ≤ j := by
    by_contra! h
    have hstart := (blockStart_strictMono s).monotone (show j + 1 ≤ i by omega)
    exact (not_lt_of_ge ((mem_casselsBlock_bounds hix).1.trans' (hyj.le.trans hstart))) hxy
  have hgap : qSeq s i ≤ y - x := by
    rcases lt_or_eq_of_le hij with hlt | rfl
    · obtain ⟨t, ht, hxt⟩ := hix
      have htt : t < blockSize s i := by
        by_contra! h
        have heq : t = blockSize s i := by omega
        rw [heq, ← blockWidth, ← blockStart_succ] at hxt
        omega
      have hm := Nat.mul_le_mul_right (qSeq s i) (Nat.succ_le_of_lt htt)
      rw [Nat.succ_mul, ← blockWidth] at hm
      have hs : blockStart s (i + 1) ≤ blockStart s j :=
        (blockStart_strictMono s).monotone (Nat.succ_le_of_lt hlt)
      have hs' := (mem_casselsBlock_bounds hjy).1
      have he := blockStart_succ s i
      omega
    · obtain ⟨t, _, hxt⟩ := hix
      obtain ⟨u, _, hyu⟩ := hjy
      have htu : t + 1 ≤ u := by
        by_contra! h
        have hm := Nat.mul_le_mul_right (qSeq s i) (show u ≤ t by omega)
        omega
      have hm := Nat.mul_le_mul_right (qSeq s i) htu
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
  exact hxi.trans_le ((blockStart_le_step_squared s hi).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgap 2)))

private lemma close_within_three_bins {m x y : ℕ} (hm : 10009 ≤ m)
    (hx : quadBin m < x) (hy : y ≤ quadBin (m + 3)) :
    100 * (y - x) ^ 2 ≤ x := by
  have hlo : m ^ 2 < 10000 * (quadBin m + 1) := Nat.lt_mul_div_succ _ (by decide)
  have hhi : 10000 * quadBin (m + 3) ≤ (m + 3) ^ 2 := by
    rw [Nat.mul_comm, quadBin]
    exact Nat.div_mul_le_self _ _
  by_cases hxy : x ≤ y
  · have hquad : (m + 3) ^ 2 = m ^ 2 + 6 * m + 9 := by ring
    rw [hquad] at hhi
    have hΔ : 10000 * (y - x) ≤ 7 * m := by omega
    have hpow := Nat.pow_le_pow_left hΔ 2
    have hx' : m ^ 2 < 10000 * x := by omega
    nlinarith only [hpow, hx']
  · simp [Nat.sub_eq_zero_of_le (by omega : y ≤ x)]

/-- After the initial bins, three consecutive quadratic bins contain at most one
    element of either individual Cassels basis. -/
theorem card_basis_in_three_bins_le_one (s : Fin 2) (m : ℕ) (hm : 10009 ≤ m)
    (F : Finset ℕ)
    (hF : ∀ x ∈ F, x ∈ casselsBasis s ∧ quadBin m < x ∧ x ≤ quadBin (m + 3)) :
    F.card ≤ 1 := by
  have hstart : blockStart s 1 ≤ quadBin m := by
    have h := (blockSize_bounds s 0).2
    have hs : blockStart s 1 = blockSize s 0 := by
      change 0 + blockSize s 0 * 1 = _
      omega
    have hb : 10000 ≤ quadBin m :=
      (show 10000 ≤ quadBin 10000 by decide).trans (quadBin_monotone (by omega))
    rw [hs]
    rcases scale_cases s with h₀ | h₀ <;> rw [h₀] at h <;> norm_num at h <;> omega
  have impossible (x y : ℕ) (hx : x ∈ F) (hy : y ∈ F) (hxy : x < y) : False := by
    obtain ⟨hxB, hxlo, _⟩ := hF x hx
    obtain ⟨hyB, _, hyhi⟩ := hF y hy
    have hgap := cassels_gap hxB hyB (hstart.trans hxlo.le) hxy
    have hclose := close_within_three_bins hm hxlo hyhi
    omega
  apply Finset.card_le_one.2
  intro x hx y hy
  rcases lt_trichotomy x y with h | h | h
  · exact (impossible x y hx hy h).elim
  · exact h
  · exact (impossible y x hy hx h).elim

/-- Both bases together contribute at most two points per group of three bins. -/
theorem card_union_in_three_bins_le_two (m : ℕ) (hm : 10009 ≤ m)
    (F : Finset ℕ)
    (hF : ∀ x ∈ F, x ∈ casselsBasis 0 ∪ casselsBasis 1 ∧
      quadBin m < x ∧ x ≤ quadBin (m + 3)) :
    F.card ≤ 2 := by
  classical
  let F₀ := F.filter (· ∈ casselsBasis 0)
  let F₁ := F.filter (· ∈ casselsBasis 1)
  have hc (s : Fin 2) : (F.filter (· ∈ casselsBasis s)).card ≤ 1 := by
    apply card_basis_in_three_bins_le_one s m hm
    intro x hx
    obtain ⟨hxF, hxB⟩ := Finset.mem_filter.1 hx
    exact ⟨hxB, (hF x hxF).2⟩
  have hsub : F ⊆ F₀ ∪ F₁ := by
    intro x hx
    rcases (hF x hx).1 with h | h
    · exact Finset.mem_union.2 (.inl (Finset.mem_filter.2 ⟨hx, h⟩))
    · exact Finset.mem_union.2 (.inr (Finset.mem_filter.2 ⟨hx, h⟩))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le F₀ F₁).trans
    (Nat.add_le_add (hc 0) (hc 1)))

end Erdos326

-- ==== Collateral



open scoped BigOperators

namespace Erdos326

/-- The selected representation records the block of each summand. -/
structure CasselsPair (s : Fin 2) (n : ℕ) where
  i : ℕ
  j : ℕ
  x : ℕ
  y : ℕ
  idx_le : i ≤ j
  idx_close : j ≤ i + 2
  left_mem : x ∈ casselsBlock s i
  right_mem : y ∈ casselsBlock s j
  sum_eq : x + y = n

theorem nonempty_casselsPair (s : Fin 2) (n : ℕ) : Nonempty (CasselsPair s n) := by
  obtain ⟨i, j, hi, hj, x, hx, y, hy, hxy⟩ := cassels_nearby_representation s n
  exact ⟨⟨i, j, x, y, hi, hj, hx, hy, hxy⟩⟩

noncomputable def casselsPair (s : Fin 2) (n : ℕ) : CasselsPair s n :=
  Classical.choice (nonempty_casselsPair s n)

def Hits (D : Finset ℕ) (s : Fin 2) (n : ℕ) : Prop :=
  (casselsPair s n).x ∈ D ∨ (casselsPair s n).y ∈ D

private lemma hit_witness {D : Finset ℕ} {s : Fin 2} {n : ℕ}
    (h : Hits D s n) :
    ∃ d ∈ D, ∃ i j, ∃ z ∈ casselsBlock s j,
      d ∈ casselsBlock s i ∧ j ≤ i + 2 ∧ i ≤ j + 2 ∧ d + z = n := by
  let r := casselsPair s n
  rcases h with hx | hy
  · exact ⟨r.x, hx, r.i, r.j, r.y, r.right_mem, r.left_mem, r.idx_close,
      r.idx_le.trans (Nat.le_add_right _ _), r.sum_eq⟩
  · exact ⟨r.y, hy, r.j, r.i, r.x, r.left_mem, r.right_mem,
      r.idx_le.trans (Nat.le_add_right _ _), r.idx_close, (Nat.add_comm _ _).trans r.sum_eq⟩

private lemma ge_index_of_mem_above {s : Fin 2} {i d k : ℕ}
    (hd : d ∈ casselsBlock s i) (hk : blockStart s k < d) : k ≤ i := by
  by_contra! h
  exact (not_lt_of_ge ((mem_casselsBlock_bounds hd).2.trans
    ((blockStart_strictMono s).monotone (Nat.succ_le_of_lt h)))) hk

/-- A deletion in `(L,U]` can only destroy the chosen representation in a bounded larger range. -/
theorem hit_sum_bounds {D : Finset ℕ} {s : Fin 2} {n L U : ℕ}
    (hL : blockStart s 2 ≤ L) (hD : ∀ d ∈ D, L < d ∧ d ≤ U)
    (h : Hits D s n) : L < n ∧ n ≤ 24577 * U := by
  obtain ⟨d, hdD, i, j, z, hz, hd, hj, _, hsum⟩ := hit_witness h
  obtain ⟨hdl, hdu⟩ := hD d hdD
  have hi := ge_index_of_mem_above hd (hL.trans_lt hdl)
  have hscale := (le_blockStart s hi).trans (mem_casselsBlock_bounds hd).1
  have hzle : z ≤ 24576 * d := calc
    z ≤ blockStart s (j + 1) := (mem_casselsBlock_bounds hz).2
    _ ≤ blockStart s (i + 3) := (blockStart_strictMono s).monotone (by omega)
    _ ≤ 6 * scale s ^ 2 * 16 ^ (i + 3) := blockStart_le s _
    _ = 24576 * (scale s ^ 2 * 16 ^ i) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hscale
  omega

/-- The intersection of two translated bounded progressions with coprime steps. -/
theorem card_of_coprime_progressions {F : Finset ℕ} {a b p q M N : ℕ}
    (hp : 0 < p) (hc : p.Coprime q)
    (hF : ∀ n ∈ F, ∃ t ≤ M, ∃ u ≤ N, n = a + t * p ∧ n = b + u * q) :
    F.card ≤ M / q + 1 := by
  let coord (n : ℕ) := (n - a) / p
  have hcoord (n : ℕ) (hn : n ∈ F) :
      n = a + coord n * p ∧ coord n ≤ M ∧ n ≡ b [MOD q] := by
    obtain ⟨t, ht, u, _, hna, hnb⟩ := hF n hn
    have hsub : n - a = t * p := by omega
    have heq : coord n = t := by
      rw [show coord n = (n - a) / p by rfl, hsub, Nat.mul_div_cancel _ hp]
    refine ⟨by rwa [heq], by rwa [heq], ?_⟩
    rw [hnb]
    have hd : q ∣ u * q := ⟨u, Nat.mul_comm _ _⟩
    simpa only [Nat.add_zero] using (Nat.modEq_zero_iff_dvd.2 hd).add_left b
  rw [← Finset.card_range (M / q + 1)]
  apply Finset.card_le_card_of_injOn (fun n => coord n / q)
  · intro n hn
    have hh := Nat.div_le_div_right (c := q) (hcoord n hn).2.1
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hh)
  · intro n hn m hm heq
    obtain ⟨hna, _, hnb⟩ := hcoord n hn
    obtain ⟨hma, _, hmb⟩ := hcoord m hm
    have hmod := hnb.trans hmb.symm
    rw [hna, hma] at hmod
    have hrem := Nat.ModEq.cancel_right_of_coprime hc.symm
      (Nat.ModEq.add_left_cancel' a hmod)
    have hcEq : coord n = coord m := by
      change coord n / q = coord m / q at heq
      change coord n % q = coord m % q at hrem
      calc
        coord n = coord n % q + q * (coord n / q) := (Nat.mod_add_div _ _).symm
        _ = coord m % q + q * (coord m / q) := by rw [heq, hrem]
        _ = coord m := Nat.mod_add_div _ _
    rw [hna, hma, hcEq]

private lemma block_indices_close {s t : Fin 2} {i j d e : ℕ}
    (hi : 2 ≤ i) (hd : d ∈ casselsBlock s i) (he : e ∈ casselsBlock t j)
    (hratio : d ≤ 3 * e) : i ≤ j + 2 := by
  by_contra! hlarge
  have hlo := (le_blockStart s hi).trans (mem_casselsBlock_bounds hd).1
  have hhi := (mem_casselsBlock_bounds he).2.trans (blockStart_le t (j + 1))
  have hs : 9 ≤ scale s ^ 2 := by rcases scale_cases s with h | h <;> rw [h] <;> decide
  have ht : scale t ^ 2 ≤ 36 := by rcases scale_cases t with h | h <;> rw [h] <;> decide
  have hpow : (16 : ℕ) ^ (j + 1) * 256 ≤ 16 ^ i := by
    rw [show (256 : ℕ) = 16 ^ 2 by decide, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hd' : 2304 * 16 ^ (j + 1) ≤ d := calc
    _ = 9 * (16 ^ (j + 1) * 256) := by ring
    _ ≤ scale s ^ 2 * 16 ^ i := Nat.mul_le_mul hs hpow
    _ ≤ d := hlo
  have he' : e ≤ 216 * 16 ^ (j + 1) := calc
    e ≤ 6 * scale t ^ 2 * 16 ^ (j + 1) := hhi
    _ ≤ 216 * 16 ^ (j + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 ht)
  have hpos : 0 < (16 : ℕ) ^ (j + 1) := by positivity
  omega

private lemma blockSize_div_le {i j : ℕ} (hj : 0 < j) (hij : i ≤ j + 6) :
    blockSize 0 i / qSeq 1 j ≤ 81920 := by
  have hi := (blockSize_bounds 0 i).2
  have hq := (qSeq_bounds_of_pos 1 hj).1
  have hz : scale 0 = 3 := by decide
  have ho : scale 1 = 6 := by decide
  rw [hz] at hi
  rw [ho] at hq
  have hm : blockSize 0 i ≤ 81920 * qSeq 1 j := calc
    _ ≤ 120 * 4 ^ i := hi
    _ ≤ 120 * 4 ^ (j + 6) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hij)
    _ = 81920 * (6 * 4 ^ j) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hq.le
  calc
    _ ≤ (81920 * qSeq 1 j) / qSeq 1 j := Nat.div_le_div_right hm
    _ = _ := Nat.mul_div_cancel _ (qSeq_pos 1 j)

/-- A bounded deletion set disables both selected representations at only a bounded
    number of integers. The bound is uniform in the numerical location of the stage. -/
theorem collateral_card_le {D H : Finset ℕ} {L U : ℕ}
    (hL : ∀ s : Fin 2, blockStart s 4 ≤ L) (hU : U ≤ 3 * L)
    (hD : ∀ d ∈ D, L < d ∧ d ≤ U)
    (hH : ∀ n ∈ H, Hits D 0 n ∧ Hits D 1 n) :
    H.card ≤ 49 * 81921 * D.card ^ 2 := by
  classical
  let active (i : ℕ) := ∃ s : Fin 2, ∃ d, L < d ∧ d ≤ U ∧ d ∈ casselsBlock s i
  by_cases hex : ∃ i, active i
  · let lo := Nat.find hex
    obtain ⟨s₀, d₀, hd₀l, _, hd₀⟩ := Nat.find_spec hex
    have hlo : 4 ≤ lo := ge_index_of_mem_above hd₀ ((hL s₀).trans_lt hd₀l)
    have active_bounds {i : ℕ} (hi : active i) : lo ≤ i ∧ i ≤ lo + 2 := by
      have hl := Nat.find_min' hex hi
      obtain ⟨s, d, hdl, hdu, hd⟩ := hi
      have hi4 : 4 ≤ i := ge_index_of_mem_above hd ((hL s).trans_lt hdl)
      exact ⟨hl, block_indices_close (by omega) hd hd₀ (by omega)⟩
    let I : Finset ℕ := Finset.Icc (lo - 2) (lo + 4)
    let keys := (D ×ˢ D) ×ˢ (I ×ˢ I)
    let slice (key : (ℕ × ℕ) × (ℕ × ℕ)) := H.filter fun n =>
      (∃ x ∈ casselsBlock 0 key.2.1, key.1.1 + x = n) ∧
      (∃ y ∈ casselsBlock 1 key.2.2, key.1.2 + y = n)
    have hcover : H ⊆ keys.biUnion slice := by
      intro n hn
      obtain ⟨h₀, h₁⟩ := hH n hn
      obtain ⟨d, hdd, i, j, x, hx, hd, hj, hi, hdx⟩ := hit_witness h₀
      obtain ⟨e, hee, k, l, y, hy, he, hl, hk, hey⟩ := hit_witness h₁
      obtain ⟨hdi, hid⟩ := active_bounds ⟨0, d, (hD d hdd).1, (hD d hdd).2, hd⟩
      obtain ⟨hek, hke⟩ := active_bounds ⟨1, e, (hD e hee).1, (hD e hee).2, he⟩
      have hjI : j ∈ I := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hlI : l ∈ I := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      exact Finset.mem_biUnion.2 ⟨((d, e), (j, l)),
        Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hdd, hee⟩, Finset.mem_product.2 ⟨hjI, hlI⟩⟩,
        Finset.mem_filter.2 ⟨hn, ⟨x, hx, hdx⟩, ⟨y, hy, hey⟩⟩⟩
    have hslice (key : (ℕ × ℕ) × (ℕ × ℕ)) (hk : key ∈ keys) : (slice key).card ≤ 81921 := by
      rcases key with ⟨⟨d, e⟩, ⟨i, j⟩⟩
      obtain ⟨hiI, hjI⟩ := Finset.mem_product.1 (Finset.mem_product.1 hk).2
      have hi : lo - 2 ≤ i ∧ i ≤ lo + 4 := Finset.mem_Icc.1 hiI
      have hj : lo - 2 ≤ j ∧ j ≤ lo + 4 := Finset.mem_Icc.1 hjI
      have hlocal (n : ℕ) (hn : n ∈ slice ((d, e), (i, j))) :
          ∃ t ≤ blockSize 0 i, ∃ u ≤ blockSize 1 j,
            n = (d + blockStart 0 i) + t * qSeq 0 i ∧
            n = (e + blockStart 1 j) + u * qSeq 1 j := by
        obtain ⟨⟨x, ⟨t, ht, rfl⟩, hx⟩, ⟨y, ⟨u, hu, rfl⟩, hy⟩⟩ :=
          (Finset.mem_filter.1 hn).2
        change d + (blockStart 0 i + t * qSeq 0 i) = n at hx
        change e + (blockStart 1 j + u * qSeq 1 j) = n at hy
        exact ⟨t, ht, u, hu, by omega, by omega⟩
      have h := card_of_coprime_progressions (qSeq_pos 0 i)
        (qSeq_coprime_cross i j) hlocal
      have hr := blockSize_div_le (i := i) (j := j) (by omega) (by omega)
      omega
    have hI : I.card = 7 := by
      change (Finset.Icc (lo - 2) (lo + 4)).card = 7
      rw [Nat.card_Icc]
      omega
    calc
      H.card ≤ (keys.biUnion slice).card := Finset.card_le_card hcover
      _ ≤ ∑ key ∈ keys, (slice key).card := Finset.card_biUnion_le
      _ ≤ ∑ key ∈ keys, (81921 : ℕ) := Finset.sum_le_sum hslice
      _ = 49 * 81921 * D.card ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [keys, Finset.card_product, hI, Nat.cast_id]
        ring
  · have hempty : H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro n hn
      obtain ⟨d, hdd, i, _, _, _, hd, _, _, _⟩ := hit_witness (hH n hn).1
      exact hex ⟨i, 0, d, (hD d hdd).1, (hD d hdd).2, hd⟩
    simp [hempty]

end Erdos326

-- ==== Witness



open scoped BigOperators

namespace Erdos326

def Represented (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x + y = n

def AllRepresentationsUse (S : Finset ℕ) (a n : ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x + y = n → x = a ∨ y = a

lemma Represented.mono {S T : Finset ℕ} {n : ℕ} (h : Represented S n) (hST : S ⊆ T) :
    Represented T n := by
  obtain ⟨x, hx, y, hy, he⟩ := h
  exact ⟨x, hST hx, y, hST hy, he⟩

/-- Each unordered non-diagonal representation contributes its larger summand. -/
def upperEndpoints (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.filter fun y => y ≤ n ∧ n - y < y ∧ n - y ∈ S

lemma upperEndpoints_above {S : Finset ℕ} {L n y : ℕ}
    (h : 2 * L < n) (hy : y ∈ upperEndpoints S n) : L < y := by
  obtain ⟨_, hle, hlt, _⟩ := Finset.mem_filter.1 hy
  omega

/-- Averaging over a finite set of targets bounds the number of deletions
    needed to annihilate the representations of at least one target. -/
theorem exists_target_with_few_endpoints (S targets : Finset ℕ) (budget : ℕ)
    (hbudget : S.card ^ 2 < targets.card * budget) :
    ∃ n ∈ targets, (upperEndpoints S n).card < budget := by
  let family := targets.sigma (upperEndpoints S)
  have hcard : family.card ≤ (S ×ˢ S).card := by
    apply Finset.card_le_card_of_injOn
      (fun z : Σ _ : ℕ, ℕ => (z.1 - z.2, z.2))
    · intro z hz
      obtain ⟨_, hzm⟩ := Finset.mem_sigma.1 hz
      obtain ⟨hv, _, _, hu⟩ := Finset.mem_filter.1 hzm
      exact Finset.mem_product.2 ⟨hu, hv⟩
    · rintro ⟨n, y⟩ hz ⟨m, v⟩ hw heq
      have hyn := (Finset.mem_filter.1 (Finset.mem_sigma.1 hz).2).2.1
      have hvm := (Finset.mem_filter.1 (Finset.mem_sigma.1 hw).2).2.1
      change (n - y, y) = (m - v, v) at heq
      injection heq with hsub hsum
      have hn : n = m := by
        change y ≤ n at hyn
        change v ≤ m at hvm
        omega
      subst m
      subst v
      rfl
  by_contra! h
  have hsum : targets.card * budget ≤ family.card := calc
    _ = ∑ n ∈ targets, budget := by simp [Finset.sum_const]
    _ ≤ ∑ n ∈ targets, (upperEndpoints S n).card := Finset.sum_le_sum h
    _ = _ := (Finset.card_sigma _ _).symm
  rw [Finset.card_product, ← sq] at hcard
  omega

/-- For an odd target the larger summands suffice, since there are no diagonal sums. -/
theorem not_represented_after_deleting_endpoints (S : Finset ℕ) {n : ℕ} (hn : Odd n) :
    ¬ Represented (S \ upperEndpoints S n) n := by
  have hpar := Nat.odd_iff.1 hn
  rintro ⟨x, hx, y, hy, hxy⟩
  obtain ⟨hxS, hxD⟩ := Finset.mem_sdiff.1 hx
  obtain ⟨hyS, hyD⟩ := Finset.mem_sdiff.1 hy
  by_cases h : x < y
  · exact hyD (Finset.mem_filter.2 ⟨hyS, by omega, by omega, by rwa [show n - y = x by omega]⟩)
  · exact hxD (Finset.mem_filter.2 ⟨hxS, by omega, by omega, by rwa [show n - x = y by omega]⟩)

theorem install_witness {S : Finset ℕ} {a n : ℕ} (ha : a ∈ S) (han : a ≤ n)
    (hs : ¬ Represented S n) :
    Represented (insert (n - a) S) n ∧ AllRepresentationsUse (insert (n - a) S) a n := by
  refine ⟨⟨a, Finset.mem_insert_of_mem ha, n - a, Finset.mem_insert_self _ _, by omega⟩, ?_⟩
  intro x hx y hy he
  rcases Finset.mem_insert.1 hx with h | hx
  · exact .inr (by omega)
  rcases Finset.mem_insert.1 hy with h | hy
  · exact .inl (by omega)
  · exact (hs ⟨x, hx, y, hy, he⟩).elim

/-- A non-diagonal new summand whose complement is absent preserves a witness. -/
lemma retain_witness_after_insert {S : Finset ℕ} {a N w : ℕ} (hodd : Odd N)
    (h : AllRepresentationsUse S a N) (hmiss : ∀ x ∈ S, w + x ≠ N) :
    AllRepresentationsUse (insert w S) a N := by
  have hpar := Nat.odd_iff.1 hodd
  intro x hx y hy hsum
  rcases Finset.mem_insert.1 hx with hxe | hx
  · rcases Finset.mem_insert.1 hy with hye | hy
    · omega
    · exact (hmiss y hy (by omega)).elim
  · rcases Finset.mem_insert.1 hy with hye | hy
    · exact (hmiss x hx (by omega)).elim
    · exact h x hx y hy hsum

/-- Repair one hole by inserting a point above the previously frozen prefix. -/
theorem repair_one_hole (S : Finset ℕ) {a N n X : ℕ} (hodd : Odd N) (h0 : 0 ∈ S)
    (hforced : AllRepresentationsUse S a N) (hn : 2 * X < n) (hne : n ≠ N)
    (havoid : n < N → ∃ u ∈ S, u ≤ X ∧ u + (N - n) ∉ S) :
    ∃ w, X < w ∧ w ≤ n ∧
      Represented (insert w S) n ∧ AllRepresentationsUse (insert w S) a N := by
  by_cases h : n < N
  · obtain ⟨u, hu, hux, hum⟩ := havoid h
    let w := n - u
    refine ⟨w, by dsimp [w]; omega, Nat.sub_le _ _,
      ⟨u, Finset.mem_insert_of_mem hu, w, Finset.mem_insert_self _ _, by dsimp [w]; omega⟩, ?_⟩
    apply retain_witness_after_insert hodd hforced
    intro x hx he
    have hxe : x = u + (N - n) := by dsimp [w] at he; omega
    exact hum (hxe ▸ hx)
  · refine ⟨n, by omega, le_rfl,
      ⟨0, Finset.mem_insert_of_mem h0, n, Finset.mem_insert_self _ _, by simp⟩, ?_⟩
    apply retain_witness_after_insert hodd hforced
    intro x _
    omega

/-- Repair a finite family of holes using at most one new point per hole.
    It suffices to have an available shift for each hole below the witness target,
    uniformly over the additions already made. -/
theorem repair_holes (S H : Finset ℕ) {a N X Y : ℕ}
    (hodd : Odd N) (h0 : 0 ∈ S) (hforced : AllRepresentationsUse S a N)
    (hH : ∀ n ∈ H, 2 * X < n ∧ n ≤ Y ∧ n ≠ N)
    (havoid : ∀ P : Finset ℕ, P.card < H.card → (∀ w ∈ P, X < w ∧ w ≤ Y) →
      ∀ n ∈ H, n < N → ∃ u ∈ S ∪ P, u ≤ X ∧ u + (N - n) ∉ S ∪ P) :
    ∃ P : Finset ℕ, P.card ≤ H.card ∧ (∀ w ∈ P, X < w ∧ w ≤ Y) ∧
      (∀ n ∈ H, Represented (S ∪ P) n) ∧ AllRepresentationsUse (S ∪ P) a N := by
  suffices h : ∀ G ⊆ H, ∃ P : Finset ℕ,
      P.card ≤ G.card ∧ (∀ w ∈ P, X < w ∧ w ≤ Y) ∧
      (∀ n ∈ G, Represented (S ∪ P) n) ∧ AllRepresentationsUse (S ∪ P) a N from
    h H (fun _ hx => hx)
  intro G
  induction G using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp, by simp, by simp, by simpa using hforced⟩
  | insert n G hnG ih =>
    intro hGH
    have hnH : n ∈ H := hGH (Finset.mem_insert_self _ _)
    have hsub : G ⊆ H := fun _ hx => hGH (Finset.mem_insert_of_mem hx)
    obtain ⟨P, hpG, hpB, hpCov, hpForce⟩ := ih hsub
    have hcards : G.card + 1 ≤ H.card := by
      rw [← Finset.card_insert_of_notMem hnG]
      exact Finset.card_le_card hGH
    have hPlt : P.card < H.card := by omega
    obtain ⟨w, hwX, hwn, hRep, hForce⟩ := repair_one_hole (S ∪ P) hodd
      (Finset.mem_union_left _ h0) hpForce (hH n hnH).1 (hH n hnH).2.2
      (havoid P hPlt hpB n hnH)
    have he : insert w (S ∪ P) = S ∪ insert w P := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto
    rw [he] at hRep hForce
    refine ⟨insert w P, ?_, ?_, ?_, hForce⟩
    · rw [Finset.card_insert_of_notMem hnG]
      exact (Finset.card_insert_le w P).trans (Nat.add_le_add_right hpG 1)
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨hwX, hwn.trans (hH n hnH).2.1⟩
      · exact hpB z hz
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hRep
      · exact (hpCov z hz).mono (by
          intro v hv
          rcases Finset.mem_union.1 hv with hv | hv
          · exact Finset.mem_union_left _ hv
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hv))

end Erdos326

-- ==== Stage



namespace Erdos326

private lemma upperEndpoints_filter {S : Finset ℕ} {n B : ℕ} (hn : n ≤ B) :
    upperEndpoints (S.filter (· ≤ B)) n = upperEndpoints S n := by
  ext y
  constructor
  · intro hy
    obtain ⟨hy, hyn, hylt, hx⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, hyn, hylt, (Finset.mem_filter.1 hx).1⟩
  · intro hy
    obtain ⟨hyS, hyn, hylt, hxS⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hyS, hyn.trans hn⟩, hyn, hylt,
      Finset.mem_filter.2 ⟨hxS, (Nat.sub_le _ _).trans hn⟩⟩

/-- In a quadratic-scale window, a bounded number of deletions isolates some odd target. -/
theorem exists_odd_target (S : Finset ℕ) (m : ℕ) (hm : 200 ≤ m)
    (hS : (S.filter (· ≤ 3 * quadBin m)).card ≤ 3 * m) :
    ∃ n, 2 * quadBin m < n ∧ n ≤ 3 * quadBin m ∧ Odd n ∧
      (upperEndpoints S n).card < 400000 := by
  let L := quadBin m
  let f (k : ℕ) := 2 * L + 2 * k + 1
  let targets := (Finset.range (L / 2)).image f
  have hcard : targets.card = L / 2 := by
    exact (Finset.card_image_of_injective _ (show Function.Injective f by
      intro i j h
      dsimp [f] at h
      omega)).trans (Finset.card_range _)
  have hsq : m ^ 2 < 10000 * (L + 1) := Nat.lt_mul_div_succ _ (by decide)
  have hlarge : 4 ≤ L := by
    calc
      4 = quadBin 200 := by decide
      _ ≤ quadBin m := quadBin_monotone hm
  change (S.filter (· ≤ 3 * L)).card ≤ 3 * m at hS
  have hbudget : (S.filter (· ≤ 3 * L)).card ^ 2 < targets.card * 400000 := by
    rw [hcard]
    have hsq' := Nat.pow_le_pow_left hS 2
    rw [show (3 * m) ^ 2 = 9 * m ^ 2 by ring] at hsq'
    omega
  obtain ⟨n, hn, hde⟩ := exists_target_with_few_endpoints _ targets _ hbudget
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hn
  have hk' : k < L / 2 := Finset.mem_range.1 hk
  have hlo : 2 * L < f k := by dsimp [f]; omega
  have hhi : f k ≤ 3 * L := by dsimp [f]; omega
  have hodd : Odd (f k) := Nat.odd_iff.2 (by dsimp [f]; omega)
  rw [upperEndpoints_filter hhi] at hde
  exact ⟨f k, hlo, hhi, hodd, hde⟩

/-- For a small positive shift, a missing successor follows from a finite count.
    The point and its tested successor both lie in the frozen interval. -/
theorem shift_avoided_in_prefix (S : Finset ℕ) {X d : ℕ}
    (h0 : 0 ∈ S) (hd : 0 < d)
    (hspace : (S.filter (· ≤ X)).card * d ≤ X) :
    ∃ u ∈ S, u + d ≤ X ∧ u + d ∉ S := by
  let A := S.filter (· ≤ X)
  have hex : ∃ k, k ≤ A.card ∧ k * d ∉ S := by
    by_contra! h
    have hm : (Finset.range (A.card + 1)).card ≤ A.card := by
      apply Finset.card_le_card_of_injOn (fun k : ℕ => k * d)
      · intro k hk
        have hka : k ≤ A.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        exact Finset.mem_filter.2 ⟨h k hka, (Nat.mul_le_mul_right _ hka).trans hspace⟩
      · intro k _ j _ heq
        exact Nat.eq_of_mul_eq_mul_right hd heq
    simp at hm
  let k := Nat.find hex
  obtain ⟨hk, hkS⟩ := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra! h
    have : k = 0 := by omega
    rw [show Nat.find hex = k from rfl, this, Nat.zero_mul] at hkS
    exact hkS h0
  have hprev : k - 1 < Nat.find hex := by change k - 1 < k; omega
  have hle : (k - 1) ≤ A.card := by change k ≤ A.card at hk; omega
  have hprevS : (k - 1) * d ∈ S := by
    by_contra ha
    exact Nat.find_min hex hprev ⟨hle, ha⟩
  have hn : (k - 1) * d + d = k * d := by
    calc
      _ = ((k - 1) + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hkpos]
  change k ≤ A.card at hk
  change k * d ∉ S at hkS
  exact ⟨(k - 1) * d, hprevS, by rw [hn]; exact (Nat.mul_le_mul_right _ hk).trans hspace,
    by rwa [hn]⟩

/-- If the shifted interval contains fewer points than the palette, some shift is absent. -/
theorem shift_avoided_by_card (S palette : Finset ℕ) {X d : ℕ} (hsub : palette ⊆ S)
    (hsmall : ∀ u ∈ palette, u ≤ X)
    (hcard : (S.filter (fun z => d ≤ z ∧ z ≤ d + X)).card < palette.card) :
    ∃ u ∈ S, u ≤ X ∧ u + d ∉ S := by
  by_contra! h
  have hle : palette.card ≤ (S.filter (fun z => d ≤ z ∧ z ≤ d + X)).card := by
    apply Finset.card_le_card_of_injOn (· + d)
    · intro u hu
      change u + d ∈ (S.filter (fun z => d ≤ z ∧ z ≤ d + X))
      exact Finset.mem_filter.2 ⟨h u (hsub hu) (hsmall u hu), by omega, by
        have hup := hsmall u hu
        omega⟩
    · intro x _ y _ heq
      exact Nat.add_right_cancel heq
  omega

/-- Replace each removed point with a distinct admissible point in the same bin.
    The resulting set has the same bin counts and still omits the target. -/
theorem replace_endpoints (S D : Finset ℕ) (bin : ℕ → ℕ) {N : ℕ}
    (hodd : Odd N) (hempty : ¬ Represented (S \ D) N)
    (available : ∀ P : Finset ℕ, P.card < D.card → ∀ d ∈ D,
      ∃ w, w ∉ S ∪ P ∧ bin w = bin d ∧ ∀ z ∈ (S \ D) ∪ P, w + z ≠ N) :
    ∃ P : Finset ℕ, Disjoint P S ∧ P.card = D.card ∧
      (∀ keep : ℕ → Prop, ∀ [DecidablePred keep],
        (P.filter (fun x => keep (bin x))).card = (D.filter (fun x => keep (bin x))).card) ∧
      ¬ Represented ((S \ D) ∪ P) N := by
  suffices h : ∀ G ⊆ D, ∃ P : Finset ℕ, Disjoint P S ∧ P.card = G.card ∧
      (∀ keep : ℕ → Prop, ∀ [DecidablePred keep],
        (P.filter (fun x => keep (bin x))).card = (G.filter (fun x => keep (bin x))).card) ∧
      ¬ Represented ((S \ D) ∪ P) N from
    h D (fun _ hx => hx)
  intro G
  induction G using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp, rfl, fun _ _ => rfl, by simpa using hempty⟩
  | insert d G hdG ih =>
    intro hGD
    have hdD : d ∈ D := hGD (Finset.mem_insert_self _ _)
    have hG : G ⊆ D := fun _ hx => hGD (Finset.mem_insert_of_mem hx)
    obtain ⟨P, hdisj, hcard, hbins, hn⟩ := ih hG
    have hP : P.card < D.card := by
      have hbound := Finset.card_le_card hGD
      rw [Finset.card_insert_of_notMem hdG] at hbound
      omega
    obtain ⟨w, hw, hbin, hsafe⟩ := available P hP d hdD
    have hwS : w ∉ S := fun h => hw (Finset.mem_union_left _ h)
    have hwP : w ∉ P := fun h => hw (Finset.mem_union_right _ h)
    have hdisj' : Disjoint (insert w P) S := Finset.disjoint_insert_left.2 ⟨hwS, hdisj⟩
    have hcard' : (insert w P).card = (insert d G).card := by
      rw [Finset.card_insert_of_notMem hwP, Finset.card_insert_of_notMem hdG, hcard]
    refine ⟨insert w P, hdisj', hcard', ?_, ?_⟩
    · intro keep _
      have hPj : w ∉ P.filter (fun x => keep (bin x)) := fun h => hwP (Finset.mem_filter.1 h).1
      have hGj : d ∉ G.filter (fun x => keep (bin x)) := fun h => hdG (Finset.mem_filter.1 h).1
      by_cases hj : keep (bin d)
      · have hj' : keep (bin w) := hbin ▸ hj
        simp only [Finset.filter_insert, hj, hj', ite_true]
        rw [Finset.card_insert_of_notMem hPj, Finset.card_insert_of_notMem hGj, hbins keep]
      · have hj' : ¬ keep (bin w) := by rwa [hbin]
        simp only [Finset.filter_insert, hj, hj', ite_false, hbins keep]
    · have he : (S \ D) ∪ insert w P = insert w ((S \ D) ∪ P) := by
        ext z
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [he]
      have hpar := Nat.odd_iff.1 hodd
      rintro ⟨x, hx, y, hy, hxy⟩
      rcases Finset.mem_insert.1 hx with hxe | hx
      · rcases Finset.mem_insert.1 hy with hye | hy
        · omega
        · exact hsafe y hy (by omega)
      · rcases Finset.mem_insert.1 hy with hye | hy
        · exact hsafe x hx (by omega)
        · exact hn ⟨x, hx, y, hy, hxy⟩

/-- The selected representation of `n` is present in the finite set. -/
def HasSelectedPair (B : Finset ℕ) (s : Fin 2) (n : ℕ) : Prop :=
  (casselsPair s n).x ∈ B ∧ (casselsPair s n).y ∈ B

theorem represented_after_deletion {B D : Finset ℕ} {s : Fin 2} {n : ℕ}
    (hp : HasSelectedPair B s n) (hd : ¬ Hits D s n) :
    Represented (B \ D) n := by
  refine ⟨(casselsPair s n).x, Finset.mem_sdiff.2 ⟨hp.1, fun h => hd (.inl h)⟩,
    (casselsPair s n).y, Finset.mem_sdiff.2 ⟨hp.2, fun h => hd (.inr h)⟩, (casselsPair s n).sum_eq⟩

/-- The installed witness and the set retained after the endpoint replacement. -/
def witnessCore (B D R : Finset ℕ) (a N : ℕ) : Finset ℕ :=
  insert (N - a) ((B \ D) ∪ R)

/-- Once the finite background and admissible shifts are supplied, the completed
    stage covers its full range and preserves the chosen witness. -/
theorem finish_finite_stage (B D R : Finset ℕ) {Y₀ X L N Y a : ℕ}
    (hYX : Y₀ ≤ X) (hXL : 2 * X ≤ L) (hN₀ : 2 * L < N) (hN₁ : N ≤ 3 * L)
    (horizon : 24577 * N ≤ Y) (hL : ∀ s : Fin 2, blockStart s 4 ≤ L)
    (hB : ∀ z ∈ B, z ≤ Y) (hD : ∀ d ∈ D, L < d ∧ d ≤ N)
    (hR : ∀ z ∈ R, X < z ∧ z ≤ Y)
    (h0 : 0 ∈ B) (ha : a ∈ B) (haX : a ≤ X) (hodd : Odd N)
    (hNfree : ¬ Represented ((B \ D) ∪ R) N)
    (hPrefix : ∀ n ≤ Y₀, Represented B n)
    (hBackground : ∀ n, Y₀ < n → n ≤ Y → ∀ s, HasSelectedPair B s n)
    (hShift : ∀ P : Finset ℕ, P.card < 49 * 81921 * D.card ^ 2 →
      (∀ w ∈ P, X < w ∧ w ≤ Y) → ∀ n, 2 * X < n → n < N →
      ∃ u ∈ witnessCore B D R a N ∪ P, u ≤ X ∧ u + (N - n) ∉ witnessCore B D R a N ∪ P) :
    ∃ P : Finset ℕ, P.card ≤ 49 * 81921 * D.card ^ 2 ∧ (∀ w ∈ P, X < w ∧ w ≤ Y) ∧
      let T := witnessCore B D R a N ∪ P
      (∀ n ≤ Y, Represented T n) ∧ AllRepresentationsUse T a N ∧
      (∀ z ∈ T, z ≤ Y) ∧ (∀ z ≤ X, z ∈ T ↔ z ∈ B) := by
  classical
  let S := witnessCore B D R a N
  have hsafe (z : ℕ) (hz : z ≤ X) (hzB : z ∈ B) : z ∈ B \ D :=
    Finset.mem_sdiff.2 ⟨hzB, fun hd => by have hl := (hD z hd).1; omega⟩
  have hsub : B \ D ⊆ S :=
    fun _ hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)
  have h₀ : 0 ∈ S := hsub (hsafe 0 (Nat.zero_le _) h0)
  have hN : N ≤ Y := by omega
  have hbW : X < N - a := by omega
  have hW := install_witness (Finset.mem_union_left R (hsafe a haX ha)) (by omega : a ≤ N) hNfree
  let H := (Finset.range (Y + 1)).filter fun n => n ≠ N ∧ Hits D 0 n ∧ Hits D 1 n
  have hHcard : H.card ≤ 49 * 81921 * D.card ^ 2 :=
    collateral_card_le hL hN₁ hD fun n hn => (Finset.mem_filter.1 hn).2.2
  have hH (n : ℕ) (hn : n ∈ H) : 2 * X < n ∧ n ≤ Y ∧ n ≠ N := by
    obtain ⟨hnY, hnN, hhit, _⟩ := Finset.mem_filter.1 hn
    have hm : blockStart 0 2 ≤ L :=
      ((blockStart_strictMono 0).monotone (by decide : 2 ≤ 4)).trans (hL 0)
    have hl := (hit_sum_bounds hm hD hhit).1
    exact ⟨hXL.trans_lt hl, Nat.lt_succ_iff.1 (Finset.mem_range.1 hnY), hnN⟩
  obtain ⟨P, hPc, hPb, hholes, hforced⟩ := repair_holes S H hodd h₀ hW.2 hH
    (fun P hp hb n hn hlt => hShift P (hp.trans_le hHcard) hb n (hH n hn).1 hlt)
  refine ⟨P, hPc.trans hHcard, hPb, ?_, hforced, ?_, ?_⟩
  · intro n hn
    by_cases hn₀ : n ≤ Y₀
    · obtain ⟨x, hx, y, hy, he⟩ := hPrefix n hn₀
      exact ⟨x, Finset.mem_union_left _ (hsub (hsafe x (by omega) hx)),
        y, Finset.mem_union_left _ (hsub (hsafe y (by omega) hy)), he⟩
    by_cases hnN : n = N
    · subst n
      exact hW.1.mono fun _ hx => Finset.mem_union_left _ hx
    by_cases hh : Hits D 0 n ∧ Hits D 1 n
    · exact hholes n (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hnN, hh⟩)
    have survive (s : Fin 2) (hs : ¬ Hits D s n) : Represented (S ∪ P) n :=
      (represented_after_deletion (hBackground n (by omega) hn s) hs).mono
        (fun _ hx => Finset.mem_union_left _ (hsub hx))
    by_cases hz : Hits D 0 n
    · exact survive 1 (fun ho => hh ⟨hz, ho⟩)
    · exact survive 0 hz
  · intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (Nat.sub_le _ _).trans hN
      · rcases Finset.mem_union.1 hz with hb | hr
        · exact hB z (Finset.mem_sdiff.1 hb).1
        · exact (hR z hr).2
    · exact (hPb z hz).2
  · intro z hz
    constructor
    · intro hzt
      rcases Finset.mem_union.1 hzt with hzs | hzp
      · rcases Finset.mem_insert.1 hzs with he | hz'
        · omega
        · rcases Finset.mem_union.1 hz' with hb | hr
          · exact (Finset.mem_sdiff.1 hb).1
          · exact (not_lt_of_ge hz (hR z hr).1).elim
      · exact (not_lt_of_ge hz (hPb z hzp).1).elim
    · exact fun hzb => Finset.mem_union_left _ (hsub (hsafe z hz hzb))

end Erdos326

-- ==== Bins



namespace Erdos326

/-- Group three consecutive quadratic bins, so at most two points are mandatory. -/
def coarseEdge (i : ℕ) : ℕ := quadBin (3 * i)

def countThrough (S : Finset ℕ) (i : ℕ) : ℕ := (S.filter (· ≤ coarseEdge i)).card

lemma coarseEdge_monotone : Monotone coarseEdge :=
  fun _ _ hij => quadBin_monotone (Nat.mul_le_mul_left 3 hij)

lemma coarseEdge_cofinal (x : ℕ) : ∃ i, x ≤ coarseEdge i := by
  let i := 10000 * (x + 1)
  exact ⟨i, (quadBin_cofinal x).trans (quadBin_monotone (show i ≤ 3 * i by omega))⟩

noncomputable def binIndex (x : ℕ) : ℕ := Nat.find (coarseEdge_cofinal x)

lemma binIndex_le_iff {x i : ℕ} : binIndex x ≤ i ↔ x ≤ coarseEdge i := by
  refine ⟨fun h => (Nat.find_spec (coarseEdge_cofinal x)).trans (coarseEdge_monotone h),
    fun h => Nat.find_min' (coarseEdge_cofinal x) h⟩

lemma binIndex_succ_iff {x i : ℕ} :
    binIndex x = i + 1 ↔ coarseEdge i < x ∧ x ≤ coarseEdge (i + 1) := by
  have hlo := not_congr (binIndex_le_iff (x := x) (i := i))
  have hhi := binIndex_le_iff (x := x) (i := i + 1)
  omega

private lemma coarseEdge_width_ge_of {i d : ℕ} (hi : 10000 * (d + 1) ≤ 18 * i + 9) :
    coarseEdge i + d ≤ coarseEdge (i + 1) := by
  have hlo : 10000 * quadBin (3 * i) ≤ (3 * i) ^ 2 := by
    rw [Nat.mul_comm, quadBin]
    exact Nat.div_mul_le_self _ _
  have hhi : (3 * (i + 1)) ^ 2 < 10000 * (quadBin (3 * (i + 1)) + 1) :=
    Nat.lt_mul_div_succ _ (by decide)
  rw [show (3 * (i + 1)) ^ 2 = (3 * i) ^ 2 + 18 * i + 9 by ring] at hhi
  change quadBin (3 * i) + d ≤ quadBin (3 * (i + 1))
  omega

lemma coarseEdge_width_ge {i d : ℕ} (hi : 1000 * (d + 1) ≤ i) :
    coarseEdge i + d ≤ coarseEdge (i + 1) :=
  coarseEdge_width_ge_of (by omega)

lemma quadBin_mul_ge (d m : ℕ) : d ^ 2 * quadBin m ≤ quadBin (d * m) := by
  have h : 10000 * quadBin m ≤ m ^ 2 := by
    rw [Nat.mul_comm, quadBin]
    exact Nat.div_mul_le_self _ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2
  calc
    _ = d ^ 2 * (10000 * quadBin m) := by ring
    _ ≤ d ^ 2 * m ^ 2 := Nat.mul_le_mul_left _ h
    _ = (d * m) ^ 2 := by rw [mul_pow]

lemma coarseEdge_mul_ge (d i : ℕ) : d ^ 2 * coarseEdge i ≤ coarseEdge (d * i) := by
  unfold coarseEdge
  rw [show 3 * (d * i) = d * (3 * i) by ring]
  exact quadBin_mul_ge d (3 * i)

lemma countThrough_eq_card {S : Finset ℕ} {i : ℕ}
    (h : ∀ x ∈ S, x ≤ coarseEdge i) : countThrough S i = S.card := by
  unfold countThrough
  rw [Finset.filter_eq_self.2 h]

lemma countThrough_of_agree {S T : Finset ℕ} {i : ℕ}
    (h : ∀ x ≤ coarseEdge i, x ∈ S ↔ x ∈ T) : countThrough S i = countThrough T i := by
  unfold countThrough
  congr 1
  ext x
  simp only [Finset.mem_filter]
  by_cases hx : x ≤ coarseEdge i
  · simp [hx, h x hx]
  · simp [hx]

lemma countThrough_succ (S : Finset ℕ) (i : ℕ) :
    countThrough S (i + 1) =
      countThrough S i + (S.filter (fun x => binIndex x = i + 1)).card := by
  let P := S.filter (· ≤ coarseEdge i)
  let Q := S.filter (fun x => binIndex x = i + 1)
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.2
    intro x hx hy
    have hx₁ := (Finset.mem_filter.1 hx).2
    have hy₁ := (binIndex_succ_iff.1 (Finset.mem_filter.1 hy).2).1
    omega
  have he : S.filter (· ≤ coarseEdge (i + 1)) = P ∪ Q := by
    ext x
    simp only [P, Q, Finset.mem_union, Finset.mem_filter, binIndex_succ_iff]
    have hlo : coarseEdge i ≤ coarseEdge (i + 1) := coarseEdge_monotone (by omega)
    by_cases hx : x ≤ coarseEdge i
    · have hy : x ≤ coarseEdge (i + 1) := hx.trans hlo
      simp [hx, hy]
    · have hx' : coarseEdge i < x := by omega
      simp [hx, hx']
  change (S.filter (· ≤ coarseEdge (i + 1))).card = P.card + Q.card
  rw [he, Finset.card_union_of_disjoint hdis]

def skeleton : Set ℕ := casselsBasis 0 ∪ casselsBasis 1

/-- If a future representation uses a point in a frozen range, that point survived. -/
def IntactAfter (S : Finset ℕ) (Y : ℕ) : Prop :=
  ∀ s : Fin 2, ∀ n > Y,
    ((casselsPair s n).x ≤ Y → (casselsPair s n).x ∈ S) ∧
    ((casselsPair s n).y ≤ Y → (casselsPair s n).y ∈ S)

private lemma casselsBasis_subset_skeleton (s : Fin 2) :
    casselsBasis s ⊆ skeleton := by
  fin_cases s
  · exact Set.subset_union_left
  · exact Set.subset_union_right

lemma pair_bounds (s : Fin 2) (n : ℕ) :
    (casselsPair s n).x ≤ n ∧ (casselsPair s n).y ≤ n := by
  have h := (casselsPair s n).sum_eq
  omega

lemma IntactAfter.extend {S B : Finset ℕ} {lo hi : ℕ} (h : IntactAfter S lo)
    (hsub : S ⊆ B) (hnew : ∀ x, lo < x → x ≤ hi → x ∈ skeleton → x ∈ B)
    (s : Fin 2) (n : ℕ) (hn : lo < n) :
    ((casselsPair s n).x ≤ hi → (casselsPair s n).x ∈ B) ∧
    ((casselsPair s n).y ≤ hi → (casselsPair s n).y ∈ B) := by
  have hcopy (x : ℕ) (hx : x ∈ casselsBasis s) (hOld : x ≤ lo → x ∈ S) (hhi : x ≤ hi) : x ∈ B := by
    by_cases hlo : x ≤ lo
    · exact hsub (hOld hlo)
    · exact hnew x (by omega) hhi (casselsBasis_subset_skeleton s hx)
  let r := casselsPair s n
  exact ⟨hcopy r.x (mem_casselsBasis.2 ⟨r.i, r.left_mem⟩) (h s n hn).1,
    hcopy r.y (mem_casselsBasis.2 ⟨r.j, r.right_mem⟩) (h s n hn).2⟩

private lemma fill_one_bin (B : Finset ℕ) (i : ℕ) (hi : 4000 ≤ i)
    (hB : ∀ x ∈ B, x ≤ coarseEdge i) (hcount : 3 * i + 2 ≤ B.card) :
    ∃ T : Finset ℕ,
      (∀ x ∈ T, x ≤ coarseEdge (i + 1)) ∧
      (∀ x ≤ coarseEdge i, x ∈ T ↔ x ∈ B) ∧
      (∀ x, coarseEdge i < x → x ≤ coarseEdge (i + 1) → x ∈ skeleton → x ∈ T) ∧
      T.card ≤ max (3 * (i + 1) + 2) (B.card + 2) ∧
      3 * (i + 1) + 2 ≤ T.card := by
  classical
  let I := Finset.Ioc (coarseEdge i) (coarseEdge (i + 1))
  let G := I.filter (· ∈ skeleton)
  have hG : G.card ≤ 2 := by
    apply card_union_in_three_bins_le_two (3 * i) (by omega)
    intro x hx
    obtain ⟨hix, hs⟩ := Finset.mem_filter.1 hx
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.1 hix
    have he : 3 * (i + 1) = 3 * i + 3 := by omega
    exact ⟨hs, hlo, by simpa only [coarseEdge, he] using hhi⟩
  have hI : 5 ≤ I.card := by
    change 5 ≤ (Finset.Ioc (coarseEdge i) (coarseEdge (i + 1))).card
    rw [Nat.card_Ioc]
    have hbig := coarseEdge_width_ge_of (i := i) (d := 5) (by omega)
    omega
  let need := (3 * (i + 1) + 2) - (B.card + G.card)
  have haveRoom : need ≤ (I \ G).card := by
    have h := Finset.card_sdiff_add_card_eq_card (show G ⊆ I from Finset.filter_subset _ _)
    change (3 * (i + 1) + 2) - (B.card + G.card) ≤ (I \ G).card
    omega
  obtain ⟨F, hF, hcF⟩ := Finset.exists_subset_card_eq haveRoom
  let T := B ∪ (G ∪ F)
  have hGF : Disjoint G F := by
    apply Finset.disjoint_left.2
    exact fun _ hxG hxF => (Finset.mem_sdiff.1 (hF hxF)).2 hxG
  have hinside : G ∪ F ⊆ I := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (Finset.mem_filter.1 hx).1
    · exact (Finset.mem_sdiff.1 (hF hx)).1
  have hdis : Disjoint B (G ∪ F) := by
    apply Finset.disjoint_left.2
    intro x hx hy
    exact (not_lt_of_ge (hB x hx)) (Finset.mem_Ioc.1 (hinside hy)).1
  have he : T.card = B.card + G.card + need := by
    change (B ∪ (G ∪ F)).card = _
    rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hGF, hcF]
    omega
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (hB x hx).trans (coarseEdge_monotone (by omega))
    · exact (Finset.mem_Ioc.1 (hinside hx)).2
  · intro x hx
    refine ⟨fun hm => ?_, fun hm => Finset.mem_union_left _ hm⟩
    rcases Finset.mem_union.1 hm with hm | hm
    · exact hm
    · exact (not_lt_of_ge hx (Finset.mem_Ioc.1 (hinside hm)).1).elim
  · intro x hlo hhi hs
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.2
      ⟨Finset.mem_Ioc.2 ⟨hlo, hhi⟩, hs⟩))
  · rw [he]
    change B.card + G.card + (3 * (i + 1) + 2 - (B.card + G.card)) ≤ _
    omega
  · rw [he]
    change 3 * (i + 1) + 2 ≤ B.card + G.card + (3 * (i + 1) + 2 - (B.card + G.card))
    omega

/-- A stage frozen at the end of a coarse bin. -/
structure StagePrefix (start E : ℕ) where
  index : ℕ
  points : Finset ℕ
  index_ge : start ≤ index
  bounded : ∀ x ∈ points, x ≤ coarseEdge index
  covered : ∀ n ≤ coarseEdge index, Represented points n
  intact : IntactAfter points (coarseEdge index)
  counts : ∀ i, start ≤ i → i ≤ index →
    3 * i + 2 ≤ countThrough points i ∧ countThrough points i ≤ 3 * i + 2 + E

/-- Normal filling keeps the prior prefix, includes the skeleton in the new
    range, and reduces any counting surplus by at least one per coarse bin. -/
theorem extend_normally {start E : ℕ} (hstart : 4000 ≤ start)
    (p : StagePrefix start E) {j : ℕ} (hj : p.index ≤ j) :
    ∃ B : Finset ℕ,
      (∀ x ∈ B, x ≤ coarseEdge j) ∧
      (∀ x ≤ coarseEdge p.index, x ∈ B ↔ x ∈ p.points) ∧
      (∀ x, coarseEdge p.index < x → x ≤ coarseEdge j → x ∈ skeleton → x ∈ B) ∧
      (∀ i, start ≤ i → i ≤ j →
        3 * i + 2 ≤ countThrough B i ∧ countThrough B i ≤ 3 * i + 2 + (E - (i - p.index))) := by
  induction j, hj using Nat.le_induction with
  | base =>
    refine ⟨p.points, p.bounded, fun _ _ => Iff.rfl, ?_, ?_⟩
    · intro x h h'
      exact (not_lt_of_ge h' h).elim
    · intro i hi hi'
      have h := p.counts i hi hi'
      simpa [Nat.sub_eq_zero_of_le hi'] using h
  | succ j h_j ih =>
    obtain ⟨B, hb, hagree, hnew, hc⟩ := ih
    have hj : 4000 ≤ j := hstart.trans (p.index_ge.trans h_j)
    have hjstart := p.index_ge.trans h_j
    have heq := countThrough_eq_card hb
    have hlo : 3 * j + 2 ≤ B.card := heq ▸ (hc j hjstart le_rfl).1
    have hhi : B.card ≤ 3 * j + 2 + (E - (j - p.index)) := heq ▸ (hc j hjstart le_rfl).2
    obtain ⟨T, hTb, hTagree, hTnew, hThi, hTlo⟩ := fill_one_bin B j hj hb hlo
    have hcut := coarseEdge_monotone h_j
    refine ⟨T, hTb, fun x hx => (hTagree x (hx.trans hcut)).trans (hagree x hx), ?_, ?_⟩
    · intro x hx hy hs
      by_cases h : x ≤ coarseEdge j
      · exact (hTagree x h).2 (hnew x hx h hs)
      · exact hTnew x (by omega) hy hs
    · intro i hi hij
      by_cases h : i ≤ j
      · rw [countThrough_of_agree (fun x hx => hTagree x (hx.trans (coarseEdge_monotone h)))]
        exact hc i hi h
      · have h' : i = j + 1 := by omega
        subst i
        rw [countThrough_eq_card hTb]
        exact ⟨hTlo, by omega⟩

end Erdos326

-- ==== Initial



namespace Erdos326

def firstBin : ℕ := 20000

private noncomputable def skeletonPrefix (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Iic (coarseEdge i)).filter (· ∈ skeleton)

private lemma mem_skeletonPrefix {i x : ℕ} :
    x ∈ skeletonPrefix i ↔ x ≤ coarseEdge i ∧ x ∈ skeleton := by
  classical
  simp [skeletonPrefix]

private lemma skeletonPrefix_card (i : ℕ) (hi : 4000 ≤ i) :
    (skeletonPrefix i).card ≤ coarseEdge 4000 + 1 + 2 * (i - 4000) := by
  induction i, hi using Nat.le_induction with
  | base =>
    classical
    simpa [skeletonPrefix] using Finset.card_filter_le (s := Finset.Iic (coarseEdge 4000))
      (· ∈ skeleton)
  | succ i hi ih =>
    let B := skeletonPrefix (i + 1)
    have he : B.card = (skeletonPrefix i).card +
        (B.filter (fun x => binIndex x = i + 1)).card := by
      rw [← countThrough_eq_card (show ∀ x ∈ B, x ≤ coarseEdge (i + 1)
        from fun _ hx => (mem_skeletonPrefix.1 hx).1), countThrough_succ]
      rw [countThrough_of_agree (T := skeletonPrefix i)]
      · rw [countThrough_eq_card (fun _ hx => (mem_skeletonPrefix.1 hx).1)]
      · intro x hx
        change x ∈ skeletonPrefix (i + 1) ↔ x ∈ skeletonPrefix i
        rw [mem_skeletonPrefix, mem_skeletonPrefix]
        have h := hx.trans (coarseEdge_monotone (Nat.le_succ _))
        simp [hx, h]
    have hbin : (B.filter (fun x => binIndex x = i + 1)).card ≤ 2 := by
      apply card_union_in_three_bins_le_two (3 * i) (by omega)
      intro x hx
      obtain ⟨hxB, hxj⟩ := Finset.mem_filter.1 hx
      obtain ⟨hxLo, hxHi⟩ := binIndex_succ_iff.1 hxj
      have hi' : 3 * (i + 1) = 3 * i + 3 := by omega
      exact ⟨(mem_skeletonPrefix.1 hxB).2, hxLo, by simpa only [coarseEdge, hi'] using hxHi⟩
    change B.card ≤ _
    rw [he]
    omega

/-- Start with both skeletons up to a large bin boundary and pad the initial count. -/
theorem initial_prefix (E : ℕ) : Nonempty (StagePrefix firstBin E) := by
  classical
  let A := skeletonPrefix firstBin
  let I := Finset.Iic (coarseEdge firstBin)
  have hA : A.card ≤ 3 * firstBin + 2 := by
    exact (skeletonPrefix_card firstBin (by decide)).trans (by decide)
  have hI : 3 * firstBin + 2 ≤ I.card := by
    change 3 * firstBin + 2 ≤ (Finset.Iic (coarseEdge firstBin)).card
    rw [Nat.card_Iic]
    decide
  have hsub : A ⊆ I := fun _ hx => Finset.mem_Iic.2 (mem_skeletonPrefix.1 hx).1
  have hroom : 3 * firstBin + 2 - A.card ≤ (I \ A).card := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨F, hF, hf⟩ := Finset.exists_subset_card_eq hroom
  have hdisj : Disjoint A F := Finset.disjoint_left.2
    (fun _ hx hy => (Finset.mem_sdiff.1 (hF hy)).2 hx)
  let S := A ∪ F
  have hS : ∀ x ∈ S, x ≤ coarseEdge firstBin := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (mem_skeletonPrefix.1 hx).1
    · exact Finset.mem_Iic.1 (Finset.mem_sdiff.1 (hF hx)).1
  have hsk : ∀ x ≤ coarseEdge firstBin, x ∈ skeleton → x ∈ S :=
    fun _ h₁ h₂ => Finset.mem_union_left _ (mem_skeletonPrefix.2 ⟨h₁, h₂⟩)
  have hcard : S.card = 3 * firstBin + 2 := by
    change (A ∪ F).card = _
    rw [Finset.card_union_of_disjoint hdisj, hf]
    omega
  refine ⟨⟨firstBin, S, le_rfl, hS, ?_, ?_, ?_⟩⟩
  · intro n hn
    obtain ⟨x, hx, y, hy, he⟩ := cassels_basis_covers 0 n
    exact ⟨x, hsk x (by omega) (.inl hx), y, hsk y (by omega) (.inl hy), he⟩
  · intro s n _
    let r := casselsPair s n
    have hs : casselsBasis s ⊆ skeleton := by
      fin_cases s
      · exact Set.subset_union_left
      · exact Set.subset_union_right
    exact ⟨fun h => hsk r.x h (hs (mem_casselsBasis.2 ⟨r.i, r.left_mem⟩)),
      fun h => hsk r.y h (hs (mem_casselsBasis.2 ⟨r.j, r.right_mem⟩))⟩
  · intro i hi hij
    rw [le_antisymm hij hi, countThrough_eq_card hS, hcard]
    exact ⟨le_rfl, Nat.le_add_right _ _⟩

end Erdos326

-- ==== LocalCount



open scoped BigOperators

namespace Erdos326

def windowCount (S : Finset ℕ) (u w : ℕ) : ℕ :=
  (S.filter (fun x => u ≤ x ∧ x ≤ u + w)).card

lemma binIndex_monotone : Monotone binIndex := by
  intro u v huv
  apply binIndex_le_iff.2
  exact huv.trans (binIndex_le_iff.1 le_rfl)

private lemma coarseEdge_jump {i j d : ℕ} (hi : 1000 * (d + 1) ≤ i) (hij : i ≤ j) :
    coarseEdge i + (j - i) * d ≤ coarseEdge j := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    have h := coarseEdge_width_ge (i := j) (d := d) (hi.trans hj)
    have hr : (j + 1 - i) * d = (j - i) * d + d := by
      rw [show j + 1 - i = j - i + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [hr]
    omega

private lemma window_bins {u w x J d : ℕ} (hd : 0 < d) (hj : 1000 * (d + 1) ≤ J)
    (hu : u ≤ x) (hw : x ≤ u + w) (hx : coarseEdge J < x) :
    let i := max (binIndex u) (J + 1)
    i ≤ binIndex x ∧ binIndex x ≤ i + w / d + 1 := by
  let i := max (binIndex u) (J + 1)
  have hlo₁ : binIndex u ≤ binIndex x := binIndex_monotone hu
  have hlo₂ : J + 1 ≤ binIndex x := by
    by_contra! h
    exact (not_lt_of_ge (binIndex_le_iff.1 (show binIndex x ≤ J by omega))) hx
  have hlo : i ≤ binIndex x := max_le hlo₁ hlo₂
  refine ⟨hlo, ?_⟩
  by_cases hix : binIndex x ≤ i
  · exact hix.trans ((Nat.le_add_right i (w / d)).trans (Nat.le_add_right _ 1))
  let k := binIndex x - 1
  have hki : i ≤ k := by dsimp [k]; omega
  have hk : binIndex x = k + 1 := by dsimp [k]; omega
  have hstart : 1000 * (d + 1) ≤ i := hj.trans (by dsimp [i]; omega)
  have hlow := coarseEdge_jump hstart hki
  have hxe := (binIndex_succ_iff.1 hk).1
  have he : u ≤ coarseEdge i := binIndex_le_iff.1 (le_max_left _ _)
  have hprod : (k - i) * d ≤ w := by omega
  have hle := (Nat.le_div_iff_mul_le hd).2 hprod
  omega

private lemma tail_window_card {S : Finset ℕ} {J d p u w : ℕ}
    (hd : 0 < d) (hJ : 1000 * (d + 1) ≤ J)
    (hcap : ∀ i > J, (S.filter (fun x => binIndex x = i)).card ≤ p) :
    (S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x)).card ≤ p * (w / d + 2) := by
  let Tail := S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x)
  let lo := max (binIndex u) (J + 1)
  let I := Finset.Icc lo (lo + w / d + 1)
  let part (i : ℕ) := S.filter (fun x => binIndex x = i)
  have hsub : Tail ⊆ I.biUnion part := by
    intro x hx
    obtain ⟨hxS, hu, hw, hj⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_biUnion.2 ⟨binIndex x, Finset.mem_Icc.2 (window_bins hd hJ hu hw hj),
      Finset.mem_filter.2 ⟨hxS, rfl⟩⟩
  have hI : I.card = w / d + 2 := by
    change (Finset.Icc lo (lo + w / d + 1)).card = w / d + 2
    rw [Nat.card_Icc]
    generalize w / d = r
    omega
  calc
    _ ≤ (I.biUnion part).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, (part i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, p := by
      apply Finset.sum_le_sum
      intro i hi
      have hh : lo ≤ i := (Finset.mem_Icc.1 hi).1
      exact hcap i (by dsimp [lo] at hh; omega)
    _ = _ := by simp [Finset.sum_const, hI, Nat.mul_comm]

/-- A fixed initial prefix and bounded occupancy of long bins give a uniform local count. -/
theorem window_count_le {S : Finset ℕ} {J d p u w : ℕ}
    (hd : 0 < d) (hJ : 1000 * (d + 1) ≤ J)
    (hcap : ∀ i > J, (S.filter (fun x => binIndex x = i)).card ≤ p) :
    windowCount S u w ≤ countThrough S J + p * (w / d + 2) := by
  let H := S.filter (· ≤ coarseEdge J)
  let T := S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x)
  have hsub : S.filter (fun x => u ≤ x ∧ x ≤ u + w) ⊆ H ∪ T := by
    intro x hx
    obtain ⟨hxS, hu, hw⟩ := Finset.mem_filter.1 hx
    by_cases h : x ≤ coarseEdge J
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxS, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hxS, hu, hw, by omega⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le H T).trans
    (Nat.add_le_add_left (tail_window_card (u := u) (w := w) hd hJ hcap) _))

/-- A late interval shorter than the guaranteed bin width touches at most two bins. -/
theorem late_window_count_le {S : Finset ℕ} {J d p u w : ℕ}
    (hJ : 1000 * (d + 1) ≤ J) (hcap : ∀ i > J, (S.filter (fun x => binIndex x = i)).card ≤ p)
    (hu : coarseEdge J < u) (hw : w < d) : windowCount S u w ≤ 2 * p := by
  have he : S.filter (fun x => u ≤ x ∧ x ≤ u + w) =
      S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hx, hux, hxu⟩ => ⟨hx, hux, hxu, hu.trans_le hux⟩,
      fun ⟨hx, hux, hxu, _⟩ => ⟨hx, hux, hxu⟩⟩
  unfold windowCount
  rw [he]
  simpa [Nat.div_eq_of_lt hw, Nat.mul_comm] using
    tail_window_card (u := u) (w := w) (by omega : 0 < d) hJ hcap

private lemma card_reflected_points {S : Finset ℕ} {l W N Q : ℕ}
    (localCount : ∀ u, windowCount S u W ≤ Q) :
    ((Finset.Ico l (l + W)).filter (fun x => x ≤ N ∧ N - x ∈ S)).card ≤ Q := by
  let lower := N - (l + W)
  let src := (Finset.Ico l (l + W)).filter (fun x => x ≤ N ∧ N - x ∈ S)
  have h : src.card ≤ windowCount S lower W := by
    apply Finset.card_le_card_of_injOn (fun x => N - x)
    · intro x hx
      obtain ⟨hb, hxN, hxS⟩ := Finset.mem_filter.1 hx
      have hx' := Finset.mem_Ico.1 hb
      change N - x ∈ S.filter (fun z => lower ≤ z ∧ z ≤ lower + W)
      exact Finset.mem_filter.2 ⟨hxS, by dsimp [lower]; omega, by dsimp [lower]; omega⟩
    · intro x hx y hy heq
      have hxN := (Finset.mem_filter.1 hx).2.1
      have hyN := (Finset.mem_filter.1 hy).2.1
      change N - x = N - y at heq
      omega
  exact h.trans (localCount _)

/-- A long interval contains a fresh replacement avoiding the chosen sum.
    Both the occupied points and their reflected copies are excluded. -/
theorem replacement_in_window (B P : Finset ℕ) (l W N Q : ℕ)
    (localCount : ∀ u, windowCount B u W ≤ Q)
    (hW : 2 * Q + 2 * P.card < W) :
    ∃ w, l ≤ w ∧ w < l + W ∧ w ∉ B ∪ P ∧ ∀ z ∈ B ∪ P, w + z ≠ N := by
  let I := Finset.Ico l (l + W)
  let occB := I.filter (· ∈ B)
  let occP := I.filter (· ∈ P)
  let refB := I.filter (fun x => x ≤ N ∧ N - x ∈ B)
  let refP := I.filter (fun x => x ≤ N ∧ N - x ∈ P)
  let blocked := (occB ∪ occP) ∪ (refB ∪ refP)
  have hb : occB.card ≤ Q := by
    apply (Finset.card_le_card (t := B.filter (fun x => l ≤ x ∧ x ≤ l + W)) ?_).trans (localCount l)
    intro x hx
    obtain ⟨hxI, hxB⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨hxB, (Finset.mem_Ico.1 hxI).1, (Finset.mem_Ico.1 hxI).2.le⟩
  have hp : occP.card ≤ P.card :=
    Finset.card_le_card (fun _ hx => (Finset.mem_filter.1 hx).2)
  have hpb (u : ℕ) : windowCount P u W ≤ P.card := Finset.card_filter_le _ _
  have hbr : refB.card ≤ Q := card_reflected_points localCount
  have hpr : refP.card ≤ P.card := card_reflected_points hpb
  have hblocked : blocked.card ≤ 2 * Q + 2 * P.card := by
    have h₁ := (Finset.card_union_le occB occP).trans (Nat.add_le_add hb hp)
    have h₂ := (Finset.card_union_le refB refP).trans (Nat.add_le_add hbr hpr)
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add h₁ h₂).trans (by omega))
  have hI : I.card = W := by
    change (Finset.Ico l (l + W)).card = W
    rw [Nat.card_Ico]
    omega
  obtain ⟨w, hw, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show blocked.card < I.card by rw [hI]; exact hblocked.trans_lt hW)
  obtain ⟨hwl, hwh⟩ := Finset.mem_Ico.1 hw
  refine ⟨w, hwl, hwh, ?_, ?_⟩
  · intro hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hm (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hw, hx⟩)))
    · exact hm (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hw, hx⟩)))
  · intro z hz he
    have hn : w ≤ N := by omega
    have hz' : N - w = z := by omega
    rcases Finset.mem_union.1 hz with hz | hz
    · exact hm (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hw, hn, hz' ▸ hz⟩)))
    · exact hm (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hw, hn, hz' ▸ hz⟩)))

end Erdos326

-- ==== Closure



open Filter Topology

namespace Erdos326

private lemma card_filter_union_le {B P : Finset ℕ} (test : ℕ → Prop) [DecidablePred test] :
    ((B ∪ P).filter test).card ≤ (B.filter test).card + P.card := by
  rw [Finset.filter_union]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_filter_le _ _) _)

private lemma count_window_mono {S T : Finset ℕ} (h : S ⊆ T) (u w : ℕ) :
    windowCount S u w ≤ windowCount T u w :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

private lemma countThrough_mono {S T : Finset ℕ} (h : S ⊆ T) (i : ℕ) :
    countThrough S i ≤ countThrough T i :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

private lemma count_profile_of_replacement {B D R : Finset ℕ}
    (hD : D ⊆ B) (hR : Disjoint R B)
    (profile : ∀ test : ℕ → Prop, ∀ [DecidablePred test],
      (R.filter (fun x => test (binIndex x))).card = (D.filter (fun x => test (binIndex x))).card)
    (i : ℕ) : countThrough ((B \ D) ∪ R) i = countThrough B i := by
  let test (x : ℕ) := x ≤ coarseEdge i
  have hc := profile (· ≤ i)
  simp only [binIndex_le_iff] at hc
  have he : (B \ D).filter test = B.filter test \ D.filter test := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hdis : Disjoint ((B \ D).filter test) (R.filter test) := by
    apply Finset.disjoint_left.2
    intro x hx hy
    exact Finset.disjoint_left.1 hR (Finset.mem_filter.1 hy).1
      (Finset.mem_sdiff.1 (Finset.mem_filter.1 hx).1).1
  change (((B \ D) ∪ R).filter test).card = (B.filter test).card
  rw [Finset.filter_union, Finset.card_union_of_disjoint hdis, he]
  change _ + (R.filter (· ≤ coarseEdge i)).card = _
  rw [hc]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ hD)

private lemma bin_cap {B : Finset ℕ} {j E : ℕ}
    (hB : ∀ x ∈ B, x ≤ coarseEdge j)
    (hcount : ∀ i, firstBin ≤ i → i ≤ j →
      3 * i + 2 ≤ countThrough B i ∧ countThrough B i ≤ 3 * i + 2 + E)
    (i : ℕ) (hi : firstBin < i) :
    (B.filter (fun x => binIndex x = i)).card ≤ E + 3 := by
  by_cases h : i ≤ j
  · let k := i - 1
    have hk : k + 1 = i := by dsimp [k]; omega
    have he := countThrough_succ B k
    rw [hk] at he
    have lo := (hcount k (by dsimp [k]; omega) (by dsimp [k]; omega)).1
    have up := (hcount i (by omega) h).2
    omega
  · have he : B.filter (fun x => binIndex x = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro x hx
      obtain ⟨hxB, hxi⟩ := Finset.mem_filter.1 hx
      have hidx := binIndex_le_iff.2 (hB x hxB)
      omega
    simp [he]

private lemma frozen_under_witness {B D R P : Finset ℕ} {X a N : ℕ}
    (hD : ∀ d ∈ D, X < d) (hR : ∀ w ∈ R, X < w)
    (hP : ∀ w ∈ P, X < w) (hW : X < N - a) :
    ∀ x ≤ X, x ∈ witnessCore B D R a N ∪ P ↔ x ∈ B := by
  intro x hx
  have hd : x ∉ D := fun h => (not_lt_of_ge hx) (hD x h)
  have hr : x ∉ R := fun h => (not_lt_of_ge hx) (hR x h)
  have hp : x ∉ P := fun h => (not_lt_of_ge hx) (hP x h)
  simp [witnessCore, hd, hr, hp, show x ≠ N - a by omega]

private lemma width_enough (p c K : ℕ) :
    let d := 16 * (p + 1)
    let W := d * (4 * (c + 2 * p + K + 1))
    2 * (c + p * (W / d + 2)) + 2 * K < W := by
  dsimp
  rw [Nat.mul_comm (16 * (p + 1)), Nat.mul_div_cancel _ (by omega : 0 < 16 * (p + 1))]
  nlinarith only [show 0 ≤ p * (c + 2 * p + K + 1) by positivity]

/-- The number of repairs permitted after choosing the odd target. -/
def repairBudget : ℕ := 49 * 81921 * 400000 ^ 2

def maxExcess : ℕ := repairBudget + 1

private lemma choose_stage_index (i E J q W H h₀ h₁ : ℕ) :
    ∃ t, i < t ∧ i + E ≤ t ∧ J ≤ t ∧ q ≤ t ∧ 1000 * (W + 1) ≤ t ∧
      10000 * H ≤ t ∧ 10000 * (h₀ + 1) ≤ t ∧ 10000 * (h₁ + 1) ≤ t := by
  refine ⟨i + E + J + q + 1000 * (W + 1) + 10000 * (H + h₀ + h₁ + 1) + 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Construct and certify a complete new stage, including its counting bounds. -/
theorem advance_stage (p : StagePrefix firstBin maxExcess) (a : ℕ) (ha : a ∈ p.points) :
    ∃ q : StagePrefix firstBin maxExcess, ∃ N,
      p.index < q.index ∧
      (∀ x ≤ coarseEdge p.index, x ∈ q.points ↔ x ∈ p.points) ∧
      coarseEdge p.index < N ∧ N ≤ coarseEdge q.index ∧
      AllRepresentationsUse q.points a N := by
  classical
  let cap := maxExcess + 3
  let spacing := 16 * (cap + 1)
  let J := max firstBin (1000 * (spacing + 1))
  let prefixCap := 3 * J + 2 + maxExcess
  let W := spacing * (4 * (prefixCap + 2 * cap + 400000 + 1))
  let Q := prefixCap + cap * (W / spacing + 2)
  let paletteBin := max firstBin (2 * cap + 400000 + repairBudget + 1) + 1
  let paletteWidth := coarseEdge paletteBin
  let shiftStart := 1000 * (paletteWidth + 2) + firstBin
  let shiftCut := coarseEdge shiftStart
  obtain ⟨t, ht₀, htE, hJt, hqt, htW, hshiftT, hscale₀, hscale₁⟩ :=
    choose_stage_index p.index maxExcess J paletteBin W shiftCut (blockStart 0 4) (blockStart 1 4)
  let j := 1000 * t
  let X := coarseEdge t
  let L := coarseEdge (2 * t)
  let Y := coarseEdge j
  have htpos : 0 < t := (Nat.zero_le _).trans_lt ht₀
  have hj : t ≤ j := Nat.le_mul_of_pos_left _ (by decide)
  have htL : t ≤ 2 * t := Nat.le_mul_of_pos_left _ (by decide)
  have hY₀ : coarseEdge p.index ≤ X := coarseEdge_monotone ht₀.le
  have hXLle : X ≤ L := coarseEdge_monotone htL
  have hXL : 2 * X ≤ L := (Nat.mul_le_mul_right X (by decide : 2 ≤ 4)).trans
    (coarseEdge_mul_ge 2 t)
  have hLY : 250000 * L ≤ Y := by
    have he := coarseEdge_mul_ge 500 (2 * t)
    change 250000 * L ≤ coarseEdge (500 * (2 * t)) at he
    rwa [show 500 * (2 * t) = j from (Nat.mul_assoc 500 2 t).symm] at he
  have hL : ∀ s : Fin 2, blockStart s 4 ≤ L := by
    have hb : t ≤ 3 * (2 * t) := htL.trans (Nat.le_mul_of_pos_left _ (by decide))
    intro s
    fin_cases s
    · exact (quadBin_cofinal _).trans (quadBin_monotone (hscale₀.trans hb))
    · exact (quadBin_cofinal _).trans (quadBin_monotone (hscale₁.trans hb))
  obtain ⟨B, hB, hAgree, hNew, hCount⟩ := extend_normally
    (by decide : 4000 ≤ firstBin) p (ht₀.le.trans hj)
  have hCounts (i : ℕ) (hi : firstBin ≤ i) (hij : i ≤ j) :
      3 * i + 2 ≤ countThrough B i ∧ countThrough B i ≤ 3 * i + 2 + maxExcess := by
    obtain ⟨hl, hu⟩ := hCount i hi hij
    exact ⟨hl, hu.trans (Nat.add_le_add_left (Nat.sub_le _ _) _)⟩
  have hExact (i : ℕ) (hi : t ≤ i) (hij : i ≤ j) : countThrough B i = 3 * i + 2 := by
    obtain ⟨hl, hu⟩ := hCount i (p.index_ge.trans (ht₀.le.trans hi)) hij
    omega
  have hold : p.points ⊆ B := fun x hx => (hAgree x (p.bounded x hx)).2 hx
  have haX : a ≤ X := (p.bounded a ha).trans hY₀
  have h0 : 0 ∈ B := by
    obtain ⟨x, hx, y, _, he⟩ := p.covered 0 (Nat.zero_le _)
    rw [show x = 0 by omega] at hx
    exact hold hx
  have hTargetCount : (B.filter (· ≤ 3 * L)).card ≤ 3 * (6 * t) := by
    have h4 : 4 * L ≤ coarseEdge (4 * t) := by
      have he := coarseEdge_mul_ge 2 (2 * t)
      rwa [show 2 * (2 * t) = 4 * t by omega] at he
    have he := hExact (4 * t) (Nat.le_mul_of_pos_left t (by decide))
      (Nat.mul_le_mul_right t (by decide : 4 ≤ 1000))
    have hcard : (B.filter (· ≤ 3 * L)).card ≤ countThrough B (4 * t) := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxB, hxL⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨hxB, hxL.trans (by omega)⟩
    omega
  have hL' : L = quadBin (6 * t) := by
    change quadBin (3 * (2 * t)) = _
    rw [show 3 * (2 * t) = 6 * t by omega]
  have hmin : 200 ≤ 6 * t := by
    have hfirst := p.index_ge
    unfold firstBin at hfirst
    omega
  rw [hL'] at hTargetCount
  obtain ⟨N, hN₀, hN₁, hodd, _hNd⟩ := exists_odd_target B (6 * t) hmin hTargetCount
  rw [← hL'] at hN₀ hN₁
  let D := upperEndpoints B N
  have hNd : D.card < 400000 := _hNd
  have hDsub : D ⊆ B := Finset.filter_subset _ _
  have hD (d : ℕ) (hd : d ∈ D) : L < d ∧ d ≤ N :=
    ⟨upperEndpoints_above hN₀ hd, (Finset.mem_filter.1 hd).2.1⟩
  have hHorizon : 24577 * N ≤ Y := by omega
  have h0D (d : ℕ) (hd : d ∈ D) : X < d := hXLle.trans_lt (hD d hd).1
  have hWcard : 2 * Q + 2 * 400000 < W := width_enough cap prefixCap 400000
  have hCap (i : ℕ) (hi : firstBin < i) :
      (B.filter (fun x => binIndex x = i)).card ≤ cap :=
    bin_cap hB hCounts i hi
  have localCount (u : ℕ) : windowCount B u W ≤ Q := by
    have hlo : 1000 * (spacing + 1) ≤ J := le_max_right _ _
    have hj' : firstBin ≤ J := le_max_left _ _
    have h := window_count_le (u := u) (w := W) (d := spacing)
      (show 0 < spacing by dsimp [spacing]; omega) hlo
      (fun i hi => hCap i (hj'.trans_lt hi))
    exact h.trans (Nat.add_le_add_right (hCounts J hj' (hJt.trans hj)).2 _)
  have available (P : Finset ℕ) (hp : P.card < D.card) (d : ℕ) (hd : d ∈ D) :
      ∃ w, w ∉ B ∪ P ∧ binIndex w = binIndex d ∧ ∀ z ∈ (B \ D) ∪ P, w + z ≠ N := by
    let k := binIndex d - 1
    have hkd : 2 * t < binIndex d := by
      by_contra! he
      exact (not_lt_of_ge (binIndex_le_iff.1 he)) (hD d hd).1
    have hk : 2 * t ≤ k := by dsimp [k]; omega
    have hkEq : binIndex d = k + 1 := by dsimp [k]; omega
    have hw : coarseEdge k + W ≤ coarseEdge (k + 1) :=
      coarseEdge_width_ge (htW.trans (htL.trans hk))
    obtain ⟨w, hlo, hhi, hfree, hsafe⟩ :=
      replacement_in_window B P (coarseEdge k + 1) W N Q localCount (by omega)
    refine ⟨w, hfree, ?_, ?_⟩
    · rw [hkEq, binIndex_succ_iff]
      omega
    · intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · exact hsafe z (Finset.mem_union_left _ (Finset.mem_sdiff.1 hz).1)
      · exact hsafe z (Finset.mem_union_right _ hz)
  obtain ⟨R, hRdis, hRcard, profile, hRfree⟩ :=
    replace_endpoints B D binIndex hodd (not_represented_after_deleting_endpoints B hodd) available
  have hR (w : ℕ) (hw : w ∈ R) : X < w ∧ w ≤ Y := by
    have hpos : 0 < (R.filter (fun x => binIndex x = binIndex w)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨hw, rfl⟩⟩
    have he := profile (· = binIndex w)
    rw [he] at hpos
    obtain ⟨d, hd'⟩ := Finset.card_pos.1 hpos
    obtain ⟨hd, heq⟩ := Finset.mem_filter.1 hd'
    have hlow : 2 * t < binIndex w := by
      rw [← heq]
      by_contra! hh
      exact (not_lt_of_ge (binIndex_le_iff.1 hh)) (hD d hd).1
    have hhigh : binIndex w ≤ j := heq ▸ (binIndex_le_iff.2 (hB d (hDsub hd)))
    have h' : L < w := by
      by_contra! hh
      exact (not_le_of_gt hlow) (binIndex_le_iff.2 hh)
    exact ⟨hXLle.trans_lt h', binIndex_le_iff.1 hhigh⟩
  have hM : 49 * 81921 * D.card ^ 2 ≤ repairBudget := by
    unfold repairBudget
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNd.le 2)
  have hbW : X < N - a := by omega
  let S := witnessCore B D R a N
  have hzB (P : Finset ℕ) (hPb : ∀ w ∈ P, X < w ∧ w ≤ Y) :
      ∀ x ≤ X, x ∈ S ∪ P ↔ x ∈ B :=
    frozen_under_witness h0D (fun x hx => (hR x hx).1) (fun x hx => (hPb x hx).1) hbW
  have hspace : (3 * t + 2) * shiftCut ≤ X := by
    change (3 * t + 2) * shiftCut ≤ (3 * t) ^ 2 / 10000
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2
    calc
      _ = (3 * t + 2) * (10000 * shiftCut) := by ring
      _ ≤ (3 * t + 2) * t := Nat.mul_le_mul_left _ hshiftT
      _ ≤ (3 * t) ^ 2 := by nlinarith only [htpos]
  have hShift (P : Finset ℕ) (hPc : P.card < 49 * 81921 * D.card ^ 2)
      (hPb : ∀ w ∈ P, X < w ∧ w ≤ Y) (n : ℕ) (_hlo : 2 * X < n) (hn : n < N) :
      ∃ u ∈ S ∪ P, u ≤ X ∧ u + (N - n) ∉ S ∪ P := by
    let d := N - n
    have hd : 0 < d := Nat.sub_pos_of_lt hn
    by_cases hs : d ≤ shiftCut
    · have hc : countThrough (S ∪ P) t = 3 * t + 2 := by
        rw [countThrough_of_agree (hzB P hPb), hExact t le_rfl hj]
      have hc' : ((S ∪ P).filter (· ≤ X)).card * d ≤ X := by
        change countThrough (S ∪ P) t * d ≤ X
        rw [hc]
        exact (Nat.mul_le_mul_left _ hs).trans hspace
      obtain ⟨u, hu, hux, hum⟩ := shift_avoided_in_prefix (S ∪ P)
        ((hzB P hPb 0 (Nat.zero_le _)).2 h0) hd hc'
      exact ⟨u, hu, by omega, hum⟩
    · let palette := B.filter (· ≤ paletteWidth)
      have hpX : paletteWidth ≤ X := coarseEdge_monotone hqt
      have hpS : palette ⊆ S ∪ P := by
        intro u hu
        obtain ⟨huB, hux⟩ := Finset.mem_filter.1 hu
        exact (hzB P hPb u (hux.trans hpX)).2 huB
      have hlc : windowCount B d paletteWidth ≤ 2 * cap :=
        late_window_count_le (J := shiftStart) (d := paletteWidth + 1)
          (by dsimp [shiftStart]; omega)
          (fun i hi => hCap i (by dsimp [shiftStart] at hi; omega))
          (by omega : shiftCut < d) (by omega)
      have hsub : S ∪ P ⊆ B ∪ R ∪ insert (N - a) P := by
        intro u hu
        rcases Finset.mem_union.1 hu with hu | hu
        · rcases Finset.mem_insert.1 hu with rfl | hu
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · rcases Finset.mem_union.1 hu with hu | hu
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.1 hu).1)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hu)
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hu)
      have hcomp : windowCount (S ∪ P) d paletteWidth ≤
          2 * cap + R.card + (P.card + 1) := calc
        _ ≤ windowCount (B ∪ R ∪ insert (N - a) P) d paletteWidth :=
          count_window_mono hsub _ _
        _ ≤ windowCount (B ∪ R) d paletteWidth + (insert (N - a) P).card :=
          card_filter_union_le _
        _ ≤ _ := Nat.add_le_add
          ((card_filter_union_le (B := B) (P := R) _).trans (Nat.add_le_add_right hlc _))
          (Finset.card_insert_le _ _)
      have hpCard : 3 * paletteBin + 2 ≤ palette.card :=
        (hCounts paletteBin ((le_max_left _ _).trans (Nat.le_succ _)) (hqt.trans hj)).1
      have hrlt : R.card < 400000 := hRcard ▸ hNd
      have hpless : P.card < repairBudget := hPc.trans_le hM
      have hcard : windowCount (S ∪ P) d paletteWidth < palette.card := calc
        _ ≤ 2 * cap + R.card + (P.card + 1) := hcomp
        _ ≤ 2 * cap + 400000 + (repairBudget + 1) :=
          Nat.add_le_add (Nat.add_le_add_left hrlt.le _) (Nat.add_le_add_right hpless.le 1)
        _ < paletteBin := by
          rw [← Nat.add_assoc]
          exact Nat.lt_succ_of_le (le_max_right _ _)
        _ ≤ 3 * paletteBin + 2 := (Nat.le_mul_of_pos_left _ (by decide)).trans (Nat.le_add_right _ _)
        _ ≤ palette.card := hpCard
      obtain ⟨u, hu, hux, hum⟩ := shift_avoided_by_card (S ∪ P) palette hpS
        (fun _ hu => (Finset.mem_filter.1 hu).2) hcard
      exact ⟨u, hu, hux.trans hpX, hum⟩
  have hBg (n : ℕ) (hn : coarseEdge p.index < n) (hnY : n ≤ Y)
      (s : Fin 2) : HasSelectedPair B s n :=
    let h := p.intact.extend hold hNew s n hn
    ⟨h.1 ((pair_bounds s n).1.trans hnY), h.2 ((pair_bounds s n).2.trans hnY)⟩
  obtain ⟨P, hPc, _hPb, hCover, hForced, hBound, hFreeze⟩ :=
    finish_finite_stage B D R hY₀ hXL hN₀ hN₁ hHorizon hL hB hD hR h0 (hold ha) haX
      hodd hRfree (fun n hn => (p.covered n hn).mono hold) hBg hShift
  let T := S ∪ P
  have hAdded : (insert (N - a) P).card ≤ maxExcess :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hPc.trans hM) 1)
  have hT : T = ((B \ D) ∪ R) ∪ insert (N - a) P := by
    ext x
    change x ∈ insert (N - a) ((B \ D) ∪ R) ∪ P ↔
      x ∈ ((B \ D) ∪ R) ∪ insert (N - a) P
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((hx | hx) | hx)
      · exact .inr (.inl hx)
      · exact .inl hx
      · exact .inr (.inr hx)
    · rintro (hx | hx | hx)
      · exact .inl (.inr hx)
      · exact .inl (.inl hx)
      · exact .inr hx
  have hLive (i : ℕ) : countThrough ((B \ D) ∪ R) i = countThrough B i :=
    count_profile_of_replacement hDsub hRdis profile i
  have hTC (i : ℕ) (hi : firstBin ≤ i) (hij : i ≤ j) :
      3 * i + 2 ≤ countThrough T i ∧ countThrough T i ≤ 3 * i + 2 + maxExcess := by
    by_cases hh : i ≤ t
    · rw [countThrough_of_agree (T := B)
        (fun x hx => hFreeze x (hx.trans (coarseEdge_monotone hh)))]
      exact hCounts i hi hij
    · have he := hExact i (not_le.mp hh).le hij
      have he' : countThrough ((B \ D) ∪ R) i = 3 * i + 2 := (hLive i).trans he
      constructor
      · rw [hT, ← he']
        exact countThrough_mono (fun _ hx => Finset.mem_union_left _ hx) i
      · rw [hT]
        exact (card_filter_union_le _).trans (Nat.add_le_add he'.le hAdded)
  have hIntact : IntactAfter T Y := by
    intro s n hn
    have hpair := p.intact.extend hold hNew s n (by omega : coarseEdge p.index < n)
    have htD : ¬ Hits D s n := by
      intro hg
      have hstart := ((blockStart_strictMono s).monotone (by decide : 2 ≤ 4)).trans (hL s)
      exact (not_lt_of_ge ((hit_sum_bounds hstart hD hg).2.trans hHorizon)) hn
    have add (x : ℕ) (hx : x ∈ B) (hnD : x ∉ D) : x ∈ T := by
      rw [hT]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hnD⟩))
    exact ⟨fun h => add _ (hpair.1 h) (fun hx => htD (.inl hx)),
      fun h => add _ (hpair.2 h) (fun hx => htD (.inr hx))⟩
  have hBefore : coarseEdge p.index < N := by omega
  have hAfter : N ≤ Y := by omega
  refine ⟨⟨j, T, p.index_ge.trans (ht₀.le.trans hj), hBound, hCover, hIntact, hTC⟩,
    N, ht₀.trans_le hj, ?_, hBefore, hAfter, hForced⟩
  intro x hx
  exact (hFreeze x (hx.trans hY₀)).trans (hAgree x hx)

private def StagePrefix.toFinePrefix (p : StagePrefix firstBin maxExcess) :
    FinitePrefix (3 * firstBin) (maxExcess + 4) where
  index := 3 * p.index
  points := p.points
  index_ge := Nat.mul_le_mul_left _ p.index_ge
  bounded := p.bounded
  coverage := p.covered
  counts i hi hij := by
    let l := i / 3
    let u := (i + 2) / 3
    have hl : 3 * l ≤ i := by dsimp [l]; omega
    have hu : i ≤ 3 * u := by dsimp [u]; omega
    have hl' : i ≤ 3 * l + 2 := by dsimp [l]; omega
    have hu' : 3 * u + 2 ≤ i + 4 := by dsimp [u]; omega
    have hlo := (p.counts l (by dsimp [l]; omega) (by dsimp [l]; omega)).1
    have hhi := (p.counts u (by dsimp [u]; omega) (by dsimp [u]; omega)).2
    have hcard (a b : ℕ) (h : a ≤ b) :
        (p.points.filter (· ≤ quadBin a)).card ≤ (p.points.filter (· ≤ quadBin b)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxP, hxb⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨hxP, hxb.trans (quadBin_monotone h)⟩
    change 3 * l + 2 ≤ (p.points.filter (· ≤ quadBin (3 * l))).card at hlo
    change (p.points.filter (· ≤ quadBin (3 * u))).card ≤ 3 * u + 2 + maxExcess at hhi
    exact ⟨hl'.trans (hlo.trans (hcard _ _ hl)),
      (hcard _ _ hu).trans (hhi.trans (by omega))⟩

/-- An affirmative solution to Erdős Problem 326, with limiting constant `1/10000`. -/
theorem erdos_326_fixed_limit :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 (1 / 10000 : ℝ)) := by
  obtain ⟨initial⟩ := initial_prefix maxExcess
  let Valid (p : FinitePrefix (3 * firstBin) (maxExcess + 4)) :=
    ∃ q : StagePrefix firstBin maxExcess, q.toFinePrefix = p
  apply exists_of_prefix_extensions Valid initial.toFinePrefix ⟨initial, rfl⟩
  intro p hp a ha
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q, N, hidx, hagree, hN₀, hN₁, hw⟩ := advance_stage p' a ha
  exact ⟨q.toFinePrefix, ⟨q, rfl⟩, ⟨Nat.mul_lt_mul_of_pos_left hidx (by decide), hagree⟩,
    ⟨N, hN₀, hN₁, hw⟩⟩

/-- The original problem statement, using an explicit sum-of-two definition of basis. -/
theorem erdos_326 :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  obtain ⟨a, ha, hm, ht⟩ := erdos_326_fixed_limit
  exact ⟨a, ha, hm, 1 / 10000, by norm_num, ht⟩

end Erdos326


-- ==== Statement



open scoped Pointwise

namespace Erdos326

/-- Equivalence with the order-two specialization of the definition used by
    Formal Conjectures, expressed with the cofinite filter and pointwise sums. -/
theorem asymptotic_basis_iff_cofinite_sum (A : Set ℕ) :
    IsAsymptoticBasisOrder2 A ↔ ∀ᶠ n in cofinite, n ∈ (2 : ℕ) • A := by
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  simp only [IsAsymptoticBasisOrder2, two_nsmul, Set.mem_add]

/-- Erdős #326 with the Formal Conjectures predicate unfolded. -/
theorem erdos_326_cofinite :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      Minimal (fun A : Set ℕ => ∀ᶠ n in cofinite, n ∈ (2 : ℕ) • A) (Set.range a) ∧
      ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  have h : IsAsymptoticBasisOrder2 =
      (fun A : Set ℕ => ∀ᶠ n in cofinite, n ∈ (2 : ℕ) • A) :=
    funext fun A => propext (asymptotic_basis_iff_cofinite_sum A)
  rw [← h]
  exact erdos_326

end Erdos326

end OMA.Port6

theorem OMA.solution : type_of% @Erdos326.erdos_326 := by
  have h := OMA.Port6.Erdos326.erdos_326_cofinite
  exact h
