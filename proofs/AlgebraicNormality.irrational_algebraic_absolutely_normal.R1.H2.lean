import OMAReductions.R_AlgebraicNormality_irrational_algebraic_absolutely_normal_R1

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-!
# Normality in base b implies normality in base b ^ k

For every integer base b at least 2, every k at least 1 and every real x normal
in base b, the number x is normal in base b ^ k. This is the forward direction
of Theorem 8.2 in Kuipers and Niederreiter, Uniform Distribution of Sequences
(1974), p. 72, which also argues through a frequency bound (Lemma 8.1, p. 71;
interval form, Exercise 8.8, p. 77). The first L digits of a number
in base b ^ k are its first k * L digits in base b, and multiplying by
(b ^ k) ^ i is multiplying by b ^ (k * i). So an occurrence of a block of L
digits in base b ^ k at position i is an occurrence of a block of k * L digits
in base b at position k * i. Each block frequency in base b ^ k is therefore
at most k times a block frequency in base b, and eventually at most
(k + 1) / (b ^ k) ^ L. The block-frequency criterion of Piatetski-Shapiro,
DivBlocks.normal_of_freq_bound, then gives normality in base b ^ k. The
criterion and the carry argument come from our proof that division by a
positive integer preserves normality, after the binary argument of
Kozachinskiy and Shen, Automatic Kolmogorov complexity, normality, and
finite-state dimension revisited, Theorem 4.

The digit-prefix and equidistribution lemmas in WallBridge are adapted from
Ralf Stephan's Apache-2.0 formalization of normal numbers in his fork of
formal-conjectures, revision a522a5352dd28df0b5ef08c213c368b5f6a5df6e, file
FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean.
This file modifies that work: the namespace, imports and attributes are
adapted, the rich-number results are omitted, and the lemmas are combined
with new material. The copyright and license notice above are retained.

The frequency criterion was formalized by Codex sessions (GPT-6). A Claude
Code session (claude-opus-5-5) wrote the base-power argument (digitPrefix_pow,
prefix_freq, pow_freq_bound and normal_pow) and assembled this file.
-/

open NormalNumber Filter Topology

namespace WallBridge

/-- The natural number formed by the first `k` base-`b` digits of the fractional part of `y`. -/
noncomputable def digitPrefix (b k : ℕ) (y : ℝ) : ℕ :=
  ⌊(b : ℝ) ^ k * Int.fract y⌋₊

/-- The natural number with base-`b` digits `w 0, …, w (k - 1)`, most significant first. -/
def ofBlock (b : ℕ) (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => b * ofBlock b w k + w k

/-- The proportion of indices `m < n` such that the fractional part of `s m` lies in `S`. -/
noncomputable def visitFreq (s : ℕ → ℝ) (S : Set ℝ) [DecidablePred (· ∈ S)] (n : ℕ) : ℝ :=
  (((Finset.range n).filter fun m => Int.fract (s m) ∈ S).card : ℝ) / n

theorem digitPrefix_zero (b : ℕ) (y : ℝ) : digitPrefix b 0 y = 0 := by
  simp [digitPrefix, Int.fract_lt_one]

theorem digitPrefix_succ {b : ℕ} (hb : 0 < b) (k : ℕ) (y : ℝ) :
    digitPrefix b (k + 1) y = b * digitPrefix b k y + digitSeq b y k := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have h : digitPrefix b (k + 1) y / b = digitPrefix b k y := by
    rw [digitPrefix, digitPrefix, ← Nat.floor_div_natCast]
    congr 1
    field_simp
    ring
  rw [← h]
  exact (Nat.div_add_mod _ _).symm

theorem digitPrefix_lt {b : ℕ} (hb : 0 < b) (k : ℕ) (y : ℝ) : digitPrefix b k y < b ^ k := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [digitPrefix, Nat.floor_lt (mul_nonneg hB.le (Int.fract_nonneg y))]
  push_cast
  exact mul_lt_of_lt_one_right hB (Int.fract_lt_one y)

theorem digitPrefix_eq_iff {b : ℕ} (hb : 0 < b) (k m : ℕ) (y : ℝ) :
    digitPrefix b k y = m ↔
      Int.fract y ∈ Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k) := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [digitPrefix, Nat.floor_eq_iff (mul_nonneg hB.le (Int.fract_nonneg y)), Set.mem_Ico,
    div_le_iff₀ hB, lt_div_iff₀ hB, mul_comm (Int.fract y)]

theorem digitPrefix_add {b : ℕ} (i j : ℕ) (x : ℝ) :
    digitPrefix b (i + j) x = digitPrefix b j ((b : ℝ) ^ i * x) + b ^ j * digitPrefix b i x := by
  have hnn : 0 ≤ (b : ℝ) ^ i * Int.fract x := mul_nonneg (by positivity) (Int.fract_nonneg x)
  have hfr : Int.fract ((b : ℝ) ^ i * x) =
      (b : ℝ) ^ i * Int.fract x - (⌊(b : ℝ) ^ i * Int.fract x⌋₊ : ℝ) := by
    have h1 : (b : ℝ) ^ i * x = (b : ℝ) ^ i * Int.fract x + ((b ^ i * ⌊x⌋ : ℤ) : ℝ) := by
      push_cast
      rw [← Int.fract_add_floor x]
      ring_nf
      simp
    rw [h1, Int.fract_add_intCast, Int.fract, ← Int.natCast_floor_eq_floor hnn]
    push_cast
    ring
  rw [digitPrefix, digitPrefix, digitPrefix, hfr, add_comm, ← Nat.floor_add_natCast]
  · congr 1
    rw [pow_add]
    push_cast
    ring
  · exact mul_nonneg (by positivity) (sub_nonneg.2 (Nat.floor_le hnn))

theorem digitSeq_add {b : ℕ} (i j : ℕ) (x : ℝ) :
    digitSeq b x (i + j) = digitSeq b ((b : ℝ) ^ i * x) j := by
  have h := digitPrefix_add (b := b) i (j + 1) x
  rw [← add_assoc] at h
  change digitPrefix b (i + j + 1) x % b = digitPrefix b (j + 1) ((b : ℝ) ^ i * x) % b
  rw [h, pow_succ, mul_comm (b ^ j) b, mul_assoc, Nat.add_mul_mod_self_left]

theorem mul_add_eq_mul_add_iff {b a r a' r' : ℕ} (hb : 0 < b) (hr : r < b) (hr' : r' < b) :
    b * a + r = b * a' + r' ↔ a = a' ∧ r = r' := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have h1 := congrArg (· / b) h
  have h2 := congrArg (· % b) h
  simp only [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr', add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h1 h2
  exact ⟨h1, h2⟩

theorem forall_digitSeq_eq_iff {b : ℕ} (hb : 0 < b) {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k : ℕ)
    (y : ℝ) : (∀ j < k, digitSeq b y j = w j) ↔ digitPrefix b k y = ofBlock b w k := by
  induction k with
  | zero => simp [digitPrefix_zero, ofBlock]
  | succ k ih =>
    rw [Nat.forall_lt_succ_right, ih, digitPrefix_succ hb, ofBlock,
      mul_add_eq_mul_add_iff hb (show digitSeq b y k < b from Nat.mod_lt _ hb) (hw k)]

theorem ofBlock_lt {b : ℕ} {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k : ℕ) : ofBlock b w k < b ^ k := by
  induction k with
  | zero => simp [ofBlock]
  | succ k ih =>
    calc b * ofBlock b w k + w k < b * (ofBlock b w k + 1) := by linarith [hw k]
      _ ≤ b * b ^ k := Nat.mul_le_mul_left _ ih
      _ = b ^ (k + 1) := by ring

theorem ofBlock_congr {b : ℕ} {w w' : ℕ → ℕ} (k : ℕ) (h : ∀ j < k, w j = w' j) :
    ofBlock b w k = ofBlock b w' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ofBlock, ofBlock, ih fun j hj => h j (by omega), h k (by omega)]

theorem exists_ofBlock_eq {b : ℕ} (hb : 0 < b) (k : ℕ) :
    ∀ m < b ^ k, ∃ w : ℕ → ℕ, (∀ j, w j < b) ∧ ofBlock b w k = m := by
  induction k with
  | zero =>
    intro m hm
    rw [pow_zero, Nat.lt_one_iff] at hm
    exact ⟨fun _ => 0, fun _ => hb, hm.symm⟩
  | succ k ih =>
    intro m hm
    obtain ⟨w, hw, hwm⟩ := ih (m / b) ((Nat.div_lt_iff_lt_mul hb).2 (by rwa [← pow_succ]))
    refine ⟨Function.update w k (m % b), fun j => ?_, ?_⟩
    · rcases eq_or_ne j k with rfl | hj
      · simpa using Nat.mod_lt m hb
      · simpa [hj] using hw j
    · rw [ofBlock, ofBlock_congr (w' := w) k fun j hj => Function.update_of_ne hj.ne _ _, hwm,
        Function.update_self]
      exact Nat.div_add_mod m b

theorem exists_extend {b k : ℕ} (hb : 0 < b) (wf : Fin k → ℕ) (hwf : ∀ j, wf j < b) :
    ∃ w : ℕ → ℕ, (∀ j, w j < b) ∧ ∀ j : Fin k, wf j = w j := by
  refine ⟨fun j => if hj : j < k then wf ⟨j, hj⟩ else 0, fun j => ?_, fun j => by simp [j.isLt]⟩
  dsimp only
  split_ifs
  exacts [hwf _, hb]

/-- A block of digits at position `i` corresponds to a `b`-adic interval for `b ^ i * x`. -/
theorem block_iff {b : ℕ} (hb : 0 < b) {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k i : ℕ) (x : ℝ) :
    (∀ j : Fin k, digitSeq b x (i + j) = w j) ↔
      Int.fract ((b : ℝ) ^ i * x) ∈ Set.Ico ((ofBlock b w k : ℝ) / (b : ℝ) ^ k)
        (((ofBlock b w k : ℝ) + 1) / (b : ℝ) ^ k) := by
  rw [← digitPrefix_eq_iff hb, ← forall_digitSeq_eq_iff hb hw, Fin.forall_iff]
  simp only [digitSeq_add]

theorem visitFreq_mono {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : ∀ y ∈ Set.Ico (0 : ℝ) 1, y ∈ S → y ∈ T)
    (n : ℕ) : visitFreq s S n ≤ visitFreq s T n := by
  refine div_le_div_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card fun m hm => ?_))
    (Nat.cast_nonneg _)
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, h _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩ hm.2⟩

theorem visitFreq_congr {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : S = T) : visitFreq s S = visitFreq s T := by
  subst h
  congr

theorem visitFreq_union {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : Disjoint S T) (n : ℕ) :
    visitFreq s (S ∪ T) n = visitFreq s S n + visitFreq s T n := by
  rw [visitFreq, visitFreq, visitFreq, ← add_div, ← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · simp only [Set.mem_union, Finset.filter_or]
  · exact Finset.disjoint_filter.2 fun _ _ h1 h2 => Set.disjoint_left.1 h h1 h2

/-- Frequencies of unions of consecutive `b`-adic intervals. -/
theorem tendsto_visitFreq_Ico {b : ℕ} {s : ℕ → ℝ}
    (hA : ∀ k, ∀ m < b ^ k, Tendsto (visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
      (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k)))
    (k : ℕ) {m₁ m₂ : ℕ} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ b ^ k) :
    Tendsto (visitFreq s (Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) ((m₂ : ℝ) / (b : ℝ) ^ k))) atTop
      (𝓝 (((m₂ : ℝ) - m₁) / (b : ℝ) ^ k)) := by
  induction m₂, h₁₂ using Nat.le_induction with
  | base =>
    rw [sub_self, zero_div]
    refine tendsto_const_nhds.congr fun n => ?_
    simp [visitFreq]
  | succ m₂ h ih =>
    have hdiv : (m₁ : ℝ) / (b : ℝ) ^ k ≤ (m₂ : ℝ) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (Nat.cast_le.2 h) (by positivity)
    have hdiv' : (m₂ : ℝ) / (b : ℝ) ^ k ≤ ((m₂ : ℝ) + 1) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hset : Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) (((m₂ + 1 : ℕ) : ℝ) / (b : ℝ) ^ k) =
        Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) ((m₂ : ℝ) / (b : ℝ) ^ k) ∪
          Set.Ico ((m₂ : ℝ) / (b : ℝ) ^ k) (((m₂ : ℝ) + 1) / (b : ℝ) ^ k) := by
      rw [Set.Ico_union_Ico_eq_Ico hdiv hdiv']
      push_cast
      rfl
    have hsum := ((ih (by omega)).add (hA k m₂ (by omega))).congr
      (f₂ := visitFreq s (Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) (((m₂ + 1 : ℕ) : ℝ) / (b : ℝ) ^ k)))
      fun n => by rw [visitFreq_congr hset, visitFreq_union Set.Ico_disjoint_Ico_same]
    convert hsum using 2
    push_cast
    ring

/-- `x` is normal in base `b` iff every `b`-adic interval has the expected frequency. -/
theorem isNormalInBase_iff_tendsto {b : ℕ} (hb : 0 < b) (x : ℝ) :
    IsNormalInBase b x ↔ ∀ k, ∀ m < b ^ k,
      Tendsto (visitFreq (fun n => (b : ℝ) ^ n * x) (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k)) := by
  constructor
  · intro h k m hm
    obtain ⟨w, hw, rfl⟩ := exists_ofBlock_eq hb k m hm
    refine (h k (fun j => w j) fun j => hw j).congr fun n => ?_
    simp only [visitFreq]
    congr 3
    exact Finset.filter_congr fun i _ => block_iff hb hw k i x
  · intro h k wf hwf
    obtain ⟨w, hw, hwf'⟩ := exists_extend hb wf hwf
    refine (h k _ (ofBlock_lt hw k)).congr fun n => ?_
    simp only [visitFreq, hwf']
    congr 3
    exact (Finset.filter_congr fun i _ => block_iff hb hw k i x).symm


theorem exists_one_div_pow_lt {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 / (b : ℝ) ^ k < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
    ((div_lt_one (by positivity)).2 (by exact_mod_cast (by omega : 1 < b)) : (1 : ℝ) / b < 1)
  exact ⟨k, by rwa [div_pow, one_pow] at hk⟩

theorem add_one_div_pow_le_one {b k m : ℕ} (hm : m < b ^ k) :
    ((m : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Nat.succ_le_of_lt hm) (by positivity)


/-- Frequencies of `b`-adic intervals determine uniform distribution modulo one. -/
theorem tendsto_Ico_iff_isEquidistributedModuloOne {b : ℕ} (hb : 2 ≤ b) (s : ℕ → ℝ) :
    (∀ k, ∀ m < b ^ k, Tendsto (visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
      (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k))) ↔
    IsEquidistributedModuloOne s := by
  constructor
  · intro hA c d hcd hsub
    have hc0 : 0 ≤ c := (hsub ⟨le_rfl, hcd⟩).1
    have hd1 : d ≤ 1 := (hsub ⟨hcd, le_rfl⟩).2
    have hd0 : 0 ≤ d := hc0.trans hcd
    change Tendsto (visitFreq s (Set.Icc c d)) atTop (𝓝 ((d - c) / (1 - 0)))
    rw [sub_zero, div_one, tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨k, hk⟩ := exists_one_div_pow_lt hb (show 0 < (d - c - a) / 2 by linarith)
      have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      set B := (b : ℝ) ^ k with hBdef
      set m₂ := ⌊d * B⌋₊ with hm₂def
      set m₁ := min ⌈c * B⌉₊ m₂ with hm₁def
      have hm₂ : m₂ ≤ b ^ k := Nat.floor_le_of_le (by
        push_cast
        exact mul_le_of_le_one_left hB.le hd1)
      have hlim := tendsto_visitFreq_Ico hA k (min_le_right ⌈c * B⌉₊ m₂) hm₂
      have h1 : (m₁ : ℝ) < c * B + 1 :=
        (Nat.cast_le.2 (min_le_left _ _)).trans_lt (Nat.ceil_lt_add_one (mul_nonneg hc0 hB.le))
      have h2 : d * B - 1 < m₂ := Nat.sub_one_lt_floor _
      have h3 : 2 < d * B - c * B - a * B := by
        have := (div_lt_iff₀ hB).1 hk
        linarith
      have hgt : a < ((m₂ : ℝ) - m₁) / B := by
        rw [lt_div_iff₀ hB]
        linarith
      refine (hlim.eventually (lt_mem_nhds hgt)).mono fun n hn => hn.trans_le (visitFreq_mono ?_ n)
      rintro y - ⟨hy1, hy2⟩
      have hlt : m₁ < m₂ := by exact_mod_cast (div_lt_div_iff_of_pos_right hB).1 (hy1.trans_lt hy2)
      have hm₁ : m₁ = ⌈c * B⌉₊ := by
        rw [hm₁def]
        refine min_eq_left ?_
        by_contra hne
        rw [not_le] at hne
        rw [hm₁def, min_eq_right hne.le] at hlt
        exact lt_irrefl _ hlt
      constructor
      · calc c ≤ (m₁ : ℝ) / B := by
              rw [le_div_iff₀ hB, hm₁]
              exact Nat.le_ceil _
          _ ≤ y := hy1
      · calc y ≤ (m₂ : ℝ) / B := hy2.le
          _ ≤ d := by
              rw [div_le_iff₀ hB]
              exact Nat.floor_le (mul_nonneg hd0 hB.le)
    · obtain ⟨k, hk⟩ := exists_one_div_pow_lt hb (show 0 < (a - (d - c)) / 2 by linarith)
      have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      set B := (b : ℝ) ^ k with hBdef
      have hBnat : ((b ^ k : ℕ) : ℝ) = B := by push_cast; rfl
      set m₁ := ⌊c * B⌋₊ with hm₁def
      set m₂ := min (⌊d * B⌋₊ + 1) (b ^ k) with hm₂def
      have hm₁ : m₁ ≤ b ^ k := Nat.floor_le_of_le (by
        rw [hBnat]
        exact mul_le_of_le_one_left hB.le (hcd.trans hd1))
      have hm₁₂ : m₁ ≤ m₂ := le_min
        ((Nat.floor_le_floor (mul_le_mul_of_nonneg_right hcd hB.le)).trans (Nat.le_succ _)) hm₁
      have hlim := tendsto_visitFreq_Ico hA k hm₁₂ (min_le_right _ _)
      have h1 : c * B - 1 < m₁ := Nat.sub_one_lt_floor _
      have h2 : (m₂ : ℝ) ≤ d * B + 1 := by
        have : (m₂ : ℝ) ≤ ((⌊d * B⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_le.2 (min_le_left _ _)
        push_cast at this
        linarith [Nat.floor_le (mul_nonneg hd0 hB.le)]
      have h3 : 2 < a * B - d * B + c * B := by
        have := (div_lt_iff₀ hB).1 hk
        linarith
      have hlt : ((m₂ : ℝ) - m₁) / B < a := by
        rw [div_lt_iff₀ hB]
        linarith
      refine (hlim.eventually (gt_mem_nhds hlt)).mono fun n hn => (visitFreq_mono ?_ n).trans_lt hn
      rintro y ⟨-, hy1⟩ ⟨hcy, hyd⟩
      constructor
      · calc (m₁ : ℝ) / B ≤ c := by
              rw [div_le_iff₀ hB]
              exact Nat.floor_le (mul_nonneg hc0 hB.le)
          _ ≤ y := hcy
      · rw [lt_div_iff₀ hB, hm₂def, Nat.cast_min, lt_min_iff]
        constructor
        · push_cast
          linarith [mul_le_mul_of_nonneg_right hyd hB.le, Nat.lt_floor_add_one (d * B)]
        · rw [hBnat]
          exact mul_lt_of_lt_one_left hB hy1
  · intro hud k m hm
    have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hc0 : 0 ≤ (m : ℝ) / (b : ℝ) ^ k := by positivity
    have hcd : (m : ℝ) / (b : ℝ) ^ k ≤ ((m : ℝ) + 1) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) hB.le
    have hd1 := add_one_div_pow_le_one hm
    have h1 : Tendsto (visitFreq s (Set.Icc _ _)) atTop _ :=
      hud _ _ hcd (Set.Icc_subset_Icc hc0 hd1)
    have h2 : Tendsto (visitFreq s (Set.Icc _ _)) atTop _ :=
      hud _ _ le_rfl (Set.Icc_subset_Icc (hc0.trans hcd) hd1)
    have hsplit (n : ℕ) : visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k)) n =
        visitFreq s (Set.Icc ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)) n -
          visitFreq s (Set.Icc (((m : ℝ) + 1) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)) n := by
      rw [eq_sub_iff_add_eq, ← visitFreq_union (Set.disjoint_left.2 fun y hy hy' =>
        lt_irrefl y (hy.2.trans_le hy'.1))]
      exact congrFun (visitFreq_congr (Set.Ico_union_Icc_eq_Icc hcd le_rfl)) n
    convert (h1.sub h2).congr fun n => (hsplit n).symm using 2
    ring

/-- A real number $\xi$ is normal in base $b$ if and only if $(b^n \xi)_{n \ge 0}$ is uniformly
distributed modulo $1$ [Wal49], [Bug12, Theorem 4.14]. -/
theorem isNormalInBase_iff_isEquidistributedModuloOne (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsNormalInBase b ξ ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * ξ :=
  (isNormalInBase_iff_tendsto (by omega) ξ).trans (tendsto_Ico_iff_isEquidistributedModuloOne hb _)


end WallBridge


namespace NormalDivision

open WallBridge (digitPrefix)

private theorem digitPrefix_mod {b : ℕ} (hb : 0 < b) (k : ℕ) (y : ℝ) :
    (digitPrefix b k y : ℤ) = ⌊(b : ℝ)^k*y⌋ % (b^k : ℕ) := by
  have BposR : 0 < (b : ℝ)^k := by positivity
  have hy : (b : ℝ)^k*y = (b : ℝ)^k*Int.fract y + (((b^k : ℕ) : ℤ)*⌊y⌋ : ℤ) := by
    push_cast
    rw [← mul_add, Int.fract_add_floor]
  rw [hy, Int.floor_add_intCast, Int.add_mul_emod_self_left]
  have h0 : 0 ≤ (b : ℝ)^k*Int.fract y := mul_nonneg BposR.le (Int.fract_nonneg _)
  rw [← Int.natCast_floor_eq_floor h0]
  apply (Int.emod_eq_of_lt (Int.natCast_nonneg _) ?_).symm
  exact_mod_cast (by
    unfold digitPrefix
    rw [Nat.floor_lt h0]
    push_cast
    exact mul_lt_of_lt_one_right BposR (Int.fract_lt_one y) : digitPrefix b k y < b^k)

theorem digitPrefix_mul {b m : ℕ} (hb : 0 < b) (hm : 0 < m) (k : ℕ) (y : ℝ) :
    ∃ c : ℕ, c < m ∧ digitPrefix b k ((m:ℝ)*y) = (m * digitPrefix b k y + c) % b^k := by
  let u := (b : ℝ)^k*y
  let c := ⌊(m:ℝ)*Int.fract u⌋₊
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnon : 0 ≤ (m:ℝ)*Int.fract u := mul_nonneg hmR.le (Int.fract_nonneg _)
  refine ⟨c, (Nat.floor_lt hnon).mpr (mul_lt_of_lt_one_right hmR (Int.fract_lt_one u)), ?_⟩
  have hf : ⌊(b:ℝ)^k*((m:ℝ)*y)⌋ = (m:ℤ)*⌊u⌋+c := by
    have hprod : (b:ℝ)^k*(m*y) = (m:ℝ)*Int.fract u + (((m:ℤ)*⌊u⌋ : ℤ):ℝ) := by
      push_cast
      rw [← mul_add, Int.fract_add_floor]
      dsimp [u]
      ring
    rw [hprod, Int.floor_add_intCast, ← Int.natCast_floor_eq_floor hnon, add_comm]
  apply Nat.cast_injective (R := ℤ)
  rw [digitPrefix_mod hb, hf, Int.natCast_emod, Nat.cast_add, Nat.cast_mul, digitPrefix_mod hb]
  change (↑m * ⌊u⌋ + ↑c) % ↑(b^k) = (↑m * (⌊u⌋ % ↑(b^k)) + ↑c) % ↑(b^k)
  simp [Int.add_emod, Int.mul_emod]

end NormalDivision

/- Overlapping block counts and consecutive nonoverlapping sample positions. -/
open Filter Topology
namespace DivBlocks

def window {b : ℕ} (s : ℕ → Fin b) (i k : ℕ) : Fin k → Fin b :=
  fun t => s (i + t.val)

noncomputable def freq {b k : ℕ} (s : ℕ → Fin b) (w : Fin k → Fin b) (N : ℕ) : ℝ :=
  ((Finset.range N).filter (fun i => window s i k = w)).card / (N : ℝ)

def subblock {b k L : ℕ} (w : Fin (k*L) → Fin b) (j : Fin L) : Fin k → Fin b :=
  fun t => w ⟨k*j.val+t.val, by nlinarith [j.isLt, t.isLt, Nat.mul_le_mul_left k j.isLt]⟩

noncomputable def score {b k L : ℕ} (w : Fin (k*L) → Fin b) (v : Fin k → Fin b) : ℝ :=
  ((Finset.univ.filter (fun j : Fin L => subblock w j = v)).card : ℝ) / L

end DivBlocks

/- Finite second moment of occurrences at disjoint positions in a long digit block. -/

namespace DivBlocks

private theorem sum_succ_words {A : Type} [Fintype A] {n : ℕ}
    (f : (Fin (n+1) → A) → ℝ) :
    ∑ u, f u = ∑ a : A, ∑ u : Fin n → A, f (Fin.cons a u) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  exact Fintype.sum_prod_type _

private theorem centered_word_moments {A : Type} [Fintype A] (g : A → ℝ)
    (hg : ∑ a, g a = 0) (hg2 : ∀ a, g a ^ 2 ≤ 1) (n : ℕ) :
    (∑ u : Fin n → A, ∑ i, g (u i)) = 0 ∧
    (∑ u : Fin n → A, (∑ i, g (u i)) ^ 2) ≤ (Fintype.card A : ℝ)^n * n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let C := (Fintype.card A : ℝ)
    have hC : 0 ≤ C := by positivity
    have hsplit (a : A) (u : Fin n → A) :
        ∑ i, g (Fin.cons (α := fun _ : Fin (n+1) => A) a u i) = g a + ∑ j, g (u j) := by simp [Fin.sum_univ_succ]
    constructor
    · rw [sum_succ_words]
      simp only [hsplit, Finset.sum_add_distrib, ih.1, add_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      rw [← Finset.mul_sum, hg, mul_zero]
    · rw [sum_succ_words]
      simp only [hsplit, add_sq, Finset.sum_add_distrib, ← Finset.mul_sum, ih.1, mul_zero,
        add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      have hsq : (∑ a, g a ^ 2) ≤ C := by
        simpa [C] using Finset.sum_le_sum (s := Finset.univ) (fun a _ => hg2 a)
      calc C ^ n * ∑ a, g a ^ 2 + C * (∑ u : Fin n → A, (∑ i, g (u i)) ^ 2)
          ≤ C^n * C + C * (C^n * n) :=
            add_le_add (mul_le_mul_of_nonneg_left hsq (pow_nonneg hC _)) (mul_le_mul_of_nonneg_left ih.2 hC)
        _ = _ := by push_cast; change _ = C^(n+1)*_; ring

private def blocksEquiv (b k L : ℕ) :
    (Fin (k*L) → Fin b) ≃ (Fin L → Fin k → Fin b) :=
  (((finProdFinEquiv.trans (finCongr (Nat.mul_comm L k))).symm).arrowCongr (Equiv.refl _)).trans
    (Equiv.curry _ _ _)

private theorem blocksEquiv_apply {b k L : ℕ} (w : Fin (k*L) → Fin b) (j : Fin L) :
    blocksEquiv b k L w j = subblock w j := by
  funext t
  change w ⟨t.val + k*j.val, _⟩ = w ⟨k*j.val + t.val, _⟩
  congr 1
  apply Fin.ext
  exact Nat.add_comm _ _

theorem variance_score {b k L : ℕ} (hb : 2 ≤ b) (_hk : 0 < k) (hL : 0 < L)
    (v : Fin k → Fin b) :
    (∑ w : Fin (k*L) → Fin b, (score w v - 1 / (b^k : ℕ)) ^ 2) /
      (b^(k*L) : ℕ) ≤ 1 / (L : ℝ) := by
  classical
  let p : ℝ := 1 / (b^k : ℕ)
  let g : (Fin k → Fin b) → ℝ := fun z => (if z = v then 1 else 0) - p
  have hb' : 0 < b := by omega
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < (b^k : ℕ))).mpr
    exact_mod_cast Nat.one_le_pow k b hb'
  have hg : ∑ a, g a = 0 := by
    simp [g, Finset.sum_sub_distrib, p, hb'.ne']
  have h2 (a) : g a ^ 2 ≤ 1 := by
    by_cases heq : a = v
    · simp only [g, if_pos heq]
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hp1)]
    · simp only [g, if_neg heq, zero_sub, neg_sq]
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hp1)]
  have hm := (centered_word_moments g hg h2 L).2
  have hl : 0 < (L : ℝ) := by exact_mod_cast hL
  have hquad (w : Fin (k*L) → Fin b) :
      (score w v - p)^2 = (∑ i, g (blocksEquiv b k L w i))^2 / (L : ℝ)^2 := by
    simp only [g, blocksEquiv_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_boole]
    unfold score
    field_simp
  change (∑ w, (score w v - p)^2)/_ ≤ _
  simp_rw [hquad]
  rw [← Finset.sum_div, (blocksEquiv b k L).sum_comp (fun u => (∑ i, g (u i))^2)]
  rw [div_le_div_iff₀ (by positivity) hl, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hl)]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hm ⊢
  rw [pow_mul]
  nlinarith [mul_le_mul_of_nonneg_right hm hl.le]

end DivBlocks

/- Sliding-window counts for disjoint samples within each long observed block. -/

open Filter Topology
namespace DivBlocks

private theorem avg_weight {b k : ℕ} (s : ℕ → Fin b) (a : (Fin k → Fin b) → ℝ) (N : ℕ) :
    (∑ w, freq s w N * a w) = (∑ i ∈ Finset.range N, a (window s i k)) / N := by
  classical
  unfold freq
  calc
    _ = (∑ w, ∑ i ∈ Finset.range N, if window s i k = w then a w else 0) / N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_filter]
      simp [div_mul_eq_mul_div]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem sum_freq {b k : ℕ} (s : ℕ → Fin b) {N : ℕ} (hN : 0 < N) :
    (∑ w : Fin k → Fin b, freq s w N) = 1 := by
  simpa [Nat.ne_of_gt hN] using avg_weight (k := k) s (fun _ => 1) N

private theorem score_average {b k L : ℕ} (s : ℕ → Fin b) (v : Fin k → Fin b) (N : ℕ) :
    (∑ w : Fin (k*L) → Fin b, freq s w N * score w v) =
    (∑ j : Fin L, (∑ i ∈ Finset.range N,
      if window s (i+k*j.val) k = v then (1:ℝ) else 0) / N) / L := by
  classical
  have heq (i : ℕ) (j : Fin L) : subblock (window s i (k*L)) j = window s (i+k*j.val) k := by
    funext t
    simp [subblock, window, Nat.add_assoc]
  rw [avg_weight]
  unfold score
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, heq]
  simp_rw [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

private theorem shift_delta {f : ℕ → ℝ} (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) (d : ℕ) :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, f (i+d)) / N -
      (∑ i ∈ Finset.range N, f i) / N) atTop (𝓝 0) := by
  have total (N : ℕ) :
      (∑ i ∈ Finset.range N, f (i+d)) - (∑ i ∈ Finset.range N, f i) =
      (∑ i ∈ Finset.range d, f (i+N)) - (∑ i ∈ Finset.range d, f i) := by
    have e : (∑ i ∈ Finset.range (d+N), f i) = ∑ i ∈ Finset.range (N+d), f i := by
      rw [Nat.add_comm d N]
    rw [Finset.sum_range_add, Finset.sum_range_add] at e
    simpa only [Nat.add_comm] using (show
      (∑ i ∈ Finset.range N, f (d+i)) - (∑ i ∈ Finset.range N, f i) =
      (∑ i ∈ Finset.range d, f (N+i)) - (∑ i ∈ Finset.range d, f i) by linarith)
  have lower (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) : 0 ≤ ∑ i ∈ Finset.range d, g i :=
    Finset.sum_nonneg (fun i _ => hg i)
  have upper (g : ℕ → ℝ) (hg : ∀ i, g i ≤ 1) : (∑ i ∈ Finset.range d, g i) ≤ d :=
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.range d) => hg i)).trans_eq (by simp)
  have lim := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (d : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun N : ℕ => -((d:ℝ)/N))
    (h := fun N : ℕ => (d:ℝ)/N) (by simpa using lim.neg) lim
  · intro N
    dsimp only
    rw [← sub_div, total, ← neg_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    linarith [lower (fun i => f (i+N)) (fun _ => h0 _), upper f h1]
  · intro N
    dsimp only
    rw [← sub_div, total]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    linarith [lower f h0, upper (fun i => f (i+N)) (fun _ => h1 _)]

theorem score_average_tendsto {b k L : ℕ} (s : ℕ → Fin b) (v : Fin k → Fin b) (hL : 0 < L) :
    Tendsto (fun N => (∑ w : Fin (k*L) → Fin b, freq s w N * score w v) - freq s v N)
      atTop (𝓝 0) := by
  classical
  let f : ℕ → ℝ := fun i => if window s i k = v then 1 else 0
  have h0 (i : ℕ) : 0 ≤ f i := by simp [f]; split <;> norm_num
  have h1 (i : ℕ) : f i ≤ 1 := by simp [f]; split <;> norm_num
  have sums := tendsto_finsetSum (s := (Finset.univ : Finset (Fin L)))
    (fun j _ => shift_delta h0 h1 (k*j.val))
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have ht := sums.div_const (L:ℝ)
  simp only [Finset.sum_const_zero, zero_div] at ht
  refine ht.congr fun N => ?_
  rw [score_average, Finset.sum_sub_distrib]
  have hf : (∑ i ∈ Finset.range N, f i) / N = freq s v N := by
    simp only [freq, f, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hf, sub_div, f]
  field_simp

end DivBlocks

/- A uniform upper bound on block frequencies implies normality. -/
open Filter Topology
namespace DivBlocks

private theorem weighted_deviation {α : Type*} [Fintype α] (f t : α → ℝ) (p D : ℝ)
    (hn : ∀ a, 0 ≤ f a) (hs : ∑ a, f a = 1) (hD : ∀ a, f a ≤ D) :
    ((∑ a, f a * t a) - p)^2 ≤ D * ∑ a, (t a - p)^2 := by
  have he : (∑ a, f a * (t a - p)) = (∑ a, f a * t a) - p := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  rw [← he]
  calc
    _ ≤ (∑ a, f a) * ∑ a, f a * (t a - p)^2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (fun i _ => hn i)
        (fun i _ => mul_nonneg (hn i) (sq_nonneg _)) (fun i _ => by rw [mul_pow]; ring_nf; rfl)
    _ ≤ D * ∑ a, (t a - p)^2 := by
      rw [hs, one_mul, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _))

theorem normal_of_freq_bound {b : ℕ} (s : ℕ → Fin b) (C : ℝ) (hC : 0 ≤ C)
    (bound : ∀ k (w : Fin k → Fin b), ∀ᶠ N in atTop, freq s w N ≤ C / (b : ℝ)^k)
    (mass : ∀ k N, 0 < N → ∑ w : Fin k → Fin b, freq s w N = 1)
    (moment : ∀ k L, 0 < k → 0 < L → ∀ v : Fin k → Fin b,
      (∑ w : Fin (k*L) → Fin b, (score w v - 1/(b : ℝ)^k)^2) / (b : ℝ)^(k*L) ≤ 1/(L : ℝ))
    (shift : ∀ k L, 0 < L → ∀ v : Fin k → Fin b,
      Tendsto (fun N => (∑ w : Fin (k*L) → Fin b, freq s w N * score w v) - freq s v N)
        atTop (𝓝 0)) :
    ∀ k (v : Fin k → Fin b), Tendsto (freq s v) atTop (𝓝 (1/(b : ℝ)^k)) := by
  intro k v
  rcases k.eq_zero_or_pos with rfl | hk
  · have hconst : ∀ᶠ N : ℕ in atTop, freq s v N = 1 := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Subsingleton.elim v default]
      simpa using mass 0 N hN
    simpa using (tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm) : Tendsto (freq s v) atTop (𝓝 1))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε/2 := by positivity
  have he2 := sq_pos_of_pos he
  obtain ⟨L, hL⟩ := exists_nat_gt (C/(ε/2)^2)
  have hLpos : (0 : ℝ) < L := (div_nonneg hC he2.le).trans_lt hL
  have hLn : 0 < L := by exact_mod_cast hLpos
  have hsmall : C * (1/(L:ℝ)) < (ε/2)^2 := by
    rw [mul_one_div, div_lt_iff₀ hLpos]
    exact (div_lt_iff₀ he2).mp hL |>.trans_eq (mul_comm _ _)
  have hmoment := mul_le_mul_of_nonneg_left (moment k L hk hLn v) hC
  have hu : ∀ᶠ N in atTop, ∀ w : Fin (k*L) → Fin b, freq s w N ≤ C/(b:ℝ)^(k*L) :=
    Filter.eventually_all.mpr (bound (k*L))
  have hshift := (Metric.tendsto_nhds.mp (shift k L hLn v)) (ε/2) he
  filter_upwards [hu, hshift, eventually_gt_atTop 0] with N hN hδ hpos
  let μ := ∑ w : Fin (k*L) → Fin b, freq s w N * score w v
  let p := 1 / (b:ℝ)^k
  have hweight := weighted_deviation (fun w : Fin (k*L) → Fin b => freq s w N)
    (fun w => score w v) p (C/(b:ℝ)^(k*L)) (fun w => by unfold freq; positivity)
    (mass _ _ hpos) hN
  have ht : (μ - p)^2 < (ε/2)^2 := by
    apply hweight.trans_lt
    apply lt_of_le_of_lt _ hsmall
    simpa only [div_mul_eq_mul_div, mul_div_assoc] using hmoment
  have hclose : |μ - p| < ε/2 := abs_lt_of_sq_lt_sq ht he.le
  change dist (μ - freq s v N) 0 < ε/2 at hδ
  rw [Real.dist_eq, sub_zero] at hδ
  change |freq s v N - p| < ε
  rw [abs_lt] at hδ hclose ⊢
  constructor <;> linarith [hδ.1, hδ.2, hclose.1, hclose.2]

end DivBlocks

/- A quotient digit block covers at most one input digit block for each possible carry. -/
open Filter Topology NormalNumber
namespace DivBlocks

noncomputable def digits {b : ℕ} (hb : 0 < b) (x : ℝ) (i : ℕ) : Fin b :=
  ⟨digitSeq b x i, Nat.mod_lt _ hb⟩

private theorem window_eq_digits {b k : ℕ} (hb : 0 < b) (x : ℝ) (w : Fin k → Fin b) (i : ℕ) :
    window (digits hb x) i k = w ↔ ∀ j : Fin k, digitSeq b x (i + j) = (w j).val := by
  constructor
  · intro h j
    exact congrArg Fin.val (congrFun h j)
  · intro h
    exact funext fun j => Fin.ext (h j)

theorem normal_iff_freq {b : ℕ} (hb : 0 < b) (x : ℝ) :
    IsNormalInBase b x ↔ ∀ k (w : Fin k → Fin b),
      Tendsto (freq (digits hb x) w) atTop (𝓝 (1 / (b : ℝ)^k)) := by
  classical
  constructor
  · intro hx k w
    refine (hx k (fun j => (w j).val) fun j => (w j).isLt).congr fun n => ?_
    unfold freq
    congr 3
    exact Finset.filter_congr fun i _ => (window_eq_digits hb x w i).symm
  · intro hx k wf hwf
    let w (j : Fin k) : Fin b := ⟨wf j, hwf j⟩
    refine (hx k w).congr fun n => ?_
    unfold freq
    congr 3
    exact Finset.filter_congr fun i _ => window_eq_digits hb x w i

private theorem window_eq_prefix {b k : ℕ} (hb : 0 < b) (x : ℝ) (wf : Fin k → Fin b)
    (w : ℕ → ℕ) (hw : ∀ j, w j < b) (he : ∀ j : Fin k, (wf j).val = w j) (i : ℕ) :
    window (digits hb x) i k = wf ↔
      WallBridge.digitPrefix b k ((b : ℝ)^i*x) = WallBridge.ofBlock b w k := by
  rw [window_eq_digits, ← WallBridge.forall_digitSeq_eq_iff hb hw, Fin.forall_iff]
  simp only [WallBridge.digitSeq_add, he]

/-- A prescribed quotient block has at most `m` possible blocks in its multiple.
The extra unit makes the upper bound valid at every sufficiently large sample size. -/
theorem div_freq_eventually {b m : ℕ} {x : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hx : IsNormalInBase b x) (k : ℕ) (w : Fin k → Fin b) :
    ∀ᶠ N in atTop, freq (digits hb ((m : ℝ)⁻¹*x)) w N ≤ ((m : ℝ)+1)/(b : ℝ)^k := by
  classical
  obtain ⟨W, hW, he⟩ := WallBridge.exists_extend hb (fun j => (w j).val) fun j => (w j).isLt
  let a := WallBridge.ofBlock b W k
  let q (c : ℕ) := (m*a+c) % b^k
  let hit (c N : ℕ) := (Finset.range N).filter fun i =>
    WallBridge.digitPrefix b k ((b : ℝ)^i*x) = q c
  let g (c N : ℕ) : ℝ := ((hit c N).card : ℝ) / N
  have hg (c : ℕ) : Tendsto (g c) atTop (𝓝 (1 / (b : ℝ)^k)) := by
    obtain ⟨u, hu, hq⟩ := WallBridge.exists_ofBlock_eq hb k (q c) (Nat.mod_lt _ (pow_pos hb _))
    let v (j : Fin k) : Fin b := ⟨u j, hu j⟩
    refine ((normal_iff_freq hb x).mp hx k v).congr fun N => ?_
    unfold freq g hit
    congr 3
    exact Finset.filter_congr fun i _ => hq ▸ window_eq_prefix hb x v u hu (fun _ => rfl) i
  have hbnd (N : ℕ) : freq (digits hb ((m : ℝ)⁻¹*x)) w N ≤ ∑ c ∈ Finset.range m, g c N := by
    have hsub : ((Finset.range N).filter fun i => window (digits hb ((m : ℝ)⁻¹*x)) i k = w) ⊆
        (Finset.range m).biUnion (fun c => hit c N) := by
      intro i hi
      obtain ⟨hiN, hwi⟩ := Finset.mem_filter.mp hi
      have ha := (window_eq_prefix hb _ w W hW he i).mp hwi
      obtain ⟨c, hc, hcarry⟩ := NormalDivision.digitPrefix_mul hb hm k ((b : ℝ)^i*((m : ℝ)⁻¹*x))
      have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      have hmprod : (m : ℝ)*((b : ℝ)^i*((m : ℝ)⁻¹*x)) = (b : ℝ)^i*x := by
        field_simp
      change WallBridge.digitPrefix _ _ _ = (m*WallBridge.digitPrefix b k _+c) % _ at hcarry
      rw [hmprod, ha] at hcarry
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_range.mpr hc, Finset.mem_filter.mpr ⟨hiN,hcarry⟩⟩
    unfold g freq
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hlim : Tendsto (fun N => ∑ c ∈ Finset.range m, g c N) atTop
      (𝓝 ((m : ℝ) * (1 / (b : ℝ)^k))) := by
    simpa using tendsto_finsetSum (Finset.range m) (fun c _ => hg c)
  have hlt : (m : ℝ) * (1 / (b : ℝ)^k) < ((m : ℝ)+1)/(b : ℝ)^k := by
    rw [← mul_div_assoc, mul_one]
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  exact (hlim.eventually_le_const hlt).mono fun N hN => (hbnd N).trans hN

end DivBlocks

open Filter Topology NormalNumber

namespace DivBlocks

/-- The first `L` digits in base `b ^ k` are the first `k * L` digits in base `b`. -/
theorem digitPrefix_pow (b k L : ℕ) (y : ℝ) :
    WallBridge.digitPrefix (b ^ k) L y = WallBridge.digitPrefix b (k * L) y := by
  unfold WallBridge.digitPrefix
  rw [Nat.cast_pow, ← pow_mul]

/-- For `x` normal in base `b`, each value of the first `n` digits of `b ^ i * x`
occurs with frequency `1 / b ^ n`. -/
theorem prefix_freq {b : ℕ} (hb : 0 < b) {x : ℝ} (hx : IsNormalInBase b x) (n a : ℕ)
    (ha : a < b ^ n) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter
      fun i => WallBridge.digitPrefix b n ((b : ℝ) ^ i * x) = a).card : ℝ) / N)
      atTop (𝓝 (1 / (b : ℝ) ^ n)) := by
  obtain ⟨u, hu, hq⟩ := WallBridge.exists_ofBlock_eq hb n a ha
  let v (j : Fin n) : Fin b := ⟨u j, hu j⟩
  refine ((normal_iff_freq hb x).mp hx n v).congr fun N => ?_
  unfold freq
  congr 3
  exact Finset.filter_congr fun i _ => hq ▸ window_eq_prefix hb x v u hu (fun _ => rfl) i

/-- Block frequencies in base `b ^ k` are eventually at most `(k + 1) / (b ^ k) ^ L`. -/
theorem pow_freq_bound {b k : ℕ} (hb : 0 < b) (hk : 0 < k) {x : ℝ} (hx : IsNormalInBase b x)
    (hB : 0 < b ^ k) (L : ℕ) (w : Fin L → Fin (b ^ k)) :
    ∀ᶠ N in atTop, freq (digits hB x) w N ≤ ((k : ℝ) + 1) / ((b ^ k : ℕ) : ℝ) ^ L := by
  classical
  obtain ⟨W, hW, he⟩ := WallBridge.exists_extend hB (fun j => (w j).val) fun j => (w j).isLt
  have hn : WallBridge.ofBlock (b ^ k) W L < b ^ (k * L) := by
    rw [pow_mul]
    exact WallBridge.ofBlock_lt hW L
  let hit (M : ℕ) := (Finset.range M).filter
    fun m => WallBridge.digitPrefix b (k * L) ((b : ℝ) ^ m * x) = WallBridge.ofBlock (b ^ k) W L
  have hev (i : ℕ) : window (digits hB x) i L = w ↔
      WallBridge.digitPrefix b (k * L) ((b : ℝ) ^ (k * i) * x) =
        WallBridge.ofBlock (b ^ k) W L := by
    rw [window_eq_prefix hB x w W hW he i, digitPrefix_pow, Nat.cast_pow, ← pow_mul]
  have hcount (N : ℕ) :
      ((Finset.range N).filter fun i => window (digits hB x) i L = w).card ≤
        (hit (k * N)).card := by
    refine Finset.card_le_card_of_injOn (fun i => k * i) ?_ ?_
    · intro i hi
      obtain ⟨hiN, hwi⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨?_, (hev i).mp hwi⟩
      rw [Finset.mem_range] at hiN ⊢
      exact Nat.mul_lt_mul_of_pos_left hiN hk
    · intro i _ j _ hij
      exact Nat.eq_of_mul_eq_mul_left hk hij
  have hkN : Tendsto (fun N : ℕ => k * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id
  have hlim := ((prefix_freq hb hx (k * L) _ hn).comp hkN).const_mul (k : ℝ)
  have hlt : (k : ℝ) * (1 / (b : ℝ) ^ (k * L)) < ((k : ℝ) + 1) / ((b ^ k : ℕ) : ℝ) ^ L := by
    rw [Nat.cast_pow, ← pow_mul, ← mul_div_assoc, mul_one]
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  filter_upwards [hlim.eventually_le_const hlt, eventually_gt_atTop 0] with N hN hN0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc freq (digits hB x) w N
      = (((Finset.range N).filter fun i => window (digits hB x) i L = w).card : ℝ) / N := rfl
    _ ≤ ((hit (k * N)).card : ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hNR.le
        exact_mod_cast hcount N
    _ = (k : ℝ) * (((hit (k * N)).card : ℝ) / ((k * N : ℕ) : ℝ)) := by
        rw [Nat.cast_mul]
        field_simp
    _ ≤ ((k : ℝ) + 1) / ((b ^ k : ℕ) : ℝ) ^ L := hN

/-- Normality in base `b` implies normality in base `b ^ k` for every `k ≥ 1`. -/
theorem normal_pow {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (x : ℝ) (hx : IsNormalInBase b x) :
    IsNormalInBase (b ^ k) x := by
  have hb0 : 0 < b := by omega
  have hB : 0 < b ^ k := pow_pos hb0 k
  have hB2 : 2 ≤ b ^ k := le_trans hb (Nat.le_self_pow (by omega) b)
  apply (normal_iff_freq hB x).mpr
  apply normal_of_freq_bound (digits hB x) ((k : ℝ) + 1) (by positivity)
  · exact fun L w => pow_freq_bound hb0 hk hx hB L w
  · exact fun _ _ hN => sum_freq _ hN
  · intro L M hL hM v
    simpa only [Nat.cast_pow] using variance_score hB2 hL hM v
  · exact fun _ _ hM v => score_average_tendsto _ v hM

end DivBlocks

theorem OMA.solution : OMA.R_AlgebraicNormality_irrational_algebraic_absolutely_normal_R1.H2 := by
  intro b k hb hk x hx
  exact DivBlocks.normal_pow hb hk x hx
