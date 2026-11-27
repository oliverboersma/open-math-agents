import OMAReductions.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1

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
# Nonzero integer multiples preserve normality in a fixed base

This is the integer-multiplier case of Wall's theorem (1949). See Doty, Lutz
and Nandakumar, Finite-State Dimension and Real Arithmetic, Corollary 4.4.

The digit and equidistribution lemmas in WallBridge are adapted from the
Apache-2.0 Lean proof in Ralf Stephan's formal-conjectures fork, revision
a522a5352dd28df0b5ef08c213c368b5f6a5df6e:
https://github.com/rwst/formal-conjectures/blob/a522a5352dd28df0b5ef08c213c368b5f6a5df6e/FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean
The namespace, imports and attributes have been adapted and the separate
rich-number results omitted. WallScale proves the integer-multiplication step.
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

open Filter Topology WallBridge

namespace WallScale

/-- Removing the right endpoint does not change the limiting frequency of an interval. -/
theorem tendsto_Ico {s : ℕ → ℝ} (hs : IsEquidistributedModuloOne s) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    Tendsto (visitFreq s (Set.Ico c d)) atTop (𝓝 (d - c)) := by
  have hclosed : Tendsto (visitFreq s (Set.Icc c d)) atTop _ :=
    hs c d hcd (Set.Icc_subset_Icc hc hd)
  have hend : Tendsto (visitFreq s (Set.Icc d d)) atTop _ :=
    hs d d le_rfl (Set.Icc_subset_Icc (hc.trans hcd) hd)
  have hsplit (n : ℕ) : visitFreq s (Set.Ico c d) n =
      visitFreq s (Set.Icc c d) n - visitFreq s (Set.Icc d d) n := by
    rw [eq_sub_iff_add_eq, ← visitFreq_union (Set.disjoint_left.2 fun y hy hy' =>
      lt_irrefl y (hy.2.trans_le hy'.1))]
    exact congrFun (visitFreq_congr (Set.Ico_union_Icc_eq_Icc hcd le_rfl)) n
  simpa using (hclosed.sub hend).congr (fun n => (hsplit n).symm)

end WallScale

namespace WallScale

/-- A half-open interval pulls back to one interval in each of the multiplier's cells. -/
theorem fract_nat_mul_mem_Ico_nat {m : ℕ} (hm : 0 < m) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (x : ℝ) :
    Int.fract ((m : ℝ) * x) ∈ Set.Ico a b ↔
      ∃ j < m, Int.fract x ∈ Set.Ico (((j : ℝ) + a) / m) (((j : ℝ) + b) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let t := (m : ℝ) * Int.fract x
  have ht : 0 ≤ t := mul_nonneg hmR.le (Int.fract_nonneg x)
  have htm : t < m := mul_lt_of_lt_one_right hmR (Int.fract_lt_one x)
  have hsplit : (m : ℝ) * x = t + (((m : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    push_cast
    dsimp [t]
    rw [← mul_add, Int.fract_add_floor]
  have hfrac : Int.fract ((m : ℝ) * x) = t - (⌊t⌋₊ : ℝ) := by
    rw [hsplit, Int.fract_add_intCast, Int.fract, ← Int.natCast_floor_eq_floor ht]
    simp
  rw [hfrac, Set.mem_Ico]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨⌊t⌋₊, (Nat.floor_lt ht).mpr htm, ?_⟩
    rw [Set.mem_Ico, div_le_iff₀ hmR, lt_div_iff₀ hmR, mul_comm (Int.fract x)]
    change ↑⌊t⌋₊ + a ≤ t ∧ t < ↑⌊t⌋₊ + b
    constructor <;> linarith
  · rintro ⟨j, _, hj⟩
    rw [Set.mem_Ico, div_le_iff₀ hmR, lt_div_iff₀ hmR, mul_comm (Int.fract x)] at hj
    change (j : ℝ) + a ≤ t ∧ t < j + b at hj
    have hjfloor : ⌊t⌋₊ = j := (Nat.floor_eq_iff ht).mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩
    rw [hjfloor]
    constructor <;> linarith [hj.1, hj.2]


theorem fiber_disjoint {m i j : ℕ} (hm : 0 < m) (hij : i ≠ j) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    Disjoint (Set.Ico (((i : ℝ) + a) / m) (((i : ℝ) + b) / m))
      (Set.Ico (((j : ℝ) + a) / m) (((j : ℝ) + b) / m)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Set.disjoint_left]
  intro x hi hj
  rw [Set.mem_Ico, div_le_iff₀ hmR, lt_div_iff₀ hmR] at hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hgap : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hi.2, hj.1]
  · have hgap : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hj.2, hi.1]

end WallScale

/- Positive integer scaling decomposes the inverse image of each interval into equal pieces. -/

open WallBridge Filter Topology

namespace WallScale

-- Frequencies add over a disjoint finite family of intervals.
private theorem tendsto_union_freq {s : ℕ → ℝ} (m : ℕ)
    (I : ℕ → Set ℝ) (L : ℝ)
    (hdis : ∀ {j k}, j ≠ k → Disjoint (I j) (I k))
    [∀ j, DecidablePred (· ∈ I j)]
    (hlim : ∀ j < m, Tendsto (visitFreq s (I j)) atTop (𝓝 L)) :
    ∀ T : Finset ℕ, T ⊆ Finset.range m →
      Tendsto (fun n => @visitFreq s {x | ∃ j ∈ T, x ∈ I j} (Classical.decPred _) n)
        atTop (𝓝 ((T.card : ℝ) * L)) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simp [visitFreq]
  | @insert j T hj ih =>
    intro hT
    let U : Set ℝ := {x | ∃ k ∈ T, x ∈ I k}
    have hT' : T ⊆ Finset.range m := fun k hk => hT (Finset.mem_insert_of_mem hk)
    have hjm : j < m := Finset.mem_range.mp (hT (Finset.mem_insert_self _ _))
    have hsep : Disjoint (I j) U := by
      refine Set.disjoint_left.mpr ?_
      rintro y hy ⟨k, hk, hyk⟩
      have hjk : j ≠ k := fun e => hj (e.symm ▸ hk)
      exact Set.disjoint_left.mp (hdis hjk) hy hyk
    have eqU : {x | ∃ k ∈ insert j T, x ∈ I k} = I j ∪ U := by
      ext x
      simp [U]
    have h := ((hlim j hjm).add (ih hT')).congr (f₂ := fun n =>
      @visitFreq s {x | ∃ k ∈ insert j T, x ∈ I k} (Classical.decPred _) n) fun n => by
        let : DecidablePred (· ∈ U) := Classical.decPred _
        let : DecidablePred (· ∈ {x | ∃ k ∈ insert j T, x ∈ I k}) := Classical.decPred _
        calc _ = visitFreq s (I j ∪ U) n := (visitFreq_union hsep n).symm
             _ = _ := congrFun (visitFreq_congr (s := s) eqU.symm) n
    simpa [Finset.card_insert_of_notMem hj, add_mul, add_comm] using h

theorem natScale {s : ℕ → ℝ} (hs : IsEquidistributedModuloOne s)
    (m : ℕ) (hm : 0 < m) :
    IsEquidistributedModuloOne (fun n => (m : ℝ) * s n) := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply (tendsto_Ico_iff_isEquidistributedModuloOne (b := 2) (by decide) _).mp
  intro k i hi
  let a : ℝ := (i : ℝ) / (2 : ℝ)^k
  let b : ℝ := ((i : ℝ) + 1) / (2 : ℝ)^k
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ b := div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hb : b ≤ 1 := add_one_div_pow_le_one hi
  let I := fun j : ℕ => Set.Ico (((j : ℝ) + a) / m) (((j : ℝ) + b) / m)
  have hlim (j : ℕ) (hj : j < m) :
      Tendsto (visitFreq s (I j)) atTop (𝓝 ((b - a) / m)) := by
    have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have h := tendsto_Ico hs (c := ((j : ℝ) + a) / m) (d := ((j : ℝ) + b) / m)
      (div_nonneg (add_nonneg (Nat.cast_nonneg _) ha) hm'.le)
      (div_le_div_of_nonneg_right (by linarith) hm'.le)
      ((div_le_one hm').mpr (by linarith))
    convert h using 2
    ring
  have h := tendsto_union_freq m I ((b - a) / m)
    (fun hij => fiber_disjoint hm hij ha hb) hlim (Finset.range m) (fun _ h => h)
  have heq (n : ℕ) :
      @visitFreq s {x | ∃ j ∈ Finset.range m, x ∈ I j} (Classical.decPred _) n =
        visitFreq (fun t => (m : ℝ) * s t) (Set.Ico a b) n := by
    unfold visitFreq
    congr 2
    apply congrArg Finset.card
    ext t
    simp only [Finset.mem_filter, Set.mem_ofPred_eq, Finset.mem_range]
    exact and_congr_right fun _ => (fract_nat_mul_mem_Ico_nat hm ha hb (s t)).symm
  have h' := h.congr heq
  have H : ((Finset.range m).card : ℝ) * ((b - a) / (m : ℝ)) = 1 / (2 : ℝ)^k := by
    simp only [Finset.card_range]
    dsimp [a,b]
    field_simp
    ring
  rw [H] at h'
  exact h'

end WallScale

/- Reflection of a uniformly distributed sequence. -/

open WallBridge Filter Topology

namespace WallScale

/-- Count a set of visits by covering the indices with two other sets of visits. -/
private theorem visitFreq_cover {s t u : ℕ → ℝ} {S T U : Set ℝ}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (h : ∀ i, Int.fract (s i) ∈ S → Int.fract (t i) ∈ T ∨ Int.fract (u i) ∈ U) (n : ℕ) :
    visitFreq s S n ≤ visitFreq t T n + visitFreq u U n := by
  classical
  simp only [visitFreq, ← add_div, ← Nat.cast_add]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Nat.cast_le.mpr
  refine (Finset.card_le_card (t := ((Finset.range n).filter fun i => Int.fract (t i) ∈ T) ∪
    ((Finset.range n).filter fun i => Int.fract (u i) ∈ U)) ?_).trans (Finset.card_union_le _ _)
  intro i hi
  obtain ⟨hi, hs⟩ := Finset.mem_filter.mp hi
  rcases h i hs with ht | hu
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, ht⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hu⟩)

/-- Reflection preserves uniform distribution. Only integer samples see the cut at zero. -/
theorem negSeq {s : ℕ → ℝ} (hs : IsEquidistributedModuloOne s) :
    IsEquidistributedModuloOne (fun n => -s n) := by
  intro c d hcd hsub
  have hc : 0 ≤ c := (hsub ⟨le_rfl, hcd⟩).1
  have hd : d ≤ 1 := (hsub ⟨hcd, le_rfl⟩).2
  let reflected := Set.Icc (1 - d) (1 - c)
  let zeroPoint := Set.Icc (0 : ℝ) 0
  have hr : Tendsto (visitFreq s reflected) atTop (𝓝 (d - c)) := by
    have hr' := hs (1 - d) (1 - c) (by linarith)
      (Set.Icc_subset_Icc (by linarith) (by linarith))
    change Tendsto (visitFreq s reflected) atTop (𝓝 ((1 - c - (1 - d)) / (1 - 0))) at hr'
    rwa [show (1 - c - (1 - d)) / (1 - 0) = d - c by ring] at hr'
  have hz : Tendsto (visitFreq s zeroPoint) atTop (𝓝 0) := by
    have hz' := hs 0 0 le_rfl (Set.Icc_subset_Icc (by norm_num) (by norm_num))
    change Tendsto (visitFreq s zeroPoint) atTop (𝓝 ((0 - 0) / (1 - 0))) at hz'
    simpa only [sub_zero, zero_div] using hz'
  have hreflect (i : ℕ) (hi : Int.fract (s i) ≠ 0) :
      Int.fract (-s i) ∈ Set.Icc c d ↔ Int.fract (s i) ∈ reflected := by
    rw [Int.fract_neg hi]
    change (c ≤ 1 - _ ∧ 1 - _ ≤ d) ↔ 1 - d ≤ _ ∧ _ ≤ 1 - c
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  change Tendsto (visitFreq (fun n => -s n) (Set.Icc c d)) atTop (𝓝 ((d - c) / (1 - 0)))
  rw [sub_zero, div_one]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => visitFreq s reflected n - visitFreq s zeroPoint n)
    (h := fun n => visitFreq s reflected n + visitFreq s zeroPoint n)
    (by simpa using hr.sub hz) (by simpa using hr.add hz)
  · intro n
    apply sub_le_iff_le_add.mpr
    apply visitFreq_cover
    intro i hi
    by_cases hz' : Int.fract (s i) = 0
    · exact Or.inr (by simp [zeroPoint, hz'])
    · exact Or.inl ((hreflect i hz').mpr hi)
  · intro n
    apply visitFreq_cover
    intro i hi
    by_cases hz' : Int.fract (s i) = 0
    · exact Or.inr (by simp [zeroPoint, hz'])
    · exact Or.inl ((hreflect i hz').mp hi)

end WallScale

theorem OMA.solution : OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1.H2 := by
  intro b hb x m hm hx
  have hud := (WallBridge.isNormalInBase_iff_isEquidistributedModuloOne b hb x).mp hx
  apply (WallBridge.isNormalInBase_iff_isEquidistributedModuloOne b hb _).mpr
  cases m with
  | ofNat k =>
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hm rfl)
    have h := WallScale.natScale hud k hk
    convert h using 1
    funext n
    change (b : ℝ) ^ n * (↑(↑k : ℤ) * x) = (k : ℝ) * ((b : ℝ) ^ n * x)
    push_cast
    ring
  | negSucc k =>
    have h := WallScale.negSeq (WallScale.natScale hud (k + 1) (Nat.succ_pos _))
    convert h using 1
    funext n
    push_cast
    ring
