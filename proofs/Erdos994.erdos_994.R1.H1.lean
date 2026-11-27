import OMAReductions.R_Erdos994_erdos_994_R1

/-!
# Erdős Problem 994 — Step H1 (Marstrand finite maximal estimate)

Proves `OMA.R_Erdos994_erdos_994_R1.H1` by combining the Avila–Candela multi-parameter
Rokhlin tower construction for commuting integer dilations modulo `1` with the
Quas–Wierdl logarithmic bin pigeonhole argument over dyadic windows.
-/

open MeasureTheory Set Erdos994
open scoped ENNReal

namespace Erdos994H1

noncomputable def dil (a : ℕ) (x : ℝ) : ℝ := Int.fract ((a : ℝ) * x)

def pre (a : ℕ) (S : Set ℝ) : Set ℝ := dil a ⁻¹' S ∩ Ico (0 : ℝ) 1

noncomputable def mu (S : Set ℝ) : ℝ := (volume S).toReal

lemma dil_mem_Ico (a : ℕ) (x : ℝ) : dil a x ∈ Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma dil_mul (a b : ℕ) (x : ℝ) : dil a (dil b x) = dil (a * b) x := by
  unfold dil
  have h : (a : ℝ) * Int.fract ((b : ℝ) * x) =
      ((a * b : ℕ) : ℝ) * x - (((a : ℤ) * ⌊(b : ℝ) * x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.fract_sub_intCast]

lemma dil_one_eq {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : dil 1 x = x := by
  unfold dil
  rw [Nat.cast_one, one_mul]
  exact Int.fract_eq_self.mpr hx

lemma pre_sub (a : ℕ) (S : Set ℝ) : pre a S ⊆ Ico (0 : ℝ) 1 :=
  inter_subset_right

lemma pre_one {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) : pre 1 S = S := by
  ext x
  simp only [pre, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    rwa [dil_one_eq h2] at h1
  · intro hx
    exact ⟨by rwa [dil_one_eq (hS hx)], hS hx⟩

lemma pre_comp (a b : ℕ) (S : Set ℝ) : pre b (pre a S) = pre (a * b) S := by
  ext x
  simp only [pre, mem_inter_iff, mem_preimage, dil_mul]
  exact ⟨fun ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩, fun ⟨h, hx⟩ => ⟨⟨h, dil_mem_Ico b x⟩, hx⟩⟩

lemma pre_inter (a : ℕ) (S T : Set ℝ) : pre a (S ∩ T) = pre a S ∩ pre a T := by
  ext x
  simp only [pre, mem_inter_iff, mem_preimage]
  tauto

lemma pre_diff (a : ℕ) (S T : Set ℝ) : pre a (S \ T) = pre a S \ pre a T := by
  ext x
  simp only [pre, mem_inter_iff, Set.mem_sdiff, mem_preimage]
  tauto

lemma pre_empty (a : ℕ) : pre a ∅ = ∅ := by
  ext x
  simp [pre]

lemma pre_mono (a : ℕ) {S T : Set ℝ} (h : S ⊆ T) : pre a S ⊆ pre a T :=
  fun _ hx => ⟨h hx.1, hx.2⟩

lemma pre_disjoint (a : ℕ) {S T : Set ℝ} (h : Disjoint S T) : Disjoint (pre a S) (pre a T) := by
  rw [Set.disjoint_iff_inter_eq_empty] at h ⊢
  rw [← pre_inter, h, pre_empty]

lemma pre_biUnion {ι : Type*} (a : ℕ) (s : Finset ι) (F : ι → Set ℝ) :
    pre a (⋃ i ∈ s, F i) = ⋃ i ∈ s, pre a (F i) := by
  ext x
  simp only [pre, mem_inter_iff, mem_preimage, mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi, hxi⟩, hx⟩
    exact ⟨i, hi, hxi, hx⟩
  · rintro ⟨i, hi, hxi, hx⟩
    exact ⟨⟨i, hi, hxi⟩, hx⟩

lemma disjoint_biUnion_left {ι : Type*} {s : Finset ι} {F : ι → Set ℝ} {T : Set ℝ}
    (h : ∀ i ∈ s, Disjoint (F i) T) : Disjoint (⋃ i ∈ s, F i) T := by
  rw [Set.disjoint_left]
  intro x hx hT
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  exact Set.disjoint_left.mp (h i hi) hxi hT

lemma disjoint_biUnion_right {ι : Type*} {s : Finset ι} {T : Set ℝ} {F : ι → Set ℝ}
    (h : ∀ i ∈ s, Disjoint T (F i)) : Disjoint T (⋃ i ∈ s, F i) :=
  (disjoint_biUnion_left fun i hi => (h i hi).symm).symm

lemma pre_eq_biUnion {a : ℕ} (ha : 0 < a) {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) :
    pre a S = ⋃ k ∈ Finset.range a, ((a : ℝ) * ·) ⁻¹' ((· - (k : ℝ)) ⁻¹' S) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  ext x
  simp only [pre, dil, mem_inter_iff, mem_preimage, mem_Ico, mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨hxS, hx0, hx1⟩
    have hmul0 : 0 ≤ (a : ℝ) * x := mul_nonneg haR.le hx0
    have hmul1 : (a : ℝ) * x < a := by nlinarith
    have hfl0 : 0 ≤ ⌊(a : ℝ) * x⌋ := Int.floor_nonneg.mpr hmul0
    have hfl1 : ⌊(a : ℝ) * x⌋ < (a : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hmul1)
    have htoNat : (⌊(a : ℝ) * x⌋.toNat : ℤ) = ⌊(a : ℝ) * x⌋ := Int.toNat_of_nonneg hfl0
    refine ⟨⌊(a : ℝ) * x⌋.toNat, by omega, ?_⟩
    have hk : ((⌊(a : ℝ) * x⌋.toNat : ℕ) : ℝ) = (⌊(a : ℝ) * x⌋ : ℝ) := by exact_mod_cast htoNat
    rw [hk]
    exact hxS
  · rintro ⟨k, hka, hxk⟩
    obtain ⟨hy0, hy1⟩ := hS hxk
    have hkR : (k : ℝ) + 1 ≤ a := by exact_mod_cast hka
    have hx0 : 0 ≤ x := by
      have : (0 : ℝ) ≤ (a : ℝ) * x := by linarith
      exact nonneg_of_mul_nonneg_right this haR
    have hx1 : x < 1 := by
      have : (a : ℝ) * x < (a : ℝ) * 1 := by linarith
      exact (mul_lt_mul_iff_right₀ haR).mp this
    refine ⟨?_, hx0, hx1⟩
    have hfr : (a : ℝ) * x = ((a : ℝ) * x - (k : ℝ)) + (k : ℕ) := by ring
    rw [hfr, Int.fract_add_natCast, Int.fract_eq_self.mpr ⟨hy0, hy1⟩]
    exact hxk

lemma pre_measurable {a : ℕ} (ha : 0 < a) {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1)
    (hm : MeasurableSet S) : MeasurableSet (pre a S) := by
  rw [pre_eq_biUnion ha hS]
  refine Finset.measurableSet_biUnion _ fun k _ => ?_
  exact ((measurable_id.sub measurable_const).comp (measurable_const.mul measurable_id)) hm

lemma pre_volume {a : ℕ} (ha : 0 < a) {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1)
    (hm : MeasurableSet S) : volume (pre a S) = volume S := by
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hapos : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  rw [pre_eq_biUnion ha hS, measure_biUnion_finset]
  · have hpiece : ∀ k ∈ Finset.range a,
        volume (((a : ℝ) * ·) ⁻¹' ((· - (k : ℝ)) ⁻¹' S)) =
          ENNReal.ofReal (a : ℝ)⁻¹ * volume S := by
      intro k _
      rw [Real.volume_preimage_mul_left haR]
      have hsub : ((· - (k : ℝ)) ⁻¹' S) = ((· + (-(k : ℝ))) ⁻¹' S) := by
        ext y; simp [sub_eq_add_neg]
      rw [hsub, measure_preimage_add_right, abs_of_pos (inv_pos.mpr hapos)]
    rw [Finset.sum_congr rfl hpiece, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← mul_assoc]
    have h1 : (a : ℝ≥0∞) * ENNReal.ofReal (a : ℝ)⁻¹ = 1 := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hapos.le, mul_inv_cancel₀ haR,
        ENNReal.ofReal_one]
    rw [h1, one_mul]
  · intro k₁ _ k₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨h10, h11⟩ := hS hx1
    obtain ⟨h20, h21⟩ := hS hx2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast hlt
      linarith
    · have : (k₂ : ℝ) + 1 ≤ k₁ := by exact_mod_cast hgt
      linarith
  · intro k _
    exact ((measurable_id.sub measurable_const).comp (measurable_const.mul measurable_id)) hm

lemma volume_le_one_of_sub {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) : volume S ≤ 1 := by
  calc volume S ≤ volume (Ico (0 : ℝ) 1) := measure_mono hS
    _ = 1 := by simp [Real.volume_Ico]

lemma volume_ne_top_of_sub {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (volume_le_one_of_sub hS)

lemma mu_nonneg (S : Set ℝ) : 0 ≤ mu S := ENNReal.toReal_nonneg

lemma mu_le_one {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) : mu S ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using volume_le_one_of_sub hS)

lemma mu_mono {S T : Set ℝ} (hT : T ⊆ Ico (0 : ℝ) 1) (h : S ⊆ T) : mu S ≤ mu T :=
  ENNReal.toReal_mono (volume_ne_top_of_sub hT) (measure_mono h)

lemma mu_union {S T : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) (hT : T ⊆ Ico (0 : ℝ) 1)
    (hmT : MeasurableSet T) (hd : Disjoint S T) : mu (S ∪ T) = mu S + mu T := by
  unfold mu
  rw [measure_union hd hmT, ENNReal.toReal_add (volume_ne_top_of_sub hS) (volume_ne_top_of_sub hT)]

lemma mu_biUnion {ι : Type*} (s : Finset ι) (F : ι → Set ℝ)
    (hsub : ∀ i ∈ s, F i ⊆ Ico (0 : ℝ) 1) (hm : ∀ i ∈ s, MeasurableSet (F i))
    (hd : (s : Set ι).PairwiseDisjoint F) :
    mu (⋃ i ∈ s, F i) = ∑ i ∈ s, mu (F i) := by
  unfold mu
  rw [measure_biUnion_finset hd hm,
    ENNReal.toReal_sum fun i hi => volume_ne_top_of_sub (hsub i hi)]

lemma mu_biUnion_le {ι : Type*} (s : Finset ι) (F : ι → Set ℝ)
    (hsub : ∀ i ∈ s, F i ⊆ Ico (0 : ℝ) 1) :
    mu (⋃ i ∈ s, F i) ≤ ∑ i ∈ s, mu (F i) := by
  unfold mu
  have hfin : ∀ i ∈ s, volume (F i) ≠ ⊤ := fun i hi => volume_ne_top_of_sub (hsub i hi)
  rw [← ENNReal.toReal_sum hfin]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin) (measure_biUnion_finset_le s F)

lemma mu_diff {S T : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) (hmT : MeasurableSet T) (hTS : T ⊆ S) :
    mu (S \ T) = mu S - mu T := by
  unfold mu
  rw [measure_sdiff hTS hmT.nullMeasurableSet (volume_ne_top_of_sub (hTS.trans hS)),
    ENNReal.toReal_sub_of_le (measure_mono hTS) (volume_ne_top_of_sub hS)]

lemma mu_pre {a : ℕ} (ha : 0 < a) {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) (hm : MeasurableSet S) :
    mu (pre a S) = mu S := by
  unfold mu
  rw [pre_volume ha hS hm]

lemma mu_Ico_zero_one : mu (Ico (0 : ℝ) 1) = 1 := by
  unfold mu
  simp [Real.volume_Ico]

def flipAt {N : ℕ} (i : Fin N) (f : Fin N → Bool) : Fin N → Bool :=
  Function.update f i (!f i)

lemma flipAt_involutive {N : ℕ} (i : Fin N) : Function.Involutive (flipAt i) := by
  intro f
  ext k
  unfold flipAt
  by_cases hk : k = i <;> simp [hk]

lemma sum_bool_single {N : ℕ} (i : Fin N) (c : ℝ) :
    2 * ∑ f : Fin N → Bool, (if f i = true then c else 0) = (2 : ℝ) ^ N * c := by
  have hbij : ∑ f : Fin N → Bool, (if f i = false then c else 0) =
      ∑ f : Fin N → Bool, (if f i = true then c else 0) := by
    rw [← (flipAt_involutive i).bijective.sum_comp (fun f => if f i = true then c else 0)]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp [flipAt]
  have htot : ∑ f : Fin N → Bool, (if f i = true then c else 0) +
      ∑ f : Fin N → Bool, (if f i = false then c else 0) = (2 : ℝ) ^ N * c := by
    rw [← Finset.sum_add_distrib]
    have hcongr : ∀ f : Fin N → Bool,
        (if f i = true then c else 0) + (if f i = false then c else 0) = c := by
      intro f; cases f i <;> simp
    simp [hcongr]
  linarith

lemma sum_bool_pair {N : ℕ} {i j : Fin N} (hij : i ≠ j) (c : ℝ) :
    4 * ∑ f : Fin N → Bool, (if f i = true ∧ f j = true then c else 0) = (2 : ℝ) ^ N * c := by
  let S (b1 b2 : Bool) : ℝ := ∑ f : Fin N → Bool, (if f i = b1 ∧ f j = b2 then c else 0)
  have htf : S true false = S true true := by
    dsimp [S]
    rw [← (flipAt_involutive j).bijective.sum_comp (fun f => if f i = true ∧ f j = true then c else 0)]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp [flipAt, hij]
  have hft : S false true = S true true := by
    dsimp [S]
    rw [← (flipAt_involutive i).bijective.sum_comp (fun f => if f i = true ∧ f j = true then c else 0)]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp [flipAt, hij.symm]
  have hff : S false false = S true false := by
    dsimp [S]
    rw [← (flipAt_involutive i).bijective.sum_comp (fun f => if f i = true ∧ f j = false then c else 0)]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp [flipAt, hij.symm]
  have htot : S true true + S true false + S false true + S false false = (2 : ℝ) ^ N * c := by
    dsimp [S]
    simp only [← Finset.sum_add_distrib]
    have hcongr : ∀ f : Fin N → Bool,
        (((if f i = true ∧ f j = true then c else 0) +
          (if f i = true ∧ f j = false then c else 0)) +
          (if f i = false ∧ f j = true then c else 0)) +
          (if f i = false ∧ f j = false then c else 0) = c := by
      intro f; cases f i <;> cases f j <;> simp
    simp [hcongr]
  change 4 * S true true = (2 : ℝ) ^ N * c
  linarith

def cell (N : ℕ) (i : Fin N) : Set ℝ :=
  Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N)

lemma cell_sub {N : ℕ} (i : Fin N) : cell N i ⊆ Ico (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.zero_le (i : ℕ) |>.trans_lt i.isLt)
  intro x hx
  refine ⟨le_trans (div_nonneg (Nat.cast_nonneg _) hN.le) hx.1, lt_of_lt_of_le hx.2 ?_⟩
  rw [div_le_one hN]
  exact_mod_cast i.isLt

lemma cell_disjoint {N : ℕ} :
    (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint (cell N) := by
  intro i _ j _ hij
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.zero_le (i : ℕ) |>.trans_lt i.isLt)
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
  · have hle : ((i : ℕ) + 1 : ℝ) / N ≤ (j : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact_mod_cast hlt
    exact not_lt.mpr (hle.trans hxj.1) hxi.2
  · have hle : ((j : ℕ) + 1 : ℝ) / N ≤ (i : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact_mod_cast hgt
    exact not_lt.mpr (hle.trans hxi.1) hxj.2

lemma iUnion_cell {N : ℕ} (hN : 0 < N) :
    (⋃ i ∈ (Finset.univ : Finset (Fin N)), cell N i) = Ico (0 : ℝ) 1 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  ext x
  simp only [mem_iUnion, Finset.mem_univ, exists_prop, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact cell_sub i hi
  · rintro ⟨hx0, hx1⟩
    have hmul0 : 0 ≤ (N : ℝ) * x := mul_nonneg hNR.le hx0
    have hmul1 : (N : ℝ) * x < N := by nlinarith
    have hfl0 : 0 ≤ ⌊(N : ℝ) * x⌋ := Int.floor_nonneg.mpr hmul0
    have hfl1 : ⌊(N : ℝ) * x⌋ < (N : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hmul1)
    have htoNat : (⌊(N : ℝ) * x⌋.toNat : ℤ) = ⌊(N : ℝ) * x⌋ := Int.toNat_of_nonneg hfl0
    have hlt : ⌊(N : ℝ) * x⌋.toNat < N := by omega
    refine ⟨⟨⌊(N : ℝ) * x⌋.toNat, hlt⟩, ?_⟩
    have hk : ((⌊(N : ℝ) * x⌋.toNat : ℕ) : ℝ) = (⌊(N : ℝ) * x⌋ : ℝ) := by exact_mod_cast htoNat
    simp only [cell, mem_Ico, hk]
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀' hNR]
      exact Int.floor_le _
    · rw [lt_div_iff₀' hNR]
      exact Int.lt_floor_add_one _

lemma diag_overlap_bound {a b N : ℕ} (ha : 0 < a) (hab : a < b) (hN : 0 < N) :
    mu (⋃ i ∈ (Finset.univ : Finset (Fin N)), pre a (cell N i) ∩ pre b (cell N i)) ≤
      (a + b + 1 : ℝ) * (2 / N) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hd_pos : 0 < b - a := Nat.sub_pos_of_lt hab
  have hdR : (1 : ℝ) ≤ (b - a : ℕ) := by exact_mod_cast hd_pos
  have hd0 : (0 : ℝ) < (b - a : ℕ) := lt_of_lt_of_le zero_lt_one hdR
  let d : ℝ := (b - a : ℕ)
  let Iv (m : ℤ) : Set ℝ := Ioo (((m : ℝ) - (N : ℝ)⁻¹) / d) (((m : ℝ) + (N : ℝ)⁻¹) / d)
  have hsub : (⋃ i ∈ (Finset.univ : Finset (Fin N)), pre a (cell N i) ∩ pre b (cell N i)) ⊆
      ⋃ m ∈ Finset.Icc (-(a : ℤ)) (b : ℤ), Iv m := by
    intro x hx
    simp only [mem_iUnion, Finset.mem_univ, exists_prop, true_and, mem_inter_iff] at hx
    obtain ⟨i, ⟨ha_cell, hx0, hx1⟩, ⟨hb_cell, _, _⟩⟩ := hx
    obtain ⟨ha1, ha2⟩ := ha_cell
    obtain ⟨hb1, hb2⟩ := hb_cell
    have hfl_a0 : 0 ≤ ⌊(a : ℝ) * x⌋ := Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hx0)
    have hfl_a1 : ⌊(a : ℝ) * x⌋ < (a : ℤ) := by
      rw [Int.floor_lt, Int.cast_natCast]
      have : (a : ℝ) * x < (a : ℝ) * 1 := mul_lt_mul_of_pos_left hx1 (Nat.cast_pos.mpr ha)
      linarith
    have hfl_b0 : 0 ≤ ⌊(b : ℝ) * x⌋ := Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hx0)
    have hfl_b1 : ⌊(b : ℝ) * x⌋ < (b : ℤ) := by
      rw [Int.floor_lt, Int.cast_natCast]
      have : (b : ℝ) * x < (b : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hx1 (Nat.cast_pos.mpr (ha.trans hab))
      linarith
    let m : ℤ := ⌊(b : ℝ) * x⌋ - ⌊(a : ℝ) * x⌋
    simp only [mem_iUnion, Finset.mem_Icc]
    refine ⟨m, ⟨by omega, by omega⟩, ?_⟩
    have hdiff : d * x - (m : ℝ) = dil b x - dil a x := by
      dsimp [d, m, dil]
      rw [Nat.cast_sub hab.le, Int.fract, Int.fract]
      push_cast
      ring
    have hlen : (((i : ℝ) + 1) / N) - ((i : ℝ) / N) = (N : ℝ)⁻¹ := by ring
    refine ⟨?_, ?_⟩
    · rw [div_lt_iff₀ hd0]
      linarith
    · rw [lt_div_iff₀ hd0]
      linarith
  have hvol : volume (⋃ i ∈ (Finset.univ : Finset (Fin N)), pre a (cell N i) ∩ pre b (cell N i)) ≤
      ENNReal.ofReal ((a + b + 1 : ℝ) * (2 / N)) := by
    calc volume (⋃ i ∈ (Finset.univ : Finset (Fin N)), pre a (cell N i) ∩ pre b (cell N i))
      _ ≤ volume (⋃ m ∈ Finset.Icc (-(a : ℤ)) (b : ℤ), Iv m) := measure_mono hsub
      _ ≤ ∑ m ∈ Finset.Icc (-(a : ℤ)) (b : ℤ), volume (Iv m) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc (-(a : ℤ)) (b : ℤ), ENNReal.ofReal (2 / N) := by
          refine Finset.sum_le_sum fun m _ => ?_
          dsimp [Iv]
          rw [Real.volume_Ioo]
          apply ENNReal.ofReal_le_ofReal
          have hnum : (((m : ℝ) + (N : ℝ)⁻¹) / d) - (((m : ℝ) - (N : ℝ)⁻¹) / d) = (2 / N) / d := by
            ring
          rw [hnum]
          exact div_le_self (by positivity) hdR
      _ = ENNReal.ofReal ((a + b + 1 : ℝ) * (2 / N)) := by
          rw [Finset.sum_const, Int.card_Icc]
          have hcard : ((b : ℤ) + 1 - -(a : ℤ)).toNat = a + b + 1 := by omega
          rw [hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          push_cast
          rfl
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hvol

lemma two_tower_step {a b : ℕ} (ha : 0 < a) (hab : a < b) {Y : Set ℝ}
    (hY : Y ⊆ Ico (0 : ℝ) 1) (hmY : MeasurableSet Y) :
    ∃ B : Set ℝ, B ⊆ pre a Y ∧ MeasurableSet B ∧ Disjoint (pre a B) (pre b B) ∧
      mu Y ≤ 5 * mu B := by
  have hb : 0 < b := ha.trans hab
  by_cases hY0 : mu Y ≤ 0
  · refine ⟨∅, empty_subset _, MeasurableSet.empty, by simp [pre_empty], ?_⟩
    exact hY0.trans (by simp [mu])
  · have hYpos : 0 < mu Y := not_le.mp hY0
    obtain ⟨N, hN_gt⟩ := exists_nat_gt ((10 * (a + b + 1 : ℝ)) / mu Y)
    have hN : 0 < N := by
      have hpos : 0 < (10 * (a + b + 1 : ℝ)) / mu Y := by positivity
      exact Nat.cast_pos.mp (hpos.trans hN_gt)
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hsmall : (a + b + 1 : ℝ) * (2 / N) ≤ (1 / 5 : ℝ) * mu Y := by
      rw [mul_div_assoc', div_le_iff₀ hNR]
      have := (div_lt_iff₀ hYpos).mp hN_gt
      linarith
    let Q (i : Fin N) : Set ℝ := Y ∩ cell N i
    have hQsub : ∀ i, Q i ⊆ Ico (0 : ℝ) 1 := fun i => inter_subset_right.trans (cell_sub i)
    have hQmeas : ∀ i, MeasurableSet (Q i) := fun i => hmY.inter measurableSet_Ico
    have hQdisj : ∀ {i j : Fin N}, i ≠ j → Disjoint (Q i) (Q j) := fun hij =>
      (cell_disjoint (Finset.mem_univ _) (Finset.mem_univ _) hij).mono
        inter_subset_right inter_subset_right
    have hQu : (⋃ i ∈ (Finset.univ : Finset (Fin N)), Q i) = Y := by
      simp only [Q, ← inter_iUnion₂, iUnion_cell hN, inter_eq_self_of_subset_left hY]
    have hmuQ : ∑ i : Fin N, mu (Q i) = mu Y := by
      have hbu := mu_biUnion Finset.univ Q (fun i _ => hQsub i) (fun i _ => hQmeas i)
        (fun i _ j _ hij => hQdisj hij)
      rw [← hbu, hQu]
    let D (f : Fin N → Bool) : Set ℝ := ⋃ i ∈ Finset.univ.filter (fun i => f i = true), Q i
    let Bf (f : Fin N → Bool) : Set ℝ := pre a (D f) \ pre b (D f)
    have hDsub : ∀ f, D f ⊆ Y := fun f => iUnion₂_subset fun i _ => inter_subset_left
    have hDmeas : ∀ f, MeasurableSet (D f) := fun f =>
      Finset.measurableSet_biUnion _ fun i _ => hQmeas i
    have hBf_meas : ∀ f, MeasurableSet (Bf f) := fun f =>
      (pre_measurable ha ((hDsub f).trans hY) (hDmeas f)).diff
        (pre_measurable hb ((hDsub f).trans hY) (hDmeas f))
    have hBf_disj : ∀ f, Disjoint (pre a (Bf f)) (pre b (Bf f)) := by
      intro f
      rw [Set.disjoint_left]
      intro x hxa hxb
      simp only [Bf, pre_diff, pre_comp, Set.mem_sdiff] at hxa hxb
      rw [Nat.mul_comm b a] at hxa
      exact hxa.2 hxb.1
    let W (i j : Fin N) : Set ℝ := pre a (Q i) ∩ pre b (Q j)
    have hWmeas : ∀ i j, MeasurableSet (W i j) := fun i j =>
      (pre_measurable ha (hQsub i) (hQmeas i)).inter (pre_measurable hb (hQsub j) (hQmeas j))
    have hmu_prea : ∀ f, mu (pre a (D f)) =
        ∑ i : Fin N, (if f i = true then mu (Q i) else 0) := by
      intro f
      rw [mu_pre ha ((hDsub f).trans hY) (hDmeas f),
        mu_biUnion _ Q (fun i _ => hQsub i) (fun i _ => hQmeas i)
          (fun i _ j _ hij => hQdisj hij),
        Finset.sum_filter]
    have hmu_inter : ∀ f, mu (pre a (D f) ∩ pre b (D f)) =
        ∑ p : Fin N × Fin N, (if f p.1 = true ∧ f p.2 = true then mu (W p.1 p.2) else 0) := by
      intro f
      let sf := Finset.univ.filter (fun i : Fin N => f i = true)
      have heq : pre a (D f) ∩ pre b (D f) = ⋃ p ∈ sf ×ˢ sf, W p.1 p.2 := by
        ext x
        simp only [D, W, pre_biUnion, mem_inter_iff, mem_iUnion, Finset.mem_product, Prod.exists]
        constructor
        · rintro ⟨⟨i, hi, hxi⟩, ⟨j, hj, hxj⟩⟩
          exact ⟨i, j, ⟨hi, hj⟩, hxi, hxj⟩
        · rintro ⟨i, j, ⟨hi, hj⟩, hxi, hxj⟩
          exact ⟨⟨i, hi, hxi⟩, ⟨j, hj, hxj⟩⟩
      rw [heq, mu_biUnion (sf ×ˢ sf) (fun p => W p.1 p.2)
        (fun p _ => inter_subset_left.trans (pre_sub _ _))
        (fun p _ => hWmeas p.1 p.2)]
      · rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext ⟨i, j⟩
        simp [sf]
      · intro p₁ _ p₂ _ hpne
        rw [Function.onFun]
        rcases ne_or_eq p₁.1 p₂.1 with h1 | h1
        · exact (pre_disjoint a (hQdisj h1)).mono inter_subset_left inter_subset_left
        · have h2 : p₁.2 ≠ p₂.2 := fun h2 => hpne (Prod.ext h1 h2)
          exact (pre_disjoint b (hQdisj h2)).mono inter_subset_right inter_subset_right
    have hsum1 : 2 * ∑ f : Fin N → Bool, mu (pre a (D f)) = (2 : ℝ) ^ N * mu Y := by
      simp_rw [hmu_prea]
      rw [Finset.sum_comm, Finset.mul_sum]
      simp_rw [sum_bool_single, ← Finset.mul_sum, hmuQ]
    have hsumW_all : ∑ p : Fin N × Fin N, mu (W p.1 p.2) ≤ mu Y := by
      have heq : (⋃ p ∈ (Finset.univ : Finset (Fin N × Fin N)), W p.1 p.2) =
          pre a Y ∩ pre b Y := by
        ext x
        rw [← hQu, pre_biUnion, pre_biUnion]
        simp only [W, mem_iUnion, Finset.mem_univ, exists_prop, true_and, mem_inter_iff,
          Prod.exists]
        constructor
        · rintro ⟨i, j, hxi, hxj⟩
          exact ⟨⟨i, hxi⟩, ⟨j, hxj⟩⟩
        · rintro ⟨⟨i, hxi⟩, ⟨j, hxj⟩⟩
          exact ⟨i, j, hxi, hxj⟩
      have hbu := mu_biUnion (Finset.univ : Finset (Fin N × Fin N)) (fun p => W p.1 p.2)
        (fun p _ => inter_subset_left.trans (pre_sub _ _))
        (fun p _ => hWmeas p.1 p.2)
        (by
          intro p₁ _ p₂ _ hpne
          rw [Function.onFun]
          rcases ne_or_eq p₁.1 p₂.1 with h1 | h1
          · exact (pre_disjoint a (hQdisj h1)).mono inter_subset_left inter_subset_left
          · have h2 : p₁.2 ≠ p₂.2 := fun h2 => hpne (Prod.ext h1 h2)
            exact (pre_disjoint b (hQdisj h2)).mono inter_subset_right inter_subset_right)
      rw [← hbu, heq, ← mu_pre ha hY hmY]
      exact mu_mono (pre_sub a Y) inter_subset_left
    have hsumW_diag : ∑ i : Fin N, mu (W i i) ≤ (1 / 5 : ℝ) * mu Y := by
      have hbu := mu_biUnion (Finset.univ : Finset (Fin N)) (fun i => W i i)
        (fun i _ => inter_subset_left.trans (pre_sub _ _))
        (fun i _ => hWmeas i i)
        (fun i _ j _ hij => (pre_disjoint a (hQdisj hij)).mono inter_subset_left inter_subset_left)
      rw [← hbu]
      refine le_trans (mu_mono ?_ ?_) ((diag_overlap_bound ha hab hN).trans hsmall)
      · exact iUnion₂_subset fun i _ =>
          inter_subset_left.trans (pre_sub _ _)
      · refine iUnion₂_mono fun i _ => inter_subset_inter
          (pre_mono a inter_subset_right) (pre_mono b inter_subset_right)
    have hsum2 : 4 * ∑ f : Fin N → Bool, mu (pre a (D f) ∩ pre b (D f)) ≤
        (2 : ℝ) ^ N * (mu Y + (1 / 5 : ℝ) * mu Y) := by
      simp_rw [hmu_inter]
      rw [Finset.sum_comm, Finset.mul_sum]
      have hterm : ∀ p : Fin N × Fin N,
          4 * ∑ f : Fin N → Bool, (if f p.1 = true ∧ f p.2 = true then mu (W p.1 p.2) else 0) =
            (2 : ℝ) ^ N * mu (W p.1 p.2) +
              (if p.1 = p.2 then (2 : ℝ) ^ N * mu (W p.1 p.2) else 0) := by
        rintro ⟨i, j⟩
        by_cases hij : i = j
        · subst hij
          simp only [and_self, ↓reduceIte]
          have h2 := sum_bool_single i (mu (W i i))
          linarith
        · simp only [hij, ↓reduceIte, add_zero]
          exact sum_bool_pair hij (mu (W i j))
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hdiag_eq : ∑ p : Fin N × Fin N,
          (if p.1 = p.2 then (2 : ℝ) ^ N * mu (W p.1 p.2) else 0) =
            (2 : ℝ) ^ N * ∑ i : Fin N, mu (W i i) := by
        rw [Finset.mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp
      rw [hdiag_eq]
      nlinarith [pow_pos (zero_lt_two : (0 : ℝ) < 2) N]
    have hBf_mu : ∀ f, mu (Bf f) = mu (pre a (D f)) - mu (pre a (D f) ∩ pre b (D f)) := by
      intro f
      have hd : Bf f = pre a (D f) \ (pre a (D f) ∩ pre b (D f)) := by
        ext x; simp only [Bf, Set.mem_sdiff, mem_inter_iff]; tauto
      rw [hd]
      exact mu_diff (pre_sub _ _)
        ((pre_measurable ha ((hDsub f).trans hY) (hDmeas f)).inter
          (pre_measurable hb ((hDsub f).trans hY) (hDmeas f)))
        inter_subset_left
    have havg : ∑ _f : Fin N → Bool, mu Y ≤ ∑ f : Fin N → Bool, (5 * mu (Bf f)) := by
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
      push_cast
      have hsub_sum : ∑ f : Fin N → Bool, mu (Bf f) =
          ∑ f : Fin N → Bool, mu (pre a (D f)) -
            ∑ f : Fin N → Bool, mu (pre a (D f) ∩ pre b (D f)) := by
        simp_rw [hBf_mu, Finset.sum_sub_distrib]
      linarith
    obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le
      ⟨fun _ => false, Finset.mem_univ _⟩ havg
    exact ⟨Bf f, sdiff_subset.trans (pre_mono a (hDsub f)), hBf_meas f, hBf_disj f, hf⟩

def psi {d : ℕ} (p : Fin d → ℕ) (m : Fin d → ℕ) : ℕ :=
  ∏ i : Fin d, p i ^ m i

lemma psi_pos {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i)) (m : Fin d → ℕ) :
    0 < psi p m :=
  Finset.prod_pos fun i _ => pow_pos (hp i).pos _

lemma psi_zero {d : ℕ} (p : Fin d → ℕ) : psi p 0 = 1 := by
  simp [psi]

lemma psi_add {d : ℕ} (p : Fin d → ℕ) (m n : Fin d → ℕ) :
    psi p (m + n) = psi p m * psi p n := by
  simp only [psi, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

lemma psi_factorization {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (m : Fin d → ℕ) (j : Fin d) :
    (psi p m).factorization (p j) = m j := by
  unfold psi
  rw [Nat.factorization_prod fun i _ => (pow_pos (hp i).pos _).ne', Finsupp.finsetSum_apply]
  have hterm : ∀ i : Fin d, (p i ^ m i).factorization (p j) = if i = j then m j else 0 := by
    intro i
    rw [Nat.factorization_pow, Finsupp.smul_apply, (hp i).factorization, Finsupp.single_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have hpne : p i ≠ p j := fun h => hij (hinj h)
      simp [hij, hpne]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp

lemma psi_injective {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) : Function.Injective (psi p) := by
  intro m n h
  ext j
  rw [← psi_factorization hp hinj m j, ← psi_factorization hp hinj n j, h]

def act {d : ℕ} (p : Fin d → ℕ) (m : Fin d → ℕ) (S : Set ℝ) : Set ℝ :=
  pre (psi p m) S

lemma act_zero {d : ℕ} (p : Fin d → ℕ) {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) :
    act p 0 S = S := by
  simp [act, psi_zero, pre_one hS]

lemma act_add {d : ℕ} (p : Fin d → ℕ) (m n : Fin d → ℕ) (S : Set ℝ) :
    act p n (act p m S) = act p (m + n) S := by
  simp [act, pre_comp, psi_add]

lemma act_sub {d : ℕ} (p : Fin d → ℕ) (m : Fin d → ℕ) (S : Set ℝ) :
    act p m S ⊆ Ico (0 : ℝ) 1 :=
  pre_sub _ _

lemma act_mono {d : ℕ} (p : Fin d → ℕ) (m : Fin d → ℕ) {S T : Set ℝ} (h : S ⊆ T) :
    act p m S ⊆ act p m T :=
  pre_mono _ h

lemma act_diff {d : ℕ} (p : Fin d → ℕ) (m : Fin d → ℕ) (S T : Set ℝ) :
    act p m (S \ T) = act p m S \ act p m T :=
  pre_diff _ S T

lemma act_union {d : ℕ} (p : Fin d → ℕ) (m : Fin d → ℕ) (S T : Set ℝ) :
    act p m (S ∪ T) = act p m S ∪ act p m T := by
  ext x; simp [act, pre]; tauto

lemma act_biUnion {d : ℕ} {ι : Type*} (p : Fin d → ℕ) (m : Fin d → ℕ)
    (s : Finset ι) (F : ι → Set ℝ) :
    act p m (⋃ i ∈ s, F i) = ⋃ i ∈ s, act p m (F i) :=
  pre_biUnion _ s F

lemma act_disjoint {d : ℕ} (p : Fin d → ℕ) (m : Fin d → ℕ) {S T : Set ℝ} (h : Disjoint S T) :
    Disjoint (act p m S) (act p m T) :=
  pre_disjoint _ h

lemma act_measurable {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i)) (m : Fin d → ℕ)
    {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) (hm : MeasurableSet S) :
    MeasurableSet (act p m S) :=
  pre_measurable (psi_pos hp m) hS hm

lemma mu_act {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i)) (m : Fin d → ℕ)
    {S : Set ℝ} (hS : S ⊆ Ico (0 : ℝ) 1) (hm : MeasurableSet S) :
    mu (act p m S) = mu S :=
  mu_pre (psi_pos hp m) hS hm

def box {d : ℕ} (n : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.range (n i)

lemma mem_box {d : ℕ} {m n : Fin d → ℕ} : m ∈ box n ↔ ∀ i, m i < n i := by
  simp [box]

lemma card_box {d : ℕ} (n : Fin d → ℕ) : (box n).card = ∏ i, n i := by
  simp [box]

lemma zero_mem_box {d : ℕ} {n : Fin d → ℕ} (hn : ∀ i, 0 < n i) : (0 : Fin d → ℕ) ∈ box n := by
  simp [mem_box, hn]

def IsAdm {d : ℕ} (p : Fin d → ℕ) (n : Fin d → ℕ) (B : Set ℝ) : Prop :=
  B ⊆ Ico (0 : ℝ) 1 ∧ MeasurableSet B ∧
    (↑(box n) : Set (Fin d → ℕ)).PairwiseDisjoint fun k => act p k B

def tower {d : ℕ} (p : Fin d → ℕ) (n : Fin d → ℕ) (B : Set ℝ) : Set ℝ :=
  ⋃ k ∈ box n, act p k B

lemma sub_tower {d : ℕ} {p : Fin d → ℕ} {n : Fin d → ℕ} {B : Set ℝ} {k : Fin d → ℕ}
    (hk : k ∈ box n) : act p k B ⊆ tower p n B :=
  fun _ hx => mem_iUnion₂.mpr ⟨k, hk, hx⟩

lemma tower_sub {d : ℕ} (p : Fin d → ℕ) (n : Fin d → ℕ) (B : Set ℝ) :
    tower p n B ⊆ Ico (0 : ℝ) 1 :=
  iUnion₂_subset fun k _ => act_sub p k B

lemma tower_measurable {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    {n : Fin d → ℕ} {B : Set ℝ} (hB : IsAdm p n B) :
    MeasurableSet (tower p n B) :=
  Finset.measurableSet_biUnion _ fun k _ => act_measurable hp k hB.1 hB.2.1

lemma mu_tower {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    {n : Fin d → ℕ} {B : Set ℝ} (hB : IsAdm p n B) :
    mu (tower p n B) = (∏ i, (n i : ℝ)) * mu B := by
  rw [tower, mu_biUnion (box n) _ (fun k _ => act_sub p k B)
    (fun k _ => act_measurable hp k hB.1 hB.2.1) hB.2.2]
  simp_rw [mu_act hp _ hB.1 hB.2.1, Finset.sum_const, card_box, nsmul_eq_mul, Nat.cast_prod]

lemma basic_tower_list {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (L : List ((Fin d → ℕ) × (Fin d → ℕ)))
    (hL : ∀ kl ∈ L, kl.1 ≠ kl.2) {Y : Set ℝ} (hY : Y ⊆ Ico (0 : ℝ) 1) (hmY : MeasurableSet Y) :
    ∃ M : Fin d → ℕ, ∃ B : Set ℝ, B ⊆ act p M Y ∧ MeasurableSet B ∧
      (∀ kl ∈ L, Disjoint (act p kl.1 B) (act p kl.2 B)) ∧
      mu Y ≤ (5 : ℝ) ^ L.length * mu B := by
  induction L with
  | nil =>
    exact ⟨0, Y, by rw [act_zero p hY], hmY, by simp, by simp⟩
  | cons kl rest ih =>
    obtain ⟨M₁, B₁, hB₁sub, hB₁m, hB₁disj, hB₁mu⟩ :=
      ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    have hB₁Ico : B₁ ⊆ Ico (0 : ℝ) 1 := hB₁sub.trans (act_sub p M₁ Y)
    have hkne : kl.1 ≠ kl.2 := hL kl List.mem_cons_self
    have hpsine : psi p kl.1 ≠ psi p kl.2 := fun h => hkne (psi_injective hp hinj h)
    rcases lt_or_gt_of_ne hpsine with hlt | hgt
    · obtain ⟨B₂, hB₂sub, hB₂m, hB₂disj, hB₂mu⟩ :=
        two_tower_step (psi_pos hp kl.1) hlt hB₁Ico hB₁m
      refine ⟨M₁ + kl.1, B₂, ?_, hB₂m, ?_, ?_⟩
      · exact hB₂sub.trans ((act_mono p kl.1 hB₁sub).trans (by rw [act_add]))
      · intro kl' hmem
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact hB₂disj
        · have h1 : act p kl'.1 B₂ ⊆ act p kl.1 (act p kl'.1 B₁) := by
            calc act p kl'.1 B₂ ⊆ act p kl'.1 (act p kl.1 B₁) := act_mono p kl'.1 hB₂sub
              _ = act p (kl.1 + kl'.1) B₁ := act_add p _ _ _
              _ = act p (kl'.1 + kl.1) B₁ := by rw [add_comm]
              _ = act p kl.1 (act p kl'.1 B₁) := (act_add p _ _ _).symm
          have h2 : act p kl'.2 B₂ ⊆ act p kl.1 (act p kl'.2 B₁) := by
            calc act p kl'.2 B₂ ⊆ act p kl'.2 (act p kl.1 B₁) := act_mono p kl'.2 hB₂sub
              _ = act p (kl.1 + kl'.2) B₁ := act_add p _ _ _
              _ = act p (kl'.2 + kl.1) B₁ := by rw [add_comm]
              _ = act p kl.1 (act p kl'.2 B₁) := (act_add p _ _ _).symm
          exact (act_disjoint p kl.1 (hB₁disj kl' hrest)).mono h1 h2
      · simp only [List.length_cons, pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 5) rest.length]
    · obtain ⟨B₂, hB₂sub, hB₂m, hB₂disj, hB₂mu⟩ :=
        two_tower_step (psi_pos hp kl.2) hgt hB₁Ico hB₁m
      refine ⟨M₁ + kl.2, B₂, ?_, hB₂m, ?_, ?_⟩
      · exact hB₂sub.trans ((act_mono p kl.2 hB₁sub).trans (by rw [act_add]))
      · intro kl' hmem
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact hB₂disj.symm
        · have h1 : act p kl'.1 B₂ ⊆ act p kl.2 (act p kl'.1 B₁) := by
            calc act p kl'.1 B₂ ⊆ act p kl'.1 (act p kl.2 B₁) := act_mono p kl'.1 hB₂sub
              _ = act p (kl.2 + kl'.1) B₁ := act_add p _ _ _
              _ = act p (kl'.1 + kl.2) B₁ := by rw [add_comm]
              _ = act p kl.2 (act p kl'.1 B₁) := (act_add p _ _ _).symm
          have h2 : act p kl'.2 B₂ ⊆ act p kl.2 (act p kl'.2 B₁) := by
            calc act p kl'.2 B₂ ⊆ act p kl'.2 (act p kl.2 B₁) := act_mono p kl'.2 hB₂sub
              _ = act p (kl.2 + kl'.2) B₁ := act_add p _ _ _
              _ = act p (kl'.2 + kl.2) B₁ := by rw [add_comm]
              _ = act p kl.2 (act p kl'.2 B₁) := (act_add p _ _ _).symm
          exact (act_disjoint p kl.2 (hB₁disj kl' hrest)).mono h1 h2
      · simp only [List.length_cons, pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 5) rest.length]

lemma basic_tower {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (n : Fin d → ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {Y : Set ℝ}, Y ⊆ Ico (0 : ℝ) 1 → MeasurableSet Y →
      ∃ M : Fin d → ℕ, ∃ B : Set ℝ, B ⊆ act p M Y ∧ IsAdm p n B ∧ mu Y ≤ (C : ℝ) * mu B := by
  let S := (box n ×ˢ box n).filter fun kl : (Fin d → ℕ) × (Fin d → ℕ) => kl.1 ≠ kl.2
  refine ⟨5 ^ S.card, Nat.one_le_pow _ _ (by omega), ?_⟩
  intro Y hY hmY
  obtain ⟨M, B, hBsub, hBm, hBdisj, hBmu⟩ :=
    basic_tower_list hp hinj S.toList
      (fun kl hkl => (Finset.mem_filter.mp (Finset.mem_toList.mp hkl)).2) hY hmY
  rw [Finset.length_toList] at hBmu
  refine ⟨M, B, hBsub, ⟨hBsub.trans (act_sub p M Y), hBm, ?_⟩, ?_⟩
  · intro k hk l hl hne
    exact hBdisj (k, l)
      (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk, hl⟩, hne⟩))
  · push_cast
    exact hBmu

lemma prop_tower_aux {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    {n : Fin d → ℕ} (hn : ∀ i, 0 < n i) {C : ℕ} (hC1 : 1 ≤ C)
    (hbasic : ∀ {Z : Set ℝ}, Z ⊆ Ico (0 : ℝ) 1 → MeasurableSet Z →
      ∃ M : Fin d → ℕ, ∃ B : Set ℝ, B ⊆ act p M Z ∧ IsAdm p n B ∧ mu Z ≤ (C : ℝ) * mu B)
    {Y : Set ℝ} (hY : Y ⊆ Ico (0 : ℝ) 1) (hmY : MeasurableSet Y) (t : ℕ) :
    ∃ N₀ : Fin d → ℕ, ∃ D : Set ℝ, D ⊆ act p N₀ Y ∧ IsAdm p n D ∧
      ((2⁻¹ : ℝ) ^ (d + 1) * mu Y ≤ mu (tower p n D) ∨
        (t : ℝ) * (2⁻¹ * mu Y / (C : ℝ)) ≤ mu D) := by
  induction t with
  | zero =>
    refine ⟨0, ∅, empty_subset _, ⟨empty_subset _, MeasurableSet.empty, ?_⟩, Or.inr (by simp [mu])⟩
    intro _ _ _ _ _
    simp [act, pre_empty]
  | succ t ih =>
    obtain ⟨N₀, D, hDsub, hDadm, hDor⟩ := ih
    rcases hDor with hdone | hstep
    · exact ⟨N₀, D, hDsub, hDadm, Or.inl hdone⟩
    · by_cases hnow : (2⁻¹ : ℝ) ^ (d + 1) * mu Y ≤ mu (tower p n D)
      · exact ⟨N₀, D, hDsub, hDadm, Or.inl hnow⟩
      · have hnow' : mu (tower p n D) < (2⁻¹ : ℝ) ^ (d + 1) * mu Y := not_le.mp hnow
        have hCR : (0 : ℝ) < C := Nat.cast_pos.mpr hC1
        let n2 : Fin d → ℕ := fun i => 2 * n i
        let T2 : Set ℝ := tower p n2 D
        have hmT2 : MeasurableSet T2 :=
          Finset.measurableSet_biUnion _ fun k _ => act_measurable hp k hDadm.1 hDadm.2.1
        have hmuT2 : mu T2 ≤ 2⁻¹ * mu Y := by
          have h1 : mu T2 ≤ ∑ k ∈ box n2, mu (act p k D) :=
            mu_biUnion_le (box n2) _ fun k _ => act_sub p k D
          have h2 : ∑ k ∈ box n2, mu (act p k D) = (2 : ℝ) ^ d * mu (tower p n D) := by
            simp_rw [mu_act hp _ hDadm.1 hDadm.2.1, Finset.sum_const, card_box, nsmul_eq_mul,
              mu_tower hp hDadm]
            simp only [n2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin]
            push_cast
            ring
          have h3 : (2 : ℝ) ^ d * (2⁻¹ : ℝ) ^ (d + 1) = 2⁻¹ := by
            rw [pow_succ, ← mul_assoc, ← mul_pow]
            norm_num
          have h4 : (2 : ℝ) ^ d * mu (tower p n D) < 2⁻¹ * mu Y := by
            calc (2 : ℝ) ^ d * mu (tower p n D)
              _ < (2 : ℝ) ^ d * ((2⁻¹ : ℝ) ^ (d + 1) * mu Y) :=
                  mul_lt_mul_of_pos_left hnow' (pow_pos zero_lt_two d)
              _ = ((2 : ℝ) ^ d * (2⁻¹ : ℝ) ^ (d + 1)) * mu Y := by ring
              _ = 2⁻¹ * mu Y := by rw [h3]
          linarith
        let Y' : Set ℝ := act p (N₀ + n) Y
        have hY'sub : Y' ⊆ Ico (0 : ℝ) 1 := act_sub p _ Y
        have hmY' : MeasurableSet Y' := act_measurable hp _ hY hmY
        have hmuY' : mu Y' = mu Y := mu_act hp _ hY hmY
        let Z : Set ℝ := Y' \ T2
        have hZsub : Z ⊆ Ico (0 : ℝ) 1 := sdiff_subset.trans hY'sub
        have hmZ : MeasurableSet Z := hmY'.diff hmT2
        have hmuZ : 2⁻¹ * mu Y ≤ mu Z := by
          have heq : Z = Y' \ (Y' ∩ T2) := by
            ext x; simp only [Z, Set.mem_sdiff, mem_inter_iff]; tauto
          rw [heq, mu_diff hY'sub (hmY'.inter hmT2) inter_subset_left, hmuY']
          have hle : mu (Y' ∩ T2) ≤ mu T2 := mu_mono (tower_sub p n2 D) inter_subset_right
          linarith
        obtain ⟨N₁, B'', hB''sub, hB''adm, hB''mu⟩ := hbasic hZsub hmZ
        have hB''lb : 2⁻¹ * mu Y / (C : ℝ) ≤ mu B'' := by
          rw [div_le_iff₀ hCR]
          linarith
        let B₁ : Set ℝ := act p (n + N₁) D
        have hB₁subY : B₁ ⊆ act p (N₀ + n + N₁) Y := by
          calc B₁ = act p N₁ (act p n D) := (act_add p n N₁ D).symm
            _ ⊆ act p N₁ (act p n (act p N₀ Y)) := act_mono p N₁ (act_mono p n hDsub)
            _ = act p (N₀ + n + N₁) Y := by rw [act_add, act_add, add_assoc]
        have hB''subY : B'' ⊆ act p (N₀ + n + N₁) Y := by
          calc B'' ⊆ act p N₁ Z := hB''sub
            _ ⊆ act p N₁ Y' := act_mono p N₁ sdiff_subset
            _ = act p (N₀ + n + N₁) Y := act_add p _ _ Y
        have hcross : ∀ {k l : Fin d → ℕ}, k ∈ box n → l ∈ box n →
            Disjoint (act p k B₁) (act p l B'') := by
          intro k l hk hl
          let m : Fin d → ℕ := fun i => n i + k i - l i
          have hm_box : m ∈ box n2 := by
            rw [mem_box] at hk hl ⊢
            intro i
            dsimp [m, n2]
            have := hk i; have := hl i
            omega
          have hm_eq : m + (N₁ + l) = n + N₁ + k := by
            ext i
            simp only [Pi.add_apply, m]
            have := (mem_box.mp hl) i
            omega
          have hleft : act p k B₁ ⊆ act p (N₁ + l) T2 := by
            calc act p k B₁ = act p (n + N₁ + k) D := act_add p _ _ D
              _ = act p (m + (N₁ + l)) D := by rw [hm_eq]
              _ = act p (N₁ + l) (act p m D) := (act_add p _ _ D).symm
              _ ⊆ act p (N₁ + l) T2 := act_mono p _ (sub_tower hm_box)
          have hright : act p l B'' ⊆ act p (N₁ + l) Y' \ act p (N₁ + l) T2 := by
            calc act p l B'' ⊆ act p l (act p N₁ Z) := act_mono p l hB''sub
              _ = act p (N₁ + l) (Y' \ T2) := act_add p _ _ _
              _ = act p (N₁ + l) Y' \ act p (N₁ + l) T2 := act_diff p _ _ _
          exact disjoint_sdiff_self_right.mono hleft hright
        have hB₁m : MeasurableSet B₁ := act_measurable hp _ hDadm.1 hDadm.2.1
        have hdisj0 : Disjoint B₁ B'' := by
          have hB₁sub : B₁ ⊆ Ico (0 : ℝ) 1 := act_sub p _ D
          simpa only [act_zero p hB₁sub, act_zero p hB''adm.1] using
            hcross (zero_mem_box hn) (zero_mem_box hn)
        refine ⟨N₀ + n + N₁, B₁ ∪ B'', union_subset hB₁subY hB''subY, ?_, Or.inr ?_⟩
        · refine ⟨union_subset (act_sub p _ D) hB''adm.1, hB₁m.union hB''adm.2.1, ?_⟩
          intro k hk l hl hne
          rw [Function.onFun, act_union, act_union]
          refine Disjoint.union_left ?_ ?_
          · refine Disjoint.union_right ?_ (hcross hk hl)
            have hk1 : act p k B₁ = act p (n + N₁) (act p k D) := by
              rw [act_add, act_add, add_comm k (n + N₁)]
            have hl1 : act p l B₁ = act p (n + N₁) (act p l D) := by
              rw [act_add, act_add, add_comm l (n + N₁)]
            rw [hk1, hl1]
            exact act_disjoint p _ (hDadm.2.2 hk hl hne)
          · exact Disjoint.union_right (hcross hl hk).symm (hB''adm.2.2 hk hl hne)
        · rw [mu_union (act_sub p _ D) hB''adm.1 hB''adm.2.1 hdisj0,
            mu_act hp _ hDadm.1 hDadm.2.1, Nat.cast_add, Nat.cast_one]
          linarith

lemma prop_tower {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) {n : Fin d → ℕ} (hn : ∀ i, 0 < n i)
    {Y : Set ℝ} (hY : Y ⊆ Ico (0 : ℝ) 1) (hmY : MeasurableSet Y) :
    ∃ N₀ : Fin d → ℕ, ∃ D : Set ℝ, D ⊆ act p N₀ Y ∧ IsAdm p n D ∧
      (2⁻¹ : ℝ) ^ (d + 1) * mu Y ≤ mu (tower p n D) := by
  by_cases hY0 : mu Y ≤ 0
  · refine ⟨0, ∅, empty_subset _, ⟨empty_subset _, MeasurableSet.empty, fun _ _ _ _ _ => ?_⟩, ?_⟩
    · simp [act, pre_empty]
    · have : mu Y = 0 := le_antisymm hY0 (mu_nonneg Y)
      rw [this, mul_zero]
      exact mu_nonneg _
  · have hYpos : 0 < mu Y := not_le.mp hY0
    obtain ⟨C, hC1, hbasic⟩ := basic_tower hp hinj n
    have hCR : (0 : ℝ) < C := Nat.cast_pos.mpr hC1
    obtain ⟨N₀, D, hDsub, hDadm, hDor⟩ :=
      prop_tower_aux hp hn hC1 hbasic hY hmY (2 * C + 1)
    refine ⟨N₀, D, hDsub, hDadm, ?_⟩
    rcases hDor with hdone | habs
    · exact hdone
    · exfalso
      have hDle : mu D ≤ mu Y := by
        calc mu D ≤ mu (act p N₀ Y) := mu_mono (act_sub p N₀ Y) hDsub
          _ = mu Y := mu_act hp N₀ hY hmY
      have hgt : mu Y < ((2 * C + 1 : ℕ) : ℝ) * (2⁻¹ * mu Y / (C : ℝ)) := by
        have hmul : mu Y * (C : ℝ) < ((2 * C + 1 : ℕ) : ℝ) * (2⁻¹ * mu Y) := by
          push_cast
          nlinarith
        calc mu Y = (mu Y * (C : ℝ)) / (C : ℝ) := by field_simp [hCR.ne']
          _ < (((2 * C + 1 : ℕ) : ℝ) * (2⁻¹ * mu Y)) / (C : ℝ) :=
              div_lt_div_of_pos_right hmul hCR
          _ = ((2 * C + 1 : ℕ) : ℝ) * (2⁻¹ * mu Y / (C : ℝ)) := by ring
      linarith

lemma bernoulli_sub (d : ℕ) {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (d : ℝ) * x ≤ (1 - x) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have h1 : (1 - (d : ℝ) * x) * (1 - x) ≤ (1 - x) ^ d * (1 - x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    nlinarith [sq_nonneg x]

lemma bernoulli_add (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) :
    1 + (k : ℝ) * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have h1 : (1 + (k : ℝ) * x) * (1 + x) ≤ (1 + x) ^ k * (1 + x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    nlinarith [sq_nonneg x]

lemma nat_le_two_pow (K : ℕ) : (K : ℝ) ≤ (2 : ℝ) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
    linarith

lemma full_tower_aux {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (k : ℕ) :
    ∀ {n : Fin d → ℕ}, (∀ i, 0 < n i) →
      ∃ B : Set ℝ, IsAdm p n B ∧ 1 - (1 - (2⁻¹ : ℝ) ^ (d + 2)) ^ k ≤ mu (tower p n B) := by
  let ρ : ℝ := 1 - (2⁻¹ : ℝ) ^ (d + 2)
  have h2pow_pos : 0 < (2⁻¹ : ℝ) ^ (d + 2) := by positivity
  have h2pow_le : (2⁻¹ : ℝ) ^ (d + 2) ≤ 1 / 4 := by
    rw [pow_add]
    have : (2⁻¹ : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith
  induction k with
  | zero =>
    intro n _
    refine ⟨∅, ⟨empty_subset _, MeasurableSet.empty, fun _ _ _ _ _ => ?_⟩, ?_⟩
    · simp [act, pre_empty]
    · simp only [pow_zero, sub_self]
      exact mu_nonneg _
  | succ k ih =>
    intro n hn
    have htarget_pos : 0 < (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k := mul_pos h2pow_pos (pow_pos hρ_pos k)
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt ((d : ℝ) / ((2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k))
    let K : ℕ := K₀ + 1
    have hK_pos : 1 ≤ 2 ^ K := Nat.one_le_pow _ _ (by omega)
    have hK_small : (d : ℝ) * (2⁻¹ : ℝ) ^ K ≤ (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k := by
      have h2K_pos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
      have hK_gt : (d : ℝ) / ((2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k) < (2 : ℝ) ^ K := by
        calc (d : ℝ) / ((2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k) < K₀ := hK₀
          _ ≤ K := by exact_mod_cast Nat.le_succ K₀
          _ ≤ (2 : ℝ) ^ K := nat_le_two_pow K
      rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ h2K_pos]
      have := (div_lt_iff₀ htarget_pos).mp hK_gt
      linarith [mul_comm ((2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k) ((2 : ℝ) ^ K)]
    let n' : Fin d → ℕ := fun i => 2 ^ K * n i
    have hn' : ∀ i, 0 < n' i := fun i => mul_pos (pow_pos zero_lt_two K) (hn i)
    obtain ⟨B', hB'adm, hB'mu⟩ := ih hn'
    change 1 - ρ ^ k ≤ mu (tower p n' B') at hB'mu
    let Y' : Set ℝ := Ico (0 : ℝ) 1 \ tower p n' B'
    have hY'sub : Y' ⊆ Ico (0 : ℝ) 1 := sdiff_subset
    have hmY' : MeasurableSet Y' := measurableSet_Ico.diff (tower_measurable hp hB'adm)
    have hmuY' : mu Y' = 1 - mu (tower p n' B') := by
      rw [mu_diff subset_rfl (tower_measurable hp hB'adm) (tower_sub p n' B'), mu_Ico_zero_one]
    obtain ⟨N', B'', hB''sub, hB''adm, hB''mu⟩ := prop_tower hp hinj hn hY'sub hmY'
    let T_idx : Finset (Fin d → ℕ) := Fintype.piFinset fun _ : Fin d => Finset.Ico 1 (2 ^ K)
    let sh (t : Fin d → ℕ) : Fin d → ℕ := fun i => t i * n i + N' i
    let D : Set ℝ := ⋃ t ∈ T_idx, act p (sh t) B'
    have htk_box : ∀ {t k₁ : Fin d → ℕ}, t ∈ T_idx → k₁ ∈ box n →
        (fun i => t i * n i + k₁ i) ∈ box n' := by
      intro t k₁ ht hk₁
      rw [mem_box]
      intro i
      have ht_i : t i ∈ Finset.Ico 1 (2 ^ K) := (Fintype.mem_piFinset.mp ht) i
      have hk_i : k₁ i < n i := (mem_box.mp hk₁) i
      have ht2 : t i + 1 ≤ 2 ^ K := (Finset.mem_Ico.mp ht_i).2
      dsimp [n']
      nlinarith
    have htk_inj : ∀ {t₁ t₂ k₁ k₂ : Fin d → ℕ},
        k₁ ∈ box n → k₂ ∈ box n →
        (fun i => t₁ i * n i + k₁ i) = (fun i => t₂ i * n i + k₂ i) →
        t₁ = t₂ ∧ k₁ = k₂ := by
      intro t₁ t₂ k₁ k₂ hk₁ hk₂ heq
      have ht_eq : t₁ = t₂ := by
        ext i
        have hi := congr_fun heq i
        have h1 := (mem_box.mp hk₁) i
        have h2 := (mem_box.mp hk₂) i
        rcases lt_trichotomy (t₁ i) (t₂ i) with hlt | h_eq | hgt
        · exfalso; have : t₁ i + 1 ≤ t₂ i := hlt; nlinarith
        · exact h_eq
        · exfalso; have : t₂ i + 1 ≤ t₁ i := hgt; nlinarith
      subst ht_eq
      refine ⟨rfl, ?_⟩
      ext i
      have hi := congr_fun heq i
      omega
    have htk_act : ∀ (t k₁ : Fin d → ℕ),
        act p k₁ (act p (sh t) B') = act p N' (act p (fun i => t i * n i + k₁ i) B') := by
      intro t k₁
      rw [act_add, act_add]
      congr 1
      ext i
      dsimp [sh]
      omega
    have htk_disj : ∀ {t₁ t₂ k₁ k₂ : Fin d → ℕ},
        t₁ ∈ T_idx → t₂ ∈ T_idx → k₁ ∈ box n → k₂ ∈ box n →
        (t₁, k₁) ≠ (t₂, k₂) →
        Disjoint (act p k₁ (act p (sh t₁) B')) (act p k₂ (act p (sh t₂) B')) := by
      intro t₁ t₂ k₁ k₂ ht₁ ht₂ hk₁ hk₂ hne
      rw [htk_act, htk_act]
      refine act_disjoint p N' (hB'adm.2.2 (htk_box ht₁ hk₁) (htk_box ht₂ hk₂) ?_)
      intro heq
      obtain ⟨rfl, rfl⟩ := htk_inj hk₁ hk₂ heq
      exact hne rfl
    have hDadm : IsAdm p n D := by
      refine ⟨iUnion₂_subset fun t _ => act_sub p _ B',
        Finset.measurableSet_biUnion _ fun t _ => act_measurable hp _ hB'adm.1 hB'adm.2.1, ?_⟩
      intro k₁ hk₁ k₂ hk₂ hkne
      rw [Function.onFun, act_biUnion, act_biUnion]
      exact disjoint_biUnion_left fun t₁ ht₁ =>
        disjoint_biUnion_right fun t₂ ht₂ =>
          htk_disj ht₁ ht₂ hk₁ hk₂ fun h => hkne (Prod.ext_iff.mp h).2
    have hmuD_tower : mu (tower p n D) =
        (1 - (2⁻¹ : ℝ) ^ K) ^ d * mu (tower p n' B') := by
      have hDmu : mu D = ((2 ^ K - 1 : ℕ) ^ d : ℝ) * mu B' := by
        rw [mu_biUnion T_idx (fun t => act p (sh t) B')
          (fun t _ => act_sub p _ B')
          (fun t _ => act_measurable hp _ hB'adm.1 hB'adm.2.1)]
        · simp_rw [mu_act hp _ hB'adm.1 hB'adm.2.1, Finset.sum_const, nsmul_eq_mul]
          have hcard : T_idx.card = (2 ^ K - 1) ^ d := by
            simp [T_idx, Nat.card_Ico]
          rw [hcard, Nat.cast_pow]
        · intro t₁ ht₁ t₂ ht₂ htne
          rw [Function.onFun]
          simpa only [act_zero p (act_sub p _ B')] using
            htk_disj ht₁ ht₂ (zero_mem_box hn) (zero_mem_box hn) fun h => htne (Prod.ext_iff.mp h).1
      rw [mu_tower hp hDadm, hDmu, mu_tower hp hB'adm]
      have hprod_n' : (∏ i : Fin d, (n' i : ℝ)) = ((2 : ℝ) ^ K) ^ d * ∏ i : Fin d, (n i : ℝ) := by
        simp only [n', Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hprod_n']
      have hsub_eq : ((2 ^ K - 1 : ℕ) : ℝ) = (2 : ℝ) ^ K * (1 - (2⁻¹ : ℝ) ^ K) := by
        rw [Nat.cast_sub hK_pos, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_sub, mul_one,
          ← mul_pow]
        norm_num
      rw [hsub_eq, mul_pow]
      ring
    have hcross : ∀ {t k₁ k₂ : Fin d → ℕ}, t ∈ T_idx → k₁ ∈ box n → k₂ ∈ box n →
        Disjoint (act p k₁ (act p (sh t) B')) (act p k₂ B'') := by
      intro t k₁ k₂ ht hk₁ hk₂
      have ht_i : ∀ i, 1 ≤ t i ∧ t i < 2 ^ K := fun i =>
        Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp ht) i)
      let m : Fin d → ℕ := fun i => t i * n i + k₁ i - k₂ i
      have hm_box : m ∈ box n' := by
        rw [mem_box]
        intro i
        dsimp [m, n']
        have h1 := (ht_i i).2
        have h2 := (mem_box.mp hk₁) i
        have : t i + 1 ≤ 2 ^ K := h1
        have : t i * n i + k₁ i < 2 ^ K * n i := by nlinarith
        omega
      have hm_eq : m + (N' + k₂) = sh t + k₁ := by
        ext i
        simp only [Pi.add_apply, m, sh]
        have h1 := (ht_i i).1
        have h2 := (mem_box.mp hk₂) i
        have : k₂ i < 1 * n i := by simpa using h2
        have : 1 * n i ≤ t i * n i := Nat.mul_le_mul_right _ h1
        omega
      have hleft : act p k₁ (act p (sh t) B') ⊆ act p (N' + k₂) (tower p n' B') := by
        calc act p k₁ (act p (sh t) B') = act p (sh t + k₁) B' := act_add p _ _ B'
          _ = act p (m + (N' + k₂)) B' := by rw [hm_eq]
          _ = act p (N' + k₂) (act p m B') := (act_add p _ _ B').symm
          _ ⊆ act p (N' + k₂) (tower p n' B') := act_mono p _ (sub_tower hm_box)
      have hright : act p k₂ B'' ⊆ act p (N' + k₂) (Ico 0 1) \ act p (N' + k₂) (tower p n' B') := by
        calc act p k₂ B'' ⊆ act p k₂ (act p N' Y') := act_mono p k₂ hB''sub
          _ = act p (N' + k₂) (Ico 0 1 \ tower p n' B') := act_add p _ _ _
          _ = act p (N' + k₂) (Ico 0 1) \ act p (N' + k₂) (tower p n' B') := act_diff p _ _ _
      exact disjoint_sdiff_self_right.mono hleft hright
    have hcrossD : ∀ {k₁ k₂ : Fin d → ℕ}, k₁ ∈ box n → k₂ ∈ box n →
        Disjoint (act p k₁ D) (act p k₂ B'') := by
      intro k₁ k₂ hk₁ hk₂
      rw [act_biUnion]
      exact disjoint_biUnion_left fun t ht => hcross ht hk₁ hk₂
    have hBadm : IsAdm p n (B'' ∪ D) := by
      refine ⟨union_subset hB''adm.1 hDadm.1, hB''adm.2.1.union hDadm.2.1, ?_⟩
      intro k₁ hk₁ k₂ hk₂ hkne
      rw [Function.onFun, act_union, act_union]
      exact Disjoint.union_left
        (Disjoint.union_right (hB''adm.2.2 hk₁ hk₂ hkne) (hcrossD hk₂ hk₁).symm)
        (Disjoint.union_right (hcrossD hk₁ hk₂) (hDadm.2.2 hk₁ hk₂ hkne))
    refine ⟨B'' ∪ D, hBadm, ?_⟩
    change 1 - ρ ^ (k + 1) ≤ mu (tower p n (B'' ∪ D))
    have htow_eq : tower p n (B'' ∪ D) = tower p n B'' ∪ tower p n D := by
      ext y
      simp only [tower, act_union, mem_union, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨i, hi, hy | hy⟩
        · exact Or.inl ⟨i, hi, hy⟩
        · exact Or.inr ⟨i, hi, hy⟩
      · rintro (⟨i, hi, hy⟩ | ⟨i, hi, hy⟩)
        · exact ⟨i, hi, Or.inl hy⟩
        · exact ⟨i, hi, Or.inr hy⟩
    have htow_disj : Disjoint (tower p n B'') (tower p n D) :=
      disjoint_biUnion_left fun k₂ hk₂ =>
        disjoint_biUnion_right fun k₁ hk₁ => (hcrossD hk₁ hk₂).symm
    rw [htow_eq, mu_union (tower_sub p n B'') (tower_sub p n D) (tower_measurable hp hDadm) htow_disj]
    let x := mu (tower p n' B')
    have hx0 : 0 ≤ x := mu_nonneg _
    have hx1 : x ≤ 1 := mu_le_one (tower_sub p n' B')
    have hbern : 1 - (d : ℝ) * (2⁻¹ : ℝ) ^ K ≤ (1 - (2⁻¹ : ℝ) ^ K) ^ d :=
      bernoulli_sub d (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    have hD_lb : x - (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k ≤ mu (tower p n D) := by
      rw [hmuD_tower]
      have h1 : (1 - (d : ℝ) * (2⁻¹ : ℝ) ^ K) * x ≤ (1 - (2⁻¹ : ℝ) ^ K) ^ d * x :=
        mul_le_mul_of_nonneg_right hbern hx0
      have h2 : ((d : ℝ) * (2⁻¹ : ℝ) ^ K) * x ≤ (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k := by
        calc ((d : ℝ) * (2⁻¹ : ℝ) ^ K) * x ≤ ((d : ℝ) * (2⁻¹ : ℝ) ^ K) * 1 :=
              mul_le_mul_of_nonneg_left hx1 (by positivity)
          _ ≤ (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k := by linarith
      linarith
    have hB''_lb : (2⁻¹ : ℝ) ^ (d + 1) * (1 - x) ≤ mu (tower p n B'') := by
      rwa [hmuY'] at hB''mu
    have h2d1_le : (2⁻¹ : ℝ) ^ (d + 1) ≤ 1 / 2 := by
      rw [pow_succ]
      have : (2⁻¹ : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hmon : (1 - (2⁻¹ : ℝ) ^ (d + 1)) * (1 - ρ ^ k) ≤ (1 - (2⁻¹ : ℝ) ^ (d + 1)) * x :=
      mul_le_mul_of_nonneg_left hB'mu (by linarith)
    have hpow_rel : (2⁻¹ : ℝ) ^ (d + 1) = 2 * (2⁻¹ : ℝ) ^ (d + 2) := by
      rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
      ring
    have hident : 1 - ρ ^ (k + 1) =
        (1 - (2⁻¹ : ℝ) ^ (d + 1)) * (1 - ρ ^ k) +
          (2⁻¹ : ℝ) ^ (d + 1) - (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k := by
      have hρ_succ : ρ ^ (k + 1) = ρ ^ k * (1 - (2⁻¹ : ℝ) ^ (d + 2)) := pow_succ ρ k
      rw [hρ_succ, hpow_rel]
      ring
    have hident2 : (2⁻¹ : ℝ) ^ (d + 1) * (1 - x) + (x - (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k) =
        (1 - (2⁻¹ : ℝ) ^ (d + 1)) * x +
          (2⁻¹ : ℝ) ^ (d + 1) - (2⁻¹ : ℝ) ^ (d + 2) * ρ ^ k := by
      ring
    linarith

lemma full_tower_three_quarters {d : ℕ} {p : Fin d → ℕ} (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) {n : Fin d → ℕ} (hn : ∀ i, 0 < n i) :
    ∃ B : Set ℝ, IsAdm p n B ∧ (3 / 4 : ℝ) ≤ mu (tower p n B) := by
  let a : ℝ := (2⁻¹ : ℝ) ^ (d + 2)
  have ha_pos : 0 < a := by positivity
  have ha_lt1 : a ≤ 1 / 4 := by
    dsimp [a]; rw [pow_add]
    have : (2⁻¹ : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let k : ℕ := 4 * 2 ^ (d + 2)
  obtain ⟨B, hBadm, hBmu⟩ := full_tower_aux hp hinj k hn
  refine ⟨B, hBadm, ?_⟩
  have hka : (k : ℝ) * a = 4 := by
    dsimp [k, a]
    push_cast
    rw [mul_assoc, ← mul_pow]
    norm_num
  have h1a : 5 ≤ (1 + a) ^ k := by
    have := bernoulli_add k ha_pos.le
    linarith
  have hprod : ((1 - a) * (1 + a)) ^ k ≤ 1 := by
    apply pow_le_one₀
    · nlinarith
    · nlinarith [sq_nonneg a]
  have hpow_le : (1 - a) ^ k ≤ 1 / 4 := by
    rw [mul_pow] at hprod
    have hpos : 0 ≤ (1 - a) ^ k := pow_nonneg (by linarith) k
    nlinarith
  change 1 - (1 - a) ^ k ≤ mu (tower p n B) at hBmu
  linarith

lemma fract_step_hit {K : ℕ} (hK : 1 ≤ K) (b : Fin K) (y₀ : ℝ) :
    ∃ s ∈ Finset.Icc 1 (2 * K + 1),
      (2 * (b : ℝ) + 1) / (2 * K) ≤ Int.fract (y₀ + (s : ℝ) / (2 * K)) ∧
      Int.fract (y₀ + (s : ℝ) / (2 * K)) < (2 * (b : ℝ) + 2) / (2 * K) := by
  have h2K_pos : (0 : ℝ) < 2 * (K : ℝ) := by positivity
  have h2KZ_pos : (0 : ℤ) < 2 * (K : ℤ) := by omega
  let c : ℤ := ⌈2 * (b : ℝ) + 1 - 2 * (K : ℝ) * y₀⌉
  let r : ℤ := (c - 1) % (2 * (K : ℤ))
  let q : ℤ := (c - 1) / (2 * (K : ℤ))
  have hr0 : 0 ≤ r := Int.emod_nonneg _ h2KZ_pos.ne'
  have hr1 : r < 2 * (K : ℤ) := Int.emod_lt_of_pos _ h2KZ_pos
  let s : ℕ := (r + 1).toNat
  have hs_cast : (s : ℤ) = r + 1 := Int.toNat_of_nonneg (by omega)
  have hs_mem : s ∈ Finset.Icc 1 (2 * K + 1) := by
    rw [Finset.mem_Icc]
    constructor <;> zify <;> omega
  have hdiv : 2 * (K : ℤ) * q + r = c - 1 := Int.mul_ediv_add_emod (c - 1) (2 * (K : ℤ))
  have hsc : (s : ℝ) = (c : ℝ) - 2 * (K : ℝ) * (q : ℝ) := by
    have hz : (s : ℤ) = c - 2 * (K : ℤ) * q := by omega
    exact_mod_cast hz
  have hceil_le : 2 * (b : ℝ) + 1 - 2 * (K : ℝ) * y₀ ≤ (c : ℝ) := Int.le_ceil _
  have hceil_lt : (c : ℝ) < 2 * (b : ℝ) + 1 - 2 * (K : ℝ) * y₀ + 1 := Int.ceil_lt_add_one _
  let val : ℝ := (2 * (K : ℝ) * y₀ + (c : ℝ)) / (2 * K)
  have hval_lo : (2 * (b : ℝ) + 1) / (2 * K) ≤ val := by
    dsimp [val]
    rw [div_le_div_iff_of_pos_right h2K_pos]
    linarith
  have hval_hi : val < (2 * (b : ℝ) + 2) / (2 * K) := by
    dsimp [val]
    rw [div_lt_div_iff_of_pos_right h2K_pos]
    linarith
  have hval_Ico : val ∈ Ico (0 : ℝ) 1 := by
    refine ⟨le_trans (by positivity) hval_lo, lt_of_lt_of_le hval_hi ?_⟩
    rw [div_le_one h2K_pos]
    have hb : (b : ℝ) + 1 ≤ K := by exact_mod_cast b.isLt
    linarith
  have heq : y₀ + (s : ℝ) / (2 * K) = val - (q : ℝ) := by
    dsimp [val]
    rw [hsc]
    field_simp
    ring
  refine ⟨s, hs_mem, ?_, ?_⟩
  · rw [heq, Int.fract_sub_intCast, Int.fract_eq_self.mpr hval_Ico]
    exact hval_lo
  · rw [heq, Int.fract_sub_intCast, Int.fract_eq_self.mpr hval_Ico]
    exact hval_hi

lemma prod_primes_up_to {M k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    (∏ q ∈ (Finset.Icc 2 M).filter Nat.Prime, q ^ k.factorization q) = k := by
  have hk0 : k ≠ 0 := by omega
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hk0]
  symm
  refine Finset.prod_subset ?_ ?_
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hpq : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    exact ⟨⟨hpq.two_le, (Nat.le_of_mem_primeFactors hq).trans hkM⟩, hpq⟩
  · intro q _ hq_not
    have hzero : k.factorization q = 0 := Finsupp.notMem_support_iff.mp hq_not
    rw [hzero, pow_zero]

lemma factorization_le_self_of_le {M k q : ℕ} (hkM : k ≤ M) :
    k.factorization q ≤ M := by
  by_cases hk0 : k = 0
  · subst hk0; simp
  · by_cases hq : q ∈ k.primeFactors
    · have hpq : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
      have hdvd : q ^ k.factorization q ∣ k := Nat.ordProj_dvd k q
      have hpow_le : q ^ k.factorization q ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd
      exact (Nat.lt_pow_self hpq.one_lt).le.trans (hpow_le.trans hkM)
    · have hzero : k.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
      omega

lemma exists_prime_basis (M : ℕ) :
    ∃ (d : ℕ) (p : Fin d → ℕ) (v_exp : ℕ → Fin d → ℕ),
      (∀ i, Nat.Prime (p i)) ∧ Function.Injective p ∧
      (∀ {k : ℕ}, 1 ≤ k → k ≤ M → psi p (v_exp k) = k) ∧
      (∀ {k : ℕ}, k ≤ M → ∀ i : Fin d, v_exp k i ≤ M) := by
  classical
  let P_set : Finset ℕ := (Finset.Icc 2 M).filter Nat.Prime
  let d : ℕ := P_set.card
  let p_equiv : Fin d ≃ {q // q ∈ P_set} := P_set.equivFin.symm
  let p (i : Fin d) : ℕ := (p_equiv i).1
  let v_exp (k : ℕ) : Fin d → ℕ := fun i => k.factorization (p i)
  refine ⟨d, p, v_exp, fun i => (Finset.mem_filter.mp (p_equiv i).2).2,
    fun i₁ i₂ h => p_equiv.injective (Subtype.ext h), ?_, fun hkM i => factorization_le_self_of_le hkM⟩
  intro k hk1 hkM
  unfold psi v_exp
  have hbij : (∏ i : Fin d, p i ^ k.factorization (p i)) =
      ∏ q ∈ P_set, q ^ k.factorization q := by
    rw [← Finset.prod_attach P_set]
    exact Equiv.prod_comp p_equiv fun q => (q : ℕ) ^ k.factorization (q : ℕ)
  rw [hbij]
  exact prod_primes_up_to hk1 hkM

theorem h1_proof : OMA.R_Erdos994_erdos_994_R1.H1 := by
  classical
  intro j
  obtain ⟨K, hK_def⟩ : ∃ K : ℕ, K = 8 * 2 ^ j := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK_def]; have := Nat.one_le_pow j 2 (by omega); omega
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK1
  obtain ⟨j', hj'_def⟩ : ∃ j' : ℕ, j' = max j 2 := ⟨_, rfl⟩
  have hj_le_j' : j ≤ j' := hj'_def ▸ le_max_left j 2
  have hj'2 : 2 ≤ j' := hj'_def ▸ le_max_right j 2
  obtain ⟨S_steps, hS_def⟩ : ∃ S_steps : ℕ, S_steps = 2 * K + 1 := ⟨_, rfl⟩
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = j' * 2 ^ S_steps := ⟨_, rfl⟩
  obtain ⟨d, p, v_exp, hp, hinj, hpsi_v, hv_le⟩ := exists_prime_basis M
  obtain ⟨R, hR_def⟩ : ∃ R : ℕ, R = 3 * (d + 1) * (M + 1) := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR_def]; nlinarith
  obtain ⟨H, hH_def⟩ : ∃ H : ℕ, H = R + M := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := by omega
  have hHR : (0 : ℝ) < H := Nat.cast_pos.mpr hH1
  let n_H : Fin d → ℕ := fun _ => H
  have hn_H : ∀ i, 0 < n_H i := fun _ => hH1
  obtain ⟨W₀, hW₀adm, hW₀mu⟩ := full_tower_three_quarters hp hinj hn_H
  let W : Set ℝ := W₀ \ {0}
  have hW_Ioo : W ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hxIco := hW₀adm.1 hx.1
    have hxne : x ≠ 0 := hx.2
    exact ⟨lt_of_le_of_ne hxIco.1 hxne.symm, hxIco.2⟩
  have hW_Ico : W ⊆ Ico (0 : ℝ) 1 := hW_Ioo.trans Ioo_subset_Ico_self
  have hWm : MeasurableSet W := hW₀adm.2.1.diff (measurableSet_singleton 0)
  have hWmu_eq : mu W = mu W₀ := by
    unfold mu W
    rw [measure_sdiff_null (measure_singleton 0)]
  have hWadm : IsAdm p n_H W := by
    refine ⟨hW_Ico, hWm, fun k₁ hk₁ k₂ hk₂ hne => ?_⟩
    exact (hW₀adm.2.2 hk₁ hk₂ hne).mono (act_mono p k₁ sdiff_subset) (act_mono p k₂ sdiff_subset)
  have hHpow_pos : (0 : ℝ) < (H : ℝ) ^ d := pow_pos hHR d
  have hprod_H : (∏ _i : Fin d, (H : ℝ)) = (H : ℝ) ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hHW_lb : (3 / 4 : ℝ) ≤ (H : ℝ) ^ d * mu W := by
    have htow₀ : mu (tower p n_H W₀) = (H : ℝ) ^ d * mu W := by
      rw [mu_tower hp hW₀adm, ← hWmu_eq]
      dsimp [n_H]
      rw [hprod_H]
    linarith
  have hHW_ub : (H : ℝ) ^ d * mu W ≤ 1 := by
    have htow : mu (tower p n_H W) = (H : ℝ) ^ d * mu W := by
      rw [mu_tower hp hWadm]
      dsimp [n_H]
      rw [hprod_H]
    rw [← htow]
    exact mu_le_one (tower_sub p n_H W)
  let rev (r : Fin d → ℕ) : Fin d → ℕ := fun i => H - 1 - r i
  have hrev_box : ∀ {r : Fin d → ℕ}, r ∈ box n_H → rev r ∈ box n_H := by
    intro r hr
    rw [mem_box] at hr ⊢
    intro i; dsimp [rev, n_H] at hr ⊢; have := hr i; omega
  have hrev_inj : ∀ {r₁ r₂ : Fin d → ℕ}, r₁ ∈ box n_H → r₂ ∈ box n_H →
      rev r₁ = rev r₂ → r₁ = r₂ := by
    intro r₁ r₂ hr₁ hr₂ heq
    ext i
    have hi := congr_fun heq i
    dsimp [rev] at hi
    have h1 : r₁ i < H := (mem_box.mp hr₁) i
    have h2 : r₂ i < H := (mem_box.mp hr₂) i
    omega
  let lvl (r : Fin d → ℕ) : Set ℝ := act p (rev r) W
  have hlvl_Ioo : ∀ r, lvl r ⊆ Ioo (0 : ℝ) 1 := by
    intro r x hx
    have hxIco : x ∈ Ico (0 : ℝ) 1 := hx.2
    have hdil : dil (psi p (rev r)) x ∈ W := hx.1
    refine ⟨?_, hxIco.2⟩
    by_contra hxle
    have hx0 : x = 0 := le_antisymm (not_lt.mp hxle) hxIco.1
    subst hx0
    have hd0 : dil (psi p (rev r)) 0 = 0 := by simp [dil]
    rw [hd0] at hdil
    exact (hW_Ioo hdil).1.ne rfl
  have hlvl_m : ∀ r, MeasurableSet (lvl r) := fun r => act_measurable hp (rev r) hW_Ico hWm
  have hlvl_mu : ∀ r, mu (lvl r) = mu W := fun r => mu_act hp (rev r) hW_Ico hWm
  have hlvl_disj : (↑(box n_H) : Set (Fin d → ℕ)).PairwiseDisjoint lvl := by
    intro r₁ hr₁ r₂ hr₂ hne
    exact hWadm.2.2 (hrev_box hr₁) (hrev_box hr₂) fun h => hne (hrev_inj hr₁ hr₂ h)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdenom_pos : 0 < 2 * (K : ℝ) * Real.log 2 := by positivity
  let L_log (r : Fin d → ℕ) : ℝ :=
    (∑ i : Fin d, (r i : ℝ) * Real.log (p i)) / (2 * (K : ℝ) * Real.log 2)
  have hL_add_k : ∀ (m : Fin d → ℕ) {k : ℕ}, 1 ≤ k → k ≤ M →
      L_log (m + v_exp k) = L_log m + Real.log (k : ℝ) / (2 * (K : ℝ) * Real.log 2) := by
    intro m k hk1 hkM
    have hlog_k : Real.log (k : ℝ) = ∑ i : Fin d, (v_exp k i : ℝ) * Real.log (p i) := by
      conv_lhs => rw [← hpsi_v hk1 hkM]
      unfold psi
      rw [Nat.cast_prod, Real.log_prod fun i _ => Nat.cast_ne_zero.mpr (pow_pos (hp i).pos _).ne']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    dsimp [L_log]
    rw [hlog_k, ← add_div, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    change (((m i + v_exp k i : ℕ) : ℝ) * Real.log (p i)) =
      (m i : ℝ) * Real.log (p i) + (v_exp k i : ℝ) * Real.log (p i)
    rw [Nat.cast_add]
    ring
  let Eb (b : Fin K) : Finset (Fin d → ℕ) :=
    (box n_H).filter fun r =>
      (b : ℝ) / K ≤ Int.fract (L_log r) ∧ Int.fract (L_log r) < ((b : ℝ) + 1) / K
  have hEb_part : ∑ b : Fin K, (Eb b).card = H ^ d := by
    have hcard_H : (box n_H).card = H ^ d := by
      rw [card_box]
      dsimp [n_H]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← hcard_H, ← Finset.card_biUnion]
    · congr 1
      ext r
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Eb, Finset.mem_filter]
      constructor
      · rintro ⟨_, hr, _⟩; exact hr
      · intro hr
        have hmem : Int.fract (L_log r) ∈ ⋃ b ∈ (Finset.univ : Finset (Fin K)), cell K b := by
          rw [iUnion_cell hK1]
          exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
        simp only [mem_iUnion, Finset.mem_univ, exists_prop, true_and] at hmem
        obtain ⟨b, hb1, hb2⟩ := hmem
        exact ⟨b, hr, hb1, hb2⟩
    · intro b₁ _ b₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro r hr₁ hr₂
      have h1 := (Finset.mem_filter.mp hr₁).2
      have h2 := (Finset.mem_filter.mp hr₂).2
      exact Set.disjoint_left.mp (cell_disjoint (Finset.mem_univ b₁) (Finset.mem_univ b₂) hne) h1 h2
  have hpig : ∑ b : Fin K, (K * (Eb b).card) ≤ ∑ _b : Fin K, H ^ d := by
    rw [← Finset.mul_sum, hEb_part, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  obtain ⟨b, _, hb_card⟩ := Finset.exists_le_of_sum_le ⟨⟨0, hK1⟩, Finset.mem_univ _⟩ hpig
  let E : Set ℝ := ⋃ r ∈ Eb b, lvl r
  let n_R : Fin d → ℕ := fun _ => R
  let B : Set ℝ := ⋃ m ∈ box n_R, lvl m
  have hE_Ioo : E ⊆ Ioo (0 : ℝ) 1 := iUnion₂_subset fun r _ => hlvl_Ioo r
  have hE_Ico : E ⊆ Ico (0 : ℝ) 1 := hE_Ioo.trans Ioo_subset_Ico_self
  have hEm : MeasurableSet E := Finset.measurableSet_biUnion _ fun r _ => hlvl_m r
  have hB_Ioo : B ⊆ Ioo (0 : ℝ) 1 := iUnion₂_subset fun m _ => hlvl_Ioo m
  have hB_Ico : B ⊆ Ico (0 : ℝ) 1 := hB_Ioo.trans Ioo_subset_Ico_self
  have hBm : MeasurableSet B := Finset.measurableSet_biUnion _ fun m _ => hlvl_m m
  have hboxR_sub : box n_R ⊆ box n_H := by
    intro m hm
    rw [mem_box] at hm ⊢
    intro i; have := hm i; dsimp [n_R, n_H] at this ⊢; omega
  have hvolE : volume E ≤ (8 : ℝ≥0∞)⁻¹ * (2⁻¹ : ℝ≥0∞) ^ j := by
    have hmuE : mu E ≤ (8⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ j := by
      have hEb_sub : Eb b ⊆ box n_H := Finset.filter_subset _ _
      rw [mu_biUnion (Eb b) lvl (fun r _ => (hlvl_Ioo r).trans Ioo_subset_Ico_self)
        (fun r _ => hlvl_m r) (hlvl_disj.subset hEb_sub)]
      simp_rw [hlvl_mu, Finset.sum_const, nsmul_eq_mul]
      have hcardR : (K : ℝ) * ((Eb b).card : ℝ) ≤ (H : ℝ) ^ d := by exact_mod_cast hb_card
      have hcard_le : ((Eb b).card : ℝ) ≤ (H : ℝ) ^ d / K := (le_div_iff₀' hK_pos).mpr hcardR
      have hW_le : mu W ≤ ((H : ℝ) ^ d)⁻¹ := by
        calc mu W = ((H : ℝ) ^ d * mu W) / (H : ℝ) ^ d := by field_simp [hHpow_pos.ne']
          _ ≤ 1 / (H : ℝ) ^ d := div_le_div_of_nonneg_right hHW_ub hHpow_pos.le
          _ = ((H : ℝ) ^ d)⁻¹ := one_div _
      have hprod_le : ((Eb b).card : ℝ) * mu W ≤ (K : ℝ)⁻¹ := by
        calc ((Eb b).card : ℝ) * mu W ≤ ((H : ℝ) ^ d / K) * ((H : ℝ) ^ d)⁻¹ :=
              mul_le_mul hcard_le hW_le (mu_nonneg W) (by positivity)
          _ = (K : ℝ)⁻¹ := by field_simp [hHpow_pos.ne']
      have hK_eq : (K : ℝ)⁻¹ = (8⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ j := by
        rw [hK_def]; push_cast; rw [mul_inv, inv_pow]
      linarith
    rw [← ENNReal.ofReal_toReal (volume_ne_top_of_sub hE_Ico)]
    calc ENNReal.ofReal (mu E) ≤ ENNReal.ofReal ((8⁻¹ : ℝ) * (2⁻¹ : ℝ) ^ j) :=
          ENNReal.ofReal_le_ofReal hmuE
      _ = (8 : ℝ≥0∞)⁻¹ * (2⁻¹ : ℝ≥0∞) ^ j := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
  have hvolB : (2 : ℝ≥0∞)⁻¹ ≤ volume B := by
    have hmuB : (1 / 2 : ℝ) ≤ mu B := by
      rw [mu_biUnion (box n_R) lvl (fun m _ => (hlvl_Ioo m).trans Ioo_subset_Ico_self)
        (fun m _ => hlvl_m m) (hlvl_disj.subset hboxR_sub)]
      simp_rw [hlvl_mu, Finset.sum_const, card_box, nsmul_eq_mul]
      have hprodR : (∏ _i : Fin d, R : ℕ) = R ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      dsimp [n_R]
      rw [hprodR, Nat.cast_pow]
      have hRH : (R : ℝ) / H = 1 - (M : ℝ) / H := by
        have hHR_eq : (H : ℝ) = (R : ℝ) + M := by rw [hH_def]; push_cast; rfl
        field_simp [hHR.ne']
        linarith
      have hMH_le : (d : ℝ) * ((M : ℝ) / H) ≤ 1 / 3 := by
        rw [mul_div_assoc', div_le_iff₀ hHR]
        have hR_real : (R : ℝ) = 3 * ((d : ℝ) + 1) * ((M : ℝ) + 1) := by
          rw [hR_def]; push_cast; ring
        have hH_real : (H : ℝ) = (R : ℝ) + M := by rw [hH_def]; push_cast; rfl
        nlinarith
      have hratio : (2 / 3 : ℝ) ≤ ((R : ℝ) / H) ^ d := by
        rw [hRH]
        have hM_le_H : (M : ℝ) ≤ H := by
          have : M ≤ H := by omega
          exact_mod_cast this
        have hbern := bernoulli_sub d (by positivity : (0 : ℝ) ≤ (M : ℝ) / H)
          (div_le_one_of_le₀ hM_le_H hHR.le)
        linarith
      have hident : (R : ℝ) ^ d * mu W = ((R : ℝ) / H) ^ d * ((H : ℝ) ^ d * mu W) := by
        rw [div_pow]
        field_simp [hHpow_pos.ne']
      rw [hident]
      nlinarith
    rw [← ENNReal.ofReal_toReal (volume_ne_top_of_sub hB_Ico)]
    calc (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (mu B) := ENNReal.ofReal_le_ofReal hmuB
  refine ⟨E, B, M, hE_Ioo, hEm, hvolE, hB_Ioo, hBm, hvolB, ?_⟩
  intro α hα
  obtain ⟨m, hm_R, hαm⟩ := mem_iUnion₂.mp hα
  let y₀ : ℝ := L_log m + Real.log (j' : ℝ) / (2 * (K : ℝ) * Real.log 2)
  obtain ⟨s, hs_Icc, hs_lo, hs_hi⟩ := fract_step_hit hK1 b y₀
  obtain ⟨hs1, hs2K⟩ := Finset.mem_Icc.mp hs_Icc
  have hsS : s ≤ S_steps := by omega
  obtain ⟨n, hn_def⟩ : ∃ n : ℕ, n = j' * 2 ^ s := ⟨_, rfl⟩
  have hn_pos : 0 < n := by rw [hn_def]; exact mul_pos (by omega) (pow_pos zero_lt_two s)
  have hn_Icc : n ∈ Finset.Icc j M := by
    rw [Finset.mem_Icc, hn_def, hM_def]
    refine ⟨hj_le_j'.trans (Nat.le_mul_of_pos_right j' (pow_pos zero_lt_two s)), ?_⟩
    exact Nat.mul_le_mul_left j' (Nat.pow_le_pow_right (by omega) hsS)
  refine ⟨n, hn_Icc, ?_⟩
  have hns_log : L_log (m + v_exp n) = y₀ + (s : ℝ) / (2 * K) := by
    rw [hL_add_k m hn_pos (Finset.mem_Icc.mp hn_Icc).2]
    dsimp [y₀]
    rw [hn_def, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hne : Real.log 2 ≠ 0 := hlog2_pos.ne'
    field_simp [hne]
    ring
  obtain ⟨k_lo, hk_lo_def⟩ : ∃ k_lo : ℕ, k_lo = j' * 2 ^ (s - 1) := ⟨_, rfl⟩
  have hk_lo_pos : 1 ≤ k_lo := by
    rw [hk_lo_def]
    exact mul_pos (by omega : 0 < j') (pow_pos zero_lt_two _)
  have hn_eq : n = 2 * k_lo := by
    rw [hn_def, hk_lo_def]
    conv_lhs => rw [← Nat.sub_add_cancel hs1, pow_succ]
    ring
  have hk_hit : ∀ k ∈ Finset.Icc k_lo n, Int.fract ((k : ℝ) * α) ∈ E := by
    intro k hk
    obtain ⟨hk_ge, hk_le⟩ := Finset.mem_Icc.mp hk
    have hk1 : 1 ≤ k := hk_lo_pos.trans hk_ge
    have hkM : k ≤ M := hk_le.trans (Finset.mem_Icc.mp hn_Icc).2
    have hmv_box : m + v_exp k ∈ box n_H := by
      rw [mem_box]
      intro i
      have hm_i : m i < R := (mem_box.mp hm_R) i
      have hv_i : v_exp k i ≤ M := hv_le hkM i
      dsimp [n_H]
      omega
    have h_in_lvl : Int.fract ((k : ℝ) * α) ∈ lvl (m + v_exp k) := by
      have hrev_eq : rev (m + v_exp k) + v_exp k = rev m := by
        ext i
        simp only [Pi.add_apply, rev]
        have hm_i : m i < R := (mem_box.mp hm_R) i
        have hv_i : v_exp k i ≤ M := hv_le hkM i
        omega
      have hmul_psi : psi p (rev (m + v_exp k)) * k = psi p (rev m) := by
        calc psi p (rev (m + v_exp k)) * k
          _ = psi p (rev (m + v_exp k)) * psi p (v_exp k) := by rw [hpsi_v hk1 hkM]
          _ = psi p (rev (m + v_exp k) + v_exp k) := (psi_add _ _ _).symm
          _ = psi p (rev m) := by rw [hrev_eq]
      refine ⟨?_, dil_mem_Ico k α⟩
      change dil (psi p (rev (m + v_exp k))) (dil k α) ∈ W
      rw [dil_mul, hmul_psi]
      exact hαm.1
    have h_in_Eb : m + v_exp k ∈ Eb b := by
      rw [Finset.mem_filter]
      refine ⟨hmv_box, ?_⟩
      let δ : ℝ := (Real.log (k : ℝ) - Real.log (n : ℝ)) / (2 * (K : ℝ) * Real.log 2)
      have hδ_le0 : δ ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hdenom_pos.le
        have : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (Nat.cast_pos.mpr hk1) (by exact_mod_cast hk_le)
        linarith
      have hδ_ge : -(1 / (2 * (K : ℝ))) ≤ δ := by
        dsimp [δ]
        rw [← neg_div, le_div_iff₀ hdenom_pos]
        have h1 : (n : ℝ) ≤ 2 * (k : ℝ) := by
          have : n ≤ 2 * k := by omega
          exact_mod_cast this
        have hlog_le : Real.log (n : ℝ) ≤ Real.log 2 + Real.log (k : ℝ) := by
          rw [← Real.log_mul two_ne_zero (Nat.cast_ne_zero.mpr (by omega))]
          exact Real.log_le_log (Nat.cast_pos.mpr hn_pos) h1
        have hsimp : (-1 : ℝ) / (2 * (K : ℝ)) * (2 * (K : ℝ) * Real.log 2) = -Real.log 2 := by
          field_simp [hK_pos.ne']
        linarith
      have hL_diff : L_log (m + v_exp k) = L_log (m + v_exp n) + δ := by
        rw [hL_add_k m hk1 hkM, hL_add_k m hn_pos (Finset.mem_Icc.mp hn_Icc).2]
        dsimp [δ]
        ring
      rw [hns_log] at hL_diff
      let f0 : ℝ := Int.fract (y₀ + (s : ℝ) / (2 * K))
      have hf0_lo : (2 * (b : ℝ) + 1) / (2 * K) ≤ f0 := hs_lo
      have hf0_hi : f0 < (2 * (b : ℝ) + 2) / (2 * K) := hs_hi
      have hfδ_lo : (b : ℝ) / K ≤ f0 + δ := by
        have : (2 * (b : ℝ) + 1) / (2 * K) - 1 / (2 * (K : ℝ)) = (b : ℝ) / K := by
          field_simp [hK_pos.ne']; ring
        linarith
      have hfδ_hi : f0 + δ < ((b : ℝ) + 1) / K := by
        have : (2 * (b : ℝ) + 2) / (2 * K) = ((b : ℝ) + 1) / K := by
          field_simp [hK_pos.ne']
        linarith
      have hfδ_Ico : f0 + δ ∈ Ico (0 : ℝ) 1 := by
        refine ⟨le_trans (by positivity) hfδ_lo, lt_of_lt_of_le hfδ_hi ?_⟩
        rw [div_le_one hK_pos]
        exact_mod_cast b.isLt
      have hfr_eq : Int.fract (L_log (m + v_exp k)) = f0 + δ := by
        have hdecomp : L_log (m + v_exp k) =
            (f0 + δ) + (⌊y₀ + (s : ℝ) / (2 * K)⌋ : ℝ) := by
          rw [hL_diff]
          dsimp [f0]
          linarith [Int.fract_add_floor (y₀ + (s : ℝ) / (2 * K))]
        rw [hdecomp, Int.fract_add_intCast, Int.fract_eq_self.mpr hfδ_Ico]
      rw [hfr_eq]
      exact ⟨hfδ_lo, hfδ_hi⟩
    exact mem_biUnion h_in_Eb h_in_lvl
  unfold visitAverage
  rw [le_div_iff₀ (Nat.cast_pos.mpr hn_pos)]
  have hsub_Icc : Finset.Icc k_lo n ⊆ Finset.Icc 1 n := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    exact ⟨hk_lo_pos.trans hk.1, hk.2⟩
  have hsum_ge : ((Finset.Icc k_lo n).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 n, if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0 := by
    calc ((Finset.Icc k_lo n).card : ℝ)
      _ = ∑ _k ∈ Finset.Icc k_lo n, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ k ∈ Finset.Icc k_lo n, if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [if_pos (hk_hit k hk)]
      _ ≤ ∑ k ∈ Finset.Icc 1 n, if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub_Icc fun k _ _ => ?_
          split_ifs <;> norm_num
  have hcard_ge : (1 / 2 : ℝ) * (n : ℝ) ≤ ((Finset.Icc k_lo n).card : ℝ) := by
    rw [Nat.card_Icc]
    have hcard_nat : n + 1 - k_lo = k_lo + 1 := by omega
    rw [hcard_nat, hn_eq]
    push_cast
    linarith
  linarith

end Erdos994H1

theorem OMA.solution : OMA.R_Erdos994_erdos_994_R1.H1 := Erdos994H1.h1_proof
