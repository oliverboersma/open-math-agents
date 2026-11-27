import FormalConjectures.ErdosProblems.«186»
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! From the divisor and interval theorems of Bringmann and Wellnitz, arXiv:2010.09096, Theorems 4.1 and 4.2, and the common-subsums argument of Erdős and Sárközy, On a Problem of Straus, sections 2 and 3. -/

open Finset
namespace OMA.R_Erdos186_erdos_186_variants_erdos_sarkozy_R1
lemma left_card (A : Finset ℕ) (a : ℕ) :
    (((A.filter fun x => x < a).image fun x => a - x)).card = (A.filter fun x => x < a).card := by
  apply card_image_iff.mpr
  intro x hx y hy he
  have hx' := (mem_filter.mp hx).2
  have hy' := (mem_filter.mp hy).2
  dsimp at he
  omega

lemma right_card (A : Finset ℕ) (a : ℕ) :
    (((A.filter fun x => a < x).image fun x => x - a)).card = (A.filter fun x => a < x).card := by
  apply card_image_iff.mpr
  intro x hx y hy he
  have hx' := (mem_filter.mp hx).2
  have hy' := (mem_filter.mp hy).2
  dsimp at he
  omega

lemma left_in_bounds {A : Finset ℕ} {N a : ℕ} (ha : a ∈ A)
    (hA : A ⊆ Icc 1 N) : ((A.filter fun x => x < a).image fun x => a - x) ⊆ Icc 1 N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
  have h := (mem_filter.mp hy).2
  have haN := (mem_Icc.mp (hA ha)).2
  exact mem_Icc.mpr ⟨by omega, by omega⟩

lemma right_in_bounds {A : Finset ℕ} {N a : ℕ}
    (hA : A ⊆ Icc 1 N) : ((A.filter fun x => a < x).image fun x => x - a) ⊆ Icc 1 N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
  have h := (mem_filter.mp hy).2
  have hyN := (mem_Icc.mp (hA (mem_filter.mp hy).1)).2
  exact mem_Icc.mpr ⟨by omega, by omega⟩

-- Equal subsums of distances below and above a would give a nonempty subset with average a.
lemma no_common_sum {A : Finset ℕ} {a : ℕ} (ha : a ∈ A)
    (hna : Erdos186.NonAveraging A)
    {U V : Finset ℕ} (hU : U ⊆ ((A.filter fun x => x < a).image fun x => a - x)) (hV : V ⊆ ((A.filter fun x => a < x).image fun x => x - a))
    (hUn : U.Nonempty) (hVn : V.Nonempty) :
    (∑ u ∈ U, u) ≠ ∑ v ∈ V, v := by
  classical
  intro he
  let L := U.image fun u => a - u
  let R := V.image fun v => a + v
  have hUprops (u : ℕ) (hu : u ∈ U) : 0 < u ∧ u ≤ a ∧ a - u ∈ A := by
    obtain ⟨x, hx, hxu⟩ := mem_image.mp (hU hu)
    obtain ⟨hxA, hxa⟩ := mem_filter.mp hx
    refine ⟨by omega, by omega, ?_⟩
    have : a - u = x := by omega
    rwa [this]
  have hVprops (v : ℕ) (hv : v ∈ V) : 0 < v ∧ a + v ∈ A := by
    obtain ⟨x, hx, hxv⟩ := mem_image.mp (hV hv)
    obtain ⟨hxA, hxa⟩ := mem_filter.mp hx
    refine ⟨by omega, ?_⟩
    have : a + v = x := by omega
    rwa [this]
  have hLinj : Set.InjOn (fun u : ℕ => a - u) (↑U : Set ℕ) := by
    intro u hu u' hu' h
    have h1 := (hUprops u hu).2.1
    have h2 := (hUprops u' hu').2.1
    dsimp at h
    omega
  have hRinj : Set.InjOn (fun v : ℕ => a + v) (↑V : Set ℕ) := by
    intro v _ v' _ h
    dsimp at h
    omega
  have hLa : L ⊆ A.erase a := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨hpos, hle, hmem⟩ := hUprops u hu
    exact mem_erase.mpr ⟨by omega, hmem⟩
  have hRa : R ⊆ A.erase a := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    obtain ⟨hpos, hmem⟩ := hVprops v hv
    exact mem_erase.mpr ⟨by omega, hmem⟩
  have hdis : Disjoint L R := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, hu, hux⟩ := mem_image.mp hx
    obtain ⟨v, hv, hvx⟩ := mem_image.mp hy
    have hpos := (hVprops v hv).1
    omega
  have hLc : L.card = U.card := card_image_iff.mpr hLinj
  have hRc : R.card = V.card := card_image_iff.mpr hRinj
  have hpU := card_pos.mpr hUn
  have hpV := card_pos.mpr hVn
  have hcard : (L ∪ R).card = U.card + V.card := by
    rw [card_union_of_disjoint hdis, hLc, hRc]
  apply hna a ha (L ∪ R) (union_subset hLa hRa) (by omega)
  rw [sum_union hdis, hcard]
  have hls : (∑ x ∈ L, (x : ℤ)) = (U.card : ℤ) * a - ∑ u ∈ U, (u : ℤ) := by
    dsimp [L]
    rw [sum_image hLinj]
    calc
      _ = ∑ u ∈ U, ((a : ℤ) - (u : ℤ)) :=
        sum_congr rfl fun u hu => Int.ofNat_sub (hUprops u hu).2.1
      _ = _ := by rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hrs : (∑ x ∈ R, (x : ℤ)) = (V.card : ℤ) * a + ∑ v ∈ V, (v : ℤ) := by
    dsimp [R]
    rw [sum_image hRinj]
    calc
      _ = ∑ v ∈ V, ((a : ℤ) + (v : ℤ)) :=
        sum_congr rfl fun v _ => Nat.cast_add a v
      _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  have he' : (∑ u ∈ U, (u : ℤ)) = ∑ v ∈ V, (v : ℤ) := by
    exact (Nat.cast_sum (R := ℤ) U (fun n => n)).symm.trans
      ((congrArg (fun n : ℕ => (n : ℤ)) he).trans (Nat.cast_sum (R := ℤ) V (fun n => n)))
  have goal : (∑ x ∈ L, (x : ℤ)) + (∑ x ∈ R, (x : ℤ)) = ((U.card : ℤ) + V.card) * a := by
    rw [hls, hrs, he']
    ring
  apply Nat.cast_injective (R := ℤ)
  simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul] using goal


lemma median_distances (A : Finset ℕ) (hc : 0 < A.card) :
    ∃ a ∈ A, (A.card - 1) / 2 ≤ (((A.filter fun x => x < a).image fun x => a - x)).card ∧
      (A.card - 1) / 2 ≤ (((A.filter fun x => a < x).image fun x => x - a)).card := by
  classical
  let k := (A.card - 1) / 2
  let a := A.orderEmbOfFin rfl ⟨k, by dsimp [k]; omega⟩
  refine ⟨a, A.orderEmbOfFin_mem rfl _, ?_, ?_⟩
  · rw [left_card]
    let f : Fin k → ℕ := fun i => A.orderEmbOfFin rfl ⟨i, by have := i.isLt; dsimp [k] at *; omega⟩
    have hi : Function.Injective f := by
      intro i j h
      have hh := (A.orderEmbOfFin rfl).injective h
      exact Fin.ext (congrArg (fun i : Fin A.card => i.val) hh)
    have hs : Finset.univ.image f ⊆ A.filter (fun x => x < a) := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      apply mem_filter.mpr
      refine ⟨A.orderEmbOfFin_mem rfl _, ?_⟩
      exact (A.orderEmbOfFin rfl).strictMono i.isLt
    have hh := card_le_card hs
    simpa [card_image_of_injective _ hi] using hh
  · rw [right_card]
    let f : Fin k → ℕ := fun i => A.orderEmbOfFin rfl ⟨k+1+i, by have := i.isLt; dsimp [k] at *; omega⟩
    have hi : Function.Injective f := by
      intro i j h
      have hh := congrArg Fin.val ((A.orderEmbOfFin rfl).injective h)
      apply Fin.ext
      dsimp at hh
      omega
    have hs : Finset.univ.image f ⊆ A.filter (fun x => a < x) := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      apply mem_filter.mpr
      refine ⟨A.orderEmbOfFin_mem rfl _, ?_⟩
      apply (A.orderEmbOfFin rfl).strictMono
      change k < k + 1 + i.val
      omega
    have hh := card_le_card hs
    simpa [card_image_of_injective _ hi] using hh



open Filter Topology Real

theorem upper_of_commonBound (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ∀ A B : Finset ℕ, A ⊆ Icc 1 N → B ⊆ Icc 1 N →
      C * Real.sqrt (N * Real.log N) < (A.card : ℝ) →
      C * Real.sqrt (N * Real.log N) < (B.card : ℝ) →
      ∃ S ⊆ A, ∃ T ⊆ B, S.Nonempty ∧ T.Nonempty ∧ (∑ x ∈ S, x) = ∑ x ∈ T, x) :
    type_of% @Erdos186.erdos_186.variants.erdos_sarkozy := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨2*C+2, by linarith, ?_⟩
  have hlarge : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.sqrt (N * Real.log N) := by
    have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with N hn hl
    have hn' : (1 : ℝ) ≤ N := by exact_mod_cast hn
    apply (Real.le_sqrt (by positivity) (mul_nonneg (by positivity) (by linarith))).mpr
    calc
      (1 : ℝ)^2 = 1*1 := by norm_num
      _ ≤ N * Real.log N := mul_le_mul hn' hl (by norm_num) (by positivity)
  filter_upwards [h, hlarge] with N hN hroot
  rw [Erdos186.F]
  have aux (A : Finset ℕ) (hA : A ⊆ Icc 1 N) (hna : Erdos186.NonAveraging A) :
      (A.card : ℝ) ≤ (2 * C + 2) * Real.sqrt ((N : ℝ) * Real.log N) := by
    by_cases hc : 0 < A.card
    · obtain ⟨a, ha, hl, hr⟩ := median_distances A hc
      let k := (A.card - 1) / 2
      have hk : (k : ℝ) ≤ C * Real.sqrt (N * Real.log N) := by
        by_contra! hk
        have hl' : (k : ℝ) ≤ ((((A.filter fun x => x < a).image fun x => a - x)).card : ℝ) := by exact_mod_cast hl
        have hr' : (k : ℝ) ≤ ((((A.filter fun x => a < x).image fun x => x - a)).card : ℝ) := by exact_mod_cast hr
        obtain ⟨S, hs, T, ht, hsn, htn, hst⟩ :=
          hN _ _ (left_in_bounds ha hA) (right_in_bounds hA) (hk.trans_le hl') (hk.trans_le hr')
        exact no_common_sum ha hna hs ht hsn htn hst
      have hc' : (A.card : ℝ) ≤ 2 * (k : ℝ) + 2 := by
        exact_mod_cast (show A.card ≤ 2*k+2 by dsimp [k]; omega)
      linarith
    · have hzero : A.card = 0 := by omega
      rw [hzero, Nat.cast_zero]
      positivity
  let s := (Icc 1 N).powerset.filter Erdos186.NonAveraging
  change ((s.sup Finset.card : ℕ) : ℝ) ≤ _
  -- Finish by a maximal member, or the empty default.
  by_cases hne : s.Nonempty
  · obtain ⟨A, hAs, heq⟩ := Finset.exists_mem_eq_sup s hne Finset.card
    rw [heq]
    exact aux A (mem_powerset.mp (mem_filter.mp hAs).1) (mem_filter.mp hAs).2
  · have hz : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero]
    positivity


open Finset

lemma exists_dvd_subset {d : ℕ} (hd : 0 < d) {B : Finset ℕ} (hB : d ≤ B.card) :
    ∃ S ⊆ B, S.Nonempty ∧ S.card ≤ d ∧ d ∣ ∑ x ∈ S, x := by
  classical
  letI : NeZero d := ⟨by omega⟩
  let e : Fin d ↪ ℕ := (B.orderEmbOfCardLe hB).toEmbedding
  let T (i : Fin (d + 1)) : Finset (Fin d) := univ.filter fun j => j.val < i.val
  let F (i : Fin (d + 1)) : ZMod d := ∑ j ∈ T i, (e j : ZMod d)
  have hf : ¬Function.Injective F := by
    intro hinj
    have hc := Fintype.card_le_of_injective F hinj
    rw [Fintype.card_fin, ZMod.card] at hc
    omega
  unfold Function.Injective at hf
  push Not at hf
  obtain ⟨i, j, he, hij⟩ := hf
  have get (i j : Fin (d+1)) (hlt : i < j) (he : F i = F j) :
      ∃ S ⊆ B, S.Nonempty ∧ S.card ≤ d ∧ d ∣ ∑ x ∈ S, x := by
    let R := T j \ T i
    let S := R.map e
    have hs : T i ⊆ T j := by
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hx).2).trans hlt⟩
    have hi : i.val < d := by have hj := j.isLt; change i.val < j.val at hlt; omega
    have hr : R.Nonempty := by
      refine ⟨⟨i.val, hi⟩, mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hlt⟩, ?_⟩⟩
      exact fun h => (Nat.lt_irrefl i.val) (mem_filter.mp h).2
    refine ⟨S, ?_, hr.map, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, _, rfl⟩ := mem_map.mp hx
      exact B.orderEmbOfCardLe_mem hB y
    · rw [card_map]
      simpa using (card_le_univ R)
    · have hz : (∑ x ∈ R, (e x : ZMod d)) = 0 := by
        have hh := sum_sdiff (f := fun x : Fin d => (e x : ZMod d)) hs
        change (∑ x ∈ R, (e x : ZMod d)) + F i = F j at hh
        rw [← he] at hh
        exact add_right_cancel (hh.trans (zero_add _).symm)
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_sum, sum_map]
      exact hz
  rcases lt_or_gt_of_ne hij with h | h
  · exact get i j h he
  · exact get j i h he.symm

lemma grid_hit {M N d u : ℕ} {B : Finset ℕ}
    (hM : 0 < M) (hd : 0 < d) (hu : 0 < u)
    (hB : B ⊆ Icc M N) (hbnd : u ≤ M * (B.card - d)) :
    ∃ S ⊆ B, S.Nonempty ∧ u ≤ ∑ x ∈ S, x ∧ (∑ x ∈ S, x) < u + N*d ∧
      d ∣ ∑ x ∈ S, x := by
  classical
  let good := B.powerset.filter fun S => (∑ x ∈ S, x) < u ∧ d ∣ ∑ x ∈ S, x
  let values := good.image fun S => ∑ x ∈ S, x
  have hempty : ∅ ∈ good := by simp [good, hu]
  have hval : values.Nonempty := ⟨0, mem_image.mpr ⟨∅, hempty, by simp⟩⟩
  obtain ⟨L, hL, heq⟩ := mem_image.mp (max'_mem values hval)
  have hgood := (mem_filter.mp hL).2
  have hLB : L ⊆ B := mem_powerset.mp (mem_filter.mp hL).1
  have hcardL : L.card < B.card - d := by
    have helper : L.card * M ≤ ∑ x ∈ L, x := by
      rw [← Nat.nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun x hx => (mem_Icc.mp (hB (hLB hx))).1
    have help : M * L.card < M * (B.card - d) :=
      lt_of_lt_of_le (lt_of_le_of_lt (by simpa only [Nat.mul_comm M] using helper) hgood.1) hbnd
    exact Nat.lt_of_mul_lt_mul_left help
  have hdrem : d ≤ (B \ L).card := by
    rw [card_sdiff_of_subset hLB]
    omega
  obtain ⟨R, hR, hRn, hRc, hRd⟩ := exists_dvd_subset hd hdrem
  have hRB : R ⊆ B := fun x hx => (mem_sdiff.mp (hR hx)).1
  have hdis : Disjoint L R := disjoint_left.mpr fun x hx hy => (mem_sdiff.mp (hR hy)).2 hx
  have hnd : d ∣ ∑ x ∈ L ∪ R, x := by rw [sum_union hdis]; exact dvd_add hgood.2 hRd
  have hsumpos : 0 < ∑ x ∈ R, x := by
    apply sum_pos (fun x hx => hM.trans_le (mem_Icc.mp (hB (hRB hx))).1) hRn
  have hsumupper : (∑ x ∈ R, x) ≤ N * d := by
    calc
      _ ≤ ∑ _x ∈ R, N := sum_le_sum fun x hx => (mem_Icc.mp (hB (hRB hx))).2
      _ ≤ _ := by rw [sum_const, Nat.nsmul_eq_mul, Nat.mul_comm R.card]; exact Nat.mul_le_mul_left _ hRc
  have hS : L ∪ R ⊆ B := union_subset hLB hRB
  have hhit : u ≤ ∑ x ∈ L ∪ R, x := by
    by_contra! hbad
    have hmg : L ∪ R ∈ good := mem_filter.mpr ⟨mem_powerset.mpr hS, hbad, hnd⟩
    have hmv : (∑ x ∈ L ∪ R, x) ∈ values := mem_image.mpr ⟨_, hmg, rfl⟩
    have hle := le_max' values _ hmv
    rw [← heq, sum_union hdis] at hle
    omega
  refine ⟨L ∪ R, hS, ?_, hhit, ?_, hnd⟩
  · obtain ⟨x, hx⟩ := hRn
    exact ⟨x, mem_union_right _ hx⟩
  · rw [sum_union hdis]
    omega

lemma progression_overlap {M N d y z : ℕ} {A B : Finset ℕ}
    (hM : 0 < M) (hd : 0 < d) (hy : 0 < y)
    (hB : B ⊆ Icc M N) (hspan : y + N ≤ z) (hbudget : y*d ≤ M*(B.card-d))
    (hprog : ∀ j, y ≤ j → j ≤ z → ∃ S ⊆ A, S.Nonempty ∧ (∑ x ∈ S, x) = j*d) :
    ∃ S ⊆ A, ∃ T ⊆ B, S.Nonempty ∧ T.Nonempty ∧ (∑ x ∈ S, x) = ∑ x ∈ T, x := by
  obtain ⟨T, hTB, hTn, hlo, hhi, j, hj⟩ := grid_hit hM hd (Nat.mul_pos hy hd) hB hbudget
  have hmul : (∑ x ∈ T, x) = j*d := hj.trans (Nat.mul_comm d j)
  rw [hmul] at hlo hhi
  have h1 : y ≤ j := Nat.le_of_mul_le_mul_right hlo hd
  have h2 : j < y + N := by
    apply Nat.lt_of_mul_lt_mul_right
    rw [Nat.add_mul]
    exact hhi
  obtain ⟨S, hSA, hSn, hSj⟩ := hprog j h1 (h2.le.trans hspan)
  exact ⟨S, hSA, T, hTB, hSn, hTn, hSj.trans hmul.symm⟩


open Finset

lemma order_index_lower {k : ℕ} (f : Fin k ↪o ℕ) (hA : ∀ i, 0 < f i) (i : Fin k) :
    i.val+1 ≤ f i := by
  cases k with
  | zero => exact i.elim0
  | succ k =>
    induction i using Fin.induction with
    | zero => exact hA _
    | succ i ih =>
      exact (Nat.add_le_add_right ih 1).trans
        (f.strictMono (show i.castSucc < i.succ by exact Nat.lt_succ_self _))

lemma card_sq_le_two_sum {A : Finset ℕ} (hA : ∀ n ∈ A, 0<n) :
    A.card*A.card ≤ 2*(∑ x ∈ A, x) := by
  classical
  let e : Fin A.card ↪ ℕ := (A.orderEmbOfFin rfl).toEmbedding
  have hEq : univ.map e = A := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := mem_map.mp hx
      exact A.orderEmbOfFin_mem rfl _
    · rw [card_map, card_univ, Fintype.card_fin]
  have hsum : (∑ i : Fin A.card, (i.val+1)) ≤ ∑ x ∈ A, x := by
    calc
      _ ≤ ∑ i : Fin A.card, e i := by
        exact sum_le_sum (fun i _ => order_index_lower (A.orderEmbOfFin rfl)
          (fun j => hA _ (A.orderEmbOfFin_mem rfl j)) i)
      _ = ∑ x ∈ univ.map e, x := (sum_map univ e (fun x => x)).symm
      _ = _ := congrArg (fun S : Finset ℕ => ∑ x ∈ S, x) hEq
  have ha := sum_range_id_mul_two A.card
  rw [Fin.sum_univ_eq_sum_range fun i => i+1, sum_add_distrib, sum_const, Nat.nsmul_eq_mul,
    card_range, Nat.mul_one] at hsum
  cases hcard : A.card with
  | zero => omega
  | succ n =>
    rw [hcard, Nat.succ_sub_one] at ha
    rw [hcard] at hsum
    nlinarith

lemma sum_le_card_mul {L : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 L) :
    (∑ x ∈ A, x) ≤ A.card * L := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun x hx => (mem_Icc.mp (hA hx)).2



lemma scaled_interval_parameters {N M k n d L T : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N) (hn : 0 < n)
    (hdL : d*L ≤ M) (hL : L ≤ M) (hnU : n ≤ k) (hkU : k ≤ 2*n)
    (hd : d*k ≤ 4*M) (hlarge : 4000000*N ≤ k*k)
    (hSum1 : n*n ≤ 2*T) (hSum2 : T ≤ n*L) :
    ∃ y z : ℕ, 0 < y ∧ y+N ≤ z ∧ y*d ≤ M*(k-d) ∧
      ∀ j : ℕ, y ≤ j → j ≤ z → 200000*L*T ≤ j*(n*n) ∧ 2*j ≤ T := by
  let q := n*n
  let g := 200000*L*T
  let y := g/q+1
  have hq : 0 < q := Nat.mul_pos hn hn
  have hyq : y*q ≤ g+q := by
    dsimp [y]
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have hgq : g ≤ y*q := by
    dsimp [y]
    have hh := Nat.mod_add_div g q
    have hm := Nat.mod_lt g hq
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (g/q)]
    omega
  have hsq : k*k ≤ 4*q := by
    calc
      _ ≤ (2*n)*(2*n) := Nat.mul_le_mul hkU hkU
      _ = _ := by dsimp [q]; ring
  have h4L : 800000*L ≤ q := by
    have hLM := hL.trans hMN
    have hbig := Nat.mul_le_mul_left 4000000 hLM
    omega
  have hSpan1 : 4*y ≤ T+4 := by
    have hh : (4*y)*q ≤ (T+4)*q := by
      calc
        _ = 4*(y*q) := by ring
        _ ≤ 4*(g+q) := Nat.mul_le_mul_left _ hyq
        _ = (800000*L)*T + 4*q := by dsimp [g]; ring
        _ ≤ q*T + 4*q := Nat.add_le_add_right (Nat.mul_le_mul_right T h4L) _
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right hh hq
  have hSpan2 : 4*N+8 ≤ T := by
    change k*k ≤ 4*(n*n) at hsq
    omega
  have hy_n : y*n ≤ 200000*L*L+n := by
    have hbound : (y*n)*n ≤ (200000*L*L+n)*n := by
      calc
        _ = y*q := by dsimp [q]; ring
        _ ≤ g+q := hyq
        _ ≤ 200000*L*(n*L)+q := Nat.add_le_add_right (Nat.mul_le_mul_left _ hSum2) _
        _ = _ := by dsimp [q]; ring
    exact Nat.le_of_mul_le_mul_right hbound hn
  have hy_budget : y*d*k ≤ 400008*M*M := by
    have hMy : d*L*L ≤ M*M := Nat.mul_le_mul hdL hL
    have hd' : d*n ≤ 4*M := (Nat.mul_le_mul_left d hnU).trans hd
    have hmm : M ≤ M*M := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left M hM
    calc
      _ ≤ y*d*(2*n) := Nat.mul_le_mul_left _ hkU
      _ = 2*d*(y*n) := by ring
      _ ≤ 2*d*(200000*L*L+n) := Nat.mul_le_mul_left _ hy_n
      _ = 400000*(d*L*L)+2*(d*n) := by ring
      _ ≤ 400000*(M*M)+2*(4*M) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hMy) (Nat.mul_le_mul_left _ hd')
      _ ≤ 400000*(M*M)+8*(M*M) := by
        have hh := Nat.mul_le_mul_left 8 hmm
        omega
      _ = _ := by ring
  have hb : (y*d+M*d)*k ≤ (M*k)*k := by
    calc
      _ = y*d*k+M*(d*k) := by ring
      _ ≤ 400008*M*M+M*(4*M) := Nat.add_le_add hy_budget (Nat.mul_le_mul_left M hd)
      _ = M*(400012*M) := by ring
      _ ≤ M*(k*k) := Nat.mul_le_mul_left M (by
        have hh := Nat.mul_le_mul_left 4000000 hMN
        omega)
      _ = _ := by ring
  have hk : 0 < k := hn.trans_le hnU
  have hb' := Nat.le_of_mul_le_mul_right hb hk
  have hdk : d ≤ k := by
    by_contra! hc
    have hh := Nat.mul_lt_mul_of_pos_left hc hM
    omega
  have hbe : M*(k-d)+M*d = M*k := by rw [← Nat.mul_add, Nat.sub_add_cancel hdk]
  have hyp : 0 < y := Nat.succ_pos _
  refine ⟨y,T/2,hyp,by omega,by omega,?_⟩
  intro j hj htop
  exact ⟨hgq.trans (Nat.mul_le_mul_right _ hj), by omega⟩


open Finset

lemma ordered_halves {k N : ℕ} {A B : Finset ℕ} (hk : 0 < k)
    (hA : A ⊆ Icc 1 N) (hB : B ⊆ Icc 1 N)
    (hAk : 2*k ≤ A.card) (hBk : 2*k ≤ B.card) :
    ∃ M ≤ N, 0 < M ∧ ∃ U V : Finset ℕ, U.card = k ∧ V.card = k ∧
      U ⊆ Icc 1 M ∧ V ⊆ Icc M N ∧
      ((U ⊆ A ∧ V ⊆ B) ∨ (U ⊆ B ∧ V ⊆ A)) := by
  classical
  suffices oriented : ∀ (P Q : Finset ℕ), P ⊆ Icc 1 N → Q ⊆ Icc 1 N →
      ∀ (hp : 2*k ≤ P.card) (hq : 2*k ≤ Q.card),
      P.orderEmbOfFin rfl ⟨k, by omega⟩ ≤ Q.orderEmbOfFin rfl ⟨k, by omega⟩ →
      ∃ M ≤ N, 0 < M ∧ ∃ U V : Finset ℕ, U.card = k ∧ V.card = k ∧
        U ⊆ Icc 1 M ∧ V ⊆ Icc M N ∧ U ⊆ P ∧ V ⊆ Q by
    rcases le_total (A.orderEmbOfFin rfl ⟨k, by omega⟩)
        (B.orderEmbOfFin rfl ⟨k, by omega⟩) with h | h
    · obtain ⟨M, hMN, hM0, U, V, hUc, hVc, hUM, hVM, hUA, hVB⟩ := oriented A B hA hB hAk hBk h
      exact ⟨M, hMN, hM0, U, V, hUc, hVc, hUM, hVM, Or.inl ⟨hUA, hVB⟩⟩
    · obtain ⟨M, hMN, hM0, U, V, hUc, hVc, hUM, hVM, hUB, hVA⟩ := oriented B A hB hA hBk hAk h
      exact ⟨M, hMN, hM0, U, V, hUc, hVc, hUM, hVM, Or.inr ⟨hUB, hVA⟩⟩
  intro P Q hP hQ hp hq hPQ
  let M := P.orderEmbOfFin rfl ⟨k, by omega⟩
  let f : Fin k → ℕ := fun i => P.orderEmbOfFin rfl ⟨i.val, by have := i.isLt; omega⟩
  let g : Fin k → ℕ := fun i => Q.orderEmbOfFin rfl ⟨k+i.val, by have := i.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg (fun v : Fin P.card => v.val) ((P.orderEmbOfFin rfl).injective hij))
  have hg : Function.Injective g := by
    intro i j hij
    have hh := congrArg (fun v : Fin Q.card => v.val) ((Q.orderEmbOfFin rfl).injective hij)
    apply Fin.ext
    change k+i.val = k+j.val at hh
    omega
  let U := univ.image f
  let V := univ.image g
  have hU : U ⊆ P := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := mem_image.mp hu
    exact P.orderEmbOfFin_mem rfl _
  have hV : V ⊆ Q := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact Q.orderEmbOfFin_mem rfl _
  have hMem : M ∈ Icc 1 N := hP (P.orderEmbOfFin_mem rfl _)
  refine ⟨M, (mem_Icc.mp hMem).2, (mem_Icc.mp hMem).1, U, V, ?_, ?_, ?_, ?_, hU, hV⟩
  · dsimp [U]
    rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
  · dsimp [V]
    rw [card_image_of_injective _ hg, card_univ, Fintype.card_fin]
  · intro u hu
    have h1 := (mem_Icc.mp (hP (hU hu))).1
    obtain ⟨i, _, rfl⟩ := mem_image.mp hu
    exact mem_Icc.mpr ⟨h1, (P.orderEmbOfFin rfl).monotone i.isLt.le⟩
  · intro v hv
    have h2 := (mem_Icc.mp (hQ (hV hv))).2
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    refine mem_Icc.mpr ⟨hPQ.trans ((Q.orderEmbOfFin rfl).monotone ?_), h2⟩
    change k ≤ k+i.val
    omega


open Filter Topology Real

/-- Divisor extraction for dense finite sets. The parameter grows only logarithmically
    in the original cardinality, and is preserved under taking and scaling multiples. -/
def H1 : Prop :=
  ∀ (M : ℕ) (U : Finset ℕ), U.Nonempty → U ⊆ Icc 1 M →
    2000000 * (1 + Real.log (2 * (U.card : ℝ))) * M ≤ (U.card : ℝ)^2 →
    ∃ d L : ℕ, ∃ W : Finset ℕ, 0 < d ∧ 0 < L ∧ W.Nonempty ∧
      d*L ≤ M ∧ d*U.card ≤ 4*M ∧ W.card ≤ U.card ∧ U.card ≤ 2*W.card ∧
      W ⊆ Icc 1 L ∧ (∀ w ∈ W, d*w ∈ U) ∧
      2000000 * (1 + Real.log (2 * (U.card : ℝ))) * L ≤ (W.card : ℝ)^2 ∧
      ∀ r : ℕ, 1 < r → 42480*(∑ w ∈ W, w) <
        (W.filter fun w => ¬ r ∣ w).card * W.card * W.card

/-- Dense sets with no almost divisor have an interval of subset sums up to their midpoint. -/
def H2 : Prop :=
  ∀ (L : ℕ) (W : Finset ℕ), W.Nonempty → W ⊆ Icc 1 L →
    2000000 * (1 + Real.log (2 * (W.card : ℝ))) * L ≤ (W.card : ℝ)^2 →
    (∀ r : ℕ, 1 < r → 42480*(∑ w ∈ W, w) <
      (W.filter fun w => ¬ r ∣ w).card * W.card * W.card) →
    ∀ j : ℕ, 200000 * L * (∑ w ∈ W, w) ≤ j*(W.card*W.card) →
      2*j ≤ ∑ w ∈ W, w → ∃ S ⊆ W, (∑ w ∈ S, w) = j

lemma common_of_halves (extract : H1) (fill : H2)
    {M N k : ℕ} {U V : Finset ℕ} (hM0 : 0 < M) (hMN : M ≤ N)
    (hUc : U.card = k) (hVc : V.card = k) (hk0 : 0 < k) (hUk : U ⊆ Icc 1 M) (hVk : V ⊆ Icc M N)
    (hbig : 4000000*N ≤ k*k)
    (hdense : 2000000 * (1 + Real.log (2 * (k : ℝ))) * M ≤ (k : ℝ)^2) :
    ∃ S ⊆ U, ∃ T ⊆ V, S.Nonempty ∧ T.Nonempty ∧ (∑ x ∈ S, x) = ∑ x ∈ T, x := by
  classical
  have hUn : U.Nonempty := card_pos.mp (hUc ▸ hk0)
  obtain ⟨d,L,W,hd,hL,hWn,hdL,hdU,hnU,hUn',hW,hWU,hden,hfree⟩ :=
    extract M U hUn hUk (by simpa only [hUc] using hdense)
  have hn : 0 < W.card := card_pos.mpr hWn
  have hL' : L ≤ M := (by
    calc
      L = 1*L := (Nat.one_mul _).symm
      _ ≤ d*L := Nat.mul_le_mul_right _ hd
      _ ≤ M := hdL)
  have hWden : 2000000 * (1 + Real.log (2 * (W.card : ℝ))) * L ≤ (W.card : ℝ)^2 := by
    have hcard : (W.card : ℝ) ≤ U.card := by exact_mod_cast hnU
    have hcpos : (0 : ℝ) < W.card := by exact_mod_cast hn
    have hlog : Real.log (2 * (W.card : ℝ)) ≤ Real.log (2 * (U.card : ℝ)) :=
      Real.log_le_log (mul_pos (by norm_num) hcpos) (mul_le_mul_of_nonneg_left hcard (by norm_num))
    have ha : (1 : ℝ) + Real.log (2 * (W.card : ℝ)) ≤ 1 + Real.log (2 * (U.card : ℝ)) := by linarith
    apply le_trans _ hden
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ha (by norm_num)) (by positivity)
  have hT1 := card_sq_le_two_sum (A := W) (fun w hw => (mem_Icc.mp (hW hw)).1)
  have hT2 := sum_le_card_mul hW
  have hNk : 0 < N := hM0.trans_le hMN
  obtain ⟨y,z,hy,hspan,hbudget,hinterval⟩ := scaled_interval_parameters hNk hM0 hMN hn hdL hL'
    (by simpa only [hUc] using hnU) (by simpa only [hUc] using hUn')
    (by simpa only [hUc] using hdU) hbig hT1 hT2
  rw [← hVc] at hbudget
  apply progression_overlap hM0 hd hy hVk hspan hbudget
  intro j hj hb
  obtain ⟨hlo,hhi⟩ := hinterval j hj hb
  obtain ⟨S,hSW,hsum⟩ := fill L W hWn hW hWden hfree j hlo hhi
  have hnS : S.Nonempty := by
    by_contra! hnS
    rw [hnS, sum_empty] at hsum
    omega
  let dmul : ℕ ↪ ℕ := ⟨fun x => d*x, fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h⟩
  refine ⟨S.map dmul, ?_, hnS.map, ?_⟩
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hx
    exact hWU w (hSW hw)
  · rw [sum_map]
    change (∑ x ∈ S, d*x) = j*d
    rw [← mul_sum, hsum, Nat.mul_comm]
lemma common_of_bw (extract : H1) (fill : H2) : (∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ∀ A B : Finset ℕ, A ⊆ Icc 1 N → B ⊆ Icc 1 N →
      C * Real.sqrt (N * Real.log N) < (A.card : ℝ) →
      C * Real.sqrt (N * Real.log N) < (B.card : ℝ) →
      ∃ S ⊆ A, ∃ T ⊆ B, S.Nonempty ∧ T.Nonempty ∧ (∑ x ∈ S, x) = ∑ x ∈ T, x) := by
  let D : ℝ := 3000
  refine ⟨2*D + 2, by norm_num [D], ?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with N hN hlogN
  intro A B hA hB haa hbb
  let s := Real.sqrt ((N : ℝ)*Real.log N)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs2 : s^2 = (N : ℝ)*Real.log N :=
    Real.sq_sqrt (mul_nonneg (by positivity) (by linarith))
  have hs1 : 1 ≤ s := by
    apply (Real.le_sqrt (by positivity) (mul_nonneg (by positivity) (by linarith))).mpr
    calc
      (1 : ℝ)^2 = 1*1 := by norm_num
      _ ≤ (N : ℝ)*Real.log N := mul_le_mul hNreal hlogN (by norm_num) (by positivity)
  let k := (min A.card B.card) / 2
  have hmin : (min A.card B.card : ℝ) ≤ 2*(k : ℝ)+1 := by
    exact_mod_cast (show min A.card B.card ≤ 2*k+1 by dsimp [k]; omega)
  have hthr : (2*D+2)*s < (min A.card B.card : ℝ) := by
    exact lt_min_iff.mpr ⟨haa, hbb⟩
  have hkD : D*s ≤ (k : ℝ) := by nlinarith
  have hk : 0 < k := by
    have hr : (0 : ℝ) < k := lt_of_lt_of_le (mul_pos (by norm_num [D]) (by linarith)) hkD
    exact_mod_cast hr
  have hs2N : (N : ℝ) ≤ s^2 := by
    rw [hs2]
    conv_lhs => rw [← mul_one (N : ℝ)]
    gcongr
  have hbase : (9000000 : ℝ)*s^2 ≤ (k : ℝ)^2 := by
    calc
      _ = (D*s)^2 := by dsimp [D]; ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by norm_num [D]) (by linarith)) hkD _
  have hsq : 4000000*N ≤ k*k := by
    have h : (4000000 : ℝ)*N ≤ (k : ℝ)*(k : ℝ) := by
      calc
        _ ≤ 9000000 * s^2 := mul_le_mul (by norm_num) hs2N (by positivity) (by norm_num)
        _ ≤ _ := by simpa only [pow_two] using hbase
    exact_mod_cast h
  have hminL := Nat.min_le_left A.card B.card
  have hminR := Nat.min_le_right A.card B.card
  obtain ⟨M, hMN, hM, U, V, hUc, hVc, hUM, hVM, hor⟩ :=
    ordered_halves hk hA hB (by dsimp [k]; omega) (by dsimp [k]; omega)
  have hkM : k ≤ M := by
    have hd := card_le_card hUM
    rw [hUc, Nat.card_Icc] at hd
    omega
  have hkc : (k : ℝ) ≤ N := by exact_mod_cast hkM.trans hMN
  have hMc : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogs : Real.log (2*(k : ℝ)) ≤ 1 + Real.log N := by
    have h0 : Real.log (2*(k : ℝ)) ≤ Real.log (2*(N : ℝ)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hkc (by norm_num))
    rw [Real.log_mul (x := (2:ℝ)) (y := (N:ℝ)) (by norm_num) (by linarith)] at h0
    linarith
  have hden : 2000000 * (1 + Real.log (2*(k : ℝ))) * M ≤ (k : ℝ)^2 := by
    calc
      _ ≤ (6000000 * Real.log N) * N := by
        apply mul_le_mul _ hMc (by positivity) (mul_nonneg (by norm_num) (by linarith))
        linarith
      _ ≤ 9000000*s^2 := by rw [hs2]; nlinarith [mul_nonneg (show 0 ≤ (N:ℝ) by positivity) (show 0 ≤ Real.log N by linarith)]
      _ ≤ _ := hbase
  obtain ⟨S,hS,T,hT,hSn,hTn,hst⟩ :=
    common_of_halves extract fill hM hMN hUc hVc hk hUM hVM hsq hden
  rcases hor with ⟨hUA,hVB⟩ | ⟨hUB,hVA⟩
  · exact ⟨S,hS.trans hUA,T,hT.trans hVB,hSn,hTn,hst⟩
  · exact ⟨T,hT.trans hVA,S,hS.trans hUB,hTn,hSn,hst.symm⟩


theorem main : H1 → H2 → type_of% @Erdos186.erdos_186.variants.erdos_sarkozy := by
  intro he hf
  exact upper_of_commonBound (common_of_bw he hf)

end OMA.R_Erdos186_erdos_186_variants_erdos_sarkozy_R1
