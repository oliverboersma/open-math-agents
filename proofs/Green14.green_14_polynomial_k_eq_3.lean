import FormalConjectures.GreensOpenProblems.«14»
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace OMA.Hunter

open Finset BigOperators Filter Set Topology
open scoped Classical Matrix

/-! ## Section 1: Distance to integers and finite prime-grid embeddings -/

noncomputable def tdist (r : ℝ) : ℝ := |r - (round r : ℝ)|

lemma tdist_nonneg (r : ℝ) : 0 ≤ tdist r := abs_nonneg _

lemma tdist_le_half (r : ℝ) : tdist r ≤ 1 / 2 := abs_sub_round r

lemma tdist_le_abs_sub_int (r : ℝ) (m : ℤ) : tdist r ≤ |r - (m : ℝ)| := by
  unfold tdist
  by_cases h : round r = m
  · rw [h]
  · have h1 : (1 : ℤ) ≤ |round r - m| := by rw [le_abs]; omega
    have h2 : (1 : ℝ) ≤ |(round r : ℝ) - (m : ℝ)| := by exact_mod_cast h1
    have h3 : |r - (round r : ℝ)| ≤ 1 / 2 := abs_sub_round r
    have h4 : |(round r : ℝ) - (m : ℝ)| ≤ |r - (round r : ℝ)| + |r - (m : ℝ)| := by
      have eq : (round r : ℝ) - (m : ℝ) = ((round r : ℝ) - r) + (r - (m : ℝ)) := by ring
      rw [eq]
      calc |((round r : ℝ) - r) + (r - (m : ℝ))|
          ≤ |(round r : ℝ) - r| + |r - (m : ℝ)| := abs_add_le _ _
        _ = |r - (round r : ℝ)| + |r - (m : ℝ)| := by rw [abs_sub_comm]
    linarith

lemma tdist_le_abs (r : ℝ) : tdist r ≤ |r| := by
  simpa using tdist_le_abs_sub_int r 0

lemma tdist_add_int (r : ℝ) (m : ℤ) : tdist (r + (m : ℝ)) = tdist r := by
  apply le_antisymm
  · have h := tdist_le_abs_sub_int (r + (m : ℝ)) (round r + m)
    simpa [tdist, Int.cast_add, add_sub_add_right_eq_sub] using h
  · have h := tdist_le_abs_sub_int r (round (r + (m : ℝ)) - m)
    have eq : r - ((round (r + (m : ℝ)) - m : ℤ) : ℝ) =
        (r + (m : ℝ)) - (round (r + (m : ℝ)) : ℝ) := by push_cast; ring
    rw [eq] at h
    exact h

lemma tdist_eq_of_sub_int {x y : ℝ} (m : ℤ) (h : x - y = (m : ℝ)) : tdist x = tdist y := by
  have : x = y + (m : ℝ) := by linarith
  rw [this, tdist_add_int]

lemma tdist_neg (r : ℝ) : tdist (-r) = tdist r := by
  apply le_antisymm
  · have h := tdist_le_abs_sub_int (-r) (-round r)
    have eq : -r - ((-round r : ℤ) : ℝ) = -(r - (round r : ℝ)) := by push_cast; ring
    rw [eq, abs_neg] at h; exact h
  · have h := tdist_le_abs_sub_int r (-round (-r))
    have eq : r - ((-round (-r) : ℤ) : ℝ) = -(-r - (round (-r) : ℝ)) := by push_cast; ring
    rw [eq, abs_neg] at h; exact h

lemma tdist_add_le (x y : ℝ) : tdist (x + y) ≤ tdist x + tdist y := by
  have h := tdist_le_abs_sub_int (x + y) (round x + round y)
  have eq : x + y - ((round x + round y : ℤ) : ℝ) =
      (x - (round x : ℝ)) + (y - (round y : ℝ)) := by push_cast; ring
  rw [eq] at h
  exact h.trans (abs_add_le _ _)

lemma tdist_int_mul_le (n : ℤ) (x : ℝ) : tdist ((n : ℝ) * x) ≤ |(n : ℝ)| * tdist x := by
  have h := tdist_le_abs_sub_int ((n : ℝ) * x) (n * round x)
  have eq : (n : ℝ) * x - ((n * round x : ℤ) : ℝ) = (n : ℝ) * (x - (round x : ℝ)) := by
    push_cast; ring
  rw [eq, abs_mul] at h
  exact h

lemma tdist_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    tdist (∑ i ∈ s, f i) ≤ ∑ i ∈ s, tdist (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [tdist]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (tdist_add_le _ _).trans (add_le_add le_rfl ih)

lemma tdist_eq_abs_of_le_half {r : ℝ} (h : |r| ≤ 1 / 2) : tdist r = |r| := by
  apply le_antisymm (tdist_le_abs r)
  unfold tdist
  by_cases hr : round r = 0
  · simp [hr]
  · have h1 : (1 : ℤ) ≤ |round r| := by rw [le_abs]; omega
    have h2 : (1 : ℝ) ≤ |(round r : ℝ)| := by exact_mod_cast h1
    have h3 : |(round r : ℝ)| ≤ |r - (round r : ℝ)| + |r| := by
      have eq : (round r : ℝ) = ((round r : ℝ) - r) + r := by ring
      calc |(round r : ℝ)| = |((round r : ℝ) - r) + r| := by congr 1
        _ ≤ |(round r : ℝ) - r| + |r| := abs_add_le _ _
        _ = |r - (round r : ℝ)| + |r| := by rw [abs_sub_comm]
    linarith

lemma tdist_fract_lt_of_same_interval {a b c δ : ℝ}
    (ha1 : c ≤ Int.fract a) (ha2 : Int.fract a < c + δ)
    (hb1 : c ≤ Int.fract b) (hb2 : Int.fract b < c + δ) :
    tdist (a - b) < δ := by
  have hsub : (a - b) - (Int.fract a - Int.fract b) = ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) := by
    simp only [Int.fract, Int.cast_sub]; ring
  rw [tdist_eq_of_sub_int (⌊a⌋ - ⌊b⌋) hsub]
  refine (tdist_le_abs _).trans_lt ?_
  rw [abs_lt]; constructor <;> linarith

noncomputable def embed (P : ℕ) (a : ZMod P) : ℝ := (a.val : ℝ) / (P : ℝ)

lemma embed_intCast_sub {P : ℕ} [NeZero P] (n : ℤ) :
    ∃ m : ℤ, embed P (n : ZMod P) - (n : ℝ) / (P : ℝ) = (m : ℝ) := by
  have hP : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne P)
  have hmod : ((n : ZMod P).val : ℤ) = n % (P : ℤ) := ZMod.val_intCast n
  refine ⟨-(n / (P : ℤ)), ?_⟩
  unfold embed
  have hdiv : (P : ℤ) * (n / (P : ℤ)) + n % (P : ℤ) = n := Int.mul_ediv_add_emod n (P : ℤ)
  have hdivR : (P : ℝ) * ((n / (P : ℤ) : ℤ) : ℝ) + ((n % (P : ℤ) : ℤ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hdiv
  have hvalR : ((n : ZMod P).val : ℝ) = ((n % (P : ℤ) : ℤ) : ℝ) := by exact_mod_cast hmod
  rw [hvalR]
  field_simp [hP]
  push_cast
  linarith

lemma embed_add_sub {P : ℕ} [NeZero P] (a b : ZMod P) :
    ∃ m : ℤ, embed P (a + b) - (embed P a + embed P b) = (m : ℝ) := by
  have hP : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne P)
  have hval : (a + b).val = (a.val + b.val) % P := ZMod.val_add a b
  let q : ℕ := (a.val + b.val) / P
  refine ⟨-(q : ℤ), ?_⟩
  unfold embed
  rw [hval]
  have hdiv : P * q + (a.val + b.val) % P = a.val + b.val := by
    dsimp only [q]; linarith [Nat.div_add_mod (a.val + b.val) P]
  have hdivR : (P : ℝ) * (q : ℝ) + (((a.val + b.val) % P : ℕ) : ℝ) =
      (a.val : ℝ) + (b.val : ℝ) := by exact_mod_cast hdiv
  field_simp [hP]
  rw [Int.cast_neg, Int.cast_natCast]
  linarith

lemma embed_int_mul_sub {P : ℕ} [NeZero P] (c : ℤ) (a : ZMod P) :
    ∃ m : ℤ, embed P ((c : ZMod P) * a) - (c : ℝ) * embed P a = (m : ℝ) := by
  have heq : (c : ZMod P) * a = ((c * (a.val : ℤ) : ℤ) : ZMod P) := by
    simp [Int.cast_mul]
  rw [heq]
  obtain ⟨m, hm⟩ := embed_intCast_sub (P := P) (c * (a.val : ℤ))
  refine ⟨m, ?_⟩
  unfold embed at hm ⊢
  have hr : ((c * (a.val : ℤ) : ℤ) : ℝ) / (P : ℝ) = (c : ℝ) * ((a.val : ℝ) / (P : ℝ)) := by
    push_cast; ring
  rw [← hr]
  exact hm

lemma embed_sum_int_mul_sub {P : ℕ} [NeZero P] {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (x : ι → ZMod P) :
    ∃ m : ℤ, embed P (∑ i ∈ s, (c i : ZMod P) * x i) - ∑ i ∈ s, (c i : ℝ) * embed P (x i) = (m : ℝ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [embed]⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨m1, hm1⟩ := embed_add_sub (P := P) ((c a : ZMod P) * x a) (∑ i ∈ s, (c i : ZMod P) * x i)
    obtain ⟨m2, hm2⟩ := embed_int_mul_sub (P := P) (c a) (x a)
    obtain ⟨m3, hm3⟩ := ih
    exact ⟨m1 + m2 + m3, by push_cast; linarith⟩

lemma card_zmod_tdist_le {P : ℕ} [NeZero P] {τ : ℝ} (_hτ : 0 ≤ τ) :
    (Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ τ)).card ≤
      2 * Nat.floor (τ * P) + 1 := by
  have hPpos : 0 < P := NeZero.pos P
  have hP : (0 : ℝ) < P := by exact_mod_cast hPpos
  let L := Nat.floor (τ * P)
  let S : Finset (ZMod P) :=
    (Finset.range (L + 1)).image (fun k : ℕ => (k : ZMod P)) ∪
    (Finset.Icc 1 L).image (fun k : ℕ => ((P - k : ℕ) : ZMod P))
  have hsub : Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ τ) ⊆ S := by
    intro a ha
    have htd : tdist (embed P a) ≤ τ := (Finset.mem_filter.mp ha).2
    have hval_lt : a.val < P := ZMod.val_lt a
    have h0 : 0 ≤ (a.val : ℝ) / (P : ℝ) := div_nonneg (Nat.cast_nonneg _) hP.le
    have h1 : (a.val : ℝ) / (P : ℝ) < 1 := (div_lt_one hP).mpr (by exact_mod_cast hval_lt)
    rw [Finset.mem_union]
    by_cases hhalf : (a.val : ℝ) / (P : ℝ) ≤ 1 / 2
    · left
      have hteq : tdist (embed P a) = (a.val : ℝ) / (P : ℝ) := by
        unfold embed
        rw [tdist_eq_abs_of_le_half (by rw [abs_of_nonneg h0]; exact hhalf), abs_of_nonneg h0]
      rw [hteq] at htd
      have hle : (a.val : ℝ) ≤ τ * P := (div_le_iff₀ hP).mp htd
      exact Finset.mem_image.mpr ⟨a.val, Finset.mem_range.mpr (by have := Nat.le_floor hle; omega),
        ZMod.natCast_zmod_val a⟩
    · right
      push Not at hhalf
      have hneg_le : |((a.val : ℝ) / (P : ℝ) - 1)| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith
      have hteq : tdist (embed P a) = 1 - (a.val : ℝ) / (P : ℝ) := by
        have hs := tdist_eq_of_sub_int (x := embed P a) (y := embed P a - 1) 1 (by ring)
        rw [hs, tdist_eq_abs_of_le_half (by simpa [embed] using hneg_le)]
        unfold embed
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [hteq] at htd
      have hle : ((P - a.val : ℕ) : ℝ) ≤ τ * P := by
        rw [Nat.cast_sub hval_lt.le]
        have := mul_le_mul_of_nonneg_right htd hP.le
        field_simp [hP.ne'] at this
        linarith
      refine Finset.mem_image.mpr ⟨P - a.val, Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hle⟩, ?_⟩
      have hsub_eq : P - (P - a.val) = a.val := by omega
      rw [hsub_eq, ZMod.natCast_zmod_val a]
  calc (Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ τ)).card
      ≤ S.card := Finset.card_le_card hsub
    _ ≤ ((Finset.range (L + 1)).image (fun k : ℕ => (k : ZMod P))).card +
        ((Finset.Icc 1 L).image (fun k : ℕ => ((P - k : ℕ) : ZMod P))).card :=
          Finset.card_union_le _ _
    _ ≤ (Finset.range (L + 1)).card + (Finset.Icc 1 L).card :=
          add_le_add Finset.card_image_le Finset.card_image_le
    _ = (L + 1) + L := by simp
    _ = 2 * L + 1 := by omega

lemma card_zmod_fract_in_interval {P G : ℕ} [NeZero P] (hG : 1 ≤ G) (hPG : G ≤ P)
    (k : Fin G) (β : ℝ) :
    P / G ≤ (Finset.univ.filter (fun a : ZMod P =>
      ((k : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (embed P a + β) ∧
      Int.fract (embed P a + β) < (((k : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ))).card := by
  have hPpos : 0 < P := NeZero.pos P
  have hP : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hGpos : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  let L := P / G
  have hLP : L ≤ P := Nat.div_le_self P G
  let c : ℝ := ((k : ℕ) : ℝ) / (G : ℝ)
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hGpos.le
  have hc1 : c + 1 / (G : ℝ) ≤ 1 := by
    dsimp only [c]
    rw [← add_div, div_le_one hGpos]
    have : (k : ℕ) + 1 ≤ G := k.isLt
    exact_mod_cast this
  let m0 : ℤ := ⌈(P : ℝ) * (c - β)⌉
  let f : Fin L → ZMod P := fun r => ((m0 + (r : ℕ) : ℤ) : ZMod P)
  have hf_inj : Function.Injective f := by
    intro r1 r2 hr
    dsimp only [f] at hr
    have hdiff : ((((r1 : ℕ) : ℤ) - ((r2 : ℕ) : ℤ) : ℤ) : ZMod P) = 0 := by
      have hsub : ((m0 + (r1 : ℕ) : ℤ) : ZMod P) - ((m0 + (r2 : ℕ) : ℤ) : ZMod P) = 0 :=
        sub_eq_zero.mpr hr
      have heq : (m0 + (r1 : ℕ) : ℤ) - (m0 + (r2 : ℕ) : ℤ) = ((r1 : ℕ) : ℤ) - ((r2 : ℕ) : ℤ) := by ring
      rw [← heq, Int.cast_sub]
      exact hsub
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hdiff
    obtain ⟨q, hq⟩ := hdiff
    have h1 := r1.isLt
    have h2 := r2.isLt
    have hq0 : q = 0 := by nlinarith
    rw [hq0, mul_zero] at hq
    apply Fin.ext
    omega
  have hf_mem : ∀ r : Fin L,
      c ≤ Int.fract (embed P (f r) + β) ∧ Int.fract (embed P (f r) + β) < c + 1 / (G : ℝ) := by
    intro r
    obtain ⟨m, hm⟩ := embed_intCast_sub (P := P) (m0 + (r : ℕ))
    have hfr_eq : Int.fract (embed P (f r) + β) =
        Int.fract (((m0 + (r : ℕ) : ℤ) : ℝ) / (P : ℝ) + β) := by
      have hadd : embed P (f r) + β = (((m0 + (r : ℕ) : ℤ) : ℝ) / (P : ℝ) + β) + (m : ℝ) := by
        dsimp only [f]; linarith
      rw [hadd, Int.fract_add_intCast]
    rw [hfr_eq]
    have hm0_ge : (P : ℝ) * (c - β) ≤ (m0 : ℝ) := Int.le_ceil _
    have hm0_lt : (m0 : ℝ) < (P : ℝ) * (c - β) + 1 := Int.ceil_lt_add_one _
    have hr_lt : ((r : ℕ) + 1 : ℝ) ≤ (L : ℝ) := by
      have : (r : ℕ) + 1 ≤ L := r.isLt; exact_mod_cast this
    have hLP_le : (L : ℝ) / (P : ℝ) ≤ 1 / (G : ℝ) := by
      rw [div_le_div_iff₀ hP hGpos]
      have : (L : ℝ) * (G : ℝ) ≤ (P : ℝ) := by exact_mod_cast Nat.div_mul_le_self P G
      linarith
    have hlo : c ≤ ((m0 + (r : ℕ) : ℤ) : ℝ) / (P : ℝ) + β := by
      rw [← sub_le_iff_le_add, le_div_iff₀ hP]
      push_cast
      have hr0 : (0 : ℝ) ≤ (r : ℕ) := Nat.cast_nonneg _
      nlinarith
    have hhi : ((m0 + (r : ℕ) : ℤ) : ℝ) / (P : ℝ) + β < c + 1 / (G : ℝ) := by
      have hstep1 : ((m0 + (r : ℕ) : ℤ) : ℝ) / (P : ℝ) + β < c + ((r : ℕ) + 1 : ℝ) / (P : ℝ) := by
        have : ((m0 + (r : ℕ) : ℤ) : ℝ) + β * (P : ℝ) < c * (P : ℝ) + ((r : ℕ) + 1 : ℝ) := by
          push_cast; linarith
        have := div_lt_div_of_pos_right this hP
        field_simp [hP.ne'] at this ⊢
        linarith
      have hstep2 : ((r : ℕ) + 1 : ℝ) / (P : ℝ) ≤ (L : ℝ) / (P : ℝ) :=
        div_le_div_of_nonneg_right hr_lt hP.le
      linarith
    rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact ⟨hlo, hhi⟩
  have hsub : Finset.univ.image f ⊆ Finset.univ.filter (fun a : ZMod P =>
      ((k : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (embed P a + β) ∧
      Int.fract (embed P a + β) < (((k : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ)) := by
    intro a ha
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcast : (((k : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ) = c + 1 / (G : ℝ) := by
      dsimp only [c]; push_cast; ring
    rw [hcast]
    exact hf_mem r
  calc L = (Finset.univ : Finset (Fin L)).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf_inj).symm
    _ ≤ _ := Finset.card_le_card hsub

/- ## Section 2: Finite-field linear surjectivity and Mahler/Cassels short basis -/

lemma card_preimage_of_surjective_linearMap {K : Type*} [Field K] [Fintype K]
    {V W : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] [Fintype W]
    (f : V →ₗ[K] W) (hsurj : Function.Surjective f) (s : Finset W) :
    (Finset.univ.filter (fun v : V => f v ∈ s)).card * Fintype.card W =
      s.card * Fintype.card V := by
  have hfib : ∀ w : W, (Finset.univ.filter (fun v : V => f v = w)).card =
      (Finset.univ.filter (fun v : V => f v = 0)).card := by
    intro w
    obtain ⟨v0, rfl⟩ := hsurj w
    refine Finset.card_bij (fun v _ => v - v0) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [map_sub, hv, sub_self]
    · intro v1 _ v2 _ h; exact sub_left_inj.mp h
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact ⟨u + v0, by simp [map_add, hu], add_sub_cancel_right u v0⟩
  have hpart : ∀ t : Finset W, (Finset.univ.filter (fun v : V => f v ∈ t)).card =
      t.card * (Finset.univ.filter (fun v : V => f v = 0)).card := by
    intro t
    have hbi : Finset.univ.filter (fun v : V => f v ∈ t) =
        t.biUnion (fun w => Finset.univ.filter (fun v : V => f v = w)) := by
      ext v; simp
    rw [hbi, Finset.card_biUnion]
    · simp [hfib]
    · intro w1 _ w2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      exact hne (hv1.symm.trans hv2)
  have htot := hpart Finset.univ
  have huniv : Finset.univ.filter (fun v : V => f v ∈ (Finset.univ : Finset W)) = Finset.univ := by
    ext v; simp
  rw [huniv, Finset.card_univ, Finset.card_univ] at htot
  rw [hpart s, htot]
  ring

lemma abs_det_le_factorial_mul_pow {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (B : ℕ)
    (hB : ∀ i j, |M i j| ≤ (B : ℤ)) :
    |M.det| ≤ (m.factorial : ℤ) * (B : ℤ) ^ m := by
  rw [Matrix.det_apply]
  calc |∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin m), |(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), (B : ℤ) ^ m := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul]
        have hsign : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [hsign, one_mul, Finset.abs_prod]
        calc ∏ i : Fin m, |M (σ i) i|
            ≤ ∏ _i : Fin m, (B : ℤ) :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hB (σ i) i)
          _ = (B : ℤ) ^ m := by simp
    _ = (m.factorial : ℤ) * (B : ℤ) ^ m := by simp [Fintype.card_perm, Fintype.card_fin]

lemma exists_invertible_minor_of_linearIndependent {m D : ℕ}
    (v : Fin m → Fin D → ℤ)
    (hind : LinearIndependent ℚ (fun i b => (v i b : ℚ))) :
    ∃ cols : Fin m → Fin D,
      (Matrix.of (fun i j : Fin m => v i (cols j))).det ≠ 0 := by
  let A : Matrix (Fin m) (Fin D) ℚ := Matrix.of (fun i j => (v i j : ℚ))
  have hrank : A.rank = m := by
    have hrow : LinearIndependent ℚ A.row := hind
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hrow, Fintype.card_fin]
  have hcol_span : Submodule.span ℚ (Set.range (fun j : Fin D => fun i : Fin m => A i j)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun j : Fin D => fun i : Fin m => A i j))) =
        A.rank := by rw [Matrix.rank_eq_finrank_span_cols]; rfl
    rw [h1, hrank, Module.finrank_fin_fun]
  obtain ⟨s, hs_sub, hs_span, hs_ind⟩ := exists_linearIndependent ℚ
    (Set.range (fun j : Fin D => fun i : Fin m => A i j))
  rw [hcol_span] at hs_span
  have hs_fin : s.Finite := (Set.finite_range _).subset hs_sub
  let : Fintype s := hs_fin.fintype
  have hcard_eq : Fintype.card s = m := by
    have hfr := finrank_span_eq_card hs_ind
    rw [Subtype.range_coe, hs_span, finrank_top, Module.finrank_fin_fun] at hfr
    exact hfr.symm
  let e : Fin m ≃ s := (Fintype.equivFinOfCardEq hcard_eq).symm
  have hmem : ∀ j : Fin m, (e j : Fin m → ℚ) ∈ Set.range (fun col : Fin D => fun i : Fin m => A i col) :=
    fun j => hs_sub (e j).2
  choose cols hcols using hmem
  refine ⟨cols, ?_⟩
  intro hdet0
  let B : Matrix (Fin m) (Fin m) ℚ := Matrix.of (fun i j => (v i (cols j) : ℚ))
  have hBdet : B.det = 0 := by
    change ((Int.castRingHom ℚ).mapMatrix (Matrix.of (fun i j : Fin m => v i (cols j)))).det = 0
    rw [← RingHom.map_det, hdet0, map_zero]
  have hcol_ind : LinearIndependent ℚ (fun j : Fin m => fun i : Fin m => B i j) := by
    have hcomp : (fun j : Fin m => fun i : Fin m => B i j) = (fun x : s => (x : Fin m → ℚ)) ∘ e := by
      funext j i
      have h := congrFun (hcols j) i
      simpa [B, A] using h
    rw [hcomp]
    exact hs_ind.comp e e.injective
  have hBunit : IsUnit B.det := by
    rw [← Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det Bᵀ).mp ((Matrix.linearIndependent_rows_iff_isUnit (A := Bᵀ)).mp hcol_ind)
  exact hBunit.ne_zero hBdet

lemma surjective_dot_map_zmod {m D P : ℕ} [Fact P.Prime]
    (v : Fin m → Fin D → ℤ) (B : ℕ)
    (hB : ∀ i b, |v i b| ≤ (B : ℤ))
    (hind : LinearIndependent ℚ (fun i b => (v i b : ℚ)))
    (hP : m.factorial * B ^ m < P) :
    Function.Surjective (fun (x : Fin D → ZMod P) (i : Fin m) =>
      ∑ b : Fin D, (v i b : ZMod P) * x b) := by
  obtain ⟨cols, hdet_ne⟩ := exists_invertible_minor_of_linearIndependent v hind
  let M : Matrix (Fin m) (Fin m) ℤ := Matrix.of (fun i j => v i (cols j))
  have hdet_bd : |M.det| ≤ (m.factorial : ℤ) * (B : ℤ) ^ m :=
    abs_det_le_factorial_mul_pow M B (fun i j => hB i (cols j))
  have hdet_lt : |M.det| < (P : ℤ) := lt_of_le_of_lt hdet_bd (by exact_mod_cast hP)
  have hdet_nz_mod : (M.det : ZMod P) ≠ 0 := by
    intro h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hdvd : (P : ℤ) ∣ |M.det| := by
      rcases le_or_gt 0 M.det with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact dvd_neg.mpr h0
    have hle : (P : ℤ) ≤ |M.det| := Int.le_of_dvd (abs_pos.mpr hdet_ne) hdvd
    omega
  have hcols_inj : Function.Injective cols := by
    intro j1 j2 hjeq
    by_contra hne
    exact hdet_ne (Matrix.det_zero_of_column_eq hne (fun i => by simp [hjeq]))
  let Mp : Matrix (Fin m) (Fin m) (ZMod P) := M.map (Int.castRingHom (ZMod P))
  have hMp_det : Mp.det ≠ 0 := by
    change ((Int.castRingHom (ZMod P)).mapMatrix M).det ≠ 0
    rw [← RingHom.map_det]
    exact hdet_nz_mod
  let : Invertible Mp := Matrix.invertibleOfIsUnitDet Mp (isUnit_iff_ne_zero.mpr hMp_det)
  intro y
  let z : Fin m → ZMod P := (⅟ Mp).mulVec y
  let x : Fin D → ZMod P := fun b =>
    if h : ∃ j : Fin m, cols j = b then z h.choose else 0
  refine ⟨x, funext fun i => ?_⟩
  have hsupp : ∀ b : Fin D, b ∉ Finset.univ.image cols → (v i b : ZMod P) * x b = 0 := by
    intro b hb
    have hni : ¬ ∃ j : Fin m, cols j = b := by
      rintro ⟨j, rfl⟩
      exact hb (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simp [x, dif_neg hni]
  dsimp only
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image cols)) (fun b _ hb => hsupp b hb)]
  rw [Finset.sum_image (fun j1 _ j2 _ h => hcols_inj h)]
  have hterm : ∀ j : Fin m, (v i (cols j) : ZMod P) * x (cols j) = Mp i j * z j := by
    intro j
    have hex : ∃ j' : Fin m, cols j' = cols j := ⟨j, rfl⟩
    have hch : hex.choose = j := hcols_inj hex.choose_spec
    simp [x, dif_pos hex, hch, Mp, M]
  simp_rw [hterm]
  have hmul : (Mp.mulVec z) i = y i := by
    have : Mp.mulVec ((⅟ Mp).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
    exact congrFun this i
  simpa [Matrix.mulVec, dotProduct] using hmul

set_option maxHeartbeats 800000 in
/-- Mahler-Cassels short integral basis + Cramer coefficient bound. -/
lemma mahler_short_basis {m D Q : ℕ} (hm : 1 ≤ m) (hQ : 1 ≤ Q)
    (v : Fin m → Fin D → ℤ)
    (hv_bd : ∀ i b, |v i b| ≤ (Q : ℤ))
    (hind : LinearIndependent ℚ (fun i b => (v i b : ℚ))) :
    ∃ w : Fin m → Fin D → ℤ,
      LinearIndependent ℚ (fun i b => (w i b : ℚ)) ∧
      (∀ i b, |w i b| ≤ (m : ℤ) * (Q : ℤ)) ∧
      (Submodule.span ℚ (Set.range (fun i b => (w i b : ℚ))) =
        Submodule.span ℚ (Set.range (fun i b => (v i b : ℚ)))) ∧
      (∀ ξ : Fin D → ℤ,
        (fun b => (ξ b : ℚ)) ∈ Submodule.span ℚ (Set.range (fun i b => (v i b : ℚ))) →
        (∀ b, |ξ b| ≤ (Q : ℤ)) →
        ∃ n : Fin m → ℤ,
          (∀ b, ξ b = ∑ i : Fin m, n i * w i b) ∧
          (∀ i, |n i| ≤ ((m + 1).factorial : ℤ) * ((m : ℤ) * (Q : ℤ)) ^ (m + 1))) := by
  let V : Submodule ℚ (Fin D → ℚ) := Submodule.span ℚ (Set.range (fun i b => (v i b : ℚ)))
  let vQ : Fin m → V := fun i => ⟨fun b => (v i b : ℚ), Submodule.subset_span ⟨i, rfl⟩⟩
  have hvQ_ind : LinearIndependent ℚ vQ := by
    rw [linearIndependent_iff'] at hind ⊢
    intro s g hg i hi
    exact hind s g (by simpa [vQ] using congrArg Subtype.val hg) i hi
  have hvQ_span : Submodule.span ℚ (Set.range vQ) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add _ _ _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
    | smul a _ _ ih => exact Submodule.smul_mem _ a ih
  let bas : Module.Basis (Fin m) ℚ V := Module.Basis.mk hvQ_ind (by rw [hvQ_span])
  obtain ⟨cols, hdet_ne⟩ := exists_invertible_minor_of_linearIndependent v hind
  let M : Matrix (Fin m) (Fin m) ℤ := Matrix.of (fun i j => v i (cols j))
  let Δ : ℕ := M.det.natAbs
  have hΔ_pos : 0 < Δ := Int.natAbs_pos.mpr hdet_ne
  have hcoord_den : ∀ z : Fin D → ℤ, (hz : (fun b => (z b : ℚ)) ∈ V) →
      ∀ j : Fin m, ∃ t : ℤ, (Δ : ℚ) * bas.repr ⟨fun b => (z b : ℚ), hz⟩ j = (t : ℚ) := by
    intro z hz j
    let c : Fin m → ℚ := fun i => bas.repr ⟨fun b => (z b : ℚ), hz⟩ i
    have hlin : ∀ b : Fin D, (z b : ℚ) = ∑ i : Fin m, c i * (v i b : ℚ) := by
      intro b
      have hval := congrFun (congrArg Subtype.val (bas.sum_repr ⟨fun b => (z b : ℚ), hz⟩)) b
      simpa [c, bas, vQ, Finset.sum_apply] using hval.symm
    let Mq : Matrix (Fin m) (Fin m) ℚ := M.map (Int.castRingHom ℚ)
    let zsub : Fin m → ℚ := fun r => (z (cols r) : ℚ)
    have hvec : Mqᵀ.mulVec c = zsub := by
      ext r
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Mq, M, Matrix.map_apply,
        Matrix.of_apply, zsub, eq_intCast]
      rw [hlin (cols r)]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hadj := congrArg (fun u => Mqᵀ.adjugate.mulVec u) hvec
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.det_transpose] at hadj
    have hcomp := congrFun hadj j
    have hMqdet : Mq.det = (M.det : ℚ) := by
      change ((Int.castRingHom ℚ).mapMatrix M).det = _
      rw [← RingHom.map_det]; rfl
    have hadj_int : ∀ r : Fin m, Mqᵀ.adjugate j r = ((Mᵀ.adjugate j r : ℤ) : ℚ) := by
      intro r
      have h1 : Mqᵀ = Mᵀ.map (Int.castRingHom ℚ) := by ext a b; simp [Mq]
      rw [h1]
      exact (congrFun (congrFun (RingHom.map_adjugate (Int.castRingHom ℚ) Mᵀ) j) r).symm
    have hval_int : (M.det : ℚ) * c j =
        ((∑ r : Fin m, Mᵀ.adjugate j r * z (cols r) : ℤ) : ℚ) := by
      rw [← hMqdet]
      simpa [Matrix.mulVec, dotProduct, hadj_int, zsub, Int.cast_sum, Int.cast_mul] using hcomp
    rcases Int.natAbs_eq M.det with hpos | hneg
    · refine ⟨∑ r : Fin m, Mᵀ.adjugate j r * z (cols r), ?_⟩
      have hcast : (Δ : ℚ) = (M.det : ℚ) := by dsimp only [Δ]; rw [← Int.cast_natCast, ← hpos]
      rw [hcast]; exact hval_int
    · refine ⟨-(∑ r : Fin m, Mᵀ.adjugate j r * z (cols r)), ?_⟩
      have hcast : (Δ : ℚ) = -(M.det : ℚ) := by
        dsimp only [Δ]
        have : (M.det : ℚ) = -(M.det.natAbs : ℚ) := by exact_mod_cast hneg
        linarith
      rw [hcast, neg_mul, hval_int, Int.cast_neg]
  let IsGood (k : Fin m) (a : ℕ) : Prop :=
    0 < a ∧ ∃ z : Fin D → ℤ, ∃ hz : (fun b => (z b : ℚ)) ∈ V,
      (∀ j : Fin m, k < j → bas.repr ⟨fun b => (z b : ℚ), hz⟩ j = 0) ∧
      (Δ : ℚ) * bas.repr ⟨fun b => (z b : ℚ), hz⟩ k = (a : ℚ)
  have hex_good : ∀ k : Fin m, ∃ a, IsGood k a := by
    intro k
    refine ⟨Δ, hΔ_pos, v k, Submodule.subset_span ⟨k, rfl⟩, ?_, ?_⟩
    · intro j hj
      have hrepr : bas.repr (vQ k) = Finsupp.single k 1 := by simpa [bas] using bas.repr_self k
      have h1 : bas.repr (vQ k) j = (Finsupp.single k (1 : ℚ)) j := congrFun (congrArg DFunLike.coe hrepr) j
      rw [Finsupp.single_apply, if_neg (ne_of_lt hj)] at h1
      exact h1
    · have hrepr : bas.repr (vQ k) = Finsupp.single k 1 := by simpa [bas] using bas.repr_self k
      have h1 : bas.repr (vQ k) k = 1 := by
        have := congrFun (congrArg DFunLike.coe hrepr) k
        simpa using this
      change (Δ : ℚ) * bas.repr (vQ k) k = (Δ : ℚ)
      rw [h1, mul_one]
  let amin (k : Fin m) : ℕ := Nat.find (hex_good k)
  have hamin_spec (k : Fin m) : IsGood k (amin k) := Nat.find_spec (hex_good k)
  have hamin_min (k : Fin m) {a : ℕ} (ha : IsGood k a) : amin k ≤ a := Nat.find_min' (hex_good k) ha
  have hamin_le_Δ (k : Fin m) : amin k ≤ Δ := by
    apply hamin_min k
    refine ⟨hΔ_pos, v k, Submodule.subset_span ⟨k, rfl⟩, ?_, ?_⟩
    · intro j hj
      have hrepr : bas.repr (vQ k) = Finsupp.single k 1 := by simpa [bas] using bas.repr_self k
      have h1 : bas.repr (vQ k) j = (Finsupp.single k (1 : ℚ)) j := congrFun (congrArg DFunLike.coe hrepr) j
      rw [Finsupp.single_apply, if_neg (ne_of_lt hj)] at h1
      exact h1
    · have hrepr : bas.repr (vQ k) = Finsupp.single k 1 := by simpa [bas] using bas.repr_self k
      have h1 : bas.repr (vQ k) k = 1 := by
        have := congrFun (congrArg DFunLike.coe hrepr) k
        simpa using this
      change (Δ : ℚ) * bas.repr (vQ k) k = (Δ : ℚ)
      rw [h1, mul_one]
  choose zraw hzraw_mem hzraw_hi hzraw_k using fun k => (hamin_spec k).2
  let w : Fin m → Fin D → ℤ := fun k b =>
    zraw k b - ∑ j ∈ Finset.univ.filter (· < k),
      round (bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ j) * v j b
  have hw_mem : ∀ k : Fin m, (fun b => (w k b : ℚ)) ∈ V := by
    intro k
    have hsub : (fun b => (w k b : ℚ)) = (fun b => (zraw k b : ℚ)) -
        ∑ j ∈ Finset.univ.filter (· < k),
          ((round (bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ j) : ℤ) : ℚ) •
            (fun b => (v j b : ℚ)) := by
      ext b; simp [w, Finset.sum_apply]
    rw [hsub]
    exact V.sub_mem (hzraw_mem k)
      (V.sum_mem fun j _ => V.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))
  have hw_repr : ∀ k j : Fin m,
      bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j =
        if j < k then
          bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ j -
            (round (bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ j) : ℚ)
        else bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ j := by
    intro k j
    have heq : (⟨fun b => (w k b : ℚ), hw_mem k⟩ : V) =
        ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ -
          ∑ i ∈ Finset.univ.filter (· < k),
            ((round (bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ i) : ℤ) : ℚ) • vQ i := by
      apply Subtype.ext; ext b; simp [w, vQ, Finset.sum_apply]
    rw [heq, map_sub, map_sum, Finsupp.sub_apply, Finsupp.finsetSum_apply]
    have hterm : ∀ i : Fin m,
        (bas.repr (((round (bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ i) : ℤ) : ℚ) • vQ i)) j =
        if i = j then (round (bas.repr ⟨fun b => (zraw k b : ℚ), hzraw_mem k⟩ i) : ℚ) else 0 := by
      intro i
      rw [map_smul, Finsupp.smul_apply]
      have hr : bas.repr (vQ i) j = if i = j then 1 else 0 := by
        have h1 : bas.repr (vQ i) = Finsupp.single i 1 := by simpa [bas] using bas.repr_self i
        rw [h1, Finsupp.single_apply]
      rw [hr]; split_ifs <;> simp
    simp_rw [hterm]
    by_cases hjk : j < k
    · rw [if_pos hjk, Finset.sum_ite_eq']; simp [hjk]
    · rw [if_neg hjk, Finset.sum_ite_eq']; simp [hjk]
  have hw_hi : ∀ k j : Fin m, k < j → bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j = 0 := by
    intro k j hkj
    rw [hw_repr k j, if_neg (not_lt.mpr hkj.le)]
    exact hzraw_hi k j hkj
  have hw_diag : ∀ k : Fin m,
      (Δ : ℚ) * bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ k = (amin k : ℚ) := by
    intro k
    rw [hw_repr k k, if_neg (lt_irrefl k)]
    exact hzraw_k k
  have hw_diag_pos : ∀ k : Fin m, 0 < bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ k := by
    intro k
    have h1 := hw_diag k
    have h2 : (0 : ℚ) < (amin k : ℚ) := by exact_mod_cast (hamin_spec k).1
    have h3 : (0 : ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ_pos
    nlinarith
  have hw_diag_le_one : ∀ k : Fin m, bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ k ≤ 1 := by
    intro k
    have h1 := hw_diag k
    have h2 : (amin k : ℚ) ≤ (Δ : ℚ) := by exact_mod_cast hamin_le_Δ k
    have h3 : (0 : ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ_pos
    nlinarith
  have hw_ind : LinearIndependent ℚ (fun k b => (w k b : ℚ)) := by
    rw [linearIndependent_iff']
    intro s g hg
    suffices hdesc : ∀ r : ℕ, ∀ k ∈ s, m - r ≤ k.val → g k = 0 by
      intro k hk; exact hdesc m k hk (by omega)
    intro r
    induction r with
    | zero => intro k _ hk; omega
    | succ r ih =>
      intro k hks hk
      by_cases hgt : m - r ≤ k.val
      · exact ih k hks hgt
      · have hVsum : ∑ i ∈ s, g i • (⟨fun b => (w i b : ℚ), hw_mem i⟩ : V) = 0 := by
          apply Subtype.ext; ext b
          simpa [Finset.sum_apply] using congrFun hg b
        have hcomp := congrArg (fun x => bas.repr x k) hVsum
        rw [map_sum, map_zero, Finsupp.finsetSum_apply, Finsupp.zero_apply] at hcomp
        have hzero : ∀ i ∈ s, i ≠ k →
            (bas.repr (g i • ⟨fun b => (w i b : ℚ), hw_mem i⟩)) k = 0 := by
          intro i his hik
          rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
          rcases lt_or_gt_of_ne hik with hlt | hgt'
          · rw [hw_hi i k hlt, mul_zero]
          · have hi0 : g i = 0 := ih i his (by change k.val < i.val at hgt'; omega)
            rw [hi0, zero_mul]
        rw [Finset.sum_eq_single k (fun i hi hik => hzero i hi hik) (fun h => absurd hks h),
          map_smul, Finsupp.smul_apply, smul_eq_mul] at hcomp
        exact (mul_eq_zero.mp hcomp).resolve_right (hw_diag_pos k).ne'
  have hw_bd : ∀ k b, |w k b| ≤ (m : ℤ) * (Q : ℤ) := by
    intro k b
    have hlin : (w k b : ℚ) = ∑ j : Fin m, bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j * (v j b : ℚ) := by
      have hval := congrFun (congrArg Subtype.val (bas.sum_repr ⟨fun b => (w k b : ℚ), hw_mem k⟩)) b
      simpa [bas, vQ, Finset.sum_apply] using hval.symm
    have hq : |(w k b : ℚ)| ≤ (m : ℚ) * (Q : ℚ) := by
      rw [hlin]
      calc |∑ j : Fin m, bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j * (v j b : ℚ)|
          ≤ ∑ j : Fin m, |bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j * (v j b : ℚ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin m, (Q : ℚ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have hc1 : |bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j| ≤ 1 := by
              rcases lt_trichotomy j k with hlt | rfl | hgt
              · rw [hw_repr k j, if_pos hlt]
                exact (abs_sub_round _).trans (by norm_num)
              · rw [abs_of_pos (hw_diag_pos j)]
                exact hw_diag_le_one j
              · rw [hw_hi k j hgt, abs_zero]; norm_num
            have hv1 : |(v j b : ℚ)| ≤ (Q : ℚ) := by exact_mod_cast hv_bd j b
            calc |bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j| * |(v j b : ℚ)|
                ≤ 1 * (Q : ℚ) := mul_le_mul hc1 hv1 (abs_nonneg _) zero_le_one
              _ = (Q : ℚ) := one_mul _
        _ = (m : ℚ) * (Q : ℚ) := by simp
    exact_mod_cast hq
  have hw_span : Submodule.span ℚ (Set.range (fun i b => (w i b : ℚ))) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hw_mem i
    · rw [finrank_span_eq_card hw_ind, finrank_span_eq_card hind]
  -- Integral generation by induction on the highest nonzero coordinate
  have hz_gen : ∀ r : ℕ, r ≤ m → ∀ ξ : Fin D → ℤ, (hξ : (fun b => (ξ b : ℚ)) ∈ V) →
      (∀ j : Fin m, r ≤ j.val → bas.repr ⟨fun b => (ξ b : ℚ), hξ⟩ j = 0) →
      ∃ n : Fin m → ℤ, ∀ b, ξ b = ∑ i : Fin m, n i * w i b := by
    intro r
    induction r with
    | zero =>
      intro _ ξ hξ hzero
      refine ⟨0, fun b => ?_⟩
      have hrepr0 : bas.repr ⟨fun b => (ξ b : ℚ), hξ⟩ = 0 := by
        ext j; exact hzero j (Nat.zero_le _)
      have hξ0 : (⟨fun b => (ξ b : ℚ), hξ⟩ : V) = 0 := bas.repr.injective (by simpa using hrepr0)
      have hb0 : (ξ b : ℚ) = 0 := congrFun (congrArg Subtype.val hξ0) b
      simpa using (show ξ b = 0 by exact_mod_cast hb0)
    | succ r ih =>
      intro hr ξ hξ hzero
      let k : Fin m := ⟨r, by omega⟩
      obtain ⟨t, ht⟩ := hcoord_den ξ hξ k
      let a := amin k
      have ha_pos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast (hamin_spec k).1
      let q : ℤ := t / (a : ℤ)
      let rem : ℤ := t % (a : ℤ)
      have hdiv : (a : ℤ) * q + rem = t := Int.mul_ediv_add_emod t (a : ℤ)
      have hrem0 : 0 ≤ rem := Int.emod_nonneg t ha_pos.ne'
      have hrem_lt : rem < (a : ℤ) := Int.emod_lt_of_pos t ha_pos
      let ξ' : Fin D → ℤ := fun b => ξ b - q * w k b
      have hξ'_mem : (fun b => (ξ' b : ℚ)) ∈ V := by
        have : (fun b => (ξ' b : ℚ)) = (fun b => (ξ b : ℚ)) - (q : ℚ) • (fun b => (w k b : ℚ)) := by
          ext b; simp [ξ']
        rw [this]
        exact V.sub_mem hξ (V.smul_mem _ (hw_mem k))
      have hξ'_repr : ∀ j : Fin m,
          bas.repr ⟨fun b => (ξ' b : ℚ), hξ'_mem⟩ j =
            bas.repr ⟨fun b => (ξ b : ℚ), hξ⟩ j - (q : ℚ) * bas.repr ⟨fun b => (w k b : ℚ), hw_mem k⟩ j := by
        intro j
        have heq : (⟨fun b => (ξ' b : ℚ), hξ'_mem⟩ : V) =
            ⟨fun b => (ξ b : ℚ), hξ⟩ - (q : ℚ) • ⟨fun b => (w k b : ℚ), hw_mem k⟩ := by
          apply Subtype.ext; ext b; simp [ξ']
        rw [heq, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
      have hξ'_hi : ∀ j : Fin m, k < j → bas.repr ⟨fun b => (ξ' b : ℚ), hξ'_mem⟩ j = 0 := by
        intro j hj
        rw [hξ'_repr j, hzero j (by change r < j.val at hj; omega), hw_hi k j hj, mul_zero, sub_zero]
      have hξ'_k : (Δ : ℚ) * bas.repr ⟨fun b => (ξ' b : ℚ), hξ'_mem⟩ k = (rem : ℚ) := by
        rw [hξ'_repr k, mul_sub, ht, ← mul_assoc, mul_comm (Δ : ℚ) (q : ℚ), mul_assoc, hw_diag k]
        have hdivQ : ((a : ℤ) : ℚ) * (q : ℚ) + (rem : ℚ) = (t : ℚ) := by exact_mod_cast hdiv
        push_cast at hdivQ ⊢
        linarith
      have hrem_eq0 : rem = 0 := by
        by_contra hne
        have hrem_pos : 0 < rem.toNat := by omega
        have hgood : IsGood k rem.toNat := by
          refine ⟨hrem_pos, ξ', hξ'_mem, hξ'_hi, ?_⟩
          rw [hξ'_k]
          have : ((rem.toNat : ℕ) : ℚ) = (rem : ℚ) := by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg hrem0]
          exact this.symm
        have hle := hamin_min k hgood
        omega
      have hξ'_r : ∀ j : Fin m, r ≤ j.val → bas.repr ⟨fun b => (ξ' b : ℚ), hξ'_mem⟩ j = 0 := by
        intro j hj
        by_cases hjk : j = k
        · subst hjk
          rw [hrem_eq0, Int.cast_zero] at hξ'_k
          have hΔne : (Δ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hΔ_pos.ne'
          exact (mul_eq_zero.mp hξ'_k).resolve_left hΔne
        · exact hξ'_hi j (by change r < j.val; have : j.val ≠ r := fun h => hjk (Fin.ext h); omega)
      obtain ⟨n', hn'⟩ := ih (by omega) ξ' hξ'_mem hξ'_r
      refine ⟨fun i => n' i + if i = k then q else 0, fun b => ?_⟩
      have hsum : ∑ i : Fin m, (n' i + if i = k then q else 0) * w i b =
          (∑ i : Fin m, n' i * w i b) + q * w k b := by
        simp_rw [add_mul, Finset.sum_add_distrib]
        congr 1
        simp [ite_mul]
      rw [hsum, ← hn' b]
      dsimp only [ξ']; ring
  refine ⟨w, hw_ind, hw_bd, hw_span, ?_⟩
  intro ξ hξ hξ_bd
  obtain ⟨n, hn⟩ := hz_gen m (le_refl m) ξ hξ (fun j hj => by have := j.isLt; omega)
  -- Cramer's rule bound on |n i|
  obtain ⟨cols2, hdet2_ne⟩ := exists_invertible_minor_of_linearIndependent w hw_ind
  let W : Matrix (Fin m) (Fin m) ℤ := Matrix.of (fun i j => w i (cols2 j))
  have hW_bd : ∀ i j, |W i j| ≤ (m : ℤ) * (Q : ℤ) := fun i j => hw_bd i (cols2 j)
  have hvec : Wᵀ.mulVec n = fun r => ξ (cols2 r) := by
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, W, Matrix.of_apply]
    rw [hn (cols2 r)]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hadj := congrArg (fun u => Wᵀ.adjugate.mulVec u) hvec
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.det_transpose] at hadj
  refine ⟨n, hn, fun i => ?_⟩
  have hcomp := congrFun hadj i
  have hdet_ge1 : (1 : ℤ) ≤ |W.det| := by
    have : 0 < |W.det| := abs_pos.mpr hdet2_ne; omega
  have hni_le : |n i| ≤ |W.det * n i| := by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) hdet_ge1
  have hadj_bd : ∀ r : Fin m, |Wᵀ.adjugate i r| ≤ (m.factorial : ℤ) * ((m : ℤ) * (Q : ℤ)) ^ m := by
    intro r
    rw [Matrix.adjugate_apply]
    have hupd_bd : ∀ a b : Fin m, |(Wᵀ.updateRow r (Pi.single i 1)) a b| ≤ (m : ℤ) * (Q : ℤ) := by
      intro a b
      by_cases har : a = r
      · subst har
        rw [Matrix.updateRow_self]
        by_cases hbi : b = i
        · subst hbi; simp only [Pi.single_eq_same, abs_one]
          have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
          have : (1 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ
          nlinarith
        · simp only [Pi.single_eq_of_ne hbi, abs_zero]
          positivity
      · rw [Matrix.updateRow_ne har]
        exact hW_bd b a
    have hcast : ((m * Q : ℕ) : ℤ) = (m : ℤ) * (Q : ℤ) := by push_cast; rfl
    rw [← hcast]
    exact abs_det_le_factorial_mul_pow _ (m * Q) (fun a b => by rw [hcast]; exact hupd_bd a b)
  have hmul_eq : W.det * n i = ∑ r : Fin m, Wᵀ.adjugate i r * ξ (cols2 r) := by
    simpa [Matrix.mulVec, dotProduct] using hcomp
  have hQ_le_mQ : (Q : ℤ) ≤ (m : ℤ) * (Q : ℤ) := by
    have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    have : (0 : ℤ) ≤ (Q : ℤ) := by positivity
    nlinarith
  calc |n i| ≤ |W.det * n i| := hni_le
    _ = |∑ r : Fin m, Wᵀ.adjugate i r * ξ (cols2 r)| := by rw [hmul_eq]
    _ ≤ ∑ r : Fin m, |Wᵀ.adjugate i r * ξ (cols2 r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin m, ((m.factorial : ℤ) * ((m : ℤ) * (Q : ℤ)) ^ m) * ((m : ℤ) * (Q : ℤ)) := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hadj_bd r) ((hξ_bd (cols2 r)).trans hQ_le_mQ) (abs_nonneg _) (by positivity)
    _ = (m : ℤ) * ((m.factorial : ℤ) * ((m : ℤ) * (Q : ℤ)) ^ (m + 1)) := by
        simp [pow_succ, mul_assoc]
    _ ≤ ((m + 1 : ℕ) : ℤ) * ((m.factorial : ℤ) * ((m : ℤ) * (Q : ℤ)) ^ (m + 1)) := by
        have h1 : (m : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by omega
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((m + 1).factorial : ℤ) * ((m : ℤ) * (Q : ℤ)) ^ (m + 1) := by
        rw [Nat.factorial_succ, Nat.cast_mul]; ring

/- ## Section 3: Pillar 1 — Well-distributed centers on the finite prime grid -/

set_option maxHeartbeats 1600000 in
lemma hunter_H1 (t : ℕ) (ht : 300 ≤ t) :
    let D := 200 * t
    let ρ : ℝ := ((D : ℝ) ^ 4)⁻¹
    let M := D ^ (208 * t)
    let Y := D ^ (8 * t)
    ∃ x : Fin M → Fin D → ℝ,
      (∀ i₁ i₂ i₃ : Fin M, ¬ (i₁ = i₂ ∧ i₂ = i₃) →
        ∃ b : Fin D, 10 * ρ < tdist (x i₁ b - 2 * x i₂ b + x i₃ b)) ∧
      (∀ (S0 : Set (Fin D → ℤ)),
        Module.finrank ℚ (Submodule.span ℚ ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) '' S0)) ≤ 2 * t →
        ∀ xstar : Fin D → ℝ,
        ∃ (j : Fin Y → Fin M) (u : Fin Y → Fin D → ℝ),
          Function.Injective j ∧
          (∀ k : Fin Y, ∑ b : Fin D, (u k b) ^ 2 < (ρ / 10) ^ 2) ∧
          (∀ k : Fin Y, ∀ ξ ∈ S0, (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) →
            tdist (∑ b : Fin D, (ξ b : ℝ) * (x (j k) b + u k b - xstar b)) < 1 / 100)) := by
  intro D ρ M Y
  have hD_ge : 60000 ≤ D := by dsimp only [D]; omega
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hρ_pos : 0 < ρ := inv_pos.mpr (pow_pos hD_pos 4)
  -- Choose a huge prime P
  let Pbound : ℕ := max 1000 (max ((2 * t).factorial * (D ^ 13) ^ (2 * t) + 1) (4 * D ^ (72 * t) + D ^ 10))
  obtain ⟨P, hP_ge, hP_prime⟩ := Nat.exists_infinite_primes Pbound
  have : Fact P.Prime := ⟨hP_prime⟩
  have hP_pos : 0 < P := hP_prime.pos
  have hP_gt2 : 2 < P := by
    have : 1000 ≤ P := le_trans (le_max_left _ _) hP_ge; omega
  have hP_R : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_pos
  -- Type of all center configurations: Ω = Fin M → Fin D → ZMod P
  let Ω := Fin M → Fin D → ZMod P
  have hΩ_card : Fintype.card Ω = P ^ (D * M) := by
    simp [Ω, ZMod.card, pow_mul]
  have hΩ_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos (α := Ω)
  -- Helper: real embedding of ω : Ω
  let toR (ω : Ω) (i : Fin M) (b : Fin D) : ℝ := embed P (ω i b)
  -- Bad Event F1: some non-constant triple has tdist ≤ 10 ρ in all coords
  let triples : Finset (Fin M × Fin M × Fin M) :=
    Finset.univ.filter (fun p => ¬ (p.1 = p.2.1 ∧ p.2.1 = p.2.2))
  let bad1Of (p : Fin M × Fin M × Fin M) : Finset Ω :=
    Finset.univ.filter (fun ω => ∀ b : Fin D, tdist (toR ω p.1 b - 2 * toR ω p.2.1 b + toR ω p.2.2 b) ≤ 10 * ρ)
  let F1 : Finset Ω := triples.biUnion bad1Of
  have hbad1_card : ∀ p ∈ triples, ((bad1Of p).card : ℝ) ≤ (21 * ρ) ^ D * (Fintype.card Ω : ℝ) := by
    intro p hp
    have hne : ¬ (p.1 = p.2.1 ∧ p.2.1 = p.2.2) := (Finset.mem_filter.mp hp).2
    -- Define the linear map L : Ω → (Fin D → ZMod P) sending ω ↦ ω p.1 - 2 ω p.2.1 + ω p.2.2
    let L : Ω →ₗ[ZMod P] (Fin D → ZMod P) :=
      { toFun := fun ω b => ω p.1 b - 2 * ω p.2.1 b + ω p.2.2 b
        map_add' := fun ω₁ ω₂ => by ext b; dsimp only [Ω]; simp only [Pi.add_apply]; ring
        map_smul' := fun c ω => by ext b; dsimp only [Ω]; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hL_surj : Function.Surjective L := by
      have htwo_ne : (2 : ZMod P) ≠ 0 := by
        intro h2
        have hdvd : P ∣ 2 := (ZMod.natCast_eq_zero_iff 2 P).mp (by simpa using h2)
        have := Nat.le_of_dvd (by omega) hdvd; omega
      intro y
      by_cases h12 : p.1 = p.2.1
      · have h23 : p.2.1 ≠ p.2.2 := fun h => hne ⟨h12, h⟩
        refine ⟨fun i b => if i = p.2.2 then y b else 0, funext fun b => ?_⟩
        simp [L, h12, h23]
      · by_cases h13 : p.1 = p.2.2
        · refine ⟨fun i b => if i = p.2.1 then -(2 : ZMod P)⁻¹ * y b else 0, funext fun b => ?_⟩
          simp only [L, LinearMap.coe_mk, AddHom.coe_mk, h13.symm, h12, ↓reduceIte, zero_sub,
            add_zero]
          rw [← mul_assoc, mul_neg, neg_mul, neg_neg, mul_inv_cancel₀ htwo_ne, one_mul]
        · refine ⟨fun i b => if i = p.1 then y b else 0, funext fun b => ?_⟩
          simp [L, Ne.symm h12, Ne.symm h13]
    let smallVecs : Finset (Fin D → ZMod P) :=
      Fintype.piFinset (fun _ : Fin D => Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ 10 * ρ))
    have hsub : bad1Of p ⊆ Finset.univ.filter (fun ω : Ω => L ω ∈ smallVecs) := by
      intro ω hω
      simp only [bad1Of, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [Fintype.mem_piFinset]
      intro b
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      -- Show L ω b has same tdist as toR ω p.1 b - 2 * toR ω p.2.1 b + toR ω p.2.2 b
      obtain ⟨m1, hm1⟩ := embed_add_sub (P := P) (ω p.1 b) (-(2 : ZMod P) * ω p.2.1 b + ω p.2.2 b)
      obtain ⟨m2, hm2⟩ := embed_add_sub (P := P) (-(2 : ZMod P) * ω p.2.1 b) (ω p.2.2 b)
      obtain ⟨m3, hm3⟩ := embed_int_mul_sub (P := P) (-2) (ω p.2.1 b)
      have hLeq : L ω b = ω p.1 b + ((-(2 : ℤ) : ZMod P) * ω p.2.1 b + ω p.2.2 b) := by
        change ω p.1 b - 2 * ω p.2.1 b + ω p.2.2 b = _; push_cast; ring
      have hdiff : embed P (L ω b) - (toR ω p.1 b - 2 * toR ω p.2.1 b + toR ω p.2.2 b) =
          ((m1 + m2 + m3 : ℤ) : ℝ) := by
        rw [hLeq]
        have hm1' : embed P (ω p.1 b + ((-(2 : ℤ) : ZMod P) * ω p.2.1 b + ω p.2.2 b)) -
            (embed P (ω p.1 b) + embed P ((-(2 : ℤ) : ZMod P) * ω p.2.1 b + ω p.2.2 b)) = (m1 : ℝ) := by
          simpa using hm1
        have hm2' : embed P ((-(2 : ℤ) : ZMod P) * ω p.2.1 b + ω p.2.2 b) -
            (embed P ((-(2 : ℤ) : ZMod P) * ω p.2.1 b) + embed P (ω p.2.2 b)) = (m2 : ℝ) := by
          simpa using hm2
        dsimp only [toR]
        push_cast at hm3 ⊢
        linarith
      rw [tdist_eq_of_sub_int (m1 + m2 + m3) hdiff]
      exact hω b
    have hpre := card_preimage_of_surjective_linearMap L hL_surj smallVecs
    have hWcard : Fintype.card (Fin D → ZMod P) = P ^ D := by simp [ZMod.card]
    have hsmall_card : (smallVecs.card : ℝ) ≤ (21 * ρ * P) ^ D := by
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
      have h1 : ((Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ 10 * ρ)).card : ℝ) ≤
          21 * ρ * P := by
        have hc : ((Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ 10 * ρ)).card : ℝ) ≤
            2 * (Nat.floor (10 * ρ * P) : ℝ) + 1 := by
          exact_mod_cast card_zmod_tdist_le (P := P) (τ := 10 * ρ) (by positivity)
        have hfl : (Nat.floor (10 * ρ * P) : ℝ) ≤ 10 * ρ * P := Nat.floor_le (by positivity)
        have hP_big : (D : ℝ) ^ 4 ≤ (P : ℝ) := by
          have : D ^ 10 ≤ P := by
            have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hP_ge); omega
          have : D ^ 4 ≤ D ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
          exact_mod_cast le_trans this (by omega)
        have hρP : 1 ≤ ρ * P := by
          dsimp only [ρ]
          rw [inv_mul_eq_div, one_le_div (pow_pos hD_pos 4)]
          exact hP_big
        linarith
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) h1 D
    have hpreR : ((Finset.univ.filter (fun ω : Ω => L ω ∈ smallVecs)).card : ℝ) * (P : ℝ) ^ D =
        (smallVecs.card : ℝ) * (Fintype.card Ω : ℝ) := by
      have hpre_nat : (Finset.univ.filter (fun ω : Ω => L ω ∈ smallVecs)).card * P ^ D =
          smallVecs.card * Fintype.card Ω := by rw [← hWcard]; convert hpre
      exact_mod_cast hpre_nat
    have hcard_le : ((bad1Of p).card : ℝ) ≤
        ((Finset.univ.filter (fun ω : Ω => L ω ∈ smallVecs)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hPD_pos : (0 : ℝ) < (P : ℝ) ^ D := pow_pos hP_R D
    have hfinal : ((bad1Of p).card : ℝ) * (P : ℝ) ^ D ≤ (21 * ρ * P) ^ D * (Fintype.card Ω : ℝ) := by
      calc ((bad1Of p).card : ℝ) * (P : ℝ) ^ D
          ≤ ((Finset.univ.filter (fun ω : Ω => L ω ∈ smallVecs)).card : ℝ) * (P : ℝ) ^ D :=
            mul_le_mul_of_nonneg_right hcard_le hPD_pos.le
        _ = (smallVecs.card : ℝ) * (Fintype.card Ω : ℝ) := hpreR
        _ ≤ (21 * ρ * P) ^ D * (Fintype.card Ω : ℝ) :=
            mul_le_mul_of_nonneg_right hsmall_card hΩ_pos.le
    rw [mul_pow] at hfinal
    nlinarith [hPD_pos]
  have hF1_lt : (F1.card : ℝ) < (1 / 4 : ℝ) * (Fintype.card Ω : ℝ) := by
    have hbi : (F1.card : ℝ) ≤ (M : ℝ) ^ 3 * ((21 * ρ) ^ D * (Fintype.card Ω : ℝ)) := by
      have h1 : F1.card ≤ ∑ p ∈ triples, (bad1Of p).card := Finset.card_biUnion_le
      have h1R : (F1.card : ℝ) ≤ ∑ p ∈ triples, ((bad1Of p).card : ℝ) := by exact_mod_cast h1
      have htri_card : (triples.card : ℝ) ≤ (M : ℝ) ^ 3 := by
        have : triples.card ≤ Fintype.card (Fin M × Fin M × Fin M) := Finset.card_le_univ _
        have : triples.card ≤ M ^ 3 := by simpa [pow_succ, mul_assoc] using this
        exact_mod_cast this
      calc (F1.card : ℝ) ≤ ∑ p ∈ triples, ((bad1Of p).card : ℝ) := h1R
        _ ≤ ∑ _p ∈ triples, ((21 * ρ) ^ D * (Fintype.card Ω : ℝ)) :=
            Finset.sum_le_sum fun p hp => hbad1_card p hp
        _ = (triples.card : ℝ) * ((21 * ρ) ^ D * (Fintype.card Ω : ℝ)) := by simp
        _ ≤ (M : ℝ) ^ 3 * ((21 * ρ) ^ D * (Fintype.card Ω : ℝ)) :=
            mul_le_mul_of_nonneg_right htri_card (by positivity)
    have hfactor : (M : ℝ) ^ 3 * (21 * ρ) ^ D < 1 / 4 := by
      have h21 : (21 : ℝ) ^ 2 ≤ (D : ℝ) := by
        have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
        linarith
      have h21D : (21 : ℝ) ^ D ≤ (D : ℝ) ^ (100 * t) := by
        calc (21 : ℝ) ^ D = ((21 : ℝ) ^ 2) ^ (100 * t) := by
              rw [← pow_mul]; dsimp only [D]; congr 1; omega
          _ ≤ (D : ℝ) ^ (100 * t) := pow_le_pow_left₀ (by norm_num) h21 _
      have hM3 : (M : ℝ) ^ 3 = (D : ℝ) ^ (624 * t) := by
        dsimp only [M]; rw [Nat.cast_pow, ← pow_mul]; congr 1; ring
      have hρD : ρ ^ D = ((D : ℝ) ^ (800 * t))⁻¹ := by
        dsimp only [ρ, D]; rw [inv_pow, ← pow_mul]; congr 2; ring
      rw [hM3, mul_pow, hρD]
      have hle : (D : ℝ) ^ (624 * t) * ((21 : ℝ) ^ D * ((D : ℝ) ^ (800 * t))⁻¹) ≤
          ((D : ℝ) ^ (76 * t))⁻¹ := by
        have hnum : (D : ℝ) ^ (624 * t) * (21 : ℝ) ^ D ≤ (D : ℝ) ^ (724 * t) := by
          calc (D : ℝ) ^ (624 * t) * (21 : ℝ) ^ D
              ≤ (D : ℝ) ^ (624 * t) * (D : ℝ) ^ (100 * t) :=
                mul_le_mul_of_nonneg_left h21D (by positivity)
            _ = (D : ℝ) ^ (724 * t) := by rw [← pow_add]; congr 1; omega
        rw [← mul_assoc]
        calc (D : ℝ) ^ (624 * t) * (21 : ℝ) ^ D * ((D : ℝ) ^ (800 * t))⁻¹
            ≤ (D : ℝ) ^ (724 * t) * ((D : ℝ) ^ (800 * t))⁻¹ :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = ((D : ℝ) ^ (76 * t))⁻¹ := by
              have h800 : (D : ℝ) ^ (800 * t) = (D : ℝ) ^ (724 * t) * (D : ℝ) ^ (76 * t) := by
                rw [← pow_add]; congr 1; omega
              rw [h800, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hD_pos.ne'), one_mul]
      have hD76 : (4 : ℝ) < (D : ℝ) ^ (76 * t) := by
        have h1 : (4 : ℝ) < (D : ℝ) := by
          have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
          linarith
        calc (4 : ℝ) < (D : ℝ) := h1
          _ = (D : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (D : ℝ) ^ (76 * t) := pow_le_pow_right₀ (by linarith) (by omega)
      calc (D : ℝ) ^ (624 * t) * ((21 : ℝ) ^ D * ((D : ℝ) ^ (800 * t))⁻¹)
          ≤ ((D : ℝ) ^ (76 * t))⁻¹ := hle
        _ < (4 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) hD76
        _ = 1 / 4 := by norm_num
    nlinarith [hbi, hfactor, hΩ_pos]
  -- Bad Event F2: partition Fin M into Y blocks of size S = D ^ (200 * t)
  let S : ℕ := D ^ (200 * t)
  have hMSY : Y * S = M := by dsimp only [Y, S, M]; rw [← pow_add]; congr 1; omega
  let blockIdx (y : Fin Y) (s : Fin S) : Fin M :=
    ⟨y.val * S + s.val, by
      have hy := y.isLt; have hs := s.isLt
      have h1 : (y.val + 1) * S ≤ Y * S := Nat.mul_le_mul_right S hy
      have h2 : (y.val + 1) * S = y.val * S + S := by rw [Nat.add_mul, one_mul]
      omega⟩
  have hblockIdx_inj : Function.Injective (fun p : Fin Y × Fin S => blockIdx p.1 p.2) := by
    intro ⟨y1, s1⟩ ⟨y2, s2⟩ h
    have hv : y1.val * S + s1.val = y2.val * S + s2.val := congrArg Fin.val h
    have hs1 := s1.isLt; have hs2 := s2.isLt
    have hq : y1.val = y2.val := by
      have h1 := congrArg (· / S) hv
      have hSpos : 0 < S := Nat.pow_pos (by omega)
      rw [mul_comm y1.val S, mul_comm y2.val S, Nat.mul_add_div hSpos, Nat.mul_add_div hSpos,
        Nat.div_eq_of_lt hs1, Nat.div_eq_of_lt hs2] at h1
      simpa using h1
    have hr : s1.val = s2.val := by rw [hq] at hv; omega
    exact Prod.ext (Fin.ext hq) (Fin.ext hr)
  -- Index all m ∈ [1, 2t] and bounded linearly independent m-tuples in [-D^12, D^12]^D
  let Q : ℕ := D ^ 12
  let BndVec := Fin D → Finset.Icc (-(Q : ℤ)) (Q : ℤ)
  -- For each valid (m, v) with 1 ≤ m ≤ 2t and v linearly independent, choose Mahler short basis w!
  let wOf (m : Fin (2 * t)) (v : Fin (m.val + 1) → BndVec)
      (hind : LinearIndependent ℚ (fun i b => ((v i b).1 : ℚ))) : Fin (m.val + 1) → Fin D → ℤ :=
    (mahler_short_basis (m := m.val + 1) (D := D) (Q := Q) (by omega) (Nat.pow_pos (by omega))
      (fun i b => (v i b).1) (fun i b => abs_le.mpr (Finset.mem_Icc.mp (v i b).2)) hind).choose
  let BadPairOf (y : Fin Y) (m : Fin (2 * t)) (v : Fin (m.val + 1) → BndVec)
      (hind : LinearIndependent ℚ (fun i b => ((v i b).1 : ℚ))) : Finset Ω :=
    @Finset.filter Ω (fun ω : Ω =>
      ∃ k : Fin (m.val + 1) → Fin (2 * D ^ (36 * (m.val + 1))),
        ∀ (s : Fin S) (u : Fin D → ℝ),
          (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
          ¬ ∀ i : Fin (m.val + 1),
            ((k i : ℕ) : ℝ) / ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ) ≤
              Int.fract (∑ b : Fin D, (wOf m v hind i b : ℝ) * (toR ω (blockIdx y s) b + u b)) ∧
            Int.fract (∑ b : Fin D, (wOf m v hind i b : ℝ) * (toR ω (blockIdx y s) b + u b)) <
              (((k i : ℕ) + 1 : ℕ) : ℝ) / ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ))
      (Classical.decPred _) Finset.univ
  let BadPair (y : Fin Y) (m : Fin (2 * t)) (v : Fin (m.val + 1) → BndVec) : Finset Ω :=
    if hind : LinearIndependent ℚ (fun i b => ((v i b).1 : ℚ)) then BadPairOf y m v hind else ∅
  have hmem_BadPair : ∀ (y : Fin Y) (m : Fin (2 * t)) (v : Fin (m.val + 1) → BndVec)
      (hind : LinearIndependent ℚ (fun i b => ((v i b).1 : ℚ))) (ω : Ω),
      (∃ k : Fin (m.val + 1) → Fin (2 * D ^ (36 * (m.val + 1))),
        ∀ (s : Fin S) (u : Fin D → ℝ),
          (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
          ¬ ∀ i : Fin (m.val + 1),
            ((k i : ℕ) : ℝ) / ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ) ≤
              Int.fract (∑ b : Fin D, (wOf m v hind i b : ℝ) * (toR ω (blockIdx y s) b + u b)) ∧
            Int.fract (∑ b : Fin D, (wOf m v hind i b : ℝ) * (toR ω (blockIdx y s) b + u b)) <
              (((k i : ℕ) + 1 : ℕ) : ℝ) / ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ)) →
      ω ∈ BadPair y m v := by
    intro y m v hind ω hex
    dsimp only [BadPair]
    split_ifs with h
    dsimp only [BadPairOf]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hex
  -- Bound the cardinality of BadPair y m v!
  have hBadPair_card : ∀ (y : Fin Y) (m : Fin (2 * t)) (v : Fin (m.val + 1) → BndVec),
      ((BadPair y m v).card : ℝ) ≤
        ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ) ^ (m.val + 1) *
          Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) := by
    intro y m v
    dsimp only [BadPair]
    split_ifs with hind
    · dsimp only [BadPairOf]
      let m' := m.val + 1
      have hm'_ge : 1 ≤ m' := by omega
      have hm'_le : m' ≤ 2 * t := by have := m.isLt; omega
      have hspec := (mahler_short_basis (m := m.val + 1) (D := D) (Q := Q) (by omega) (Nat.pow_pos (by omega))
        (fun i b => (v i b).1) (fun i b => abs_le.mpr (Finset.mem_Icc.mp (v i b).2)) hind).choose_spec
      let w : Fin m' → Fin D → ℤ := wOf m v hind
      obtain ⟨hw_ind, hw_bd, -, -⟩ := hspec
      set G : ℕ := 2 * D ^ (36 * m')
      have hG_pos : 1 ≤ G := by dsimp only [G]; have := Nat.pow_pos (show 0 < D by omega) (n := 36 * m'); omega
      have hG_R : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hG_pos
      have h2G_le_P : 2 * G ≤ P := by
        have h1 : 36 * m' ≤ 72 * t := by omega
        have h2 : D ^ (36 * m') ≤ D ^ (72 * t) := Nat.pow_le_pow_right (by omega) h1
        have h3 : 4 * D ^ (72 * t) ≤ P := by
          have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hP_ge); omega
        dsimp only [G]; omega
      -- Linear map φ : (Fin D → ZMod P) →ₗ[ZMod P] (Fin m' → ZMod P)
      let φ : (Fin D → ZMod P) →ₗ[ZMod P] (Fin m' → ZMod P) :=
        { toFun := fun z i => ∑ b : Fin D, (w i b : ZMod P) * z b
          map_add' := fun z1 z2 => by ext i; simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun c z => by
            ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring }
      have hφ_surj : Function.Surjective φ := by
        apply surjective_dot_map_zmod w (D ^ 13)
        · intro i b
          have h1 := hw_bd i b
          have hmD : (m' : ℤ) ≤ (D : ℤ) := by exact_mod_cast (show m' ≤ D by dsimp only [D]; omega)
          have h2 : (m' : ℤ) * (Q : ℤ) ≤ (D : ℤ) ^ 13 := by
            dsimp only [Q]; push_cast
            calc (m' : ℤ) * (D : ℤ) ^ 12 ≤ (D : ℤ) * (D : ℤ) ^ 12 :=
                  mul_le_mul_of_nonneg_right hmD (by positivity)
              _ = (D : ℤ) ^ 13 := by ring
          exact h1.trans h2
        · exact hw_ind
        · have hfac : m'.factorial ≤ (2 * t).factorial := Nat.factorial_le hm'_le
          have hpow : (D ^ 13) ^ m' ≤ (D ^ 13) ^ (2 * t) :=
            Nat.pow_le_pow_right (Nat.pow_pos (by omega)) hm'_le
          have hP1 : (2 * t).factorial * (D ^ 13) ^ (2 * t) < P := by
            have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hP_ge); omega
          exact lt_of_le_of_lt (Nat.mul_le_mul hfac hpow) hP1
      -- Construct the finite set U of well-spaced shifts u ∈ B_{ρ/10}(0)
      let Nstep : ℕ := D ^ (36 * m' - 30)
      let uOf (c : Fin m' → Fin Nstep) : Fin D → ℝ :=
        fun b => (∑ i : Fin m', ((c i : ℕ) : ℝ) * (w i b : ℝ)) / (G : ℝ)
      have hw_bd_D13 : ∀ i b, |(w i b : ℝ)| ≤ (D : ℝ) ^ 13 := by
        intro i b
        have h1 : |(w i b : ℝ)| ≤ (m' : ℝ) * (Q : ℝ) := by exact_mod_cast hw_bd i b
        have hmD : (m' : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show m' ≤ D by dsimp only [D]; omega)
        calc |(w i b : ℝ)| ≤ (m' : ℝ) * (D : ℝ) ^ 12 := by simpa [Q] using h1
          _ ≤ (D : ℝ) * (D : ℝ) ^ 12 := mul_le_mul_of_nonneg_right hmD (by positivity)
          _ = (D : ℝ) ^ 13 := by ring
      have hu_inf : ∀ c : Fin m' → Fin Nstep, ∀ b : Fin D, |uOf c b| ≤ 1 / (4 * (D : ℝ) ^ 15) := by
        intro c b
        dsimp only [uOf]
        rw [abs_div, abs_of_pos hG_R, div_le_div_iff₀ hG_R (by positivity)]
        have hsum : |∑ i : Fin m', ((c i : ℕ) : ℝ) * (w i b : ℝ)| ≤
            (m' : ℝ) * (Nstep : ℝ) * (D : ℝ) ^ 13 := by
          calc |∑ i : Fin m', ((c i : ℕ) : ℝ) * (w i b : ℝ)|
              ≤ ∑ i : Fin m', |((c i : ℕ) : ℝ) * (w i b : ℝ)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin m', (Nstep : ℝ) * (D : ℝ) ^ 13 := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
                exact mul_le_mul (by exact_mod_cast (c i).isLt.le) (hw_bd_D13 i b)
                  (abs_nonneg _) (Nat.cast_nonneg _)
            _ = (m' : ℝ) * (Nstep : ℝ) * (D : ℝ) ^ 13 := by simp [mul_assoc]
        have hG_eq : (G : ℝ) = 2 * (D : ℝ) ^ (36 * m') := by dsimp only [G]; push_cast; rfl
        have hN_eq : (Nstep : ℝ) = (D : ℝ) ^ (36 * m' - 30) := by dsimp only [Nstep]; push_cast; rfl
        have hmD : 2 * (m' : ℝ) ≤ (D : ℝ) ^ 2 := by
          have : 2 * m' ≤ D := by dsimp only [D]; omega
          have h1 : (2 * m' : ℝ) ≤ (D : ℝ) := by exact_mod_cast this
          have h2 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
          nlinarith
        rw [hN_eq] at hsum
        rw [hG_eq]
        have hexp : 36 * m' - 30 + 13 + 15 + 2 = 36 * m' := by omega
        calc |∑ i : Fin m', ((c i : ℕ) : ℝ) * (w i b : ℝ)| * (4 * (D : ℝ) ^ 15)
            ≤ ((m' : ℝ) * (D : ℝ) ^ (36 * m' - 30) * (D : ℝ) ^ 13) * (4 * (D : ℝ) ^ 15) :=
              mul_le_mul_of_nonneg_right hsum (by positivity)
          _ = 2 * (2 * (m' : ℝ)) * (D : ℝ) ^ (36 * m' - 30 + 13 + 15) := by
              rw [pow_add, pow_add]; ring
          _ ≤ 2 * (D : ℝ) ^ 2 * (D : ℝ) ^ (36 * m' - 30 + 13 + 15) := by
              have : (0 : ℝ) ≤ (D : ℝ) ^ (36 * m' - 30 + 13 + 15) := by positivity
              nlinarith
          _ = 2 * (D : ℝ) ^ (36 * m') := by
              rw [mul_assoc, ← pow_add, show 2 + (36 * m' - 30 + 13 + 15) = 36 * m' by omega]
          _ = 1 * (2 * (D : ℝ) ^ (36 * m')) := (one_mul _).symm
      have hu_norm : ∀ c : Fin m' → Fin Nstep, ∑ b : Fin D, (uOf c b) ^ 2 < (ρ / 10) ^ 2 := by
        intro c
        calc ∑ b : Fin D, (uOf c b) ^ 2
            ≤ ∑ _b : Fin D, (1 / (4 * (D : ℝ) ^ 15)) ^ 2 := by
              refine Finset.sum_le_sum fun b _ => ?_
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hu_inf c b) 2
          _ = (D : ℝ) / (16 * (D : ℝ) ^ 30) := by simp [mul_pow, ← pow_mul]; ring
          _ < (ρ / 10) ^ 2 := by
              dsimp only [ρ]
              rw [div_pow, inv_pow, ← pow_mul, inv_eq_one_div, div_div]
              rw [div_lt_div_iff₀ (by positivity) (by positivity)]
              have hD10 : (100 : ℝ) < (D : ℝ) ^ 21 := by
                have hD2 : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
                calc (100 : ℝ) < (D : ℝ) := by linarith
                  _ = (D : ℝ) ^ 1 := (pow_one _).symm
                  _ ≤ (D : ℝ) ^ 21 := pow_le_pow_right₀ (by linarith) (by omega)
              have hpow : (D : ℝ) ^ 30 = (D : ℝ) ^ 9 * (D : ℝ) ^ 21 := by rw [← pow_add]
              have hD9 : (D : ℝ) * (D : ℝ) ^ (4 * 2) = (D : ℝ) ^ 9 := by ring
              nlinarith [pow_pos hD_pos 9, hD10, hpow, hD9]
      -- For fixed box k : Fin m' → Fin G, bound the single-vector hit count!
      have hsingle_hit : ∀ k : Fin m' → Fin G,
          let hitSet := Finset.univ.filter (fun z : Fin D → ZMod P =>
            ∃ c : Fin m' → Fin Nstep, ∀ i : Fin m',
              ((k i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) ∧
              Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) <
                (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ))
          ((D : ℝ) ^ (62 * t))⁻¹ * (P : ℝ) ^ D ≤ (hitSet.card : ℝ) := by
        intro k
        dsimp only
        let hitOf (c : Fin m' → Fin Nstep) : Finset (Fin D → ZMod P) :=
          Finset.univ.filter (fun z => ∀ i : Fin m',
            ((k i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) ∧
            Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) <
              (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ))
        -- Distinct c1 ≠ c2 give DISJOINT hitOf c1 and hitOf c2!
        have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin m' → Fin Nstep)) hitOf := by
          intro c1 _ c2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          simp only [hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
          let η : Fin D → ℤ := fun b => ∑ i : Fin m', (((c1 i : ℕ) : ℤ) - ((c2 i : ℕ) : ℤ)) * w i b
          have hη_ne : ∃ b : Fin D, η b ≠ 0 := by
            by_contra hall; push Not at hall
            have hlin : ∑ i : Fin m', ((((c1 i : ℕ) : ℤ) - ((c2 i : ℕ) : ℤ) : ℤ) : ℚ) •
                (fun b => (w i b : ℚ)) = 0 := by
              ext b; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
              have : (η b : ℚ) = 0 := by rw [hall b]; simp
              simpa [η] using this
            have hcoeff := (linearIndependent_iff'.mp hw_ind) Finset.univ _ hlin
            apply hne; funext i
            have hi0 : ((((c1 i : ℕ) : ℤ) - ((c2 i : ℕ) : ℤ) : ℤ) : ℚ) = 0 := hcoeff i (Finset.mem_univ i)
            have : ((c1 i : ℕ) : ℤ) - ((c2 i : ℕ) : ℤ) = 0 := by exact_mod_cast hi0
            exact Fin.ext (by omega)
          -- Since η ≠ 0 and η = ∑ d_i w_i, ∑ d_i (w_i · η) = ∑ (η b)^2 > 0, so some w_i · η ≠ 0!
          have hdot_ne : ∃ i : Fin m', ∑ b : Fin D, w i b * η b ≠ 0 := by
            by_contra hall; push Not at hall
            have hsq0 : ∑ b : Fin D, (η b) ^ 2 = 0 := by
              calc ∑ b : Fin D, (η b) ^ 2 = ∑ b : Fin D, η b * η b := by simp [sq]
                _ = ∑ b : Fin D, (∑ i : Fin m', (((c1 i : ℕ) : ℤ) - ((c2 i : ℕ) : ℤ)) * w i b) * η b := rfl
                _ = ∑ i : Fin m', (((c1 i : ℕ) : ℤ) - ((c2 i : ℕ) : ℤ)) * ∑ b : Fin D, w i b * η b := by
                    simp_rw [Finset.sum_mul, mul_assoc, Finset.mul_sum]; rw [Finset.sum_comm]
                _ = 0 := by simp [hall]
            obtain ⟨b0, hb0⟩ := hη_ne
            have hpos : 0 < (η b0) ^ 2 := sq_pos_of_ne_zero hb0
            have hle : (η b0) ^ 2 ≤ ∑ b : Fin D, (η b) ^ 2 :=
              Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ b0)
            omega
          obtain ⟨i, hi_ne⟩ := hdot_ne
          -- Compute diff = ∑ w i b * (uOf c1 b - uOf c2 b) = (∑ w i b * η b) / G
          let diff := (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c1 b)) -
                      (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c2 b))
          have hdiff_eq : diff = ((∑ b : Fin D, w i b * η b : ℤ) : ℝ) / (G : ℝ) := by
            dsimp only [diff, uOf, η]
            rw [← Finset.sum_sub_distrib, Int.cast_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun b _ => ?_
            push_cast
            field_simp [hG_R.ne']
            congr 1
            rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => by ring
          have hdiff_lt_half : |diff| < 1 / 2 := by
            have hdiff_u : diff = ∑ b : Fin D, (w i b : ℝ) * (uOf c1 b - uOf c2 b) := by
              dsimp only [diff]; rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun b _ => by ring
            rw [hdiff_u]
            calc |∑ b : Fin D, (w i b : ℝ) * (uOf c1 b - uOf c2 b)|
                ≤ ∑ b : Fin D, |(w i b : ℝ) * (uOf c1 b - uOf c2 b)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _b : Fin D, (D : ℝ) ^ 13 * (2 / (4 * (D : ℝ) ^ 15)) := by
                  refine Finset.sum_le_sum fun b _ => ?_
                  rw [abs_mul]
                  have hu12 : |uOf c1 b - uOf c2 b| ≤ 2 / (4 * (D : ℝ) ^ 15) := by
                    calc |uOf c1 b - uOf c2 b| ≤ |uOf c1 b| + |uOf c2 b| := abs_sub _ _
                      _ ≤ 1 / (4 * (D : ℝ) ^ 15) + 1 / (4 * (D : ℝ) ^ 15) :=
                          add_le_add (hu_inf c1 b) (hu_inf c2 b)
                      _ = 2 / (4 * (D : ℝ) ^ 15) := by ring
                  exact mul_le_mul (hw_bd_D13 i b) hu12 (abs_nonneg _) (by positivity)
              _ = 1 / (2 * (D : ℝ)) := by simp; field_simp [hD_pos.ne']; ring
              _ < 1 / 2 := by
                  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
                  have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
                  linarith
          have htd_ge : 1 / (G : ℝ) ≤ tdist diff := by
            rw [tdist_eq_abs_of_le_half hdiff_lt_half.le, hdiff_eq, abs_div, abs_of_pos hG_R]
            apply div_le_div_of_nonneg_right _ hG_R.le
            have : (1 : ℤ) ≤ |∑ b : Fin D, w i b * η b| := by
              have := abs_pos.mpr hi_ne; omega
            exact_mod_cast this
          have htd_lt : tdist diff < 1 / (G : ℝ) := by
            have hki := hz1 i
            have hki2 := hz2 i
            have hcast : (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ) = ((k i : ℕ) : ℝ) / (G : ℝ) + 1 / (G : ℝ) := by
              push_cast; ring
            rw [hcast] at hki hki2
            exact tdist_fract_lt_of_same_interval hki.1 hki.2 hki2.1 hki2.2
          linarith
        -- Lower bound each |hitOf c| via surjective linear map φ!
        have hhitOf_lb : ∀ c : Fin m' → Fin Nstep,
            (P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m') ≤ ((hitOf c).card : ℝ) := by
          intro c
          let β : Fin m' → ℝ := fun i => ∑ b : Fin D, (w i b : ℝ) * uOf c b
          let targetBox : Finset (Fin m' → ZMod P) :=
            Fintype.piFinset (fun i : Fin m' =>
              Finset.univ.filter (fun a : ZMod P =>
                ((k i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (embed P a + β i) ∧
                Int.fract (embed P a + β i) < (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ)))
          have hsub : Finset.univ.filter (fun z => φ z ∈ targetBox) ⊆ hitOf c := by
            intro z hz
            simp only [targetBox, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hitOf] at hz ⊢
            intro i
            have hi := hz i
            obtain ⟨m_int, hm_int⟩ := embed_sum_int_mul_sub (P := P) Finset.univ (w i) z
            have hsum_eq : ∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b) =
                (embed P (φ z i) + β i) + (-(m_int : ℝ)) := by
              change ∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b) =
                (embed P (∑ b : Fin D, (w i b : ZMod P) * z b) + ∑ b : Fin D, (w i b : ℝ) * uOf c b) + (-(m_int : ℝ))
              simp_rw [mul_add, Finset.sum_add_distrib]
              linarith
            rw [hsum_eq, ← Int.cast_neg, Int.fract_add_intCast]
            exact hi
          have hpre := card_preimage_of_surjective_linearMap φ hφ_surj targetBox
          have hbox_lb : (P / G) ^ m' ≤ targetBox.card := by
            rw [Fintype.card_piFinset]
            calc (P / G) ^ m' = ∏ _i : Fin m', (P / G) := by simp
              _ ≤ ∏ i : Fin m', _ := Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
                  (fun i _ => card_zmod_fract_in_interval hG_pos (by omega) (k i) (β i))
          have hPG_lb : (P : ℝ) / (2 * (G : ℝ)) ≤ ((P / G : ℕ) : ℝ) := by
            have hdiv : P < (P / G + 1) * G := by
              have := Nat.lt_div_mul_add (a := P) (b := G) (by omega); linarith
            have hPG2 : 2 * G ≤ P := h2G_le_P
            have h1 : 1 ≤ P / G := Nat.div_pos (by omega) (by omega)
            have h2 : P ≤ 2 * (P / G) * G := by nlinarith
            have h2R : (P : ℝ) ≤ 2 * ((P / G : ℕ) : ℝ) * (G : ℝ) := by exact_mod_cast h2
            rw [div_le_iff₀ (by positivity)]
            linarith
          have hpreR : ((Finset.univ.filter (fun z => φ z ∈ targetBox)).card : ℝ) * (P : ℝ) ^ m' =
              (targetBox.card : ℝ) * (P : ℝ) ^ D := by
            have hpre_nat : (Finset.univ.filter (fun z => φ z ∈ targetBox)).card * P ^ m' =
                targetBox.card * P ^ D := by
              rw [Fintype.card_fun, ZMod.card, Fintype.card_fin,
                  Fintype.card_fun, ZMod.card, Fintype.card_fin] at hpre
              convert hpre
            exact_mod_cast hpre_nat
          have hboxR : ((P : ℝ) / (2 * (G : ℝ))) ^ m' ≤ (targetBox.card : ℝ) := by
            calc ((P : ℝ) / (2 * (G : ℝ))) ^ m' ≤ ((P / G : ℕ) : ℝ) ^ m' :=
                  pow_le_pow_left₀ (by positivity) hPG_lb m'
              _ ≤ (targetBox.card : ℝ) := by exact_mod_cast hbox_lb
          have h2G : 2 * (G : ℝ) = 4 * (D : ℝ) ^ (36 * m') := by dsimp only [G]; push_cast; ring
          have hcard_ge : ((Finset.univ.filter (fun z => φ z ∈ targetBox)).card : ℝ) ≤ ((hitOf c).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          have hPm_pos : (0 : ℝ) < (P : ℝ) ^ m' := pow_pos hP_R m'
          have hstep : (P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m') * (P : ℝ) ^ m' ≤
              ((hitOf c).card : ℝ) * (P : ℝ) ^ m' := by
            calc (P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m') * (P : ℝ) ^ m'
                = ((P : ℝ) / (2 * (G : ℝ))) ^ m' * (P : ℝ) ^ D := by
                  rw [h2G, div_pow, mul_pow]; field_simp [hD_pos.ne']
              _ ≤ (targetBox.card : ℝ) * (P : ℝ) ^ D :=
                  mul_le_mul_of_nonneg_right hboxR (by positivity)
              _ = ((Finset.univ.filter (fun z => φ z ∈ targetBox)).card : ℝ) * (P : ℝ) ^ m' := hpreR.symm
              _ ≤ ((hitOf c).card : ℝ) * (P : ℝ) ^ m' := mul_le_mul_of_nonneg_right hcard_ge hPm_pos.le
          exact le_of_mul_le_mul_right hstep hPm_pos
        -- Sum over all c : Fin m' → Fin Nstep using disjointness
        have hbi_sub : (Finset.univ : Finset (Fin m' → Fin Nstep)).biUnion hitOf ⊆
            Finset.univ.filter (fun z : Fin D → ZMod P =>
              ∃ c : Fin m' → Fin Nstep, ∀ i : Fin m',
                ((k i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) ∧
                Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) <
                  (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ)) := by
          intro z hz
          obtain ⟨c, -, hzc⟩ := Finset.mem_biUnion.mp hz
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, c, (Finset.mem_filter.mp hzc).2⟩
        have hbi_eq := Finset.card_biUnion hdisj
        have hsum_lb : (Nstep : ℝ) ^ m' * ((P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m')) ≤
            ((Finset.univ.biUnion hitOf).card : ℝ) := by
          rw [hbi_eq, Nat.cast_sum]
          calc (Nstep : ℝ) ^ m' * ((P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m'))
              = ∑ _c : Fin m' → Fin Nstep, ((P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m')) := by
                simp
            _ ≤ ∑ c : Fin m' → Fin Nstep, ((hitOf c).card : ℝ) :=
                Finset.sum_le_sum fun c _ => hhitOf_lb c
        have hratio : ((D : ℝ) ^ (62 * t))⁻¹ * (P : ℝ) ^ D ≤
            (Nstep : ℝ) ^ m' * ((P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m')) := by
          have hN_eq : (Nstep : ℝ) ^ m' = ((D : ℝ) ^ (36 * m')) ^ m' / ((D : ℝ) ^ 30) ^ m' := by
            dsimp only [Nstep]
            rw [Nat.cast_pow, ← pow_mul, ← pow_mul, ← pow_mul, eq_div_iff (pow_ne_zero _ hD_pos.ne'),
              ← pow_add]
            congr 1; have : 30 * m' ≤ 36 * m' * m' := by nlinarith
            have hsub : (36 * m' - 30) * m' + 30 * m' = 36 * m' * m' := by
              rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
            exact hsub
          rw [hN_eq]
          have hcancel : ((D : ℝ) ^ (36 * m')) ^ m' / ((D : ℝ) ^ 30) ^ m' *
              ((P : ℝ) ^ D / ((4 : ℝ) ^ m' * ((D : ℝ) ^ (36 * m')) ^ m')) =
              ((4 : ℝ) ^ m' * ((D : ℝ) ^ 30) ^ m')⁻¹ * (P : ℝ) ^ D := by
            field_simp [hD_pos.ne']
          rw [hcancel]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          have h4D : (4 : ℝ) ≤ (D : ℝ) := by
            have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
            linarith
          calc (4 : ℝ) ^ m' * ((D : ℝ) ^ 30) ^ m'
              ≤ (D : ℝ) ^ m' * (D : ℝ) ^ (30 * m') := by
                rw [← pow_mul]
                exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) h4D m') (by positivity)
            _ = (D : ℝ) ^ (31 * m') := by rw [← pow_add]; congr 1; omega
            _ ≤ (D : ℝ) ^ (62 * t) := pow_le_pow_right₀ (by linarith) (by omega)
        exact le_trans hratio (le_trans hsum_lb (by exact_mod_cast Finset.card_le_card hbi_sub))
      -- Now for fixed k, bound the number of ω ∈ Ω where ALL s ∈ Fin S miss hitSet!
      let badForBox (k : Fin m' → Fin G) : Finset Ω :=
        Finset.univ.filter (fun ω =>
          ∀ (s : Fin S) (u : Fin D → ℝ),
            (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
            ¬ ∀ i : Fin m',
              ((k i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) ∧
              Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) <
                (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ))
      have hbadBox_card : ∀ k : Fin m' → Fin G,
          ((badForBox k).card : ℝ) ≤ Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) := by
        intro k
        let hitSet := Finset.univ.filter (fun z : Fin D → ZMod P =>
          ∃ c : Fin m' → Fin Nstep, ∀ i : Fin m',
            ((k i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) ∧
            Int.fract (∑ b : Fin D, (w i b : ℝ) * (embed P (z b) + uOf c b)) <
              (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ))
        let blockSet : Finset (Fin M) := Finset.univ.image (fun s : Fin S => blockIdx y s)
        have hblock_card : blockSet.card = S := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro s1 s2 hs; exact (Prod.mk.inj (hblockIdx_inj hs)).2
        let allowed : Fin M → Finset (Fin D → ZMod P) := fun i =>
          if i ∈ blockSet then hitSetᶜ else Finset.univ
        have hsub : badForBox k ⊆ Fintype.piFinset allowed := by
          intro ω hω
          rw [Fintype.mem_piFinset]
          intro i
          dsimp only [allowed]
          split_ifs with hi
          · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hi
            rw [Finset.mem_compl]
            intro hmem
            obtain ⟨c, hc⟩ := (Finset.mem_filter.mp hmem).2
            exact (Finset.mem_filter.mp hω).2 s (uOf c) (hu_norm c) hc
          · exact Finset.mem_univ _
        have hpi_card : (Fintype.piFinset allowed).card =
            (hitSetᶜ.card) ^ S * (P ^ D) ^ (M - S) := by
          rw [Fintype.card_piFinset, ← Finset.prod_mul_prod_compl blockSet]
          have h1 : ∏ i ∈ blockSet, (allowed i).card = (hitSetᶜ.card) ^ S := by
            have : ∀ i ∈ blockSet, (allowed i).card = hitSetᶜ.card := fun i hi => by
              dsimp only [allowed]; rw [if_pos hi]
            rw [Finset.prod_congr rfl this, Finset.prod_const, hblock_card]
          have h2 : ∏ i ∈ blockSetᶜ, (allowed i).card = (P ^ D) ^ (M - S) := by
            have : ∀ i ∈ blockSetᶜ, (allowed i).card = P ^ D := fun i hi => by
              dsimp only [allowed]; rw [if_neg (Finset.mem_compl.mp hi)]; simp [ZMod.card]
            have hcpl : blockSetᶜ.card = M - S := by
              have := Finset.card_add_card_compl blockSet
              rw [Fintype.card_fin, hblock_card] at this; omega
            rw [Finset.prod_congr rfl this, Finset.prod_const, hcpl]
          rw [h1, h2]
        have hmiss_le : (hitSetᶜ.card : ℝ) ≤ (1 - ((D : ℝ) ^ (62 * t))⁻¹) * (P : ℝ) ^ D := by
          have htot : hitSet.card + hitSetᶜ.card = P ^ D := by
            rw [Finset.card_add_card_compl]
            simp [ZMod.card]
          have htotR : (hitSet.card : ℝ) + (hitSetᶜ.card : ℝ) = (P : ℝ) ^ D := by exact_mod_cast htot
          have hlb := hsingle_hit k
          linarith
        have hS_le_M : S ≤ M := by rw [← hMSY]; exact Nat.le_mul_of_pos_left S (Nat.pow_pos (by omega))
        have h1mp_exp : (1 - ((D : ℝ) ^ (62 * t))⁻¹) ^ S ≤ Real.exp (-((D : ℝ) ^ (138 * t))) := by
          have hstep : 1 - ((D : ℝ) ^ (62 * t))⁻¹ ≤ Real.exp (-((D : ℝ) ^ (62 * t))⁻¹) := by
            linarith [Real.add_one_le_exp (-((D : ℝ) ^ (62 * t))⁻¹)]
          have hnn : 0 ≤ 1 - ((D : ℝ) ^ (62 * t))⁻¹ := by
            have : (1 : ℝ) ≤ (D : ℝ) ^ (62 * t) := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega))
            have : ((D : ℝ) ^ (62 * t))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
            linarith
          calc (1 - ((D : ℝ) ^ (62 * t))⁻¹) ^ S
              ≤ (Real.exp (-((D : ℝ) ^ (62 * t))⁻¹)) ^ S := pow_le_pow_left₀ hnn hstep S
            _ = Real.exp ((S : ℝ) * (-((D : ℝ) ^ (62 * t))⁻¹)) := by rw [← Real.exp_nat_mul]
            _ = Real.exp (-((D : ℝ) ^ (138 * t))) := by
                congr 1
                dsimp only [S]
                rw [Nat.cast_pow, mul_neg, neg_inj, ← div_eq_mul_inv,
                  div_eq_iff (pow_ne_zero _ hD_pos.ne'), ← pow_add]
                congr 1; omega
        calc ((badForBox k).card : ℝ)
            ≤ ((Fintype.piFinset allowed).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ = (hitSetᶜ.card : ℝ) ^ S * ((P : ℝ) ^ D) ^ (M - S) := by
              rw [hpi_card]; push_cast; rfl
          _ ≤ ((1 - ((D : ℝ) ^ (62 * t))⁻¹) * (P : ℝ) ^ D) ^ S * ((P : ℝ) ^ D) ^ (M - S) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hmiss_le S) (by positivity)
          _ = (1 - ((D : ℝ) ^ (62 * t))⁻¹) ^ S * (Fintype.card Ω : ℝ) := by
              rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hS_le_M, hΩ_card, Nat.cast_pow,
                ← pow_mul]
          _ ≤ Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) :=
              mul_le_mul_of_nonneg_right h1mp_exp hΩ_pos.le
      have hbi_sub : Finset.univ.filter (fun ω => ∃ k : Fin m' → Fin G, ω ∈ badForBox k) ⊆
          (Finset.univ : Finset (Fin m' → Fin G)).biUnion badForBox := by
        intro ω hω
        obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hω).2
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hk⟩
      have hcard_filt :
          (@Finset.filter Ω (fun ω : Ω =>
            ∃ k : Fin (m.val + 1) → Fin (2 * D ^ (36 * (m.val + 1))),
              ∀ (s : Fin S) (u : Fin D → ℝ),
                (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
                ¬ ∀ i : Fin (m.val + 1),
                  ((k i : ℕ) : ℝ) / ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ) ≤
                    Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) ∧
                  Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) <
                    (((k i : ℕ) + 1 : ℕ) : ℝ) / ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ))
            (Classical.decPred _) Finset.univ).card =
          (Finset.univ.filter (fun ω => ∃ k : Fin m' → Fin G, ω ∈ badForBox k)).card := by
        congr 1; ext ω; simp [badForBox, G, m']
      rw [hcard_filt]
      calc ((Finset.univ.filter (fun ω => ∃ k : Fin m' → Fin G, ω ∈ badForBox k)).card : ℝ)
          ≤ (((Finset.univ : Finset (Fin m' → Fin G)).biUnion badForBox).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hbi_sub
        _ ≤ ∑ k : Fin m' → Fin G, ((badForBox k).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _k : Fin m' → Fin G, (Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ)) :=
            Finset.sum_le_sum fun k _ => hbadBox_card k
        _ = ((G : ℝ) ^ m') * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) := by
            simp [mul_assoc]
    · simp; positivity
  -- Union bound over all y ∈ Fin Y, m ∈ Fin (2 * t), v : Fin (m + 1) → BndVec!
  let F2 : Finset Ω :=
    (Finset.univ : Finset (Fin Y)).biUnion fun y =>
      (Finset.univ : Finset (Fin (2 * t))).biUnion fun m =>
        (Finset.univ : Finset (Fin (m.val + 1) → BndVec)).biUnion fun v =>
          BadPair y m v
  have hF2_lt : (F2.card : ℝ) < (1 / 4 : ℝ) * (Fintype.card Ω : ℝ) := by
    have hBnd_card : Fintype.card BndVec ≤ D ^ (13 * D) := by
      have hIcc : (Finset.Icc (-(Q : ℤ)) (Q : ℤ)).card ≤ D ^ 13 := by
        rw [Int.card_Icc]
        have h1 : (Q : ℤ) + 1 - -(Q : ℤ) = 2 * (Q : ℤ) + 1 := by ring
        rw [h1]
        have h2 : (2 * (Q : ℤ) + 1).toNat = 2 * Q + 1 := by omega
        rw [h2]
        dsimp only [Q]
        have : 2 * D ^ 12 + 1 ≤ D * D ^ 12 := by
          have : 3 ≤ D := by omega
          have : 1 ≤ D ^ 12 := Nat.pow_pos (by omega)
          nlinarith
        calc 2 * D ^ 12 + 1 ≤ D * D ^ 12 := this
          _ = D ^ 13 := by ring
      calc Fintype.card BndVec = ((Finset.Icc (-(Q : ℤ)) (Q : ℤ)).card) ^ D := by
            dsimp only [BndVec]; rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
        _ ≤ (D ^ 13) ^ D := Nat.pow_le_pow_left hIcc D
        _ = D ^ (13 * D) := by rw [← pow_mul]
    have hsum_le : (F2.card : ℝ) ≤ (D : ℝ) ^ (5400 * t ^ 2) *
        Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) := by
      have h1 : (F2.card : ℝ) ≤ ∑ y : Fin Y, ∑ m : Fin (2 * t), ∑ v : Fin (m.val + 1) → BndVec,
          ((BadPair y m v).card : ℝ) := by
        have hnat : F2.card ≤ ∑ y : Fin Y, ∑ m : Fin (2 * t), ∑ v : Fin (m.val + 1) → BndVec,
            (BadPair y m v).card := by
          refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ => ?_)
          exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ => Finset.card_biUnion_le)
        exact_mod_cast hnat
      have hinner : ∀ (y : Fin Y) (m : Fin (2 * t)),
          ∑ v : Fin (m.val + 1) → BndVec, ((BadPair y m v).card : ℝ) ≤
            (D : ℝ) ^ (5350 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) := by
        intro y m
        have hm_le : m.val + 1 ≤ 2 * t := by have := m.isLt; omega
        have hG_bd : ((2 * D ^ (36 * (m.val + 1)) : ℕ) : ℝ) ^ (m.val + 1) ≤ (D : ℝ) ^ (150 * t ^ 2) := by
          have h2leD : 2 ≤ D := by omega
          have hbase : (2 * D ^ (36 * (m.val + 1)) : ℕ) ≤ D ^ (37 * (m.val + 1)) := by
            calc 2 * D ^ (36 * (m.val + 1))
                ≤ D ^ (m.val + 1) * D ^ (36 * (m.val + 1)) :=
                  Nat.mul_le_mul_right _ (le_trans h2leD (Nat.le_self_pow (by omega) D))
              _ = D ^ (37 * (m.val + 1)) := by rw [← pow_add]; congr 1; omega
          have hpow : (2 * D ^ (36 * (m.val + 1))) ^ (m.val + 1) ≤ D ^ (150 * t ^ 2) := by
            calc (2 * D ^ (36 * (m.val + 1))) ^ (m.val + 1)
                ≤ (D ^ (37 * (m.val + 1))) ^ (m.val + 1) := Nat.pow_le_pow_left hbase _
              _ = D ^ (37 * (m.val + 1) * (m.val + 1)) := by rw [← pow_mul]
              _ ≤ D ^ (150 * t ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
          exact_mod_cast hpow
        have hv_card : (Fintype.card (Fin (m.val + 1) → BndVec) : ℝ) ≤ (D : ℝ) ^ (5200 * t ^ 2) := by
          have hnat : Fintype.card (Fin (m.val + 1) → BndVec) ≤ D ^ (5200 * t ^ 2) := by
            calc Fintype.card (Fin (m.val + 1) → BndVec)
                = (Fintype.card BndVec) ^ (m.val + 1) := by rw [Fintype.card_fun, Fintype.card_fin]
              _ ≤ (D ^ (13 * D)) ^ (m.val + 1) := Nat.pow_le_pow_left hBnd_card _
              _ = D ^ (13 * D * (m.val + 1)) := by rw [← pow_mul]
              _ ≤ D ^ (5200 * t ^ 2) := Nat.pow_le_pow_right (by omega) (by dsimp only [D]; nlinarith)
          exact_mod_cast hnat
        calc ∑ v : Fin (m.val + 1) → BndVec, ((BadPair y m v).card : ℝ)
            ≤ ∑ _v : Fin (m.val + 1) → BndVec,
                ((D : ℝ) ^ (150 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ)) := by
              refine Finset.sum_le_sum fun v _ => (hBadPair_card y m v).trans ?_
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG_bd (Real.exp_pos _).le) hΩ_pos.le
          _ = (Fintype.card (Fin (m.val + 1) → BndVec) : ℝ) *
                ((D : ℝ) ^ (150 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ)) := by simp
          _ ≤ (D : ℝ) ^ (5200 * t ^ 2) *
                ((D : ℝ) ^ (150 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ)) :=
              mul_le_mul_of_nonneg_right hv_card (by positivity)
          _ = (D : ℝ) ^ (5350 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) := by
              rw [← mul_assoc, ← mul_assoc, ← pow_add]; congr 3; ring
      calc (F2.card : ℝ)
          ≤ ∑ _y : Fin Y, ∑ _m : Fin (2 * t),
              ((D : ℝ) ^ (5350 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ)) :=
            h1.trans (Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun m _ => hinner y m)
        _ = (Y : ℝ) * ((2 * t : ℕ) : ℝ) *
              ((D : ℝ) ^ (5350 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ)) := by
            simp [mul_assoc]
        _ ≤ (D : ℝ) ^ (50 * t ^ 2) *
              ((D : ℝ) ^ (5350 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hnat : Y * (2 * t) ≤ D ^ (50 * t ^ 2) := by
              have h2tD : 2 * t ≤ D := by dsimp only [D]; omega
              calc Y * (2 * t) ≤ D ^ (8 * t) * D := Nat.mul_le_mul_left _ h2tD
                _ = D ^ (8 * t + 1) := by rw [pow_succ]
                _ ≤ D ^ (50 * t ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
            exact_mod_cast hnat
        _ = (D : ℝ) ^ (5400 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) * (Fintype.card Ω : ℝ) := by
            rw [← mul_assoc, ← mul_assoc, ← pow_add]; congr 3; ring
    have hexp_win : (D : ℝ) ^ (5400 * t ^ 2) * Real.exp (-((D : ℝ) ^ (138 * t))) < 1 / 4 := by
      have hlog : Real.log (D : ℝ) ≤ (D : ℝ) := (Real.log_le_sub_one_of_pos hD_pos).trans (by linarith)
      have hpow_exp : (D : ℝ) ^ (5400 * t ^ 2) = Real.exp ((5400 * t ^ 2 : ℕ) * Real.log (D : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hD_pos]
      rw [hpow_exp, ← Real.exp_add]
      have hneg_lt : ((5400 * t ^ 2 : ℕ) : ℝ) * Real.log (D : ℝ) + -((D : ℝ) ^ (138 * t)) < -2 := by
        have h1 : ((5400 * t ^ 2 : ℕ) : ℝ) * Real.log (D : ℝ) ≤ (D : ℝ) ^ 4 := by
          have h5400 : (5400 * t ^ 2 : ℕ) ≤ D ^ 3 := by dsimp only [D]; nlinarith
          have h5400R : ((5400 * t ^ 2 : ℕ) : ℝ) ≤ (D : ℝ) ^ 3 := by exact_mod_cast h5400
          calc ((5400 * t ^ 2 : ℕ) : ℝ) * Real.log (D : ℝ)
              ≤ (D : ℝ) ^ 3 * (D : ℝ) := mul_le_mul h5400R hlog
                (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))) (by positivity)
            _ = (D : ℝ) ^ 4 := by ring
        have h2 : (D : ℝ) ^ 4 + 2 < (D : ℝ) ^ (138 * t) := by
          have hD5 : (D : ℝ) ^ 5 ≤ (D : ℝ) ^ (138 * t) :=
            pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ D by omega)) (by omega)
          have hD4_pos : (2 : ℝ) < (D : ℝ) ^ 4 := by
            have hD6 : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
            have hD2 : (60000 : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by nlinarith
            nlinarith
          have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
          nlinarith [hD5, hD4_pos, show (D : ℝ) ^ 5 = (D : ℝ) ^ 4 * (D : ℝ) by ring]
        linarith
      have h4e : Real.exp (-2 : ℝ) < 1 / 4 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)]
        have h2e : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1, Real.exp_one_gt_d9]
      exact (Real.exp_lt_exp.mpr hneg_lt).trans h4e
    nlinarith [hsum_le, hexp_win, hΩ_pos]
  -- Pick ω ∈ Ω \ (F1 ∪ F2)!
  have hex_ω : ∃ ω : Ω, ω ∉ F1 ∧ ω ∉ F2 := by
    by_contra hall; push Not at hall
    have hsub : (Finset.univ : Finset Ω) ⊆ F1 ∪ F2 := fun ω _ => by
      by_cases h1 : ω ∈ F1
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ (hall ω h1)
    have hle : (Fintype.card Ω : ℝ) ≤ (F1.card : ℝ) + (F2.card : ℝ) := by
      have : Fintype.card Ω ≤ F1.card + F2.card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le F1 F2)
      exact_mod_cast this
    linarith
  obtain ⟨ω, hω1, hω2⟩ := hex_ω
  refine ⟨toR ω, ?_, ?_⟩
  · -- Condition 1
    intro i1 i2 i3 hne
    by_contra hall; push Not at hall
    apply hω1
    exact Finset.mem_biUnion.mpr ⟨(i1, i2, i3), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩⟩
  · -- Condition 2
    intro S0 hdim xstar
    let S0' : Set (Fin D → ℤ) := {ξ ∈ S0 | ∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12}
    let V0 : Submodule ℚ (Fin D → ℚ) :=
      Submodule.span ℚ ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) '' S0')
    have hV0_le : V0 ≤ Submodule.span ℚ ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) '' S0) :=
      Submodule.span_mono (Set.image_mono fun _ h => h.1)
    have hdim0 : Module.finrank ℚ V0 ≤ 2 * t :=
      (Submodule.finrank_mono hV0_le).trans hdim
    by_cases hm0 : Module.finrank ℚ V0 = 0
    · -- Trivial subspace: all ξ ∈ S0' are 0!
      have hS0'_zero : ∀ ξ ∈ S0', ξ = 0 := by
        intro ξ hξ
        have hmem : (fun b => (ξ b : ℚ)) ∈ V0 := Submodule.subset_span ⟨ξ, hξ, rfl⟩
        have hbot : V0 = ⊥ := Submodule.finrank_eq_zero.mp hm0
        rw [hbot, Submodule.mem_bot] at hmem
        ext b
        have hb : (ξ b : ℚ) = 0 := congrFun hmem b
        exact_mod_cast hb
      refine ⟨fun k => blockIdx k ⟨0, Nat.pow_pos (by omega)⟩, fun _ _ => 0, ?_, ?_, ?_⟩
      · intro k1 k2 hk; exact (Prod.mk.inj (hblockIdx_inj hk)).1
      · intro k; simp; positivity
      · intro k ξ hξ hbd
        have h0 := hS0'_zero ξ ⟨hξ, hbd⟩
        rw [h0]; simp [tdist]
    · -- Nonzero subspace: dimension m' ∈ [1, 2t]
      set m' := Module.finrank ℚ V0
      have hm'_pos : 1 ≤ m' := by omega
      have hm'_lt : m' - 1 < 2 * t := by omega
      let mIdx : Fin (2 * t) := ⟨m' - 1, hm'_lt⟩
      have hmIdx_eq : mIdx.val + 1 = m' := by dsimp only [mIdx]; omega
      -- Extract a basis of m' elements from S0'!
      obtain ⟨bs, hbs_sub, hbs_span, hbs_ind⟩ := exists_linearIndependent ℚ
        ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) '' S0')
      have hS0'_fin : S0'.Finite :=
        (Finset.finite_toSet (Fintype.piFinset fun _ : Fin D => Finset.Icc (-(Q : ℤ)) (Q : ℤ))).subset
          fun ξ hξ => Fintype.mem_piFinset.mpr fun b => Finset.mem_Icc.mpr (abs_le.mp (hξ.2 b))
      have hbs_fin : bs.Finite := (hS0'_fin.image _).subset hbs_sub
      let : Fintype bs := hbs_fin.fintype
      have hbs_card : Fintype.card bs = mIdx.val + 1 := by
        have hfr := finrank_span_eq_card hbs_ind
        rw [Subtype.range_coe, hbs_span] at hfr
        change m' = Fintype.card bs at hfr
        omega
      let ebs : Fin (mIdx.val + 1) ≃ bs := (Fintype.equivFinOfCardEq hbs_card).symm
      have hbs_ex : ∀ i : Fin (mIdx.val + 1), ∃ ξ ∈ S0', (fun b => (ξ b : ℚ)) = (ebs i : Fin D → ℚ) :=
        fun i => hbs_sub (ebs i).2
      choose vraw hvraw_mem hvraw_eq using hbs_ex
      let v : Fin (mIdx.val + 1) → BndVec := fun i b =>
        ⟨vraw i b, Finset.mem_Icc.mpr (abs_le.mp ((hvraw_mem i).2 b))⟩
      have hv_ind : LinearIndependent ℚ (fun i b => ((v i b).1 : ℚ)) := by
        have hcomp : (fun i b => ((v i b).1 : ℚ)) = (fun x : bs => (x : Fin D → ℚ)) ∘ ebs := by
          funext i b; exact congrFun (hvraw_eq i) b
        rw [hcomp]
        exact hbs_ind.comp ebs ebs.injective
      have hv_span : Submodule.span ℚ (Set.range (fun i b => ((v i b).1 : ℚ))) = V0 := by
        have hrg : Set.range (fun i b => ((v i b).1 : ℚ)) = bs := by
          ext x; constructor
          · rintro ⟨i, rfl⟩
            have h1 : (fun b => ((v i b).1 : ℚ)) = (ebs i : Fin D → ℚ) := funext fun b => congrFun (hvraw_eq i) b
            dsimp only
            rw [h1]; exact (ebs i).2
          · intro hx
            refine ⟨ebs.symm ⟨x, hx⟩, ?_⟩
            funext b
            have := congrFun (hvraw_eq (ebs.symm ⟨x, hx⟩)) b
            simpa [v] using this
        rw [hrg, hbs_span]
      -- Extract Mahler short basis w for v!
      have hspec := (mahler_short_basis (m := mIdx.val + 1) (D := D) (Q := Q) (by omega)
        (Nat.pow_pos (by omega)) (fun i b => (v i b).1)
        (fun i b => abs_le.mpr (Finset.mem_Icc.mp (v i b).2)) hv_ind).choose_spec
      let w : Fin (mIdx.val + 1) → Fin D → ℤ := wOf mIdx v hv_ind
      obtain ⟨-, -, -, hw_gen⟩ := hspec
      let G : ℕ := 2 * D ^ (36 * (mIdx.val + 1))
      have hG_pos : (0 : ℝ) < (G : ℝ) := by
        dsimp only [G]; positivity
      -- Locate xstar in a cube kstar : Fin (mIdx.val + 1) → Fin G!
      let kstar : Fin (mIdx.val + 1) → Fin G := fun i =>
        ⟨Nat.floor (Int.fract (∑ b : Fin D, (w i b : ℝ) * xstar b) * (G : ℝ)), by
          rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hG_pos.le)]
          have hlt1 : Int.fract (∑ b : Fin D, (w i b : ℝ) * xstar b) < 1 := Int.fract_lt_one _
          nlinarith⟩
      have hkstar_mem : ∀ i : Fin (mIdx.val + 1),
          ((kstar i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * xstar b) ∧
          Int.fract (∑ b : Fin D, (w i b : ℝ) * xstar b) < (((kstar i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ) := by
        intro i
        constructor
        · rw [div_le_iff₀ hG_pos]
          exact Nat.floor_le (mul_nonneg (Int.fract_nonneg _) hG_pos.le)
        · rw [lt_div_iff₀ hG_pos]
          simpa [kstar] using Nat.lt_floor_add_one (Int.fract (∑ b : Fin D, (w i b : ℝ) * xstar b) * (G : ℝ))
      -- Since ω ∉ F2, for EVERY y : Fin Y, ω ∉ BadPair y mIdx v, giving s_y and u_y!
      have hex_y : ∀ y : Fin Y, ∃ (s : Fin S) (u : Fin D → ℝ),
          (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) ∧
          (∀ i : Fin (mIdx.val + 1),
            ((kstar i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) ∧
            Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) <
              (((kstar i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ)) := by
        intro y
        have hnot : ω ∉ BadPair y mIdx v := fun hm =>
          hω2 (Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _,
            Finset.mem_biUnion.mpr ⟨mIdx, Finset.mem_univ _,
              Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hm⟩⟩⟩)
        have hnot' : ¬ (∃ k : Fin (mIdx.val + 1) → Fin G,
            ∀ (s : Fin S) (u : Fin D → ℝ),
              (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
              ¬ ∀ i : Fin (mIdx.val + 1),
                ((k i : ℕ) : ℝ) / (G : ℝ) ≤ Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) ∧
                Int.fract (∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y s) b + u b)) <
                  (((k i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ)) := by
          intro hex
          exact hnot (hmem_BadPair y mIdx v hv_ind ω hex)
        push Not at hnot'
        exact hnot' kstar
      choose s_of u_of hu_norm hu_box using hex_y
      refine ⟨fun y => blockIdx y (s_of y), u_of, ?_, hu_norm, ?_⟩
      · intro y1 y2 hy; exact (Prod.mk.inj (hblockIdx_inj hy)).1
      · intro y ξ hξ hbd
        have hξ_mem : (fun b => (ξ b : ℚ)) ∈ Submodule.span ℚ (Set.range (fun i b => ((v i b).1 : ℚ))) := by
          rw [hv_span]
          exact Submodule.subset_span ⟨ξ, ⟨hξ, hbd⟩, rfl⟩
        obtain ⟨n, hn_eq, hn_bd⟩ := hw_gen ξ hξ_mem hbd
        have hlin : ∑ b : Fin D, (ξ b : ℝ) * (toR ω (blockIdx y (s_of y)) b + u_of y b - xstar b) =
            ∑ i : Fin (mIdx.val + 1), (n i : ℝ) *
              ((∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y (s_of y)) b + u_of y b)) -
               (∑ b : Fin D, (w i b : ℝ) * xstar b)) := by
          have h1 : ∀ b : Fin D, (ξ b : ℝ) = ∑ i : Fin (mIdx.val + 1), (n i : ℝ) * (w i b : ℝ) := by
            intro b; exact_mod_cast hn_eq b
          simp_rw [h1, Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, ← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl fun b _ => by ring
        rw [hlin]
        have htd_each : ∀ i : Fin (mIdx.val + 1),
            tdist ((∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y (s_of y)) b + u_of y b)) -
                   (∑ b : Fin D, (w i b : ℝ) * xstar b)) < 1 / (G : ℝ) := by
          intro i
          have h1 := hu_box y i
          have h2 := hkstar_mem i
          have hcast : (((kstar i : ℕ) + 1 : ℕ) : ℝ) / (G : ℝ) = ((kstar i : ℕ) : ℝ) / (G : ℝ) + 1 / (G : ℝ) := by
            push_cast; ring
          rw [hcast] at h1 h2
          exact tdist_fract_lt_of_same_interval h1.1 h1.2 h2.1 h2.2
        have hm1_le_D : mIdx.val + 1 + 1 ≤ D := by
          have := mIdx.isLt; dsimp only [D]; omega
        have hn_D28 : ∀ i : Fin (mIdx.val + 1), |(n i : ℝ)| ≤ (D : ℝ) ^ (28 * (mIdx.val + 1)) := by
          intro i
          have h1 : |(n i : ℝ)| ≤ (((mIdx.val + 1 + 1).factorial : ℕ) : ℝ) *
              (((mIdx.val + 1 : ℕ) : ℝ) * (Q : ℝ)) ^ (mIdx.val + 1 + 1) := by
            exact_mod_cast hn_bd i
          have hfac : (mIdx.val + 1 + 1).factorial ≤ D ^ (mIdx.val + 1 + 1) := by
            calc (mIdx.val + 1 + 1).factorial ≤ (mIdx.val + 1 + 1) ^ (mIdx.val + 1 + 1) :=
                  Nat.factorial_le_pow _
              _ ≤ D ^ (mIdx.val + 1 + 1) := Nat.pow_le_pow_left hm1_le_D _
          have hmQ : (mIdx.val + 1) * Q ≤ D ^ 13 := by
            dsimp only [Q]
            calc (mIdx.val + 1) * D ^ 12 ≤ D * D ^ 12 := Nat.mul_le_mul_right _ (by omega)
              _ = D ^ 13 := by ring
          have hprod : (mIdx.val + 1 + 1).factorial * ((mIdx.val + 1) * Q) ^ (mIdx.val + 1 + 1) ≤
              D ^ (28 * (mIdx.val + 1)) := by
            calc (mIdx.val + 1 + 1).factorial * ((mIdx.val + 1) * Q) ^ (mIdx.val + 1 + 1)
                ≤ D ^ (mIdx.val + 1 + 1) * (D ^ 13) ^ (mIdx.val + 1 + 1) :=
                  Nat.mul_le_mul hfac (Nat.pow_le_pow_left hmQ _)
              _ = D ^ (14 * (mIdx.val + 1 + 1)) := by
                  rw [← pow_mul, ← pow_add]; congr 1; ring
              _ ≤ D ^ (28 * (mIdx.val + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
          exact h1.trans (by exact_mod_cast hprod)
        calc tdist (∑ i : Fin (mIdx.val + 1), (n i : ℝ) *
              ((∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y (s_of y)) b + u_of y b)) -
               (∑ b : Fin D, (w i b : ℝ) * xstar b)))
            ≤ ∑ i : Fin (mIdx.val + 1), tdist ((n i : ℝ) *
              ((∑ b : Fin D, (w i b : ℝ) * (toR ω (blockIdx y (s_of y)) b + u_of y b)) -
               (∑ b : Fin D, (w i b : ℝ) * xstar b))) := tdist_sum_le _ _
          _ ≤ ∑ i : Fin (mIdx.val + 1), |(n i : ℝ)| * (1 / (G : ℝ)) := by
              refine Finset.sum_le_sum fun i _ => (tdist_int_mul_le _ _).trans ?_
              exact mul_le_mul_of_nonneg_left (htd_each i).le (abs_nonneg _)
          _ ≤ ∑ _i : Fin (mIdx.val + 1), (D : ℝ) ^ (28 * (mIdx.val + 1)) * (1 / (G : ℝ)) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hn_D28 i) (by positivity)
          _ = ((mIdx.val + 1 : ℕ) : ℝ) * (D : ℝ) ^ (28 * (mIdx.val + 1)) / (2 * (D : ℝ) ^ (36 * (mIdx.val + 1))) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              dsimp only [G]; push_cast; ring
          _ < 1 / 100 := by
              rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
              have hmD : ((mIdx.val + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show mIdx.val + 1 ≤ D by omega)
              have hD8 : 100 * (D : ℝ) < 2 * (D : ℝ) ^ (8 * (mIdx.val + 1)) := by
                have h1 : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ (8 * (mIdx.val + 1)) :=
                  pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ D by omega)) (by omega)
                have hDbig : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
                nlinarith [h1, hDbig]
              have h36 : (D : ℝ) ^ (36 * (mIdx.val + 1)) =
                  (D : ℝ) ^ (28 * (mIdx.val + 1)) * (D : ℝ) ^ (8 * (mIdx.val + 1)) := by
                rw [← pow_add]; congr 1; omega
              rw [h36]
              nlinarith [pow_pos hD_pos (28 * (mIdx.val + 1)), hmD, hD8]

/- ## Section 4: Pillar 2 — Diophantine rotation on the finite prime grid -/

set_option maxHeartbeats 1600000 in
lemma hunter_H2 (t : ℕ) (ht : 300 ≤ t) :
    let D := 200 * t
    let N := D ^ (200 * t ^ 2)
    let X := D ^ (10000 * t)
    ∃ θ : Fin D → ℝ,
      (∀ d : ℕ, 1 ≤ d → d ≤ N →
        ∃ b : Fin D, (2 * (D : ℝ) ^ (2 * t))⁻¹ < tdist ((d : ℝ) * θ b)) ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ N →
        Module.finrank ℚ (Submodule.span ℚ
          ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) ''
            {ξ : Fin D → ℤ | (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) ∧
              tdist ((d : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b)) ≤
                (D : ℝ) ^ (8 * D) / (X : ℝ)})) ≤ 2 * t) := by
  intro D N X
  have hD_ge : 60000 ≤ D := by dsimp only [D]; omega
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  let r : ℕ := 2 * t + 1
  let Q : ℕ := D ^ 12
  let Pbound : ℕ := max (2 * N + 1) (max (r.factorial * Q ^ r + 1) (2 * X + 1))
  obtain ⟨P, hP_ge, hP_prime⟩ := Nat.exists_infinite_primes Pbound
  have : Fact P.Prime := ⟨hP_prime⟩
  have hP_pos : 0 < P := hP_prime.pos
  have hP_R : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP_pos
  let Θ := Fin D → ZMod P
  have hΘ_card : Fintype.card Θ = P ^ D := by simp [Θ, ZMod.card]
  have hΘ_pos : (0 : ℝ) < (P : ℝ) ^ D := pow_pos hP_R D
  let toR (θ : Θ) (b : Fin D) : ℝ := embed P (θ b)
  -- Bad Event B1: ∃ d ∈ [1, N], ∀ b, tdist (d * θ b) ≤ (2 D^(2t))⁻¹
  let bad1Of (d : ℕ) : Finset Θ :=
    Finset.univ.filter (fun θ => ∀ b : Fin D, tdist ((d : ℝ) * toR θ b) ≤ (2 * (D : ℝ) ^ (2 * t))⁻¹)
  let B1 : Finset Θ := (Finset.Icc 1 N).biUnion bad1Of
  have hB1_lt : (B1.card : ℝ) < (1 / 4 : ℝ) * (P : ℝ) ^ D := by
    have hbad1 : ∀ d ∈ Finset.Icc 1 N, ((bad1Of d).card : ℝ) ≤ (2 / (D : ℝ) ^ (2 * t)) ^ D * (P : ℝ) ^ D := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have hd_lt_P : d < P := by
        have : 2 * N + 1 ≤ P := le_trans (le_max_left _ _) hP_ge; omega
      have hd_ne : (d : ZMod P) ≠ 0 := by
        intro h0
        have hdvd : P ∣ d := (ZMod.natCast_eq_zero_iff d P).mp h0
        have := Nat.le_of_dvd (by omega) hdvd; omega
      let L : Θ →ₗ[ZMod P] Θ :=
        { toFun := fun θ b => (d : ZMod P) * θ b
          map_add' := fun a b => by ext i; dsimp only [Θ]; simp only [Pi.add_apply]; ring
          map_smul' := fun c a => by ext i; dsimp only [Θ]; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
      have hL_surj : Function.Surjective L := fun y =>
        ⟨fun b => (d : ZMod P)⁻¹ * y b, funext fun b => by
          change (d : ZMod P) * ((d : ZMod P)⁻¹ * y b) = y b
          rw [← mul_assoc, mul_inv_cancel₀ hd_ne, one_mul]⟩
      let τ1 : ℝ := (2 * (D : ℝ) ^ (2 * t))⁻¹
      let small : Finset Θ :=
        Fintype.piFinset (fun _ : Fin D => Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ τ1))
      have hsub : bad1Of d ⊆ Finset.univ.filter (fun θ => L θ ∈ small) := by
        intro θ hθ
        simp only [bad1Of, small, Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
        rw [Fintype.mem_piFinset]
        intro b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        obtain ⟨m, hm⟩ := embed_int_mul_sub (P := P) (d : ℤ) (θ b)
        have hdiff : embed P (L θ b) - (d : ℝ) * toR θ b = (m : ℝ) := by simpa [L, toR] using hm
        rw [tdist_eq_of_sub_int m hdiff]
        exact hθ b
      have hpre := card_preimage_of_surjective_linearMap L hL_surj small
      have hsmall_card : (small.card : ℝ) ≤ (2 / (D : ℝ) ^ (2 * t) * P) ^ D := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
        apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ D
        have hc : ((Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ τ1)).card : ℝ) ≤
            2 * (Nat.floor (τ1 * P) : ℝ) + 1 := by
          exact_mod_cast card_zmod_tdist_le (P := P) (τ := τ1) (by positivity)
        have hfl : (Nat.floor (τ1 * P) : ℝ) ≤ τ1 * P := Nat.floor_le (by positivity)
        have hP_big : (D : ℝ) ^ (2 * t) ≤ (P : ℝ) := by
          have h1 : D ^ (2 * t) ≤ N := Nat.pow_le_pow_right (by omega) (by nlinarith)
          have h2 : 2 * N + 1 ≤ P := le_trans (le_max_left _ _) hP_ge
          exact_mod_cast le_trans h1 (by omega)
        have h1le : (1 : ℝ) ≤ (P : ℝ) / (D : ℝ) ^ (2 * t) := (one_le_div (by positivity)).mpr hP_big
        have h2τ : 2 * (τ1 * P) = (P : ℝ) / (D : ℝ) ^ (2 * t) := by
          dsimp only [τ1]; field_simp [hD_pos.ne']
        have hrhs : 2 / (D : ℝ) ^ (2 * t) * P = 2 * ((P : ℝ) / (D : ℝ) ^ (2 * t)) := by ring
        linarith
      have hcard_eq : (Finset.univ.filter (fun θ => L θ ∈ small)).card = small.card := by
        have hpos : 0 < Fintype.card Θ := Fintype.card_pos
        have h1 : (Finset.univ.filter (fun θ => L θ ∈ small)).card * Fintype.card Θ =
            small.card * Fintype.card Θ := by convert hpre
        exact Nat.eq_of_mul_eq_mul_right hpos h1
      calc ((bad1Of d).card : ℝ) ≤ (small.card : ℝ) := by
            rw [← hcard_eq]; exact_mod_cast Finset.card_le_card hsub
        _ ≤ (2 / (D : ℝ) ^ (2 * t) * P) ^ D := hsmall_card
        _ = (2 / (D : ℝ) ^ (2 * t)) ^ D * (P : ℝ) ^ D := by rw [mul_pow]
    have hbi : (B1.card : ℝ) ≤ (N : ℝ) * ((2 / (D : ℝ) ^ (2 * t)) ^ D * (P : ℝ) ^ D) := by
      have h1 : (B1.card : ℝ) ≤ ∑ d ∈ Finset.Icc 1 N, ((bad1Of d).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      calc (B1.card : ℝ) ≤ ∑ _d ∈ Finset.Icc 1 N, ((2 / (D : ℝ) ^ (2 * t)) ^ D * (P : ℝ) ^ D) :=
            h1.trans (Finset.sum_le_sum fun d hd => hbad1 d hd)
        _ = (N : ℝ) * ((2 / (D : ℝ) ^ (2 * t)) ^ D * (P : ℝ) ^ D) := by simp
    have hfac : (N : ℝ) * (2 / (D : ℝ) ^ (2 * t)) ^ D < 1 / 4 := by
      have h2D : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 2 ≤ D by omega)
      have h2pow : (2 : ℝ) ^ D ≤ (D : ℝ) ^ D := pow_le_pow_left₀ (by norm_num) h2D D
      rw [div_pow, ← pow_mul]
      have hN_eq : (N : ℝ) = (D : ℝ) ^ (200 * t ^ 2) := by dsimp only [N]; push_cast; rfl
      have h2tD : 2 * t * D = 400 * t ^ 2 := by dsimp only [D]; ring
      rw [hN_eq, h2tD]
      have hnum : (D : ℝ) ^ (200 * t ^ 2) * (2 : ℝ) ^ D ≤ (D : ℝ) ^ (200 * t ^ 2 + D) := by
        rw [pow_add]; exact mul_le_mul_of_nonneg_left h2pow (by positivity)
      have hdiv_le : (D : ℝ) ^ (200 * t ^ 2) * ((2 : ℝ) ^ D / (D : ℝ) ^ (400 * t ^ 2)) ≤ (D : ℝ)⁻¹ := by
        rw [← mul_div_assoc, div_le_iff₀ (pow_pos hD_pos _)]
        have hexp : 200 * t ^ 2 + D + 1 ≤ 400 * t ^ 2 := by dsimp only [D]; nlinarith
        calc (D : ℝ) ^ (200 * t ^ 2) * (2 : ℝ) ^ D
            ≤ (D : ℝ) ^ (200 * t ^ 2 + D) := hnum
          _ = (D : ℝ)⁻¹ * (D : ℝ) ^ (200 * t ^ 2 + D + 1) := by
              rw [pow_succ' (D : ℝ), ← mul_assoc, inv_mul_cancel₀ hD_pos.ne', one_mul]
          _ ≤ (D : ℝ)⁻¹ * (D : ℝ) ^ (400 * t ^ 2) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hexp) (by positivity)
      have hD4 : (4 : ℝ) < (D : ℝ) := by
        have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
        linarith
      calc (D : ℝ) ^ (200 * t ^ 2) * ((2 : ℝ) ^ D / (D : ℝ) ^ (400 * t ^ 2))
          ≤ (D : ℝ)⁻¹ := hdiv_le
        _ < (4 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) hD4
        _ = 1 / 4 := by norm_num
    nlinarith [hbi, hfac, hΘ_pos]
  -- Bad Event B2: ∃ d ∈ [1, N], ∃ r = 2t + 1 lin. indep. ξ_i ∈ [-Q, Q]^D with tdist ≤ D^(8D)/X
  let BndVec := Fin D → Finset.Icc (-(Q : ℤ)) (Q : ℤ)
  let τ2 : ℝ := (D : ℝ) ^ (8 * D) / (X : ℝ)
  let bad2Of (d : ℕ) (ξs : Fin r → BndVec) : Finset Θ :=
    if hind : LinearIndependent ℚ (fun i b => ((ξs i b).1 : ℚ)) then
      Finset.univ.filter (fun θ => ∀ i : Fin r,
        tdist ((d : ℝ) * ∑ b : Fin D, ((ξs i b).1 : ℝ) * toR θ b) ≤ τ2)
    else ∅
  let B2 : Finset Θ :=
    (Finset.Icc 1 N).biUnion fun d =>
      (Finset.univ : Finset (Fin r → BndVec)).biUnion fun ξs =>
        bad2Of d ξs
  have hbad2_card : ∀ d ∈ Finset.Icc 1 N, ∀ ξs : Fin r → BndVec,
      ((bad2Of d ξs).card : ℝ) ≤ ((D : ℝ) * τ2) ^ r * (P : ℝ) ^ D := by
    intro d hd ξs
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    dsimp only [bad2Of]
    split_ifs with hind
    · have hd_lt_P : d < P := by
        have : 2 * N + 1 ≤ P := le_trans (le_max_left _ _) hP_ge; omega
      have hd_ne : (d : ZMod P) ≠ 0 := by
        intro h0
        have hdvd : P ∣ d := (ZMod.natCast_eq_zero_iff d P).mp h0
        have := Nat.le_of_dvd (by omega) hdvd; omega
      let L : Θ →ₗ[ZMod P] (Fin r → ZMod P) :=
        { toFun := fun θ i => (d : ZMod P) * ∑ b : Fin D, ((ξs i b).1 : ZMod P) * θ b
          map_add' := fun a b => by
            ext i; dsimp only [Θ]
            simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
          map_smul' := fun c a => by
            ext i; dsimp only [Θ]
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring }
      have hL_surj : Function.Surjective L := by
        have hsurj0 := surjective_dot_map_zmod (P := P) (fun i b => (ξs i b).1) Q
          (fun i b => abs_le.mpr (Finset.mem_Icc.mp (ξs i b).2)) hind
          (by have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hP_ge); omega)
        intro y
        obtain ⟨θ, hθ⟩ := hsurj0 (fun i => (d : ZMod P)⁻¹ * y i)
        refine ⟨θ, funext fun i => ?_⟩
        change (d : ZMod P) * (∑ b : Fin D, ((ξs i b).1 : ZMod P) * θ b) = y i
        have hθi : ∑ b : Fin D, ((ξs i b).1 : ZMod P) * θ b = (d : ZMod P)⁻¹ * y i := congrFun hθ i
        rw [hθi, ← mul_assoc, mul_inv_cancel₀ hd_ne, one_mul]
      let small : Finset (Fin r → ZMod P) :=
        Fintype.piFinset (fun _ : Fin r => Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ τ2))
      have hsub : Finset.univ.filter (fun θ => ∀ i : Fin r,
          tdist ((d : ℝ) * ∑ b : Fin D, ((ξs i b).1 : ℝ) * toR θ b) ≤ τ2) ⊆
          Finset.univ.filter (fun θ => L θ ∈ small) := by
        intro θ hθ
        simp only [small, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset] at hθ ⊢
        intro i
        obtain ⟨m1, hm1⟩ := embed_int_mul_sub (P := P) (d : ℤ) (∑ b : Fin D, ((ξs i b).1 : ZMod P) * θ b)
        obtain ⟨m2, hm2⟩ := embed_sum_int_mul_sub (P := P) Finset.univ (fun b => (ξs i b).1) θ
        have hdiff : embed P (L θ i) - (d : ℝ) * ∑ b : Fin D, ((ξs i b).1 : ℝ) * toR θ b =
            ((m1 + (d : ℤ) * m2 : ℤ) : ℝ) := by
          change embed P ((d : ZMod P) * ∑ b : Fin D, ((ξs i b).1 : ZMod P) * θ b) -
            (d : ℝ) * ∑ b : Fin D, ((ξs i b).1 : ℝ) * embed P (θ b) = ((m1 + (d : ℤ) * m2 : ℤ) : ℝ)
          push_cast at hm1 ⊢
          nlinarith [hm1, hm2]
        rw [tdist_eq_of_sub_int (m1 + (d : ℤ) * m2) hdiff]
        exact hθ i
      have hpre := card_preimage_of_surjective_linearMap L hL_surj small
      have hsmall_card : (small.card : ℝ) ≤ ((D : ℝ) * τ2 * P) ^ r := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
        apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ r
        have hc : ((Finset.univ.filter (fun a : ZMod P => tdist (embed P a) ≤ τ2)).card : ℝ) ≤
            2 * (Nat.floor (τ2 * P) : ℝ) + 1 := by
          exact_mod_cast card_zmod_tdist_le (P := P) (τ := τ2) (by positivity)
        have hfl : (Nat.floor (τ2 * P) : ℝ) ≤ τ2 * P := Nat.floor_le (by positivity)
        have hτ2P : 1 ≤ τ2 * P := by
          dsimp only [τ2]
          have hX_le_P : (X : ℝ) ≤ (P : ℝ) := by
            have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hP_ge)
            exact_mod_cast (show X ≤ P by omega)
          have hD1 : (1 : ℝ) ≤ (D : ℝ) ^ (8 * D) := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega))
          rw [div_mul_eq_mul_div, one_le_div (by exact_mod_cast Nat.pow_pos (show 0 < D by omega) : (0 : ℝ) < X)]
          nlinarith
        have h3D : (3 : ℝ) ≤ (D : ℝ) := by
          have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
          linarith
        nlinarith
      have hpreR : ((Finset.univ.filter (fun θ => L θ ∈ small)).card : ℝ) * (P : ℝ) ^ r =
          (small.card : ℝ) * (P : ℝ) ^ D := by
        have hpre_nat : (Finset.univ.filter (fun θ => L θ ∈ small)).card * P ^ r =
            small.card * P ^ D := by
          rw [hΘ_card, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hpre
          convert hpre
        exact_mod_cast hpre_nat
      have hcard_le : ((Finset.univ.filter (fun θ => ∀ i : Fin r,
          tdist ((d : ℝ) * ∑ b : Fin D, ((ξs i b).1 : ℝ) * toR θ b) ≤ τ2)).card : ℝ) ≤
          ((Finset.univ.filter (fun θ => L θ ∈ small)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hPr_pos : (0 : ℝ) < (P : ℝ) ^ r := pow_pos hP_R r
      have hstep : ((Finset.univ.filter (fun θ => ∀ i : Fin r,
          tdist ((d : ℝ) * ∑ b : Fin D, ((ξs i b).1 : ℝ) * toR θ b) ≤ τ2)).card : ℝ) * (P : ℝ) ^ r ≤
          ((D : ℝ) * τ2) ^ r * (P : ℝ) ^ D * (P : ℝ) ^ r := by
        calc _ ≤ ((Finset.univ.filter (fun θ => L θ ∈ small)).card : ℝ) * (P : ℝ) ^ r :=
              mul_le_mul_of_nonneg_right hcard_le hPr_pos.le
          _ = (small.card : ℝ) * (P : ℝ) ^ D := hpreR
          _ ≤ ((D : ℝ) * τ2 * P) ^ r * (P : ℝ) ^ D := mul_le_mul_of_nonneg_right hsmall_card hΘ_pos.le
          _ = ((D : ℝ) * τ2) ^ r * (P : ℝ) ^ D * (P : ℝ) ^ r := by rw [mul_pow]; ring
      exact le_of_mul_le_mul_right hstep hPr_pos
    · simp; positivity
  have hB2_lt : (B2.card : ℝ) < (1 / 4 : ℝ) * (P : ℝ) ^ D := by
    have hBnd_card : Fintype.card BndVec ≤ D ^ (13 * D) := by
      have hIcc : (Finset.Icc (-(Q : ℤ)) (Q : ℤ)).card ≤ D ^ 13 := by
        rw [Int.card_Icc]
        have h1 : (Q : ℤ) + 1 - -(Q : ℤ) = 2 * (Q : ℤ) + 1 := by ring
        rw [h1, show (2 * (Q : ℤ) + 1).toNat = 2 * Q + 1 by omega]
        dsimp only [Q]
        have : 2 * D ^ 12 + 1 ≤ D * D ^ 12 := by
          have : 3 ≤ D := by omega
          have : 1 ≤ D ^ 12 := Nat.pow_pos (by omega); nlinarith
        calc 2 * D ^ 12 + 1 ≤ D * D ^ 12 := this
          _ = D ^ 13 := by ring
      calc Fintype.card BndVec = ((Finset.Icc (-(Q : ℤ)) (Q : ℤ)).card) ^ D := by
            dsimp only [BndVec]; rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
        _ ≤ (D ^ 13) ^ D := Nat.pow_le_pow_left hIcc D
        _ = D ^ (13 * D) := by rw [← pow_mul]
    have hcount_le : (N : ℝ) * (Fintype.card (Fin r → BndVec) : ℝ) ≤ (D : ℝ) ^ (8000 * t ^ 2) := by
      have hnat : N * Fintype.card (Fin r → BndVec) ≤ D ^ (8000 * t ^ 2) := by
        have h1 : Fintype.card (Fin r → BndVec) ≤ D ^ (13 * D * r) := by
          calc Fintype.card (Fin r → BndVec) = (Fintype.card BndVec) ^ r := by rw [Fintype.card_fun, Fintype.card_fin]
            _ ≤ (D ^ (13 * D)) ^ r := Nat.pow_le_pow_left hBnd_card r
            _ = D ^ (13 * D * r) := by rw [← pow_mul]
        calc N * Fintype.card (Fin r → BndVec)
            ≤ D ^ (200 * t ^ 2) * D ^ (13 * D * r) := Nat.mul_le_mul_left _ h1
          _ = D ^ (200 * t ^ 2 + 13 * D * r) := by rw [← pow_add]
          _ ≤ D ^ (8000 * t ^ 2) := Nat.pow_le_pow_right (by omega) (by dsimp only [D, r]; nlinarith)
      exact_mod_cast hnat
    have hτ2_eq : (D : ℝ) * τ2 = ((D : ℝ) ^ (8400 * t - 1))⁻¹ := by
      dsimp only [τ2, X, D]
      rw [Nat.cast_pow, mul_div_assoc', ← pow_succ', inv_eq_one_div,
        div_eq_div_iff (pow_ne_zero _ hD_pos.ne') (pow_ne_zero _ hD_pos.ne'), one_mul, ← pow_add]
      congr 1; omega
    have hbi : (B2.card : ℝ) ≤ (D : ℝ) ^ (8000 * t ^ 2) * (((D : ℝ) ^ (8400 * t - 1))⁻¹) ^ r * (P : ℝ) ^ D := by
      have h1 : (B2.card : ℝ) ≤ ∑ d ∈ Finset.Icc 1 N, ∑ ξs : Fin r → BndVec, ((bad2Of d ξs).card : ℝ) := by
        have hnat : B2.card ≤ ∑ d ∈ Finset.Icc 1 N, ∑ ξs : Fin r → BndVec, (bad2Of d ξs).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun d _ => Finset.card_biUnion_le)
        exact_mod_cast hnat
      calc (B2.card : ℝ)
          ≤ ∑ _d ∈ Finset.Icc 1 N, ∑ _ξs : Fin r → BndVec, (((D : ℝ) * τ2) ^ r * (P : ℝ) ^ D) :=
            h1.trans (Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun ξs _ => hbad2_card d hd ξs)
        _ = ((N : ℝ) * (Fintype.card (Fin r → BndVec) : ℝ)) * (((D : ℝ) * τ2) ^ r * (P : ℝ) ^ D) := by
            simp [mul_assoc]
        _ ≤ (D : ℝ) ^ (8000 * t ^ 2) * (((D : ℝ) * τ2) ^ r * (P : ℝ) ^ D) :=
            mul_le_mul_of_nonneg_right hcount_le (by positivity)
        _ = (D : ℝ) ^ (8000 * t ^ 2) * (((D : ℝ) ^ (8400 * t - 1))⁻¹) ^ r * (P : ℝ) ^ D := by
            rw [hτ2_eq, mul_assoc]
    have hfac : (D : ℝ) ^ (8000 * t ^ 2) * (((D : ℝ) ^ (8400 * t - 1))⁻¹) ^ r < 1 / 4 := by
      rw [inv_pow, ← pow_mul]
      have hexp : 8000 * t ^ 2 + 1 ≤ (8400 * t - 1) * r := by
        have h1 : 8000 * t ≤ 8400 * t - 1 := by omega
        calc 8000 * t ^ 2 + 1 ≤ 8000 * t * r := by dsimp only [r]; nlinarith
          _ ≤ (8400 * t - 1) * r := Nat.mul_le_mul_right r h1
      have hle : (D : ℝ) ^ (8000 * t ^ 2) * ((D : ℝ) ^ ((8400 * t - 1) * r))⁻¹ ≤ (D : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hD_pos _)]
        calc (D : ℝ) ^ (8000 * t ^ 2)
            = (D : ℝ)⁻¹ * (D : ℝ) ^ (8000 * t ^ 2 + 1) := by
              rw [pow_succ' (D : ℝ), ← mul_assoc, inv_mul_cancel₀ hD_pos.ne', one_mul]
          _ ≤ (D : ℝ)⁻¹ * (D : ℝ) ^ ((8400 * t - 1) * r) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ D by omega)) hexp) (by positivity)
      have hD4 : (4 : ℝ) < (D : ℝ) := by
        have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
        linarith
      calc _ ≤ (D : ℝ)⁻¹ := hle
        _ < (4 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) hD4
        _ = 1 / 4 := by norm_num
    nlinarith [hbi, hfac, hΘ_pos]
  -- Pick θ ∉ B1 ∪ B2!
  have hex_θ : ∃ θ : Θ, θ ∉ B1 ∧ θ ∉ B2 := by
    by_contra hall; push Not at hall
    have hsub : (Finset.univ : Finset Θ) ⊆ B1 ∪ B2 := fun θ _ => by
      by_cases h1 : θ ∈ B1
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ (hall θ h1)
    have hle : (P : ℝ) ^ D ≤ (B1.card : ℝ) + (B2.card : ℝ) := by
      have : P ^ D ≤ B1.card + B2.card := by
        rw [← hΘ_card]; exact (Finset.card_le_card hsub).trans (Finset.card_union_le B1 B2)
      exact_mod_cast this
    linarith
  obtain ⟨θ, hθ1, hθ2⟩ := hex_θ
  refine ⟨toR θ, ?_, ?_⟩
  · intro d hd1 hdN
    by_contra hall; push Not at hall
    apply hθ1
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩⟩
  · intro d hd1 hdN
    by_contra hgt; push Not at hgt
    let Sset : Set (Fin D → ℤ) :=
      {ξ : Fin D → ℤ | (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) ∧
        tdist ((d : ℝ) * ∑ b : Fin D, (ξ b : ℝ) * toR θ b) ≤ τ2}
    obtain ⟨bs, hbs_sub, hbs_span, hbs_ind⟩ := exists_linearIndependent ℚ
      ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) '' Sset)
    have hSset_fin : Sset.Finite :=
      (Finset.finite_toSet (Fintype.piFinset fun _ : Fin D => Finset.Icc (-(Q : ℤ)) (Q : ℤ))).subset
        fun ξ hξ => Fintype.mem_piFinset.mpr fun b => Finset.mem_Icc.mpr (abs_le.mp (hξ.1 b))
    have hbs_fin : bs.Finite := (hSset_fin.image _).subset hbs_sub
    let : Fintype bs := hbs_fin.fintype
    have hbs_card : r ≤ Fintype.card bs := by
      have hfr := finrank_span_eq_card hbs_ind
      rw [Subtype.range_coe, hbs_span] at hfr
      change _ = Fintype.card bs at hfr
      dsimp only [r, Sset, τ2] at *
      omega
    let ebs : Fin (Fintype.card bs) ≃ bs := (Fintype.equivFin bs).symm
    let pick : Fin r → bs := fun i => ebs ⟨i.val, lt_of_lt_of_le i.isLt hbs_card⟩
    have hpick_inj : Function.Injective pick := fun i j hij =>
      Fin.ext (congrArg (fun x : Fin (Fintype.card bs) => x.val) (ebs.injective hij))
    have hpick_mem : ∀ i : Fin r, ∃ ξ ∈ Sset, (fun b => (ξ b : ℚ)) = (pick i : Fin D → ℚ) :=
      fun i => hbs_sub (pick i).2
    choose ξraw hξraw_mem hξraw_eq using hpick_mem
    let ξs : Fin r → BndVec := fun i b =>
      ⟨ξraw i b, Finset.mem_Icc.mpr (abs_le.mp ((hξraw_mem i).1 b))⟩
    have hξs_ind : LinearIndependent ℚ (fun i b => ((ξs i b).1 : ℚ)) := by
      have hcomp : (fun i b => ((ξs i b).1 : ℚ)) = (fun x : bs => (x : Fin D → ℚ)) ∘ pick := by
        funext i b; exact congrFun (hξraw_eq i) b
      rw [hcomp]
      exact hbs_ind.comp pick hpick_inj
    apply hθ2
    refine Finset.mem_biUnion.mpr ⟨d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩,
      Finset.mem_biUnion.mpr ⟨ξs, Finset.mem_univ _, ?_⟩⟩
    dsimp only [bad2Of]
    rw [dif_pos hξs_ind, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i => (hξraw_mem i).2⟩

/- ## Section 5: Pillar 3 — Fourier hitting lemma via finite grid orthogonality -/

lemma sin_pi_ge_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    2 * t ≤ Real.sin (Real.pi * t) := by
  have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le ht0) (by nlinarith [Real.pi_pos])
  have heq : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp [Real.pi_ne_zero]
  rwa [heq] at h

lemma abs_sin_pi_ge_two_tdist (β : ℝ) :
    2 * tdist β ≤ |Real.sin (Real.pi * β)| := by
  let r := β - (round β : ℝ)
  have hr : |r| ≤ 1 / 2 := abs_sub_round β
  have hsin_eq : |Real.sin (Real.pi * β)| = |Real.sin (Real.pi * r)| := by
    have harg : Real.pi * β = Real.pi * r + (round β : ℤ) * Real.pi := by dsimp only [r]; ring
    rw [harg, Real.sin_add_int_mul_pi, abs_mul]
    have : |(-1 : ℝ) ^ (round β : ℤ)| = 1 := by
      rw [abs_zpow, abs_neg, abs_one, one_zpow]
    rw [this, one_mul]
  rw [hsin_eq]
  change 2 * |r| ≤ |Real.sin (Real.pi * r)|
  rcases le_or_gt 0 r with h0 | h0
  · rw [abs_of_nonneg h0] at hr ⊢
    exact (sin_pi_ge_two_mul h0 hr).trans (le_abs_self _)
  · have hneg0 : 0 ≤ -r := by linarith
    have hneg1 : -r ≤ 1 / 2 := by rw [abs_of_neg h0] at hr; exact hr
    rw [abs_of_neg h0]
    have h1 := sin_pi_ge_two_mul hneg0 hneg1
    rw [mul_neg Real.pi r, Real.sin_neg] at h1
    exact (by linarith : 2 * -r ≤ -Real.sin (Real.pi * r)).trans (neg_le_abs _)

lemma fejer_sum_cos_bound (L : ℕ) (β : ℝ) (hβ : 0 < tdist β) :
    |∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * β)| ≤
      1 / (2 * tdist β) := by
  have hsin_pos : 0 < |Real.sin (Real.pi * β)| :=
    lt_of_lt_of_le (by linarith) (abs_sin_pi_ge_two_tdist β)
  -- Telescoping sum: 2 * sin(π β) * ∑_{a=-L}^L cos(2π a β) = 2 * sin((2L+1) π β)
  have htele : 2 * Real.sin (Real.pi * β) *
      (∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * β)) =
      2 * Real.sin (((2 * (L : ℝ) + 1) * Real.pi * β)) := by
    rw [Finset.mul_sum]
    have hterm : ∀ a : ℤ,
        2 * Real.sin (Real.pi * β) * Real.cos (2 * Real.pi * (a : ℝ) * β) =
          Real.sin ((2 * (a : ℝ) + 1) * Real.pi * β) - Real.sin ((2 * (a : ℝ) - 1) * Real.pi * β) := by
      intro a
      have h1 := Real.sin_add (2 * Real.pi * (a : ℝ) * β) (Real.pi * β)
      have h2 := Real.sin_sub (2 * Real.pi * (a : ℝ) * β) (Real.pi * β)
      have ha1 : 2 * Real.pi * (a : ℝ) * β + Real.pi * β = (2 * (a : ℝ) + 1) * Real.pi * β := by ring
      have ha2 : 2 * Real.pi * (a : ℝ) * β - Real.pi * β = (2 * (a : ℝ) - 1) * Real.pi * β := by ring
      rw [ha1] at h1; rw [ha2] at h2
      linarith
    simp_rw [hterm]
    -- Reindex Icc (-L) L to range (2*L + 1)
    let f (n : ℕ) : ℝ := Real.sin ((2 * ((n : ℤ) - (L : ℤ) : ℝ) - 1) * Real.pi * β)
    have hreindex : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
        (Real.sin ((2 * (a : ℝ) + 1) * Real.pi * β) - Real.sin ((2 * (a : ℝ) - 1) * Real.pi * β)) =
        ∑ n ∈ Finset.range (2 * L + 1), (f (n + 1) - f n) := by
      refine Finset.sum_bij (fun a _ => (a + L).toNat) ?_ ?_ ?_ ?_
      · intro a ha; rw [Finset.mem_Icc] at ha; rw [Finset.mem_range]; omega
      · intro a1 ha1 a2 ha2 h; rw [Finset.mem_Icc] at ha1 ha2; omega
      · intro n hn; rw [Finset.mem_range] at hn
        refine ⟨(n : ℤ) - (L : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a ha; rw [Finset.mem_Icc] at ha
        have hcast : (((a + L).toNat : ℕ) : ℤ) = a + L := Int.toNat_of_nonneg (by omega)
        have hcastR : (((a + L).toNat : ℕ) : ℝ) = (a : ℝ) + (L : ℝ) := by exact_mod_cast hcast
        dsimp only [f]
        push_cast
        rw [hcastR]
        congr 2 <;> ring
    rw [hreindex, Finset.sum_range_sub]
    dsimp only [f]
    push_cast
    have heq1 : (2 * ((2 * (L : ℝ) + 1 : ℝ) - (L : ℝ)) - 1) * Real.pi * β =
        (2 * (L : ℝ) + 1) * Real.pi * β := by ring
    have heq2 : (2 * ((0 : ℝ) - (L : ℝ)) - 1) * Real.pi * β =
        -((2 * (L : ℝ) + 1) * Real.pi * β) := by ring
    rw [heq1, heq2, Real.sin_neg]
    ring
  have habs := congrArg abs htele
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
  have hle1 : |Real.sin ((2 * (L : ℝ) + 1) * Real.pi * β)| ≤ 1 := Real.abs_sin_le_one _
  have hprod_le : |Real.sin (Real.pi * β)| *
      |∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * β)| ≤ 1 := by linarith
  have h2td : 2 * tdist β *
      |∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * β)| ≤ 1 :=
    (mul_le_mul_of_nonneg_right (abs_sin_pi_ge_two_tdist β) (abs_nonneg _)).trans hprod_le
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma double_fejer_cos (L : ℕ) (A B : ℝ) :
    ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      Real.cos (A + ((a : ℝ) + (b : ℝ)) * B) =
    Real.cos A * (∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos ((a : ℝ) * B)) ^ 2 := by
  have hsin0 : ∀ C : ℝ, ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.sin ((a : ℝ) * C) = 0 := by
    intro C
    have hneg : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.sin ((a : ℝ) * C) =
        ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), -Real.sin ((a : ℝ) * C) := by
      refine Finset.sum_bij (fun a _ => -a) ?_ ?_ ?_ ?_
      · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
      · intro a1 _ a2 _ h; omega
      · intro a ha; rw [Finset.mem_Icc] at ha; exact ⟨-a, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a _; push_cast; rw [neg_mul, Real.sin_neg, neg_neg]
    rw [Finset.sum_neg_distrib] at hneg
    linarith
  have hstep : ∀ a b : ℤ,
      Real.cos (A + ((a : ℝ) + (b : ℝ)) * B) =
        Real.cos A * (Real.cos ((a : ℝ) * B) * Real.cos ((b : ℝ) * B) -
          Real.sin ((a : ℝ) * B) * Real.sin ((b : ℝ) * B)) -
        Real.sin A * (Real.sin ((a : ℝ) * B) * Real.cos ((b : ℝ) * B) +
          Real.cos ((a : ℝ) * B) * Real.sin ((b : ℝ) * B)) := by
    intro a b
    rw [Real.cos_add, show ((a : ℝ) + (b : ℝ)) * B = (a : ℝ) * B + (b : ℝ) * B by ring,
      Real.cos_add, Real.sin_add]
  simp_rw [hstep, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      Real.sin ((a : ℝ) * B) * Real.sin ((b : ℝ) * B) = 0 := by
    simp_rw [← Finset.mul_sum, hsin0 B, mul_zero, Finset.sum_const_zero]
  have h2 : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      Real.sin ((a : ℝ) * B) * Real.cos ((b : ℝ) * B) = 0 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hsin0 B, zero_mul]
  have h3 : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      Real.cos ((a : ℝ) * B) * Real.sin ((b : ℝ) * B) = 0 := by
    simp_rw [← Finset.mul_sum, hsin0 B, mul_zero, Finset.sum_const_zero]
  have h4 : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      Real.cos ((a : ℝ) * B) * Real.cos ((b : ℝ) * B) =
      (∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos ((a : ℝ) * B)) ^ 2 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [h1, h2, h3, h4]
  ring

lemma root_of_unity_sum_zero {Q : ℕ} (hQ : 0 < Q) {r : ℤ} (hr_ne : r ≠ 0) (hr_lt : |r| < (Q : ℤ)) :
    ∑ a : Fin Q, Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) * (a : ℕ) / (Q : ℝ))) = 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) / (Q : ℂ)))
  have hterm : ∀ a : Fin Q,
      Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) * (a : ℕ) / (Q : ℝ))) = ζ ^ (a : ℕ) := by
    intro a
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun a => ζ ^ a)]
  have hQne : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hζQ : ζ ^ Q = 1 := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    have harg : (Q : ℂ) * (2 * ↑Real.pi * Complex.I * ((r : ℂ) / (Q : ℂ))) =
        (r : ℂ) * (2 * ↑Real.pi * Complex.I) := by field_simp [hQne]
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I r
  have hζ_ne1 : ζ ≠ 1 := by
    intro h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have heqC : ((r : ℤ) : ℂ) / (Q : ℂ) = (n : ℂ) := by
      have h2 : 2 * ↑Real.pi * Complex.I * ((r : ℂ) / (Q : ℂ)) =
          (2 * ↑Real.pi * Complex.I) * (n : ℂ) := by
        rw [hn, mul_comm]
      exact mul_left_cancel₀ hpi h2
    have heqZ : (r : ℤ) = n * (Q : ℤ) := by
      have : ((r : ℤ) : ℂ) = (n : ℂ) * (Q : ℂ) := (div_eq_iff hQne).mp heqC
      have : ((r : ℤ) : ℂ) = ((n * (Q : ℤ) : ℤ) : ℂ) := by push_cast; exact this
      exact Int.cast_injective this
    have hn0 : n = 0 := by
      by_contra hn_ne
      have : (1 : ℤ) ≤ |n| := by have := abs_pos.mpr hn_ne; omega
      have : (Q : ℤ) ≤ |r| := by
        rw [heqZ, abs_mul, abs_of_pos (by exact_mod_cast hQ : (0 : ℤ) < Q)]
        nlinarith
      omega
    rw [hn0, zero_mul] at heqZ
    exact hr_ne heqZ
  have hgeom := mul_geom_sum ζ Q
  rw [hζQ, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hζ_ne1)

lemma cos_pi_sq_le_one_sub_two_sq {t : ℝ} (ht : |t| ≤ 1 / 2) :
    (Real.cos (Real.pi * t)) ^ 2 ≤ 1 - 2 * t ^ 2 := by
  have h1 : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    have := abs_sin_pi_ge_two_tdist t
    rwa [tdist_eq_abs_of_le_half ht] at this
  have h2 : 4 * t ^ 2 ≤ (Real.sin (Real.pi * t)) ^ 2 := by
    calc 4 * t ^ 2 = (2 * |t|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ ≤ |Real.sin (Real.pi * t)| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = (Real.sin (Real.pi * t)) ^ 2 := sq_abs _
  have hcs := Real.sin_sq_add_cos_sq (Real.pi * t)
  nlinarith

lemma cos_sq_ge_one_sub_sq (u : ℝ) :
    1 - u ^ 2 ≤ (Real.cos u) ^ 2 := by
  have h1 : |Real.sin u| ≤ |u| := Real.abs_sin_le_abs
  have h2 : (Real.sin u) ^ 2 ≤ u ^ 2 := by
    calc (Real.sin u) ^ 2 = |Real.sin u| ^ 2 := (sq_abs _).symm
      _ ≤ |u| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = u ^ 2 := sq_abs u
  have hcs := Real.sin_sq_add_cos_sq u
  linarith

set_option maxHeartbeats 1600000 in
lemma hunter_H3 (t : ℕ) (ht : 300 ≤ t) :
    let D := 200 * t
    let ρ : ℝ := ((D : ℝ) ^ 4)⁻¹
    let X := D ^ (10000 * t)
    ∀ (α x0 y u : Fin D → ℝ),
      (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
      (∀ ξ : Fin D → ℤ, (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) →
        tdist (∑ b : Fin D, (ξ b : ℝ) * α b) ≤ (D : ℝ) ^ (8 * D) / (X : ℝ) →
        tdist (∑ b : Fin D, (ξ b : ℝ) * (y b + u b - x0 b)) < 1 / 100) →
      ∃ s : ℤ, |s| ≤ (X : ℤ) / 5 ∧
        ∑ b : Fin D, (tdist (x0 b + (s : ℝ) * α b - y b)) ^ 2 < (ρ / 5) ^ 2 := by
  intro D ρ X α x0 y u hu_norm hclose
  have hD_ge : 60000 ≤ D := by dsimp only [D]; omega
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hρ_pos : 0 < ρ := inv_pos.mpr (pow_pos hD_pos 4)
  let k : ℕ := D ^ 12
  have hk_pos : 0 < k := Nat.pow_pos (by omega)
  -- Build finite trig polynomial F(v) = (∑ b, 4 cos^2(π v b))^k = ∑ ξ ∈ Box(k), c ξ * cos(2π ξ·v)
  let Step := Fin D × Fin 4
  let stepVec (st : Step) : Fin D → ℤ :=
    match st.2 with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => Pi.single st.1 1
    | ⟨3, _⟩ => Pi.single st.1 (-1)
  let Box : Finset (Fin D → ℤ) := Fintype.piFinset (fun _ : Fin D => Finset.Icc (-(k : ℤ)) (k : ℤ))
  let sumSteps (f : Fin k → Step) : Fin D → ℤ := fun b => ∑ j : Fin k, stepVec (f j) b
  have hsum_mem : ∀ f : Fin k → Step, sumSteps f ∈ Box := by
    intro f
    rw [Fintype.mem_piFinset]
    intro b
    rw [Finset.mem_Icc, ← abs_le]
    calc |∑ j : Fin k, stepVec (f j) b|
        ≤ ∑ j : Fin k, |stepVec (f j) b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, (1 : ℤ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rcases f j with ⟨b', r⟩
          fin_cases r <;> simp [stepVec, Pi.single_apply]
          all_goals split_ifs <;> norm_num
      _ = (k : ℤ) := by simp
  let coeff (ξ : Fin D → ℤ) : ℕ := (Finset.univ.filter (fun f : Fin k → Step => sumSteps f = ξ)).card
  let F (v : Fin D → ℝ) : ℝ := (∑ b : Fin D, 4 * (Real.cos (Real.pi * v b)) ^ 2) ^ k
  have hF_complex : ∀ v : Fin D → ℝ,
      (F v : ℂ) = ∑ ξ ∈ Box, (coeff ξ : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (∑ b : Fin D, (ξ b : ℝ) * v b)) := by
    intro v
    have hstep_sum : (∑ st : Step, Complex.exp (2 * Real.pi * Complex.I *
        (∑ b : Fin D, (stepVec st b : ℝ) * v b))) =
        ((∑ b : Fin D, 4 * (Real.cos (Real.pi * v b)) ^ 2 : ℝ) : ℂ) := by
      rw [Fintype.sum_prod_type]
      push_cast
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Fin.sum_univ_four]
      have h0 : ∑ b' : Fin D, ((stepVec (b, 0) b' : ℤ) : ℂ) * (v b' : ℂ) = 0 := by simp [stepVec]
      have h2 : ∑ b' : Fin D, ((stepVec (b, 2) b' : ℤ) : ℂ) * (v b' : ℂ) = (v b : ℂ) := by
        simp [stepVec, Pi.single_apply]
      have h3 : ∑ b' : Fin D, ((stepVec (b, 3) b' : ℤ) : ℂ) * (v b' : ℂ) = -(v b : ℂ) := by
        simp [stepVec, Pi.single_apply]
      rw [h0, h2, h3]
      simp only [mul_zero, Complex.exp_zero]
      have hcos : Complex.exp (2 * ↑Real.pi * Complex.I * ↑(v b)) +
          Complex.exp (2 * ↑Real.pi * Complex.I * -↑(v b)) = 2 * Complex.cos (2 * ↑Real.pi * ↑(v b)) := by
        rw [Complex.cos]
        have he1 : 2 * ↑Real.pi * Complex.I * ↑(v b) = 2 * ↑Real.pi * ↑(v b) * Complex.I := by ring
        have he2 : 2 * ↑Real.pi * Complex.I * -↑(v b) = -(2 * ↑Real.pi * ↑(v b) * Complex.I) := by ring
        rw [he1, he2]; ring
      have hsum4 : (1 : ℂ) + 1 + Complex.exp (2 * ↑Real.pi * Complex.I * ↑(v b)) +
          Complex.exp (2 * ↑Real.pi * Complex.I * -↑(v b)) = 2 + 2 * Complex.cos (2 * ↑Real.pi * ↑(v b)) := by
        calc (1 : ℂ) + 1 + Complex.exp (2 * ↑Real.pi * Complex.I * ↑(v b)) +
              Complex.exp (2 * ↑Real.pi * Complex.I * -↑(v b))
            = 2 + (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(v b)) +
                Complex.exp (2 * ↑Real.pi * Complex.I * -↑(v b))) := by ring
          _ = 2 + 2 * Complex.cos (2 * ↑Real.pi * ↑(v b)) := by rw [hcos]
      rw [hsum4]
      have hdouble : Real.cos (2 * Real.pi * v b) = 2 * (Real.cos (Real.pi * v b)) ^ 2 - 1 := by
        have := Real.cos_two_mul (Real.pi * v b)
        rwa [show 2 * (Real.pi * v b) = 2 * Real.pi * v b by ring] at this
      have hcosC : Complex.cos (2 * ↑Real.pi * ↑(v b)) = ↑(Real.cos (2 * Real.pi * v b)) := by
        rw [Complex.ofReal_cos]; push_cast; rfl
      rw [hcosC, hdouble]; push_cast; ring
    have hpow : (F v : ℂ) = (∑ st : Step, Complex.exp (2 * Real.pi * Complex.I *
        (∑ b : Fin D, (stepVec st b : ℝ) * v b))) ^ k := by
      dsimp only [F]; rw [hstep_sum, Complex.ofReal_pow]
    rw [hpow, Fintype.sum_pow]
    have hprod_exp : ∀ f : Fin k → Step,
        ∏ j : Fin k, Complex.exp (2 * Real.pi * Complex.I *
          (∑ b : Fin D, (stepVec (f j) b : ℝ) * v b)) =
        Complex.exp (2 * Real.pi * Complex.I * (∑ b : Fin D, (sumSteps f b : ℝ) * v b)) := by
      intro f
      rw [← Complex.exp_sum, ← Finset.mul_sum]
      congr 1; congr 1
      dsimp only [sumSteps]
      push_cast
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    simp_rw [hprod_exp]
    rw [← Finset.sum_fiberwise_of_maps_to (fun f _ => hsum_mem f)]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have hconst : ∀ f ∈ Finset.univ.filter (fun f : Fin k → Step => sumSteps f = ξ),
        Complex.exp (2 * Real.pi * Complex.I * (∑ b : Fin D, (sumSteps f b : ℝ) * v b)) =
        Complex.exp (2 * Real.pi * Complex.I * (∑ b : Fin D, (ξ b : ℝ) * v b)) := by
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hF_real : ∀ v : Fin D → ℝ,
      F v = ∑ ξ ∈ Box, (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ b : Fin D, (ξ b : ℝ) * v b) := by
    intro v
    have hre := congrArg Complex.re (hF_complex v)
    rw [Complex.ofReal_re, Complex.re_sum] at hre
    rw [hre]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [show (coeff ξ : ℂ) = ((coeff ξ : ℝ) : ℂ) by simp, Complex.re_ofReal_mul]
    have harg : 2 * ↑Real.pi * Complex.I * ↑(∑ b : Fin D, (ξ b : ℝ) * v b) =
        ↑(2 * Real.pi * ∑ b : Fin D, (ξ b : ℝ) * v b) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  -- Finite grid orthogonality on (Fin Q)^D with Q = 16 * k!
  let Q : ℕ := 16 * k
  have hQ_pos : 0 < Q := by dsimp only [Q]; omega
  have hQ_R : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ_pos
  have horth : ∀ η ∈ Box,
      ∑ x : Fin D → Fin Q,
        (F (fun b => ((x b : ℕ) : ℝ) / (Q : ℝ)) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * ∑ b : Fin D, (η b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ)))) =
      (Q : ℂ) ^ D * (coeff η : ℂ) := by
    intro η hη
    simp_rw [hF_complex, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hterm : ∀ ξ ∈ Box,
        ∑ x : Fin D → Fin Q,
          (coeff ξ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ b : Fin D, (ξ b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ∑ b : Fin D, (η b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ)))) =
        if ξ = η then (Q : ℂ) ^ D * (coeff η : ℂ) else 0 := by
      intro ξ hξ
      have hcomb : ∀ x : Fin D → Fin Q,
          (coeff ξ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ b : Fin D, (ξ b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ∑ b : Fin D, (η b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ)))) =
          (coeff ξ : ℂ) * ∏ b : Fin D,
            Complex.exp (2 * Real.pi * Complex.I * (((ξ b - η b : ℤ) : ℝ) * (x b : ℕ) / (Q : ℝ))) := by
        intro x
        rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_sum]
        congr 1; congr 1
        rw [← Finset.mul_sum]
        push_cast
        rw [← sub_eq_add_neg, ← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun b _ => by ring
      simp_rw [hcomb, ← Finset.mul_sum]
      rw [← Fintype.prod_sum (fun (b : Fin D) (a : Fin Q) =>
        Complex.exp (2 * ↑Real.pi * Complex.I * (((ξ b - η b : ℤ) : ℝ) * (a : ℕ) / (Q : ℝ))))]
      by_cases hξη : ξ = η
      · subst hξη
        rw [if_pos rfl]
        simp [mul_comm]
      · rw [if_neg hξη]
        have hex : ∃ b : Fin D, ξ b ≠ η b := by
          by_contra hall; push Not at hall; exact hξη (funext hall)
        obtain ⟨b0, hb0⟩ := hex
        have hξb : |ξ b0| ≤ (k : ℤ) := abs_le.mpr (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hξ) b0))
        have hηb : |η b0| ≤ (k : ℤ) := abs_le.mpr (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hη) b0))
        have hlt : |ξ b0 - η b0| < (Q : ℤ) := by
          have : |ξ b0 - η b0| ≤ |ξ b0| + |η b0| := abs_sub _ _
          dsimp only [Q]; omega
        have hsum0 := root_of_unity_sum_zero hQ_pos (sub_ne_zero.mpr hb0) hlt
        rw [Finset.prod_eq_zero (Finset.mem_univ b0) hsum0, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Box η]
    simp [hη]
  -- Deduce c 0 formula and c η ≤ c 0!
  have h0_mem : (0 : Fin D → ℤ) ∈ Box := by
    rw [Fintype.mem_piFinset]; intro _; rw [Finset.mem_Icc]; simp only [Pi.zero_apply]; omega
  have hc0_eq : (Q : ℝ) ^ D * (coeff 0 : ℝ) = ∑ x : Fin D → Fin Q, F (fun b => ((x b : ℕ) : ℝ) / (Q : ℝ)) := by
    have h := congrArg Complex.re (horth 0 h0_mem)
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, Complex.ofReal_zero,
      mul_zero, neg_zero, Complex.exp_zero, mul_one] at h
    rw [Complex.re_sum] at h
    have hre_rhs : (((Q : ℂ) ^ D * (coeff 0 : ℂ)).re) = (Q : ℝ) ^ D * (coeff 0 : ℝ) := by
      have : (Q : ℂ) ^ D * (coeff 0 : ℂ) = (((Q : ℝ) ^ D * (coeff 0 : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_re]
    rw [hre_rhs] at h
    simpa only [Complex.ofReal_re] using h.symm
  have hc_le_c0 : ∀ η ∈ Box, (coeff η : ℝ) ≤ (coeff 0 : ℝ) := by
    intro η hη
    have hnorm := congrArg (fun z : ℂ => ‖z‖) (horth η hη)
    have hrhs : ‖(Q : ℂ) ^ D * (coeff η : ℂ)‖ = (Q : ℝ) ^ D * (coeff η : ℝ) := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    rw [hrhs] at hnorm
    have hle : (Q : ℝ) ^ D * (coeff η : ℝ) ≤ ∑ x : Fin D → Fin Q, F (fun b => ((x b : ℕ) : ℝ) / (Q : ℝ)) := by
      rw [← hnorm]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      rw [norm_mul]
      have hexp1 : ‖Complex.exp (-(2 * Real.pi * Complex.I *
          ∑ b : Fin D, (η b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ))))‖ = 1 := by
        have harg : -(2 * ↑Real.pi * Complex.I * ↑(∑ b : Fin D, (η b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ)))) =
            ↑(-(2 * Real.pi * ∑ b : Fin D, (η b : ℝ) * (((x b : ℕ) : ℝ) / (Q : ℝ)))) * Complex.I := by
          push_cast; ring
        rw [harg, Complex.norm_exp_ofReal_mul_I]
      have hFnn : 0 ≤ F (fun b => ((x b : ℕ) : ℝ) / (Q : ℝ)) := by
        dsimp only [F]; positivity
      rw [hexp1, mul_one, Complex.norm_real, Real.norm_of_nonneg hFnn]
    rw [← hc0_eq] at hle
    exact le_of_mul_le_mul_left hle (pow_pos hQ_R D)
  -- Lower bound on coeff 0!
  have hc0_lb : (1 / 2 : ℝ) * ((8 * (D : ℝ) ^ 6)⁻¹) ^ D * (4 * (D : ℝ)) ^ k ≤ (coeff 0 : ℝ) := by
    let smallA : Finset (Fin Q) := Finset.univ.filter (fun a : Fin Q => (a : ℕ) < 2 * D ^ 6)
    have hsmallA_card : smallA.card = 2 * D ^ 6 := by
      have hltQ : 2 * D ^ 6 ≤ Q := by
        dsimp only [Q, k]
        have : D ^ 6 ≤ D ^ 12 := Nat.pow_le_pow_right (by omega) (by omega); nlinarith
      have hbij : smallA.card = (Finset.range (2 * D ^ 6)).card := by
        refine Finset.card_bij (fun a _ => (a : ℕ)) ?_ ?_ ?_
        · intro a ha; rw [Finset.mem_range]; exact (Finset.mem_filter.mp ha).2
        · intro a1 _ a2 _ h; exact Fin.ext h
        · intro n hn; rw [Finset.mem_range] at hn
          exact ⟨⟨n, lt_of_lt_of_le hn hltQ⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩
      rwa [Finset.card_range] at hbij
    let box0 : Finset (Fin D → Fin Q) := Fintype.piFinset (fun _ : Fin D => smallA)
    have hF_on_box0 : ∀ x ∈ box0, (1 / 2 : ℝ) * (4 * (D : ℝ)) ^ k ≤ F (fun b => ((x b : ℕ) : ℝ) / (Q : ℝ)) := by
      intro x hx
      rw [Fintype.mem_piFinset] at hx
      have hcos_each : ∀ b : Fin D, 1 - 1 / (4 * (k : ℝ)) ≤ (Real.cos (Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ)))) ^ 2 := by
        intro b
        have hlt : ((x b : ℕ) : ℝ) < 2 * (D : ℝ) ^ 6 := by exact_mod_cast (Finset.mem_filter.mp (hx b)).2
        have hpi4 : Real.pi < 4 := Real.pi_lt_four
        have hu_le : Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ)) ≤ 1 / (2 * (D : ℝ) ^ 6) := by
          have hQ_eq : (Q : ℝ) = 16 * (D : ℝ) ^ 12 := by dsimp only [Q, k]; push_cast; rfl
          rw [hQ_eq, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : Real.pi * ((x b : ℕ) : ℝ) ≤ 4 * (2 * (D : ℝ) ^ 6) := by
            have : (0 : ℝ) ≤ ((x b : ℕ) : ℝ) := Nat.cast_nonneg _
            nlinarith
          have hpow : (D : ℝ) ^ 12 = (D : ℝ) ^ 6 * (D : ℝ) ^ 6 := by rw [← pow_add]
          nlinarith [pow_pos hD_pos 6]
        have hu_sq : (Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ))) ^ 2 ≤ 1 / (4 * (k : ℝ)) := by
          calc (Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ))) ^ 2
              ≤ (1 / (2 * (D : ℝ) ^ 6)) ^ 2 := pow_le_pow_left₀ (by positivity) hu_le 2
            _ = 1 / (4 * (k : ℝ)) := by dsimp only [k]; rw [div_pow, mul_pow, ← pow_mul]; push_cast; ring
        linarith [cos_sq_ge_one_sub_sq (Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ)))]
      have hsum_ge : (4 * (D : ℝ)) * (1 - 1 / (4 * (k : ℝ))) ≤
          ∑ b : Fin D, 4 * (Real.cos (Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ)))) ^ 2 := by
        calc (4 * (D : ℝ)) * (1 - 1 / (4 * (k : ℝ)))
            = ∑ _b : Fin D, 4 * (1 - 1 / (4 * (k : ℝ))) := by simp; ring
          _ ≤ ∑ b : Fin D, 4 * (Real.cos (Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ)))) ^ 2 :=
              Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hcos_each b) (by norm_num)
      have hbern : (1 / 2 : ℝ) ≤ (1 - 1 / (4 * (k : ℝ))) ^ k := by
        have h1 := one_add_mul_le_pow (a := -(1 / (4 * (k : ℝ)))) (by
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          have : 1 / (4 * (k : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          linarith) k
        have h2 : 1 + (k : ℝ) * (-(1 / (4 * (k : ℝ)))) = 3 / 4 := by
          have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
          field_simp [hkR]; ring
        have hsub : 1 + -(1 / (4 * (k : ℝ))) = 1 - 1 / (4 * (k : ℝ)) := by ring
        rw [hsub] at h1
        linarith
      dsimp only [F]
      calc (1 / 2 : ℝ) * (4 * (D : ℝ)) ^ k
          ≤ (1 - 1 / (4 * (k : ℝ))) ^ k * (4 * (D : ℝ)) ^ k :=
            mul_le_mul_of_nonneg_right hbern (by positivity)
        _ = ((4 * (D : ℝ)) * (1 - 1 / (4 * (k : ℝ)))) ^ k := by rw [← mul_pow]; ring
        _ ≤ (∑ b : Fin D, 4 * (Real.cos (Real.pi * (((x b : ℕ) : ℝ) / (Q : ℝ)))) ^ 2) ^ k :=
            pow_le_pow_left₀ (by
              have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
              have : 1 / (4 * (k : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
              nlinarith) hsum_ge k
    have hsum_lb : (box0.card : ℝ) * ((1 / 2 : ℝ) * (4 * (D : ℝ)) ^ k) ≤ (Q : ℝ) ^ D * (coeff 0 : ℝ) := by
      rw [hc0_eq]
      calc (box0.card : ℝ) * ((1 / 2 : ℝ) * (4 * (D : ℝ)) ^ k)
          = ∑ _x ∈ box0, ((1 / 2 : ℝ) * (4 * (D : ℝ)) ^ k) := by simp
        _ ≤ ∑ x ∈ box0, F (fun b => ((x b : ℕ) : ℝ) / (Q : ℝ)) := Finset.sum_le_sum hF_on_box0
        _ ≤ ∑ x : Fin D → Fin Q, F (fun b => ((x b : ℕ) : ℝ) / (Q : ℝ)) :=
            Finset.sum_le_univ_sum_of_nonneg fun x => by dsimp only [F]; positivity
    have hbox0_eq : (box0.card : ℝ) / (Q : ℝ) ^ D = ((8 * (D : ℝ) ^ 6)⁻¹) ^ D := by
      have hbc : box0.card = (2 * D ^ 6) ^ D := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hsmallA_card]
      rw [hbc, Nat.cast_pow, ← div_pow]
      congr 1
      dsimp only [Q, k]; push_cast
      have hpow : (D : ℝ) ^ 12 = (D : ℝ) ^ 6 * (D : ℝ) ^ 6 := by rw [← pow_add]
      rw [hpow]; field_simp [hD_pos.ne']; ring
    have hQD_pos : (0 : ℝ) < (Q : ℝ) ^ D := pow_pos hQ_R D
    calc (1 / 2 : ℝ) * ((8 * (D : ℝ) ^ 6)⁻¹) ^ D * (4 * (D : ℝ)) ^ k
        = ((box0.card : ℝ) / (Q : ℝ) ^ D) * ((1 / 2 : ℝ) * (4 * (D : ℝ)) ^ k) := by rw [hbox0_eq]; ring
      _ ≤ (coeff 0 : ℝ) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hQD_pos]
          linarith
  -- Define cutoff τ = (4 * (D - 1 / (100 * D^9)))^k and show τ ≤ (1/2) * coeff 0!
  let τ : ℝ := (4 * ((D : ℝ) - 1 / (100 * (D : ℝ) ^ 9))) ^ k
  have hτ_le : τ ≤ (1 / 2 : ℝ) * (coeff 0 : ℝ) := by
    have hτ_exp : τ ≤ Real.exp (-((D : ℝ) ^ 2 / 100)) * (4 * (D : ℝ)) ^ k := by
      have hfac : 4 * ((D : ℝ) - 1 / (100 * (D : ℝ) ^ 9)) =
          (4 * (D : ℝ)) * (1 - 1 / (100 * (D : ℝ) ^ 10)) := by
        have : (D : ℝ) ^ 10 = (D : ℝ) * (D : ℝ) ^ 9 := by ring
        rw [this]; field_simp [hD_pos.ne']
      dsimp only [τ]
      rw [hfac, mul_pow]
      have h1m : 1 - 1 / (100 * (D : ℝ) ^ 10) ≤ Real.exp (-(1 / (100 * (D : ℝ) ^ 10))) := by
        linarith [Real.add_one_le_exp (-(1 / (100 * (D : ℝ) ^ 10)))]
      have hnn : 0 ≤ 1 - 1 / (100 * (D : ℝ) ^ 10) := by
        have : 1 ≤ 100 * (D : ℝ) ^ 10 := by
          have : (1 : ℝ) ≤ (D : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega)); linarith
        have : 1 / (100 * (D : ℝ) ^ 10) ≤ 1 := (div_le_one (by positivity)).mpr this
        linarith
      calc (4 * (D : ℝ)) ^ k * (1 - 1 / (100 * (D : ℝ) ^ 10)) ^ k
          ≤ (4 * (D : ℝ)) ^ k * (Real.exp (-(1 / (100 * (D : ℝ) ^ 10)))) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn h1m k) (by positivity)
        _ = Real.exp ((k : ℝ) * (-(1 / (100 * (D : ℝ) ^ 10)))) * (4 * (D : ℝ)) ^ k := by
            rw [← Real.exp_nat_mul, mul_comm]
        _ = Real.exp (-((D : ℝ) ^ 2 / 100)) * (4 * (D : ℝ)) ^ k := by
            congr 2; dsimp only [k]; push_cast
            have : (D : ℝ) ^ 12 = (D : ℝ) ^ 2 * (D : ℝ) ^ 10 := by rw [← pow_add]
            rw [this]; field_simp [hD_pos.ne']
    have hexp_cmp : Real.exp (-((D : ℝ) ^ 2 / 100)) ≤ (1 / 4 : ℝ) * ((8 * (D : ℝ) ^ 6)⁻¹) ^ D := by
      have h8D : 8 * (D : ℝ) ^ 6 ≤ (D : ℝ) ^ 7 := by
        have : (8 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 8 ≤ D by omega)
        calc 8 * (D : ℝ) ^ 6 ≤ (D : ℝ) * (D : ℝ) ^ 6 := mul_le_mul_of_nonneg_right this (by positivity)
          _ = (D : ℝ) ^ 7 := by ring
      have h4le : (4 : ℝ) * (8 * (D : ℝ) ^ 6) ^ D ≤ (D : ℝ) ^ (8 * D) := by
        have h4D : (4 : ℝ) ≤ (D : ℝ) ^ D := by
          have : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 4 ≤ D by omega)
          calc (4 : ℝ) ≤ (D : ℝ) := this
            _ = (D : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (D : ℝ) ^ D := pow_le_pow_right₀ (by linarith) (by omega)
        calc (4 : ℝ) * (8 * (D : ℝ) ^ 6) ^ D
            ≤ (D : ℝ) ^ D * ((D : ℝ) ^ 7) ^ D :=
              mul_le_mul h4D (pow_le_pow_left₀ (by positivity) h8D D) (by positivity) (by positivity)
          _ = (D : ℝ) ^ (8 * D) := by rw [← pow_mul, ← pow_add]; congr 1; ring
      have hlogD : Real.log (D : ℝ) ≤ 10 + (D : ℝ) / 1000 := by
        have hsplit : Real.log (D : ℝ) = Real.log 1000 + Real.log ((D : ℝ) / 1000) := by
          rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
        have h1 : Real.log (1000 : ℝ) ≤ 10 := by
          have hlt : (1000 : ℝ) ≤ (2 : ℝ) ^ 10 := by norm_num
          calc Real.log (1000 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) := Real.log_le_log (by norm_num) hlt
            _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
            _ ≤ 10 * 1 := by linarith [Real.log_two_lt_d9]
            _ = 10 := by ring
        have h2 : Real.log ((D : ℝ) / 1000) ≤ (D : ℝ) / 1000 :=
          (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
        linarith
      have hD8D_le_exp : (D : ℝ) ^ (8 * D) ≤ Real.exp ((D : ℝ) ^ 2 / 100) := by
        have hpow_exp : (D : ℝ) ^ (8 * D) = Real.exp (((8 * D : ℕ) : ℝ) * Real.log (D : ℝ)) := by
          rw [Real.exp_nat_mul, Real.exp_log hD_pos]
        rw [hpow_exp]
        apply Real.exp_le_exp.mpr
        have hD60 : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
        push_cast
        nlinarith [hlogD, hD60]
      have hinv : Real.exp (-((D : ℝ) ^ 2 / 100)) = (Real.exp ((D : ℝ) ^ 2 / 100))⁻¹ := Real.exp_neg _
      rw [hinv, inv_pow, show (1 / 4 : ℝ) * ((8 * (D : ℝ) ^ 6) ^ D)⁻¹ =
          (4 * (8 * (D : ℝ) ^ 6) ^ D)⁻¹ by rw [one_div, ← mul_inv]]
      exact inv_anti₀ (by positivity) (h4le.trans hD8D_le_exp)
    calc τ ≤ Real.exp (-((D : ℝ) ^ 2 / 100)) * (4 * (D : ℝ)) ^ k := hτ_exp
      _ ≤ (1 / 4 : ℝ) * ((8 * (D : ℝ) ^ 6)⁻¹) ^ D * (4 * (D : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_right hexp_cmp (by positivity)
      _ = (1 / 2 : ℝ) * ((1 / 2 : ℝ) * ((8 * (D : ℝ) ^ 6)⁻¹) ^ D * (4 * (D : ℝ)) ^ k) := by ring
      _ ≤ (1 / 2 : ℝ) * (coeff 0 : ℝ) := mul_le_mul_of_nonneg_left hc0_lb (by norm_num)
  -- Now evaluate the double Fejér sum of ψ(v) := F v - τ at z := x0 - y - u!
  let ψ (v : Fin D → ℝ) : ℝ := F v - τ
  have hψ0_pos : 0 < (coeff 0 : ℝ) - τ := by
    have hc0_pos : 0 < (coeff 0 : ℝ) :=
      lt_of_lt_of_le (by positivity) hc0_lb
    linarith
  have hc_le_2ψ0 : ∀ ξ ∈ Box, (coeff ξ : ℝ) ≤ 2 * ((coeff 0 : ℝ) - τ) := fun ξ hξ => by
    linarith [hc_le_c0 ξ hξ, hτ_le]
  let L : ℕ := X / 10
  have h10X : 10 ∣ X := by
    have h10D : 10 ∣ D := by dsimp only [D]; exact ⟨20 * t, by ring⟩
    dsimp only [X]
    exact dvd_pow h10D (by omega)
  have h10L : 10 * L = X := Nat.mul_div_cancel' h10X
  let z : Fin D → ℝ := fun b => x0 b - y b - u b
  let Ssum : ℝ := (100 / (X : ℝ)) *
    ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      ψ (fun j => z j + ((a : ℝ) + (b : ℝ)) * α j)
  -- Show Ssum > 0 by expanding F via hF_real and double_fejer_cos!
  have hSsum_pos : 0 < Ssum := by
    have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast Nat.pow_pos (show 0 < D by omega)
    let W (β : ℝ) : ℝ := (100 / (X : ℝ)) *
      (∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos (2 * Real.pi * (a : ℝ) * β)) ^ 2
    have hW_nn : ∀ β, 0 ≤ W β := fun β => mul_nonneg (by positivity) (sq_nonneg _)
    have hW0_ge : 4 * (X : ℝ) ≤ W 0 := by
      dsimp only [W]
      have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
        rw [Int.card_Icc]; omega
      have hsum0 : ∑ _a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos (2 * Real.pi * (_a : ℝ) * 0) =
          (2 * (L : ℝ) + 1) := by
        simp only [mul_zero, Real.cos_zero, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
        push_cast; rfl
      rw [hsum0]
      have h10LR : 10 * (L : ℝ) = (X : ℝ) := by exact_mod_cast h10L
      have h2L : (X : ℝ) / 5 ≤ 2 * (L : ℝ) + 1 := by linarith
      calc 4 * (X : ℝ) = (100 / (X : ℝ)) * ((X : ℝ) / 5) ^ 2 := by field_simp [hX_pos.ne']; ring
        _ ≤ (100 / (X : ℝ)) * (2 * (L : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2L 2) (by positivity)
    have hS_eq : Ssum = ((coeff 0 : ℝ) - τ) * W 0 +
        ∑ ξ ∈ Box.erase 0, (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) *
          W (∑ j : Fin D, (ξ j : ℝ) * α j) := by
      -- Expand ψ = F - τ and swap sums!
      have hψ_exp : ∀ v : Fin D → ℝ,
          ψ v = ((coeff 0 : ℝ) - τ) +
            ∑ ξ ∈ Box.erase 0, (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * v j) := by
        intro v
        dsimp only [ψ]
        rw [hF_real v, ← Finset.add_sum_erase Box _ h0_mem]
        simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, mul_zero,
          Real.cos_zero, mul_one]
        ring
      dsimp only [Ssum]
      simp_rw [hψ_exp, Finset.sum_add_distrib]
      rw [mul_add]
      congr 1
      · -- Constant term
        have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by rw [Int.card_Icc]; omega
        have hsum0 : ∑ _a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), Real.cos (2 * Real.pi * (_a : ℝ) * 0) =
            (2 * (L : ℝ) + 1) := by
          simp only [mul_zero, Real.cos_zero, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
          push_cast; rfl
        dsimp only [W]
        rw [hsum0]
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        push_cast; ring
      · -- Nonzero ξ terms
        rw [Finset.mul_sum]
        have hswap1 : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
            ∑ ξ ∈ Box.erase 0, ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
              (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * (z j + ((a : ℝ) + (b : ℝ)) * α j)) =
            ∑ ξ ∈ Box.erase 0, ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
              (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * (z j + ((a : ℝ) + (b : ℝ)) * α j)) :=
          Finset.sum_comm
        have hswap2 : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
            ∑ ξ ∈ Box.erase 0,
              (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * (z j + ((a : ℝ) + (b : ℝ)) * α j)) =
            ∑ ξ ∈ Box.erase 0, ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
              (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * (z j + ((a : ℝ) + (b : ℝ)) * α j)) := by
          calc _ = ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ ξ ∈ Box.erase 0, ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), _ :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = _ := hswap1
        rw [← Finset.mul_sum, hswap2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        have harg : ∀ a b : ℤ,
            2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * (z j + ((a : ℝ) + (b : ℝ)) * α j) =
            (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) +
              ((a : ℝ) + (b : ℝ)) * (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * α j) := by
          intro a b
          have h1 : ∑ j : Fin D, (ξ j : ℝ) * (z j + ((a : ℝ) + (b : ℝ)) * α j) =
              (∑ j : Fin D, (ξ j : ℝ) * z j) + ((a : ℝ) + (b : ℝ)) * ∑ j : Fin D, (ξ j : ℝ) * α j := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [h1]; ring
        simp_rw [← Finset.mul_sum, harg]
        rw [double_fejer_cos]
        dsimp only [W]
        have hcos_eq : ∀ a : ℤ, Real.cos ((a : ℝ) * (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * α j)) =
            Real.cos (2 * Real.pi * (a : ℝ) * ∑ j : Fin D, (ξ j : ℝ) * α j) := fun a => by congr 1; ring
        simp_rw [hcos_eq]
        ring
    rw [hS_eq]
    -- Split Box.erase 0 into small (Λ) and large (rest)!
    let Λset : Finset (Fin D → ℤ) :=
      (Box.erase 0).filter (fun ξ => tdist (∑ j : Fin D, (ξ j : ℝ) * α j) ≤ (D : ℝ) ^ (8 * D) / (X : ℝ))
    let rest : Finset (Fin D → ℤ) :=
      (Box.erase 0).filter (fun ξ => ¬ tdist (∑ j : Fin D, (ξ j : ℝ) * α j) ≤ (D : ℝ) ^ (8 * D) / (X : ℝ))
    rw [← Finset.sum_filter_add_sum_filter_not (Box.erase 0)
      (fun ξ => tdist (∑ j : Fin D, (ξ j : ℝ) * α j) ≤ (D : ℝ) ^ (8 * D) / (X : ℝ))]
    -- On Λset: every term ≥ 0 because cos(2π ξ·z) > 0!
    have hΛ_nn : 0 ≤ ∑ ξ ∈ Λset, (coeff ξ : ℝ) *
        Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) * W (∑ j : Fin D, (ξ j : ℝ) * α j) := by
      refine Finset.sum_nonneg fun ξ hξ => ?_
      have hξ_mem : ξ ∈ Box := Finset.mem_of_mem_erase (Finset.mem_filter.mp hξ).1
      have hξ_bd : ∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12 := fun b =>
        abs_le.mpr (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hξ_mem) b))
      have hξ_td := hclose ξ hξ_bd (Finset.mem_filter.mp hξ).2
      have hneg_eq : ∑ j : Fin D, (ξ j : ℝ) * z j = -(∑ j : Fin D, (ξ j : ℝ) * (y j + u j - x0 j)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by dsimp only [z]; ring
      have htd_z : tdist (∑ j : Fin D, (ξ j : ℝ) * z j) < 1 / 100 := by
        rw [hneg_eq, tdist_neg]; exact hξ_td
      have hcos_pos : 0 ≤ Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) := by
        let s := ∑ j : Fin D, (ξ j : ℝ) * z j
        let r := s - (round s : ℝ)
        have hr : |r| < 1 / 100 := htd_z
        have harg : 2 * Real.pi * s = 2 * Real.pi * r + (round s : ℤ) * (2 * Real.pi) := by
          dsimp only [r]; ring
        rw [harg, Real.cos_add_int_mul_two_pi]
        apply Real.cos_nonneg_of_mem_Icc
        have hpi : 0 < Real.pi := Real.pi_pos
        have hr' := abs_lt.mp hr
        constructor <;> nlinarith
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hcos_pos) (hW_nn _)
    -- On rest: total absolute value ≤ ((coeff 0 : ℝ) - τ) * X!
    have hrest_bd : |∑ ξ ∈ rest, (coeff ξ : ℝ) *
        Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) * W (∑ j : Fin D, (ξ j : ℝ) * α j)| ≤
        ((coeff 0 : ℝ) - τ) * (X : ℝ) := by
      have hterm_bd : ∀ ξ ∈ rest,
          |(coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) *
            W (∑ j : Fin D, (ξ j : ℝ) * α j)| ≤
          50 * ((coeff 0 : ℝ) - τ) * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹ := by
        intro ξ hξ
        have hξ_mem : ξ ∈ Box := Finset.mem_of_mem_erase (Finset.mem_filter.mp hξ).1
        have htd_gt : (D : ℝ) ^ (8 * D) / (X : ℝ) < tdist (∑ j : Fin D, (ξ j : ℝ) * α j) :=
          lt_of_not_ge (Finset.mem_filter.mp hξ).2
        have htd_pos : 0 < tdist (∑ j : Fin D, (ξ j : ℝ) * α j) := lt_trans (by positivity) htd_gt
        have hW_le : W (∑ j : Fin D, (ξ j : ℝ) * α j) ≤ 25 * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹ := by
          dsimp only [W]
          have hf := fejer_sum_cos_bound L (∑ j : Fin D, (ξ j : ℝ) * α j) htd_pos
          have hf_sq : (∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
              Real.cos (2 * Real.pi * (a : ℝ) * ∑ j : Fin D, (ξ j : ℝ) * α j)) ^ 2 ≤
              (1 / (2 * tdist (∑ j : Fin D, (ξ j : ℝ) * α j))) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hf 2
          have htd_inv : (1 / (2 * tdist (∑ j : Fin D, (ξ j : ℝ) * α j))) ^ 2 ≤
              (1 / (2 * ((D : ℝ) ^ (8 * D) / (X : ℝ)))) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) _ 2
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
          calc (100 / (X : ℝ)) * (∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
                  Real.cos (2 * Real.pi * (a : ℝ) * ∑ j : Fin D, (ξ j : ℝ) * α j)) ^ 2
              ≤ (100 / (X : ℝ)) * (1 / (2 * ((D : ℝ) ^ (8 * D) / (X : ℝ)))) ^ 2 :=
                mul_le_mul_of_nonneg_left (hf_sq.trans htd_inv) (by positivity)
            _ = 25 * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹ := by
                have h16 : (D : ℝ) ^ (16 * D) = ((D : ℝ) ^ (8 * D)) ^ 2 := by rw [← pow_mul]; congr 1; ring
                rw [h16]; field_simp [hX_pos.ne', hD_pos.ne']; ring
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (hW_nn _)]
        calc (coeff ξ : ℝ) * |Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j)| *
              W (∑ j : Fin D, (ξ j : ℝ) * α j)
            ≤ (2 * ((coeff 0 : ℝ) - τ)) * 1 * (25 * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹) := by
              have h1 : (coeff ξ : ℝ) * |Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j)| ≤
                  (2 * ((coeff 0 : ℝ) - τ)) * 1 :=
                mul_le_mul (hc_le_2ψ0 ξ hξ_mem) (Real.abs_cos_le_one _) (abs_nonneg _) (by linarith)
              exact mul_le_mul h1 hW_le (hW_nn _) (by linarith)
          _ = 50 * ((coeff 0 : ℝ) - τ) * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹ := by ring
      have hrest_card : (rest.card : ℝ) ≤ (D : ℝ) ^ (13 * D) := by
        have hsub : rest.card ≤ Box.card :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_card (Finset.erase_subset _ _))
        have hbox : Box.card ≤ D ^ (13 * D) := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have hIcc : (Finset.Icc (-(k : ℤ)) (k : ℤ)).card ≤ D ^ 13 := by
            rw [Int.card_Icc]
            have h1 : (k : ℤ) + 1 - -(k : ℤ) = 2 * (k : ℤ) + 1 := by ring
            rw [h1, show (2 * (k : ℤ) + 1).toNat = 2 * k + 1 by omega]
            dsimp only [k]
            have : 2 * D ^ 12 + 1 ≤ D * D ^ 12 := by
              have : 3 ≤ D := by omega
              have : 1 ≤ D ^ 12 := Nat.pow_pos (by omega)
              nlinarith
            calc 2 * D ^ 12 + 1 ≤ D * D ^ 12 := this
              _ = D ^ 13 := by ring
          calc ((Finset.Icc (-(k : ℤ)) (k : ℤ)).card) ^ D ≤ (D ^ 13) ^ D := Nat.pow_le_pow_left hIcc D
            _ = D ^ (13 * D) := by rw [← pow_mul]
        exact_mod_cast hsub.trans hbox
      calc |∑ ξ ∈ rest, (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) *
              W (∑ j : Fin D, (ξ j : ℝ) * α j)|
          ≤ ∑ ξ ∈ rest, |(coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) *
              W (∑ j : Fin D, (ξ j : ℝ) * α j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ξ ∈ rest, (50 * ((coeff 0 : ℝ) - τ) * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹) :=
            Finset.sum_le_sum hterm_bd
        _ = (rest.card : ℝ) * (50 * ((coeff 0 : ℝ) - τ) * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹) := by simp
        _ ≤ (D : ℝ) ^ (13 * D) * (50 * ((coeff 0 : ℝ) - τ) * (X : ℝ) * ((D : ℝ) ^ (16 * D))⁻¹) :=
            mul_le_mul_of_nonneg_right hrest_card (by positivity)
        _ = (50 * ((D : ℝ) ^ (3 * D))⁻¹) * (((coeff 0 : ℝ) - τ) * (X : ℝ)) := by
            have h16 : (D : ℝ) ^ (16 * D) = (D : ℝ) ^ (13 * D) * (D : ℝ) ^ (3 * D) := by
              rw [← pow_add]; congr 1; omega
            rw [h16]; field_simp [hD_pos.ne']
        _ ≤ 1 * (((coeff 0 : ℝ) - τ) * (X : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [← div_eq_mul_inv, div_le_one (pow_pos hD_pos _)]
            have : (50 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 50 ≤ D by omega)
            calc (50 : ℝ) ≤ (D : ℝ) := this
              _ = (D : ℝ) ^ 1 := (pow_one _).symm
              _ ≤ (D : ℝ) ^ (3 * D) := pow_le_pow_right₀ (by linarith) (by omega)
        _ = ((coeff 0 : ℝ) - τ) * (X : ℝ) := one_mul _
    have hrest_lb : -(((coeff 0 : ℝ) - τ) * (X : ℝ)) ≤
        ∑ ξ ∈ rest, (coeff ξ : ℝ) * Real.cos (2 * Real.pi * ∑ j : Fin D, (ξ j : ℝ) * z j) *
          W (∑ j : Fin D, (ξ j : ℝ) * α j) := (abs_le.mp hrest_bd).1
    have hterm0 : 4 * (((coeff 0 : ℝ) - τ) * (X : ℝ)) ≤ ((coeff 0 : ℝ) - τ) * W 0 := by
      have := mul_le_mul_of_nonneg_left hW0_ge hψ0_pos.le
      linarith
    have hpos_rhs : 0 < ((coeff 0 : ℝ) - τ) * (X : ℝ) := mul_pos hψ0_pos hX_pos
    linarith
  -- Extract a, b ∈ Icc (-L) L with ψ(z + (a + b) α) > 0!
  have hex_ab : ∃ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∃ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
      0 < ψ (fun j => z j + ((a : ℝ) + (b : ℝ)) * α j) := by
    by_contra hall; push Not at hall
    have hsum_le0 : ∑ a ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ b ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
        ψ (fun j => z j + ((a : ℝ) + (b : ℝ)) * α j) ≤ 0 :=
      Finset.sum_nonpos fun a ha => Finset.sum_nonpos fun b hb => hall a ha b hb
    have hS_le0 : Ssum ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hsum_le0
    linarith
  obtain ⟨a, ha, b, hb, hψ_pos⟩ := hex_ab
  let s : ℤ := a + b
  have hs_abs : |s| ≤ (X : ℤ) / 5 := by
    rw [Finset.mem_Icc] at ha hb
    dsimp only [s]
    rw [abs_le]
    have h2L : 2 * (L : ℤ) ≤ (X : ℤ) / 5 := by omega
    constructor <;> omega
  -- ψ(v) > 0 implies ∀ j, tdist(v j)^2 < 1 / (100 * D^9), hence ∑ tdist(v j)^2 < (ρ / 10)^2!
  let v : Fin D → ℝ := fun j => z j + (s : ℝ) * α j
  have hv_pos : 0 < ψ v := by
    dsimp only [v, s]; simpa [Int.cast_add] using hψ_pos
  have hv_each : ∀ j : Fin D, (tdist (v j)) ^ 2 < 1 / (100 * (D : ℝ) ^ 9) := by
    intro j
    by_contra hge; push Not at hge
    let r := v j - (round (v j) : ℝ)
    have hr : |r| ≤ 1 / 2 := abs_sub_round (v j)
    have hcos_eq : (Real.cos (Real.pi * v j)) ^ 2 = (Real.cos (Real.pi * r)) ^ 2 := by
      have harg : Real.pi * v j = Real.pi * r + (round (v j) : ℤ) * Real.pi := by dsimp only [r]; ring
      rw [harg, Real.cos_add_int_mul_pi, mul_pow]
      have : ((-1 : ℝ) ^ (round (v j) : ℤ)) ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp
      rw [this, one_mul]
    have hcos_le : (Real.cos (Real.pi * v j)) ^ 2 ≤ 1 - 1 / (100 * (D : ℝ) ^ 9) := by
      rw [hcos_eq]
      have h1 := cos_pi_sq_le_one_sub_two_sq hr
      have hr2 : r ^ 2 = (tdist (v j)) ^ 2 := (sq_abs r).symm
      rw [hr2] at h1
      have hpos_eps : (0 : ℝ) ≤ 1 / (100 * (D : ℝ) ^ 9) := by positivity
      linarith
    have hsum_le : ∑ i : Fin D, 4 * (Real.cos (Real.pi * v i)) ^ 2 ≤
        4 * ((D : ℝ) - 1 / (100 * (D : ℝ) ^ 9)) := by
      have hsplit := Finset.add_sum_erase Finset.univ (fun i : Fin D => 4 * (Real.cos (Real.pi * v i)) ^ 2)
        (Finset.mem_univ j)
      have hrest : ∑ i ∈ Finset.univ.erase j, 4 * (Real.cos (Real.pi * v i)) ^ 2 ≤
          4 * ((D : ℝ) - 1) := by
        calc ∑ i ∈ Finset.univ.erase j, 4 * (Real.cos (Real.pi * v i)) ^ 2
            ≤ ∑ _i ∈ Finset.univ.erase j, (4 : ℝ) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have : (Real.cos (Real.pi * v i)) ^ 2 ≤ 1 := by
                rw [← sq_abs]; exact (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))
              linarith
          _ = ((Finset.univ.erase j : Finset (Fin D)).card : ℝ) * 4 := by simp
          _ = 4 * ((D : ℝ) - 1) := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
                Nat.cast_sub (by omega : 1 ≤ D)]
              push_cast; ring
      linarith
    have hF_le_τ : F v ≤ τ := by
      dsimp only [F, τ]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum_le k
    dsimp only [ψ] at hv_pos
    linarith
  have hv_sq : ∑ j : Fin D, (tdist (v j)) ^ 2 < (ρ / 10) ^ 2 := by
    calc ∑ j : Fin D, (tdist (v j)) ^ 2
        < ∑ _j : Fin D, (1 / (100 * (D : ℝ) ^ 9)) :=
          Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun j _ => hv_each j)
      _ = (D : ℝ) / (100 * (D : ℝ) ^ 9) := by simp; ring
      _ = (ρ / 10) ^ 2 := by
          dsimp only [ρ]
          rw [div_pow, inv_pow, ← pow_mul]
          have h9 : (D : ℝ) ^ 9 = (D : ℝ) * (D : ℝ) ^ 8 := by ring
          rw [h9]; field_simp [hD_pos.ne']; ring
  -- Combine v j = x0 j + s α j - y j - u j with ‖u‖_2 < ρ / 10 via (a + b)^2 ≤ 2 a^2 + 2 b^2!
  -- Wait: 2 * ((ρ/10)^2 + (ρ/10)^2) = 4 * (ρ/10)^2 = (ρ/5)^2!! EXACT!!
  refine ⟨s, hs_abs, ?_⟩
  have hcoord : ∀ j : Fin D, (tdist (x0 j + (s : ℝ) * α j - y j)) ^ 2 ≤
      2 * (tdist (v j)) ^ 2 + 2 * (u j) ^ 2 := by
    intro j
    have heq : x0 j + (s : ℝ) * α j - y j = v j + u j := by dsimp only [v, z]; ring
    rw [heq]
    have htri : tdist (v j + u j) ≤ tdist (v j) + |u j| :=
      (tdist_add_le (v j) (u j)).trans (add_le_add le_rfl (tdist_le_abs (u j)))
    have hsq : (tdist (v j + u j)) ^ 2 ≤ (tdist (v j) + |u j|) ^ 2 :=
      pow_le_pow_left₀ (tdist_nonneg _) htri 2
    nlinarith [sq_nonneg (tdist (v j) - |u j|), sq_abs (u j)]
  calc ∑ j : Fin D, (tdist (x0 j + (s : ℝ) * α j - y j)) ^ 2
      ≤ ∑ j : Fin D, (2 * (tdist (v j)) ^ 2 + 2 * (u j) ^ 2) :=
        Finset.sum_le_sum fun j _ => hcoord j
    _ = 2 * (∑ j : Fin D, (tdist (v j)) ^ 2) + 2 * (∑ j : Fin D, (u j) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ < 2 * (ρ / 10) ^ 2 + 2 * (ρ / 10) ^ 2 := by linarith
    _ = (ρ / 5) ^ 2 := by ring

/- ## Section 6: Combine Pillars 1, 2, 3 into Zach Hunter's 2-coloring theorem -/

private lemma pow_ge_two_mul_pred_pow (K : ℕ) (hK : 1 ≤ K) :
    2 * (K - 1) ^ K ≤ K ^ K := by
  have hKeq : (K - 1) + 1 = K := by omega
  have hexp : K ^ K = ∑ m ∈ Finset.range (K + 1), (K - 1) ^ m * K.choose m := by
    conv_lhs => rw [← hKeq]
    rw [add_pow]; simp only [hKeq, one_pow, mul_one, Nat.cast_id]
  have hsub2 : ({K, K - 1} : Finset ℕ) ⊆ Finset.range (K + 1) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hsum2 := Finset.sum_le_sum_of_subset
    (f := fun m => (K - 1) ^ m * K.choose m) hsub2
  rw [Finset.sum_pair (by omega : K ≠ K - 1)] at hsum2
  simp only [Nat.choose_self, mul_one] at hsum2
  have hchoose : K.choose (K - 1) = K := by
    have := Nat.choose_symm (by omega : K - 1 ≤ K)
    rw [show K - (K - 1) = 1 by omega, Nat.choose_one_right] at this
    exact this.symm
  rw [hchoose] at hsum2
  have hterm : (K - 1) ^ K ≤ (K - 1) ^ (K - 1) * K := by
    conv_lhs => rw [show K = (K - 1) + 1 by omega, pow_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  rw [hexp]; omega

private lemma card_avoiding_funs {M Y K : ℕ} (j : Fin Y → Fin M) (hj : Function.Injective j)
    (r : Fin Y → Fin K) :
    (Finset.univ.filter (fun e : Fin M → Fin K => ∀ k : Fin Y, e (j k) ≠ r k)).card =
      (K - 1) ^ Y * K ^ (M - Y) := by
  let S : Finset (Fin M) := Finset.univ.image j
  have hScard : S.card = Y := by rw [Finset.card_image_of_injective _ hj]; simp
  have hScompl : Sᶜ.card = M - Y := by
    have := Finset.card_add_card_compl S; rw [Fintype.card_fin, hScard] at this; omega
  let allowed : Fin M → Finset (Fin K) := fun i =>
    if h : ∃ k : Fin Y, j k = i then Finset.univ.erase (r h.choose) else Finset.univ
  have hfilt : Finset.univ.filter (fun e : Fin M → Fin K => ∀ k : Fin Y, e (j k) ≠ r k) =
      Fintype.piFinset allowed := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro he i; dsimp only [allowed]; split_ifs with h
      · rw [Finset.mem_erase]; exact ⟨by have := he h.choose; rwa [h.choose_spec] at this, Finset.mem_univ _⟩
      · exact Finset.mem_univ _
    · intro he k
      have hi := he (j k); dsimp only [allowed] at hi
      have hex : ∃ k' : Fin Y, j k' = j k := ⟨k, rfl⟩
      rw [dif_pos hex, Finset.mem_erase, hj hex.choose_spec] at hi
      exact hi.1
  rw [hfilt, Fintype.card_piFinset, ← Finset.prod_mul_prod_compl S]
  have hprodS : ∏ i ∈ S, (allowed i).card = (K - 1) ^ Y := by
    have hpt : ∀ i ∈ S, (allowed i).card = K - 1 := by
      intro i hi; obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      have hex : ∃ k' : Fin Y, j k' = j k := ⟨k, rfl⟩
      dsimp only [allowed]; rw [dif_pos hex, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    rw [Finset.prod_congr rfl hpt, Finset.prod_const, hScard]
  have hprodSc : ∏ i ∈ Sᶜ, (allowed i).card = K ^ (M - Y) := by
    have hpt : ∀ i ∈ Sᶜ, (allowed i).card = K := by
      intro i hi
      have hni : ¬ ∃ k : Fin Y, j k = i := by
        rintro ⟨k, rfl⟩; exact (Finset.mem_compl.mp hi) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
      dsimp only [allowed]; rw [dif_neg hni, Finset.card_fin]
    rw [Finset.prod_congr rfl hpt, Finset.prod_const, hScompl]
  rw [hprodS, hprodSc]

set_option maxHeartbeats 1600000 in
theorem hunter_coloring_exists (t : ℕ) (ht : 300 ≤ t) :
    let D := 200 * t
    let N := D ^ (200 * t ^ 2)
    let X := D ^ (10000 * t)
    ∃ isBlue : ℕ → Prop,
      (∀ a d_ap : ℕ, 1 ≤ a → 1 ≤ d_ap → a + 2 * d_ap ≤ N →
        ¬ (isBlue a ∧ isBlue (a + d_ap) ∧ isBlue (a + 2 * d_ap))) ∧
      (∀ a d_ap : ℕ, 1 ≤ a → 1 ≤ d_ap → a + (X - 1) * d_ap ≤ N →
        ∃ m < X, isBlue (a + m * d_ap)) := by
  intro D N X
  let ρ : ℝ := ((D : ℝ) ^ 4)⁻¹
  let M : ℕ := D ^ (208 * t)
  let Y : ℕ := D ^ (8 * t)
  let K : ℕ := D ^ (4 * t - 4)
  let δ : ℝ := ((D : ℝ) ^ (4 * t))⁻¹
  have hD_ge : 60000 ≤ D := by dsimp only [D]; omega
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hρ_pos : 0 < ρ := inv_pos.mpr (pow_pos hD_pos 4)
  have hδ_pos : 0 < δ := inv_pos.mpr (pow_pos hD_pos (4 * t))
  have hK_ge : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  have hK_mul_δ : (K : ℝ) * δ = ρ := by
    dsimp only [K, δ, ρ]
    rw [Nat.cast_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hD_pos.ne'),
      inv_mul_eq_div, eq_div_iff (pow_ne_zero _ hD_pos.ne'), ← pow_add]
    congr 1; omega
  have hρ_lt : ρ < 1 / 12 := by
    dsimp only [ρ]; rw [inv_lt_comm₀ (pow_pos hD_pos 4) (by norm_num)]
    have hD6 : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
    have h12 : (1 / 12 : ℝ)⁻¹ = 12 := by norm_num
    rw [h12]
    have hD2 : (60000 : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by nlinarith
    nlinarith
  obtain ⟨x, hx1, hx2⟩ := hunter_H1 t ht
  obtain ⟨θ, hθ1, hθ2⟩ := hunter_H2 t ht
  have hH3 := hunter_H3 t ht
  let isBlueOf (e : Fin M → Fin K) (n : ℕ) : Prop :=
    ∃ i : Fin M,
      (((e i : ℕ) : ℝ) * δ) ^ 2 ≤ ∑ b : Fin D, (tdist ((n : ℝ) * θ b - x i b)) ^ 2 ∧
      ∑ b : Fin D, (tdist ((n : ℝ) * θ b - x i b)) ^ 2 < ((((e i : ℕ) + 1 : ℕ) : ℝ) * δ) ^ 2
  -- Step 1: No blue 3-AP for ANY e : Fin M → Fin K
  have no_blue_3AP : ∀ (e : Fin M → Fin K) (a d_ap : ℕ),
      1 ≤ a → 1 ≤ d_ap → a + 2 * d_ap ≤ N →
      ¬ (isBlueOf e a ∧ isBlueOf e (a + d_ap) ∧ isBlueOf e (a + 2 * d_ap)) := by
    intro e a d_ap ha hd_pos hend ⟨⟨i0, h0lo, h0hi⟩, ⟨i1, h1lo, h1hi⟩, ⟨i2, h2lo, h2hi⟩⟩
    let r0 : Fin D → ℝ := fun b => (a : ℝ) * θ b - x i0 b - (round ((a : ℝ) * θ b - x i0 b) : ℝ)
    let r1 : Fin D → ℝ := fun b => ((a + d_ap : ℕ) : ℝ) * θ b - x i1 b -
      (round (((a + d_ap : ℕ) : ℝ) * θ b - x i1 b) : ℝ)
    let r2 : Fin D → ℝ := fun b => ((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i2 b -
      (round (((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i2 b) : ℝ)
    have hsq_eq : ∀ (r : Fin D → ℝ) (f : Fin D → ℝ),
        (∀ b, r b = f b - (round (f b) : ℝ)) →
        ∑ b : Fin D, (r b) ^ 2 = ∑ b : Fin D, (tdist (f b)) ^ 2 := fun r f hrf =>
      Finset.sum_congr rfl fun b _ => by rw [hrf b, tdist, sq_abs]
    have hr0_eq := hsq_eq r0 (fun b => (a : ℝ) * θ b - x i0 b) (fun _ => rfl)
    have hr1_eq := hsq_eq r1 (fun b => ((a + d_ap : ℕ) : ℝ) * θ b - x i1 b) (fun _ => rfl)
    have hr2_eq := hsq_eq r2 (fun b => ((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i2 b) (fun _ => rfl)
    rw [← hr0_eq] at h0lo h0hi; rw [← hr1_eq] at h1lo h1hi; rw [← hr2_eq] at h2lo h2hi
    have hrad : ∀ i : Fin M, ((((e i : ℕ) + 1 : ℕ) : ℝ) * δ) ≤ ρ := fun i =>
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (e i).isLt) hδ_pos.le).trans hK_mul_δ.le
    have coord_lt_ρ : ∀ (f : Fin D → ℝ), ∑ b : Fin D, (f b) ^ 2 < ρ ^ 2 → ∀ b, |f b| < ρ := by
      intro f hf b
      have := lt_of_le_of_lt (Finset.single_le_sum (fun j _ => sq_nonneg (f j)) (Finset.mem_univ b)) hf
      nlinarith [sq_abs (f b), abs_nonneg (f b)]
    have hr0_lt := coord_lt_ρ r0 (lt_of_lt_of_le h0hi (pow_le_pow_left₀ (by positivity) (hrad i0) 2))
    have hr1_lt := coord_lt_ρ r1 (lt_of_lt_of_le h1hi (pow_le_pow_left₀ (by positivity) (hrad i1) 2))
    have hr2_lt := coord_lt_ρ r2 (lt_of_lt_of_le h2hi (pow_le_pow_left₀ (by positivity) (hrad i2) 2))
    have hi_eq : i0 = i1 ∧ i1 = i2 := by
      by_contra hne
      obtain ⟨b, hb⟩ := hx1 i0 i1 i2 hne
      let m : ℤ := -(round ((a : ℝ) * θ b - x i0 b)) +
        2 * round (((a + d_ap : ℕ) : ℝ) * θ b - x i1 b) -
        round (((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i2 b)
      have hdiff : (x i0 b - 2 * x i1 b + x i2 b) - (-r0 b + 2 * r1 b - r2 b) = (m : ℝ) := by
        dsimp only [r0, r1, r2, m]; push_cast; ring
      rw [tdist_eq_of_sub_int m hdiff] at hb
      have htri : |-r0 b + 2 * r1 b - r2 b| < 4 * ρ := by
        have h0 := abs_lt.mp (hr0_lt b); have h1 := abs_lt.mp (hr1_lt b); have h2 := abs_lt.mp (hr2_lt b)
        rw [abs_lt]; constructor <;> linarith
      linarith [tdist_le_abs (-r0 b + 2 * r1 b - r2 b)]
    obtain ⟨rfl, rfl⟩ := hi_eq
    let v : Fin D → ℝ := fun b => r1 b - r0 b
    have hr2_lin : ∀ b : Fin D, r2 b = r0 b + 2 * v b := by
      intro b
      let m : ℤ := round ((a : ℝ) * θ b - x i0 b) -
        2 * round (((a + d_ap : ℕ) : ℝ) * θ b - x i0 b) +
        round (((a + 2 * d_ap : ℕ) : ℝ) * θ b - x i0 b)
      have hdiff : r2 b - (r0 b + 2 * v b) = -(m : ℝ) := by dsimp only [v, r0, r1, r2, m]; push_cast; ring
      have habs : |(m : ℝ)| < 1 / 2 := by
        have h0 := abs_lt.mp (hr0_lt b); have h1 := abs_lt.mp (hr1_lt b); have h2 := abs_lt.mp (hr2_lt b)
        have h3 : |r2 b - (r0 b + 2 * v b)| < 4 * ρ := by
          have : r2 b - (r0 b + 2 * v b) = r2 b - 2 * r1 b + r0 b := by dsimp only [v]; ring
          rw [this, abs_lt]; constructor <;> linarith
        rw [hdiff, abs_neg] at h3; linarith
      have hm0 : m = 0 := by
        have h1 : |(m : ℤ)| < 1 := by
          by_contra hge; push Not at hge
          have : (1 : ℝ) ≤ (|(m : ℤ)| : ℝ) := by exact_mod_cast hge
          have : |(m : ℝ)| = (|(m : ℤ)| : ℝ) := by simp
          linarith
        rw [abs_lt] at h1; omega
      rw [hm0] at hdiff; simp at hdiff; linarith
    have hpara : 2 * ∑ b : Fin D, (v b) ^ 2 =
        ∑ b : Fin D, (r0 b) ^ 2 + ∑ b : Fin D, (r2 b) ^ 2 - 2 * ∑ b : Fin D, (r1 b) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => by rw [hr2_lin b]; dsimp only [v]; ring
    have hv_sq : ∑ b : Fin D, (v b) ^ 2 < ((2 * (D : ℝ) ^ (2 * t))⁻¹) ^ 2 := by
      let k := (e i0 : ℕ)
      have hk_lt : k < K := (e i0).isLt
      have h1 : 2 * ∑ b : Fin D, (v b) ^ 2 < 2 * ((((k + 1 : ℕ) : ℝ) * δ) ^ 2 - ((k : ℝ) * δ) ^ 2) := by
        linarith [h0hi, h2hi, h1lo]
      have h2 : ((((k + 1 : ℕ) : ℝ) * δ) ^ 2 - ((k : ℝ) * δ) ^ 2) = (2 * (k : ℝ) + 1) * δ ^ 2 := by
        push_cast; ring
      have h3 : (2 * (k : ℝ) + 1) * δ ^ 2 ≤ 2 * ρ * δ := by
        have : (2 * (k : ℝ) + 1) ≤ 2 * (K : ℝ) := by exact_mod_cast (show 2 * k + 1 ≤ 2 * K by omega)
        calc (2 * (k : ℝ) + 1) * δ ^ 2 ≤ (2 * (K : ℝ)) * δ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg δ)
          _ = 2 * ((K : ℝ) * δ) * δ := by ring
          _ = 2 * ρ * δ := by rw [hK_mul_δ]
      have h4 : (1 / 4 : ℝ) * δ = ((2 * (D : ℝ) ^ (2 * t))⁻¹) ^ 2 := by
        dsimp only [δ]; rw [inv_pow, mul_pow, ← pow_mul, show 2 * t * 2 = 4 * t by omega]; ring
      nlinarith
    have hd_le_N : d_ap ≤ (200 * t) ^ (200 * t ^ 2) := by dsimp only [N, D] at hend; omega
    obtain ⟨b, hb⟩ := hθ1 d_ap hd_pos hd_le_N
    let mv : ℤ := round (((a + d_ap : ℕ) : ℝ) * θ b - x i0 b) - round ((a : ℝ) * θ b - x i0 b)
    have hdiff_v : (d_ap : ℝ) * θ b - v b = (mv : ℝ) := by dsimp only [v, r1, r0, mv]; push_cast; ring
    rw [tdist_eq_of_sub_int mv hdiff_v] at hb
    have hvb_sq : (v b) ^ 2 < ((2 * (D : ℝ) ^ (2 * t))⁻¹) ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ b)) hv_sq
    have hvb_lt : |v b| < (2 * (D : ℝ) ^ (2 * t))⁻¹ := by
      have : (0 : ℝ) < (2 * (D : ℝ) ^ (2 * t))⁻¹ := by positivity
      nlinarith [sq_abs (v b), abs_nonneg (v b)]
    linarith [tdist_le_abs (v b)]
  -- Step 2: Finite counting on Fin M → Fin K to avoid all red X-APs!
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let badFor (p : ℕ × ℕ) : Finset (Fin M → Fin K) :=
    Finset.univ.filter (fun e => p.1 + (X - 1) * p.2 ≤ N ∧ ∀ m < X, ¬ isBlueOf e (p.1 + m * p.2))
  have hbad_card : ∀ p ∈ pairs, (badFor p).card ≤ (K - 1) ^ Y * K ^ (M - Y) := by
    intro p hp
    by_cases hvalid : p.1 + (X - 1) * p.2 ≤ N
    · have hp1 := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
      have hp2 := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
      let a := p.1; let d_ap := p.2; let n1 : ℕ := a + (X / 2) * d_ap
      let Λ : Set (Fin D → ℤ) :=
        {ξ : Fin D → ℤ | (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) ∧
          tdist ((d_ap : ℝ) * ∑ b : Fin D, (ξ b : ℝ) * θ b) ≤ (D : ℝ) ^ (8 * D) / (X : ℝ)}
      obtain ⟨j, u, hj_inj, hu_norm, hu_close⟩ := hx2 Λ (hθ2 d_ap hp2.1 hp2.2) (fun b => (n1 : ℝ) * θ b)
      have hhit : ∀ k : Fin Y, ∃ (m : ℕ) (rk : Fin K), m < X ∧
          ∀ e : Fin M → Fin K, e (j k) = rk → isBlueOf e (a + m * d_ap) := by
        intro k
        have hclose_k : ∀ ξ : Fin D → ℤ, (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) →
            tdist (∑ b : Fin D, (ξ b : ℝ) * ((d_ap : ℝ) * θ b)) ≤ (D : ℝ) ^ (8 * D) / (X : ℝ) →
            tdist (∑ b : Fin D, (ξ b : ℝ) * (x (j k) b + u k b - (n1 : ℝ) * θ b)) < 1 / 100 := by
          intro ξ hξ_bd hξ_small
          have hsum_eq : ∑ b : Fin D, (ξ b : ℝ) * ((d_ap : ℝ) * θ b) =
              (d_ap : ℝ) * ∑ b : Fin D, (ξ b : ℝ) * θ b := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
          rw [hsum_eq] at hξ_small
          exact hu_close k ξ ⟨hξ_bd, hξ_small⟩ hξ_bd
        obtain ⟨s, hs_abs, hs_hit⟩ := hH3 (fun b => (d_ap : ℝ) * θ b) (fun b => (n1 : ℝ) * θ b)
          (x (j k)) (u k) (hu_norm k) hclose_k
        have hX5 : 5 ≤ X := le_trans (by omega : 5 ≤ D) (Nat.le_self_pow (by omega) D)
        have hs_abs' : |s| ≤ (X : ℤ) / 5 := hs_abs
        have hm_nn : (0 : ℤ) ≤ ((X / 2 : ℕ) : ℤ) + s := by have := (abs_le.mp hs_abs').1; omega
        let m : ℕ := (((X / 2 : ℕ) : ℤ) + s).toNat
        have hm_cast : (m : ℤ) = ((X / 2 : ℕ) : ℤ) + s := Int.toNat_of_nonneg hm_nn
        have hm_lt : m < X := by have := (abs_le.mp hs_abs').2; omega
        have hval_eq : ((a + m * d_ap : ℕ) : ℝ) = (n1 : ℝ) + (s : ℝ) * (d_ap : ℝ) := by
          have hZ : ((a + m * d_ap : ℕ) : ℤ) = (n1 : ℤ) + s * (d_ap : ℤ) := by
            dsimp only [n1]; rw [Nat.cast_add, Nat.cast_mul, hm_cast, Nat.cast_add, Nat.cast_mul]; ring
          exact_mod_cast hZ
        let distSq : ℝ := ∑ b : Fin D, (tdist (((a + m * d_ap : ℕ) : ℝ) * θ b - x (j k) b)) ^ 2
        have hdistSq_lt : distSq < (ρ / 5) ^ 2 := by
          convert hs_hit using 1
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hval_eq]; congr 2; ring
        have hdistSq_nn : 0 ≤ distSq := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hsqrt_lt : Real.sqrt distSq < ρ := by
          have : Real.sqrt distSq < ρ / 5 := (Real.sqrt_lt' (by positivity)).mpr hdistSq_lt
          linarith
        let r_nat : ℕ := Nat.floor (Real.sqrt distSq * (D : ℝ) ^ (4 * t))
        have hr_lt : r_nat < K := by
          rw [Nat.floor_lt (by positivity)]
          calc Real.sqrt distSq * (D : ℝ) ^ (4 * t) < ρ * (D : ℝ) ^ (4 * t) :=
                mul_lt_mul_of_pos_right hsqrt_lt (pow_pos hD_pos _)
            _ = (K : ℝ) := by rw [← hK_mul_δ]; dsimp only [δ]; field_simp [hD_pos.ne']
        have hlo_r : ((r_nat : ℝ) * δ) ^ 2 ≤ distSq := by
          have h1 := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity) :
            (r_nat : ℝ) ≤ Real.sqrt distSq * (D : ℝ) ^ (4 * t)) hδ_pos.le
          have h2 : Real.sqrt distSq * (D : ℝ) ^ (4 * t) * δ = Real.sqrt distSq := by
            dsimp only [δ]; field_simp [hD_pos.ne']
          calc ((r_nat : ℝ) * δ) ^ 2 ≤ (Real.sqrt distSq) ^ 2 :=
                pow_le_pow_left₀ (by positivity) (by linarith) 2
            _ = distSq := Real.sq_sqrt hdistSq_nn
        have hhi_r : distSq < ((((r_nat + 1 : ℕ) : ℝ)) * δ) ^ 2 := by
          have hlt : Real.sqrt distSq * (D : ℝ) ^ (4 * t) < ((r_nat + 1 : ℕ) : ℝ) := by
            push_cast; exact Nat.lt_floor_add_one _
          have h1 := mul_lt_mul_of_pos_right hlt hδ_pos
          have h2 : Real.sqrt distSq * (D : ℝ) ^ (4 * t) * δ = Real.sqrt distSq := by
            dsimp only [δ]; field_simp [hD_pos.ne']
          calc distSq = (Real.sqrt distSq) ^ 2 := (Real.sq_sqrt hdistSq_nn).symm
            _ < (((r_nat + 1 : ℕ) : ℝ) * δ) ^ 2 :=
                pow_lt_pow_left₀ (by linarith) (Real.sqrt_nonneg _) (by omega)
        refine ⟨m, ⟨r_nat, hr_lt⟩, hm_lt, fun e heq => ⟨j k, ?_, ?_⟩⟩
        · rw [congrArg Fin.val heq]; exact hlo_r
        · rw [congrArg Fin.val heq]; exact hhi_r
      choose m_of r_of hm_lt hblue_of using hhit
      have hsub : badFor p ⊆
          Finset.univ.filter (fun e : Fin M → Fin K => ∀ k : Fin Y, e (j k) ≠ r_of k) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨Finset.mem_univ _, fun k heq => he.2.2 (m_of k) (hm_lt k) (hblue_of k e heq)⟩
      exact (Finset.card_le_card hsub).trans (card_avoiding_funs j hj_inj r_of).le
    · have : badFor p = ∅ := by ext e; simp [badFor, hvalid]
      rw [this]; simp
  have hunion_lt : (pairs.biUnion badFor).card < Fintype.card (Fin M → Fin K) := by
    have hcard_bi : (pairs.biUnion badFor).card ≤ N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y)) := by
      calc (pairs.biUnion badFor).card ≤ ∑ p ∈ pairs, (badFor p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ pairs, ((K - 1) ^ Y * K ^ (M - Y)) := Finset.sum_le_sum hbad_card
        _ = N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y)) := by simp [pairs, sq]
    let q : ℕ := D ^ (4 * t + 4)
    have hY_eq : Y = K * q := by dsimp only [Y, K, q]; rw [← pow_add]; congr 1; omega
    have hpow_q : 2 ^ q * (K - 1) ^ Y ≤ K ^ Y := by
      rw [hY_eq, pow_mul, pow_mul, ← mul_pow]
      exact Nat.pow_le_pow_left (pow_ge_two_mul_pred_pow K hK_ge) q
    have hN2_lt : N ^ 2 < 2 ^ q := by
      have hN2_le : N ^ 2 ≤ 2 ^ (400 * D * t ^ 2) := by
        calc N ^ 2 = D ^ (400 * t ^ 2) := by dsimp only [N]; rw [← pow_mul]; congr 1; ring
          _ ≤ (2 ^ D) ^ (400 * t ^ 2) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
          _ = 2 ^ (400 * D * t ^ 2) := by rw [← pow_mul]; congr 1; ring
      have hexp_lt : 400 * D * t ^ 2 < q := by
        have hq_ge : D ^ 4 ≤ q := Nat.pow_le_pow_right (by omega) (by omega)
        have h4 : 400 * D * t ^ 2 < D ^ 4 := by
          have ht2 : 0 < t ^ 2 := by nlinarith
          have hD_eq : D = 200 * t := rfl
          have h1 : 400 * t ^ 2 < D ^ 3 := by
            have : D ^ 3 = (200 * t) * (200 * t) * (200 * t) := by rw [hD_eq]; ring
            nlinarith
          have h2 : D ^ 4 = D * D ^ 3 := by ring
          nlinarith
        omega
      exact lt_of_le_of_lt hN2_le (Nat.pow_lt_pow_right (by omega) hexp_lt)
    have hYM : Y ≤ M := Nat.pow_le_pow_right (by omega) (by omega)
    have hK2 : 2 ≤ K := le_trans (by omega : 2 ≤ D) (Nat.le_self_pow (by omega) D)
    have hstrict : N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y)) < K ^ M := by
      calc N ^ 2 * ((K - 1) ^ Y * K ^ (M - Y))
          = (N ^ 2 * (K - 1) ^ Y) * K ^ (M - Y) := by ring
        _ < (2 ^ q * (K - 1) ^ Y) * K ^ (M - Y) :=
            Nat.mul_lt_mul_of_pos_right
              (Nat.mul_lt_mul_of_pos_right hN2_lt (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
        _ ≤ K ^ Y * K ^ (M - Y) := Nat.mul_le_mul_right _ hpow_q
        _ = K ^ M := by rw [← pow_add, Nat.add_sub_cancel' hYM]
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact lt_of_le_of_lt hcard_bi hstrict
  have hex_e : ∃ e : Fin M → Fin K, e ∉ pairs.biUnion badFor := by
    by_contra hall; push Not at hall
    have hle := Finset.card_le_card (fun e _ => hall e : Finset.univ ⊆ pairs.biUnion badFor)
    rw [Finset.card_univ] at hle; omega
  obtain ⟨e, he⟩ := hex_e
  refine ⟨isBlueOf e, no_blue_3AP e, fun a d_ap ha hd hend => ?_⟩
  by_contra hall; push Not at hall
  apply he
  have hX1 : 1 ≤ X - 1 := by
    have : 2 ≤ X := le_trans (by omega : 2 ≤ D) (Nat.le_self_pow (by omega) D); omega
  have hd_le : d_ap ≤ N := le_trans (Nat.le_mul_of_pos_left d_ap hX1) (by omega)
  exact Finset.mem_biUnion.mpr ⟨(a, d_ap),
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha, by omega⟩, Finset.mem_Icc.mpr ⟨hd, hd_le⟩⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hend, hall⟩⟩

/- ## Section 7: Bridge to `Green14.W` and Hunter's asymptotic bound -/

private lemma mixedMonoAPGuaranteeSet_nonempty (k r : ℕ) :
    (Green14.mixedMonoAPGuaranteeSet k r).Nonempty := by
  let m := max 1 (max k r)
  obtain ⟨ι, instι, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin m) (Fin 2)
  let _ : Fintype ι := instι
  let N := Fintype.card ι * (m - 1) + 1
  have word_sum_le (v : ι → Fin m) : ∑ i, (v i : ℕ) ≤ Fintype.card ι * (m - 1) := by
    calc ∑ i, (v i : ℕ) ≤ ∑ _i : ι, (m - 1) :=
          Finset.sum_le_sum fun i _ => Nat.le_pred_of_lt (v i).isLt
      _ = Fintype.card ι * (m - 1) := by simp
  refine ⟨N, fun coloring => ?_⟩
  let wordPoint (v : ι → Fin m) : Set.Icc 1 N :=
    ⟨1 + ∑ i, (v i : ℕ), ⟨by omega, by dsimp only [N]; have := word_sum_le v; omega⟩⟩
  obtain ⟨line, color, hmono⟩ := hι (fun v => coloring (wordPoint v))
  set active : Finset ι := Finset.univ.filter (fun i => line.idxFun i = none) with hactive
  let a : ℕ := active.card
  let b : ℕ := ∑ i ∈ activeᶜ, ((line.idxFun i).map fun x : Fin m => (x : ℕ)).getD 0
  have ha : 0 < a := Finset.card_pos.mpr ⟨line.proper.choose, by
    rw [hactive, Finset.mem_filter]; exact ⟨Finset.mem_univ _, line.proper.choose_spec⟩⟩
  have line_sum (x : Fin m) : ∑ i, ((line x i : Fin m) : ℕ) = a * (x : ℕ) + b := by
    rw [← Finset.sum_add_sum_compl active]
    congr 1
    · calc ∑ i ∈ active, ((line x i : Fin m) : ℕ) = ∑ _i ∈ active, (x : ℕ) :=
            Finset.sum_congr rfl fun i hi => by
              have hnone : line.idxFun i = none := by rw [hactive, Finset.mem_filter] at hi; exact hi.2
              simp [Combinatorics.Line.coe_apply, hnone]
        _ = a * (x : ℕ) := by simp [a]
    · refine Finset.sum_congr rfl fun i hi => ?_
      cases hopt : line.idxFun i with
      | none => exact ((Finset.mem_compl.mp hi) (by rw [hactive, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hopt⟩)).elim
      | some y => simp [Combinatorics.Line.coe_apply, hopt]
  have build_ap (q : ℕ) (hqm : q ≤ m) :
      ∃ s : Finset (Set.Icc 1 N), ({(z : ℕ) | z ∈ s}).IsAPOfLength q ∧ ∀ z ∈ s, coloring z = color := by
    let liftFin : Fin q → Fin m := fun x => Fin.castLE hqm x
    let value : Fin q → ℕ := fun x => a * (x : ℕ) + b + 1
    have hval_inj : Function.Injective value := fun x y hxy =>
      Fin.ext (Nat.eq_of_mul_eq_mul_left ha (by dsimp only [value] at hxy; omega))
    let point : Fin q → Set.Icc 1 N := fun x =>
      ⟨value x, ⟨by dsimp only [value]; omega, by
        have hp := (wordPoint (line (liftFin x))).property.2
        dsimp only [wordPoint] at hp; rw [line_sum] at hp
        simpa [liftFin, value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩⟩
    let emb : Fin q ↪ Set.Icc 1 N := ⟨point, fun x y hxy => hval_inj (Subtype.ext_iff.mp hxy)⟩
    refine ⟨Finset.univ.map emb, ⟨b + 1, a, ?_, ?_⟩, fun z hz => ?_⟩
    · have hsets : ({(z : ℕ) | z ∈ Finset.univ.map emb} : Set ℕ) = Set.range value := by
        ext z
        simp only [Set.mem_ofPred_eq, Finset.mem_map, Finset.mem_univ, true_and, Set.mem_range]
        constructor
        · rintro ⟨y, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩; exact ⟨point x, ⟨x, rfl⟩, rfl⟩
      rw [hsets, _root_.ENat.card_coe_set_eq, ← Set.image_univ, hval_inj.encard_image]; simp
    · ext z
      simp only [Set.mem_ofPred_eq, Finset.mem_map, Finset.mem_univ, true_and,
        ENat.natCast_lt_natCast, nsmul_eq_mul]
      constructor
      · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
        exact ⟨x.val, x.isLt, by change b + 1 + x.val * a = value x; dsimp only [value]; ring⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨point ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩, by simp only [point, value, Nat.cast_id]; ring⟩
    · rcases Finset.mem_map.mp hz with ⟨x, -, rfl⟩
      have hpw : point x = wordPoint (line (liftFin x)) := by
        apply Subtype.ext; dsimp only [point, value, wordPoint]; rw [line_sum]; simp [liftFin, Nat.add_comm]
      change coloring (point x) = color; rw [hpw]; exact hmono (liftFin x)
  fin_cases color
  · exact Or.inl (build_ap k (le_trans (le_max_left k r) (le_max_right 1 _)))
  · exact Or.inr (build_ap r (le_trans (le_max_right k r) (le_max_right 1 _)))

private lemma mixedMonoAPGuaranteeSet_upward {k r M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ Green14.mixedMonoAPGuaranteeSet k r) : N ∈ Green14.mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Set.Icc 1 M ↪ Set.Icc 1 N := ⟨fun x => ⟨x, x.2.1, x.2.2.trans hMN⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : Set.Icc 1 N => (z : ℕ)) h)⟩
  have lift : ∀ l c (s : Finset (Set.Icc 1 M)),
      ({(x : ℕ) | x ∈ s} : Set ℕ).IsAPOfLength l → (∀ x ∈ s, coloring (emb x) = c) →
      ∃ t : Finset (Set.Icc 1 N), ({(x : ℕ) | x ∈ t} : Set ℕ).IsAPOfLength l ∧ ∀ x ∈ t, coloring x = c := by
    intro l c s hAP hc
    refine ⟨s.map emb, ?_, fun x hx => by rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩; exact hc y hy⟩
    convert hAP using 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨emb x, Finset.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩
  rcases hM (coloring ∘ emb) with ⟨s, hAP, hc⟩ | ⟨s, hAP, hc⟩
  · exact Or.inl (lift k 0 s hAP hc)
  · exact Or.inr (lift r 1 s hAP hc)

private lemma isAPOfLength_extract {N k : ℕ} (hk : 2 ≤ k) {s : Finset (Set.Icc 1 N)}
    (hAP : ({(x : ℕ) | x ∈ s} : Set ℕ).IsAPOfLength k) :
    ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
      ∀ i < k, ∃ x ∈ s, (x : ℕ) = a + i * d := by
  rcases hAP with ⟨a, d, hcard, hset⟩
  have term_mem : ∀ i < k, ∃ x ∈ s, (x : ℕ) = a + i * d := by
    intro i hi
    have : a + i * d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ) := by
      rw [hset]; exact ⟨i, by exact_mod_cast hi, by simp⟩
    exact this
  obtain ⟨x0, _, hx0⟩ := term_mem 0 (by omega)
  obtain ⟨xl, _, hxl⟩ := term_mem (k - 1) (by omega)
  have hdpos : 1 ≤ d := by
    by_contra h0
    have hd0 : d = 0 := by omega
    have hsub : ({(x : ℕ) | x ∈ s} : Set ℕ) ⊆ {a} := by
      intro z hz; rw [hset] at hz; rcases hz with ⟨i, _, rfl⟩; simp [hd0]
    have hle : ({(x : ℕ) | x ∈ s} : Set ℕ).encard ≤ 1 :=
      (Set.encard_le_encard hsub).trans (Set.encard_singleton a).le
    rw [← _root_.ENat.card_coe_set_eq] at hle
    rw [hcard] at hle
    have : k ≤ 1 := by exact_mod_cast hle
    omega
  exact ⟨a, d, by simpa [hx0] using x0.2.1, hdpos, by simpa [hxl] using xl.2.2, term_mem⟩

lemma W_three_ge_of_hunter (t : ℕ) (ht : 300 ≤ t) {r : ℕ}
    (hr : (200 * t) ^ (10000 * t) ≤ r) :
    (200 * t) ^ (200 * t ^ 2) + 1 ≤ Green14.W 3 r := by
  let D := 200 * t
  let N := D ^ (200 * t ^ 2)
  let X := D ^ (10000 * t)
  obtain ⟨isBlue, hno3, hnoX⟩ := hunter_coloring_exists t ht
  have hnot_mem : N ∉ Green14.mixedMonoAPGuaranteeSet 3 r := by
    intro hmem
    let coloring : Set.Icc 1 N → Fin 2 := fun z => if isBlue z.1 then 0 else 1
    rcases hmem coloring with ⟨s, hAP, hc⟩ | ⟨s, hAP, hc⟩
    · obtain ⟨a, d_ap, ha, hd, hend, hterms⟩ := isAPOfLength_extract (by omega) hAP
      have hmem_blue : ∀ i < 3, isBlue (a + i * d_ap) := by
        intro i hi
        obtain ⟨x, hx, hxv⟩ := hterms i hi
        have hcx := hc x hx; dsimp only [coloring] at hcx; rw [hxv] at hcx
        by_contra hnb; simp [hnb] at hcx
      exact hno3 a d_ap ha hd (by omega)
        ⟨by simpa using hmem_blue 0 (by omega),
         by simpa using hmem_blue 1 (by omega),
         hmem_blue 2 (by omega)⟩
    · have hX2 : 2 ≤ X := le_trans (by dsimp only [D]; omega : 2 ≤ D) (Nat.le_self_pow (by omega) D)
      have hrX : X ≤ r := hr
      obtain ⟨a, d_ap, ha, hd, hend, hterms⟩ := isAPOfLength_extract (by omega : 2 ≤ r) hAP
      have hendX : a + (X - 1) * d_ap ≤ N :=
        le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right d_ap (by omega)) a) hend
      obtain ⟨m, hm, hbm⟩ := hnoX a d_ap ha hd hendX
      obtain ⟨x, hx, hxv⟩ := hterms m (lt_of_lt_of_le hm hrX)
      have hcx := hc x hx; dsimp only [coloring] at hcx; rw [hxv, if_pos hbm] at hcx
      exact absurd hcx (by decide)
  rw [Green14.W]
  apply le_csInf (mixedMonoAPGuaranteeSet_nonempty 3 r)
  intro b hb
  by_contra hlt
  have hbN : b ≤ N := by dsimp only [N, D]; omega
  exact hnot_mem (mixedMonoAPGuaranteeSet_upward hbN hb)

private def Xf (t : ℕ) : ℕ := (200 * t) ^ (10000 * t)

/-- Concrete quantitative lower bound: `W(3, r) ≥ exp(c * (log r)^2 / log (log r))` for all large `r`. -/
theorem hunter_explicit_bound :
    ∃ (c : ℝ) (R₀ : ℕ), 0 < c ∧ 100 ≤ R₀ ∧
      ∀ r ≥ R₀, Real.exp (c * (Real.log (r : ℝ)) ^ 2 / Real.log (Real.log (r : ℝ))) ≤ (Green14.W 3 r : ℝ) := by
  refine ⟨1 / 8000000, max 100 (Xf 300), by norm_num, le_max_left _ _, fun r hr => ?_⟩
  have hr100 : 100 ≤ r := le_trans (le_max_left _ _) hr
  have hrX300 : Xf 300 ≤ r := le_trans (le_max_right _ _) hr
  -- Find t ≥ 300 with Xf t ≤ r < Xf (t + 1)
  have hex_t : ∃ t : ℕ, 300 ≤ t ∧ r < Xf (t + 1) ∧ Xf t ≤ r := by
    have hex_gt : ∃ s : ℕ, 300 ≤ s ∧ r < Xf (s + 1) := by
      refine ⟨max 300 r, le_max_left _ _, ?_⟩
      let s := max 300 r
      have hrs : r < 200 * (s + 1) := by dsimp only [s]; omega
      exact lt_of_lt_of_le hrs (Nat.le_self_pow (by omega) (200 * (s + 1)))
    let t : ℕ := Nat.find hex_gt
    have ht_spec : 300 ≤ t ∧ r < Xf (t + 1) := Nat.find_spec hex_gt
    refine ⟨t, ht_spec.1, ht_spec.2, ?_⟩
    by_cases h300 : t = 300
    · rw [h300]; exact hrX300
    · have hmin := Nat.find_min hex_gt (show t - 1 < t by omega)
      push Not at hmin
      have hge := hmin (by omega)
      rwa [show t - 1 + 1 = t by omega] at hge
  obtain ⟨t, ht300, hr_lt, hXf_le⟩ := hex_t
  clear hr hrX300
  -- Deduce log r bounds in terms of t and D = 200 * t!
  let D : ℕ := 200 * t
  have hD_ge : 60000 ≤ D := by dsimp only [D]; omega
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hlogD_ge1 : 1 ≤ Real.log (D : ℝ) := by
    have heD : Real.exp 1 ≤ (D : ℝ) := by
      have : (60000 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_ge
      linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) heD
  have hlog_r_le : Real.log (r : ℝ) ≤ 40000 * (t : ℝ) * Real.log (D : ℝ) := by
    have h1 : (r : ℝ) ≤ ((200 * (t + 1) : ℕ) : ℝ) ^ (10000 * (t + 1)) := by
      exact_mod_cast hr_lt.le
    have hlog1 : Real.log (r : ℝ) ≤ ((10000 * (t + 1) : ℕ) : ℝ) * Real.log ((200 * (t + 1) : ℕ) : ℝ) := by
      calc Real.log (r : ℝ) ≤ Real.log (((200 * (t + 1) : ℕ) : ℝ) ^ (10000 * (t + 1))) :=
            Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) h1
        _ = ((10000 * (t + 1) : ℕ) : ℝ) * Real.log ((200 * (t + 1) : ℕ) : ℝ) := Real.log_pow _ _
    have h2 : ((200 * (t + 1) : ℕ) : ℝ) ≤ (D : ℝ) ^ 2 := by
      have : 200 * (t + 1) ≤ D ^ 2 := by
        calc 200 * (t + 1) ≤ (200 * t) * 2 := by omega
          _ ≤ (200 * t) * (200 * t) := Nat.mul_le_mul_left _ (by omega)
          _ = D ^ 2 := by dsimp only [D]; ring
      exact_mod_cast this
    have hlog2 : Real.log ((200 * (t + 1) : ℕ) : ℝ) ≤ 2 * Real.log (D : ℝ) := by
      calc Real.log ((200 * (t + 1) : ℕ) : ℝ) ≤ Real.log ((D : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) h2
        _ = 2 * Real.log (D : ℝ) := by rw [Real.log_pow]; norm_num
    have htp1 : ((10000 * (t + 1) : ℕ) : ℝ) ≤ 20000 * (t : ℝ) := by
      push_cast
      have : (300 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht300
      linarith
    calc Real.log (r : ℝ) ≤ ((10000 * (t + 1) : ℕ) : ℝ) * Real.log ((200 * (t + 1) : ℕ) : ℝ) := hlog1
      _ ≤ (20000 * (t : ℝ)) * (2 * Real.log (D : ℝ)) :=
          mul_le_mul htp1 hlog2 (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 200 * (t + 1) by omega))) (by positivity)
      _ = 40000 * (t : ℝ) * Real.log (D : ℝ) := by ring
  have hlog_r_ge : (D : ℝ) ≤ Real.log (r : ℝ) := by
    have h1 : ((D : ℝ) ^ (10000 * t)) ≤ (r : ℝ) := by exact_mod_cast hXf_le
    have hlog1 : ((10000 * t : ℕ) : ℝ) * Real.log (D : ℝ) ≤ Real.log (r : ℝ) := by
      calc ((10000 * t : ℕ) : ℝ) * Real.log (D : ℝ) = Real.log ((D : ℝ) ^ (10000 * t)) := (Real.log_pow _ _).symm
        _ ≤ Real.log (r : ℝ) := Real.log_le_log (pow_pos hD_pos _) h1
    have hD_le : (D : ℝ) ≤ ((10000 * t : ℕ) : ℝ) * Real.log (D : ℝ) := by
      have hDt : (D : ℝ) ≤ ((10000 * t : ℕ) : ℝ) := by dsimp only [D]; push_cast; linarith
      calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
        _ ≤ ((10000 * t : ℕ) : ℝ) * Real.log (D : ℝ) :=
          mul_le_mul hDt hlogD_ge1 zero_le_one (by positivity)
    exact hD_le.trans hlog1
  have hlogD_le_ll : Real.log (D : ℝ) ≤ Real.log (Real.log (r : ℝ)) :=
    Real.log_le_log hD_pos hlog_r_ge
  have hll_pos : 0 < Real.log (Real.log (r : ℝ)) := lt_of_lt_of_le (by linarith) hlogD_le_ll
  have hlog_r_pos : 0 < Real.log (r : ℝ) := lt_of_lt_of_le hD_pos hlog_r_ge
  -- Compare exponent with log(D^(200 t^2)) = 200 t^2 log D!
  have hexp_le : (1 / 8000000 : ℝ) * (Real.log (r : ℝ)) ^ 2 / Real.log (Real.log (r : ℝ)) ≤
      ((200 * t ^ 2 : ℕ) : ℝ) * Real.log (D : ℝ) := by
    rw [div_le_iff₀ hll_pos]
    have hsq : (Real.log (r : ℝ)) ^ 2 ≤ (40000 * (t : ℝ) * Real.log (D : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog_r_pos.le hlog_r_le 2
    have h1 : (1 / 8000000 : ℝ) * (Real.log (r : ℝ)) ^ 2 ≤
        ((200 * t ^ 2 : ℕ) : ℝ) * Real.log (D : ℝ) * Real.log (D : ℝ) := by
      calc (1 / 8000000 : ℝ) * (Real.log (r : ℝ)) ^ 2
          ≤ (1 / 8000000 : ℝ) * (40000 * (t : ℝ) * Real.log (D : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = ((200 * t ^ 2 : ℕ) : ℝ) * Real.log (D : ℝ) * Real.log (D : ℝ) := by push_cast; ring
    exact h1.trans (mul_le_mul_of_nonneg_left hlogD_le_ll (by positivity))
  have hW_ge := W_three_ge_of_hunter t ht300 hXf_le
  have hN_le_W : ((D : ℝ) ^ (200 * t ^ 2)) ≤ (Green14.W 3 r : ℝ) := by
    have : D ^ (200 * t ^ 2) ≤ Green14.W 3 r := by dsimp only [D]; omega
    exact_mod_cast this
  calc Real.exp ((1 / 8000000 : ℝ) * (Real.log (r : ℝ)) ^ 2 / Real.log (Real.log (r : ℝ)))
      ≤ Real.exp (((200 * t ^ 2 : ℕ) : ℝ) * Real.log (D : ℝ)) := Real.exp_le_exp.mpr hexp_le
    _ = (D : ℝ) ^ (200 * t ^ 2) := by rw [Real.exp_nat_mul, Real.exp_log hD_pos]
    _ ≤ (Green14.W 3 r : ℝ) := hN_le_W

end OMA.Hunter

open Filter Topology

theorem OMA.solution : type_of% @Green14.green_14_polynomial_k_eq_3 := by
  rintro ⟨d, hO⟩
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [Filter.eventually_atTop] at hC
  obtain ⟨R₀, hR0⟩ := hC
  let t : ℕ := max 300 (max R₀ (max (50 * d + 1) (Nat.ceil (max C 1) + 1)))
  have ht300 : 300 ≤ t := le_max_left _ _
  have htR0 : R₀ ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have htd : 50 * d + 1 ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have htC : Nat.ceil (max C 1) + 1 ≤ t :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  let D : ℕ := 200 * t
  let X : ℕ := D ^ (10000 * t)
  let N : ℕ := D ^ (200 * t ^ 2)
  have hX_ge_R0 : R₀ ≤ X := by
    calc R₀ ≤ t := htR0
      _ ≤ D := by dsimp only [D]; omega
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ (10000 * t) := Nat.pow_le_pow_right (by dsimp only [D]; omega) (by omega)
  have hW_ge : N + 1 ≤ Green14.W 3 X := OMA.Hunter.W_three_ge_of_hunter t ht300 le_rfl
  have hW_le := hR0 X hX_ge_R0
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)] at hW_le
  have hC_lt_D : C < (D : ℝ) := by
    have h1 : C ≤ (Nat.ceil (max C 1) : ℝ) := le_trans (le_max_left C 1) (Nat.le_ceil _)
    have h2 : (Nat.ceil (max C 1) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast htC
    have h3 : (t : ℝ) ≤ (D : ℝ) := by dsimp only [D]; exact_mod_cast (show t ≤ 200 * t by omega)
    linarith
  have hexp : 10000 * t * d + 1 ≤ 200 * t ^ 2 := by nlinarith
  have hNat : D * X ^ d ≤ N := by
    dsimp only [X, N]
    rw [← pow_mul, ← pow_succ']
    exact Nat.pow_le_pow_right (by dsimp only [D]; omega) hexp
  have hReal : (D : ℝ) * (X : ℝ) ^ d ≤ (N : ℝ) := by exact_mod_cast hNat
  have hXd_pos : (0 : ℝ) < (X : ℝ) ^ d := by
    have hXpos : 0 < X := Nat.pow_pos (show 0 < D by dsimp only [D]; omega)
    exact_mod_cast Nat.pow_pos hXpos (n := d)
  have hN_gt : C * (X : ℝ) ^ d < (N : ℝ) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hC_lt_D hXd_pos) hReal
  have hW_ge_R : (N : ℝ) + 1 ≤ (Green14.W 3 X : ℝ) := by exact_mod_cast hW_ge
  linarith
