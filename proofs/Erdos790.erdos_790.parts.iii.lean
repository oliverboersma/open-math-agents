import FormalConjectures.ErdosProblems.«790»
import Mathlib

/-!
# Erdos Problem 790

The core of this file (namespace OMA790, renamed from Erdos790 to avoid clashing with the
upstream statement file) is adapted from the Lean 4 formalization in
https://github.com/hongjin-he/erdos-lean (directory ErdosLean/Erdos790, commit efede969),
released under the Apache License 2.0. It formalizes Samuel Korsky, Large Sum-Free Subsets of
Sets of Integers (preprint, 2026), Theorem 1: l(n) is at least n / (1024 (log n)^2).
Changes: the modules are concatenated in dependency order, comments are removed, the namespace
is renamed, and Mathlib API drift is repaired. The final section bridges the source definition
of l to the one in FormalConjectures.ErdosProblems.790 and derives the target statement.
-/

-- Statement
section
namespace OMA790

open Filter

def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ x ∈ B, ∀ S ⊆ B, x ∉ S → 2 ≤ S.card → ∑ s ∈ S, s ≠ x

noncomputable def l (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ k ≤ B.card}

def Erdos790Answer : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → c * n / Real.log n ^ 2 ≤ l n) ∧
  (∀ n : ℕ, l n ≤ n) ∧
  Tendsto (fun n : ℕ => (l n : ℝ) / Real.sqrt n) atTop atTop ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ l n) ∧
  ¬ (∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c))

end OMA790
end

-- Defs
section
namespace OMA790

noncomputable def elem (A : Finset ℤ) (s : ℕ) : ℤ :=
  if h : s < A.card then A.orderEmbOfFin rfl ⟨s, h⟩ else 0

def rank (A : Finset ℤ) (a : ℤ) : ℕ := (A.filter (· < a)).card

def splitPt (h i : ℕ) : ℕ := i / 2 ^ (h + 1) * 2 ^ (h + 1) + 2 ^ h

noncomputable def Dset (A : Finset ℤ) (a : ℤ) : Finset ℤ :=
  ((Finset.range (Nat.clog 2 A.card)).filter (fun h => splitPt h (rank A a) < A.card)).image
    (fun h => |elem A (splitPt h (rank A a)) - a|)

noncomputable def Dplus (A : Finset ℤ) (a : ℤ) : Finset ℤ := insert a (Dset A a)

def dyIdx (a : ℤ) : ℕ := Nat.log 2 a.toNat

def topIdx (A : Finset ℤ) : ℕ := A.sup dyIdx

def window (N : ℕ) (δ : ℤ) (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter
    (fun j => δ ≤ 2 * (N : ℤ) * 2 ^ (j + 1) ∧ (2 : ℤ) ^ j ≤ 2 * δ)

noncomputable def Fset (A : Finset ℤ) (a : ℤ) : Finset ℕ :=
  ((Dplus A a).biUnion (fun δ => window A.card δ (topIdx A))).erase (dyIdx a)

def K (N : ℕ) : ℕ := (Nat.clog 2 N + 1) * (Nat.clog 2 N + 5)

def idx (A : Finset ℤ) (j : ℕ) : Fin (topIdx A + 1) := Fin.ofNat (topIdx A + 1) j

end OMA790
end

-- BitSplit
section
namespace OMA790

theorem bit_split (L i k : ℕ) (hik : i < k) (hk : k < 2 ^ L) :
    ∃ h < L, splitPt h i = splitPt h k ∧ i < splitPt h i ∧ splitPt h k ≤ k := by
  have hex : ∃ m, i / 2 ^ m = k / 2 ^ m :=
    ⟨L, by rw [Nat.div_eq_of_lt hk, Nat.div_eq_of_lt (hik.trans hk)]⟩
  classical
  obtain ⟨m, hmspec, hmL, hm0, hmin⟩ : ∃ m, i / 2 ^ m = k / 2 ^ m ∧ m ≤ L ∧ m ≠ 0 ∧
      ∀ j < m, i / 2 ^ j ≠ k / 2 ^ j := by
    refine ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex
      (by rw [Nat.div_eq_of_lt hk, Nat.div_eq_of_lt (hik.trans hk)]), ?_,
      fun j hj => Nat.find_min hex hj⟩
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp at this
    omega
  obtain ⟨h, rfl⟩ : ∃ h, m = h + 1 := ⟨m - 1, by omega⟩
  have hne : i / 2 ^ h ≠ k / 2 ^ h := hmin h (by omega)
  have hpos : 0 < 2 ^ h := by positivity
  set q := i / 2 ^ (h + 1) with hq
  have hi2 : i / 2 ^ h / 2 = q := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hk2 : k / 2 ^ h / 2 = q := by rw [Nat.div_div_eq_div_mul, ← pow_succ, ← hmspec]
  have hle : i / 2 ^ h ≤ k / 2 ^ h := Nat.div_le_div_right hik.le
  have hia : i / 2 ^ h = 2 * q := by omega
  have hka : k / 2 ^ h = 2 * q + 1 := by omega
  have hsp : splitPt h i = (2 * q + 1) * 2 ^ h := by
    unfold splitPt; rw [← hq, pow_succ]; ring
  have hspk : splitPt h k = splitPt h i := by
    unfold splitPt; rw [← hmspec]
  refine ⟨h, by omega, hspk.symm, ?_, ?_⟩
  · rw [hsp]
    exact (Nat.div_lt_iff_lt_mul hpos).1 (by omega)
  · rw [hspk, hsp]
    exact (Nat.le_div_iff_mul_le hpos).1 (by omega)

end OMA790
end

-- RankElem
section
namespace OMA790

lemma exists_orderEmb_eq (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) :
    ∃ i : Fin A.card, A.orderEmbOfFin rfl i = a := by
  have : a ∈ Set.range (A.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact ha
  exact this

lemma rank_orderEmb (A : Finset ℤ) (i : Fin A.card) :
    rank A (A.orderEmbOfFin rfl i) = i := by
  unfold rank
  have h : A.filter (· < A.orderEmbOfFin rfl i) =
      (Finset.Iio i).map (A.orderEmbOfFin rfl).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨j, rfl⟩ := exists_orderEmb_eq A hx
      exact ⟨j, (A.orderEmbOfFin rfl).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem A rfl j, (A.orderEmbOfFin rfl).lt_iff_lt.mpr hj⟩
  rw [h, Finset.card_map, Fin.card_Iio]

lemma elem_eq (A : Finset ℤ) (i : Fin A.card) : elem A i = A.orderEmbOfFin rfl i := by
  unfold elem; simp [i.2]

theorem rank_lt_card (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) : rank A a < A.card := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  rw [rank_orderEmb]; exact i.2

theorem elem_rank (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) : elem A (rank A a) = a := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  rw [rank_orderEmb, elem_eq]

theorem rank_lt_rank (A : Finset ℤ) {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    rank A a < rank A b := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  obtain ⟨j, rfl⟩ := exists_orderEmb_eq A hb
  rw [rank_orderEmb, rank_orderEmb]
  exact (A.orderEmbOfFin rfl).lt_iff_lt.mp hab

theorem elem_lt_elem (A : Finset ℤ) {s t : ℕ} (hst : s < t) (ht : t < A.card) :
    elem A s < elem A t := by
  have hs : s < A.card := hst.trans ht
  rw [elem_eq A ⟨s, hs⟩, elem_eq A ⟨t, ht⟩]
  exact (A.orderEmbOfFin rfl).lt_iff_lt.mpr hst

end OMA790
end

-- DistanceLists
section
namespace OMA790

private theorem mem_Dset_of (A : Finset ℤ) (a : ℤ) {h : ℕ} (hL : h < Nat.clog 2 A.card)
    (hs : splitPt h (rank A a) < A.card) :
    |elem A (splitPt h (rank A a)) - a| ∈ Dset A a := by
  unfold Dset
  exact Finset.mem_image.2 ⟨h, Finset.mem_filter.2 ⟨Finset.mem_range.2 hL, hs⟩, rfl⟩

theorem distance_lists (A : Finset ℤ) {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    ∃ δ, (δ ∈ Dset A a ∨ δ ∈ Dset A b) ∧ b - a ≤ 2 * δ ∧ δ ≤ b - a := by
  have hik := rank_lt_rank A ha hb hab
  have hkn := rank_lt_card A hb
  have hk : rank A b < 2 ^ Nat.clog 2 A.card :=
    lt_of_lt_of_le hkn (Nat.le_pow_clog (by norm_num) _)
  obtain ⟨h, hL, heq, his, hsk⟩ := bit_split _ _ _ hik hk
  have hsn : splitPt h (rank A b) < A.card := lt_of_le_of_lt hsk hkn
  have hsn' : splitPt h (rank A a) < A.card := heq ▸ hsn
  set e := elem A (splitPt h (rank A b)) with he
  have hae : a < e := by
    have := elem_lt_elem A (heq ▸ his) hsn
    rwa [elem_rank A ha] at this
  have heb : e ≤ b := by
    rcases lt_or_eq_of_le hsk with hlt | heq2
    · have := elem_lt_elem A hlt hkn
      rw [elem_rank A hb] at this; exact this.le
    · rw [he, heq2, elem_rank A hb]
  have hDa : |e - a| ∈ Dset A a := by
    have := mem_Dset_of A a hL hsn'
    rwa [heq] at this
  have hDb : |e - b| ∈ Dset A b := mem_Dset_of A b hL hsn
  rw [abs_of_pos (by linarith)] at hDa
  rw [abs_of_nonpos (by linarith)] at hDb
  by_cases hc : b - a ≤ 2 * (e - a)
  · exact ⟨e - a, Or.inl hDa, hc, by linarith⟩
  · exact ⟨-(e - b), Or.inr hDb, by linarith, by linarith⟩

theorem card_Dset_le (A : Finset ℤ) (a : ℤ) : (Dset A a).card ≤ Nat.clog 2 A.card := by
  unfold Dset
  refine Finset.card_image_le.trans ?_
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

end OMA790
end

-- Dyadic
section
namespace OMA790

private lemma toNat_cast {z : ℤ} (hz : 0 < z) : ((z.toNat : ℕ) : ℤ) = z :=
  Int.toNat_of_nonneg hz.le

theorem two_pow_dyIdx_le {z : ℤ} (hz : 0 < z) : (2 : ℤ) ^ dyIdx z ≤ z := by
  have hn : z.toNat ≠ 0 := by omega
  have := Nat.pow_log_le_self 2 hn
  unfold dyIdx
  calc (2 : ℤ) ^ Nat.log 2 z.toNat = ((2 ^ Nat.log 2 z.toNat : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ ((z.toNat : ℕ) : ℤ) := by exact_mod_cast this
    _ = z := toNat_cast hz

theorem lt_two_pow_dyIdx_succ {z : ℤ} (hz : 0 < z) : z < (2 : ℤ) ^ (dyIdx z + 1) := by
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z.toNat
  unfold dyIdx
  calc z = ((z.toNat : ℕ) : ℤ) := (toNat_cast hz).symm
    _ < ((2 ^ (Nat.log 2 z.toNat).succ : ℕ) : ℤ) := by exact_mod_cast this
    _ = (2 : ℤ) ^ (Nat.log 2 z.toNat + 1) := by push_cast; rfl

theorem dyIdx_lt_of_two_mul_lt {z x : ℤ} (hz : 0 < z) (hzx : 2 * z < x) :
    dyIdx z < dyIdx x := by
  have h1 := two_pow_dyIdx_le hz
  have h2 : (2 : ℤ) ^ (dyIdx z + 1) ≤ x := by
    rw [pow_succ]; linarith
  have hx : 0 < x := by linarith
  have h3 : 2 ^ (dyIdx z + 1) ≤ x.toNat := by
    have : ((2 ^ (dyIdx z + 1) : ℕ) : ℤ) ≤ ((x.toNat : ℕ) : ℤ) := by
      rw [toNat_cast hx]; push_cast; exact h2
    exact_mod_cast this
  have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h3
  unfold dyIdx at *
  omega

theorem lt_two_mul_of_dyIdx_eq {z b : ℤ} (hz : 0 < z) (hb : 0 < b) (h : dyIdx b = dyIdx z) :
    b < 2 * z := by
  have h1 := lt_two_pow_dyIdx_succ hb
  have h2 := two_pow_dyIdx_le hz
  rw [h, pow_succ] at h1
  linarith

theorem dyIdx_le_topIdx {A : Finset ℤ} {z : ℤ} (hz : z ∈ A) : dyIdx z ≤ topIdx A :=
  Finset.le_sup (f := dyIdx) hz

end OMA790
end

-- Window
section
namespace OMA790

theorem mem_window_of (A : Finset ℤ) (N : ℕ) {z δ : ℤ} (hzA : z ∈ A) (hz : 0 < z)
    (h1 : δ ≤ 2 * (N : ℤ) * z) (h2 : z ≤ 2 * δ) : dyIdx z ∈ window N δ (topIdx A) := by
  unfold window
  rw [Finset.mem_filter, Finset.mem_range]
  have hle : dyIdx z ≤ topIdx A := Finset.le_sup (f := dyIdx) hzA
  have hzn : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz.le
  have hne : z.toNat ≠ 0 := by omega
  have hlo : 2 ^ dyIdx z ≤ z.toNat := Nat.pow_log_le_self 2 hne
  have hhi : z.toNat < 2 ^ (dyIdx z + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlo' : (2 : ℤ) ^ dyIdx z ≤ z := by rw [← hzn]; exact_mod_cast hlo
  have hhi' : z < (2 : ℤ) ^ (dyIdx z + 1) := by rw [← hzn]; exact_mod_cast hhi
  refine ⟨by omega, ?_, by linarith⟩
  have : 2 * (N : ℤ) * z ≤ 2 * (N : ℤ) * 2 ^ (dyIdx z + 1) :=
    mul_le_mul_of_nonneg_left hhi'.le (by positivity)
  linarith

theorem card_window_le (N : ℕ) (hN : 1 ≤ N) (δ : ℤ) (M : ℕ) :
    (window N δ M).card ≤ Nat.clog 2 N + 5 := by
  rcases (window N δ M).eq_empty_or_nonempty with h | h
  · simp [h]
  set a := (window N δ M).min' h
  have ha := Finset.min'_mem _ h
  have haw : δ ≤ 2 * (N : ℤ) * 2 ^ (a + 1) := by
    have := ha; unfold window at this; rw [Finset.mem_filter] at this; exact this.2.1
  have hNc : (N : ℤ) ≤ 2 ^ Nat.clog 2 N := by exact_mod_cast Nat.le_pow_clog (by norm_num) N
  have hsub : window N δ M ⊆ Finset.Icc a (a + Nat.clog 2 N + 3) := by
    intro j hj
    have hmin : a ≤ j := Finset.min'_le _ _ hj
    have hj' := hj
    unfold window at hj'; rw [Finset.mem_filter] at hj'
    have h2 : (2 : ℤ) ^ j ≤ 2 * δ := hj'.2.2
    have key : (2 : ℤ) ^ j ≤ 2 ^ (a + Nat.clog 2 N + 3) := by
      have e : (2 : ℤ) ^ (a + Nat.clog 2 N + 3) = 4 * 2 ^ Nat.clog 2 N * 2 ^ (a + 1) := by
        ring
      have hp : (0 : ℤ) ≤ 2 ^ (a + 1) := by positivity
      have : 2 * (2 * (N : ℤ) * 2 ^ (a + 1)) ≤ 4 * 2 ^ Nat.clog 2 N * 2 ^ (a + 1) := by
        nlinarith
      linarith
    have : j ≤ a + Nat.clog 2 N + 3 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 key
    exact Finset.mem_Icc.2 ⟨hmin, this⟩
  calc (window N δ M).card ≤ (Finset.Icc a (a + Nat.clog 2 N + 3)).card := Finset.card_le_card hsub
    _ = Nat.clog 2 N + 4 := by simp; omega
    _ ≤ _ := by omega

end OMA790
end

-- FsetCard
section
namespace OMA790

theorem fs_card_window_le (N : ℕ) (δ : ℤ) (M : ℕ) :
    (window N δ M).card ≤ Nat.clog 2 N + 5 := by
  rcases (window N δ M).eq_empty_or_nonempty with h | hne
  · simp [h]
  set j0 := (window N δ M).min' hne with hj0def
  have hj0 : j0 ∈ window N δ M := Finset.min'_mem _ _
  have hsub : window N δ M ⊆ Finset.Ico j0 (j0 + (Nat.clog 2 N + 4)) := by
    intro j hj
    have hle : j0 ≤ j := Finset.min'_le _ _ hj
    simp only [window, Finset.mem_filter] at hj hj0
    rw [Finset.mem_Ico]
    refine ⟨hle, ?_⟩
    have hN : (N : ℤ) ≤ 2 ^ Nat.clog 2 N := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) N
    have h1 : (2:ℤ) ^ j ≤ 2 ^ (j0 + Nat.clog 2 N + 3) := by
      calc (2:ℤ) ^ j ≤ 2 * δ := hj.2.2
        _ ≤ 2 * (2 * N * 2 ^ (j0 + 1)) := by linarith [hj0.2.1]
        _ = 8 * N * 2 ^ j0 := by ring
        _ ≤ 8 * 2 ^ Nat.clog 2 N * 2 ^ j0 := by gcongr
        _ = 2 ^ (j0 + Nat.clog 2 N + 3) := by ring
    have := (pow_le_pow_iff_right₀ (by norm_num : (1:ℤ) < 2)).1 h1
    omega
  calc _ ≤ (Finset.Ico j0 (j0 + (Nat.clog 2 N + 4))).card := Finset.card_le_card hsub
    _ = Nat.clog 2 N + 4 := by simp
    _ ≤ _ := by omega

theorem card_Dplus_le (A : Finset ℤ) (a : ℤ) :
    (Dplus A a).card ≤ Nat.clog 2 A.card + 1 := by
  unfold Dplus
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  unfold Dset
  refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
  simp

theorem card_Fset_le (A : Finset ℤ) (hA : 1 ≤ A.card) (a : ℤ) :
    (Fset A a).card ≤ K A.card := by
  unfold Fset K
  calc _ ≤ ((Dplus A a).biUnion (fun δ => window A.card δ (topIdx A))).card :=
        Finset.card_erase_le
    _ ≤ ∑ δ ∈ Dplus A a, (window A.card δ (topIdx A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _δ ∈ Dplus A a, (Nat.clog 2 A.card + 5) :=
        Finset.sum_le_sum fun δ _ => fs_card_window_le _ _ _
    _ = (Dplus A a).card * (Nat.clog 2 A.card + 5) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_Dplus_le A a)

theorem lt_of_mem_Fset {A : Finset ℤ} {a : ℤ} {j : ℕ} (hj : j ∈ Fset A a) :
    j < topIdx A + 1 := by
  unfold Fset at hj
  obtain ⟨_, hj⟩ := Finset.mem_erase.1 hj
  obtain ⟨δ, _, hj⟩ := Finset.mem_biUnion.1 hj
  unfold window at hj
  exact Finset.mem_range.1 (Finset.mem_filter.1 hj).1

theorem dyIdx_not_mem_Fset (A : Finset ℤ) (a : ℤ) : dyIdx a ∉ Fset A a := by
  unfold Fset
  exact Finset.notMem_erase _ _

theorem fs_mem_Fset_of {A : Finset ℤ} {a δ : ℤ} {j : ℕ} (hδ : δ ∈ Dplus A a)
    (hj : j ∈ window A.card δ (topIdx A)) (hne : j ≠ dyIdx a) : j ∈ Fset A a := by
  unfold Fset
  exact Finset.mem_erase.2 ⟨hne, Finset.mem_biUnion.2 ⟨δ, hδ, hj⟩⟩

end OMA790
end

-- RelationShape
section
namespace OMA790

theorem relation_shape (S : Finset ℤ) (hpos : ∀ s ∈ S, 0 < s) (h2 : 2 ≤ S.card) (x : ℤ)
    (hsum : ∑ s ∈ S, s = x) :
    ∃ b₁ ∈ S, ∃ z ∈ S, 0 < z ∧ z < b₁ ∧ b₁ + z ≤ x ∧ z ≤ x - b₁ ∧
      x - b₁ ≤ (S.card : ℤ) * z ∧ x ≤ (S.card : ℤ) * b₁ := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  set b₁ := S.max' hS with hb₁def
  have hb₁ : b₁ ∈ S := S.max'_mem hS
  set T := S.erase b₁ with hTdef
  have hTcard : T.card = S.card - 1 := Finset.card_erase_of_mem hb₁
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  set z := T.max' hT with hzdef
  have hzT : z ∈ T := T.max'_mem hT
  have hzS : z ∈ S := Finset.mem_of_mem_erase hzT
  have hzne : z ≠ b₁ := Finset.ne_of_mem_erase hzT
  have hzle : z ≤ b₁ := S.le_max' z hzS
  have hzlt : z < b₁ := lt_of_le_of_ne hzle hzne
  have hzpos : 0 < z := hpos z hzS
  have hsplit : b₁ + ∑ s ∈ T, s = x := by
    rw [hTdef, Finset.add_sum_erase S (fun s => s) hb₁]; exact hsum
  have hTle : ∑ s ∈ T, s ≤ (T.card : ℤ) * z := by
    have := Finset.sum_le_card_nsmul T (fun s => s) z (fun s hs => T.le_max' s hs)
    simpa [nsmul_eq_mul] using this
  have hTge : z ≤ ∑ s ∈ T, s := by
    have := Finset.single_le_sum (f := fun s => s)
      (fun s hs => le_of_lt (hpos s (Finset.mem_of_mem_erase hs))) hzT
    simpa using this
  have hSle : ∑ s ∈ S, s ≤ (S.card : ℤ) * b₁ := by
    have := Finset.sum_le_card_nsmul S (fun s => s) b₁ (fun s hs => S.le_max' s hs)
    simpa [nsmul_eq_mul] using this
  have hcardT : (T.card : ℤ) ≤ S.card := by exact_mod_cast (by omega : T.card ≤ S.card)
  refine ⟨b₁, hb₁, z, hzS, hzpos, hzlt, by linarith, by linarith, ?_, by linarith⟩
  have : (T.card : ℤ) * z ≤ (S.card : ℤ) * z :=
    mul_le_mul_of_nonneg_right hcardT hzpos.le
  linarith

end OMA790
end

-- Obstruction
section
namespace OMA790

private theorem mem_Fset_of (A : Finset ℤ) {a z δ : ℤ} (hzA : z ∈ A) (hz : 0 < z)
    (hδ : δ ∈ Dplus A a) (h1 : δ ≤ 2 * (A.card : ℤ) * z) (h2 : z ≤ 2 * δ)
    (hne : dyIdx z ≠ dyIdx a) : dyIdx z ∈ Fset A a := by
  unfold Fset
  rw [Finset.mem_erase]
  exact ⟨hne, Finset.mem_biUnion.2 ⟨δ, hδ, mem_window_of A A.card hzA hz h1 h2⟩⟩

theorem obstruction (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) {x : ℤ} (hx : x ∈ A)
    {S : Finset ℤ} (hS : S ⊆ A) (hxS : x ∉ S) (h2 : 2 ≤ S.card) (hsum : ∑ s ∈ S, s = x) :
    ∃ z ∈ S, ∃ a, (a = x ∨ a ∈ S) ∧ dyIdx z ∈ Fset A a := by
  obtain ⟨b₁, hb₁, z, hzS, hz, hzb, hbz, hzd, hdz, hxb⟩ :=
    relation_shape S (fun s hs => hpos s (hS hs)) h2 x hsum
  have hcard : (S.card : ℤ) ≤ A.card := by exact_mod_cast Finset.card_le_card hS
  have hzA := hS hzS
  have hbA := hS hb₁
  have hb0 : 0 < b₁ := lt_trans hz hzb
  have hzx : 2 * z < x := by linarith
  have hdx : dyIdx z ≠ dyIdx x := (dyIdx_lt_of_two_mul_lt hz hzx).ne
  refine ⟨z, hzS, ?_⟩
  by_cases hcase : dyIdx b₁ = dyIdx z
  · have hb2 := lt_two_mul_of_dyIdx_eq hz hb0 hcase
    refine ⟨x, Or.inl rfl, mem_Fset_of A hzA hz (Finset.mem_insert_self _ _) ?_ (by linarith) hdx⟩
    have : (S.card : ℤ) * b₁ ≤ (A.card : ℤ) * (2 * z) :=
      mul_le_mul hcard hb2.le hb0.le (by positivity)
    linarith
  · have hbx : b₁ < x := by linarith
    obtain ⟨δ, hδ, hd1, hd2⟩ := distance_lists A hbA hx hbx
    have hNz : (S.card : ℤ) * z ≤ (A.card : ℤ) * z := mul_le_mul_of_nonneg_right hcard hz.le
    have hw1 : δ ≤ 2 * (A.card : ℤ) * z := by nlinarith
    have hw2 : z ≤ 2 * δ := by linarith
    rcases hδ with hδ | hδ
    · exact ⟨b₁, Or.inr hb₁, mem_Fset_of A hzA hz (Finset.mem_insert_of_mem hδ) hw1 hw2
        (Ne.symm hcase)⟩
    · exact ⟨x, Or.inl rfl, mem_Fset_of A hzA hz (Finset.mem_insert_of_mem hδ) hw1 hw2 hdx⟩

end OMA790
end

-- Averaging
section
namespace OMA790

open Classical in

theorem card_coloring_eq_mul {ι : Type*} [Fintype ι] (m : ℕ) {j k : ι} (hjk : j ≠ k) :
    m * (Finset.univ.filter (fun χ : ι → Fin m => χ j = χ k)).card =
      Fintype.card (ι → Fin m) := by
  set e := Equiv.funSplitAt j (Fin m)
  have hk : k ≠ j := fun h => hjk h.symm
  have h1 : (Finset.univ.filter (fun χ : ι → Fin m => χ j = χ k)).card =
      Fintype.card ({ i // i ≠ j } → Fin m) := by
    rw [Finset.card_filter, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
    have : ∀ (b : Fin m) (f : { i // i ≠ j } → Fin m),
        (if (e.symm (b, f)) j = (e.symm (b, f)) k then 1 else 0 : ℕ) =
          if f ⟨k, hk⟩ = b then 1 else 0 := by
      intro b f
      simp only [e, Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, hk, dite_false,
        dite_true]
      by_cases h : b = f ⟨k, hk⟩
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one]
  rw [h1, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]

open Classical in
theorem exists_coloring_many_good {α ι : Type*} [Fintype ι] (S : Finset α) (g : α → ι)
    (G : α → Finset ι) (m : ℕ) (hm : 0 < m) (hg : ∀ a ∈ S, g a ∉ G a)
    (hG : ∀ a ∈ S, 2 * (G a).card ≤ m) :
    ∃ χ : ι → Fin m, S.card ≤ 2 * (S.filter (fun a => ∀ j ∈ G a, χ j ≠ χ (g a))).card := by
  set N := Fintype.card (ι → Fin m) with hN
  have hNpos : 0 < N := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact Fintype.card_pos
  let good : (ι → Fin m) → ℕ := fun χ => (S.filter (fun a => ∀ j ∈ G a, χ j ≠ χ (g a))).card
  let bad : (ι → Fin m) → ℕ := fun χ => (S.filter (fun a => ¬ ∀ j ∈ G a, χ j ≠ χ (g a))).card
  have hgb : ∀ χ, good χ + bad χ = S.card := fun χ => Finset.card_filter_add_card_filter_not _

  have hbad : ∀ χ : ι → Fin m, bad χ ≤
      ∑ a ∈ S, ∑ j ∈ G a, (if χ j = χ (g a) then 1 else 0 : ℕ) := by
    intro χ
    show (S.filter _).card ≤ _
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro a _
    by_cases h : ∀ j ∈ G a, χ j ≠ χ (g a)
    · rw [if_neg (not_not_intro h)]; exact Nat.zero_le _
    · rw [if_pos h]
      push Not at h
      obtain ⟨j, hj, hjeq⟩ := h
      have := Finset.single_le_sum (f := fun j => (if χ j = χ (g a) then 1 else 0 : ℕ))
        (fun _ _ => Nat.zero_le _) hj
      simp only [hjeq, ite_true] at this
      exact this
  have hsum : m * ∑ χ, bad χ ≤ ∑ a ∈ S, (G a).card * N := by
    calc m * ∑ χ, bad χ ≤ m * ∑ χ : ι → Fin m,
          ∑ a ∈ S, ∑ j ∈ G a, (if χ j = χ (g a) then 1 else 0 : ℕ) :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum fun χ _ => hbad χ)
      _ = ∑ a ∈ S, ∑ j ∈ G a,
          m * (Finset.univ.filter (fun χ : ι → Fin m => χ j = χ (g a))).card := by
          simp_rw [Finset.mul_sum, Finset.card_filter, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_comm
      _ = ∑ a ∈ S, (G a).card * N := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [Finset.sum_congr rfl fun j hj =>
            card_coloring_eq_mul m (j := j) (k := g a)
              (fun h => hg a ha (by rw [← h]; exact hj))]
          simp [hN]
  have hsum2 : 2 * ∑ χ, bad χ ≤ S.card * N := by
    have : m * (2 * ∑ χ, bad χ) ≤ m * (S.card * N) := by
      calc m * (2 * ∑ χ, bad χ) = 2 * (m * ∑ χ, bad χ) := by ring
        _ ≤ 2 * ∑ a ∈ S, (G a).card * N := Nat.mul_le_mul_left _ hsum
        _ = ∑ a ∈ S, (2 * (G a).card) * N := by rw [Finset.mul_sum]; simp [mul_assoc]
        _ ≤ ∑ a ∈ S, m * N := Finset.sum_le_sum fun a ha => Nat.mul_le_mul_right _ (hG a ha)
        _ = m * (S.card * N) := by rw [Finset.sum_const, smul_eq_mul]; ring
    exact Nat.le_of_mul_le_mul_left this hm
  have htot : ∑ χ, good χ + ∑ χ, bad χ = S.card * N := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun χ _ => hgb χ, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, hN, mul_comm]
  by_contra hcon
  push Not at hcon
  have hlt : ∑ χ : ι → Fin m, 2 * good χ < ∑ χ : ι → Fin m, S.card := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩
    · intro χ _; exact hcon χ
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hN] at hlt
  nlinarith [hsum2, htot, hlt]

end OMA790
end

-- Pigeon
section
namespace OMA790

open Classical in
theorem exists_color_fiber {α : Type*} (T : Finset α) {m : ℕ} (hm : 0 < m) (f : α → Fin m) :
    ∃ c : Fin m, T.card ≤ m * (T.filter (fun a => f a = c)).card := by
  by_contra h
  push Not at h
  have hsum : T.card = ∑ c : Fin m, (T.filter (fun a => f a = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hlt : ∑ c : Fin m, m * (T.filter (fun a => f a = c)).card
      < ∑ _c : Fin m, T.card := Finset.sum_lt_sum_of_nonempty hne (fun c _ => h c)
  rw [← Finset.mul_sum, ← hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hlt
  exact lt_irrefl _ hlt

end OMA790
end

-- CastIdx
section
namespace OMA790

theorem idx_not_mem_image_Fset {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    idx A (dyIdx a) ∉ (Fset A a).image (idx A) := by
  intro h
  rw [Finset.mem_image] at h
  obtain ⟨j, hj, heq⟩ := h
  unfold Fset at hj
  rw [Finset.mem_erase, Finset.mem_biUnion] at hj
  obtain ⟨hne, δ, _, hw⟩ := hj
  unfold window at hw
  rw [Finset.mem_filter, Finset.mem_range] at hw
  have hda : dyIdx a < topIdx A + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := dyIdx) ha)
  have hv := congrArg Fin.val heq
  simp only [idx, Fin.val_ofNat] at hv
  rw [Nat.mod_eq_of_lt hw.1, Nat.mod_eq_of_lt hda] at hv
  exact hne hv

end OMA790
end

-- SignSplit
section
namespace OMA790

theorem sign_split (A : Finset ℤ) (hA : 2 ≤ A.card) :
    A.card ≤ 4 * (A.filter (fun x => 0 < x)).card ∨
      A.card ≤ 4 * (A.filter (fun x => x < 0)).card := by
  have hsub : A ⊆ insert 0 (A.filter (fun x => 0 < x) ∪ A.filter (fun x => x < 0)) := by
    intro x hx
    rcases lt_trichotomy x 0 with h | h | h
    · simp [hx, h]
    · simp [h]
    · simp [hx, h]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le (0 : ℤ)
    (A.filter (fun x => 0 < x) ∪ A.filter (fun x => x < 0))
  have h3 := Finset.card_union_le (A.filter (fun x => 0 < x)) (A.filter (fun x => x < 0))
  omega

theorem isSumFree_image_neg {B : Finset ℤ} (hB : IsSumFree B) :
    IsSumFree (B.image (fun x => -x)) := by
  intro x hx S hS hxS hcard hsum
  have hinj : Function.Injective (fun x : ℤ => -x) := neg_injective
  refine hB (-x) ?_ (S.image (fun x => -x)) ?_ ?_ ?_ ?_
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hS hz)
    simpa using hw
  · intro h
    obtain ⟨z, hz, hz'⟩ := Finset.mem_image.mp h
    have : z = x := by simpa using hz'
    exact hxS (this ▸ hz)
  · rwa [Finset.card_image_of_injective _ hinj]
  · rw [Finset.sum_image (fun a _ b _ h => hinj h), Finset.sum_neg_distrib, hsum]

end OMA790
end

-- LBridge
section
namespace OMA790

theorem l_set_upper (n : ℕ) :
    n ∈ upperBounds {k : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ k ≤ B.card} := by
  intro k hk
  have hA : ((Finset.range n).image (fun i : ℕ => (i : ℤ))).card = n := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  obtain ⟨B, hBA, -, hkB⟩ := hk _ hA
  exact hkB.trans ((Finset.card_le_card hBA).trans hA.le)

theorem l_lower_of (n M : ℕ) (hM : 0 < M)
    (h : ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ n ≤ M * B.card) :
    n ≤ M * l n := by
  set k0 := (n + M - 1) / M with hk0
  have hmem : k0 ∈ {k : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ k ≤ B.card} := by
    intro A hA
    obtain ⟨B, hBA, hB, hnB⟩ := h A hA
    refine ⟨B, hBA, hB, ?_⟩
    rw [hk0, Nat.div_le_iff_le_mul_add_pred hM]
    omega
  have hle : k0 ≤ l n := le_csSup ⟨n, l_set_upper n⟩ hmem
  have h1 := Nat.div_add_mod (n + M - 1) M
  have h2 := Nat.mod_lt (n + M - 1) hM
  rw [← hk0] at h1
  have h3 : M * k0 ≤ M * l n := Nat.mul_le_mul_left M hle
  generalize M * k0 = x at h1 h3
  omega

theorem l_le_self (n : ℕ) : l n ≤ n :=
  csSup_le' (l_set_upper n)

end OMA790
end

-- LogBound
section
namespace OMA790

theorem K_mono {M N : ℕ} (h : M ≤ N) : K M ≤ K N := by
  unfold K
  have := Nat.clog_mono_right 2 h
  exact Nat.mul_le_mul (by omega) (by omega)

theorem K_le_log_sq (n : ℕ) (hn : 2 ≤ n) : (K n : ℝ) ≤ 64 * Real.log n ^ 2 := by
  unfold K
  have hpow' : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  rw [Nat.pred_eq_sub_one] at hpow'
  set c := Nat.clog 2 n with hc
  set p := c - 1 with hp
  have hpow : 2 ^ p < n := hpow'
  have hcp : c ≤ p + 1 := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hpl : (p : ℝ) * Real.log 2 < Real.log n := by
    have h1 : ((2 : ℝ) ^ p) < n := by exact_mod_cast hpow
    have h2 := Real.log_lt_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hcR : (c : ℝ) ≤ p + 1 := by exact_mod_cast hcp
  have hp0 : (0 : ℝ) ≤ p := by positivity
  push_cast
  set L := Real.log n
  have hpL : (p : ℝ) * 0.69 ≤ L := by nlinarith
  nlinarith [mul_le_mul hcR hcR (by positivity) (by positivity)]

theorem K_pos (n : ℕ) : 0 < K n := by
  unfold K; positivity

end OMA790
end

-- Asymptotics
section
namespace OMA790

open Filter

lemma asymptotics_key (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ c * x / Real.log x ^ 2 := by
  have h := (isLittleO_log_rpow_atTop (half_pos hε)).bound (Real.sqrt_pos.2 hc)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hxpos : 0 < x := by linarith
  rw [Real.norm_of_nonneg hl.le, Real.norm_of_nonneg (by positivity)] at hx
  have hsq : Real.log x ^ 2 ≤ c * x ^ ε := by
    calc Real.log x ^ 2 ≤ (Real.sqrt c * x ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ hl.le hx 2
      _ = c * x ^ ε := by
        rw [mul_pow, Real.sq_sqrt hc.le, ← Real.rpow_natCast (x ^ (ε / 2)),
          ← Real.rpow_mul hxpos.le]
        norm_num
  rw [le_div_iff₀ (by positivity)]
  calc x ^ (1 - ε) * Real.log x ^ 2 ≤ x ^ (1 - ε) * (c * x ^ ε) := by gcongr
    _ = c * x := by rw [mul_left_comm, ← Real.rpow_add hxpos]; simp

theorem asymptotics (f : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ n : ℕ, 2 ≤ n → c * n / Real.log n ^ 2 ≤ f n) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.sqrt n) atTop atTop ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ f n := by
  have h2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ f n := by
    intro ε hε
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (asymptotics_key c hc ε hε),
      eventually_ge_atTop 2] with n hn h2n
    exact hn.trans (hf n h2n)
  refine ⟨?_, h2⟩
  refine tendsto_atTop_mono' atTop ?_
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop)
  filter_upwards [h2 (1 / 4) (by norm_num), eventually_ge_atTop 1] with n hn h1n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1n
  simp only [Function.comp]
  rw [le_div_iff₀ (Real.sqrt_pos.2 hnpos), Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
  norm_num at hn ⊢
  exact hn

end OMA790
end

-- Main
section
namespace OMA790

open Filter

theorem selected_sumFree (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) {m : ℕ}
    (χ : Fin (topIdx A + 1) → Fin m) (c : Fin m) :
    IsSumFree (A.filter (fun a => χ (idx A (dyIdx a)) = c ∧
      ∀ j ∈ (Fset A a).image (idx A), χ j ≠ c)) := by
  set B := A.filter (fun a => χ (idx A (dyIdx a)) = c ∧
      ∀ j ∈ (Fset A a).image (idx A), χ j ≠ c) with hBdef
  intro x hx S hS hxS h2 hsum
  have hSA : S ⊆ A := hS.trans (Finset.filter_subset _ _)
  obtain ⟨z, hzS, a, ha, hmem⟩ :=
    obstruction A hpos (Finset.mem_filter.1 hx).1 hSA hxS h2 hsum
  have hz := (Finset.mem_filter.1 (hS hzS)).2.1
  have haB : a ∈ B := by
    rcases ha with rfl | ha
    · exact hx
    · exact hS ha
  exact (Finset.mem_filter.1 haB).2.2 _ (Finset.mem_image_of_mem _ hmem) hz

theorem positive_case (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) (hA : 1 ≤ A.card) :
    ∃ B ⊆ A, IsSumFree B ∧ A.card ≤ 4 * K A.card * B.card := by
  have hm : 0 < 2 * K A.card := by have := K_pos A.card; omega
  obtain ⟨χ, hχ⟩ := exists_coloring_many_good A (fun a => idx A (dyIdx a))
    (fun a => (Fset A a).image (idx A)) (2 * K A.card) hm
    (fun a ha => idx_not_mem_image_Fset ha)
    (fun a _ => by
      have h1 := Finset.card_image_le (s := Fset A a) (f := idx A)
      have h2 := card_Fset_le A hA a
      omega)
  set T := A.filter (fun a => ∀ j ∈ (Fset A a).image (idx A),
    χ j ≠ χ (idx A (dyIdx a))) with hT
  obtain ⟨c, hc⟩ := exists_color_fiber T hm (fun a => χ (idx A (dyIdx a)))
  set B := A.filter (fun a => χ (idx A (dyIdx a)) = c ∧
      ∀ j ∈ (Fset A a).image (idx A), χ j ≠ c) with hB
  refine ⟨B, Finset.filter_subset _ _, selected_sumFree A hpos χ c, ?_⟩
  have hsub : T.filter (fun a => χ (idx A (dyIdx a)) = c) ⊆ B := by
    intro a ha
    rw [Finset.mem_filter, hT, Finset.mem_filter] at ha
    obtain ⟨⟨haA, hgood⟩, hca⟩ := ha
    rw [hB, Finset.mem_filter]
    refine ⟨haA, hca, fun j hj => ?_⟩
    rw [← hca]
    exact hgood j hj
  have h1 := Finset.card_le_card hsub
  have h2 : 2 * K A.card * (T.filter (fun a => χ (idx A (dyIdx a)) = c)).card ≤
      2 * K A.card * B.card := Nat.mul_le_mul_left _ h1
  have h0 : A.card ≤ 2 * T.card := by rw [hT]; convert hχ
  linarith

theorem general_case (A : Finset ℤ) (hA : 2 ≤ A.card) :
    ∃ B ⊆ A, IsSumFree B ∧ A.card ≤ 16 * K A.card * B.card := by
  rcases sign_split A hA with h | h
  · set P := A.filter (fun x => 0 < x) with hP
    have hP1 : 1 ≤ P.card := by omega
    obtain ⟨B, hBP, hB, hcard⟩ :=
      positive_case P (fun a ha => (Finset.mem_filter.1 ha).2) hP1
    have hK : K P.card ≤ K A.card := K_mono (Finset.card_le_card (Finset.filter_subset _ _))
    refine ⟨B, hBP.trans (Finset.filter_subset _ _), hB, ?_⟩
    have : K P.card * B.card ≤ K A.card * B.card := Nat.mul_le_mul_right _ hK
    nlinarith
  · set N := A.filter (fun x => x < 0) with hN
    set P := N.image (fun x => -x) with hP
    have hPc : P.card = N.card := Finset.card_image_of_injective _ neg_injective
    have hP1 : 1 ≤ P.card := by omega
    have hpos : ∀ a ∈ P, 0 < a := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
      have := (Finset.mem_filter.1 hy).2
      omega
    obtain ⟨B, hBP, hB, hcard⟩ := positive_case P hpos hP1
    refine ⟨B.image (fun x => -x), ?_, isSumFree_image_neg hB, ?_⟩
    · intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hBP hw)
      simpa using (Finset.mem_filter.1 hv).1
    · rw [Finset.card_image_of_injective _ neg_injective]
      have hK : K P.card ≤ K A.card :=
        K_mono (by rw [hPc]; exact Finset.card_le_card (Finset.filter_subset _ _))
      have : K P.card * B.card ≤ K A.card * B.card := Nat.mul_le_mul_right _ hK
      nlinarith

theorem erdos_790 : Erdos790Answer := by
  have hlow : ∀ n : ℕ, 2 ≤ n → n ≤ 16 * K n * l n := by
    intro n hn
    apply l_lower_of n (16 * K n) (by have := K_pos n; omega)
    intro A hA
    obtain ⟨B, hBA, hB, h⟩ := general_case A (by omega)
    exact ⟨B, hBA, hB, by rw [hA] at h; exact h⟩
  have hc : ∀ n : ℕ, 2 ≤ n → (1 / 1024 : ℝ) * n / Real.log n ^ 2 ≤ l n := by
    intro n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h1 : (n : ℝ) ≤ 16 * K n * l n := by exact_mod_cast hlow n hn
    have h2 := K_le_log_sq n hn
    have hl : (0 : ℝ) ≤ l n := Nat.cast_nonneg _
    have h3 : (K n : ℝ) * l n ≤ 64 * Real.log n ^ 2 * l n := mul_le_mul_of_nonneg_right h2 hl
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨h3, h4⟩ := asymptotics l (1 / 1024) (by norm_num) hc
  refine ⟨⟨1 / 1024, by norm_num, hc⟩, l_le_self, h3, h4, ?_⟩
  rintro ⟨c, hc0, hfreq⟩
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually (h4 c hc0)).exists
  linarith

end OMA790
end

/-! ### Bridge to the statement in FormalConjectures.ErdosProblems.790 -/

namespace OMA790Bridge

open Filter

theorem sumFree_iff (B : Finset ℤ) : OMA790.IsSumFree B ↔ Erdos790.DistinctSubsetSumFree B := by
  constructor
  · intro h a ha S hS h2
    exact h a ha S (hS.trans (Finset.erase_subset _ _))
      (fun haS => (Finset.mem_erase.1 (hS haS)).1 rfl) h2
  · intro h x hx S hS hxS h2
    exact h x hx S (fun y hy => Finset.mem_erase.2 ⟨fun hyx => hxS (hyx ▸ hy), hS hy⟩) h2

theorem guarantees_le {n k : ℕ} (hk : Erdos790.Guarantees n k) : k ≤ n := by
  have hcard : ((Finset.range n).image (fun i : ℕ => (i : ℤ))).card = n := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  obtain ⟨B, hBA, -, hkB⟩ := hk _ hcard
  exact hkB.trans ((Finset.card_le_card hBA).trans hcard.le)

theorem guarantees_zero (n : ℕ) : Erdos790.Guarantees n 0 := by
  intro A _
  refine ⟨∅, Finset.empty_subset _, ?_, le_refl _⟩
  intro a ha
  exact absurd ha (Finset.notMem_empty a)

theorem mem_iff (n k : ℕ) :
    k ∈ {k : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, OMA790.IsSumFree B ∧ k ≤ B.card} ↔
      Erdos790.Guarantees n k := by
  simp only [Set.mem_setOf_eq, Erdos790.Guarantees, sumFree_iff]

theorem l_eq (n : ℕ) : OMA790.l n = Erdos790.l n := by
  classical
  unfold OMA790.l Erdos790.l
  apply le_antisymm
  · apply csSup_le ⟨0, (mem_iff n 0).2 (guarantees_zero n)⟩
    intro k hk
    have hk' := (mem_iff n k).1 hk
    exact Nat.le_findGreatest (guarantees_le hk') hk'
  · apply le_csSup ⟨n, fun k hk => guarantees_le ((mem_iff n k).1 hk)⟩
    exact (mem_iff n _).2 (Nat.findGreatest_spec (Nat.zero_le n) (guarantees_zero n))

theorem answer : OMA790.Erdos790Answer := OMA790.erdos_790

end OMA790Bridge

open OMA790Bridge in
theorem OMA.disproof : ¬ (type_of% @Erdos790.erdos_790.parts.iii) := by
  rintro ⟨c, hc, hev⟩
  apply answer.2.2.2.2
  refine ⟨c, hc, ?_⟩
  refine (hev.mono fun n hn => ?_).frequently
  rw [l_eq]
  exact hn
