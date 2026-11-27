import FormalConjectures.ErdosProblems.«357»
import Mathlib

/-!
# Explicit upper bound for Erdős 357

Copyright 2026 Chandler Snively. Licensed under the Apache License, Version 2.0.
Original formalization: https://github.com/dreadpiratechan/erdos-357
Revision 58025bf3b27889103eb32ce4f39c8bf6610a5c76.
This file has been modified for the pinned upstream definitions and toolchain. Selected upper-bound
lemmas from P0357, P0357Upper, P0357Upper2, P0357Upper4Gen and P0357Upper4
are combined here, followed by a new proof of the indexed asymptotic statement.
The imported extremal function and distinct-sums predicate are from the Formal
Conjectures authors and Google DeepMind, also licensed under Apache 2.0.
https://www.apache.org/licenses/LICENSE-2.0
-/

namespace Snively357
open Finset

/-- A positive-length interval determines its start and length. -/
theorem block_injective : Set.InjOn
    (fun p : ℕ × ℕ ↦ Ico p.1 (p.1 + p.2)) {p | 0 < p.2} := by
  intro p hp q hq he
  change 0 < p.2 at hp
  change 0 < q.2 at hq
  change Ico p.1 (p.1 + p.2) = Ico q.1 (q.1 + q.2) at he
  have hp0 : p.1 ∈ Ico p.1 (p.1 + p.2) := mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hq0 : q.1 ∈ Ico q.1 (q.1 + q.2) := mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hpq := (mem_Ico.mp (he ▸ hp0)).1
  have hqp := (mem_Ico.mp (he.symm ▸ hq0)).1
  have hstart : p.1 = q.1 := by omega
  have hlen : p.2 = q.2 := by
    have hh := congrArg Finset.card he
    simpa using hh
  exact Prod.ext hstart hlen

/-- A suffix crossing t has sum at most max(a_i,2t). -/
theorem crossing_interval {k : ℕ} (a : Fin k → ℕ) (hm : Monotone a)
    (i : Fin k) (t : ℕ) (hi : t < ∑ j ∈ Iic i, a j) :
    ∃ j ≤ i, t < ∑ x ∈ Icc j i, a x ∧
      ∑ x ∈ Icc j i, a x ≤ max (a i) (2 * t) := by
  classical
  let S := (Iic i).filter (fun j ↦ t < ∑ x ∈ Icc j i, a x)
  have hS : S.Nonempty := by
    let z : Fin k := ⟨0, by have := i.isLt; omega⟩
    refine ⟨z, mem_filter.mpr ⟨mem_Iic.mpr (by exact Nat.zero_le _), ?_⟩⟩
    have he : Icc z i = Iic i := by
      ext x
      simp only [mem_Icc, mem_Iic]
      exact and_iff_right (show z ≤ x from Nat.zero_le _)
    simpa [he] using hi
  let j := S.max' hS
  have hj := mem_filter.mp (S.max'_mem hS)
  have hji : j ≤ i := mem_Iic.mp hj.1
  refine ⟨j, hji, hj.2, ?_⟩
  by_cases heq : j = i
  · simp [heq]
  · have hjlt : j < i := lt_of_le_of_ne hji heq
    let u : Fin k := ⟨j.val + 1, by have := i.isLt; exact lt_of_le_of_lt hjlt i.isLt⟩
    have hu : u ≤ i := hjlt
    have htail : ∑ x ∈ Icc u i, a x ≤ t := by
      by_contra hn
      have huS : u ∈ S := mem_filter.mpr ⟨mem_Iic.mpr hu, by omega⟩
      have hle := S.le_max' u huS
      change u ≤ j at hle
      have : u.val ≤ j.val := hle
      dsimp [u] at this
      omega
    have hai : a i ≤ t := by
      have hmem : i ∈ Icc u i := mem_Icc.mpr ⟨hu, le_rfl⟩
      exact (single_le_sum (fun x _ ↦ Nat.zero_le (a x)) hmem).trans htail
    have haj : a j ≤ t := (hm hji).trans hai
    have he : Icc j i = insert j (Icc u i) := by
      ext x
      simp only [mem_Icc, mem_insert]
      change (j.val ≤ x.val ∧ x.val ≤ i.val) ↔
        x = j ∨ (j.val + 1 ≤ x.val ∧ x.val ≤ i.val)
      constructor
      · rintro ⟨hx, hxi⟩
        by_cases h : x.val = j.val
        · exact Or.inl (Fin.ext h)
        · exact Or.inr ⟨by omega, hxi⟩
      · rintro (rfl | ⟨hx, hxi⟩)
        · exact ⟨le_rfl, hji⟩
        · exact ⟨by omega, hxi⟩
    have hnot : j ∉ Icc u i := by
      simp only [mem_Icc, not_and]
      intro h
      have : j.val + 1 ≤ j.val := h
      omega
    rw [he, sum_insert hnot]
    exact (Nat.add_le_add haj htail).trans (by omega)

/-- Positive strict increase supplies the triangular prefix lower bound. -/
theorem prefix_twice_lower {k : ℕ} (a : Fin k → ℕ) (hm : StrictMono a)
    (hp : ∀ i, 0 < a i) (i : Fin k) :
    (i.val + 1) * (i.val + 2) ≤ 2 * ∑ j ∈ Iic i, a j := by
  have hlower : ∀ v (hv : v < k), v + 1 ≤ a ⟨v, hv⟩ := by
    intro v
    induction v with
    | zero => intro hv; exact hp _
    | succ v ih =>
      intro hv
      have hv' : v < k := by omega
      have h := ih hv'
      have h' := hm (show (⟨v, hv'⟩ : Fin k) < ⟨v + 1, hv⟩ from Nat.lt_succ_self v)
      omega
  have hsum : ∑ j ∈ Iic i, (j.val + 1) ≤ ∑ j ∈ Iic i, a j :=
    sum_le_sum (fun j _ ↦ hlower j.val j.isLt)
  have he : (Iic i).map Fin.valEmbedding = range (i.val + 1) := by
    rw [Fin.map_valEmbedding_Iic]
    ext x
    simp only [mem_Iic, mem_range]
    omega
  have hs : ∑ j ∈ Iic i, (j.val + 1) = ∑ j ∈ range (i.val + 1), (j + 1) := by
    rw [← he, sum_map]
    rfl
  rw [hs, sum_add_distrib] at hsum
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at hsum
  have hgauss := sum_range_id_mul_two (i.val + 1)
  simp only [Nat.add_sub_cancel] at hgauss
  nlinarith

/-- Every sufficiently long prefix crosses floor(n/2). -/
theorem prefix_crosses_half {k : ℕ} (a : Fin k → ℕ) (hm : StrictMono a)
    (hp : ∀ i, 0 < a i) (n : ℕ) (i : Fin k) (hi : Nat.sqrt n ≤ i.val) :
    n / 2 < ∑ j ∈ Iic i, a j := by
  have hprefix := prefix_twice_lower a hm hp i
  have hsqrt := Nat.lt_succ_sqrt n
  have hsq : (Nat.sqrt n + 1)^2 ≤ (i.val + 1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hdiv := Nat.div_mul_le_self n 2
  nlinarith
/-- The audited finite crossing bound; it applies to finite sequences directly. -/
theorem finite_length_le_half_add_sqrt {k n : ℕ} (a : Fin k → ℕ)
    (hm : StrictMono a) (hp : ∀ i, 0 < a i) (hb : ∀ i, a i ≤ n)
    (ha : Erdos357.HasDistinctSums a) : k ≤ n - n / 2 + Nat.sqrt n := by
  classical
  by_cases hk : k ≤ Nat.sqrt n
  · omega
  let m : Fin k := ⟨Nat.sqrt n, by omega⟩
  let S := Ici m
  have hc : ∀ i : S, ∃ j ≤ (i : Fin k),
      n / 2 < ∑ x ∈ Icc j (i : Fin k), a x ∧
      ∑ x ∈ Icc j (i : Fin k), a x ≤ max (a i) (2 * (n / 2)) := by
    intro i
    apply crossing_interval a hm.monotone
    apply prefix_crosses_half a hm hp
    have hle : m ≤ (i : Fin k) := mem_Ici.mp i.property
    exact hle
  choose start hstart using hc
  let v : S → ℕ := fun i ↦ ∑ x ∈ Icc (start i) (i : Fin k), a x
  have hv (i : S) : v i ∈ Ioc (n / 2) n := by
    apply mem_Ioc.mpr
    refine ⟨(hstart i).2.1, (hstart i).2.2.trans ?_⟩
    apply max_le (hb i)
    omega
  have hinj : Function.Injective v := by
    intro i j he
    have hI : Icc (start i) (i : Fin k) = Icc (start j) (j : Fin k) := by
      apply ha
      · simpa only [Set.mem_ofPred_eq, coe_Icc] using
          (Set.ordConnected_Icc : (Set.Icc (start i) (i : Fin k)).OrdConnected)
      · simpa only [Set.mem_ofPred_eq, coe_Icc] using
          (Set.ordConnected_Icc : (Set.Icc (start j) (j : Fin k)).OrdConnected)
      · exact he
    have hi : (i : Fin k) ∈ Icc (start i) (i : Fin k) :=
      mem_Icc.mpr ⟨(hstart i).1, le_rfl⟩
    have hj : (j : Fin k) ∈ Icc (start j) (j : Fin k) :=
      mem_Icc.mpr ⟨(hstart j).1, le_rfl⟩
    have hij := (mem_Icc.mp (hI ▸ hi)).2
    have hji := (mem_Icc.mp (hI.symm ▸ hj)).2
    exact Subtype.ext (le_antisymm hij hji)
  have hcount : S.card ≤ n - n / 2 := by
    calc
      S.card = (univ.image v).card := by rw [card_image_of_injective _ hinj]; simp
      _ ≤ (Ioc (n / 2) n).card := card_le_card (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := mem_image.mp hx
        exact hv i)
      _ = n - n / 2 := Nat.card_Ioc _ _
  have hcard : S.card = k - Nat.sqrt n := by simp [S, m, Fin.card_Ici]
  rw [hcard] at hcount
  omega

/-- Integer-valued version, with exactly the finite admissibility assumptions upstream. -/
theorem finite_int_length_le_half_add_sqrt {k n : ℕ} (a : Fin k → ℤ)
    (hr : Set.range a ⊆ Set.Icc 1 (n : ℤ)) (hm : StrictMono a)
    (ha : Erdos357.HasDistinctSums a) : k ≤ n - n / 2 + Nat.sqrt n := by
  let b := fun i ↦ (a i).toNat
  have hab (i : Fin k) : 1 ≤ a i ∧ a i ≤ n := hr ⟨i, rfl⟩
  have he (i : Fin k) : (b i : ℤ) = a i := Int.toNat_of_nonneg (by have := (hab i).1; omega)
  have hm' : StrictMono b := by
    intro i j hij
    have hh := hm hij
    rw [← he i, ← he j] at hh
    exact_mod_cast hh
  have hp : ∀ i, 0 < b i := by
    intro i
    have hh := (hab i).1
    rw [← he i] at hh
    omega
  have hb : ∀ i, b i ≤ n := by
    intro i
    have hh := (hab i).2
    rw [← he i] at hh
    exact_mod_cast hh
  have hdistinct : Erdos357.HasDistinctSums b := by
    intro J hJ K hK hs
    apply ha hJ hK
    have hc := congrArg (fun z : ℕ ↦ (z : ℤ)) hs
    simpa only [Nat.cast_sum, he] using hc
  exact finite_length_le_half_add_sqrt b hm' hp hb hdistinct

/-- The literal finite predicate forces injectivity for natural block encodings. -/
theorem block_inj_of_hasDistinctSums (a : ℕ → ℕ) (k : ℕ)
    (ha : Erdos357.HasDistinctSums (fun i : Fin k ↦ a i.val))
    {i l j r : ℕ} (hl : 0 < l) (hr : 0 < r) (hil : i+l ≤ k) (hjr : j+r ≤ k)
    (he : (∑ t ∈ range l, a (i+t)) = (∑ t ∈ range r, a (j+t))) : i = j ∧ l = r := by
  classical
  let J : Finset (Fin k) := Icc ⟨i, by omega⟩ ⟨i+l-1, by omega⟩
  let K : Finset (Fin k) := Icc ⟨j, by omega⟩ ⟨j+r-1, by omega⟩
  have hJ : J.map Fin.valEmbedding = Ico i (i+l) := by
    dsimp [J]
    rw [Fin.map_valEmbedding_Icc]
    ext t
    simp only [mem_Icc, mem_Ico]
    omega
  have hK : K.map Fin.valEmbedding = Ico j (j+r) := by
    dsimp [K]
    rw [Fin.map_valEmbedding_Icc]
    ext t
    simp only [mem_Icc, mem_Ico]
    omega
  have hs (S : Finset (Fin k)) (x len : ℕ)
      (hS : S.map Fin.valEmbedding = Ico x (x+len)) :
      (∑ t ∈ S, a t.val) = ∑ t ∈ range len, a (x+t) := by
    have hh : (∑ t ∈ S, a t.val) = ∑ t ∈ S.map Fin.valEmbedding, a t := by simp
    rw [hh, hS, sum_Ico_eq_sum_range]
    simp
  have hJK : J = K := ha
    (by simpa only [Set.mem_ofPred_eq, J, coe_Icc] using (Set.ordConnected_Icc :
      (Set.Icc (⟨i, by omega⟩ : Fin k) ⟨i+l-1, by omega⟩).OrdConnected))
    (by simpa only [Set.mem_ofPred_eq, K, coe_Icc] using (Set.ordConnected_Icc :
      (Set.Icc (⟨j, by omega⟩ : Fin k) ⟨j+r-1, by omega⟩).OrdConnected))
    (by change (∑ t ∈ J, a t.val) = ∑ t ∈ K, a t.val
        rw [hs J i l hJ, hs K j r hK]
        exact he)
  have hmap : Ico i (i+l) = Ico j (j+r) := by rw [← hJ, ← hK, hJK]
  have hh : (i,l) = (j,r) := block_injective hl hr hmap
  exact Prod.mk.inj hh

end Snively357

namespace Erdos357Upper
open Finset

/-- Sum of `a x, ..., a (y-1)`. -/
def blk (a : ℕ → ℕ) (x y : ℕ) : ℕ := ∑ i ∈ Ico x y, a i

/-- Hypotheses on the first `k` terms. -/
structure Adm (a : ℕ → ℕ) (k n : ℕ) : Prop where
  pos : ∀ i, i < k → 0 < a i
  mono : ∀ i j, i < j → j < k → a i < a j
  le : ∀ i, i < k → a i ≤ n
  inj : ∀ x y x' y', x < y → x' < y' → y ≤ k → y' ≤ k →
    blk a x y = blk a x' y' → x = x' ∧ y = y'

theorem blk_split (a : ℕ → ℕ) {x m y : ℕ} (h1 : x ≤ m) (h2 : m ≤ y) :
    blk a x y = blk a x m + blk a m y :=
  (Finset.sum_Ico_consecutive a h1 h2).symm

theorem blk_succ (a : ℕ → ℕ) (x : ℕ) : blk a x (x + 1) = a x := by
  simp [blk]

theorem blk_run (a : ℕ → ℕ) (i c : ℕ) :
    ∀ l, (∀ j < l, a (i + j) = c + j) → 2 * blk a i (i + l) + l = l * (2 * c + l) := by
  intro l
  induction l with
  | zero => intro _; simp [blk]
  | succ l ih =>
    intro h
    have h1 := ih (fun j hj => h j (by omega))
    have h2 : blk a i (i + (l + 1)) = blk a i (i + l) + a (i + l) := by
      rw [← add_assoc, blk_split a (show i ≤ i + l by omega) (show i + l ≤ i + l + 1 by omega),
        blk_succ]
    have h3 := h l (by omega)
    rw [h2, h3]
    nlinarith

theorem Adm.ge_idx {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) :
    ∀ i, i < k → i + 1 ≤ a i := by
  intro i
  induction i with
  | zero => intro h; exact H.pos 0 h
  | succ i ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := H.mono i (i + 1) (by omega) h
    omega

theorem Adm.tri {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) :
    ∀ y, y ≤ k → y * (y + 1) ≤ 2 * blk a 0 y := by
  intro y
  induction y with
  | zero => intro _; simp [blk]
  | succ y ih =>
    intro hy
    have h1 := ih (by omega)
    have h2 := H.ge_idx y (by omega)
    have h3 : blk a 0 (y + 1) = blk a 0 y + a y := by
      rw [blk_split a (Nat.zero_le y) (Nat.le_succ y), blk_succ]
    rw [h3]
    nlinarith

/-- The canonical start: the last start whose block ending at `y` has sum `> t`. -/
def canon (a : ℕ → ℕ) (t y : ℕ) : ℕ :=
  Nat.findGreatest (fun x => t < blk a x y) (y - 1)

theorem canon_lt (a : ℕ → ℕ) (t : ℕ) {y : ℕ} (hy : 1 ≤ y) : canon a t y < y := by
  have := Nat.findGreatest_le (P := fun x => t < blk a x y) (y - 1)
  unfold canon
  omega

theorem canon_spec (a : ℕ → ℕ) (t : ℕ) {y : ℕ} (h0 : t < blk a 0 y) :
    t < blk a (canon a t y) y :=
  Nat.findGreatest_spec (P := fun x => t < blk a x y) (Nat.zero_le (y - 1)) h0

theorem canon_max (a : ℕ → ℕ) (t : ℕ) {y x : ℕ} (hx : canon a t y < x) (hxy : x < y) :
    blk a x y ≤ t := by
  have := Nat.findGreatest_is_greatest (P := fun x => t < blk a x y) hx (by omega)
  exact not_lt.mp this

theorem canon_le_n {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t y : ℕ}
    (ht : 2 * t ≤ n) (hy : 1 ≤ y) (hyk : y ≤ k) :
    blk a (canon a t y) y ≤ n := by
  have hc := canon_lt a t hy
  by_cases h1 : canon a t y + 1 = y
  · have : blk a (canon a t y) y = a (canon a t y) := by
      have h2 := blk_succ a (canon a t y)
      rwa [h1] at h2
    rw [this]
    exact H.le _ (by omega)
  · have hc1 : canon a t y + 1 < y := by omega
    have hle : blk a (canon a t y + 1) y ≤ t := canon_max a t (by omega) hc1
    have hsplit : blk a (canon a t y) y = a (canon a t y) + blk a (canon a t y + 1) y := by
      rw [blk_split a (show canon a t y ≤ canon a t y + 1 by omega) (by omega), blk_succ]
    have hlast : a (y - 1) ≤ blk a (canon a t y + 1) y := by
      have hmem : y - 1 ∈ Ico (canon a t y + 1) y := mem_Ico.mpr ⟨by omega, by omega⟩
      exact Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) hmem
    have hlt := H.mono (canon a t y) (y - 1) (by omega) (by omega)
    omega

/-- One step to the left of a non-singleton block of sum `≤ θ` stays `≤ n`. -/
theorem chain {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {θ : ℕ} (hθ : 3 * θ ≤ 2 * n + 4)
    {x y : ℕ} (hxy : x + 2 ≤ y) (hyk : y ≤ k) (hx1 : 1 ≤ x) (hs : blk a x y ≤ θ) :
    blk a (x - 1) y ≤ n := by
  have hsplit : blk a (x - 1) y = a (x - 1) + blk a x y := by
    have := blk_split a (show x - 1 ≤ x by omega) (show x ≤ y by omega)
    rw [this]
    have h2 : x = (x - 1) + 1 := by omega
    have := blk_succ a (x - 1)
    rw [← h2] at this
    rw [this]
  have hpair : a x + a (x + 1) ≤ blk a x y := by
    have hsub : ({x, x + 1} : Finset ℕ) ⊆ Ico x y := by
      intro i hi
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp only [mem_Ico] <;> omega
    have := Finset.sum_le_sum_of_subset (f := a) hsub
    rwa [Finset.sum_pair (by omega)] at this
  have h1 := H.mono (x - 1) x (by omega) (by omega)
  have h2 := H.mono x (x + 1) (by omega) (by omega)
  omega

/-- Existence of the extension beyond `θ` used for the hole accounting. -/
theorem exists_beyond {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {θ : ℕ} (hθ : 3 * θ ≤ 2 * n + 4)
    {y c : ℕ} (hyk : y ≤ k) (hc : c + 2 ≤ y) (hcθ : blk a c y ≤ θ) (h0 : θ < blk a 0 y) :
    ∃ x', x' < c ∧ θ < blk a x' y ∧ blk a x' y ≤ n := by
  let s : Set ℕ := {x | blk a x y ≤ θ}
  have hne : s.Nonempty := ⟨c, hcθ⟩
  have hmem : sInf s ∈ s := Nat.sInf_mem hne
  have hle : sInf s ≤ c := Nat.sInf_le hcθ
  have hne0 : sInf s ≠ 0 := by
    intro h0'
    have : blk a 0 y ≤ θ := by
      have := hmem
      rw [h0'] at this
      exact this
    omega
  have hmin : sInf s - 1 ∉ s := Nat.notMem_of_lt_sInf (by omega)
  refine ⟨sInf s - 1, by omega, ?_, ?_⟩
  · simp only [s, Set.mem_ofPred_eq, not_le] at hmin
    exact hmin
  · exact chain H hθ (by omega) hyk (by omega) hmem

/-- A run of consecutive integers inside the set is a run of consecutive terms. -/
theorem consecutive_run {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (c : ℕ) :
    ∀ l, 1 ≤ l → (∀ j < l, ∃ i, i < k ∧ a i = c + j) →
      ∃ i, i + l ≤ k ∧ ∀ j < l, a (i + j) = c + j := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    intro hmem
    obtain ⟨i, hi, hai⟩ := hmem 0 (by omega)
    refine ⟨i, by omega, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    simpa using hai
  | succ l hl ih =>
    intro hmem
    obtain ⟨i, hil, hai⟩ := ih (fun j hj => hmem j (by omega))
    obtain ⟨i2, hi2, hai2⟩ := hmem l (by omega)
    have h1 : a (i + (l - 1)) = c + (l - 1) := hai (l - 1) (by omega)
    have hlt : i + l ≤ i2 := by
      by_contra hn
      have h3 : i2 ≤ i + (l - 1) := by omega
      rcases h3.eq_or_lt with h | h
      · rw [h] at hai2; omega
      · have := H.mono i2 (i + (l - 1)) h (by omega); omega
    have hlk : i + l < k := by omega
    have hge : a (i + (l - 1)) < a (i + l) := H.mono _ _ (by omega) hlk
    have hle : a (i + l) ≤ a i2 := by
      rcases hlt.eq_or_lt with h | h
      · rw [h]
      · exact (H.mono _ _ h hi2).le
    refine ⟨i, by omega, fun j hj => ?_⟩
    by_cases hjl : j < l
    · exact hai j hjl
    · have : j = l := by omega
      subst this
      omega

/-- Integers of `(t, θ]` that are not terms. -/
def holes (a : ℕ → ℕ) (k t θ : ℕ) : Finset ℕ :=
  (Ioc t θ).filter (fun z => z ∉ (range k).image a)

theorem mem_holes {a : ℕ → ℕ} {k t θ z : ℕ} :
    z ∈ holes a k t θ ↔ (t < z ∧ z ≤ θ) ∧ ¬ ∃ i, i < k ∧ a i = z := by
  simp [holes, mem_Ioc]

/-- Main accounting: each hole in `(t, θ]` costs one slot of `(t, n]`. -/
theorem main_count {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ : ℕ}
    (ht : 2 * t ≤ n) (htθ : t ≤ θ) (hθ : 3 * θ ≤ 2 * n + 4) (hθn : θ ≤ n) :
    k + (holes a k t θ).card ≤ (n - t) + Nat.sqrt (2 * θ) := by
  classical
  let A : Finset ℕ := (range k).image a
  let S : ℕ → ℕ := fun y => blk a 0 y
  let σ : ℕ → ℕ := fun y => blk a (canon a t y) y
  let Yall : Finset ℕ := Icc 1 k
  let I : Finset ℕ := Yall.filter (fun y => t < S y)
  let Lot : Finset ℕ := Yall.filter (fun y => ¬ t < S y)
  let Lo : Finset ℕ := Yall.filter (fun y => S y ≤ θ)
  let Y1 : Finset ℕ := I.filter (fun y => σ y ≤ θ ∧ σ y ∉ A)
  let Y2 : Finset ℕ := Y1.filter (fun y => θ < S y)
  let Y1lo : Finset ℕ := Y1.filter (fun y => ¬ θ < S y)
  have memI : ∀ y, y ∈ I ↔ (1 ≤ y ∧ y ≤ k) ∧ t < S y := by
    intro y; simp only [I, Yall, mem_filter, mem_Icc]
  have memY1 : ∀ y, y ∈ Y1 ↔ ((1 ≤ y ∧ y ≤ k) ∧ t < S y) ∧ (σ y ≤ θ ∧ σ y ∉ A) := by
    intro y; simp only [Y1, I, Yall, mem_filter, mem_Icc]
  have memY2 : ∀ y, y ∈ Y2 ↔ (((1 ≤ y ∧ y ≤ k) ∧ t < S y) ∧ (σ y ≤ θ ∧ σ y ∉ A)) ∧ θ < S y := by
    intro y; simp only [Y2, Y1, I, Yall, mem_filter, mem_Icc]
  have memA : ∀ z, z ∈ A ↔ ∃ i, i < k ∧ a i = z := by
    intro z; simp [A]
  -- basic facts for y ∈ I
  have hI1 : ∀ y ∈ I, canon a t y < y := by
    intro y hy
    have := (memI y).mp hy
    exact canon_lt a t this.1.1
  have hI2 : ∀ y ∈ I, t < σ y ∧ σ y ≤ n := by
    intro y hy
    have h := (memI y).mp hy
    exact ⟨canon_spec a t h.2, canon_le_n H ht h.1.1 h.1.2⟩
  have σinj : Set.InjOn σ (I : Set ℕ) := by
    intro y hy y2 hy2 he
    have hy' := (memI y).mp hy
    have hy2' := (memI y2).mp hy2
    exact (H.inj _ _ _ _ (hI1 y hy) (hI1 y2 hy2) hy'.1.2 hy2'.1.2 he).2
  -- extension beyond θ for y ∈ Y2
  have hex : ∀ y ∈ Y2, ∃ x', x' < canon a t y ∧ θ < blk a x' y ∧ blk a x' y ≤ n := by
    intro y hy
    have h := (memY2 y).mp hy
    have hyI : y ∈ I := (memI y).mpr h.1.1
    have hc := hI1 y hyI
    have hc1 : canon a t y + 1 < y := by
      by_contra hn
      have heq : canon a t y + 1 = y := by omega
      have h2 : σ y = a (canon a t y) := by
        have h3 := blk_succ a (canon a t y)
        simp only [σ]
        rw [heq] at h3
        exact h3
      apply h.1.2.2
      rw [memA]
      exact ⟨canon a t y, by omega, h2.symm⟩
    exact exists_beyond H hθ h.1.1.1.2 (by omega) h.1.2.1 h.2
  choose! xp hxp using hex
  let Ψ : ℕ → ℕ := fun y => blk a (xp y) y
  have hY2k : ∀ y ∈ Y2, y ≤ k := fun y hy => ((memY2 y).mp hy).1.1.1.2
  have hΨlt : ∀ y ∈ Y2, xp y < y := fun y hy => by
    have := hI1 y ((memI y).mpr ((memY2 y).mp hy).1.1)
    have := (hxp y hy).1
    omega
  have Ψinj : Set.InjOn Ψ (Y2 : Set ℕ) := by
    intro y hy y2 hy2 he
    exact (H.inj _ _ _ _ (hΨlt y hy) (hΨlt y2 hy2) (hY2k y hy) (hY2k y2 hy2) he).2
  let Sg : Finset ℕ := I.image σ
  let Hs : Finset ℕ := holes a k t θ
  let Hb : Finset ℕ := Hs.filter (fun z => z ∉ Sg)
  let Ha : Finset ℕ := Hs.filter (fun z => ¬ z ∉ Sg)
  let Ps : Finset ℕ := Y2.image Ψ
  have cSg : Sg.card = I.card := card_image_of_injOn σinj
  have cPs : Ps.card = Y2.card := card_image_of_injOn Ψinj
  have cH : Hb.card + Ha.card = Hs.card := card_filter_add_card_filter_not _
  -- Ha is covered by Y1
  have hHa : Ha.card ≤ Y1.card := by
    have hsub : Ha ⊆ Y1.image σ := by
      intro z hz
      simp only [Ha, mem_filter, not_not] at hz
      obtain ⟨hzH, hzS⟩ := hz
      obtain ⟨y, hyI, rfl⟩ := mem_image.mp hzS
      have hzh := mem_holes.mp hzH
      rw [mem_image]
      refine ⟨y, (memY1 y).mpr ⟨(memI y).mp hyI, hzh.1.2, ?_⟩, rfl⟩
      rw [memA]
      exact hzh.2
    exact (card_le_card hsub).trans card_image_le
  -- Y1 splits at θ < S
  have cY1 : Y2.card + Y1lo.card = Y1.card := card_filter_add_card_filter_not _
  -- I and Lot split Yall
  have cI : I.card + Lot.card = k := by
    have h := card_filter_add_card_filter_not (s := Yall) (fun y => t < S y)
    have hk : Yall.card = k := by simp [Yall]
    rw [hk] at h
    exact h
  -- small prefix sums
  have hLo : Lo.card ≤ Nat.sqrt (2 * θ) := by
    have hsub : Lo ⊆ Icc 1 (Nat.sqrt (2 * θ)) := by
      intro y hy
      simp only [Lo, Yall, mem_filter, mem_Icc] at hy
      rw [mem_Icc]
      refine ⟨hy.1.1, Nat.le_sqrt.mpr ?_⟩
      have := H.tri y hy.1.2
      nlinarith [hy.2]
    have := card_le_card hsub
    simpa using this
  have hdisj : Disjoint Lot Y1lo := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Lot, Y1lo, Y1, I, Yall, mem_filter, mem_Icc] at hy1 hy2
    exact hy1.2 hy2.1.1.2
  have hLoSub : Lot ∪ Y1lo ⊆ Lo := by
    intro y hy
    rcases mem_union.mp hy with h | h
    · simp only [Lot, Lo, Yall, mem_filter, mem_Icc] at h ⊢
      exact ⟨h.1, by omega⟩
    · simp only [Y1lo, Lo, Y1, I, Yall, mem_filter, mem_Icc] at h ⊢
      exact ⟨h.1.1.1, by omega⟩
  have hLo2 : Lot.card + Y1lo.card ≤ Nat.sqrt (2 * θ) := by
    have := card_le_card hLoSub
    rw [card_union_of_disjoint hdisj] at this
    omega
  -- the target interval
  have hd1 : Disjoint Sg Hb := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Hb, mem_filter] at hz2
    exact hz2.2 hz1
  have hd2 : Disjoint Sg Ps := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨y2, hy2, rfl⟩ := mem_image.mp hz2
    obtain ⟨y, hy, he⟩ := mem_image.mp hz1
    have hyI : y ∈ I := hy
    have hy2Y := (memY2 y2).mp hy2
    have hy2I : y2 ∈ I := (memI y2).mpr hy2Y.1.1
    have hyk := ((memI y).mp hyI).1.2
    have := H.inj (canon a t y) y (xp y2) y2 (hI1 y hyI) (hΨlt y2 hy2) hyk
      (hY2k y2 hy2) he
    have h1 := (hxp y2 hy2).1
    have h2 : y = y2 := this.2
    subst h2
    omega
  have hd3 : Disjoint Hb Ps := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨y2, hy2, rfl⟩ := mem_image.mp hz2
    simp only [Hb, Hs, mem_filter] at hz1
    have h1 := (mem_holes.mp hz1.1).1.2
    have h2 := (hxp y2 hy2).2.1
    simp only [Ψ] at h1
    omega
  have hsubI : Sg ∪ Hb ∪ Ps ⊆ Ioc t n := by
    intro z hz
    rw [mem_Ioc]
    rcases mem_union.mp hz with h | h
    · rcases mem_union.mp h with h | h
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
        exact hI2 y hy
      · simp only [Hb, Hs, mem_filter] at h
        have := (mem_holes.mp h.1).1
        omega
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
      have h1 := (hxp y hy).2
      simp only [Ψ]
      omega
  have hcard : Sg.card + Hb.card + Ps.card ≤ n - t := by
    have h1 := card_le_card hsubI
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hd2, hd3⟩),
      card_union_of_disjoint hd1] at h1
    simpa using h1
  have hHs : Hs.card = (holes a k t θ).card := rfl
  omega

/- ### Bridge to the literal upstream `f` -/

/-- Admissible integer sequences give `Adm` (zero-based natural encoding). -/
theorem adm_of_int {k n : ℕ} (a : Fin k → ℤ) (hr : Set.range a ⊆ Set.Icc 1 (n : ℤ))
    (hm : StrictMono a) (ha : Erdos357.HasDistinctSums a) :
    ∃ b : ℕ → ℕ, Adm b k n := by
  classical
  have hab : ∀ i : Fin k, 1 ≤ a i ∧ a i ≤ n := fun i => hr ⟨i, rfl⟩
  let c : Fin k → ℕ := fun i => (a i).toNat
  have hc : ∀ i, (c i : ℤ) = a i := fun i => Int.toNat_of_nonneg (by have := (hab i).1; omega)
  have hcm : StrictMono c := by
    intro i j hij
    have h := hm hij
    rw [← hc i, ← hc j] at h
    exact_mod_cast h
  have hcd : Erdos357.HasDistinctSums c := by
    intro J hJ K hK hs
    apply ha hJ hK
    have h2 := congrArg (fun z : ℕ => (z : ℤ)) hs
    simpa only [Nat.cast_sum, hc] using h2
  let b : ℕ → ℕ := fun i => if h : i < k then c ⟨i, h⟩ else 0
  have hbc : ∀ i (h : i < k), b i = c ⟨i, h⟩ := fun i h => by simp [b, h]
  have hbd : Erdos357.HasDistinctSums (fun i : Fin k => b i.val) := by
    have : (fun i : Fin k => b i.val) = c := by
      funext i; rw [hbc i.val i.isLt]
    rw [this]; exact hcd
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hbc i hi]
    have := (hab ⟨i, hi⟩).1
    have := hc ⟨i, hi⟩
    omega
  · intro i j hij hj
    rw [hbc i (by omega), hbc j hj]
    exact hcm (show (⟨i, by omega⟩ : Fin k) < ⟨j, hj⟩ from hij)
  · intro i hi
    rw [hbc i hi]
    have := (hab ⟨i, hi⟩).2
    have := hc ⟨i, hi⟩
    omega
  · intro x y x' y' hxy hxy' hyk hyk' he
    have e1 : blk b x y = ∑ t ∈ range (y - x), b (x + t) :=
      Finset.sum_Ico_eq_sum_range _ _ _
    have e2 : blk b x' y' = ∑ t ∈ range (y' - x'), b (x' + t) :=
      Finset.sum_Ico_eq_sum_range _ _ _
    have := Snively357.block_inj_of_hasDistinctSums b k hbd (i := x) (l := y - x) (j := x')
      (r := y' - x') (by omega) (by omega) (by omega) (by omega) (by rw [← e1, ← e2]; exact he)
    omega

/-- `z` lies in the `(l+1)`-run `[l w, l w + l]` or in the `l`-run `[(l+1) w + 1, (l+1) w + l]`. -/
def Hit (l w z : ℕ) : Prop :=
  (l * w ≤ z ∧ z ≤ l * w + l) ∨ ((l + 1) * w + 1 ≤ z ∧ z ≤ (l + 1) * w + l)

instance (l w z : ℕ) : Decidable (Hit l w z) := by unfold Hit; infer_instance

/-- Equal-sum runs of lengths `l+1` and `l`: they cannot both lie in the set. -/
theorem pattern_false_gen {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (l w : ℕ) (hl : 1 ≤ l)
    (hY : ∀ j < l + 1, ∃ i, i < k ∧ a i = l * w + j)
    (hX : ∀ j < l, ∃ i, i < k ∧ a i = (l + 1) * w + 1 + j) : False := by
  obtain ⟨iY, hiY, haY⟩ := consecutive_run H (l * w) (l + 1) (by omega) hY
  obtain ⟨iX, hiX, haX⟩ := consecutive_run H ((l + 1) * w + 1) l hl hX
  have e1 := blk_run a iY (l * w) (l + 1) haY
  have e2 := blk_run a iX ((l + 1) * w + 1) l haX
  have hb : blk a iY (iY + (l + 1)) = blk a iX (iX + l) := by nlinarith [e1, e2]
  have := H.inj iY (iY + (l + 1)) iX (iX + l) (by omega) (by omega) hiY hiX hb
  omega

/-- Every pattern whose points lie in `(t, θ]` contains a hole. -/
theorem pattern_hit {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ l w : ℕ} (hl : 1 ≤ l)
    (h1 : t < l * w) (h2 : (l + 1) * w + l ≤ θ) :
    ∃ z, z ∈ holes a k t θ ∧ Hit l w z := by
  by_contra hcon
  push Not at hcon
  have h3 : l * w ≤ (l + 1) * w := Nat.mul_le_mul_right w (Nat.le_succ l)
  have hall : ∀ z, Hit l w z → ∃ i, i < k ∧ a i = z := by
    intro z hz
    by_contra hnot
    apply hcon z _ hz
    rw [mem_holes]
    refine ⟨⟨?_, ?_⟩, hnot⟩
    · rcases hz with h | h <;> omega
    · rcases hz with h | h <;> omega
  exact pattern_false_gen H l w hl (fun j hj => hall _ (Or.inl ⟨by omega, by omega⟩))
    (fun j hj => hall _ (Or.inr ⟨by omega, by omega⟩))

/-- Number of patterns `w ∈ (α, β]` of family `l` that contain `z`. -/
def cnt (l α β z : ℕ) : ℕ := ((Ioc α β).filter (fun w => Hit l w z)).card

/-- Weakening of the size bound. -/
theorem Adm.mono_n {a : ℕ → ℕ} {k n n' : ℕ} (H : Adm a k n) (h : n ≤ n') : Adm a k n' :=
  { pos := H.pos, mono := H.mono, le := fun i hi => (H.le i hi).trans h, inj := H.inj }

/-- One band: each of its patterns contains a hole, so `#patterns ≤ Σ_{holes} cnt`. -/
theorem band_count {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ l α β : ℕ} (hl : 1 ≤ l)
    (h1 : t < l * (α + 1)) (h2 : (l + 1) * β + l ≤ θ) :
    β - α ≤ ∑ z ∈ holes a k t θ, cnt l α β z := by
  classical
  have hex : ∀ w ∈ Ioc α β, 1 ≤ ((holes a k t θ).filter (fun z => Hit l w z)).card := by
    intro w hw
    have hw' := mem_Ioc.mp hw
    have e1 : l * (α + 1) ≤ l * w := Nat.mul_le_mul_left l hw'.1
    have e2 : (l + 1) * w ≤ (l + 1) * β := Nat.mul_le_mul_left (l + 1) hw'.2
    obtain ⟨z, hz, hzw⟩ := pattern_hit H hl (t := t) (θ := θ) (l := l) (w := w)
      (by omega) (by omega)
    exact card_pos.mpr ⟨z, mem_filter.mpr ⟨hz, hzw⟩⟩
  calc β - α = (Ioc α β).card := by simp
    _ = ∑ w ∈ Ioc α β, 1 := by simp
    _ ≤ ∑ w ∈ Ioc α β, ((holes a k t θ).filter (fun z => Hit l w z)).card := sum_le_sum hex
    _ = ∑ z ∈ holes a k t θ, cnt l α β z := by
        unfold cnt
        exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun w z => Hit l w z)

/-- A list of bands: total number of patterns `≤ Σ_{holes} (total degree)`. -/
theorem list_key {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ : ℕ} (L : List (ℕ × ℕ × ℕ))
    (hL : ∀ p ∈ L, 1 ≤ p.1 ∧ t < p.1 * (p.2.1 + 1) ∧ (p.1 + 1) * p.2.2 + p.1 ≤ θ) :
    (L.map (fun p => p.2.2 - p.2.1)).sum ≤
      ∑ z ∈ holes a k t θ, (L.map (fun p => cnt p.1 p.2.1 p.2.2 z)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := hL p (List.mem_cons_self)
    have ih' := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    have hb := band_count H hp.1 hp.2.1 hp.2.2
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    exact Nat.add_le_add hb ih'

/-- **Packing count for a design.**  If every integer has total degree `≤ D`, then
`#patterns ≤ D * #holes`. -/
theorem list_count {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) {t θ D : ℕ} (L : List (ℕ × ℕ × ℕ))
    (hL : ∀ p ∈ L, 1 ≤ p.1 ∧ t < p.1 * (p.2.1 + 1) ∧ (p.1 + 1) * p.2.2 + p.1 ≤ θ)
    (hfib : ∀ z, (L.map (fun p => cnt p.1 p.2.1 p.2.2 z)).sum ≤ D) :
    (L.map (fun p => p.2.2 - p.2.1)).sum ≤ D * (holes a k t θ).card := by
  refine (list_key H L hL).trans ?_
  calc ∑ z ∈ holes a k t θ, (L.map (fun p => cnt p.1 p.2.1 p.2.2 z)).sum
      ≤ ∑ z ∈ holes a k t θ, D := sum_le_sum (fun z _ => hfib z)
    _ = D * (holes a k t θ).card := by simp [mul_comm]

/- ### Where can a band touch an integer? -/

/-- Y-hits of a band at `z`: `z ∈ [l w, l w + l]`. -/
def cY (l α β z : ℕ) : ℕ := ((Ioc α β).filter (fun w => l * w ≤ z ∧ z ≤ l * w + l)).card

/-- X-hits of a band at `z`: `z ∈ [(l+1) w + 1, (l+1) w + l]`. -/
def cX (l α β z : ℕ) : ℕ :=
  ((Ioc α β).filter (fun w => (l + 1) * w + 1 ≤ z ∧ z ≤ (l + 1) * w + l)).card

theorem cnt_le_add (l α β z : ℕ) : cnt l α β z ≤ cY l α β z + cX l α β z := by
  classical
  unfold cnt cY cX
  have : (Ioc α β).filter (fun w => Hit l w z) =
      (Ioc α β).filter (fun w => l * w ≤ z ∧ z ≤ l * w + l) ∪
        (Ioc α β).filter (fun w => (l + 1) * w + 1 ≤ z ∧ z ≤ (l + 1) * w + l) := by
    rw [← filter_or]
    rfl
  rw [this]
  exact card_union_le _ _

theorem cX_le_one (l α β z : ℕ) : cX l α β z ≤ 1 := by
  classical
  unfold cX
  apply card_le_one.mpr
  intro w1 h1 w2 h2
  rw [mem_filter] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.mul_le_mul_left (l + 1) (Nat.succ_le_of_lt h)
    nlinarith [h1.2.1, h1.2.2, h2.2.1, h2.2.2]
  · have := Nat.mul_le_mul_left (l + 1) (Nat.succ_le_of_lt h)
    nlinarith [h1.2.1, h1.2.2, h2.2.1, h2.2.2]

theorem cY_le_two (l α β z : ℕ) (hl : 1 ≤ l) : cY l α β z ≤ 2 := by
  classical
  unfold cY
  have hsub : (Ioc α β).filter (fun w => l * w ≤ z ∧ z ≤ l * w + l) ⊆ {z / l, z / l - 1} := by
    intro w hw
    rw [mem_filter] at hw
    obtain ⟨_, h1, h2⟩ := hw
    have a1 : w ≤ z / l := (Nat.le_div_iff_mul_le hl).2 (by linarith)
    have a2 : z / l < w + 2 := (Nat.div_lt_iff_lt_mul hl).2 (by nlinarith)
    simp only [mem_insert, mem_singleton]
    omega
  exact (card_le_card hsub).trans card_le_two

theorem cY_zero (l α β z : ℕ) (h : z < l * (α + 1) ∨ l * β + l < z) : cY l α β z = 0 := by
  classical
  unfold cY
  rw [card_eq_zero, filter_eq_empty_iff]
  intro w hw
  have hw' := mem_Ioc.mp hw
  have e1 : l * (α + 1) ≤ l * w := Nat.mul_le_mul_left l hw'.1
  have e2 : l * w ≤ l * β := Nat.mul_le_mul_left l hw'.2
  rintro ⟨h1, h2⟩
  omega

theorem cX_zero (l α β z : ℕ) (h : z < (l + 1) * (α + 1) + 1 ∨ (l + 1) * β + l < z) :
    cX l α β z = 0 := by
  classical
  unfold cX
  rw [card_eq_zero, filter_eq_empty_iff]
  intro w hw
  have hw' := mem_Ioc.mp hw
  have e1 : (l + 1) * (α + 1) ≤ (l + 1) * w := Nat.mul_le_mul_left (l + 1) hw'.1
  have e2 : (l + 1) * w ≤ (l + 1) * β := Nat.mul_le_mul_left (l + 1) hw'.2
  rintro ⟨h1, h2⟩
  omega

/-- Neither the Y-runs nor the X-runs of the band reach `z`. -/
theorem cnt_zero (l α β z : ℕ) (hY : z < l * (α + 1) ∨ l * β + l < z)
    (hX : z < (l + 1) * (α + 1) + 1 ∨ (l + 1) * β + l < z) : cnt l α β z = 0 := by
  have := cnt_le_add l α β z
  rw [cY_zero l α β z hY, cX_zero l α β z hX] at this
  omega

/-- Only the X-runs can reach `z`: degree `≤ 1`. -/
theorem cnt_X1 (l α β z : ℕ) (hY : z < l * (α + 1) ∨ l * β + l < z) : cnt l α β z ≤ 1 := by
  have := cnt_le_add l α β z
  have := cX_le_one l α β z
  rw [cY_zero l α β z hY] at *
  omega

/-- Only the Y-runs can reach `z`: degree `≤ 2`. -/
theorem cnt_Y2 (l α β z : ℕ) (hl : 1 ≤ l)
    (hX : z < (l + 1) * (α + 1) + 1 ∨ (l + 1) * β + l < z) : cnt l α β z ≤ 2 := by
  have := cnt_le_add l α β z
  have := cY_le_two l α β z hl
  rw [cX_zero l α β z hX] at *
  omega

/-- Both kinds can reach `z`: degree `≤ 3`. -/
theorem cnt_YX3 (l α β z : ℕ) (hl : 1 ≤ l) : cnt l α β z ≤ 3 := by
  have := cnt_le_add l α β z
  have := cX_le_one l α β z
  have := cY_le_two l α β z hl
  omega


/-- The design (in units of `j`). -/
def bandsL (j : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(4, 45000 * j, 45687 * j),
   (5, 36550 * j, 37499 * j),
   (6, 31250 * j, 31729 * j),
   (5, 38075 * j, 39999 * j),
   (9, 22222 * j, 23999 * j)]

theorem bandsL_ok (j : ℕ) (hj : 12 ≤ j) :
    ∀ p ∈ bandsL j, 1 ≤ p.1 ∧ 180000 * j < p.1 * (p.2.1 + 1) ∧
      (p.1 + 1) * p.2.2 + p.1 ≤ 240000 * j + 1 := by
  intro p hp
  simp only [bandsL, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by norm_num, ?_, ?_⟩ <;> dsimp only <;> omega

theorem bandsL_fib (j : ℕ) (hj : 12 ≤ j) (z : ℕ) :
    ((bandsL j).map (fun p => cnt p.1 p.2.1 p.2.2 z)).sum ≤ 2 := by
  simp only [bandsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rcases lt_or_ge z (180000 * j) with h0 | h0
  · -- z below 180000 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (182749 * j) with h1 | h1
  · -- z below 182749 j
    have c0 := cnt_Y2 4 (45000 * j) (45687 * j) z (by norm_num) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (182750 * j) with h2 | h2
  · -- z below 182750 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (187496 * j) with h3 | h3
  · -- z below 187496 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_Y2 5 (36550 * j) (37499 * j) z (by norm_num) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (187500 * j) with h4 | h4
  · -- z below 187500 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (190375 * j) with h5 | h5
  · -- z below 190375 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_Y2 6 (31250 * j) (31729 * j) z (by norm_num) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (199996 * j) with h6 | h6
  · -- z below 199996 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_Y2 5 (38075 * j) (39999 * j) z (by norm_num) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (199998 * j) with h7 | h7
  · -- z below 199998 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (215992 * j) with h8 | h8
  · -- z below 215992 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_Y2 9 (22222 * j) (23999 * j) z (by norm_num) (by omega)
    omega
  rcases lt_or_ge z (218750 * j) with h9 | h9
  · -- z below 218750 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (219300 * j) with h10 | h10
  · -- z below 219300 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_X1 6 (31250 * j) (31729 * j) z (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (222104 * j) with h11 | h11
  · -- z below 222104 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_X1 5 (36550 * j) (37499 * j) z (by omega)
    have c2 := cnt_X1 6 (31250 * j) (31729 * j) z (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (222220 * j) with h12 | h12
  · -- z below 222220 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_X1 5 (36550 * j) (37499 * j) z (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  rcases lt_or_ge z (224995 * j) with h13 | h13
  · -- z below 224995 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_X1 5 (36550 * j) (37499 * j) z (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_X1 9 (22222 * j) (23999 * j) z (by omega)
    omega
  rcases lt_or_ge z (225000 * j) with h14 | h14
  · -- z below 225000 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_X1 9 (22222 * j) (23999 * j) z (by omega)
    omega
  rcases lt_or_ge z (228436 * j) with h15 | h15
  · -- z below 228436 j
    have c0 := cnt_X1 4 (45000 * j) (45687 * j) z (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_X1 9 (22222 * j) (23999 * j) z (by omega)
    omega
  rcases lt_or_ge z (228450 * j) with h16 | h16
  · -- z below 228450 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
    have c4 := cnt_X1 9 (22222 * j) (23999 * j) z (by omega)
    omega
  rcases lt_or_ge z (239991 * j) with h17 | h17
  · -- z below 239991 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_X1 5 (38075 * j) (39999 * j) z (by omega)
    have c4 := cnt_X1 9 (22222 * j) (23999 * j) z (by omega)
    omega
  rcases lt_or_ge z (239995 * j) with h18 | h18
  · -- z below 239995 j
    have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
    have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
    have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
    have c3 := cnt_X1 5 (38075 * j) (39999 * j) z (by omega)
    have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
    omega
  have c0 := cnt_zero 4 (45000 * j) (45687 * j) z (by omega) (by omega)
  have c1 := cnt_zero 5 (36550 * j) (37499 * j) z (by omega) (by omega)
  have c2 := cnt_zero 6 (31250 * j) (31729 * j) z (by omega) (by omega)
  have c3 := cnt_zero 5 (38075 * j) (39999 * j) z (by omega) (by omega)
  have c4 := cnt_zero 9 (22222 * j) (23999 * j) z (by omega) (by omega)
  omega

/-- The packing count: `5816 * j ≤ 2 * #holes` for `n' = 360000 * j`. -/
theorem design_count {a : ℕ → ℕ} {k j : ℕ} (H : Adm a k (360000 * j)) (hj : 12 ≤ j) :
    5816 * j ≤ 2 * (holes a k (180000 * j) (240000 * j + 1)).card := by
  have h := list_count H (t := 180000 * j) (θ := 240000 * j + 1) (D := 2) (bandsL j)
    (bandsL_ok j hj) (bandsL_fib j hj)
  have e : ((bandsL j).map (fun p => p.2.2 - p.2.1)).sum = 5816 * j := by
    simp only [bandsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  rw [e] at h
  exact h

/-- The crossing bound with the design: `720000 k ≤ 354184 (n + 360000) + 720000 sqrt(2θ)`, where
`θ = 240000 j + 1` and `j = ⌈n / 360000⌉` (the design is applied to `n' = 360000 j ≥ n`). -/
theorem adm_bound4 {a : ℕ → ℕ} {k n : ℕ} (H : Adm a k n) (hn : 4320000 ≤ n) :
    720000 * k ≤ 354184 * (n + 360000) +
      720000 * Nat.sqrt (2 * (240000 * ((n + 359999) / 360000) + 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, j = (n + 359999) / 360000 := ⟨_, rfl⟩
  rw [← hj]
  have hj1 : 12 ≤ j := by omega
  have hj2 : n ≤ 360000 * j := by omega
  have hj3 : 360000 * j ≤ n + 359999 := by omega
  have H' := H.mono_n hj2
  have h1 := main_count H' (t := 180000 * j) (θ := 240000 * j + 1) (by omega) (by omega)
    (by omega) (by omega)
  have h2 := design_count H' hj1
  omega

/-- **Upper bound, round 4.**  For the literal upstream `f`:
`720000 f(n) ≤ 354184 n + 1440000 sqrt n + 128010240000`.
In particular `f(n) ≤ (44273/90000) n + 2 sqrt n + O(1)`. -/
theorem f_le_upper4 (n : ℕ) :
    720000 * Erdos357.f n ≤ 354184 * n + 1440000 * Nat.sqrt n + 128010240000 := by
  have hbound : ∀ k, k ∈ {k : ℕ | ∃ a : Fin k → ℤ,
      Set.range a ⊆ Set.Icc 1 (n : ℤ) ∧ StrictMono a ∧ Erdos357.HasDistinctSums a} →
      720000 * k ≤ 354184 * n + 1440000 * Nat.sqrt n + 128010240000 := by
    rintro k ⟨a, hr, hm, ha⟩
    by_cases hn : 4320000 ≤ n
    · obtain ⟨b, hb⟩ := adm_of_int a hr hm ha
      have h := adm_bound4 hb hn
      have hs : Nat.sqrt (2 * (240000 * ((n + 359999) / 360000) + 1)) ≤ 2 * Nat.sqrt n + 700 := by
        have h1 := Nat.sqrt_le' (2 * (240000 * ((n + 359999) / 360000) + 1))
        have h2 := Nat.lt_succ_sqrt' n
        by_contra hcon
        push Not at hcon
        set s := Nat.sqrt (2 * (240000 * ((n + 359999) / 360000) + 1))
        set m := Nat.sqrt n
        have h3 : 3 * s ^ 2 ≤ 4 * n + 1440002 := by omega
        have h4 : (2 * m + 701) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (by omega) 2
        simp only [Nat.succ_eq_add_one] at h2
        nlinarith
      have := Nat.mul_le_mul_left 720000 hs
      omega
    · have h1 := Snively357.finite_int_length_le_half_add_sqrt a hr hm ha
      omega
  have hf : Erdos357.f n ≤ (354184 * n + 1440000 * Nat.sqrt n + 128010240000) / 720000 := by
    unfold Erdos357.f
    apply csSup_le'
    intro k hk
    have := hbound k hk
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have := (Nat.le_div_iff_mul_le (show 0 < 720000 by norm_num)).mp hf
  omega

/-- Real-valued form: `f(n) ≤ (44273/90000) n + 2 sqrt n + 177792`, `44273/90000 = 1/2 - 5816/720000`. -/
theorem f_le_real4 (n : ℕ) :
    (Erdos357.f n : ℝ) ≤ (44273 / 90000) * n + 2 * Real.sqrt n + 177792 := by
  have h := f_le_upper4 n
  have hm : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have h5 : (720000 : ℝ) * (Erdos357.f n : ℝ) ≤ 354184 * n + 1440000 * (Nat.sqrt n : ℝ) + 128010240000 := by
    exact_mod_cast h
  nlinarith

end Erdos357Upper

noncomputable def OMA.answer (n : ℕ) : ℝ :=
  (44273 / 90000) * n + 2 * Real.sqrt n + 177792

theorem OMA.pointwise (n : ℕ) : (Erdos357.f n : ℝ) ≤ OMA.answer n :=
  Erdos357Upper.f_le_real4 n

theorem OMA.solution : Erdos357.erdos_357.parts.ii.bigO_version_symm.answer = OMA.answer →
    type_of% @Erdos357.erdos_357.parts.ii.bigO_version_symm := by
  intro h
  rw [h]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards with n
  have hnonneg : 0 ≤ OMA.answer n := by unfold OMA.answer; positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using OMA.pointwise n

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
