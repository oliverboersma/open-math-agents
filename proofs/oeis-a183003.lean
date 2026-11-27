import OMAStatements.S_oeis_a183003
import Mathlib
open OMA.S_oeis_a183003

lemma stepA (k : ℕ) (hk : 1 ≤ k) :
    A072670 (k - 1) = ((k.divisors.filter (fun d => d * d ≤ k)).filter (fun d => 2 ≤ d)).card := by
  unfold A072670
  refine Finset.card_bij' (fun p _ => p.1 + 1) (fun d _ => (d - 1, k / d - 1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_filter, Nat.mem_divisors]
    have hk' : k = (p.1 + 1) * (p.2 + 1) := by
      have := hp.2.2; ring_nf; ring_nf at this; omega
    refine ⟨⟨⟨⟨p.2 + 1, hk'⟩, by omega⟩, ?_⟩, by omega⟩
    rw [hk']; exact Nat.mul_le_mul_left _ (by omega)
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨⟨e, he⟩, _⟩, hdd⟩, h2⟩ := hd
    have hdpos : 0 < d := by omega
    have hde : d ≤ e := by
      rw [he] at hdd; exact Nat.le_of_mul_le_mul_left hdd hdpos
    rw [he, Nat.mul_div_cancel_left _ hdpos]
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Nat.add_sub_cancel]
    have hx : (d' + 1) * (e' + 1) = d' * e' + d' + e' + 1 := by ring
    refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, by omega⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    have hk' : k = (p.1 + 1) * (p.2 + 1) := by
      have := hp.2.2; ring_nf; ring_nf at this; omega
    rw [hk', Nat.mul_div_cancel_left _ (by omega)]
    simp
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    simp only
    omega

lemma stepB (k : ℕ) (hk : 1 ≤ k) :
    k.divisors.card + k.divisors.card % 2 - 2
      = 2 * ((k.divisors.filter (fun d => d * d ≤ k)).filter (fun d => 2 ≤ d)).card := by
  set s := k.divisors with hs
  have hk0 : k ≠ 0 := by omega
  have h1 := Finset.card_filter_add_card_filter_not (s := s) (fun d => d * d ≤ k)
  have hL : s.filter (fun d => d * d ≤ k) = s.filter (fun d => d * d < k) ∪ s.filter (fun d => d * d = k) := by
    rw [← Finset.filter_or]; apply Finset.filter_congr; intro x _; omega
  have hdisj : Disjoint (s.filter (fun d => d * d < k)) (s.filter (fun d => d * d = k)) := by
    rw [Finset.disjoint_filter]; intro x _ h; omega
  have h2 := Finset.card_union_of_disjoint hdisj
  rw [← hL] at h2
  have hB : (s.filter (fun d => d * d = k)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    exact Nat.mul_self_inj.mp (hx.2.trans hy.2.symm)
  have hG : (s.filter (fun d => ¬ d * d ≤ k)).card = (s.filter (fun d => d * d < k)).card := by
    refine Finset.card_bij' (fun d _ => k / d) (fun d _ => k / d) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [hs, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨⟨e, he⟩, _⟩, hdd⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)
      rw [he, Nat.mul_div_cancel_left _ hdpos]
      refine ⟨⟨⟨d, by ring⟩, by omega⟩, ?_⟩
      rw [he] at hdd
      have : e < d := by
        by_contra hc; exact hdd (Nat.mul_le_mul_left _ (Nat.le_of_not_lt hc))
      exact Nat.mul_lt_mul_of_pos_right this (by rcases e with _ | e; simp at he; omega; omega)
    · intro d hd
      simp only [hs, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨⟨e, he⟩, _⟩, hdd⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)
      rw [he, Nat.mul_div_cancel_left _ hdpos]
      refine ⟨⟨⟨d, by ring⟩, by omega⟩, ?_⟩
      rw [he] at hdd
      have : d < e := by
        by_contra hc; exact absurd hdd (not_lt.mpr (Nat.mul_le_mul_left _ (Nat.le_of_not_lt hc)))
      intro hc
      exact absurd hc (not_le.mpr (Nat.mul_lt_mul_of_pos_right this (by omega)))
    · intro d hd
      simp only [hs, Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hk0
    · intro d hd
      simp only [hs, Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hk0
  have h3 := Finset.card_filter_add_card_filter_not
    (s := s.filter (fun d => d * d ≤ k)) (fun d => 2 ≤ d)
  have hO : ((s.filter (fun d => d * d ≤ k)).filter (fun d => ¬ 2 ≤ d)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext x
    simp only [hs, Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨hx, _⟩, _⟩, h⟩
      have : x ≠ 0 := by rintro rfl; simp at hx; omega
      omega
    · rintro rfl; exact ⟨⟨⟨one_dvd _, hk0⟩, by omega⟩, by omega⟩
  omega

lemma key (k : ℕ) (hk : 1 ≤ k) : A161840 k = 2 * A072670 (k - 1) := by
  rw [stepA k hk, A161840, stepB k hk]

lemma sumeq (n : ℕ) : A183002 n = 2 * ∑ m ∈ Finset.range n, A072670 m := by
  induction n with
  | zero => simp [A183002]
  | succ n ih =>
    unfold A183002 at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih, key (n + 1) (by omega), Finset.sum_range_succ]
    simp; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a183003.main := by
  intro n _
  rw [a, sumeq, Nat.mul_div_cancel_left _ (by norm_num)]
