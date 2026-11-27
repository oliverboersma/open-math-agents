import OMAStatements.S_mse_2030706
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Finset OMA.S_mse_2030706

namespace SuccessorSums

private def exponent : ℕ → ℕ
  | 0 => 2
  | k+1 => 4 + exponent k * 4

private def radius (k : ℕ) := 2^(exponent k)
private def hole (k : ℕ) := 2 * (radius k)^2
private def previous : ℕ → ℕ
  | 0 => 0
  | k+1 => hole k
private def kept : Set ℕ := {x | 0 < x ∧ ∀ k, x ≠ hole k}

private lemma radius_pos (k : ℕ) : 0 < radius k := by
  unfold radius
  positivity

private lemma radius_succ (k : ℕ) : radius (k+1) = 16*(radius k)^4 := by
  simp [radius, exponent, pow_add, pow_mul]

private lemma hole_mono : StrictMono hole := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hp := radius_pos k
  have hpow : radius k ≤ radius k ^ 4 := Nat.le_self_pow (by decide) _
  have hr : radius k < radius (k+1) := by rw [radius_succ]; omega
  unfold hole
  gcongr

private lemma gap {k x : ℕ} (hlo : previous k < x) (hhi : x < hole k) :
    x ∈ kept := by
  refine ⟨by omega, ?_⟩
  intro j h
  have hj : j < k := hole_mono.lt_iff_lt.mp (h ▸ hhi)
  cases k with
  | zero => omega
  | succ i =>
    have := hole_mono.monotone (show j ≤ i by omega)
    change hole i < x at hlo
    omega

private def tri (n : ℕ) := ∑ i ∈ range (n+1), i

private lemma double_tri (n : ℕ) : tri n * 2 = (n+1)*n := by
  simpa [tri] using sum_range_id_mul_two (n+1)

private lemma tri_mono : Monotone tri := fun _ _ h =>
  sum_le_sum_of_subset (range_mono (Nat.succ_le_succ h))

private lemma gap_size (k : ℕ) : tri (previous k) < radius k := by
  cases k with
  | zero => decide
  | succ i =>
    have h := double_tri (hole i)
    have hp := radius_pos i
    have hs := Nat.le_self_pow (a := (radius i)^2) (by decide : 2 ≠ 0)
    simp only [previous, radius_succ]
    unfold hole at h ⊢
    nlinarith

/-- Any divisor greater than one of a power of two is even. -/
private lemma even_factor {d e : ℕ} (h : d ∣ 2^e) (hd : 1 < d) : 2 ∣ d := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  cases j with
  | zero => simp_all
  | succ j => rw [hj, pow_succ]; exact dvd_mul_left _ _

/-- A block of at least two consecutive positive integers cannot sum to a power of two. -/
private lemma interval_ne_pow {l u : ℕ} (hl : 0 < l) (hu : l < u) (e : ℕ) :
    (∑ x ∈ Icc l u, x) ≠ 2^e := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  obtain ⟨d, hd⟩ : ∃ d, u = t+1+d+1 := ⟨u-(t+2), by omega⟩
  subst u
  intro heq
  have hi : Ico (t+1) (t+1+d+1+1) = Icc (t+1) (t+1+d+1) := by
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  have split := sum_range_add_sum_Ico (fun i : ℕ => i)
    (show t+1 ≤ t+1+d+1+1 by omega)
  rw [hi, heq] at split
  change tri t + 2^e = tri (t+1+d+1) at split
  have hprod : (d+2)*(2*t+d+3) = 2^(e+1) := by
    rw [pow_succ]
    nlinarith [double_tri t, double_tri (t+1+d+1)]
  have h1 := even_factor (hprod ▸ dvd_mul_right (d+2) (2*t+d+3)) (by omega)
  have h2 := even_factor (hprod ▸ dvd_mul_left (2*t+d+3) (d+2)) (by omega)
  omega

private lemma hole_power (k : ℕ) : hole k = 2^(exponent k * 2+1) := by
  rw [pow_succ, pow_mul]
  simp [hole, radius, mul_comm]

private lemma closed (l : ℕ) (hl : l ∈ kept) (u : ℕ) (hu : u ∈ kept) (hlu : l ≤ u) :
    (∑ x ∈ block kept l u, x) ∈ kept := by
  classical
  let s := block kept l u
  have mem_s (x : ℕ) : x ∈ s ↔ (l ≤ x ∧ x ≤ u) ∧ x ∈ kept := by
    simp [s, block]
  have hle : u ≤ ∑ x ∈ s, x :=
    single_le_sum (fun i _ => Nat.zero_le i) ((mem_s u).mpr ⟨⟨hlu, le_rfl⟩, hu⟩)
  refine ⟨lt_of_lt_of_le hu.1 hle, ?_⟩
  intro k hsum
  change (∑ x ∈ s, x) = hole k at hsum
  have hbound : u < hole k := lt_of_le_of_ne (hle.trans_eq hsum) (hu.2 k)
  by_cases hstart : previous k < l
  · have hs : s = Icc l u := by
      ext x
      rw [mem_s, mem_Icc]
      exact ⟨And.left, fun h => ⟨h, gap (hstart.trans_le h.1) (h.2.trans_lt hbound)⟩⟩
    rw [hs] at hsum
    rcases hlu.eq_or_lt with he | hlt
    · subst u
      simpa using (hl.2 k) (by simpa using hsum)
    · exact interval_ne_pow hl.1 hlt _ (hsum.trans (hole_power k))
  · have hs : s ⊆ range (u+1) := by
      intro x hx
      exact mem_range.mpr (by have := ((mem_s x).mp hx).1.2; omega)
    have lower : hole k ≤ tri u := hsum ▸ sum_le_sum_of_subset hs
    have cover : range (u+1) ⊆ range (previous k+1) ∪ s := by
      intro x hx
      have xu := mem_range.mp hx
      by_cases xp : x ≤ previous k
      · exact mem_union_left _ (mem_range.mpr (by omega))
      · exact mem_union_right _ ((mem_s x).mpr
          ⟨⟨by omega, by omega⟩, gap (k := k) (by omega) (by omega)⟩)
    have sc := sum_le_sum_of_subset (f := id) cover
    have su := sum_union_inter (s₁ := range (previous k+1)) (s₂ := s) (f := id)
    have upper : tri u ≤ tri (previous k) + hole k := by
      unfold tri
      simp only [id_eq] at sc su
      omega
    have hr := radius_pos k
    have hsmall := gap_size k
    by_cases hcut : u < 2*radius k
    · have ht := tri_mono (show u ≤ 2*radius k-1 by omega)
      have ht2 := double_tri (2*radius k-1)
      have ht3 : (2*radius k-1)+1 = 2*radius k := by omega
      rw [ht3] at ht2
      unfold hole at lower
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 2*radius k)]
    · have ht := tri_mono (show 2*radius k ≤ u by omega)
      unfold hole at upper
      nlinarith [double_tri (2*radius k)]

theorem counterexample : ¬ (type_of% @OMA.S_mse_2030706.main) := by
  intro h
  have odd_mem (N : ℕ) : 2*N+1 ∈ kept := by
    refine ⟨by omega, ?_⟩
    intro k
    unfold hole
    omega
  have hone : 1 ∈ kept := by simpa using odd_mem 0
  obtain ⟨N, hN⟩ := h kept (fun _ hx => hx.1)
    (fun m => ⟨_, odd_mem m, by omega⟩)
    (fun d hd => Nat.dvd_one.mp (hd 1 hone)) closed
  have hlarge : N < hole (N+1) := lt_of_lt_of_le (Nat.lt_succ_self _) (hole_mono.id_le _)
  exact (hN _ hlarge).2 _ rfl

end SuccessorSums

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2030706.main) :=
  SuccessorSums.counterexample
