import FormalConjectures.ErdosProblems.«385»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Sieve and interval endpoints for Erdős problem 385(ii) -/

-- Reduction Erdos385.erdos_385.parts.ii.R1
-- Credit: @marcusbuffett
-- The second-moment sieve is ported from Aafi Khan Malek, Erdos430Density.lean,
-- https://github.com/Aafimalek/erdos-385-almost-all/tree/b4097a3b184ad80aaae869beb1d144a8f8f9096b
-- We apply its bound to the explicit sieve obstruction itself and combine it
-- with a first-failure argument at endpoints of intervals supplied by composites.
/-
MIT License

Copyright (c) 2026 Aafi Khan Malek

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace OMA.R_Erdos385_erdos_385_parts_ii_R1

open Finset Filter Topology
open Erdos385 (F)

open scoped Classical

noncomputable section

theorem card_class_le (a : ℤ) (L m : ℕ) (hm : 0 < m) (j : ℤ) :
    #{x ∈ Ico a (a + L) | (m : ℤ) ∣ j - x} ≤ (L - 1) / m + 1 := by
  set A := (Ico a (a + L)).filter (fun x => (m : ℤ) ∣ j - x) with hA
  rcases A.eq_empty_or_nonempty with h | hne
  · rw [h]; simp
  set c := A.min' hne
  have hc : c ∈ A := A.min'_mem hne
  have hsub : A ⊆ (range ((L - 1) / m + 1)).image (fun t : ℕ => c + (t : ℤ) * m) := by
    intro x hx
    have hcx : c ≤ x := A.min'_le x hx
    simp only [hA, mem_filter, mem_Ico] at hx hc
    obtain ⟨⟨hax, hxL⟩, hdx⟩ := hx
    obtain ⟨⟨hac, hcL⟩, hdc⟩ := hc
    obtain ⟨t, ht⟩ : (m : ℤ) ∣ x - c := by
      have := dvd_sub hdc hdx
      rwa [show j - c - (j - x) = x - c by ring] at this
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    have ht0 : 0 ≤ t := by nlinarith
    refine mem_image.mpr ⟨t.toNat, ?_, ?_⟩
    · rw [mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hm]
      have hle : (t.toNat : ℤ) * m ≤ (L : ℤ) - 1 := by
        rw [Int.toNat_of_nonneg ht0]; nlinarith
      omega
    · rw [Int.toNat_of_nonneg ht0]; linarith
  calc #A ≤ #((range ((L - 1) / m + 1)).image (fun t : ℕ => c + (t : ℤ) * m)) :=
        card_le_card hsub
    _ ≤ #(range ((L - 1) / m + 1)) := card_image_le
    _ = (L - 1) / m + 1 := card_range _

theorem card_partners_le (a : ℤ) (L m : ℕ) (hm : 0 < m) (j : ℤ) (hj : j ∈ Ico a (a + L)) :
    (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ) ≤ ((L : ℝ) - 1) / m := by
  have hset : (Ico a (a + L)).filter (fun j' => j' ≠ j ∧ (m : ℤ) ∣ j - j') =
      ((Ico a (a + L)).filter (fun x => (m : ℤ) ∣ j - x)).erase j := by
    ext x; simp [mem_erase, and_left_comm]
  have hmem : j ∈ (Ico a (a + L)).filter (fun x => (m : ℤ) ∣ j - x) := by
    simp [hj]
  have hL : 1 ≤ L := by
    rw [mem_Ico] at hj; omega
  have hnat : #{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} ≤ (L - 1) / m := by
    rw [hset, card_erase_of_mem hmem]
    exact Nat.sub_le_iff_le_add.mpr (card_class_le a L m hm j)
  calc (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ)
      ≤ (((L - 1) / m : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ ((L - 1 : ℕ) : ℝ) / m := Nat.cast_div_le
    _ = ((L : ℝ) - 1) / m := by rw [Nat.cast_sub hL]; simp

theorem sum_partners_le (a : ℤ) (L m : ℕ) (hm : 0 < m) :
    ∑ j ∈ Ico a (a + L), (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ) ≤
      (L : ℝ) * ((L : ℝ) - 1) / m := by
  calc ∑ j ∈ Ico a (a + L), (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ (m : ℤ) ∣ j - j'} : ℝ)
      ≤ ∑ _j ∈ Ico a (a + L), ((L : ℝ) - 1) / m :=
        sum_le_sum fun j hj => card_partners_le a L m hm j hj
    _ = (L : ℝ) * ((L : ℝ) - 1) / m := by
        rw [sum_const, Int.card_Ico, show a + L - a = (L : ℤ) by ring, Int.toNat_natCast,
          nsmul_eq_mul]
        ring

theorem prod_dvd_of_forall_dvd {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) {d : ℤ}
    (h : ∀ q ∈ s, (q : ℤ) ∣ d) : ((∏ q ∈ s, q : ℕ) : ℤ) ∣ d := by
  push_cast
  apply Finset.prod_dvd_of_coprime _ h
  intro q hq r hr hqr
  exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hs q hq) (hs r hr)).mpr hqr)

private theorem value_le {m n : ℕ} (hm : m < n) (hc : m.Composite) : m + m.minFac ≤ F n := by
  unfold F
  refine le_csSup ?_ ⟨m, hm, hc, rfl⟩
  refine ⟨2 * n, ?_⟩
  rintro _ ⟨k, hk, hkc, rfl⟩
  have h := Nat.minFac_le (show 0 < k by have := hkc.1; omega)
  omega

theorem prod_one_sub_inv_ge (P : Finset ℕ) (hP : ∀ q ∈ P, 2 ≤ q) :
    1 / ((#P : ℝ) + 1) ≤ ∏ q ∈ P, (1 - 1 / (q : ℝ)) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs2 : ∀ q ∈ s, 2 ≤ q := fun q hq => hP q (mem_insert_of_mem hq)
    have ha2 : 2 ≤ a := hP a (mem_insert_self a s)
    have hcard : #s + 2 ≤ a := by
      have hsub : s ⊆ Ico 2 a := fun q hq => mem_Ico.mpr ⟨hs2 q hq, hlt q hq⟩
      have := card_le_card hsub
      rw [Nat.card_Ico] at this
      omega
    rw [prod_insert has, card_insert_of_notMem has]
    have ih' := ih hs2
    have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hfac : ((#s : ℝ) + 1) / (#s + 2) ≤ 1 - 1 / (a : ℝ) := by
      have hca : ((#s : ℝ) + 2) ≤ a := by exact_mod_cast hcard
      rw [div_le_iff₀ (by positivity), sub_mul, one_div, inv_mul_eq_div]
      have : ((#s : ℝ) + 2) / a ≤ 1 := (div_le_one hapos).mpr hca
      nlinarith
    calc 1 / ((((#s + 1 : ℕ)) : ℝ) + 1) = ((#s : ℝ) + 1) / (#s + 2) * (1 / ((#s : ℝ) + 1)) := by
          push_cast; field_simp; ring
      _ ≤ (1 - 1 / (a : ℝ)) * ∏ q ∈ s, (1 - 1 / (q : ℝ)) :=
          mul_le_mul hfac ih' (by positivity) (by
            have : (0 : ℝ) < 1 / a := by positivity
            have : 1 / (a : ℝ) ≤ 1 / 2 := by
              apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast ha2
            linarith)

theorem prod_div_prod_sub_one_le (z : ℕ) :
    ((∏ q ∈ Nat.primesLE z, q : ℕ) : ℝ) / ((∏ q ∈ Nat.primesLE z, (q - 1) : ℕ) : ℝ) ≤
      (Nat.primeCounting z : ℝ) + 1 := by
  have hP : ∀ q ∈ Nat.primesLE z, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  have hratio : ((∏ q ∈ Nat.primesLE z, (q - 1) : ℕ) : ℝ) / ((∏ q ∈ Nat.primesLE z, q : ℕ) : ℝ) =
      ∏ q ∈ Nat.primesLE z, (1 - 1 / (q : ℝ)) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
    refine prod_congr rfl fun q hq => ?_
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hq).ne_zero
    rw [Nat.cast_sub (hP q hq).one_lt.le, Nat.cast_one]
    field_simp
  have hge := prod_one_sub_inv_ge (Nat.primesLE z) fun q hq => (hP q hq).two_le
  rw [← hratio, Nat.primesLE_card_eq_primeCounting] at hge
  have hQpos : (0 : ℝ) < ((∏ q ∈ Nat.primesLE z, q : ℕ) : ℝ) := by
    exact_mod_cast prod_pos fun q hq => (hP q hq).pos
  have hNpos : (0 : ℝ) < ((∏ q ∈ Nat.primesLE z, (q - 1) : ℕ) : ℝ) := by
    exact_mod_cast prod_pos fun q hq => Nat.sub_pos_of_lt (hP q hq).one_lt
  rw [div_le_iff₀ hNpos]
  rw [div_le_div_iff₀ (by positivity) hQpos] at hge
  linarith

theorem card_sub_prime_le (X k : ℕ) :
    #{n ∈ range X | (n - k).Prime} ≤ Nat.primeCounting X := by
  calc #{n ∈ range X | (n - k).Prime} ≤ #{p ∈ range X | p.Prime} := by
        refine card_le_card_of_injOn (fun n => n - k) ?_ ?_
        · intro n hn
          rw [mem_coe, mem_filter, mem_range] at hn
          rw [mem_coe, mem_filter, mem_range]
          exact ⟨lt_of_le_of_lt (Nat.sub_le n k) hn.1, hn.2⟩
        · intro n hn n' hn' h
          rw [mem_coe, mem_filter] at hn hn'
          have h1 := hn.2.two_le
          have h2 := hn'.2.two_le
          simp only at h
          omega
    _ = Nat.primeCounting' X := by
        rw [← Nat.primesBelow_card_eq_primeCounting']; rfl
    _ ≤ Nat.primeCounting X := Nat.monotone_primeCounting' (Nat.le_succ X)

theorem tendsto_primeCounting_div :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (√(n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun n : ℕ => Real.log 4 / Real.log (√(n : ℝ)) + 1 / √(n : ℝ))
      atTop (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := Real.log 4)).div_atTop hlog
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hsqrt
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hbound
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hpi := Chebyshev.pi_le_log4_mul_div hn'
  rw [Nat.floor_natCast] at hpi
  have hnpos : (0 : ℝ) < n := by linarith
  have hsq : √(n : ℝ) / n = 1 / √(n : ℝ) := by
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, Real.mul_self_sqrt hnpos.le]
  calc (Nat.primeCounting n : ℝ) / n ≤ (Real.log 4 * n / Real.log √(n : ℝ) + √(n : ℝ)) / n :=
        div_le_div_of_nonneg_right hpi hnpos.le
    _ = Real.log 4 / Real.log (√(n : ℝ)) + 1 / √(n : ℝ) := by
        rw [add_div, hsq]; congr 1; field_simp

set_option maxHeartbeats 3200000 in
/-- Package the elementary sieve obstruction. Its second-moment estimate proves
that its natural density is zero, and every actual failure is among its members. -/
private theorem sieve_certificate :
    ∃ E : ℕ → ℕ → Prop, (∀ T, Tendsto (fun X : ℕ => (#{n ∈ range X | E T n} : ℝ) / X) atTop (𝓝 0)) ∧
      (∀ T n, F n ≤ n + T → E T n) ∧ (∀ T n, E T n ↔ (∀ J : ℕ, 1 ≤ J → 2 * J + 2 ≤ n →
      (∀ k ∈ Icc J (2 * J), ∃ p ∈ Nat.primesLE (2 * J + T), (n : ZMod p) = (k : ZMod p)) ∨
      ∃ k ∈ Icc J (2 * J), (n - k).Prime)) := by
  classical
  let pairWeight (P : Finset ℕ) (d : ℤ) : ℝ :=
    ∏ q ∈ P, ((if (q : ℤ) ∣ d then 1 else 0) + ((q : ℝ) - 2))
  have sum_pairWeight_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (a : ℤ) (L : ℕ) :
      ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j), pairWeight P (j - j') ≤
        (L : ℝ) * ((L : ℝ) - 1) * ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) := by
    classical
    have hq2 : ∀ q ∈ P, (0 : ℝ) ≤ (q : ℝ) - 2 := fun q hq => by
      have := (hP q hq).two_le
      have : (2 : ℝ) ≤ q := by exact_mod_cast this
      linarith
    -- Expand each weight over subsets of `P`.
    have hexp : ∀ d : ℤ, pairWeight P d ≤
        ∑ s ∈ P.powerset, (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ d then 1 else 0) *
          ∏ q ∈ P \ s, ((q : ℝ) - 2) := by
      intro d
      dsimp only [pairWeight]
      rw [prod_add]
      refine sum_le_sum fun s hs => ?_
      have hsP : s ⊆ P := mem_powerset.mp hs
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun q hq => hq2 q (mem_sdiff.mp hq).1)
      by_cases hall : ∀ q ∈ s, (q : ℤ) ∣ d
      · rw [if_pos (prod_dvd_of_forall_dvd (fun q hq => hP q (hsP hq)) hall)]
        rw [prod_congr rfl fun q hq => if_pos (hall q hq)]
        simp
      · push Not at hall
        obtain ⟨q, hq, hqd⟩ := hall
        rw [prod_eq_zero hq (if_neg hqd)]
        split_ifs <;> norm_num
    have hpos : ∀ s ∈ P.powerset, 0 < ∏ q ∈ s, q := fun s hs =>
      prod_pos fun q hq => (hP q (mem_powerset.mp hs hq)).pos
    calc ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j), pairWeight P (j - j')
        ≤ ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j),
            ∑ s ∈ P.powerset, (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j' then 1 else 0) *
              ∏ q ∈ P \ s, ((q : ℝ) - 2) :=
          sum_le_sum fun j _ => sum_le_sum fun j' _ => hexp _
      _ = ∑ j ∈ Ico a (a + L), ∑ s ∈ P.powerset, ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j),
            (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j' then 1 else 0) * ∏ q ∈ P \ s, ((q : ℝ) - 2) :=
          sum_congr rfl fun j _ => sum_comm
      _ = ∑ s ∈ P.powerset, ∑ j ∈ Ico a (a + L), ∑ j' ∈ (Ico a (a + L)).filter (· ≠ j),
            (if ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j' then 1 else 0) * ∏ q ∈ P \ s, ((q : ℝ) - 2) :=
          sum_comm
      _ = ∑ s ∈ P.powerset, (∏ q ∈ P \ s, ((q : ℝ) - 2)) *
            ∑ j ∈ Ico a (a + L),
              (#{j' ∈ Ico a (a + L) | j' ≠ j ∧ ((∏ q ∈ s, q : ℕ) : ℤ) ∣ j - j'} : ℝ) := by
          refine sum_congr rfl fun s _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [← filter_filter, ← sum_boole, mul_sum]
          exact sum_congr rfl fun j' _ => mul_comm _ _
      _ ≤ ∑ s ∈ P.powerset, (∏ q ∈ P \ s, ((q : ℝ) - 2)) *
            ((L : ℝ) * ((L : ℝ) - 1) / (∏ q ∈ s, q : ℕ)) := by
          refine sum_le_sum fun s hs => mul_le_mul_of_nonneg_left
            (sum_partners_le a L _ (hpos s hs)) (prod_nonneg fun q hq => hq2 q (mem_sdiff.mp hq).1)
      _ = (L : ℝ) * ((L : ℝ) - 1) * ∑ s ∈ P.powerset,
            (∏ q ∈ s, (1 / (q : ℝ))) * ∏ q ∈ P \ s, ((q : ℝ) - 2) := by
          rw [mul_sum]
          refine sum_congr rfl fun s _ => ?_
          push_cast
          rw [prod_div_distrib, prod_const_one]
          ring
      _ = (L : ℝ) * ((L : ℝ) - 1) * ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) := by
          rw [← prod_add]
          congr 1
          refine prod_congr rfl fun q hq => ?_
          have : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hq).ne_zero
          field_simp
          ring
  let Omega (P : Finset ℕ) := (q : P) → ZMod q
  let Avoids (P : Finset ℕ) (ω : Omega P) (j : ℤ) : Prop := ∀ q : P, ω q ≠ (j : ZMod q)
  let S (P : Finset ℕ) (I : Finset ℤ) (ω : Omega P) : ℕ := #{j ∈ I | Avoids P ω j}
  have card_omega (P : Finset ℕ) [hP0 : ∀ q : P, NeZero (q : ℕ)] : Fintype.card (Omega P) = ∏ q ∈ P, q := by
    rw [Fintype.card_pi, ← prod_coe_sort P]
    exact prod_congr rfl fun q _ => ZMod.card q
  have card_avoids (P : Finset ℕ) [hP0 : ∀ q : P, NeZero (q : ℕ)] (j : ℤ) :
      #{ω : Omega P | Avoids P ω j} = ∏ q ∈ P, (q - 1) := by
    have : (univ.filter fun ω : Omega P => Avoids P ω j) =
        Fintype.piFinset fun q : P => univ.erase (j : ZMod q) := by
      ext ω; dsimp only [Omega] at ω; simp [Avoids, Omega, Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset, ← prod_coe_sort P]
    refine prod_congr rfl fun q _ => ?_
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have card_avoids_pair (P : Finset ℕ) [hP0 : ∀ q : P, NeZero (q : ℕ)] (j j' : ℤ) (hP : ∀ q ∈ P, q.Prime) :
      (#{ω : Omega P | Avoids P ω j ∧ Avoids P ω j'} : ℝ) = pairWeight P (j - j') := by
    have : (univ.filter fun ω : Omega P => Avoids P ω j ∧ Avoids P ω j') =
        Fintype.piFinset fun q : P => (univ.erase (j : ZMod q)).erase (j' : ZMod q) := by
      ext ω; dsimp only [Omega] at ω; simp [Avoids, Omega, Fintype.mem_piFinset, forall_and, and_comm]
    dsimp only [pairWeight]
    rw [this, Fintype.card_piFinset, ← prod_coe_sort P, Nat.cast_prod]
    refine prod_congr rfl fun q _ => ?_
    have hq2 := (hP q q.2).two_le
    by_cases h : (j' : ZMod q) = (j : ZMod q)
    · have hd : ((q : ℕ) : ℤ) ∣ j - j' := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
      rw [if_pos hd, h, erase_eq_of_notMem (notMem_erase _ _), card_erase_of_mem (mem_univ _),
        card_univ, ZMod.card, Nat.cast_sub (by omega)]
      ring
    · have hd : ¬ ((q : ℕ) : ℤ) ∣ j - j' := fun hd =>
        h ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hd)
      rw [if_neg hd, card_erase_of_mem (mem_erase.mpr ⟨h, mem_univ _⟩),
        card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
      push_cast [Nat.cast_sub (show 1 ≤ (q : ℕ) by omega),
        Nat.cast_sub (show 1 ≤ (q : ℕ) - 1 by omega)]
      ring
  have card_S_eq_zero_le (P : Finset ℕ) [hP0 : ∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime) (a : ℤ) (L : ℕ) (hL : 1 ≤ L) :
      (#{ω : Omega P | S P (Ico a (a + L)) ω = 0} : ℝ) ≤
        ((∏ q ∈ P, q : ℕ) : ℝ) ^ 2 / ((L : ℝ) * (∏ q ∈ P, (q - 1) : ℕ)) := by
    classical
    set I := Ico a (a + L) with hI
    set Q : ℝ := ((∏ q ∈ P, q : ℕ) : ℝ) with hQ
    set N : ℝ := ((∏ q ∈ P, (q - 1) : ℕ) : ℝ) with hN
    have hQpos : 0 < Q := by
      rw [hQ]; exact_mod_cast prod_pos fun q hq => (hP q hq).pos
    have hNpos : 0 < N := by
      rw [hN]; exact_mod_cast prod_pos fun q hq => Nat.sub_pos_of_lt (hP q hq).one_lt
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hcardI : #I = L := by
      rw [hI, Int.card_Ico, show a + L - a = (L : ℤ) by ring, Int.toNat_natCast]
    have hcardΩ : (Fintype.card (Omega P) : ℝ) = Q := by rw [card_omega]
    -- `S` as a sum of indicators.
    have hSsum : ∀ ω : Omega P, (S P I ω : ℝ) = ∑ j ∈ I, (if Avoids P ω j then (1 : ℝ) else 0) :=
      fun ω => by dsimp only [S]; rw [sum_boole]
    -- First moment.
    have hS1 : ∑ ω : Omega P, (S P I ω : ℝ) = L * N := by
      simp_rw [hSsum]
      rw [sum_comm]
      rw [sum_congr rfl fun j _ => by rw [sum_boole, card_avoids]]
      rw [sum_const, hcardI, nsmul_eq_mul]
    -- Second moment.
    have hS2 : ∑ ω : Omega P, (S P I ω : ℝ) ^ 2 ≤
        L * N + L * (L - 1) * ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) := by
      have hexpand : ∀ ω : Omega P, (S P I ω : ℝ) ^ 2 =
          ∑ j ∈ I, ∑ j' ∈ I, (if Avoids P ω j ∧ Avoids P ω j' then (1 : ℝ) else 0) := by
        intro ω
        rw [hSsum, sq, sum_mul_sum]
        refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
        by_cases h1 : Avoids P ω j <;> by_cases h2 : Avoids P ω j' <;> simp [h1, h2]
      have hswap : ∑ ω : Omega P, (S P I ω : ℝ) ^ 2 =
          ∑ j ∈ I, ∑ j' ∈ I, ∑ ω : Omega P,
            (if Avoids P ω j ∧ Avoids P ω j' then (1 : ℝ) else 0) := by
        simp_rw [hexpand]
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_comm
      have hpair : ∀ j ∈ I, ∑ j' ∈ I, ∑ ω : Omega P,
          (if Avoids P ω j ∧ Avoids P ω j' then (1 : ℝ) else 0) =
          N + ∑ j' ∈ I.filter (· ≠ j), pairWeight P (j - j') := by
        intro j hj
        rw [← add_sum_erase _ _ hj, ← filter_ne' I j]
        congr 1
        · rw [sum_boole]
          simp only [and_self]
          rw [card_avoids]
        · refine sum_congr rfl fun j' _ => ?_
          rw [sum_boole]
          exact card_avoids_pair P j j' hP
      rw [hswap, sum_congr rfl hpair, sum_add_distrib, sum_const, hcardI, nsmul_eq_mul]
      have := sum_pairWeight_le P hP a L
      rw [← hI] at this
      linarith
    -- The identity `∏ (q - 1) ^ 2 / q = N ^ 2 / Q`.
    have hNprod : N = ∏ q ∈ P, ((q : ℝ) - 1) := by
      rw [hN, Nat.cast_prod]
      exact prod_congr rfl fun q hq => by rw [Nat.cast_sub (hP q hq).one_lt.le, Nat.cast_one]
    have hQprod : Q = ∏ q ∈ P, (q : ℝ) := by rw [hQ, Nat.cast_prod]
    have hprod : ∏ q ∈ P, (((q : ℝ) - 1) ^ 2 / q) = N ^ 2 / Q := by
      rw [hNprod, hQprod, prod_div_distrib, prod_pow]
    set μ : ℝ := L * N / Q with hμ
    have hμpos : 0 < μ := by positivity
    -- Chebyshev: each residue choice with `S = 0` contributes `μ ^ 2` to the variance.
    have hvar : ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 ≤ L * N := by
      have hterm : ∀ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 =
          (S P I ω : ℝ) ^ 2 - 2 * μ * (S P I ω : ℝ) + μ ^ 2 := fun ω => by ring
      have hexp : ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 =
          ∑ ω : Omega P, (S P I ω : ℝ) ^ 2 - 2 * μ * ∑ ω : Omega P, (S P I ω : ℝ) + Q * μ ^ 2 := by
        rw [sum_congr rfl fun ω _ => hterm ω, sum_add_distrib, sum_sub_distrib, ← mul_sum,
          sum_const, card_univ, nsmul_eq_mul, hcardΩ]
      rw [hexp, hS1]
      rw [hprod] at hS2
      have hNQ : 0 ≤ (L : ℝ) * N ^ 2 / Q := by positivity
      have hid : (L : ℝ) * (L - 1) * (N ^ 2 / Q) - 2 * μ * (L * N) + Q * μ ^ 2 =
          - ((L : ℝ) * N ^ 2 / Q) := by
        rw [hμ]; field_simp; ring
      linarith
    have hzero : (#{ω : Omega P | S P I ω = 0} : ℝ) * μ ^ 2 ≤
        ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 := by
      calc (#{ω : Omega P | S P I ω = 0} : ℝ) * μ ^ 2
          = ∑ ω ∈ univ.filter (fun ω : Omega P => S P I ω = 0), ((S P I ω : ℝ) - μ) ^ 2 := by
            rw [sum_congr rfl fun ω hω => show ((S P I ω : ℝ) - μ) ^ 2 = μ ^ 2 by
              rw [(mem_filter.mp hω).2, Nat.cast_zero]; ring]
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ ω : Omega P, ((S P I ω : ℝ) - μ) ^ 2 :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
    have hfinal : (#{ω : Omega P | S P I ω = 0} : ℝ) * μ ^ 2 ≤ L * N := hzero.trans hvar
    rw [le_div_iff₀ (by positivity)]
    set c : ℝ := (#{ω : Omega P | S P I ω = 0} : ℝ) with hc
    have hLN : 0 < (L : ℝ) * N := mul_pos hLpos hNpos
    have key : c * (L * N) * (L * N) ≤ Q ^ 2 * (L * N) := by
      have e : c * μ ^ 2 * Q ^ 2 = c * (L * N) * (L * N) := by rw [hμ]; field_simp
      have := mul_le_mul_of_nonneg_right hfinal (sq_nonneg Q)
      nlinarith [e]
    exact le_of_mul_le_mul_right key hLN
  let res (P : Finset ℕ) (n : ℕ) : Omega P := fun q => (n : ZMod q)
  have res_injOn (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (b : ℕ) :
      Set.InjOn (res P) (Ico b (b + ∏ q ∈ P, q) : Set ℕ) := by
    intro n hn n' hn' h
    simp only [coe_Ico, Set.mem_Ico] at hn hn'
    have hdvd : ∀ q ∈ P, (q : ℤ) ∣ (n : ℤ) - n' := by
      intro q hq
      have h1 := congrFun h ⟨q, hq⟩
      simp only [res] at h1
      have h2 : ((n' : ℤ) : ZMod q) = ((n : ℤ) : ZMod q) := by exact_mod_cast h1.symm
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
    have hprod := prod_dvd_of_forall_dvd hP (fun q hq => hdvd q hq)
    have hlt : |(n : ℤ) - n'| < ((∏ q ∈ P, q : ℕ) : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hprod hlt
    omega
  have card_res_le (P : Finset ℕ) [hP0 : ∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime) (X : ℕ) (p : Omega P → Prop) [DecidablePred p] :
      #{n ∈ range X | p (res P n)} ≤ (X / ∏ q ∈ P, q + 1) * #{ω : Omega P | p ω} := by
    classical
    set Q := ∏ q ∈ P, q with hQ
    have hQpos : 0 < Q := prod_pos fun q hq => (hP q hq).pos
    have hsub : (range X).filter (fun n => p (res P n)) ⊆
        (range (X / Q + 1)).biUnion fun b => (Ico (b * Q) (b * Q + Q)).filter fun n => p (res P n) := by
      intro n hn
      rw [mem_filter, mem_range] at hn
      rw [mem_biUnion]
      refine ⟨n / Q, ?_, ?_⟩
      · rw [mem_range, Nat.lt_succ_iff]
        exact Nat.div_le_div_right hn.1.le
      · rw [mem_filter, mem_Ico]
        refine ⟨⟨Nat.div_mul_le_self n Q, ?_⟩, hn.2⟩
        have := Nat.lt_div_mul_add hQpos (a := n)
        linarith
    calc #((range X).filter fun n => p (res P n))
        ≤ #((range (X / Q + 1)).biUnion fun b =>
            (Ico (b * Q) (b * Q + Q)).filter fun n => p (res P n)) := card_le_card hsub
      _ ≤ ∑ b ∈ range (X / Q + 1), #((Ico (b * Q) (b * Q + Q)).filter fun n => p (res P n)) :=
          card_biUnion_le
      _ ≤ ∑ _b ∈ range (X / Q + 1), #{ω : Omega P | p ω} := by
          refine sum_le_sum fun b _ => card_le_card_of_injOn (res P) ?_ ?_
          · intro n hn
            rw [mem_coe, mem_filter] at hn
            rw [mem_coe, mem_filter]
            exact ⟨mem_univ _, hn.2⟩
          · intro n hn n' hn' h
            rw [mem_coe, mem_filter] at hn hn'
            exact res_injOn P hP (b * Q) (by simpa using hn.1) (by simpa using hn'.1) h
      _ = (X / Q + 1) * #{ω : Omega P | p ω} := by rw [sum_const, card_range, smul_eq_mul]
  let primesLE_neZero (z : ℕ) : ∀ q : Nat.primesLE z, NeZero (q : ℕ) :=
    fun q => ⟨(Nat.prime_of_mem_primesLE q.2).ne_zero⟩
  let Screened (T n : ℕ) : Prop :=
    ∀ J : ℕ, 1 ≤ J → 2 * J + 2 ≤ n →
      S (Nat.primesLE (2 * J + T)) (Ico (J : ℤ) (J + (J + 1 : ℕ))) (res _ n) = 0 ∨
        ∃ k ∈ Icc J (2 * J), (n - k).Prime
  have shift_witness {J T n : ℕ} (hJ : 1 ≤ J) (hn : 2 * J + 2 ≤ n) (hF : F n ≤ n + T) :
      S (Nat.primesLE (2 * J + T)) (Ico (J : ℤ) (J + (J + 1 : ℕ))) (res _ n) = 0 ∨
        ∃ k ∈ Icc J (2 * J), (n - k).Prime := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hS, hprime⟩ := hcon
    obtain ⟨j, hj⟩ := card_pos.mp (Nat.pos_of_ne_zero hS)
    rw [mem_filter, mem_Ico] at hj
    obtain ⟨⟨hjJ, hj2⟩, havoid⟩ := hj
    set k := j.toNat with hk
    have hkj : (k : ℤ) = j := Int.toNat_of_nonneg (by omega)
    have hkJ : k ∈ Icc J (2 * J) := by rw [mem_Icc]; omega
    set m := n - k with hm
    have hm2 : 2 ≤ m := by omega
    have hmp : ¬ m.Prime := hprime k hkJ
    -- No prime up to `2J + T` divides `m`.
    have hnodiv : ∀ q ∈ Nat.primesLE (2 * J + T), ¬ q ∣ m := by
      intro q hq hqm
      apply havoid ⟨q, hq⟩
      have hnk : n = m + k := by omega
      show ((n : ℕ) : ZMod q) = ((j : ℤ) : ZMod q)
      rw [← hkj, hnk, Nat.cast_add, (ZMod.natCast_eq_zero_iff m q).mpr hqm, zero_add]
      simp
    have hmin : 2 * J + T < m.minFac := by
      by_contra hle
      push Not at hle
      exact hnodiv _ (Nat.mem_primesLE.mpr ⟨hle, Nat.minFac_prime (by omega)⟩) (Nat.minFac_dvd m)
    have hval := value_le (n := n) (m := m) (by omega) ⟨by omega, hmp⟩
    omega
  have card_screened_le (T J X : ℕ) (hJ : 1 ≤ J) :
      (#{n ∈ range X | Screened T n} : ℝ) ≤
        ((X : ℝ) + (∏ q ∈ Nat.primesLE (2 * J + T), q : ℕ)) *
            ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) +
          (J + 1) * Nat.primeCounting X + (2 * J + 2) := by
    classical
    set z := 2 * J + T with hz
    set P := Nat.primesLE z with hPdef
    have hP : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
    set I : Finset ℤ := Ico (J : ℤ) (J + (J + 1 : ℕ)) with hI
    set Q : ℕ := ∏ q ∈ P, q with hQ
    set N : ℕ := ∏ q ∈ P, (q - 1) with hN
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast prod_pos fun q hq => (hP q hq).pos
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast prod_pos fun q hq => Nat.sub_pos_of_lt (hP q hq).one_lt
    -- Split `{n < X : Screened T n}` into three parts.
    have hsplit : (range X).filter (fun n => Screened T n) ⊆
        ((range X).filter fun n => S P I (res P n) = 0) ∪
          (((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) ∪
            range (2 * J + 2)) := by
      intro n hn
      rw [mem_filter, mem_range] at hn
      by_cases hsmall : n < 2 * J + 2
      · exact mem_union_right _ (mem_union_right _ (mem_range.mpr hsmall))
      · rcases hn.2 J hJ (by omega) with h | ⟨k, hk, hkp⟩
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr hn.1, h⟩)
        · exact mem_union_right _ (mem_union_left _
            (mem_biUnion.mpr ⟨k, hk, mem_filter.mpr ⟨mem_range.mpr hn.1, hkp⟩⟩))
    have hA : (#((range X).filter fun n => S P I (res P n) = 0) : ℝ) ≤
        ((X : ℝ) + Q) * ((Nat.primeCounting z : ℝ) + 1) / (J + 1) := by
      have h1 := card_res_le P hP X (fun ω => S P I ω = 0)
      have h2 := card_S_eq_zero_le P hP (J : ℤ) (J + 1) (by omega)
      have h3 := prod_div_prod_sub_one_le z
      rw [← hPdef] at h3
      have hdiv : ((X / Q : ℕ) : ℝ) ≤ (X : ℝ) / Q := Nat.cast_div_le
      calc (#((range X).filter fun n => S P I (res P n) = 0) : ℝ)
          ≤ (((X / Q + 1) * #{ω : Omega P | S P I ω = 0} : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (((X / Q : ℕ) : ℝ) + 1) * (#{ω : Omega P | S P I ω = 0} : ℝ) := by push_cast; ring
        _ ≤ ((X : ℝ) / Q + 1) * ((Q : ℝ) ^ 2 / (((J + 1 : ℕ) : ℝ) * N)) := by
            apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
            exact h2
        _ = ((X : ℝ) + Q) * ((Q : ℝ) / N) / (J + 1) := by
            push_cast; field_simp
        _ ≤ ((X : ℝ) + Q) * ((Nat.primeCounting z : ℝ) + 1) / (J + 1) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hB : (#((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) : ℝ) ≤
        (J + 1) * Nat.primeCounting X := by
      have := card_biUnion_le (s := Icc J (2 * J))
        (t := fun k => (range X).filter fun n => (n - k).Prime)
      have h2 : ∑ k ∈ Icc J (2 * J), #((range X).filter fun n => (n - k).Prime) ≤
          ∑ _k ∈ Icc J (2 * J), Nat.primeCounting X :=
        sum_le_sum fun k _ => card_sub_prime_le X k
      rw [sum_const, Nat.card_Icc, smul_eq_mul] at h2
      have h3 : 2 * J + 1 - J = J + 1 := by omega
      rw [h3] at h2
      exact_mod_cast this.trans h2
    have hC : (#(range (2 * J + 2)) : ℝ) = 2 * J + 2 := by rw [card_range]; push_cast; ring
    calc (#{n ∈ range X | Screened T n} : ℝ)
        ≤ (#(((range X).filter fun n => S P I (res P n) = 0) ∪
            (((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) ∪
              range (2 * J + 2))) : ℝ) := by exact_mod_cast card_le_card hsplit
      _ ≤ (#((range X).filter fun n => S P I (res P n) = 0) : ℝ) +
            ((#((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) : ℝ) +
              #(range (2 * J + 2))) := by
          have h1 := card_union_le ((range X).filter fun n => S P I (res P n) = 0)
            (((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime) ∪
              range (2 * J + 2))
          have h2 := card_union_le
            ((Icc J (2 * J)).biUnion fun k => (range X).filter fun n => (n - k).Prime)
            (range (2 * J + 2))
          exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
      _ ≤ _ := by rw [hC]; linarith
  have density_screened (T : ℕ) :
      Tendsto (fun X : ℕ => (#{n ∈ range X | Screened T n} : ℝ) / X) atTop (𝓝 0) := by
    -- `(π(2J+T) + 1) / (J + 1) → 0` as `J → ∞`.
    have hJlim : Tendsto (fun J : ℕ => ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1))
        atTop (𝓝 0) := by
      have hlin : Tendsto (fun J : ℕ => 2 * J + T) atTop atTop :=
        tendsto_atTop_mono (fun J => show J ≤ 2 * J + T by omega) tendsto_id
      have hpi := tendsto_primeCounting_div.comp hlin
      have hratio : Tendsto (fun J : ℕ => ((2 * J + T : ℕ) : ℝ) / (J + 1)) atTop (𝓝 2) := by
        have : (fun J : ℕ => ((2 * J + T : ℕ) : ℝ) / (J + 1)) =
            fun J : ℕ => 2 + ((T : ℝ) - 2) / ((J : ℝ) + 1) := by
          funext J; push_cast; field_simp; ring
        rw [this]
        simpa using (tendsto_const_nhds (x := (2 : ℝ))).add
          ((tendsto_const_nhds (x := (T : ℝ) - 2)).div_atTop
            (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
      have hinv : Tendsto (fun J : ℕ => 1 / ((J : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have hmain := (hpi.mul hratio).add hinv
      rw [zero_mul, add_zero] at hmain
      refine hmain.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with J hJ
      have h1 : ((2 * J + T : ℕ) : ℝ) ≠ 0 := by
        have : 0 < 2 * J + T := by omega
        positivity
      show ((Nat.primeCounting (2 * J + T) : ℝ) / ((2 * J + T : ℕ) : ℝ)) *
          (((2 * J + T : ℕ) : ℝ) / (J + 1)) + 1 / ((J : ℝ) + 1) =
        ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1)
      field_simp
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (by positivity), ?_⟩
    intro ε hε
    -- Choose `J` with `(π(2J+T) + 1)/(J + 1) < ε / 2`.
    obtain ⟨J, hJ1, hJ⟩ : ∃ J : ℕ, 1 ≤ J ∧
        ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) < ε / 2 := by
      have := (hJlim.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop 1)
      obtain ⟨J, hJ⟩ := this.exists
      exact ⟨J, hJ.2, hJ.1⟩
    set c : ℝ := ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) with hc
    set Q : ℝ := ((∏ q ∈ Nat.primesLE (2 * J + T), q : ℕ) : ℝ) with hQ
    -- The upper bound divided by `X` tends to `c < ε / 2`.
    have hu : Tendsto (fun X : ℕ => (1 + Q / X) * c + (J + 1) * ((Nat.primeCounting X : ℝ) / X) +
        (2 * J + 2) / (X : ℝ)) atTop (𝓝 ((1 + 0) * c + (J + 1) * 0 + 0)) := by
      have hX : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      refine (((tendsto_const_nhds.add ((tendsto_const_nhds (x := Q)).div_atTop hX)).mul
        tendsto_const_nhds).add (tendsto_const_nhds.mul tendsto_primeCounting_div)).add
        ((tendsto_const_nhds (x := (2 * (J : ℝ) + 2))).div_atTop hX)
    simp only [add_zero, one_mul, mul_zero] at hu
    filter_upwards [hu.eventually (gt_mem_nhds (by linarith : c < ε)), eventually_ge_atTop 1]
      with X hXu hX1
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    have hbound := card_screened_le T J X hJ1
    calc (#{n ∈ range X | Screened T n} : ℝ) / X
        ≤ (((X : ℝ) + Q) * ((Nat.primeCounting (2 * J + T) : ℝ) + 1) / (J + 1) +
            (J + 1) * Nat.primeCounting X + (2 * J + 2)) / X :=
          div_le_div_of_nonneg_right hbound hXpos.le
      _ = (1 + Q / X) * c + (J + 1) * ((Nat.primeCounting X : ℝ) / X) + (2 * J + 2) / (X : ℝ) := by
          rw [hc]; field_simp
      _ < ε := hXu
  refine ⟨Screened, density_screened, fun T n hf J hJ hn => shift_witness hJ hn hf, ?_⟩
  intro T n
  constructor
  · intro he J hJ hn
    rcases he J hJ hn with hzero | hprime
    · left
      intro k hk
      by_contra! hh
      have hk' := mem_Icc.mp hk
      have hpos : 0 < S (Nat.primesLE (2 * J + T)) (Ico (J : ℤ) (J + (J + 1 : ℕ))) (res _ n) := by
        apply card_pos.mpr
        refine ⟨k, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩⟩
        intro p
        simpa [res] using hh p p.2
      omega
    · exact Or.inr hprime
  · intro h J hJ hn
    rcases h J hJ hn with h | hprime
    · left
      apply Nat.eq_zero_of_not_pos
      intro hpos
      obtain ⟨j, hj⟩ := card_pos.mp hpos
      obtain ⟨hI, hav⟩ := mem_filter.mp hj
      have hb := mem_Ico.mp hI
      have hnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
      obtain ⟨p, hp, he⟩ := h j.toNat (mem_Icc.mpr ⟨by omega, by omega⟩)
      apply hav ⟨p, hp⟩
      change (n : ZMod p) = (j : ZMod p)
      rw [← hnat, Int.cast_natCast]
      exact he
    · exact Or.inr hprime

private theorem gt_of_extends {n T : ℕ} (h : (∃ i : ℕ, T < i ∧ i + 1 < n + T ∧ ¬ (n + T - i).Prime ∧
        ∀ r : ℕ, r.Prime → r ≤ i → ¬ r ∣ n + T - i)) : n + T < F n := by
  obtain ⟨i, hi, hil, hnp, hr⟩ := h
  let r := n + T - i
  have hr2 : 1 < r := by dsimp [r]; omega
  have hlt : i < r.minFac := by
    by_contra! hh
    exact hr r.minFac (Nat.minFac_prime (by omega)) hh (Nat.minFac_dvd r)
  have hv := value_le (m := r) (n := n) (by dsimp [r]; omega) ⟨hr2, hnp⟩
  dsimp [r] at *
  omega

private theorem exists_unscreened_ge (E : ℕ → ℕ → Prop)
    (density_screened : ∀ T, Tendsto (fun X : ℕ => (#{n ∈ range X | E T n} : ℝ) / X) atTop (𝓝 0)) (T N : ℕ) : ∃ k ≥ N, ¬ E T k := by
  classical
  by_contra! hall
  have h := (density_screened T).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨M, hM⟩ := eventually_atTop.1 h
  let K := max 1 (max M N)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKM : M ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKN : N ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsub : Ico K (2 * K) ⊆ (range (2 * K)).filter (E T) := by
    intro k hk
    obtain ⟨hl, hu⟩ := mem_Ico.mp hk
    exact mem_filter.mpr ⟨mem_range.mpr hu, hall k (hKN.trans hl)⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have hnat : K ≤ #((range (2 * K)).filter (E T)) := by omega
  have hreal : (K : ℝ) ≤ (#((range (2 * K)).filter (E T)) : ℝ) := by exact_mod_cast hnat
  have hbad := hM (2 * K) (by omega)
  change (#((range (2 * K)).filter (E T)) : ℝ) / ((2 * K : ℕ) : ℝ) < 1 / 2 at hbad
  rw [div_lt_iff₀ (by exact_mod_cast (show 0 < 2 * K by omega))] at hbad
  push_cast at hbad
  linarith

private theorem propagate {T n : ℕ} {Screened : ℕ → ℕ → Prop}
    (bad_screened : F (n + 1) ≤ n + 1 + T → Screened T (n + 1)) (h₁ : Screened T (n + 1) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → T + 1 < p →
      n + 1 + T = p * (q + 1) → (∃ i : ℕ, T < i ∧ i + 1 < n + 1 + T ∧ ¬ (n + 1 + T - i).Prime ∧
        ∀ r : ℕ, r.Prime → r ≤ i → ¬ r ∣ n + 1 + T - i))
    (h₂ : Screened T (n + 1) →
    ∀ p q : ℕ, p.Prime → q.Composite → p ≤ q.minFac → T + 1 < p →
      n + 1 + T = p * (q + 1) → (∃ i : ℕ, T < i ∧ i + 1 < n + 1 + T ∧ ¬ (n + 1 + T - i).Prime ∧
        ∀ r : ℕ, r.Prime → r ≤ i → ¬ r ∣ n + 1 + T - i))
    (hprev : n + T < F n) : n + 1 + T < F (n + 1) := by
  by_contra! hbad
  have hscreen : Screened T (n + 1) := bad_screened hbad
  have hex : ∃ m < n, m.Composite ∧ n + T < m + m.minFac := by
    by_contra! hnone
    have hu : F n ≤ n + T := by
      apply csSup_le'
      rintro _ ⟨m, hm, hc, rfl⟩
      exact hnone m hm hc
    omega
  obtain ⟨m, hm, hc, hv⟩ := hex
  have hu := value_le (n := n + 1) (m := m) (by omega) hc
  have he : n + 1 + T = m + m.minFac := by omega
  let p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by have := hc.1; omega)
  have hpT : T + 1 < p := by dsimp [p]; omega
  obtain ⟨q, hmq⟩ := Nat.minFac_dvd m
  change m = p * q at hmq
  have hsq : p ^ 2 ≤ m := Nat.minFac_sq_le_self (by have := hc.1; omega) hc.2
  have hpq : p ≤ q := by
    by_contra! hq
    have hh := Nat.mul_lt_mul_of_pos_left hq hp.pos
    nlinarith
  have hfact : n + 1 + T = p * (q + 1) := by
    change n + 1 + T = m + p at he
    rw [mul_add, mul_one, ← hmq, he]
  have hq2 := hp.two_le.trans hpq
  have hfinish : (∃ i : ℕ, T < i ∧ i + 1 < n + 1 + T ∧ ¬ (n + 1 + T - i).Prime ∧
        ∀ r : ℕ, r.Prime → r ≤ i → ¬ r ∣ n + 1 + T - i) := by
    by_cases hq : q.Prime
    · exact h₁ hscreen p q hp hq hpq hpT hfact
    · have hdq : q.minFac ∣ m := hmq ▸ Dvd.dvd.mul_left (Nat.minFac_dvd q) p
      have hrough : p ≤ q.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le hdq
      exact h₂ hscreen p q hp ⟨by omega, hq⟩ hrough hpT hfact
  exact (not_lt_of_ge hbad) (gt_of_extends hfinish)

/-- Sieved endpoints from semiprimes, including squares. -/
def H1 : Prop :=
  ∀ T : ℕ, ∀ᶠ n : ℕ in atTop, (∀ J : ℕ, 1 ≤ J → 2 * J + 2 ≤ n →
      (∀ k ∈ Icc J (2 * J), ∃ p ∈ Nat.primesLE (2 * J + T), (n : ZMod p) = (k : ZMod p)) ∨
      ∃ k ∈ Icc J (2 * J), (n - k).Prime) →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → T + 1 < p →
      n + T = p * (q + 1) → (∃ i : ℕ, T < i ∧ i + 1 < n + T ∧ ¬ (n + T - i).Prime ∧
        ∀ r : ℕ, r.Prime → r ≤ i → ¬ r ∣ n + T - i)

/-- Sieved endpoints from composites with at least three prime factors, counted with multiplicity. -/
def H2 : Prop :=
  ∀ T : ℕ, ∀ᶠ n : ℕ in atTop, (∀ J : ℕ, 1 ≤ J → 2 * J + 2 ≤ n →
      (∀ k ∈ Icc J (2 * J), ∃ p ∈ Nat.primesLE (2 * J + T), (n : ZMod p) = (k : ZMod p)) ∨
      ∃ k ∈ Icc J (2 * J), (n - k).Prime) →
    ∀ p q : ℕ, p.Prime → q.Composite → p ≤ q.minFac → T + 1 < p →
      n + T = p * (q + 1) → (∃ i : ℕ, T < i ∧ i + 1 < n + T ∧ ¬ (n + T - i).Prime ∧
        ∀ r : ℕ, r.Prime → r ≤ i → ¬ r ∣ n + T - i)

theorem main : H1 → H2 → type_of% @Erdos385.erdos_385.parts.ii := by
  intro h₁ h₂
  obtain ⟨E, hdensity, hbad, hscreen⟩ := sieve_certificate
  apply tendsto_atTop.2
  intro T
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((h₁ T).and (h₂ T))
  obtain ⟨k, hk, hseed⟩ := exists_unscreened_ge E hdensity T N
  have hstart : k + T < F k := by
    by_contra! h
    exact hseed (hbad T k h)
  refine eventually_atTop.2 ⟨k, fun n hn => ?_⟩
  have hstrong : n + T < F n := by
    induction n, hn using Nat.le_induction with
    | base => exact hstart
    | succ n hn ih =>
      have h := hN (n+1) (by omega)
      exact propagate (hbad T (n+1)) (fun he => h.1 ((hscreen T (n+1)).mp he))
        (fun he => h.2 ((hscreen T (n+1)).mp he)) ih
  omega

end

end OMA.R_Erdos385_erdos_385_parts_ii_R1
