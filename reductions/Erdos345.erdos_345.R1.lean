import FormalConjectures.ErdosProblems.«345»
import Mathlib

/-!
The prime-divisor obstruction and comparison of degrees follow the mathematical
argument of Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer, Erdős 345,
in their November 2026 manuscript. The Lean proof of those steps here is independent.
For a product Q of primes p with p−1 dividing n, the missing integer used here is
Q^⌊(n+1)/4⌋−1. The completeness proof is adapted from the merged
open-math-agents proof of Erdos345.kthPowers_isAddComplete by @ysanatomic.
-/
open Filter
open scoped Topology

private theorem even_subset_sum_progressions (k d W : ℕ) (lo hi : Finset ℕ)
    (hlo : lo ⊆ Finset.range W) (hhi : hi ⊆ Finset.range W)
    (hdiff : ∀ b : ℕ, (∑ i ∈ hi, (2 * (b+i+1))^k) = (∑ i ∈ lo, (2 * (b+i+1))^k) + d) :
    ∀ T b : ℕ, ∃ S : ℕ, ∀ j ≤ T, ∃ s : Finset ℕ,
      (∀ x ∈ s, Even x ∧ 2*(b+1) ≤ x ∧ x < 2*(b+T*W+1)) ∧
        ∑ x ∈ s, x^k = S+d*j := by
  intro T
  induction T with
  | zero =>
    intro b
    refine ⟨0, fun j hj ↦ ⟨∅, by simp, ?_⟩⟩
    simp [show j = 0 by omega]
  | succ T ih =>
    intro b
    obtain ⟨B, hB⟩ := ih (b+W)
    let e (i : ℕ) := 2*(b+i+1)
    have he : Function.Injective e := by
      intro i j hij
      dsimp [e] at hij
      omega
    have combine (t : Finset ℕ) (ht : t ⊆ Finset.range W) (j : ℕ) (hj : j ≤ T) :
        ∃ s : Finset ℕ,
          (∀ x ∈ s, Even x ∧ 2*(b+1) ≤ x ∧ x < 2*(b+(T+1)*W+1)) ∧
            ∑ x ∈ s, x^k = (∑ i ∈ t, (e i)^k) + (B+d*j) := by
      obtain ⟨u, hu, hu_sum⟩ := hB j hj
      have hfirst (x : ℕ) (hx : x ∈ t.image e) :
          Even x ∧ 2*(b+1) ≤ x ∧ x < 2*(b+W+1) := by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        have hi' := Finset.mem_range.mp (ht hi)
        change Even (2*(b+i+1)) ∧ _ ∧ _
        exact ⟨⟨b+i+1, by omega⟩, by dsimp [e]; omega, by dsimp [e]; omega⟩
      have hdisj : Disjoint (t.image e) u := by
        refine Finset.disjoint_left.mpr fun x hx hxu ↦ ?_
        exact (not_lt_of_ge (hu x hxu).2.1) (hfirst x hx).2.2
      refine ⟨t.image e ∪ u, ?_, ?_⟩
      · intro x hx
        rw [show (T + 1) * W = T * W + W by ring]
        rcases Finset.mem_union.mp hx with hxt | hxu
        · obtain ⟨heven, hl, hh⟩ := hfirst x hxt
          exact ⟨heven, hl, by omega⟩
        · obtain ⟨heven, hl, hh⟩ := hu x hxu
          exact ⟨heven, by omega, by omega⟩
      · rw [Finset.sum_union hdisj, Finset.sum_image he.injOn, hu_sum]
    refine ⟨(∑ i ∈ lo, (e i)^k) + B, fun j hj ↦ ?_⟩
    cases j with
    | zero => simpa using combine lo hlo 0 (Nat.zero_le _)
    | succ j =>
      obtain ⟨s, hs, hsum⟩ := combine hi hhi j (by omega)
      refine ⟨s, hs, ?_⟩
      have hdi : (∑ i ∈ hi, (e i)^k) = (∑ i ∈ lo, (e i)^k) + d := hdiff b
      rw [hsum, hdi]
      ring

private theorem eventual_power_growth (k : ℕ) :
    ∃ N : ℕ, ∀ j ≥ N, (j + 2)^k ≤ 2 * j^k := by
  have hc : Tendsto (fun j : ℕ ↦ (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun j : ℕ ↦ (j : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hc
  have hlim : Tendsto (fun j : ℕ ↦ (1 + 2 * (j : ℝ)⁻¹)^k) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero, one_pow] using ((hinv.const_mul 2).const_add 1).pow k
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlim).2 (2 : ℝ) (by norm_num))
  refine ⟨N + 1, fun j hj ↦ ?_⟩
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hle : ((j : ℝ) + 2)^k ≤ 2 * (j : ℝ)^k := by
    calc
      _ = ((1 + 2 * (j : ℝ)⁻¹) * (j : ℝ))^k := by
        congr 1
        field_simp
      _ = (1 + 2 * (j : ℝ)⁻¹)^k * (j : ℝ)^k := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hN j (by omega)).le (by positivity)
  exact_mod_cast hle

namespace PowerCompleteness345

open Finset Function

private lemma erdos345_shift_of_const_diff (g : ℤ → ℤ) (c : ℤ)
    (hg : ∀ x, g (x + 1) - g x = c) (x : ℤ) (m : ℕ) :
    g (x + (m : ℤ)) - g x = (m : ℤ) * c := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    have h := hg (x + (m : ℤ))
    rw [← add_assoc]
    linear_combination h + ih

private lemma erdos345_iter_diff_shift (f : ℤ → ℤ) (k : ℕ) (c : ℤ)
    (hf : ∀ x, (fwdDiff (1 : ℤ))^[k + 1] f x = c) (m : ℕ) (x : ℤ) :
    (fwdDiff (1 : ℤ))^[k] (fun y ↦ f (y + (m : ℤ)) - f y) x = (m : ℤ) * c := by
  let g := (fwdDiff (1 : ℤ))^[k] f
  have hg (y : ℤ) : g (y + 1) - g y = c := by
    simpa only [g, Function.iterate_succ_apply', fwdDiff] using hf y
  let T := fwdDiff_aux.fwdDiffₗ ℤ ℤ (1 : ℤ) ^ k
  have hmap := congrFun (map_sub T (fun y : ℤ ↦ f (y + (m : ℤ))) f) x
  have h :
      (fwdDiff (1 : ℤ))^[k] (fun y ↦ f (y + (m : ℤ)) - f y) x =
      (fwdDiff (1 : ℤ))^[k] (fun y ↦ f (y + (m : ℤ))) x -
        (fwdDiff (1 : ℤ))^[k] f x := by
    change (fwdDiff (1 : ℤ))^[k] ((fun y : ℤ ↦ f (y + (m : ℤ))) - f) x = _
    simpa only [T, fwdDiff_aux.coe_fwdDiffₗ_pow, Pi.sub_apply] using hmap
  rw [h, fwdDiff_iter_comp_add]
  exact erdos345_shift_of_const_diff g c hg x m

private lemma erdos345_signed_offsets (k : ℕ) :
    ∃ W F : ℕ, ∃ lo hi : Finset ℕ, 0 < W ∧ 0 < F ∧
      lo ⊆ range W ∧ hi ⊆ range W ∧
      ∀ (f : ℤ → ℤ) (c : ℤ), (∀ x, (fwdDiff (1 : ℤ))^[k] f x = c) →
        ∀ x : ℤ, (∑ i ∈ hi, f (x + i)) - (∑ i ∈ lo, f (x + i)) = (F : ℤ) * c := by
  induction k with
  | zero =>
    refine ⟨1, 1, ∅, {0}, by decide, by decide, empty_subset _, by decide, ?_⟩
    intro f c hf x
    simpa using hf x
  | succ k ih =>
    obtain ⟨W, F, lo, hi, hW, hF, hlo, hhi, hprev⟩ := ih
    let shift := addLeftEmbedding W
    have hshift (s : Finset ℕ) (hs : s ⊆ range W) : s.map shift ⊆ range (W + W) := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hj
      have hil := mem_range.mp (hs hi)
      exact mem_range.mpr (Nat.add_lt_add_left hil W)
    have hsub (s : Finset ℕ) (hs : s ⊆ range W) : s ⊆ range (W + W) :=
      hs.trans (range_mono (Nat.le_add_right W W))
    have hdisj (s t : Finset ℕ) (ht : t ⊆ range W) : Disjoint (s.map shift) t := by
      apply Finset.disjoint_left.mpr
      intro j hj hJ
      obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      have h := mem_range.mp (ht hJ)
      change W + i < W at h
      omega
    refine ⟨W + W, F * W, lo.map shift ∪ hi, hi.map shift ∪ lo,
      by omega, Nat.mul_pos hF hW, union_subset (hshift _ hlo) (hsub _ hhi),
      union_subset (hshift _ hhi) (hsub _ hlo), ?_⟩
    intro f c hf x
    have h := hprev (fun y ↦ f (y + (W : ℤ)) - f y) ((W : ℤ) * c)
      (erdos345_iter_diff_shift f k c hf W) x
    simp only [sum_sub_distrib] at h
    rw [sum_union (hdisj _ _ hlo), sum_union (hdisj _ _ hhi), sum_map, sum_map]
    have hadd (i : ℕ) : x + ((W + i : ℕ) : ℤ) = x + i + W := by
      push_cast
      ring
    simp only [shift, addLeftEmbedding_apply, hadd, Nat.cast_mul]
    linear_combination h

/-- For each positive exponent, two translated families of even bases give sums that differ
by the same positive even number. -/
lemma erdos345_even_power_blocks (k : ℕ) (hk : 0 < k) :
    ∃ d W : ℕ, ∃ lo hi : Finset ℕ, 0 < d ∧ Even d ∧ 0 < W ∧
      lo ⊆ range W ∧ hi ⊆ range W ∧
      ∀ b : ℕ, (∑ i ∈ hi, (2 * (b + i + 1)) ^ k) =
        (∑ i ∈ lo, (2 * (b + i + 1)) ^ k) + d := by
  obtain ⟨W, F, lo, hi, hW, hF, hlo, hhi, h⟩ := erdos345_signed_offsets k
  let d := (2 : ℕ)^k * (F * k.factorial)
  have hd : 0 < d := Nat.mul_pos (pow_pos (by decide) _) (Nat.mul_pos hF (Nat.factorial_pos _))
  have hde : Even d := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp only [d, pow_succ']
    rw [mul_assoc]
    exact even_two_mul _
  refine ⟨d, W, lo, hi, hd, hde, hW, hlo, hhi, ?_⟩
  intro b
  have hconst (z : ℤ) : (fwdDiff (1 : ℤ))^[k] (fun x : ℤ ↦ x ^ k) z = (k.factorial : ℤ) := by
    exact congrFun fwdDiff_iter_eq_factorial z
  have hInt := sub_eq_iff_eq_add.mp
    (h (fun z : ℤ ↦ z ^ k) (k.factorial : ℤ) hconst ((b : ℤ) + 1))
  have hNat : (∑ i ∈ hi, (b + i + 1)^k) = (∑ i ∈ lo, (b + i + 1)^k) + F * k.factorial := by
    exact_mod_cast (by
      simpa only [add_right_comm (b : ℤ) 1, add_comm ((F : ℤ) * (k.factorial : ℤ))]
        using hInt :
      (∑ i ∈ hi, ((b : ℤ) + i + 1)^k) = (∑ i ∈ lo, ((b : ℤ) + i + 1)^k) +
        (F : ℤ) * (k.factorial : ℤ))
  simp only [mul_pow, ← mul_sum, d, ← mul_add, hNat]

end PowerCompleteness345

namespace PowerCompleteness345.ER345

open scoped BigOperators

/-- Odd bases occupy all residues modulo the increment of the even-base sums. -/
theorem exists_seed_interval (k d u : ℕ) (hd : 0 < d) (he : Even d)
    (hu : d * d + 1 < u)
    (hprogression : ∀ T : ℕ, ∃ S : ℕ, ∀ j ≤ T, ∃ s : Finset ℕ,
      (∀ x ∈ s, 0 < x ∧ Even x) ∧ ∑ x ∈ s, x ^ k = S + d * j) :
    ∀ W : ℕ, ∃ L : ℕ, ∀ n ∈ Finset.Icc L (L + W), ∃ s : Finset ℕ,
      (∀ x ∈ s, 0 < x ∧ (Even x ∨ x < u)) ∧ ∑ x ∈ s, x ^ k = n := by
  intro W
  let e : ℕ ↪ ℕ :=
    ⟨fun i ↦ 1 + d * i, fun _ _ hij ↦ Nat.mul_left_cancel hd (Nat.add_left_cancel hij)⟩
  let bankSum (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, (e i) ^ k
  let B := bankSum d
  obtain ⟨S, hS⟩ := hprogression (B + W)
  refine ⟨S + B, ?_⟩
  intro n hn
  obtain ⟨hnl, hnu⟩ := Finset.mem_Icc.mp hn
  let r := (n - S) % d
  have hr : r < d := Nat.mod_lt _ hd
  have hv_le : bankSum r ≤ B :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hr.le)
  have hmod : bankSum r ≡ r [MOD d] := by
    have hsum : bankSum r ≡ (∑ _i ∈ Finset.range r, 1) [MOD d] := by
      apply Nat.ModEq.sum
      intro i _
      have hi : 1 + d * i ≡ 1 [MOD d] := by
        simpa only [Nat.add_comm] using (Nat.ModEq.modulus_mul_add (m := d) (a := i) (b := 1))
      change (1 + d * i) ^ k ≡ 1 [MOD d]
      simpa only [one_pow] using hi.pow k
    simpa using hsum
  have hv_le_n : bankSum r ≤ n - S := by omega
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_exists_eq_add hv_le_n).mp
    (hmod.trans (Nat.mod_modEq (n - S) d))
  have hjd : j ≤ d * j := by
    simpa using Nat.mul_le_mul_right j (show 1 ≤ d from hd)
  have hjT : j ≤ B + W := by omega
  obtain ⟨s, hs, hsum⟩ := hS j hjT
  let t := (Finset.range r).map e
  have ht (x : ℕ) (hx : x ∈ t) : 0 < x ∧ Odd x ∧ x < u := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    have hid : i ≤ d := (Finset.mem_range.mp hi).le.trans hr.le
    change 0 < 1 + d * i ∧ Odd (1 + d * i) ∧ 1 + d * i < u
    have hmul := Nat.mul_le_mul_left d hid
    exact ⟨by omega, (he.mul_right i).one_add, by omega⟩
  have hdisj : Disjoint s t :=
    Finset.disjoint_left.mpr fun x hx hxt ↦ (Nat.not_even_iff_odd.mpr (ht x hxt).2.1) (hs x hx).2
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨(hs x hx).1, Or.inl (hs x hx).2⟩
    · exact ⟨(ht x hx).1, Or.inr (ht x hx).2.2⟩
  · have htsum : ∑ x ∈ t, x ^ k = bankSum r := Finset.sum_map _ _ _
    rw [Finset.sum_union hdisj, hsum, htsum]
    omega

end PowerCompleteness345.ER345

namespace PowerCompleteness345.Erdos345

open scoped BigOperators

lemma extend_odd_power_interval (k L W u : ℕ) (hu : 0 < u) (huOdd : Odd u)
    (hwidth : u ^ k ≤ W)
    (hseed : ∀ n ∈ Set.Icc L (L + W), ∃ s : Finset ℕ,
      (∀ x ∈ s, 0 < x ∧ (Even x ∨ x < u)) ∧ ∑ j ∈ s, j ^ k = n)
    (hgrowth : ∀ j, u ≤ j → (j + 2) ^ k ≤ 2 * j ^ k) :
    ∀ n, L ≤ n → ∃ s : Finset ℕ, (∀ x ∈ s, 0 < x) ∧ ∑ j ∈ s, j ^ k = n := by
  classical
  let width (t : ℕ) := W + ∑ j ∈ Finset.range t, (u + 2 * j) ^ k
  have width_succ (t : ℕ) : width (t + 1) = width t + (u + 2 * t) ^ k := by
    simp only [width, Finset.sum_range_succ, Nat.add_assoc]
  have hState (t : ℕ) :
      (u + 2 * t) ^ k ≤ width t ∧ t ≤ width t ∧
      ∀ n ∈ Set.Icc L (L + width t), ∃ s : Finset ℕ,
        (∀ x ∈ s, 0 < x ∧ (Even x ∨ x < u + 2 * t)) ∧ ∑ j ∈ s, j ^ k = n := by
    induction t with
    | zero =>
      exact ⟨by simpa [width] using hwidth, Nat.zero_le _, by simpa [width] using hseed⟩
    | succ t ih =>
      obtain ⟨hPower, hCount, hRep⟩ := ih
      have hFreshPos : 0 < u + 2 * t := by omega
      have hPowPos : 0 < (u + 2 * t) ^ k := pow_pos hFreshPos _
      have hCutoff : u + 2 * (t + 1) = (u + 2 * t) + 2 := by omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hCutoff, width_succ]
        exact (hgrowth _ (by omega)).trans (by omega)
      · rw [width_succ]
        omega
      · intro n hn
        change L ≤ n ∧ n ≤ L + width (t + 1) at hn
        rw [width_succ] at hn
        have hKeep (x : ℕ) (hx : 0 < x ∧ (Even x ∨ x < u + 2 * t)) :
            0 < x ∧ (Even x ∨ x < u + 2 * (t + 1)) :=
          ⟨hx.1, hx.2.imp_right (by omega)⟩
        by_cases hnOld : n ≤ L + width t
        · obtain ⟨s, hs, hsum⟩ := hRep n ⟨hn.1, hnOld⟩
          exact ⟨s, fun x hx => hKeep x (hs x hx), hsum⟩
        · obtain ⟨s, hs, hsum⟩ := hRep (n - (u + 2 * t) ^ k) ⟨by omega, by omega⟩
          have hFresh : u + 2 * t ∉ s := by
            intro h
            rcases (hs _ h).2 with ⟨a, ha⟩ | hlt
            · obtain ⟨b, hb⟩ := huOdd
              omega
            · omega
          refine ⟨insert (u + 2 * t) s, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ⟨hFreshPos, Or.inr (by omega)⟩
            · exact hKeep x (hs x hx)
          · rw [Finset.sum_insert hFresh, hsum]
            omega
  intro n hn
  have h := hState n
  obtain ⟨s, hs, hsum⟩ := h.2.2 n ⟨hn, by have := h.2.1; omega⟩
  exact ⟨s, fun x hx => (hs x hx).1, hsum⟩

end PowerCompleteness345.Erdos345

private theorem power_complete : ∀ k : ℕ, 0 < k → IsAddComplete (Erdos345.kthPowers k) := by
  intro k hk
  obtain ⟨d, W, lo, hi, hd, he, _, hlo, hhi, hdiff⟩ := PowerCompleteness345.erdos345_even_power_blocks k hk
  have hprogression (T : ℕ) : ∃ S : ℕ, ∀ j ≤ T, ∃ s : Finset ℕ,
      (∀ x ∈ s, 0 < x ∧ Even x) ∧ ∑ x ∈ s, x^k = S + d*j := by
    obtain ⟨S, hS⟩ := even_subset_sum_progressions k d W lo hi hlo hhi hdiff T 0
    refine ⟨S, fun j hj ↦ ?_⟩
    obtain ⟨s, hs, hsum⟩ := hS j hj
    exact ⟨s, fun x hx ↦ ⟨by have := (hs x hx).2.1; omega, (hs x hx).1⟩, hsum⟩
  obtain ⟨N, hN⟩ := eventual_power_growth k
  let u := 2 * max N (d*d+1) + 1
  have hu : 0 < u := by dsimp [u]; omega
  have huOdd : Odd u := ⟨max N (d*d+1), rfl⟩
  have huLarge : d*d+1 < u := by
    have := le_max_right N (d*d+1)
    dsimp [u]
    omega
  have huGrowth : ∀ j, u ≤ j → (j+2)^k ≤ 2 * j^k := by
    intro j hj
    apply hN
    have := le_max_left N (d*d+1)
    dsimp [u] at hj
    omega
  obtain ⟨L, hL⟩ := PowerCompleteness345.ER345.exists_seed_interval k d u hd he huLarge hprogression (u^k)
  have hseed : ∀ n ∈ Set.Icc L (L + u^k), ∃ s : Finset ℕ,
      (∀ x ∈ s, 0 < x ∧ (Even x ∨ x < u)) ∧ ∑ j ∈ s, j^k = n := by
    intro n hn
    exact hL n (Finset.mem_Icc.mpr hn)
  have hcover := PowerCompleteness345.Erdos345.extend_odd_power_interval k L (u^k) u hu huOdd le_rfl hseed huGrowth
  refine eventually_atTop.mpr ⟨L, fun n hn ↦ ?_⟩
  obtain ⟨s, hs, hsum⟩ := hcover n hn
  refine ⟨s.image (·^k), ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨j, hs j hj, rfl⟩
  · rw [Finset.sum_image (Nat.pow_left_injective hk.ne').injOn]
    exact hsum.symm

namespace OMA.R_Erdos345_erdos_345_R1

open IsAddComplete Finset
open _root_.Erdos345


private theorem frobenius_product (n b : ℕ) (P : Finset ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p ∧ p - 1 ∣ n) :
    b ^ (n + 1) ≡ b [MOD ∏ p ∈ P, p] := by
  induction P using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert p S hps ih =>
    have h := hp p (Finset.mem_insert_self ..)
    have hs (q : ℕ) (hq : q ∈ S) := hp q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps, ← Nat.modEq_and_modEq_iff_modEq_mul]
    · refine ⟨?_, ih hs⟩
      letI : Fact p.Prime := ⟨h.1⟩
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      push_cast
      obtain ⟨d,hd⟩ := h.2
      by_cases hz : (b : ZMod p) = 0
      · simp [hz]
      · rw [pow_succ,hd,pow_mul,ZMod.pow_card_sub_one_eq_one hz,one_pow,one_mul]
    · apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes h.1 (hs q hq).1).mpr (fun e => hps (e ▸ hq))

private theorem unpack {j M : ℕ} (hj : 0 < j) (hr : M ∈ subsetSums (kthPowers j)) :
    ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b) ∧ (∑ b ∈ B, b ^ j) = M := by
  classical
  obtain ⟨S,hs,he⟩ := hr
  have inj := Nat.pow_left_injective (Nat.ne_of_gt hj)
  let B := S.preimage (fun b => b ^ j) inj.injOn
  have him : B.image (fun b => b^j) = S := by
    rw [show B.image (fun b => b^j) = _ from Finset.image_preimage _ S inj.injOn]
    apply Finset.filter_true_of_mem
    intro m hm
    obtain ⟨b,_,hb⟩ := hs hm
    exact ⟨b,hb⟩
  refine ⟨B, ?_, ?_⟩
  · intro b hb
    have hmem : b^j ∈ S := (Finset.mem_preimage (f := fun x : ℕ => x^j)).mp hb
    obtain ⟨c,hc,heq⟩ := hs hmem
    exact inj heq ▸ hc
  · rw [he, ← him, Finset.sum_image inj.injOn]

private theorem missing_residue (n Q : ℕ) (hn : 7 ≤ n) (hQ : 4 ≤ Q)
    (hfix : ∀ b : ℕ, b^(n+1) ≡ b [MOD Q]) :
    Q^((n+1)/4)-1 ∉ subsetSums (kthPowers (n+1)) := by
  classical
  let t := (n+1)/4
  have ht : 0 < t := by dsimp [t]; omega
  have hpow : 1 < Q^t := Nat.one_lt_pow (by omega) (by omega)
  let M := Q^t-1
  have hM : M+1=Q^t := by dsimp [M]; omega
  intro hr
  obtain ⟨B,hpos,hsum⟩ := unpack (Nat.succ_pos _) hr
  change (∑ b ∈ B, b^(n+1)) = M at hsum
  have hnB : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at hsum
    omega
  let m := B.max' hnB
  have hmB : m ∈ B := Finset.max'_mem _ _
  have hm0 := hpos m hmB
  have hmM : m^(n+1) ≤ M := by
    rw [← hsum]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (i^(n+1))) hmB
  have hmQ : m^4 < Q := by
    by_contra! h
    have e := Nat.pow_le_pow_left h t
    rw [← pow_mul] at e
    have f : m^(4*t) ≤ m^(n+1) := Nat.pow_le_pow_right hm0 (by dsimp [t]; omega)
    omega
  have hcard : B.card ≤ m+1 := by
    have hsub : B ⊆ Finset.range (m+1) := fun b hb => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_max' _ _ hb))
    simpa using Finset.card_le_card hsub
  have hbsum : (∑ b ∈ B, b) ≤ (m+1)*m := by
    calc
      _ ≤ ∑ _b ∈ B, m := Finset.sum_le_sum (fun b hb => Finset.le_max' _ _ hb)
      _ = B.card * m := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcard
  have small : (∑ b ∈ B, b)+1 < Q := by
    by_cases hm : m < 2
    · have : m=1 := by omega
      rw [this] at hbsum
      omega
    · have hm2 : m+1 ≤ m*m := by nlinarith
      have h1 : (m+1)*m+1 ≤ (m*m)*m+m*m := Nat.add_le_add (Nat.mul_le_mul_right m hm2) (by nlinarith)
      have h2 := Nat.mul_le_mul_left (m*m) hm2
      nlinarith
  have modsum := Nat.ModEq.sum (s:=B) (fun b _ => hfix b)
  rw [hsum] at modsum
  have hd : Q ∣ (∑ b ∈ B, b)+1 := by
    apply Nat.modEq_zero_iff_dvd.mp
    have h := modsum.symm.add_right 1
    rw [hM] at h
    exact h.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self _ ht.ne'))
  exact small.not_ge (Nat.le_of_dvd (by omega) hd)

-- The two bounds use an exponent between 2/5 and 9/20 in the estimates of
-- Howe, Huffman, Kohlmeyer and Kruer. H1 is an infinitely-often shifted-prime
-- bound. H2 asks for a later degree whose representability threshold is small.
def H1 : Prop :=
  ∀ B : ℕ, ∃ n ≥ B, ∃ P : Finset ℕ,
    (∀ p ∈ P, Nat.Prime p ∧ p-1 ∣ n) ∧
    8 * (1 + ⌊Real.exp ((17/40 : ℝ) * Real.log n / Real.log (Real.log n))⌋₊) ≤ P.card

def H2 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop, ∃ k > n,
    2^((n+1) * ⌊Real.exp ((17/40 : ℝ) * Real.log n / Real.log (Real.log n))⌋₊) ∈
      IsAddComplete.thresholds (_root_.Erdos345.kthPowers k)

theorem main : H1 → H2 → type_of% @Erdos345.erdos_345 := by
  intro hprimes hlevels
  classical
  let T := fun k => threshold (_root_.Erdos345.kthPowers k)
  by_contra hfinite
  obtain ⟨B,hB⟩ := (Set.not_infinite.mp hfinite).bddAbove
  have hmono : MonotoneOn T (Set.Ici (B+1)) := by
    apply monotoneOn_nat_Ici_of_le_succ
    intro k hk
    change B+1 ≤ k at hk
    by_contra! h
    have hmem := (threshold_descent_iff (power_complete k (by omega)) (power_complete (k+1) (by omega))).mp h
    exact (show ¬k≤B by omega) (hB (show k ∈ {j : ℕ | 0 < j ∧ ∃ a b,
      IsLeast (thresholds (_root_.Erdos345.kthPowers j)) a ∧
      IsLeast (thresholds (_root_.Erdos345.kthPowers (j+1))) b ∧ b<a} from ⟨by omega,hmem⟩))
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp hlevels
  obtain ⟨n,hn,P,hP,hc⟩ := hprimes (max 7 (max B L))
  have hn7 : 7 ≤ n := le_trans (le_max_left ..) hn
  have hnB : B ≤ n := le_trans (le_max_left B L) ((le_max_right ..).trans hn)
  have hnL : L ≤ n := le_trans (le_max_right B L) ((le_max_right ..).trans hn)
  let u := ⌊Real.exp ((17/40 : ℝ) * Real.log n / Real.log (Real.log n))⌋₊
  change 8*(1+u) ≤ P.card at hc
  obtain ⟨k,hk,hbound⟩ := hL n hnL
  change 2^((n+1)*u) ∈ thresholds (_root_.Erdos345.kthPowers k) at hbound
  let Q := ∏ p ∈ P, p
  let t := (n+1)/4
  have ht : 0 < t := by dsimp [t]; omega
  have hQ : 2^P.card ≤ Q := by
    calc 2^P.card = ∏ _p ∈ P, (2:ℕ) := by simp
         _ ≤ Q := Finset.prod_le_prod' (fun p hp => (hP p hp).1.two_le)
  have four : 4 ≤ Q := le_trans (show 2^2 ≤ 2^P.card from Nat.pow_le_pow_right (by decide) (by omega)) hQ
  have hlen : n+1 ≤ 8*t := by dsimp [t]; omega
  have hexp : (n+1)*u < P.card*t := by
    have ha := Nat.mul_le_mul_right u hlen
    have hb := Nat.mul_le_mul_right t hc
    nlinarith
  have hsize : 2^((n+1)*u) < Q^t := by
    calc 2^((n+1)*u) < (2:ℕ)^(P.card*t) := Nat.pow_lt_pow_right (by decide) hexp
         _ = ((2:ℕ)^P.card)^t := pow_mul .. 
         _ ≤ Q^t := Nat.pow_le_pow_left hQ t
  have hTK : T k ≤ 2^((n+1)*u) := (threshold_isLeast (power_complete k (by omega))).2 hbound
  have hTN : T (n+1) ≤ T k := hmono (by change B+1≤n+1; omega) (by change B+1≤k; omega) hk
  have hr := (threshold_isLeast (power_complete (n+1) (by omega))).1
  exact missing_residue n Q hn7 four (fun b => frobenius_product n b P hP)
    (hr (Q^t-1) (show T (n+1) ≤ Q^t-1 by omega))


end OMA.R_Erdos345_erdos_345_R1
