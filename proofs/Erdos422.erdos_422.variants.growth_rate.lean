import FormalConjectures.ErdosProblems.«422»
import Mathlib

-- Credit: @Iraeeee

open Filter

namespace HofstadterGrowth

/-- Looking one step ahead bounds the current value by its index. -/
theorem le_index (f : ℕ+ → ℕ+) (hf : Erdos422.IsHofstadterQ f) (n : ℕ+) : f n ≤ n := by
  by_cases hn : n = 1
  · simp [hn, hf.1]
  have h : (2 : ℕ+) < n + 1 := by
    change 2 < (n : ℕ) + 1
    have := n.pos
    have hn' : (n : ℕ) ≠ 1 := fun e => hn (PNat.eq e)
    omega
  have hprev := (hf.2.2 (n + 1) h).1
  rw [PNat.add_sub] at hprev
  change (f n : ℕ) < (n : ℕ) + 1 at hprev
  exact Nat.le_of_lt_succ hprev

/-- Any total Q-sequence exceeds every slope below one half arbitrarily far out. -/
theorem exceeds_slope (f : ℕ+ → ℕ+) (hf : Erdos422.IsHofstadterQ f)
    (c : ℝ) (hc : c < 1/2) (M : ℕ+) :
    ∃ n ≥ M, c * (n : ℝ) < (f n : ℝ) := by
  by_contra! h
  have hpos (n : ℕ+) : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 ≤ c := by
    by_contra! hneg
    exact (not_lt_of_ge (h M le_rfl)) <| (mul_neg_of_neg_of_pos hneg (hpos M)).trans (hpos (f M))
  let N : ℕ+ := M + 2
  have splitAt (n : ℕ+) (hn : N ≤ n) :
      ∃ i j : ℕ+, i < n ∧ j < n ∧ f n = f i + f j ∧
        (1-c)*(n : ℝ) ≤ (i : ℝ) ∧ (1-c)*(n : ℝ) ≤ (j : ℝ) := by
    have hn2 : (2 : ℕ+) < n := (PNat.lt_add_left 2 M).trans_le hn
    obtain ⟨h1,h2,hr⟩ := hf.2.2 n hn2
    have child (d : ℕ+) (hd : d ≤ 2) (hfd : f (n-d) < n) :
        n-f (n-d) < n ∧ (1-c)*(n : ℝ) ≤ ((n-f (n-d) : ℕ+) : ℝ) := by
      have hd' : d < n := hd.trans_lt hn2
      have he := PNat.sub_add_of_lt hd'
      have he' := PNat.sub_add_of_lt hfd
      have hM : M ≤ n-d := by
        change (M : ℕ) + 2 ≤ (n : ℕ) at hn
        change (d : ℕ) ≤ 2 at hd
        have heNat : ((n-d : ℕ+) : ℕ) + (d : ℕ) = (n : ℕ) := by exact_mod_cast he
        change (M : ℕ) ≤ ((n-d : ℕ+) : ℕ)
        omega
      have hle : ((n-d : ℕ+) : ℝ) ≤ (n : ℝ) := by exact_mod_cast PNat.sub_le n d
      have hb := (h (n-d) hM).trans (mul_le_mul_of_nonneg_left hle hc0)
      have hs : ((n-f (n-d) : ℕ+) : ℝ) + (f (n-d) : ℝ) = (n : ℝ) := by exact_mod_cast he'
      exact ⟨by exact_mod_cast (show ((n-f (n-d) : ℕ+) : ℝ) < (n : ℝ) by linarith [hpos (f (n-d))]),
        by linarith⟩
    obtain ⟨hi,hi'⟩ := child 1 (by decide) h1
    obtain ⟨hj,hj'⟩ := child 2 le_rfl h2
    exact ⟨_, _, hi, hj, hr, hi', hj'⟩
  have base (n : ℕ+) : (n : ℝ) ≤ (N : ℝ) * (f n : ℝ) := by
    induction n using PNat.strongInductionOn with
    | _ n IH =>
      by_cases hn : N ≤ n
      · obtain ⟨i,j,hi,hj,he,hi',hj'⟩ := splitAt n hn
        have hs : (f n : ℝ) = (f i : ℝ) + (f j : ℝ) := by exact_mod_cast he
        rw [hs, mul_add]
        nlinarith [IH i hi, IH j hj, mul_pos (sub_pos.mpr hc) (hpos n)]
      · have hv : (1 : ℝ) ≤ (f n : ℝ) := by exact_mod_cast (f n).pos
        have hn' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_of_not_ge hn)
        exact hn'.trans (by simpa using mul_le_mul_of_nonneg_left hv (hpos N).le)
  let r : ℝ := 2*(1-c)
  have hr : 1 < r := by dsimp [r]; linarith
  have amp (k : ℕ) : ∃ B : ℕ+, ∀ n ≥ B, r^k*(n : ℝ) ≤ (N : ℝ)*(f n : ℝ) := by
    induction k with
    | zero => exact ⟨1, fun n _ => by simpa using base n⟩
    | succ k IH =>
      obtain ⟨B,hB⟩ := IH
      refine ⟨max N (B+B), fun n hn => ?_⟩
      obtain ⟨i,j,_,_,he,hi,hj⟩ := splitAt n ((le_max_left ..).trans hn)
      have hBB : (B : ℝ) + (B : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show B+B ≤ n from (le_max_right ..).trans hn)
      have half : (n : ℝ)/2 ≤ (1-c)*(n : ℝ) := by nlinarith [mul_pos (sub_pos.mpr hc) (hpos n)]
      have hBi : B ≤ i := by exact_mod_cast (show (B : ℝ) ≤ (i : ℝ) by linarith)
      have hBj : B ≤ j := by exact_mod_cast (show (B : ℝ) ≤ (j : ℝ) by linarith)
      have hs : (f n : ℝ) = (f i : ℝ) + (f j : ℝ) := by exact_mod_cast he
      rw [hs, mul_add, pow_succ]
      calc
        r^k * r * (n : ℝ) = r^k * ((1-c)*(n : ℝ) + (1-c)*(n : ℝ)) := by dsimp [r]; ring
        _ ≤ r^k * ((i : ℝ) + (j : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add hi hj) (pow_nonneg (by linarith : 0 ≤ r) k)
        _ ≤ _ := by rw [mul_add]; exact add_le_add (hB i hBi) (hB j hBj)
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (N : ℝ) hr
  obtain ⟨B,hB⟩ := amp k
  have hu : (f B : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_index f hf B
  exact (not_lt_of_ge ((hB B le_rfl).trans (mul_le_mul_of_nonneg_left hu (hpos N).le)))
    (mul_lt_mul_of_pos_right hk (hpos B))

/-- Every slope above one half also bounds arbitrarily late terms from above. -/
theorem below_slope (f : ℕ+ → ℕ+) (hf : Erdos422.IsHofstadterQ f)
    (c : ℝ) (hc : 1/2 < c) (M : ℕ+) :
    ∃ n ≥ M, (f n : ℝ) < c * (n : ℝ) := by
  by_contra! h
  have pos (n : ℕ+) : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have upper (n : ℕ+) : (f n : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_index f hf n
  have hc1 : c ≤ 1 := by
    by_contra! hh
    nlinarith [h M le_rfl, upper M, mul_pos (sub_pos.mpr hh) (pos M)]
  let N : ℕ+ := M + 2
  let r : ℝ := 2*(1-c)
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have sumIndices (n : ℕ+) (hn : N ≤ n) :
      ∃ i j : ℕ+, f n = f i + f j ∧ (i : ℝ) + (j : ℝ) ≤ r*(n : ℝ) + 3*c := by
    have hn2 : (2 : ℕ+) < n := (PNat.lt_add_left 2 M).trans_le hn
    obtain ⟨h1,h2,he⟩ := hf.2.2 n hn2
    have child (d : ℕ+) (hd : d ≤ 2) (hfd : f (n-d) < n) :
        ((n-f (n-d) : ℕ+) : ℝ) ≤ (1-c)*(n : ℝ) + c*(d : ℝ) := by
      have heNat : ((n-d : ℕ+) : ℕ) + (d : ℕ) = (n : ℕ) := by
        exact_mod_cast PNat.sub_add_of_lt (hd.trans_lt hn2)
      have hM : M ≤ n-d := by
        change (M : ℕ) + 2 ≤ (n : ℕ) at hn
        change (d : ℕ) ≤ 2 at hd
        change (M : ℕ) ≤ ((n-d : ℕ+) : ℕ)
        omega
      have heReal : ((n-d : ℕ+) : ℝ) + (d : ℝ) = (n : ℝ) := by exact_mod_cast heNat
      have hfReal : ((n-f (n-d) : ℕ+) : ℝ) + (f (n-d) : ℝ) = (n : ℝ) := by
        exact_mod_cast PNat.sub_add_of_lt hfd
      linarith [h (n-d) hM, congrArg (c * ·) heReal]
    refine ⟨_, _, he, ?_⟩
    have hsum := add_le_add (child 1 (by decide) h1) (child 2 le_rfl h2)
    norm_num at hsum
    dsimp [r]
    linarith
  have shrink (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ+, (f n : ℝ) ≤ r^k*(n : ℝ) + C := by
    induction k with
    | zero => exact ⟨0, le_rfl, fun n => by simpa using upper n⟩
    | succ k IH =>
      obtain ⟨C,hC,hB⟩ := IH
      have hpow := pow_nonneg hr0 k
      have hc0 : 0 ≤ c := by linarith
      refine ⟨(N : ℝ) + 3*c*r^k + 2*C, by positivity, fun n => ?_⟩
      by_cases hn : N ≤ n
      · obtain ⟨i,j,he,hs⟩ := sumIndices n hn
        have hfr : (f n : ℝ) = (f i : ℝ) + (f j : ℝ) := by exact_mod_cast he
        rw [hfr, pow_succ]
        nlinarith [add_le_add (hB i) (hB j), mul_le_mul_of_nonneg_left hs hpow, pos N]
      · have hsmall : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_of_not_ge hn)
        have hz : 0 ≤ r^(k+1)*(n : ℝ) + 3*c*r^k + 2*C := by positivity
        linarith [upper n]
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < c) hr1
  obtain ⟨C,_,hC⟩ := shrink k
  obtain ⟨t,ht⟩ := exists_nat_gt (C / (c-r^k))
  let n : ℕ+ := M + ⟨t+1, by omega⟩
  have hMn : M ≤ n := (PNat.lt_add_right ..).le
  have htn : (t : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show t ≤ (M : ℕ) + (t+1) by omega)
  have hbig := (div_lt_iff₀ (sub_pos.mpr hk)).mp (ht.trans_le htn)
  nlinarith [h n hMn, hC n]

end HofstadterGrowth

noncomputable def OMA.answer : ℕ+ → ℝ := fun n => n

theorem OMA.solution : Erdos422.erdos_422.variants.growth_rate.answer = OMA.answer → type_of% @Erdos422.erdos_422.variants.growth_rate := by
  intro h f hf
  rw [h]
  apply Asymptotics.IsBigO.of_bound 1
  exact Filter.Eventually.of_forall fun n => by
    have hl : (f n : ℝ) ≤ (n : ℝ) := by exact_mod_cast HofstadterGrowth.le_index f hf n
    simpa [OMA.answer, Real.norm_eq_abs] using hl
