import FormalConjectures.ErdosProblems.«1145»

/-!
# Balanced additive complements

This formalizes the counterexample of Will Howe, Grant Huffman, Jensen Kohlmeyer,
and Liam Kruer. Affine blocks at nested coprime scales have a bounded residue
count across all preceding blocks. Safe candidates supply coverage and can be
matched at distance of order the square root of their sizes.

https://hexagonmath.org/2611.00758v1
-/

namespace OMA.Erdos1145Proof

open Filter AdditiveCombinatorics
open scoped Pointwise Topology Set

def residueCount (S : Finset ℕ) (m r : ℕ) : ℕ :=
  (S.filter fun n => n ≡ r [MOD m]).card

/-- Among residue classes refining a parent of bounded size, two distinct children
cannot both use more than half of the parent's budget. -/
theorem no_two_large_children (S : Finset ℕ) {m M a b budget : ℕ}
    (hm : m ∣ M) (hab : a ≡ b [MOD m]) (hsep : ¬ a ≡ b [MOD M])
    (hbudget : residueCount S m a ≤ 2 * budget + 1) :
    ¬ (budget < residueCount S M a ∧ budget < residueCount S M b) := by
  let A := S.filter fun n => n ≡ a [MOD M]
  let B := S.filter fun n => n ≡ b [MOD M]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro n hnA hnB
    exact hsep ((Finset.mem_filter.mp hnA).2.symm.trans (Finset.mem_filter.mp hnB).2)
  have hsub : A ∪ B ⊆ S.filter (fun n => n ≡ a [MOD m]) := by
    intro n h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨hn, hM⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hn, hM.of_dvd hm⟩
    · obtain ⟨hn, hM⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hn, (hM.of_dvd hm).trans hab.symm⟩
  have hcard : A.card + B.card ≤ residueCount S m a := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  change ¬ (budget < A.card ∧ budget < B.card)
  omega

noncomputable def representations (A B : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  open scoped Classical in
  (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)

theorem convolution_eq_representations (A B : Set ℕ) (n : ℕ) :
    (((𝟙_A ∗ 𝟙_B) : ℕ → ℕ) n) = (representations A B n).card := by
  classical
  unfold representations
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;>
    simp [Set.indicatorOne, Set.indicator, ha, hb]

theorem ratio_of_sqrt_distance {a b : ℕ → ℕ} (C : ℝ)
    (hgrowth : Tendsto (fun n => (b n : ℝ)) atTop atTop)
    (hclose : ∀ᶠ n in atTop, |(a n : ℝ) - b n| ≤ C * Real.sqrt (b n : ℝ)) :
    Tendsto (fun n => (a n : ℝ) / (b n : ℝ)) atTop (𝓝 1) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hvanishes : Tendsto (fun n => C / Real.sqrt (b n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hgrowth))
  apply squeeze_zero_norm' _ hvanishes
  filter_upwards [hclose, tendsto_atTop.mp hgrowth 1] with n hc hb
  have hp : 0 < (b n : ℝ) := by linarith
  have hroot := Real.sqrt_pos.2 hp
  have hsq : (Real.sqrt (b n : ℝ)) ^ 2 = (b n : ℝ) := Real.sq_sqrt hp.le
  have heq : (a n : ℝ) / (b n : ℝ) - 1 = ((a n : ℝ) - b n) / b n := by
    field_simp
  rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hp]
  calc
    _ ≤ (C * Real.sqrt (b n : ℝ)) / b n := div_le_div_of_nonneg_right hc hp.le
    _ = C / Real.sqrt (b n : ℝ) := by
      apply (div_eq_div_iff hp.ne' hroot.ne').mpr
      calc
        _ = C * (Real.sqrt (b n : ℝ)) ^ 2 := by ring
        _ = C * (b n : ℝ) := congrArg (C * ·) hsq

theorem disproof_of_balanced_complements {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (hratio : Tendsto (fun n => (Nat.nth (· ∈ A) n : ℝ) / (Nat.nth (· ∈ B) n : ℝ)) atTop (𝓝 1))
    (hcover : ∀ᶠ n in atTop, n ∈ A + B) (C : ℕ)
    (hcount : ∀ n, (representations A B n).card ≤ C) : ¬ Erdos1145.Erdos1145Prop := by
  let values := fun n => (↑(((𝟙_A ∗ 𝟙_B) : ℕ → ℕ) n) : ℕ∞)
  have hbd : limsup values atTop ≤ (C : ℕ∞) := by
    apply limsup_le_of_le (by isBoundedDefault)
    apply Eventually.of_forall
    intro n
    dsimp [values]
    rw [convolution_eq_representations]
    exact_mod_cast hcount n
  intro h
  have hlim : limsup values atTop = ⊤ := h hA hB hratio hcover
  rw [hlim] at hbd
  exact (not_le_of_gt (show (C : ℕ∞) < ⊤ by simp)) hbd


open Finset

private def q (k : ℕ) : ℕ := 27 * 3 ^ k

private def p : ℕ → ℕ
  | 0 => 32
  | k + 1 => if 3 * q k < 2 * p k then 2 * p k else 4 * p k

private theorem q_step (k : ℕ) : q (k + 1) = 3 * q k := by
  simp [q, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem p_step (k : ℕ) : p (k + 1) = 2 * p k ∨ p (k + 1) = 4 * p k := by
  rw [p]
  split <;> simp

private theorem q_odd (k : ℕ) : Odd (q k) :=
  (by decide : Odd (27 : ℕ)).mul ((by decide : Odd (3 : ℕ)).pow)

private theorem scale_bounds (k : ℕ) : 0 < q k ∧ q k < p k ∧ p k < 2 * q k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hodd : q k % 2 = 1 := by
      obtain ⟨j, hj⟩ := q_odd k
      omega
    rw [q_step, p]
    split <;> omega

private theorem p_pos (k : ℕ) : 0 < p k := (scale_bounds k).1.trans (scale_bounds k).2.1

private theorem p_grow (k : ℕ) : 2 * p k ≤ p (k + 1) := by
  rcases p_step k with h | h <;> omega

private theorem p_strict : StrictMono p :=
  strictMono_nat_of_lt_succ fun k => (by have := p_pos k; omega : p k < 2 * p k).trans_le (p_grow k)

private theorem p_base (k : ℕ) : 32 ≤ p k := p_strict.monotone (Nat.zero_le k)

private theorem power_two (k : ℕ) : ∃ e, p k = 2 ^ e := by
  induction k with
  | zero => exact ⟨5, rfl⟩
  | succ k ih =>
    obtain ⟨e, he⟩ := ih
    rcases p_step k with h | h
    · refine ⟨e + 1, ?_⟩
      rw [h, he, pow_succ, Nat.mul_comm]
    · refine ⟨e + 2, ?_⟩
      rw [h, he, pow_add, Nat.mul_comm]
      rfl

private theorem p_coprime (i j : ℕ) : (p i).Coprime (q j) := by
  obtain ⟨e, he⟩ := power_two i
  rw [he]
  exact (Nat.coprime_two_left.mpr (q_odd j)).pow_left e

private theorem q_dvd {i j : ℕ} (h : i ≤ j) : q i ∣ q j := by
  exact Nat.mul_dvd_mul_left _ (Nat.pow_dvd_pow 3 h)

private theorem p_dvd {i j : ℕ} (h : i ≤ j) : p i ∣ p j := by
  induction j with
  | zero => simpa [show i = 0 by omega] using (dvd_rfl : p 0 ∣ p 0)
  | succ j ih =>
    by_cases h' : i ≤ j
    · rcases p_step j with he | he
      · exact (ih h').trans (he ▸ dvd_mul_left _ _)
      · exact (ih h').trans (he ▸ dvd_mul_left _ _)
    · have : i = j + 1 := by omega
      subst i
      exact dvd_rfl

private theorem mul_cancel_mod {m c x y : ℕ} (hc : m.Coprime c)
    (h : c * x ≡ c * y [MOD m]) : x ≡ y [MOD m] := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this h.symm (by omega)).symm
  have hd := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left c hxy)).mp h
  rw [← Nat.mul_sub_left_distrib] at hd
  exact (Nat.modEq_iff_dvd' hxy).mpr (hc.dvd_of_dvd_mul_left hd)

private theorem small_mod_unique {m x y : ℕ} (hx : x < m) (hy : y < m)
    (h : x ≡ y [MOD m]) : x = y := by
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using h

private theorem period_fiber_bound (c d m L r : ℕ) (hm : 0 < m) (hc : m.Coprime c) :
    ((range (L * m)).filter fun i => d + c * i ≡ r [MOD m]).card ≤ L := by
  calc
    _ ≤ (range L).card := by
      apply card_le_card_of_injOn (fun i => i / m)
      · intro i hi
        exact mem_range.mpr (Nat.div_lt_iff_lt_mul hm |>.mpr (mem_range.mp (mem_filter.mp hi).1))
      · intro i hi j hj h
        change i / m = j / m at h
        have hc' := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
        have he := mul_cancel_mod hc (Nat.ModEq.add_left_cancel' d hc')
        change i % m = j % m at he
        calc
          i = m * (i / m) + i % m := (Nat.div_add_mod i m).symm
          _ = m * (j / m) + j % m := by rw [h, he]
          _ = j := Nat.div_add_mod j m
    _ = _ := card_range _

private theorem residue_mono {S T : Finset ℕ} (h : S ⊆ T) (m r : ℕ) :
    residueCount S m r ≤ residueCount T m r := by
  exact card_le_card fun _ hx => mem_filter.mpr ⟨h (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩

private theorem residue_dvd_le (S : Finset ℕ) {m M r s : ℕ} (hd : m ∣ M) (h : s ≡ r [MOD m]) :
    residueCount S M s ≤ residueCount S m r := by
  exact card_le_card fun _ hx => mem_filter.mpr
    ⟨(mem_filter.mp hx).1, ((mem_filter.mp hx).2.of_dvd hd).trans h⟩

private theorem residue_congr (S : Finset ℕ) {m r s : ℕ} (h : r ≡ s [MOD m]) :
    residueCount S m r = residueCount S m s :=
  le_antisymm (residue_dvd_le S dvd_rfl h) (residue_dvd_le S dvd_rfl h.symm)

private def safe (old : Finset ℕ) (m n : ℕ) : Prop := residueCount old m n ≤ 784

private instance (old : Finset ℕ) (m n : ℕ) : Decidable (safe old m n) :=
  inferInstanceAs (Decidable (residueCount old m n ≤ 784))

private theorem safe_union {old fresh : Finset ℕ} {m M : ℕ} (hd : m ∣ M)
    (hOld : ∀ r, residueCount old m r ≤ 1567) (hNew : ∀ r, residueCount fresh M r ≤ 783)
    (hsafe : ∀ n ∈ fresh, safe old M n) (r : ℕ) :
    residueCount (old ∪ fresh) M r ≤ 1567 := by
  by_cases hgood : safe old M r
  · have hc : residueCount (old ∪ fresh) M r ≤ residueCount old M r + residueCount fresh M r := by
      unfold residueCount
      rw [Finset.filter_union]
      exact card_union_le _ _
    exact hc.trans (Nat.add_le_add hgood (hNew r))
  · have hn : ∀ n ∈ fresh, ¬ n ≡ r [MOD M] := by
      intro n hn hr
      have h := hsafe n hn
      unfold safe at h hgood
      exact hgood ((residue_congr old hr) ▸ h)
    have hle : residueCount (old ∪ fresh) M r ≤ residueCount old M r := by
      apply card_le_card
      intro x hx
      obtain ⟨hm, hr⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_union.mp hm).resolve_right (fun h => hn x h hr), hr⟩
    exact hle.trans ((residue_dvd_le old hd (Nat.ModEq.rfl : r ≡ r [MOD m])).trans (hOld r))

private theorem unsafe_count_le_one {old S : Finset ℕ} {m M : ℕ} (hd : m ∣ M)
    (hOld : ∀ r, residueCount old m r ≤ 1567)
    (hsame : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m])
    (hinj : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD M] → x = y) :
    (S.filter fun x => ¬ safe old M x).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxS, hxN⟩ := mem_filter.mp hx
  obtain ⟨hyS, hyN⟩ := mem_filter.mp hy
  by_contra hne
  have hc := no_two_large_children old hd (hsame x hxS y hyS) (fun h => hne (hinj x hxS y hyS h))
    (show residueCount old m x ≤ 2 * 784 + 1 by have := hOld x; omega)
  unfold safe at hxN hyN
  exact hc ⟨by omega, by omega⟩

private theorem enlarge_subset {γ : Type*} [DecidableEq γ] {S T : Finset γ} {r : ℕ}
    (h : S ⊆ T) (h₁ : S.card ≤ r) (h₂ : r ≤ T.card) :
    ∃ U, S ⊆ U ∧ U ⊆ T ∧ U.card = r := by
  have hsd := card_sdiff_of_subset h
  obtain ⟨D, hD, hcard⟩ := exists_subset_card_eq (s := T \ S) (n := r - S.card) (by omega)
  have hdisj : Disjoint S D := by
    rw [disjoint_left]
    intro z hz hzD
    exact (mem_sdiff.mp (hD hzD)).2 hz
  refine ⟨S ∪ D, subset_union_left, union_subset h (hD.trans sdiff_subset), ?_⟩
  rw [card_union_of_disjoint hdisj, hcard]
  omega

private theorem matching_subsets {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A A₀ : Finset α} {B B₀ : Finset β} (ha : A₀ ⊆ A) (hb : B₀ ⊆ B)
    (hab : A₀.card ≤ B.card) (hba : B₀.card ≤ A.card) :
    ∃ X Y, A₀ ⊆ X ∧ X ⊆ A ∧ B₀ ⊆ Y ∧ Y ⊆ B ∧ X.card = Y.card := by
  obtain ⟨X, hXA₀, hXA, hX⟩ := enlarge_subset ha (le_max_left _ _) (max_le (card_le_card ha) hba)
  obtain ⟨Y, hYB₀, hYB, hY⟩ := enlarge_subset hb (le_max_right _ _) (max_le hab (card_le_card hb))
  exact ⟨X, Y, hXA₀, hXA, hYB₀, hYB, hX.trans hY.symm⟩

private def quotientSum (m : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range k, m k / m i

private theorem quotient_budget (m : ℕ → ℕ) (hbase : 18 ≤ m 0)
    (hpos : ∀ i, 0 < m i) (hdiv : ∀ i j, i ≤ j → m i ∣ m j)
    (hstep : ∀ i, ∃ d ≥ 2, m (i+1) = d * m i) (k : ℕ) :
    9 * quotientSum m k + 18 ≤ m k := by
  induction k with
  | zero => simpa [quotientSum] using hbase
  | succ k ih =>
    obtain ⟨d, hd, hdk⟩ := hstep k
    have heq : quotientSum m (k+1) = d * quotientSum m k + d := by
      unfold quotientSum
      rw [sum_range_succ, hdk, Nat.mul_div_cancel _ (hpos k), mul_sum]
      congr 1
      apply sum_congr rfl
      intro i hi
      exact Nat.mul_div_assoc d (hdiv i k (mem_range.mp hi).le)
    have hmul := Nat.mul_le_mul_left d ih
    rw [heq, hdk]
    calc
      _ ≤ d * (9 * quotientSum m k + 18) := by
        have hd' := Nat.mul_le_mul_left 9 hd
        simp only [Nat.mul_add]
        nlinarith
      _ ≤ _ := hmul

private theorem exists_separated_anchor (m c a : ℕ → ℕ) (k base : ℕ)
    (hpos : ∀ j, 0 < m j) (hdiv : ∀ j < k, m j ∣ m k)
    (hbudget : 9 * quotientSum m k < m k) :
    ∃ offset < m k, ∀ j < k, ∀ s < 3, ∀ t < 3,
      ¬ base + offset + s * c k ≡ a j + t * c j [MOD m j] := by
  let bad (j : ℕ) (st : ℕ × ℕ) :=
    (range (m k)).filter (fun u => base + u + st.1 * c k ≡ a j + st.2 * c j [MOD m j])
  let shifts := (range 3) ×ˢ (range 3)
  let forbidden := (range k).biUnion (fun j => shifts.biUnion (bad j))
  have hbound {j : ℕ} (hj : j < k) (st : ℕ × ℕ) : (bad j st).card ≤ m k / m j := by
    have h := period_fiber_bound 1 (base + st.1 * c k) (m j) (m k / m j)
      (a j + st.2 * c j) (hpos j) (by simp)
    rw [Nat.div_mul_cancel (hdiv j hj)] at h
    simpa only [bad, one_mul, add_right_comm] using h
  have htotal : forbidden.card ≤ 9 * quotientSum m k := by
    calc
      _ ≤ ∑ j ∈ range k, (shifts.biUnion (bad j)).card := card_biUnion_le
      _ ≤ ∑ j ∈ range k, 9 * (m k / m j) := by
        apply sum_le_sum
        intro j hj
        apply card_biUnion_le.trans
        calc
          _ ≤ ∑ _ ∈ shifts, m k / m j := sum_le_sum (fun st _ => hbound (mem_range.mp hj) st)
          _ = _ := by simp [shifts]
      _ = _ := by rw [quotientSum, mul_sum]
  have hn : forbidden.card < (range (m k)).card := by simpa using htotal.trans_lt hbudget
  obtain ⟨u, hu, hun⟩ := exists_mem_notMem_of_card_lt_card hn
  refine ⟨u, mem_range.mp hu, ?_⟩
  intro j hj s hs t ht h
  exact hun (mem_biUnion.mpr ⟨j, mem_range.mpr hj, mem_biUnion.mpr
    ⟨(s,t), mem_product.mpr ⟨mem_range.mpr hs, mem_range.mpr ht⟩, mem_filter.mpr ⟨hu,h⟩⟩⟩)

private def affine (U m c X s : ℕ) : ℕ := U + m * X + s * c

private def grid (U m c w : ℕ) : Finset ℕ :=
  (range w).biUnion (fun s => (range (261 * c)).image (fun X => affine U m c X s))

private theorem grid_mem {U m c w z : ℕ} : z ∈ grid U m c w ↔
    ∃ s < w, ∃ X < 261 * c, affine U m c X s = z := by
  simp only [grid, mem_biUnion, mem_range, mem_image]

private theorem affine_residue {U m c X s M : ℕ} (hm : M ∣ m) :
    affine U m c X s ≡ U + s * c [MOD M] := by
  have hzero : m * X ≡ 0 [MOD M] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hm X)
  simpa [affine] using (hzero.add_left U).add_right (s * c)

private theorem affine_inj {U m c X Y s t : ℕ} (hm : 0 < m) (hc : m.Coprime c)
    (hs : s < m) (ht : t < m) (he : affine U m c X s = affine U m c Y t) :
    X = Y ∧ s = t := by
  have h := (affine_residue (U := U) (X := X) (s := s) (c := c) (dvd_rfl : m ∣ m)).symm.trans
    (he ▸ affine_residue (U := U) (X := Y) (s := t) (c := c) (dvd_rfl : m ∣ m))
  have hst := small_mod_unique hs ht (mul_cancel_mod hc (by
    simpa only [Nat.mul_comm c s, Nat.mul_comm c t] using Nat.ModEq.add_left_cancel' U h))
  subst t
  exact ⟨Nat.mul_left_cancel hm (by unfold affine at he; omega), rfl⟩

private theorem affine_count {U m c s r : ℕ} (hc : 0 < c) (hcop : c.Coprime m) :
    (((range (261*c)).image (fun X => affine U m c X s)).filter
      (fun z => z ≡ r [MOD c])).card ≤ 261 := by
  let pool := (range (261*c)).filter (fun X => U + s*c + m*X ≡ r [MOD c])
  have he : ((range (261*c)).image (fun X => affine U m c X s)).filter
      (fun z => z ≡ r [MOD c]) = pool.image (fun X => affine U m c X s) := by
    ext z
    simp only [mem_filter, mem_image, mem_range, pool]
    constructor
    · rintro ⟨⟨X,hX,rfl⟩,hz⟩
      exact ⟨X, ⟨hX, by simpa [affine, Nat.add_right_comm] using hz⟩, rfl⟩
    · rintro ⟨X, ⟨hX,hz⟩,rfl⟩
      exact ⟨⟨X,hX,rfl⟩, by simpa [affine, Nat.add_right_comm] using hz⟩
  rw [he]
  exact card_image_le.trans (period_fiber_bound m (U+s*c) c 261 r hc hcop)

private theorem grid_cap {U m c w r : ℕ} (hc : 0 < c) (hcop : c.Coprime m) :
    residueCount (grid U m c w) c r ≤ w * 261 := by
  calc
    _ ≤ ((range w).biUnion (fun s =>
        ((range (261*c)).image (fun X => affine U m c X s)).filter (fun z => z ≡ r [MOD c]))).card := by
      apply card_le_card
      intro z hz
      obtain ⟨hz',hzr⟩ := mem_filter.mp hz
      obtain ⟨s, hs, hzs⟩ := mem_biUnion.mp hz'
      exact mem_biUnion.mpr ⟨s,hs,mem_filter.mpr ⟨hzs,hzr⟩⟩
    _ ≤ ∑ s ∈ range w, (((range (261*c)).image (fun X => affine U m c X s)).filter
      (fun z => z ≡ r [MOD c])).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range w, 261 := sum_le_sum (fun _ _ => affine_count hc hcop)
    _ = _ := by simp

private def bucket (P Q x : ℕ) : Finset ℕ :=
  (range P).filter (fun y => P*x ≤ Q*y ∧ Q*y < P*(x+1))

private theorem bucket_size {P Q x : ℕ} (hQ : 0 < Q) (hPQ : Q < P)
    (hupper : P < 2*Q) (hx : x < Q) :
    1 ≤ (bucket P Q x).card ∧ (bucket P Q x).card ≤ 2 := by
  let y := (P*x+Q-1)/Q
  have hyLo : P*x ≤ Q*y := by
    have h := Nat.div_add_mod (P*x+Q-1) Q
    have hm := Nat.mod_lt (P*x+Q-1) hQ
    change Q*y + (P*x+Q-1)%Q = P*x+Q-1 at h
    omega
  have hyHi : Q*y ≤ P*x+Q-1 := by
    exact Nat.mul_div_le _ _
  have hyTop : Q*y < P*(x+1) := by rw [Nat.mul_succ]; omega
  have hyP : y < P := by
    have h := Nat.mul_le_mul_left P (show x+1 ≤ Q by omega)
    rw [Nat.mul_comm P Q] at h
    exact Nat.lt_of_mul_lt_mul_left (hyTop.trans_le h)
  have hy : y ∈ bucket P Q x := mem_filter.mpr ⟨mem_range.mpr hyP,hyLo,hyTop⟩
  refine ⟨card_pos.mpr ⟨y,hy⟩, ?_⟩
  calc
    _ ≤ (Ico y (y+2)).card := by
      apply card_le_card
      intro z hz
      obtain ⟨_, hzLo,hzHi⟩ := mem_filter.mp hz
      rw [Nat.mul_succ] at hzHi
      apply mem_Ico.mpr
      constructor
      · by_contra! h
        have hm := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at hm
        omega
      · by_contra! h
        have hm := Nat.mul_le_mul_left Q h
        rw [Nat.mul_add, Nat.mul_comm Q 2] at hm
        omega
    _ = _ := by simp

private theorem shifted_congr {m d c a i j : ℕ} (hm : 0 < m) (hc : d.Coprime c)
    (h : a + (c*i)*m ≡ a + (c*j)*m [MOD d*m]) : i ≡ j [MOD d] := by
  exact mul_cancel_mod hc (Nat.ModEq.mul_right_cancel' hm.ne' (Nat.ModEq.add_left_cancel' a h))

private theorem shifted_parent {m c a i j : ℕ} :
    a + (c*i)*m ≡ a + (c*j)*m [MOD m] := by
  have step (z : ℕ) : (c*z)*m ≡ 0 [MOD m] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left m (c*z))
  exact (Nat.ModEq.rfl.add (step i)).trans (Nat.ModEq.rfl.add (step j)).symm

private theorem unsafe_shifts_congr {old : Finset ℕ} {m d c a i j : ℕ}
    (hm : 0 < m) (hc : d.Coprime c) (hOld : ∀ r, residueCount old m r ≤ 1567)
    (hi : ¬ safe old (d*m) (a + (c*i)*m)) (hj : ¬ safe old (d*m) (a + (c*j)*m)) :
    i ≡ j [MOD d] := by
  by_contra hne
  have hneq : ¬ a + (c*i)*m ≡ a + (c*j)*m [MOD d*m] :=
    fun h => hne (shifted_congr hm hc h)
  have hsum := no_two_large_children old (dvd_mul_left m d) shifted_parent hneq
    (show residueCount old m (a+(c*i)*m) ≤ 2*784+1 by have := hOld (a+(c*i)*m); omega)
  unfold safe at hi hj
  exact hsum ⟨by omega,by omega⟩

private theorem safe_shift_count {old : Finset ℕ} {m d a w : ℕ}
    (hm : 0 < m) (hw : w ≤ d) (hOld : ∀ r, residueCount old m r ≤ 1567) :
    w - 1 ≤ ((range w).filter fun i => safe old (d*m) (a+i*m)).card := by
  have hbad : ((range w).filter fun i => ¬ safe old (d*m) (a+i*m)).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    obtain ⟨hwi,hsi⟩ := mem_filter.mp hi
    obtain ⟨hwj,hsj⟩ := mem_filter.mp hj
    exact small_mod_unique ((mem_range.mp hwi).trans_le hw) ((mem_range.mp hwj).trans_le hw)
      (unsafe_shifts_congr (c := 1) hm (by simp) hOld (by simpa using hsi) (by simpa using hsj))
  have he := card_filter_add_card_filter_not (s := range w) (fun i => safe old (d*m) (a+i*m))
  rw [card_range] at he
  omega

private def aValue (k U x t s : ℕ) : ℕ := affine U (p k) (q k) (x+q k*t) s

private def bValue (k V y t u : ℕ) : ℕ := affine V (q k) (p k) (y+p k*t) u

private def aPool (old : Finset ℕ) (k U x t : ℕ) : Finset ℕ :=
  (range 3).filter (fun s => safe old (q (k+1)) (aValue k U x t s))

private def bPool (old : Finset ℕ) (k V x t : ℕ) : Finset (ℕ×ℕ) :=
  ((bucket (p k) (q k) x) ×ˢ (range 2)).filter
    (fun yu => safe old (p (k+1)) (bValue k V yu.1 t yu.2))

private theorem aPool_lower {old : Finset ℕ} {k U x t : ℕ}
    (hOld : ∀ r, residueCount old (q k) r ≤ 1567) :
    2 ≤ (aPool old k U x t).card := by
  have h := safe_shift_count (w := 3) (d := 3) (a := U+p k*(x+q k*t))
    (scale_bounds k).1 le_rfl hOld
  simpa only [aPool, aValue, affine, q_step] using h

private theorem bShift_exists {old : Finset ℕ} {k V y t : ℕ}
    (hOld : ∀ r, residueCount old (p k) r ≤ 1567) :
    ∃ u < 2, safe old (p (k+1)) (bValue k V y t u) := by
  have h : 1 ≤ ((range 2).filter (fun u => safe old (p (k+1)) (bValue k V y t u))).card := by
    rcases p_step k with he | he
    · simpa only [he, bValue, affine] using safe_shift_count (w := 2) (d := 2)
        (a := V+q k*(y+p k*t)) (p_pos k) le_rfl hOld
    · simpa only [he, bValue, affine] using safe_shift_count (w := 2) (d := 4)
        (a := V+q k*(y+p k*t)) (p_pos k) (by decide) hOld
  obtain ⟨u,hu⟩ := card_pos.mp h
  exact ⟨u, mem_range.mp (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩

private theorem bPool_lower {old : Finset ℕ} {k V x t : ℕ}
    (hOld : ∀ r, residueCount old (p k) r ≤ 1567) :
    (bucket (p k) (q k) x).card ≤ (bPool old k V x t).card := by
  refine (card_le_card (t := (bPool old k V x t).image Prod.fst) ?_).trans card_image_le
  intro y hy
  obtain ⟨u,hu,hs⟩ := bShift_exists (V := V) (y := y) (t := t) hOld
  exact mem_image.mpr ⟨(y,u),mem_filter.mpr ⟨mem_product.mpr ⟨hy,mem_range.mpr hu⟩,hs⟩,rfl⟩

private structure CellPick (oldA oldB : Finset ℕ) (k U V x t : ℕ) where
  left : Finset ℕ
  right : Finset (ℕ×ℕ)
  left_safe : left ⊆ aPool oldA k U x t
  right_safe : right ⊆ bPool oldB k V x t
  force_left : ∀ s ∈ aPool oldA k U x t, s = 0 → s ∈ left
  force_right : ∀ yu ∈ bPool oldB k V x t, yu.2 = 0 → yu ∈ right
  equal : left.card = right.card

private theorem cell_pick_exists {oldA oldB : Finset ℕ} {k U V x t : ℕ}
    (hx : x < q k)
    (hA : ∀ r, residueCount oldA (q k) r ≤ 1567) (hB : ∀ r, residueCount oldB (p k) r ≤ 1567) :
    Nonempty (CellPick oldA oldB k U V x t) := by
  let X := aPool oldA k U x t
  let Y := bPool oldB k V x t
  let X₀ := X.filter (· = 0)
  let Y₀ := Y.filter (fun yu => yu.2 = 0)
  obtain ⟨hq,hqp,hup⟩ := scale_bounds k
  have hb := bucket_size hq hqp hup hx
  have hx₀ : X₀.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
  have hy₀ : Y₀.card ≤ (bucket (p k) (q k) x).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro a ha
      exact (mem_product.mp (mem_filter.mp (mem_filter.mp ha).1).1).1
    · intro a ha b hb h
      exact Prod.ext h ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  obtain ⟨L,R,hL₀,hL,hR₀,hR,hEq⟩ := matching_subsets (filter_subset _ X) (filter_subset _ Y)
    (hx₀.trans (hb.1.trans (bPool_lower hB))) (hy₀.trans (hb.2.trans (aPool_lower hA)))
  exact ⟨⟨L,R,hL,hR,fun s hs h => hL₀ (mem_filter.mpr ⟨hs,h⟩),
    fun z hz h => hR₀ (mem_filter.mpr ⟨hz,h⟩), hEq⟩⟩

private theorem small_affine_solution {m c r : ℕ} (hm : 0 < m) (hc : c.Coprime m) :
    ∃ x < m, c*x ≡ r [MOD m] := by
  letI : NeZero m := ⟨hm.ne'⟩
  let u := ZMod.unitOfCoprime c hc
  let z : ZMod m := (↑(u⁻¹) : ZMod m) * r
  refine ⟨z.val, ZMod.val_lt z, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime c hc]
  change (u : ZMod m) * ((↑(u⁻¹) : ZMod m) * r) = r
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

private theorem coverage_parameters {P Q U V n : ℕ}
    (hQ : 0 < Q) (hPQ : Q < P) (hUp : P < 2*Q) (hcop : P.Coprime Q)
    (hU : P^2 ≤ U) (hU' : U < P^2+P)
    (hV : P^2 ≤ V) (hV' : V < P^2+Q)
    (hn : 16*P^2 ≤ n) (hn' : n ≤ 256*P^2) :
    ∃ x < Q, ∃ y < P, ∃ R, 12 ≤ R ∧ R ≤ 507 ∧ n = U+V+P*x+Q*y+(P*Q)*R := by
  have hP : 0 < P := hQ.trans hPQ
  have hbase : U+V ≤ n := by nlinarith
  let r := n-(U+V)
  obtain ⟨x,hx,hxmod⟩ := small_affine_solution (r := r) hQ hcop
  obtain ⟨y,hy,hymod⟩ := small_affine_solution (r := r) hP hcop.symm
  let base := U+V+P*x+Q*y
  have hbLo : 2*P^2 ≤ base := by dsimp [base]; omega
  have hbHi : base ≤ 2*P^2+2*(P*Q) := by
    dsimp [base]
    have h₁ := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hx)
    have h₂ := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt hy)
    rw [Nat.mul_succ] at h₁ h₂
    rw [Nat.mul_comm Q P] at h₂
    omega
  have hsmall : P*Q ≤ P^2 := by
    simpa only [sq] using Nat.mul_le_mul_left P hPQ.le
  have hle : base ≤ n := by omega
  have hmodP : base ≡ n [MOD P] := by
    have hxzero : P*x ≡ 0 [MOD P] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
    have h := ((Nat.ModEq.rfl : U+V ≡ U+V [MOD P]).add hxzero).add hymod
    simpa only [base,add_zero, r, Nat.add_sub_of_le hbase] using h
  have hmodQ : base ≡ n [MOD Q] := by
    have hyzero : Q*y ≡ 0 [MOD Q] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
    have h := ((Nat.ModEq.rfl : U+V ≡ U+V [MOD Q]).add hxmod).add hyzero
    simpa only [base,add_zero, r, Nat.add_sub_of_le hbase] using h
  obtain ⟨R,hR⟩ := (Nat.modEq_iff_dvd' hle).mp
    ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmodP,hmodQ⟩)
  have he : n = base+(P*Q)*R := by omega
  refine ⟨x,hx,y,hy,R,?_,?_,he⟩
  · by_contra! hr
    have hmul := Nat.mul_le_mul_left (P*Q) (show R ≤ 11 by omega)
    nlinarith
  · by_contra! hr
    have hmul := Nat.mul_le_mul_left (P*Q) (show 508 ≤ R by omega)
    have hprod := Nat.mul_lt_mul_of_pos_left hUp hP
    rw [← mul_assoc, Nat.mul_comm P 2, mul_assoc, ← sq] at hprod
    nlinarith

private theorem uniform_residue_card {S : Finset ℕ} {m L : ℕ} (hm : 0 < m)
    (hS : S ⊆ range (L*m)) (hc : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m]) : S.card ≤ L := by
  by_cases hs : S.Nonempty
  · obtain ⟨r,hr⟩ := hs
    calc
      _ ≤ ((range (L*m)).filter (fun i => 0+1*i ≡ r [MOD m])).card := by
        apply card_le_card
        intro i hi
        exact mem_filter.mpr ⟨hS hi, by simpa using hc i hi r hr⟩
      _ ≤ _ := period_fiber_bound 1 0 m L r hm (by simp)
  · simp [not_nonempty_iff_eq_empty.mp hs]

private theorem safe_phase_pair {oldA oldB : Finset ℕ} {k U V x y R : ℕ}
    (ha : ∀ r, residueCount oldA (q k) r ≤ 1567)
    (hb : ∀ r, residueCount oldB (p k) r ≤ 1567)
    (hR₁ : 12 ≤ R) (hR₂ : R ≤ 507) :
    ∃ t, t ≤ 260 ∧ R-t ≤ 260 ∧ t ≤ R ∧
      safe oldA (q (k+1)) (aValue k U x t 0) ∧
      safe oldB (p (k+1)) (bValue k V y (R-t) 0) := by
  let lo := R - 260
  let badA := (range 13).filter (fun i => ¬ safe oldA (q (k+1)) (aValue k U x (lo+i) 0))
  let badB := (range 13).filter (fun i => ¬ safe oldB (p (k+1)) (bValue k V y (R-(lo+i)) 0))
  have hA : badA.card ≤ 5 := by
    apply uniform_residue_card (m := 3) (by decide)
    · exact (filter_subset _ _).trans (range_mono (by decide))
    · intro i hi j hj
      have hc : (3 : ℕ).Coprime (p k) :=
        Nat.Coprime.of_dvd_left (dvd_mul_of_dvd_left (by decide : 3 ∣ 27) _) (p_coprime k k).symm
      have he (l : ℕ) :
          aValue k U x (lo+l) 0 = (U + p k * (x+q k*lo)) + (p k*l)*q k := by
        simp only [aValue,affine,zero_mul,add_zero]
        ring
      apply unsafe_shifts_congr (scale_bounds k).1 hc ha
      · simpa only [q_step, he] using (mem_filter.mp hi).2
      · simpa only [q_step, he] using (mem_filter.mp hj).2
  have hB : badB.card ≤ 7 := by
    apply uniform_residue_card (m := 2) (by decide)
    · exact (filter_subset _ _).trans (range_mono (by decide))
    · intro i hi j hj
      have hii : i < 13 := mem_range.mp (mem_filter.mp hi).1
      have hjj : j < 13 := mem_range.mp (mem_filter.mp hj).1
      have hc₂ := Nat.coprime_two_left.mpr (q_odd k)
      obtain ⟨d,hd,hstep⟩ : ∃ d, (d=2 ∨ d=4) ∧ p (k+1)=d*p k := by
        rcases p_step k with h | h
        · exact ⟨2,Or.inl rfl,h⟩
        · exact ⟨4,Or.inr rfl,h⟩
      have hc : d.Coprime (q k) := by
        rcases hd with rfl | rfl
        · exact hc₂
        · exact hc₂.pow_left 2
      have hdvd : 2 ∣ d := by rcases hd with rfl | rfl <;> decide
      have he (l : ℕ) : bValue k V y l 0 = (V+q k*y)+(q k*l)*p k := by
        simp only [bValue,affine,zero_mul,add_zero]
        ring
      have hg : R-(lo+i) ≡ R-(lo+j) [MOD d] := by
        apply unsafe_shifts_congr (p_pos k) hc hb
        · simpa only [hstep, he] using (mem_filter.mp hi).2
        · simpa only [hstep, he] using (mem_filter.mp hj).2
      have h := (hg.of_dvd hdvd).sub_left (Nat.sub_le _ _) (Nat.sub_le _ _)
      have hli : R - (R - (lo+i)) = lo+i := by dsimp [lo]; omega
      have hlj : R - (R - (lo+j)) = lo+j := by dsimp [lo]; omega
      rw [hli,hlj] at h
      exact Nat.ModEq.add_left_cancel' lo h
  have hc : (badA ∪ badB).card < (range 13).card := by
    have := card_union_le badA badB
    simp only [card_range]
    omega
  obtain ⟨i,hi,hgood⟩ := exists_mem_notMem_of_card_lt_card hc
  have hlt := mem_range.mp hi
  refine ⟨lo+i, by dsimp [lo]; omega, by dsimp [lo]; omega, by dsimp [lo]; omega, ?_, ?_⟩
  · by_contra hn
    exact hgood (mem_union.mpr (Or.inl (mem_filter.mpr ⟨hi,hn⟩)))
  · by_contra hn
    exact hgood (mem_union.mpr (Or.inr (mem_filter.mpr ⟨hi,hn⟩)))

private theorem phase_index_lt {m x t : ℕ} (hx : x < m) (ht : t < 261) :
    x+m*t < 261*m := by
  have h := Nat.mul_le_mul_left m (show t ≤ 260 by omega)
  simpa only [mul_comm m 260] using (show x+m*t < 261*m by omega)

private theorem phase_index_inj {m x y t u : ℕ} (hm : 0 < m)
    (hx : x < m) (hy : y < m) (he : x+m*t = y+m*u) : x = y ∧ t = u := by
  have hmod := congrArg (fun n : ℕ => n % m) he
  have hxy : x = y := by simpa [Nat.add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hmod
  exact ⟨hxy,Nat.mul_left_cancel hm (by omega)⟩

private theorem affine_near {k U V x y t s u : ℕ}
    (hU : p k^2 ≤ U) (hU' : U < p k^2+p k)
    (hV : p k^2 ≤ V) (hV' : V < p k^2+q k)
    (hy : y ∈ bucket (p k) (q k) x) (hs : s < 3) (hu : u < 2) :
    aValue k U x t s ≤ bValue k V y t u + 5*p k ∧
      bValue k V y t u ≤ aValue k U x t s + 5*p k := by
  have hqp := (scale_bounds k).2.1
  obtain ⟨_,hlo,hhi⟩ := mem_filter.mp hy
  rw [Nat.mul_succ] at hhi
  have hsq := Nat.mul_le_mul_right (q k) (show s ≤ 2 by omega)
  have hup := Nat.mul_le_mul_right (p k) (show u ≤ 1 by omega)
  simp only [aValue,bValue,affine,Nat.mul_add,Nat.mul_left_comm (q k) (p k)]
  omega

private theorem grid_range {U P m c w z : ℕ} (hP : 32 ≤ P) (hm : m ≤ P) (hc : c ≤ P)
    (hw : w ≤ 3) (hlo : P^2 ≤ U) (hhi : U < P^2+P) (hz : z ∈ grid U m c w) :
    P^2 ≤ z ∧ z ≤ 263*P^2 := by
  obtain ⟨s,hs,X,hX,rfl⟩ := grid_mem.mp hz
  have h₁ := Nat.mul_le_mul hm (hX.le.trans (Nat.mul_le_mul_left 261 hc))
  have h₂ := Nat.mul_le_mul (show s ≤ 2 by omega) hc
  constructor
  · unfold affine; omega
  · unfold affine
    have h₃ := Nat.mul_le_mul_left P (show 3 ≤ P by omega)
    nlinarith

private noncomputable def familyEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → Finset ℕ) (hF : ∀ i j, i ≠ j → Disjoint (F i) (F j)) :
    (Σ i, ↥(F i)) ≃ ↥(univ.biUnion F) := by
  classical
  let pack (x : Σ i, ↥(F i)) : ↥(univ.biUnion F) :=
    ⟨x.2.val, mem_biUnion.mpr ⟨x.1, mem_univ _, x.2.property⟩⟩
  apply Equiv.ofBijective pack
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hab : a.val = b.val := congrArg Subtype.val he
    by_cases hij : i = j
    · subst j
      have h : a = b := Subtype.ext hab
      subst b
      rfl
    · exact (Finset.disjoint_left.mp (hF i j hij) a.property (hab.symm ▸ b.property)).elim
  · intro a
    obtain ⟨i,_,ha⟩ := mem_biUnion.mp a.property
    exact ⟨⟨i,⟨a.val,ha⟩⟩,Subtype.ext rfl⟩

private def cellIndex (k : ℕ) := Fin (q k) × Fin 261
  deriving DecidableEq, Fintype

private structure LocalBlock (oldA oldB : Finset ℕ) (k U V : ℕ) where
  A : Finset ℕ
  B : Finset ℕ
  pair : ↥A ≃ ↥B
  gridA : A ⊆ grid U (p k) (q k) 3
  gridB : B ⊆ grid V (q k) (p k) 2
  safeA : ∀ a ∈ A, safe oldA (q (k+1)) a
  safeB : ∀ b ∈ B, safe oldB (p (k+1)) b
  coverage : ∀ n, 16*p k^2 ≤ n → n ≤ 256*p k^2 → ∃ a ∈ A, ∃ b ∈ B, a+b=n
  near : ∀ a : ↥A, a.val ≤ (pair a).val + 5*p k ∧ (pair a).val ≤ a.val + 5*p k

private theorem local_block_exists {oldA oldB : Finset ℕ} {k U V : ℕ}
    (hU : p k^2 ≤ U) (hU' : U < p k^2+p k)
    (hV : p k^2 ≤ V) (hV' : V < p k^2+q k)
    (hOldA : ∀ r, residueCount oldA (q k) r ≤ 1567)
    (hOldB : ∀ r, residueCount oldB (p k) r ≤ 1567) :
    Nonempty (LocalBlock oldA oldB k U V) := by
  classical
  obtain ⟨hq,hqp,hupper⟩ := scale_bounds k
  let pick (i : cellIndex k) : CellPick oldA oldB k U V i.1.val i.2.val :=
    Classical.choice (cell_pick_exists i.1.isLt hOldA hOldB)
  let As (i : cellIndex k) := (pick i).left.image (aValue k U i.1.val i.2.val)
  let Bs (i : cellIndex k) := (pick i).right.image
    (fun yu => bValue k V yu.1 i.2.val yu.2)
  have ha {i : cellIndex k} {s : ℕ} (hs : s ∈ (pick i).left) :
      s < 3 ∧ safe oldA (q (k+1)) (aValue k U i.1.val i.2.val s) :=
    ⟨mem_range.mp (mem_filter.mp ((pick i).left_safe hs)).1, (mem_filter.mp ((pick i).left_safe hs)).2⟩
  have hb {i : cellIndex k} {yu : ℕ×ℕ} (hyu : yu ∈ (pick i).right) :
      yu.1 ∈ bucket (p k) (q k) i.1.val ∧ yu.2 < 2 ∧
        safe oldB (p (k+1)) (bValue k V yu.1 i.2.val yu.2) := by
    have h := mem_filter.mp ((pick i).right_safe hyu)
    exact ⟨(mem_product.mp h.1).1,mem_range.mp (mem_product.mp h.1).2,h.2⟩
  have hAInj {i j : cellIndex k} {s t : ℕ} (hs : s ∈ (pick i).left) (ht : t ∈ (pick j).left)
      (he : aValue k U i.1.val i.2.val s = aValue k U j.1.val j.2.val t) : i = j ∧ s = t := by
    have hP := p_base k
    obtain ⟨hX, hst⟩ := affine_inj (p_pos k) (p_coprime k k)
      ((ha hs).1.trans_le (by omega)) ((ha ht).1.trans_le (by omega)) he
    obtain ⟨hx,hy⟩ := phase_index_inj hq i.1.isLt j.1.isLt hX
    exact ⟨Prod.ext (Fin.ext hx) (Fin.ext hy),hst⟩
  have hBInj {i j : cellIndex k} {a b : ℕ×ℕ} (ha : a ∈ (pick i).right) (hb' : b ∈ (pick j).right)
      (he : bValue k V a.1 i.2.val a.2 = bValue k V b.1 j.2.val b.2) : i = j ∧ a = b := by
    have hQ : 27 ≤ q k := by
      have h := Nat.one_le_pow k 3 (by decide)
      simpa [q] using Nat.mul_le_mul_left 27 h
    obtain ⟨hY, hst⟩ := affine_inj hq (p_coprime k k).symm
      ((hb ha).2.1.trans_le (by omega)) ((hb hb').2.1.trans_le (by omega)) he
    have haP : a.1 < p k := mem_range.mp (mem_filter.mp (hb ha).1).1
    have hbP : b.1 < p k := mem_range.mp (mem_filter.mp (hb hb').1).1
    obtain ⟨hy,ht⟩ := phase_index_inj (p_pos k) haP hbP hY
    have cellOf {x y : ℕ} (h : y ∈ bucket (p k) (q k) x) :
        q k*y / p k = x := by
      obtain ⟨_,hl,hu⟩ := mem_filter.mp h
      rw [Nat.mul_comm (p k) x] at hl
      exact (Nat.div_eq_iff (p_pos k)).mpr ⟨hl, by rw [Nat.mul_succ, Nat.mul_comm (p k) x] at hu; omega⟩
    have hx := (cellOf (hb ha).1).symm.trans (hy ▸ cellOf (hb hb').1)
    exact ⟨Prod.ext (Fin.ext hx) (Fin.ext ht),Prod.ext hy hst⟩
  have disA (i j : cellIndex k) (hij : i ≠ j) : Disjoint (As i) (As j) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨s,hs,he⟩ := mem_image.mp hz
    obtain ⟨t,ht,he'⟩ := mem_image.mp hz'
    exact hij (hAInj hs ht (he.trans he'.symm)).1
  have disB (i j : cellIndex k) (hij : i ≠ j) : Disjoint (Bs i) (Bs j) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨s,hs,he⟩ := mem_image.mp hz
    obtain ⟨t,ht,he'⟩ := mem_image.mp hz'
    exact hij (hBInj hs ht (he.trans he'.symm)).1
  let e (i : cellIndex k) : ↥(As i) ≃ ↥(Bs i) :=
    Finset.equivOfCardEq (by
      have hca : (As i).card = (pick i).left.card :=
        card_image_iff.mpr (fun _ hs _ ht he => (hAInj hs ht he).2)
      have hcb : (Bs i).card = (pick i).right.card :=
        card_image_iff.mpr (fun _ hs _ ht he => (hBInj hs ht he).2)
      exact hca.trans ((pick i).equal.trans hcb.symm))
  let A := univ.biUnion As
  let B := univ.biUnion Bs
  let packA := familyEquiv As disA
  let packB := familyEquiv Bs disB
  let pairing : ↥A ≃ ↥B := packA.symm.trans ((Equiv.sigmaCongrRight e).trans packB)
  refine ⟨⟨A,B,pairing,?_,?_,?_,?_,?_,?_⟩⟩
  · intro a ha'
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp ha'
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hi
    exact grid_mem.mpr ⟨s,(ha hs).1,_,phase_index_lt i.1.isLt i.2.isLt,rfl⟩
  · intro b hb'
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hb'
    obtain ⟨yu,hyu,rfl⟩ := mem_image.mp hi
    exact grid_mem.mpr ⟨yu.2,(hb hyu).2.1,_,
      phase_index_lt (mem_range.mp (mem_filter.mp (hb hyu).1).1) i.2.isLt,rfl⟩
  · intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hi
    exact (ha hs).2
  · intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    obtain ⟨yu,hyu,rfl⟩ := mem_image.mp hi
    exact (hb hyu).2.2
  · intro n hn hn'
    obtain ⟨x,hx,y,hy,R,hR,hR',heq⟩ :=
      coverage_parameters hq hqp hupper (p_coprime k k) hU hU' hV hV' hn hn'
    obtain ⟨t,ht,hrt,htR,has,hbs⟩ :=
      safe_phase_pair (U := U) (V := V) (x := x) (y := y) hOldA hOldB hR hR'
    let i : cellIndex k := (⟨x,hx⟩,⟨t,by omega⟩)
    let j : cellIndex k := (⟨q k*y/p k, (Nat.div_lt_iff_lt_mul (p_pos k)).mpr
      (Nat.mul_lt_mul_of_pos_left hy hq)⟩,⟨R-t,by omega⟩)
    have hyj : y ∈ bucket (p k) (q k) j.1.val := by
      have hv := (Nat.div_eq_iff (p_pos k)).mp (rfl : q k*y/p k = j.1.val)
      change j.1.val * p k ≤ q k*y ∧ q k*y ≤ j.1.val * p k + p k - 1 at hv
      refine mem_filter.mpr ⟨mem_range.mpr hy,?_,?_⟩
      · simpa only [Nat.mul_comm (p k) j.1.val] using hv.1
      · rw [Nat.mul_succ, Nat.mul_comm (p k) j.1.val]
        omega
    have hmA : 0 ∈ (pick i).left := (pick i).force_left 0
      (mem_filter.mpr ⟨mem_range.mpr (by decide),has⟩) rfl
    have hmB : (y,0) ∈ (pick j).right := (pick j).force_right (y,0)
      (mem_filter.mpr ⟨mem_product.mpr ⟨hyj,mem_range.mpr (by norm_num)⟩,hbs⟩) rfl
    refine ⟨aValue k U x t 0, mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨0,hmA,rfl⟩⟩,
      bValue k V y (R-t) 0, mem_biUnion.mpr ⟨j,mem_univ _,mem_image.mpr ⟨(y,0),hmB,rfl⟩⟩,?_⟩
    calc
      _ = U+V+p k*x+q k*y+(p k*q k)*(t+(R-t)) := by
        simp only [aValue,bValue,affine,zero_mul,add_zero]
        ring
      _ = n := by rw [show t+(R-t)=R by omega, ← heq]
  · intro a
    rcases h : packA.symm a with ⟨i,z⟩
    have hpack : packA ⟨i,z⟩ = a := h ▸ packA.apply_symm_apply a
    have heB : pairing a = packB ⟨i,e i z⟩ := by simp [pairing, ← hpack]
    obtain ⟨s,hs,hes⟩ := mem_image.mp z.property
    obtain ⟨yu,hyu,heyu⟩ := mem_image.mp (e i z).property
    have haVal : a.val = aValue k U i.1.val i.2.val s := by
      rw [← hpack]
      exact hes.symm
    have hbVal : (pairing a).val = bValue k V yu.1 i.2.val yu.2 := heB ▸ heyu.symm
    rw [haVal,hbVal]
    exact affine_near hU hU' hV hV' (hb hyu).1 (ha hs).1 (hb hyu).2.1

private structure Block where
  U : ℕ
  V : ℕ
  A : Finset ℕ
  B : Finset ℕ
  pair : ↥A ≃ ↥B

private structure Valid (k : ℕ) (b : Block) : Prop where
  U_lo : p k^2 ≤ b.U
  U_hi : b.U < p k^2+p k
  V_lo : p k^2 ≤ b.V
  V_hi : b.V < p k^2+q k
  gridA : b.A ⊆ grid b.U (p k) (q k) 3
  gridB : b.B ⊆ grid b.V (q k) (p k) 2
  coverage : ∀ n, 16*p k^2 ≤ n → n ≤ 256*p k^2 → ∃ a ∈ b.A, ∃ c ∈ b.B, a+c=n
  near : ∀ a : ↥b.A, a.val ≤ (b.pair a).val + 5*p k ∧ (b.pair a).val ≤ a.val + 5*p k

private theorem valid_boundsA {k b a} (h : Valid k b) (ha : a ∈ b.A) :
    p k^2 ≤ a ∧ a ≤ 263*p k^2 :=
  grid_range (p_base k) le_rfl (scale_bounds k).2.1.le le_rfl h.U_lo h.U_hi (h.gridA ha)

private theorem valid_boundsB {k b a} (h : Valid k b) (ha : a ∈ b.B) :
    p k^2 ≤ a ∧ a ≤ 263*p k^2 := by
  have hqp := (scale_bounds k).2.1.le
  exact grid_range (p_base k) hqp le_rfl (by decide) h.V_lo (h.V_hi.trans_le (Nat.add_le_add_left hqp _)) (h.gridB ha)

private def prior (f : ℕ → Block) (side : Block → Finset ℕ) (k : ℕ) : Finset ℕ :=
  (range k).biUnion (fun i => side (f i))

private theorem prior_mem {f side k z} : z ∈ prior f side k ↔ ∃ i < k, z ∈ side (f i) := by
  simp only [prior,mem_biUnion,mem_range]

private theorem prior_step {f f' : ℕ → Block} {side : Block → Finset ℕ} {k : ℕ}
    (h : ∀ i < k, f' i = f i) :
    prior f' side (k+1) = prior f side k ∪ side (f' k) := by
  ext z
  simp only [prior_mem, mem_union]
  constructor
  · rintro ⟨i,hi,hz⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl
    · exact Or.inl ⟨i,hil,by rwa [h i hil] at hz⟩
    · exact Or.inr hz
  · rintro (⟨i,hi,hz⟩ | hz)
    · exact ⟨i,by omega,by rwa [h i hi]⟩
    · exact ⟨k,by omega,hz⟩

private structure Stage (k : ℕ) where
  blocks : ℕ → Block
  valid : ∀ i < k, Valid i (blocks i)
  disA : ∀ i < k, ∀ j < k, i < j → Disjoint (blocks i).A (blocks j).A
  disB : ∀ i < k, ∀ j < k, i < j → Disjoint (blocks i).B (blocks j).B
  capA : ∀ r, residueCount (prior blocks Block.A k) (q k) r ≤ 1567
  capB : ∀ r, residueCount (prior blocks Block.B k) (p k) r ≤ 1567

private def initial : Stage 0 where
  blocks := fun _ => ⟨0,0,∅,∅,Equiv.refl _⟩
  valid := fun i hi => (Nat.not_lt_zero i hi).elim
  disA := fun i hi => (Nat.not_lt_zero i hi).elim
  disB := fun i hi => (Nat.not_lt_zero i hi).elim
  capA := fun r => by simp [prior,residueCount]
  capB := fun r => by simp [prior,residueCount]

private theorem disjoint_grids {m M c C a A w W : ℕ} (hm : m ∣ M)
    (h : ∀ s < W, ∀ t < w, ¬ A+s*C ≡ a+t*c [MOD m]) :
    Disjoint (grid a m c w) (grid A M C W) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  obtain ⟨t,ht,y,_,rfl⟩ := grid_mem.mp hn
  obtain ⟨s,hs,x,_,he⟩ := grid_mem.mp hn'
  exact h s hs t ht ((affine_residue (U := A) (X := x) (s := s) (c := C) hm).symm.trans
    (he.symm ▸ affine_residue (U := a) (X := y) (s := t) (c := c) (dvd_rfl : m ∣ m)))

private theorem stage_next {k : ℕ} (S : Stage k) :
    ∃ T : Stage (k+1), ∀ i < k, T.blocks i = S.blocks i := by
  let base := p k ^ 2
  have hposQ (i : ℕ) : 0 < q i := (scale_bounds i).1
  have p_budget : 9 * quotientSum p k < p k := by
    have h := quotient_budget p (by decide) p_pos (fun _ _ => p_dvd)
      (fun i => by rcases p_step i with h | h; exact ⟨2,by decide,h⟩; exact ⟨4,by decide,h⟩) k
    omega
  have q_budget : 9 * quotientSum q k < q k := by
    have h := quotient_budget q (by decide) hposQ (fun _ _ => q_dvd)
      (fun i => ⟨3,by decide,q_step i⟩) k
    omega
  obtain ⟨u,hu,hU⟩ := exists_separated_anchor p q (fun j => (S.blocks j).U) k base p_pos
    (fun j hj => p_dvd hj.le) p_budget
  obtain ⟨v,hv,hV⟩ := exists_separated_anchor q p (fun j => (S.blocks j).V) k base hposQ
    (fun j hj => q_dvd hj.le) q_budget
  let U := base+u
  let V := base+v
  have hU₁ : p k^2 ≤ U := by dsimp [U,base]; omega
  have hU₂ : U < p k^2+p k := by dsimp [U,base]; omega
  have hV₁ : p k^2 ≤ V := by dsimp [V,base]; omega
  have hV₂ : V < p k^2+q k := by dsimp [V,base]; omega
  obtain ⟨chosen⟩ := local_block_exists hU₁ hU₂ hV₁ hV₂ S.capA S.capB
  let b : Block := ⟨U,V,chosen.A,chosen.B,chosen.pair⟩
  let next (i : ℕ) := if i=k then b else S.blocks i
  have hagree (i : ℕ) (hi : i < k) : next i = S.blocks i := if_neg hi.ne
  have hb : next k = b := if_pos rfl
  have hvalid : Valid k b :=
    ⟨hU₁,hU₂,hV₁,hV₂,chosen.gridA,chosen.gridB,chosen.coverage,chosen.near⟩
  have valid' (i : ℕ) (hi : i < k+1) : Valid i (next i) := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hl | rfl
    · rw [hagree i hl]
      exact S.valid i hl
    · rwa [hb]
  have disjoint_newA (i : ℕ) (hi : i < k) : Disjoint (S.blocks i).A b.A := by
    apply (disjoint_grids (p_dvd hi.le) (hU i hi)).mono (S.valid i hi).gridA hvalid.gridA
  have disjoint_newB (i : ℕ) (hi : i < k) : Disjoint (S.blocks i).B b.B := by
    apply (disjoint_grids (q_dvd hi.le) (w := 2) (W := 2)
      (fun s hs t ht => hV i hi s (by omega) t (by omega))).mono (S.valid i hi).gridB hvalid.gridB
  refine ⟨⟨next,valid',?_,?_,?_,?_⟩,hagree⟩
  · intro i hi j hj hij
    have hik : i < k := by omega
    rw [hagree i hik]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
    · rw [hagree j hj']
      exact S.disA i hik j hj' hij
    · rw [hb]
      exact disjoint_newA i hik
  · intro i hi j hj hij
    have hik : i < k := by omega
    rw [hagree i hik]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
    · rw [hagree j hj']
      exact S.disB i hik j hj' hij
    · rw [hb]
      exact disjoint_newB i hik
  · intro r
    rw [prior_step hagree,hb]
    apply safe_union (q_dvd (Nat.le_succ k)) S.capA _ chosen.safeA
    intro z
    exact (residue_dvd_le b.A (q_dvd (Nat.le_succ k)) (Nat.ModEq.rfl)).trans
      ((residue_mono hvalid.gridA _ _).trans (grid_cap (hposQ k) (p_coprime k k).symm))
  · intro r
    rw [prior_step hagree,hb]
    apply safe_union (p_dvd (Nat.le_succ k)) S.capB _ chosen.safeB
    intro z
    exact (residue_dvd_le b.B (p_dvd (Nat.le_succ k)) (Nat.ModEq.rfl)).trans
      ((residue_mono hvalid.gridB _ _).trans ((grid_cap (p_pos k) (p_coprime k k)).trans (by decide)))

private noncomputable def stages : (k : ℕ) → Stage k
  | 0 => initial
  | k+1 => (stage_next (stages k)).choose

private noncomputable def blocks (i : ℕ) : Block := (stages (i+1)).blocks i

private theorem stage_agrees {i k : ℕ} (hi : i < k) : (stages k).blocks i = blocks i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
    · exact ((stage_next (stages k)).choose_spec i h).trans (ih h)
    · rfl

private theorem block_valid (i : ℕ) : Valid i (blocks i) :=
  (stages (i+1)).valid i (Nat.lt_succ_self i)

private theorem blocks_disjA {i j : ℕ} (h : i < j) : Disjoint (blocks i).A (blocks j).A := by
  rw [← stage_agrees (Nat.lt_succ_of_lt h),← stage_agrees (Nat.lt_succ_self j)]
  exact (stages (j+1)).disA i (Nat.lt_succ_of_lt h) j (Nat.lt_succ_self j) h

private theorem blocks_disjB {i j : ℕ} (h : i < j) : Disjoint (blocks i).B (blocks j).B := by
  rw [← stage_agrees (Nat.lt_succ_of_lt h),← stage_agrees (Nat.lt_succ_self j)]
  exact (stages (j+1)).disB i (Nat.lt_succ_of_lt h) j (Nat.lt_succ_self j) h

private theorem prior_agrees (side : Block → Finset ℕ) (k : ℕ) :
    prior blocks side k = prior (stages k).blocks side k := by
  ext x
  simp only [prior_mem]
  exact exists_congr fun i => and_congr_right fun hi => by rw [stage_agrees hi]

private theorem global_capA (k z : ℕ) : residueCount (prior blocks Block.A k) (q k) z ≤ 1567 := by
  rw [prior_agrees]
  exact (stages k).capA z

private theorem global_capB (k z : ℕ) : residueCount (prior blocks Block.B k) (p k) z ≤ 1567 := by
  rw [prior_agrees]
  exact (stages k).capB z

private def unionSet (F : ℕ → Finset ℕ) : Set ℕ := {x | ∃ k, x ∈ F k}

private noncomputable def A : Set ℕ := unionSet (fun k => (blocks k).A)
private noncomputable def B : Set ℕ := unionSet (fun k => (blocks k).B)

private theorem scale_ge (k : ℕ) : k+32 ≤ p k := by
  induction k with
  | zero => decide
  | succ k ih => have := p_grow k; omega

private theorem p_upper (k : ℕ) : p (k+1) ≤ 4*p k := by
  rcases p_step k with h | h <;> omega

private theorem covering_scale {n : ℕ} (hn : 16384 ≤ n) :
    ∃ k, 16*p k^2 ≤ n ∧ n ≤ 256*p k^2 := by
  have hex : ∃ k, n ≤ 256*p k^2 := by
    refine ⟨n,?_⟩
    have hp := scale_ge n
    nlinarith
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  change n ≤ 256*p k^2 at hk
  refine ⟨k,?_,hk⟩
  cases h : k with
  | zero => simpa [p] using hn
  | succ k' =>
    have hl : k' < Nat.find hex := by change k'<k; omega
    have hprev := Nat.find_min hex hl
    have hp := Nat.pow_le_pow_left (p_upper k') 2
    rw [mul_pow] at hp
    nlinarith

private theorem cofinite : ∀ᶠ n : ℕ in atTop, n ∈ A+B := by
  filter_upwards [eventually_ge_atTop (16384 : ℕ)] with n hn
  obtain ⟨k,hlo,hhi⟩ := covering_scale hn
  obtain ⟨a,ha,b,hb,he⟩ := (block_valid k).coverage n hlo hhi
  exact Set.mem_add.mpr ⟨a,⟨k,ha⟩,b,⟨k,hb⟩,he⟩

private theorem A_infinite : A.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨a,ha,b,hb,he⟩ := (block_valid n).coverage (16*p n^2) le_rfl (by omega)
  have h := (valid_boundsA (block_valid n) ha).1
  have hp := scale_ge n
  exact ⟨a,⟨n,ha⟩,by nlinarith⟩

private theorem B_infinite : B.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨a,ha,b,hb,he⟩ := (block_valid n).coverage (16*p n^2) le_rfl (by omega)
  have h := (valid_boundsB (block_valid n) hb).1
  have hp := scale_ge n
  exact ⟨b,⟨n,hb⟩,by nlinarith⟩

private theorem representation_mem {S T : Set ℕ} {n : ℕ} {z : ℕ×ℕ} :
    z ∈ representations S T n ↔ z.1+z.2=n ∧ z.1∈S ∧ z.2∈T := by
  classical
  simp [representations,Finset.HasAntidiagonal.mem_antidiagonal]

private theorem representations_swap_card (S T : Set ℕ) (n : ℕ) :
    (representations S T n).card = (representations T S n).card := by
  classical
  have he : (representations S T n).image Prod.swap = representations T S n := by
    ext z
    rcases z with ⟨a,b⟩
    simp only [mem_image,representation_mem]
    constructor
    · rintro ⟨⟨c,d⟩,⟨h,hs,ht⟩,heq⟩
      injection heq with hda hcb
      change d = a at hda
      change c = b at hcb
      subst d; subst c
      exact ⟨by simpa [Nat.add_comm] using h,ht,hs⟩
    · rintro ⟨h,ht,hs⟩
      exact ⟨(b,a),⟨by simpa [Nat.add_comm] using h,hs,ht⟩,rfl⟩
  rw [← he,card_image_of_injective _ Prod.swap_injective]

private theorem residue_equation_cap (S : Finset ℕ) {m K : ℕ}
    (hS : ∀ r, residueCount S m r ≤ K) (n d : ℕ) :
    ((S.filter fun a => a+d ≡ n [MOD m]).card) ≤ K := by
  let F := S.filter (fun a => a+d ≡ n [MOD m])
  by_cases h : F.Nonempty
  · obtain ⟨r,hr⟩ := h
    refine (le_trans ?_ (hS r))
    apply card_le_card
    intro a ha
    obtain ⟨has,hac⟩ := mem_filter.mp ha
    have hsame := Nat.ModEq.add_right_cancel' d (hac.trans (mem_filter.mp hr).2.symm)
    exact mem_filter.mpr ⟨has,hsame⟩
  · change F.card ≤ K
    simp [not_nonempty_iff_eq_empty.mp h]

private theorem cross_grid_cap {S T : Finset ℕ} {U m c w K : ℕ}
    (hT : T ⊆ grid U m c w) (hS : ∀ r, residueCount S m r ≤ K) (n : ℕ) :
    (representations (S : Set ℕ) (T : Set ℕ) n).card ≤ w*K := by
  let F := (range w).biUnion (fun s => S.filter fun a => a+(U+s*c) ≡ n [MOD m])
  have hinj : (representations (S : Set ℕ) (T : Set ℕ) n).card ≤ F.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro z hz
      obtain ⟨he,ha,hb⟩ := representation_mem.mp hz
      obtain ⟨s,hs,X,_,hv⟩ := grid_mem.mp (hT hb)
      refine mem_biUnion.mpr ⟨s,mem_range.mpr hs,mem_filter.mpr ⟨ha,?_⟩⟩
      have hres := affine_residue (U := U) (X := X) (s := s) (c := c) (dvd_rfl : m ∣ m)
      rw [hv] at hres
      rw [← he]
      exact hres.symm.add_left _
    · intro x hx y hy h
      have hx' := (representation_mem.mp hx).1
      have hy' := (representation_mem.mp hy).1
      exact Prod.ext h (by omega)
  calc
    _ ≤ F.card := hinj
    _ ≤ ∑ s ∈ range w, (S.filter fun a => a+(U+s*c) ≡ n [MOD m]).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range w, K := sum_le_sum (fun s _ => residue_equation_cap S hS n (U+s*c))
    _ = _ := by simp

private theorem prior_cap_with_block (k r : ℕ) :
    residueCount (prior blocks Block.A (k+1)) (q k) r ≤ 2350 := by
  rw [prior_step (f := blocks) (by intros; rfl)]
  have hcap := global_capA k r
  have hfresh := (residue_mono (block_valid k).gridA _ r).trans
    (grid_cap (scale_bounds k).1 (p_coprime k k).symm)
  have h := card_union_le
    ((prior blocks Block.A k).filter (fun x => x ≡ r [MOD q k]))
    (((blocks k).A).filter (fun x => x ≡ r [MOD q k]))
  unfold residueCount at hcap hfresh ⊢
  rw [Finset.filter_union]
  omega

private noncomputable def onScale (k n : ℕ) : Finset (ℕ×ℕ) :=
  representations (prior blocks Block.A (k+1) : Set ℕ) ((blocks k).B : Set ℕ) n ∪
  representations ((blocks k).A : Set ℕ) (prior blocks Block.B k : Set ℕ) n

private theorem onScale_cap (k n : ℕ) : (onScale k n).card ≤ 9401 := by
  have ha := cross_grid_cap (block_valid k).gridB (prior_cap_with_block k) n
  have hb := cross_grid_cap (block_valid k).gridA (global_capB k) n
  unfold onScale
  apply (card_union_le _ _).trans
  rw [representations_swap_card ((blocks k).A : Set ℕ)]
  omega

private def eligible (n : ℕ) : Finset ℕ :=
  (range (n+1)).filter (fun k => p k^2 ≤ n ∧ n ≤ 526*p k^2)

private theorem scale_growth (i d : ℕ) : 2^d*p i ≤ p (i+d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ,pow_succ, Nat.mul_comm (2^d) 2, Nat.mul_assoc]
    exact (Nat.mul_le_mul_left 2 ih).trans (p_grow (i+d))

private theorem eligible_cap (n : ℕ) : (eligible n).card ≤ 5 := by
  by_cases hn : (eligible n).Nonempty
  · let a := (eligible n).min' hn
    have ha : a ∈ eligible n := min'_mem _ _
    have hnHi := (mem_filter.mp ha).2.2
    calc
      _ ≤ (Ico a (a+5)).card := by
        apply card_le_card
        intro k hk
        have haK : a ≤ k := min'_le _ _ hk
        have hlow := (mem_filter.mp hk).2.1
        apply mem_Ico.mpr
        refine ⟨haK,?_⟩
        by_contra! hfar
        have hpFar := (scale_growth a 5).trans (p_strict.monotone hfar)
        norm_num at hpFar
        have hsq := Nat.pow_le_pow_left hpFar 2
        rw [mul_pow] at hsq
        have hpos := p_pos a
        nlinarith
      _ = _ := by simp
  · simp [not_nonempty_iff_eq_empty.mp hn]

private theorem total_representation_cap (n : ℕ) : (representations A B n).card ≤ 47005 := by
  classical
  have hsub : representations A B n ⊆ (eligible n).biUnion (fun k => onScale k n) := by
    intro z hz
    obtain ⟨he,⟨i,hi⟩,⟨j,hj⟩⟩ := representation_mem.mp hz
    have hiBounds := valid_boundsA (block_valid i) hi
    have hjBounds := valid_boundsB (block_valid j) hj
    let k := max i j
    have hiK : i ≤ k := le_max_left _ _
    have hjK : j ≤ k := le_max_right _ _
    have hs (l : ℕ) (hl : l ≤ k) : p l^2 ≤ p k^2 :=
      Nat.pow_le_pow_left (p_strict.monotone hl) 2
    have hiTop := Nat.mul_le_mul_left 263 (hs i hiK)
    have hjTop := Nat.mul_le_mul_left 263 (hs j hjK)
    have hkLo : p k^2 ≤ n := by
      dsimp [k]
      rcases le_total i j with h | h
      · rw [max_eq_right h]
        omega
      · rw [max_eq_left h]
        omega
    have hkHi : n ≤ 526*p k^2 := by omega
    have hkN : k < n+1 := by
      have := scale_ge k
      nlinarith
    refine mem_biUnion.mpr ⟨k,mem_filter.mpr ⟨mem_range.mpr hkN,hkLo,hkHi⟩,?_⟩
    by_cases hij : i ≤ j
    · have hkj : k=j := max_eq_right hij
      apply mem_union.mpr
      exact Or.inl (representation_mem.mpr ⟨he,prior_mem.mpr ⟨i,by omega,hi⟩,hkj.symm ▸ hj⟩)
    · have hki : k=i := max_eq_left (by omega)
      apply mem_union.mpr
      exact Or.inr (representation_mem.mpr ⟨he,hki.symm ▸ hi,prior_mem.mpr ⟨j,by omega,hj⟩⟩)
  calc
    _ ≤ ((eligible n).biUnion (fun k => onScale k n)).card := card_le_card hsub
    _ ≤ ∑ k ∈ eligible n, (onScale k n).card := card_biUnion_le
    _ ≤ ∑ _ ∈ eligible n, 9401 := sum_le_sum (fun k _ => onScale_cap k n)
    _ ≤ 47005 := by simp; nlinarith [eligible_cap n]

private noncomputable def unionEquiv (F : ℕ → Finset ℕ)
    (hF : ∀ i j, i ≠ j → Disjoint (F i) (F j)) :
    (Σ i, ↥(F i)) ≃ ↥(unionSet F) := by
  let pack (z : Σ i, ↥(F i)) : ↥(unionSet F) := ⟨z.2.val,⟨z.1,z.2.property⟩⟩
  apply Equiv.ofBijective pack
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    have he : x.val = y.val := congrArg Subtype.val h
    by_cases hij : i=j
    · subst j
      have hxy : x=y := Subtype.ext he
      subst y
      rfl
    · exact (Finset.disjoint_left.mp (hF i j hij) x.property (he.symm ▸ y.property)).elim
  · intro z
    obtain ⟨i,hi⟩ := z.property
    exact ⟨⟨i,⟨z.val,hi⟩⟩,Subtype.ext rfl⟩

private noncomputable def packA : (Σ i, ↥(blocks i).A) ≃ ↥A :=
  unionEquiv (fun i => (blocks i).A) (by
    intro i j h
    rcases lt_or_gt_of_ne h with hh | hh
    · exact blocks_disjA hh
    · exact (blocks_disjA hh).symm)

private noncomputable def packB : (Σ i, ↥(blocks i).B) ≃ ↥B :=
  unionEquiv (fun i => (blocks i).B) (by
    intro i j h
    rcases lt_or_gt_of_ne h with hh | hh
    · exact blocks_disjB hh
    · exact (blocks_disjB hh).symm)

private noncomputable def pairing : ↥A ≃ ↥B :=
  packA.symm.trans ((Equiv.sigmaCongrRight (fun i => (blocks i).pair)).trans packB)

private theorem pairing_near (a : ↥A) : (pairing a).val ≤ (a.val : ℝ)+5*Real.sqrt a.val ∧
    (a.val : ℝ) ≤ (pairing a).val + 5*Real.sqrt (pairing a).val := by
  rcases h : packA.symm a with ⟨i,x⟩
  have hA : packA ⟨i,x⟩ = a := h ▸ packA.apply_symm_apply a
  have hB : pairing a = packB ⟨i,(blocks i).pair x⟩ := by simp [pairing,h]
  have ha : a.val = x.val := congrArg Subtype.val hA.symm
  have hb : (pairing a).val = ((blocks i).pair x).val := congrArg Subtype.val hB
  rw [ha,hb]
  have hx := (valid_boundsA (block_valid i) x.property).1
  have hy := (valid_boundsB (block_valid i) ((blocks i).pair x).property).1
  have hx' : (p i : ℝ) ≤ Real.sqrt x.val := Real.le_sqrt_of_sq_le (by exact_mod_cast hx)
  have hy' : (p i : ℝ) ≤ Real.sqrt ((blocks i).pair x).val :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hy)
  obtain ⟨h₁,h₂⟩ := (block_valid i).near x
  have h₁' : (x.val : ℝ) ≤ ((blocks i).pair x).val + 5*p i := by exact_mod_cast h₁
  have h₂' : (((blocks i).pair x).val : ℝ) ≤ x.val + 5*p i := by exact_mod_cast h₂
  exact ⟨by linarith,by linarith⟩

private theorem ordered_le {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite)
    (e : ↥S ≃ ↥T) (h : ∀ x : ↥S, (e x).val ≤ (x.val : ℝ)+5*Real.sqrt x.val) (n : ℕ) :
    (Nat.nth (· ∈ T) n : ℝ) ≤ Nat.nth (· ∈ S) n + 5*Real.sqrt (Nat.nth (· ∈ S) n) := by
  classical
  by_contra! hbad
  let s (j : Fin (n+1)) : ↥S := ⟨Nat.nth (· ∈ S) j.val,Nat.nth_mem_of_infinite hS j.val⟩
  have ht (j : Fin (n+1)) : (e (s j)).val < Nat.nth (· ∈ T) n := by
    have hmono := (Nat.nth_strictMono hS).monotone (show j.val ≤ n by omega)
    have hcast : ((s j).val : ℝ) ≤ (Nat.nth (· ∈ S) n : ℝ) := by exact_mod_cast hmono
    have hr := Real.sqrt_le_sqrt hcast
    have he := h (s j)
    have hj : ((e (s j)).val : ℝ) < (Nat.nth (· ∈ T) n : ℝ) := by linarith
    exact_mod_cast hj
  have hlt (j : Fin (n+1)) : Nat.count (· ∈ T) (e (s j)).val < n := by
    apply (Nat.nth_strictMono hT).lt_iff_lt.mp
    change Nat.nth (· ∈ T) (Nat.count (· ∈ T) (e (s j)).val) < Nat.nth (· ∈ T) n
    rw [Nat.nth_count (e (s j)).property]
    exact ht j
  let f (j : Fin (n+1)) : Fin n := ⟨_,hlt j⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hc := congrArg (fun z : Fin n => Nat.nth (· ∈ T) z.val) hij
    change Nat.nth (· ∈ T) (Nat.count (· ∈ T) (e (s i)).val) =
      Nat.nth (· ∈ T) (Nat.count (· ∈ T) (e (s j)).val) at hc
    rw [Nat.nth_count (e (s i)).property,Nat.nth_count (e (s j)).property] at hc
    apply Fin.ext
    exact (Nat.nth_strictMono hS).injective (congrArg Subtype.val (e.injective (Subtype.ext hc)))
  have hh := Fintype.card_le_of_injective f hinj
  simpa using hh

private theorem ratio : Tendsto (fun n => (Nat.nth (· ∈ A) n : ℝ) /
    (Nat.nth (· ∈ B) n : ℝ)) atTop (𝓝 1) := by
  apply ratio_of_sqrt_distance 5
  · exact tendsto_natCast_atTop_atTop.comp (Nat.nth_strictMono B_infinite).tendsto_atTop
  · apply Eventually.of_forall
    intro n
    have h₁ := ordered_le A_infinite B_infinite pairing (fun x => (pairing_near x).1) n
    have h₂ := ordered_le B_infinite A_infinite pairing.symm (fun y => by
      simpa using (pairing_near (pairing.symm y)).2) n
    generalize (Nat.nth (· ∈ A) n : ℝ) = an at h₁ h₂ ⊢
    generalize (Nat.nth (· ∈ B) n : ℝ) = bn at h₁ h₂ ⊢
    rw [abs_le]
    constructor
    · by_cases h : an ≤ bn
      · have hr := Real.sqrt_le_sqrt h
        linarith
      · have hr := Real.sqrt_nonneg bn
        linarith
    · linarith

theorem counterexample : ¬ Erdos1145.Erdos1145Prop :=
  disproof_of_balanced_complements A_infinite B_infinite ratio cofinite 47005 total_representation_cap

end OMA.Erdos1145Proof

theorem OMA.disproof : ¬ (type_of% @Erdos1145.erdos_1145) := OMA.Erdos1145Proof.counterexample
