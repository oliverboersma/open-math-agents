import FormalConjectures.ErdosProblems.«143»

/-!
# Reduction of Erdős Problem 143 — part i ($500 prize)

Reduction `Erdos143.erdos_143.parts.i.R1`, following Koukoulopoulos–Lamzouri–Lichtman
(arXiv:2502.09539) and Behrend (1935).
-/

-- Reduction Erdos143.erdos_143.parts.i.R1 of Erdős Problem 143 — part i ($500 prize)
-- Credit: @Need17Bread
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Following Koukoulopoulos–Lamzouri–Lichtman (arXiv:2502.09539) and Behrend (1935):
-- * `main` proves in full:
--     1. Finiteness and linear counting bound `|A ∩ [1, x]| ≤ ⌊x⌋₊` for any `WellSeparatedSet A`.
--     2. Real-to-rational perturbation: any finite real well-separated set in `[2, N]` perturbs
--        (with factor-2 scaling) to a finite rational well-separated set in `[2, 2N + 1]`,
--        preserving the reciprocal sum up to a factor of 4.
--     3. Decomposition of a rational well-separated set into its integer part (a primitive set
--        of natural numbers) and its strictly non-integer rational part.
--     4. Exact discrete Abel partial summation and logarithmic harmonic lower bound showing that
--        `∑_{x ∈ A ∩ [1, N]} 1/x = o(log N)` implies `liminf_{x → ∞} |A ∩ [1, x]| / x = 0`.
-- * `H1` (Behrend 1935): primitive subsets of `{2, ..., M}` have reciprocal sum `o(log M)`.
-- * `H2` (Koukoulopoulos–Lamzouri–Lichtman 2025): well-separated finite sets of non-integer
--   rationals in `[2, M]` have reciprocal sum `o(log M)`.

namespace OMA.R_Erdos143_erdos_143_parts_i_R1

open Filter Finset Erdos143
open scoped BigOperators

/-- Behrend (1935): primitive subsets of `{2, ..., M}` have reciprocal sum `o(log M)`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ S : Finset ℕ, (∀ a ∈ S, 2 ≤ a ∧ a ≤ M) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b) →
      ∑ a ∈ S, (1 : ℝ) / (a : ℝ) ≤ ε * Real.log M

/-- Koukoulopoulos–Lamzouri–Lichtman (2025): well-separated finite sets of non-integer rationals
in `[2, M]` have reciprocal sum `o(log M)`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ Q : Finset ℚ, (∀ q ∈ Q, (2 : ℚ) ≤ q ∧ q ≤ (M : ℚ) ∧ 1 < q.den) →
      (∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → ∀ k : ℕ, 1 ≤ k → (1 : ℚ) ≤ |(k : ℚ) * p - q|) →
      ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ≤ ε * Real.log M

/-- Distinct elements of a well-separated set are at distance at least `1`. -/
lemma wellSeparated_dist_ge_one {A : Set ℝ} (hA : WellSeparatedSet A)
    {x y : ℝ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) : 1 ≤ |x - y| := by
  have h := hA.2.2.2 x hx y hy hxy 1 le_rfl
  simpa using h

/-- `Nat.floor` is injective on `A ∩ [1, x]` for any well-separated set `A`. -/
lemma wellSeparated_floor_injOn {A : Set ℝ} (hA : WellSeparatedSet A) (x : ℝ) :
    Set.InjOn Nat.floor (A ∩ Set.Icc 1 x) := by
  intro a ha b hb hfl
  by_contra hab
  have hdist := wellSeparated_dist_ge_one hA ha.1 hb.1 hab
  have ha0 : 0 ≤ a := by linarith [ha.2.1]
  have hb0 : 0 ≤ b := by linarith [hb.2.1]
  have ha1 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha0
  have ha2 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  have hb1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb0
  have hb2 : b < (⌊b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one b
  rw [hfl] at ha1 ha2
  have hlt : |a - b| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-- For a well-separated set `A`, `A ∩ [1, x]` is finite and has at most `⌊x⌋₊` elements. -/
lemma wellSeparated_finite_and_card_le {A : Set ℝ} (hA : WellSeparatedSet A) (x : ℝ) :
    (A ∩ Set.Icc 1 x).Finite ∧ (A ∩ Set.Icc 1 x).ncard ≤ ⌊x⌋₊ := by
  have hmaps : Set.MapsTo Nat.floor (A ∩ Set.Icc 1 x) (Finset.Icc 1 ⌊x⌋₊ : Set ℕ) := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨Nat.le_floor (by simpa using ha.2.1), Nat.floor_mono ha.2.2⟩
  have hinj := wellSeparated_floor_injOn hA x
  have hfin : (A ∩ Set.Icc 1 x).Finite :=
    Set.Finite.of_finite_image ((Finset.Icc 1 ⌊x⌋₊).finite_toSet.subset hmaps.image_subset) hinj
  have hle : (A ∩ Set.Icc 1 x).ncard ≤ ((Finset.Icc 1 ⌊x⌋₊ : Finset ℕ) : Set ℕ).ncard :=
    Set.ncard_le_ncard_of_injOn Nat.floor hmaps hinj (Finset.Icc 1 ⌊x⌋₊).finite_toSet
  rw [Set.ncard_coe_finset, Nat.card_Icc] at hle
  exact ⟨hfin, by omega⟩

/-- At most one element of a well-separated set lies in `(1, 2)`. -/
lemma wellSeparated_Ioo_one_two_subsingleton {A : Set ℝ} (hA : WellSeparatedSet A) :
    (A ∩ Set.Ioo 1 2).Subsingleton := by
  intro a ha b hb
  by_contra hab
  have hdist := wellSeparated_dist_ge_one hA ha.1 hb.1 hab
  have hlt : |a - b| < 1 := abs_lt.mpr ⟨by linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2],
    by linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]⟩
  linarith

/-- Perturb a finite real well-separated set in `[2, N]` into a finite rational well-separated
set in `[2, 2N + 1]`, preserving the reciprocal sum up to a factor of `4`. -/
lemma real_to_rat_wellSeparated {N : ℕ} (hN : 2 ≤ N) {S : Finset ℝ}
    (hS_mem : ∀ x ∈ S, (2 : ℝ) ≤ x ∧ x ≤ (N : ℝ))
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℝ) * x - y|) :
    ∃ Q : Finset ℚ,
      (∀ q ∈ Q, (2 : ℚ) ≤ q ∧ q ≤ ((2 * N + 1 : ℕ) : ℚ)) ∧
      (∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → ∀ k : ℕ, 1 ≤ k → (1 : ℚ) ≤ |(k : ℚ) * p - q|) ∧
      (1 / 4 : ℝ) * ∑ x ∈ S, (1 / x) ≤ ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  classical
  have hδ_pos : (0 : ℝ) < 1 / (4 * ((N : ℝ) + 1)) := by positivity
  have hex : ∀ x : ℝ, ∃ r : ℚ, x < (r : ℝ) ∧ (r : ℝ) < x + 1 / (4 * ((N : ℝ) + 1)) :=
    fun x => exists_rat_btwn (by linarith)
  let r : ℝ → ℚ := fun x => Classical.choose (hex x)
  have hr_lo : ∀ x : ℝ, x < (r x : ℝ) := fun x => (Classical.choose_spec (hex x)).1
  have hr_hi : ∀ x : ℝ, (r x : ℝ) < x + 1 / (4 * ((N : ℝ) + 1)) :=
    fun x => (Classical.choose_spec (hex x)).2
  let q : ℝ → ℚ := fun x => 2 * r x
  have hq_cast : ∀ x : ℝ, ((q x : ℚ) : ℝ) = 2 * (r x : ℝ) := by
    intro x
    simp [q]
  have hN1_ge : (3 : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (show 3 ≤ N + 1 by omega)
  have hδ_le : 1 / (4 * ((N : ℝ) + 1)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hq_inj : Set.InjOn q (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hS_sep x hx y hy hne 1 le_rfl
    simp only [Nat.cast_one, one_mul] at h1
    have hrx : |(r x : ℝ) - x| < 1 / 4 := by
      rw [abs_of_pos (by linarith [hr_lo x])]
      linarith [hr_hi x, hδ_le]
    have hry : |(r y : ℝ) - y| < 1 / 4 := by
      rw [abs_of_pos (by linarith [hr_lo y])]
      linarith [hr_hi y, hδ_le]
    have hreq : (r x : ℝ) = (r y : ℝ) := by
      have : (2 * r x : ℚ) = 2 * r y := hxy
      have h2 : r x = r y := mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) this
      exact_mod_cast h2
    have hdiff : x - y = (x - (r x : ℝ)) + ((r y : ℝ) - y) := by linarith
    have habs : |x - y| ≤ |(r x : ℝ) - x| + |(r y : ℝ) - y| := by
      rw [hdiff]
      calc |(x - (r x : ℝ)) + ((r y : ℝ) - y)|
          ≤ |x - (r x : ℝ)| + |(r y : ℝ) - y| := abs_add_le _ _
        _ = |(r x : ℝ) - x| + |(r y : ℝ) - y| := by rw [abs_sub_comm]
    linarith
  refine ⟨S.image q, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hx2, hxN⟩ := hS_mem x hx
    constructor
    · have : ((2 : ℚ) : ℝ) ≤ ((q x : ℚ) : ℝ) := by
        rw [hq_cast]
        norm_num
        linarith [hr_lo x]
      exact_mod_cast this
    · have : ((q x : ℚ) : ℝ) ≤ (((2 * N + 1 : ℕ) : ℚ) : ℝ) := by
        rw [hq_cast]
        push_cast
        linarith [hr_hi x, hδ_le]
      exact_mod_cast this
  · intro u hu v hv huv k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := fun h => huv (by rw [h])
    obtain ⟨hx2, hxN⟩ := hS_mem x hx
    obtain ⟨hy2, hyN⟩ := hS_mem y hy
    have hreal : (1 : ℝ) ≤ |(k : ℝ) * ((q x : ℚ) : ℝ) - ((q y : ℚ) : ℝ)| := by
      by_cases hkN : k ≤ N
      · have hsep := hS_sep x hx y hy hxy k hk
        have hrx_pos : 0 < (r x : ℝ) - x := by linarith [hr_lo x]
        have hry_pos : 0 < (r y : ℝ) - y := by linarith [hr_lo y]
        have hk_le : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have herr : |(k : ℝ) * ((r x : ℝ) - x) - ((r y : ℝ) - y)| ≤ 1 / 4 := by
          have h1 : (k : ℝ) * ((r x : ℝ) - x) < (N : ℝ) * (1 / (4 * ((N : ℝ) + 1))) := by
            calc (k : ℝ) * ((r x : ℝ) - x)
                ≤ (N : ℝ) * ((r x : ℝ) - x) := mul_le_mul_of_nonneg_right hk_le hrx_pos.le
              _ < (N : ℝ) * (1 / (4 * ((N : ℝ) + 1))) := by
                  apply mul_lt_mul_of_pos_left (by linarith [hr_hi x])
                  exact_mod_cast (show 0 < N by omega)
          have h2 : (r y : ℝ) - y < 1 / (4 * ((N : ℝ) + 1)) := by linarith [hr_hi y]
          have hsum : (N : ℝ) * (1 / (4 * ((N : ℝ) + 1))) + 1 / (4 * ((N : ℝ) + 1)) = 1 / 4 := by
            have hpos : (N : ℝ) + 1 ≠ 0 := by linarith
            field_simp
          rw [abs_le]
          constructor
          · linarith [mul_nonneg hk_nonneg hrx_pos.le]
          · linarith
        have htri : |(k : ℝ) * x - y| - |(k : ℝ) * ((r x : ℝ) - x) - ((r y : ℝ) - y)|
            ≤ |(k : ℝ) * (r x : ℝ) - (r y : ℝ)| := by
          have hid : (k : ℝ) * x - y =
              ((k : ℝ) * (r x : ℝ) - (r y : ℝ)) - ((k : ℝ) * ((r x : ℝ) - x) - ((r y : ℝ) - y)) := by
            ring
          have hle := abs_sub ((k : ℝ) * (r x : ℝ) - (r y : ℝ))
            ((k : ℝ) * ((r x : ℝ) - x) - ((r y : ℝ) - y))
          linarith [hid ▸ hle]
        have hr_sep : (3 / 4 : ℝ) ≤ |(k : ℝ) * (r x : ℝ) - (r y : ℝ)| := by linarith
        rw [hq_cast, hq_cast]
        have h2eq : (k : ℝ) * (2 * (r x : ℝ)) - 2 * (r y : ℝ) =
            2 * ((k : ℝ) * (r x : ℝ) - (r y : ℝ)) := by ring
        rw [h2eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      · have hk_ge : (N : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show N + 1 ≤ k by omega)
        rw [hq_cast, hq_cast]
        have hqx_ge : (4 : ℝ) ≤ 2 * (r x : ℝ) := by linarith [hr_lo x]
        have hqy_le : 2 * (r y : ℝ) ≤ 2 * (N : ℝ) + 1 := by linarith [hr_hi y, hδ_le]
        have hpos : 1 ≤ (k : ℝ) * (2 * (r x : ℝ)) - 2 * (r y : ℝ) := by nlinarith
        exact hpos.trans (le_abs_self _)
    have hcast : (((1 : ℚ) : ℝ)) ≤ (((|(k : ℚ) * q x - q y| : ℚ) : ℝ)) := by
      simpa using hreal
    exact_mod_cast hcast
  · rw [Finset.sum_image hq_inj, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    obtain ⟨hx2, _⟩ := hS_mem x hx
    have hqx_pos : (0 : ℝ) < ((q x : ℚ) : ℝ) := by
      rw [hq_cast]
      linarith [hr_lo x]
    have hqx_le : ((q x : ℚ) : ℝ) ≤ 4 * x := by
      rw [hq_cast]
      linarith [hr_hi x, hδ_le]
    have h1 : 1 / 4 * (1 / x) = 1 / (4 * x) := by ring
    rw [h1]
    exact one_div_le_one_div_of_le hqx_pos hqx_le

/-- Combine Behrend (`H1`) and KLL25 (`H2`) to bound the reciprocal sum of any finite rational
well-separated set in `[2, M]`. -/
lemma rat_wellSeparated_bound (h1 : H1) (h2 : H2) {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ Q : Finset ℚ, (∀ q ∈ Q, (2 : ℚ) ≤ q ∧ q ≤ (M : ℚ)) →
        (∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → ∀ k : ℕ, 1 ≤ k → (1 : ℚ) ≤ |(k : ℚ) * p - q|) →
        ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ≤ ε * Real.log M := by
  obtain ⟨M₁, hM₁⟩ := h1 (ε / 2) (half_pos hε)
  obtain ⟨M₂, hM₂⟩ := h2 (ε / 2) (half_pos hε)
  refine ⟨max M₁ M₂, fun M hM Q hQ_mem hQ_sep => ?_⟩
  let Q₁ := Q.filter (fun q : ℚ => q.den = 1)
  let Q₂ := Q.filter (fun q : ℚ => q.den ≠ 1)
  have hsplit : ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) =
      (∑ q ∈ Q₁, (1 : ℝ) / (q : ℝ)) + (∑ q ∈ Q₂, (1 : ℝ) / (q : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun q : ℚ => q.den = 1)]
  rw [hsplit]
  have hQ₁_int : ∀ q ∈ Q₁, ((q.num.toNat : ℕ) : ℚ) = q := by
    intro q hq
    obtain ⟨hqQ, hden⟩ := Finset.mem_filter.mp hq
    have hq2 : (2 : ℚ) ≤ q := (hQ_mem q hqQ).1
    have hnum_pos : (0 : ℤ) ≤ q.num := by
      have : (0 : ℚ) ≤ q := by linarith
      exact Rat.num_nonneg.mpr this
    have hnum_eq : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum_pos
    apply Rat.ext
    · simp [hnum_eq]
    · simp [hden]
  let S : Finset ℕ := Q₁.image (fun q : ℚ => q.num.toNat)
  have hinj : Set.InjOn (fun q : ℚ => q.num.toNat) (Q₁ : Set ℚ) := by
    intro p hp q hq hpq
    dsimp only at hpq
    rw [← hQ₁_int p hp, ← hQ₁_int q hq, hpq]
  have hS_mem : ∀ a ∈ S, 2 ≤ a ∧ a ≤ M := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    have hqQ := (Finset.mem_filter.mp hq).1
    have heq := hQ₁_int q hq
    have h1' : (2 : ℚ) ≤ (q.num.toNat : ℚ) := heq.symm ▸ (hQ_mem q hqQ).1
    have h2' : (q.num.toNat : ℚ) ≤ (M : ℚ) := heq.symm ▸ (hQ_mem q hqQ).2
    exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
  have hS_prim : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b := by
    intro a ha b hb hab hdvd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, hk⟩ := hdvd
    have hpQ := (Finset.mem_filter.mp hp).1
    have hqQ := (Finset.mem_filter.mp hq).1
    have hpq : p ≠ q := fun h => hab (by rw [h])
    have hb2 : 2 ≤ q.num.toNat := (hS_mem _ hb).1
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      rw [this, mul_zero] at hk
      omega
    have hsep := hQ_sep p hpQ q hqQ hpq k hk1
    have hzero : (k : ℚ) * p - q = 0 := by
      rw [← hQ₁_int p hp, ← hQ₁_int q hq]
      have : (q.num.toNat : ℚ) = (p.num.toNat : ℚ) * (k : ℚ) := by exact_mod_cast hk
      linarith
    rw [hzero, abs_zero] at hsep
    norm_num at hsep
  have hsum1 : ∑ q ∈ Q₁, (1 : ℝ) / (q : ℝ) ≤ (ε / 2) * Real.log M := by
    have heq : ∑ q ∈ Q₁, (1 : ℝ) / (q : ℝ) = ∑ a ∈ S, (1 : ℝ) / (a : ℝ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro q hq
      have hcast : ((q.num.toNat : ℕ) : ℝ) = (q : ℝ) := by
        have := congrArg (fun z : ℚ => (z : ℝ)) (hQ₁_int q hq)
        simpa using this
      rw [hcast]
    rw [heq]
    exact hM₁ M ((le_max_left M₁ M₂).trans hM) S hS_mem hS_prim
  have hsum2 : ∑ q ∈ Q₂, (1 : ℝ) / (q : ℝ) ≤ (ε / 2) * Real.log M := by
    apply hM₂ M ((le_max_right M₁ M₂).trans hM) Q₂
    · intro q hq
      obtain ⟨hqQ, hden⟩ := Finset.mem_filter.mp hq
      have hpos : 0 < q.den := q.den_pos
      exact ⟨(hQ_mem q hqQ).1, (hQ_mem q hqQ).2, by omega⟩
    · intro p hp q hq hpq k hk
      exact hQ_sep p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq k hk
  linarith

/-- Telescoping lower bound: for `1 ≤ m ≤ N`, `∑_{k=m}^{N-1} 1/(k*(k+1)) ≤ 1/m`. -/
lemma telescoping_inv_le {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∑ k ∈ Finset.Ico m N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) ≤ 1 / (m : ℝ) := by
  have hterm : ∀ k ∈ Finset.Ico m N,
      (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have := (Finset.mem_Ico.mp hk).1
      exact_mod_cast (show 1 ≤ k by omega)
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    have hk1' : (k : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  have htele : ∀ n : ℕ, m ≤ n →
      ∑ k ∈ Finset.Ico m n, ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)) =
        1 / (m : ℝ) - 1 / (n : ℝ) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro hmn
      by_cases heq : m = n + 1
      · subst heq
        simp
      · have hle : m ≤ n := by omega
        rw [Finset.sum_Ico_succ_top hle, ih hle]
        push_cast
        ring
  rw [htele N hmN]
  have hNpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  linarith

/-- Elementary logarithmic lower bound on a tail harmonic sum. -/
lemma harmonic_tail_ge_log {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    Real.log (N : ℝ) - Real.log ((K + 1 : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Ico K N, (1 : ℝ) / ((k : ℝ) + 1) := by
  have hstep : ∀ k ∈ Finset.Ico K N,
      Real.log (((k + 2 : ℕ) : ℝ)) - Real.log (((k + 1 : ℕ) : ℝ)) ≤
        (1 : ℝ) / ((k : ℝ) + 1) := by
    intro k _
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    rw [← Real.log_div hk2.ne' hk1.ne']
    have hlog := Real.log_le_sub_one_of_pos (div_pos hk2 hk1)
    have hval : ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = 1 / ((k : ℝ) + 1) := by
      push_cast
      have hne : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    linarith
  have htele : ∀ n : ℕ, K ≤ n →
      ∑ k ∈ Finset.Ico K n, (Real.log (((k + 2 : ℕ) : ℝ)) - Real.log (((k + 1 : ℕ) : ℝ))) =
        Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (((K + 1 : ℕ) : ℝ)) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro hKn
      by_cases heq : K = n + 1
      · subst heq
        simp
      · have hle : K ≤ n := by omega
        rw [Finset.sum_Ico_succ_top hle, ih hle]
        ring
  have hsum := Finset.sum_le_sum hstep
  rw [htele N hKN] at hsum
  have hlog_le : Real.log (N : ℝ) ≤ Real.log (((N + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
    exact_mod_cast (show N ≤ N + 1 by omega)
  linarith

/-- Discrete Abel partial summation: a lower bound on counting density `|A ∩ [1, k]| / k` forces
a logarithmic lower bound on `∑_{x ∈ A ∩ [1, N]} 1/x`. -/
lemma recip_sum_ge_partial_summation {A : Set ℝ} (hA : WellSeparatedSet A)
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N, ((A ∩ Set.Icc 1 (k : ℝ)).ncard : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) ≤
      ∑ x ∈ (wellSeparated_finite_and_card_le hA (N : ℝ)).1.toFinset, (1 : ℝ) / x := by
  let F := (wellSeparated_finite_and_card_le hA (N : ℝ)).1.toFinset
  have hterm : ∀ x ∈ F,
      ∑ k ∈ Finset.Ico ⌈x⌉₊ N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) ≤ 1 / x := by
    intro x hx
    have hxmem : x ∈ A ∩ Set.Icc 1 (N : ℝ) := Set.Finite.mem_toFinset _ |>.mp hx
    have hx1 : (1 : ℝ) ≤ x := hxmem.2.1
    have hxN : x ≤ (N : ℝ) := hxmem.2.2
    have hceil_ge : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
    have hceil_le : ⌈x⌉₊ ≤ N := Nat.ceil_le.mpr hxN
    calc ∑ k ∈ Finset.Ico ⌈x⌉₊ N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1))
        ≤ 1 / (⌈x⌉₊ : ℝ) := telescoping_inv_le hceil_ge hceil_le
      _ ≤ 1 / x := one_div_le_one_div_of_le (by linarith) (Nat.le_ceil x)
  have h1 : ∑ x ∈ F, ∑ k ∈ Finset.Ico ⌈x⌉₊ N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) ≤
      ∑ x ∈ F, (1 : ℝ) / x := Finset.sum_le_sum hterm
  have hswap : ∑ x ∈ F, ∑ k ∈ Finset.Ico ⌈x⌉₊ N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) =
      ∑ k ∈ Finset.Ico 1 N,
        ((F.filter (fun x => ⌈x⌉₊ ≤ k)).card : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
    calc ∑ x ∈ F, ∑ k ∈ Finset.Ico ⌈x⌉₊ N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1))
        = ∑ x ∈ F, ∑ k ∈ Finset.Ico 1 N,
            if ⌈x⌉₊ ≤ k then (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hx1 : (1 : ℝ) ≤ x := ((Set.Finite.mem_toFinset _).mp hx).2.1
          have hceil_ge : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext k
          simp only [Finset.mem_Ico, Finset.mem_filter]
          omega
      _ = ∑ k ∈ Finset.Ico 1 N, ∑ x ∈ F,
            if ⌈x⌉₊ ≤ k then (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) else 0 := Finset.sum_comm
      _ = ∑ k ∈ Finset.Ico 1 N,
            ((F.filter (fun x => ⌈x⌉₊ ≤ k)).card : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hcard_eq : ∀ k ∈ Finset.Ico 1 N,
      (F.filter (fun x => ⌈x⌉₊ ≤ k)).card = (A ∩ Set.Icc 1 (k : ℝ)).ncard := by
    intro k hk
    have hkN : k ≤ N := (Finset.mem_Ico.mp hk).2.le
    have hset : (F.filter (fun x => ⌈x⌉₊ ≤ k) : Set ℝ) = A ∩ Set.Icc 1 (k : ℝ) := by
      ext x
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, F,
        Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_Icc, Nat.ceil_le]
      constructor
      · rintro ⟨⟨hxA, hx1, _⟩, hxk⟩
        exact ⟨hxA, hx1, hxk⟩
      · rintro ⟨hxA, hx1, hxk⟩
        exact ⟨⟨hxA, hx1, hxk.trans (by exact_mod_cast hkN)⟩, hxk⟩
    rw [← Set.ncard_coe_finset, hset]
  have heq : ∑ k ∈ Finset.Ico 1 N, ((A ∩ Set.Icc 1 (k : ℝ)).ncard : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) =
      ∑ k ∈ Finset.Ico 1 N,
        ((F.filter (fun x => ⌈x⌉₊ ≤ k)).card : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcard_eq k hk]
  linarith

theorem main : H1 → H2 → type_of% @Erdos143.erdos_143.parts.i := by
  intro h1 h2 A hA
  let u : ℝ → ℝ := fun x => ((A ∩ Set.Icc 1 x).ncard : ℝ) / x
  have hu_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ u x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hu_le_one : ∀ᶠ x : ℝ in atTop, u x ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hle : ((A ∩ Set.Icc 1 x).ncard : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (wellSeparated_finite_and_card_le hA x).2
    have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    exact (div_le_one (by linarith)).mpr (hle.trans hfl)
  have hcobdd : atTop.IsCoboundedUnder (· ≥ ·) u := by
    refine ⟨1, ?_⟩
    rintro b hb
    obtain ⟨x, hx1, hxb⟩ := (hu_le_one.and hb).exists
    exact hxb.trans hx1
  have hbdd : atTop.IsBoundedUnder (· ≥ ·) u := ⟨0, hu_nonneg⟩
  apply le_antisymm
  · apply Filter.liminf_le_of_le hbdd
    intro b hb
    by_contra hpos
    have hb_pos : 0 < b := lt_of_not_ge hpos
    obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hb
    let K : ℕ := max 2 ⌈X₀⌉₊
    have hK2 : 2 ≤ K := le_max_left 2 ⌈X₀⌉₊
    have hKX : X₀ ≤ (K : ℝ) := (Nat.le_ceil X₀).trans (by exact_mod_cast le_max_right 2 ⌈X₀⌉₊)
    obtain ⟨M₀, hM₀⟩ := rat_wellSeparated_bound h1 h2 (show 0 < b / 16 by positivity)
    let C : ℝ := 1 + b * Real.log ((K + 1 : ℕ) : ℝ) + (b / 4) * Real.log 3
    have htend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htend.eventually_gt_atTop (4 * C / (3 * b)))
    let N : ℕ := max (max K M₀) (max N₁ 2)
    have hKN : K ≤ N := (le_max_left K M₀).trans (le_max_left _ _)
    have hM₀N : M₀ ≤ 2 * N + 1 := by
      have : M₀ ≤ N := (le_max_right K M₀).trans (le_max_left _ _)
      omega
    have hN₁N : N₁ ≤ N := (le_max_left N₁ 2).trans (le_max_right _ _)
    have hN2 : 2 ≤ N := (le_max_right N₁ 2).trans (le_max_right _ _)
    have hlogN_gt : 4 * C / (3 * b) < Real.log (N : ℝ) := hN₁ N hN₁N
    -- Lower bound from partial summation
    have hlow : b * (Real.log (N : ℝ) - Real.log ((K + 1 : ℕ) : ℝ)) ≤
        ∑ x ∈ (wellSeparated_finite_and_card_le hA (N : ℝ)).1.toFinset, (1 : ℝ) / x := by
      have hps := recip_sum_ge_partial_summation hA hN2
      have hsub : Finset.Ico K N ⊆ Finset.Ico 1 N :=
        Finset.Ico_subset_Ico (by omega) le_rfl
      have hnonneg : ∀ k ∈ Finset.Ico 1 N,
          0 ≤ ((A ∩ Set.Icc 1 (k : ℝ)).ncard : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
        intro k _
        positivity
      have htail : ∑ k ∈ Finset.Ico K N,
            ((A ∩ Set.Icc 1 (k : ℝ)).ncard : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) ≤
          ∑ k ∈ Finset.Ico 1 N,
            ((A ∩ Set.Icc 1 (k : ℝ)).ncard : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hnonneg k hk)
      have hdens : ∑ k ∈ Finset.Ico K N, b * ((1 : ℝ) / ((k : ℝ) + 1)) ≤
          ∑ k ∈ Finset.Ico K N,
            ((A ∩ Set.Icc 1 (k : ℝ)).ncard : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkK : K ≤ k := (Finset.mem_Ico.mp hk).1
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        have hbk : b ≤ u (k : ℝ) := hX₀ (k : ℝ) (hKX.trans (by exact_mod_cast hkK))
        have hnc : b * (k : ℝ) ≤ ((A ∩ Set.Icc 1 (k : ℝ)).ncard : ℝ) :=
          (le_div_iff₀ hkpos).mp hbk
        have heq : b * (1 / ((k : ℝ) + 1)) = (b * (k : ℝ)) / ((k : ℝ) * ((k : ℝ) + 1)) := by
          have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
          have hk1 : (k : ℝ) + 1 ≠ 0 := by linarith
          field_simp
        rw [heq]
        exact div_le_div_of_nonneg_right hnc (by positivity)
      rw [← Finset.mul_sum] at hdens
      have hharm := mul_le_mul_of_nonneg_left (harmonic_tail_ge_log (by omega) hKN) hb_pos.le
      linarith
    -- Upper bound from real-to-rational perturbation + H1 + H2
    let F := (wellSeparated_finite_and_card_le hA (N : ℝ)).1.toFinset
    let F₁ := F.filter (fun x : ℝ => x < 2)
    let F₂ := F.filter (fun x : ℝ => 2 ≤ x)
    have hF_split : ∑ x ∈ F, (1 : ℝ) / x =
        (∑ x ∈ F₁, (1 : ℝ) / x) + (∑ x ∈ F₂, (1 : ℝ) / x) := by
      have hnot : F.filter (fun x : ℝ => ¬ x < 2) = F₂ := by
        ext x
        simp [F₂, not_lt]
      rw [← hnot, Finset.sum_filter_add_sum_filter_not]
    have hF₁_le : ∑ x ∈ F₁, (1 : ℝ) / x ≤ 1 := by
      have hsub : (F₁ : Set ℝ) ⊆ A ∩ Set.Ioo 1 2 := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        have hmem := (Set.Finite.mem_toFinset _).mp hx.1
        have hgt1 : 1 < x := hA.1 hmem.1
        exact ⟨hmem.1, hgt1, hx.2⟩
      have hcard1 : F₁.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact wellSeparated_Ioo_one_two_subsingleton hA (hsub ha) (hsub hb)
      calc ∑ x ∈ F₁, (1 : ℝ) / x
          ≤ ∑ _x ∈ F₁, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            have hx1 : (1 : ℝ) < x := (hsub hx).2.1
            exact (div_le_one (by linarith)).mpr hx1.le
        _ = (F₁.card : ℝ) := by simp
        _ ≤ 1 := by exact_mod_cast hcard1
    have hF₂_mem : ∀ x ∈ F₂, (2 : ℝ) ≤ x ∧ x ≤ (N : ℝ) := by
      intro x hx
      obtain ⟨hxF, hx2⟩ := Finset.mem_filter.mp hx
      exact ⟨hx2, ((Set.Finite.mem_toFinset _).mp hxF).2.2⟩
    have hF₂_sep : ∀ x ∈ F₂, ∀ y ∈ F₂, x ≠ y → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℝ) * x - y| := by
      intro x hx y hy hxy k hk
      have hxA := ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hx).1).1
      have hyA := ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hy).1).1
      exact hA.2.2.2 x hxA y hyA hxy k hk
    obtain ⟨Q, hQ_mem, hQ_sep, hQ_sum⟩ := real_to_rat_wellSeparated hN2 hF₂_mem hF₂_sep
    have hQ_bound := hM₀ (2 * N + 1) hM₀N Q hQ_mem hQ_sep
    have hlog_2N1 : Real.log ((2 * N + 1 : ℕ) : ℝ) ≤ Real.log 3 + Real.log (N : ℝ) := by
      have hle : ((2 * N + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
        push_cast
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        linarith
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      calc Real.log ((2 * N + 1 : ℕ) : ℝ)
          ≤ Real.log (3 * (N : ℝ)) := Real.log_le_log (by positivity) hle
        _ = Real.log 3 + Real.log (N : ℝ) := Real.log_mul (by norm_num) hNpos.ne'
    have hF₂_le : ∑ x ∈ F₂, (1 : ℝ) / x ≤ (b / 4) * (Real.log 3 + Real.log (N : ℝ)) := by
      have h1' : ∑ x ∈ F₂, (1 : ℝ) / x ≤ (b / 4) * Real.log ((2 * N + 1 : ℕ) : ℝ) := by linarith
      nlinarith
    have hup : ∑ x ∈ F, (1 : ℝ) / x ≤ 1 + (b / 4) * (Real.log 3 + Real.log (N : ℝ)) := by
      linarith
    have hcontra : (3 * b / 4) * Real.log (N : ℝ) ≤ C := by
      dsimp only [C]
      linarith
    have hstrict : C < (3 * b / 4) * Real.log (N : ℝ) := by
      have h3b : 0 < 3 * b := by linarith
      have := (div_lt_iff₀ h3b).mp hlogN_gt
      linarith
    linarith
  · exact Filter.le_liminf_of_le hcobdd hu_nonneg

end OMA.R_Erdos143_erdos_143_parts_i_R1
