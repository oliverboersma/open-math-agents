import FormalConjectures.ErdosProblems.«1191»

-- Reduction Erdos1191.erdos_1191.parts.i.R2 of Erdős Problem 1191 — i
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A finite regular / irregular split of Erdős Problem 1191 (i)

Write `c_j(S) = |S ∩ [1, 2^j]|` for a finite Sidon set `S`. The target follows
(see `main`) from the finite dyadic obstruction: for every `d > 0` and `J` there
is a horizon `K ≥ J` such that every Sidon `S ⊆ [1, 2^K]` has a scale
`j ∈ [J, K]` with `d * c_j ^ 2 * j ≤ 2 ^ j`. (Conversely, the target implies
this obstruction by a compactness argument, so the obstruction is equivalent.)

The obstruction is split according to the dyadic profile `c_j ^ 2 * j / 2 ^ j`:

* `H1` (regular regime): the obstruction for Sidon sets whose profile is at most
  `C` on the whole window `[J, K]`, for every constant `C`.
* `H2` (irregular regime): for some constant `C = C(d)`, the obstruction (with a
  later horizon) for Sidon sets having a scale in a given window where the
  profile exceeds `C`.

Both are consequences of the target, and together they give it back.
-/

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R2

open Filter
open Set

theorem liminf_ofReal_zero_of_frequently {u : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ x in atTop, u x ≤ ε) :
    liminf (fun x ↦ ENNReal.ofReal (u x)) atTop = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  apply Filter.liminf_le_of_frequently_le'
  refine (h ε (by exact_mod_cast hε)).mono fun x hx => ?_
  exact ENNReal.ofReal_le_of_le_toReal (by simpa using hx)

theorem normalised_le_of_sq_le {n x : ℕ} {ε : ℝ} (hε : 0 < ε) (hx : 1 ≤ x)
    (h : (n : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x) :
    (n : ℝ) / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) ≤ ε := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, div_mul_eq_mul_div,
    div_le_iff₀ (Real.sqrt_pos.2 hx0)]
  have h1 : (n : ℝ) * Real.sqrt (Real.log x) = Real.sqrt ((n : ℝ) ^ 2 * Real.log x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n)]
  have h2 : ε * Real.sqrt x = Real.sqrt (ε ^ 2 * x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
  rw [h1, h2]
  exact Real.sqrt_le_sqrt h

theorem prefix_filter_card (S : Finset ℕ) (hS : ∀ a ∈ S, 1 ≤ a) (x : ℕ) :
    (S.filter (· ≤ x)).card = ((S : Set ℕ) ∩ Icc 1 x).ncard := by
  have h : (↑(S.filter (· ≤ x)) : Set ℕ) = (S : Set ℕ) ∩ Icc 1 x := by
    ext a
    simp only [Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_Icc]
    exact ⟨fun ha => ⟨ha.1, hS a ha.1, ha.2⟩, fun ha => ⟨ha.1, ha.2.2⟩⟩
  rw [← h, ncard_coe_finset]

/-- Restricting a finite Sidon set to a smaller dyadic horizon. -/
theorem restrict_horizon (S : Finset ℕ) {K K' : ℕ} (hK : K' ≤ K)
    (hS : (S : Set ℕ) ⊆ Icc 1 (2 ^ K)) (hsid : IsSidon (S : Set ℕ)) :
    ((S.filter (· ≤ 2 ^ K') : Finset ℕ) : Set ℕ) ⊆ Icc 1 (2 ^ K') ∧
      IsSidon ((S.filter (· ≤ 2 ^ K') : Finset ℕ) : Set ℕ) ∧
      ∀ j ≤ K', (S.filter (· ≤ 2 ^ K')).filter (· ≤ 2 ^ j) = S.filter (· ≤ 2 ^ j) := by
  refine ⟨fun a ha => ?_, fun a ha b hb c hc e he heq => ?_, fun j hj => ?_⟩
  · simp only [Finset.coe_filter, mem_setOf_eq] at ha
    exact ⟨(hS ha.1).1, ha.2⟩
  · simp only [Finset.coe_filter, mem_setOf_eq] at ha hb hc he
    exact hsid a ha.1 b hb.1 c hc.1 e he.1 heq
  · have hp : 2 ^ j ≤ 2 ^ K' := Nat.pow_le_pow_right (by decide) hj
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro a _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans hp, h⟩

/-- The finite dyadic obstruction suffices for the squared critical density bound. -/
theorem core_sq_from_finite_obstruction
    (h : ∀ d J : ℕ, 0 < d → ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j)
    (A : Set ℕ) (hS : IsSidon A) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
      ((A ∩ Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hεsq : 0 < ε ^ 2 := by positivity
  obtain ⟨d, hd⟩ := exists_nat_ge (Real.log 2 / ε ^ 2)
  have hdpos : 0 < d := by
    exact_mod_cast (div_pos hlog hεsq).trans_le hd
  have hdlog : Real.log 2 ≤ (d : ℝ) * ε ^ 2 := (div_le_iff₀ hεsq).mp hd
  obtain ⟨K, _, hK⟩ := h d N hdpos
  have hfin : (A ∩ Icc 1 (2 ^ K)).Finite :=
    (finite_Icc _ _).subset inter_subset_right
  let S := hfin.toFinset
  have hcoe : (S : Set ℕ) = A ∩ Icc 1 (2 ^ K) := hfin.coe_toFinset
  have hsub : (S : Set ℕ) ⊆ Icc 1 (2 ^ K) := hcoe ▸ inter_subset_right
  have hsid : IsSidon (S : Set ℕ) := by
    rw [hcoe]
    intro a ha b hb c hc e he heq
    exact hS a ha.1 b hb.1 c hc.1 e he.1 heq
  obtain ⟨j, hj, hjcount⟩ := hK S hsub hsid
  obtain ⟨hNj, hjK⟩ := Finset.mem_Icc.mp hj
  have hpow : (2 : ℕ) ^ j ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hjK
  rw [prefix_filter_card S (fun a ha => (hsub ha).1), hcoe, inter_assoc,
    inter_eq_right.mpr (Icc_subset_Icc_right hpow)] at hjcount
  let m : ℝ := (A ∩ Icc 1 (2 ^ j)).ncard
  have hcount : (d : ℝ) * m ^ 2 * (j : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    dsimp [m]
    exact_mod_cast hjcount
  refine ⟨2 ^ j, hNj.trans Nat.lt_two_pow_self.le, Nat.succ_le_of_lt (by positivity), ?_⟩
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  change m ^ 2 * ((j : ℝ) * Real.log 2) ≤ ε ^ 2 * (2 : ℝ) ^ j
  calc
    _ ≤ m ^ 2 * ((j : ℝ) * ((d : ℝ) * ε ^ 2)) := by gcongr
    _ = ε ^ 2 * ((d : ℝ) * m ^ 2 * (j : ℝ)) := by ring
    _ ≤ ε ^ 2 * (2 : ℝ) ^ j := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hεsq.le

/-- Regular regime: Sidon sets whose dyadic profile `c_j ^ 2 * j / 2 ^ j` stays at most
`C` on the whole window `[J, K]` have a scale in the window where it is at most `1 / d`. -/
def H1 : Prop :=
  ∀ d C J : ℕ, 0 < d → ∃ K ≥ J, ∀ S : Finset ℕ,
    (S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
    (∀ j ∈ Finset.Icc J K, (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ C * 2 ^ j) →
    ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j

/-- Irregular regime: for a suitable `C = C(d)`, a Sidon set whose dyadic profile exceeds
`C` somewhere in a window `[J, K]` has, below a later horizon `K'`, a scale `j ≥ J` where
the profile is at most `1 / d`. -/
def H2 : Prop :=
  ∀ d : ℕ, 0 < d → ∃ C : ℕ, ∀ J K : ℕ, J ≤ K → ∃ K' ≥ K, ∀ S : Finset ℕ,
    (S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K') → IsSidon (S : Set ℕ) →
    (∃ j ∈ Finset.Icc J K, C * 2 ^ j < (S.filter (· ≤ 2 ^ j)).card ^ 2 * j) →
    ∃ j ∈ Finset.Icc J K', d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j

theorem main : H1 → H2 → type_of% @Erdos1191.erdos_1191.parts.i := by
  intro hH1 hH2 A _hinf hS
  have hobs : ∀ d J : ℕ, 0 < d → ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j := by
    intro d J hd
    obtain ⟨C, hC⟩ := hH2 d hd
    obtain ⟨K1, hK1J, hK1⟩ := hH1 d C J hd
    obtain ⟨K', hK'1, hK'⟩ := hC J K1 hK1J
    refine ⟨K', hK1J.trans hK'1, fun S hsub hsid => ?_⟩
    by_cases hreg : ∀ j ∈ Finset.Icc J K1, (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ C * 2 ^ j
    · obtain ⟨hsub1, hsid1, heq⟩ := restrict_horizon S hK'1 hsub hsid
      have hreg1 : ∀ j ∈ Finset.Icc J K1,
          ((S.filter (· ≤ 2 ^ K1)).filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ C * 2 ^ j := by
        intro j hj
        rw [heq j (Finset.mem_Icc.mp hj).2]
        exact hreg j hj
      obtain ⟨j, hj, hjc⟩ := hK1 _ hsub1 hsid1 hreg1
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨j, Finset.mem_Icc.mpr ⟨hj'.1, hj'.2.trans hK'1⟩, ?_⟩
      rwa [heq j hj'.2] at hjc
    · push Not at hreg
      obtain ⟨j0, hj0, hj0c⟩ := hreg
      exact hK' S hsub hsid ⟨j0, hj0, hj0c⟩
  apply liminf_ofReal_zero_of_frequently
  intro ε hε
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨x, hNx, hx1, hx⟩ := core_sq_from_finite_obstruction hobs A hS ε hε N
  exact ⟨x, hNx, normalised_le_of_sq_le hε hx1 hx⟩

end OMA.R_Erdos1191_erdos_1191_parts_i_R2
