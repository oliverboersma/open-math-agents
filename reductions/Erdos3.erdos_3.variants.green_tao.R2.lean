import FormalConjectures.ErdosProblems.«3»

-- Reduction Erdos3.erdos_3.variants.green_tao.R2 of Erdős Problem 3 — green tao
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Uniform / structured split (the first step of the Green-Tao argument).
-- For S in [1, N] with density alpha = |S| / N let f = 1_S - alpha 1_[1,N] (a function on the integers)
-- and let U be its (unnormalised, integer) Gowers U^3 sum
--   sum over x, h1, h2, h3 of the product of f (x + w . h) over the 8 vertices w of {0,1}^3.
-- (f vanishes off [1, N], so x in [1, N] and h_i in [-N, N] already capture every nonzero term.)
-- H1 (uniform case, generalized von Neumann counting lemma): there is a polynomial threshold
--   kappa alpha^K N^4 such that 4-AP-free sets below it obey the bound (in fact they are tiny,
--   since uniformity forces about alpha^4 N^2 progressions).
-- H2 (structured case, inverse U^3 theorem plus density increment): for every polynomial threshold,
--   4-AP-free sets above it obey the bound.

open Asymptotics Filter

namespace OMA.R_Erdos3_erdos_3_variants_green_tao_R2

lemma free_elem {S : Finset ℕ} (hS : (S : Set ℕ).IsAPOfLengthFree 4) (a d : ℕ) (hd : 0 < d)
    (h0 : a ∈ S) (h1 : a + d ∈ S) (h2 : a + 2 * d ∈ S) (h3 : a + 3 * d ∈ S) : False := by
  classical
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro m n hmn
    have hmul : m * d = n * d := Nat.add_left_cancel hmn
    exact Nat.eq_of_mul_eq_mul_right hd hmul
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.range 4).image (fun n : ℕ => a + n * d) :=
    ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ T ↔ ∃ n, n < 4 ∧ a + n * d = x := by
    intro x
    rw [hT]
    simp
  have hcard : T.card = 4 := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : (T : Set ℕ) ⊆ (S : Set ℕ) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := (hmem x).mp hx
    interval_cases n
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have hAP : (T : Set ℕ).IsAPOfLength 4 := by
    refine ⟨a, d, ?_, ?_⟩
    · change (T : Set ℕ).encard = 4
      rw [Set.encard_coe_eq_coe_finsetCard, hcard]
      rfl
    · ext x
      constructor
      · intro hx
        obtain ⟨n, hn, rfl⟩ := (hmem x).mp hx
        exact ⟨n, by exact_mod_cast hn, by simp⟩
      · rintro ⟨n, hn, rfl⟩
        exact (hmem _).mpr ⟨n, by exact_mod_cast hn, by simp⟩
  have hbad := hS _ hsub hAP
  norm_num at hbad

lemma r_le_of_forall (N B : ℕ)
    (h : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree 4 → S.card ≤ B) :
    Erdos3.r 4 N ≤ B := by
  show sSup _ ≤ B
  apply csSup_le'
  rintro _ ⟨S, hS, hfree, rfl⟩
  exact h S hS hfree

lemma glue (h : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ,
    S ⊆ Finset.Icc 1 N →
    (∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S → a + 3 * d ∈ S → False) →
    (S.card : ℝ) ≤ C * ((N : ℝ) * Real.log N ^ (-c))) :
    type_of% @Erdos3.erdos_3.variants.green_tao := by
  obtain ⟨c, hc, C, hC, N₀, hcore⟩ := h
  refine ⟨c, hc, Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (max 3 N₀)] with N hN'
  have hN : 3 ≤ N := le_trans (le_max_left 3 N₀) hN'
  have hN₀ : N₀ ≤ N := le_trans (le_max_right 3 N₀) hN'
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : 0 ≤ Real.log (N : ℝ) ^ (-c) := Real.rpow_nonneg hlog (-c)
  have hy : 0 ≤ (N : ℝ) * Real.log (N : ℝ) ^ (-c) := by positivity
  have hx : 0 ≤ C * ((N : ℝ) * Real.log (N : ℝ) ^ (-c)) := by positivity
  have hr : Erdos3.r 4 N ≤ ⌊C * ((N : ℝ) * Real.log (N : ℝ) ^ (-c))⌋₊ := by
    apply r_le_of_forall
    intro S hS hfree
    rw [Nat.le_floor_iff hx]
    exact hcore N hN₀ S hS (free_elem hfree)
  have hr' : (Erdos3.r 4 N : ℝ) ≤ C * ((N : ℝ) * Real.log (N : ℝ) ^ (-c)) :=
    le_trans (by exact_mod_cast hr) (Nat.floor_le hx)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hy]
  exact hr'

/-- Monotonicity of the bound in the constants once log N is at least 1. -/
lemma bound_mono {N : ℕ} (hN : 3 ≤ N) {x c c' C C' : ℝ} (hc : c' ≤ c) (hC : C ≤ C')
    (hC0 : 0 ≤ C) (h : x ≤ C * ((N : ℝ) * Real.log N ^ (-c))) :
    x ≤ C' * ((N : ℝ) * Real.log N ^ (-c')) := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hp : Real.log (N : ℝ) ^ (-c) ≤ Real.log (N : ℝ) ^ (-c') :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  have hp0 : 0 ≤ Real.log (N : ℝ) ^ (-c) := Real.rpow_nonneg (by linarith) _
  have hp0' : 0 ≤ Real.log (N : ℝ) ^ (-c') := Real.rpow_nonneg (by linarith) _
  have hN0 : (0 : ℝ) ≤ N := by linarith
  calc x ≤ C * ((N : ℝ) * Real.log N ^ (-c)) := h
    _ ≤ C * ((N : ℝ) * Real.log N ^ (-c')) := by gcongr
    _ ≤ C' * ((N : ℝ) * Real.log N ^ (-c')) := by gcongr

def H1 : Prop := ∃ K : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
  ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
    (∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S → a + 3 * d ∈ S → False) →
    (let f : ℤ → ℝ := fun x => (if 0 < x ∧ x.toNat ∈ S then (1 : ℝ) else 0) -
        (if 0 < x ∧ x ≤ (N : ℤ) then (S.card : ℝ) / N else 0)
     ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ a ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (-(N : ℤ)) N,
       ∑ e ∈ Finset.Icc (-(N : ℤ)) N,
         f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
           f (x + b + e) * f (x + a + b + e)
       < κ * ((S.card : ℝ) / N) ^ K * (N : ℝ) ^ 4) →
    (S.card : ℝ) ≤ C * ((N : ℝ) * Real.log N ^ (-c))

def H2 : Prop := ∀ K : ℕ, ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
  ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
    (∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S → a + 3 * d ∈ S → False) →
    ¬ (let f : ℤ → ℝ := fun x => (if 0 < x ∧ x.toNat ∈ S then (1 : ℝ) else 0) -
        (if 0 < x ∧ x ≤ (N : ℤ) then (S.card : ℝ) / N else 0)
     ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ a ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (-(N : ℤ)) N,
       ∑ e ∈ Finset.Icc (-(N : ℤ)) N,
         f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
           f (x + b + e) * f (x + a + b + e)
       < κ * ((S.card : ℝ) / N) ^ K * (N : ℝ) ^ 4) →
    (S.card : ℝ) ≤ C * ((N : ℝ) * Real.log N ^ (-c))

theorem main : H1 → H2 → type_of% @Erdos3.erdos_3.variants.green_tao := by
  intro h1 h2
  obtain ⟨K, κ, hκ, c₁, hc₁, C₁, hC₁, N₁, hu⟩ := h1
  obtain ⟨c₂, hc₂, C₂, hC₂, N₂, hs⟩ := h2 K κ hκ
  apply glue
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max C₁ C₂, lt_max_of_lt_left hC₁, max 3 (max N₁ N₂), ?_⟩
  intro N hN S hS hfree
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  exact (Classical.em _).elim
    (fun h => bound_mono hN3 (min_le_left _ _) (le_max_left _ _) hC₁.le (hu N hN1 S hS hfree h))
    (fun h => bound_mono hN3 (min_le_right _ _) (le_max_right _ _) hC₂.le (hs N hN2 S hS hfree h))

end OMA.R_Erdos3_erdos_3_variants_green_tao_R2
