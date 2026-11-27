import FormalConjectures.Wikipedia.ChowlaLiouvilleConjecture

-- Reduction ChowlaLiouvilleConjecture.chowla_liouville_conjecture.R1 of Chowla's Conjecture
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target quantifies over every number k of shifts. The three hypotheses separate it by
-- what is known, after normalising the shift tuple (sorted, smallest shift moved to 0):
--   H1  one point: the mean value of the Liouville function is 0 (prime number theorem strength;
--       a Lean proof of this exact statement is already merged in this repository as the variant
--       one_point of the same upstream file).
--   H2  two points: (1/N) sum_{n<=N} lambda(n) lambda(n+d) -> 0 for every d >= 1. This is the
--       ordinary two-point Chowla conjecture, announced as proved in September 2026 (OpenAI,
--       Ordinary two-point correlations of multiplicative functions, 87 pp., with a Lean
--       formalisation in github.com/openai/math, lean/ComparatorChallenges/
--       OrdinaryTwoPointCorrelations.lean, theorem liouville_log_saving; take a1 = a2 = 1,
--       b1 = 0, b2 = d there). That development is about 7 MB of Lean on another toolchain.
--   H3  three or more points, in normal form: lambda(n) * prod_i lambda(n + g i) with
--       0 < g 0 < g 1 < ... and at least two positive shifts. This is the open core: for three
--       points only logarithmically averaged results are known (Tao and Teravainen), and for
--       an even number of points at least four not even those.
-- main does the bookkeeping: sorting an injective tuple, splitting off the smallest shift, and
-- moving the summation variable by a fixed amount (which does not change the Cesaro limit).

namespace OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_R1

def H1 : Prop :=
  Filter.Tendsto
    (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)) / (N : ℝ))
    Filter.atTop (nhds 0)

def H2 : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    Filter.Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + d) : ℝ)) / (N : ℝ))
      Filter.atTop (nhds 0)

def H3 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ g : Fin k → ℕ, StrictMono g → (∀ i, 0 < g i) →
    Filter.Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n : ℝ) *
            ∏ i : Fin k, (ArithmeticFunction.liouville (n + g i) : ℝ)) / (N : ℝ))
      Filter.atTop (nhds 0)

/-- Moving the summation variable by a fixed amount keeps a Cesaro limit equal to zero. -/
lemma shift_tendsto (F : ℕ → ℝ) (m : ℕ)
    (hF : Filter.Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, F n) / (N : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, F (n + m)) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  have key : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, F (n + m)
      = ∑ n ∈ Finset.Icc 1 (N + m), F n - ∑ n ∈ Finset.Icc 1 m, F n := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have e : N + 1 + m = (N + m) + 1 := by omega
      rw [e, Finset.sum_Icc_succ_top (by omega)]
      ring
  have h1 : Filter.Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 (N + m), F n) / ((N + m : ℕ) : ℝ))
      Filter.atTop (nhds 0) := hF.comp (Filter.tendsto_add_atTop_nat m)
  have h2 : Filter.Tendsto (fun N : ℕ ↦ (m : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)
  have h3 : Filter.Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 m, F n) / (N : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h4 : Filter.Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 (N + m), F n) / ((N + m : ℕ) : ℝ) * (1 + (m : ℝ) / (N : ℝ))
        - (∑ n ∈ Finset.Icc 1 m, F n) / (N : ℝ))
      Filter.atTop (nhds (0 * (1 + 0) - 0)) :=
    (h1.mul (tendsto_const_nhds.add h2)).sub h3
  have h5 : (0 : ℝ) * (1 + 0) - 0 = 0 := by ring
  rw [h5] at h4
  refine h4.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  rw [key N]
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNm : (0 : ℝ) < ((N + m : ℕ) : ℝ) := by
    have : 0 < N + m := by omega
    exact_mod_cast this
  have hcast : ((N + m : ℕ) : ℝ) = (N : ℝ) + (m : ℝ) := by push_cast; ring
  rw [hcast] at hNm ⊢
  field_simp

/-- Normal form of an injective shift tuple: sort it and split off the smallest shift. -/
lemma normal_form (k : ℕ) (h : Fin (k + 1) → ℕ) (hh : Function.Injective h) :
    ∃ (m : ℕ) (g : Fin k → ℕ), StrictMono g ∧ (∀ i, 0 < g i) ∧
      ∀ f : ℕ → ℝ, ∏ j : Fin (k + 1), f (h j) = f m * ∏ i : Fin k, f (m + g i) := by
  classical
  have hcard : (Finset.univ.image h).card = k + 1 := by
    rw [Finset.card_image_of_injective _ hh, Finset.card_univ, Fintype.card_fin]
  let e : Fin (k + 1) ↪o ℕ := (Finset.univ.image h).orderEmbOfFin hcard
  have he : StrictMono e := e.strictMono
  have h0 : ∀ i : Fin k, e 0 < e i.succ := fun i => he (Fin.succ_pos i)
  refine ⟨e 0, fun i => e i.succ - e 0, ?_, ?_, ?_⟩
  · intro i j hij
    have h1 : e i.succ < e j.succ := he (Fin.succ_lt_succ_iff.mpr hij)
    have h2 := h0 i
    show e i.succ - e 0 < e j.succ - e 0
    omega
  · intro i
    have h2 := h0 i
    show 0 < e i.succ - e 0
    omega
  · intro f
    have e1 : ∏ j : Fin (k + 1), f (h j) = ∏ x ∈ Finset.univ.image h, f x := by
      rw [Finset.prod_image (fun a _ b _ hab => hh hab)]
    have e2 : ∏ j : Fin (k + 1), f (e j) = ∏ x ∈ Finset.univ.image h, f x := by
      have himg : Finset.image e Finset.univ = Finset.univ.image h :=
        Finset.image_orderEmbOfFin_univ _ hcard
      rw [← himg, Finset.prod_image (fun a _ b _ hab => e.injective hab)]
    rw [e1, ← e2, Fin.prod_univ_succ]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have h2 := h0 i
    have e3 : e 0 + (e i.succ - e 0) = e i.succ := by omega
    rw [e3]

theorem main : H1 → H2 → H3 →
    type_of% @ChowlaLiouvilleConjecture.chowla_liouville_conjecture := by
  intro h1 h2 h3 k hk h hh
  obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, g, hg, hpos, hprod⟩ := normal_form k h hh
  -- the normalised correlation
  have core : Filter.Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n : ℝ) *
            ∏ i : Fin k, (ArithmeticFunction.liouville (n + g i) : ℝ)) / (N : ℝ))
      Filter.atTop (nhds 0) := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · have h1' : Filter.Tendsto
            (fun N : ℕ ↦
              (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)) / (N : ℝ))
            Filter.atTop (nhds 0) := h1
        simpa using h1'
      · have hd := h2 (g 0) (hpos 0)
        simpa using hd
    · exact h3 k hk2 g hg hpos
  have sh := shift_tendsto
    (fun n : ℕ => (ArithmeticFunction.liouville n : ℝ) *
      ∏ i : Fin k, (ArithmeticFunction.liouville (n + g i) : ℝ)) m core
  refine sh.congr (fun N => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hp : ∏ j : Fin (k + 1), (ArithmeticFunction.liouville (n + h j) : ℝ)
      = (ArithmeticFunction.liouville (n + m) : ℝ) *
        ∏ i : Fin k, (ArithmeticFunction.liouville (n + (m + g i)) : ℝ) :=
    hprod (fun x : ℕ => (ArithmeticFunction.liouville (n + x) : ℝ))
  refine Eq.trans ?_ hp.symm
  simp only [add_assoc]

end OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_R1
