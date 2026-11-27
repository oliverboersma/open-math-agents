import FormalConjectures.ErdosProblems.«208»

/-!
An interval of length 8L has at most 7L positions covered by squares of
integers from 2 through L. A bound for coverage by larger prime squares
therefore suffices to find a squarefree integer in a logarithmic interval.
-/

open Asymptotics Filter Finset Real
open Erdos208.erdos208

namespace OMA.R_Erdos208_erdos_208_variants_log_bound_R1

def H1 : Prop :=
  ∀ x L : ℕ,
    #{y ∈ Finset.Ioc x (x + 8 * L) | ∃ d ∈ Finset.Icc 2 L, d * d ∣ y} ≤ 7 * L

def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
    (let L := Nat.ceil (c * Real.log x)
     ((Finset.Ioc x (x + 8 * L)).filter (fun y =>
       ∃ p ∈ Finset.Ioc L (Nat.sqrt (x + 8 * L)), p.Prime ∧ p * p ∣ y)).card < L)

section Proof

private theorem interval_has_squarefree (x L : ℕ)
    (hSmall : #{y ∈ Finset.Ioc x (x + 8 * L) | ∃ d ∈ Finset.Icc 2 L, d * d ∣ y} ≤ 7 * L)
    (hLarge : #{y ∈ Finset.Ioc x (x + 8 * L) |
      ∃ p ∈ Finset.Ioc L (Nat.sqrt (x + 8 * L)), p.Prime ∧ p * p ∣ y} < L) :
    ∃ y ∈ Finset.Ioc x (x + 8 * L), Squarefree y := by
  let I := Finset.Ioc x (x + 8 * L)
  let A := I.filter (fun y => ∃ d ∈ Finset.Icc 2 L, d * d ∣ y)
  let B := I.filter (fun y => ∃ p ∈ Finset.Ioc L (Nat.sqrt (x + 8 * L)), p.Prime ∧ p * p ∣ y)
  by_contra! hno
  have hcover : I ⊆ A ∪ B := by
    intro y hy
    have hbad := (Nat.squarefree_iff_prime_squarefree.not).mp (hno y hy)
    push Not at hbad
    obtain ⟨p, hprime, hdiv⟩ := hbad
    have hy' := Finset.mem_Ioc.mp hy
    by_cases hsmall : p ≤ L
    · exact Finset.mem_union_left B (Finset.mem_filter.mpr
        ⟨hy, p, Finset.mem_Icc.mpr ⟨hprime.two_le, hsmall⟩, hdiv⟩)
    · have hle := (Nat.le_of_dvd (by omega : 0 < y) hdiv).trans hy'.2
      exact Finset.mem_union_right A (Finset.mem_filter.mpr
        ⟨hy, p, Finset.mem_Ioc.mpr ⟨by omega, Nat.le_sqrt.mpr hle⟩, hprime, hdiv⟩)
  have hle := (Finset.card_le_card hcover).trans (Finset.card_union_le A B)
  have hI : I.card = 8 * L := by simp [I]
  change A.card ≤ 7 * L at hSmall
  change B.card < L at hLarge
  omega

private theorem squarefree_infinite : (Set.ofPred (Squarefree : ℕ → Prop)).Infinite :=
  Nat.infinite_setOfPred_prime.mono (fun _ hp => (Nat.prime_iff.mp hp).squarefree)

theorem main : H1 → H2 → type_of% @Erdos208.erdos_208.variants.log_bound := by
  intro hSmall ⟨c, hc, hLarge⟩
  have hsMono : StrictMono s := Nat.nth_strictMono squarefree_infinite
  have hsTop := hsMono.tendsto_atTop
  have hlogTop : Tendsto (fun n : ℕ => Real.log (s n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsTop)
  refine Asymptotics.IsBigO.of_bound (8 * (c + 1)) ?_
  filter_upwards [hsTop.eventually hLarge, hlogTop.eventually_ge_atTop 1] with n hlarge hlog
  let L := ⌈c * Real.log (s n : ℝ)⌉₊
  obtain ⟨y, hy, hsq⟩ := interval_has_squarefree (s n) L (hSmall (s n) L) hlarge
  obtain ⟨m, hm⟩ := Nat.subset_range_nth
    (show y ∈ Set.ofPred (Squarefree : ℕ → Prop) from hsq)
  change s m = y at hm
  have hy' := Finset.mem_Ioc.mp hy
  have hnlt : n < m := hsMono.lt_iff_lt.mp (by rw [hm]; exact hy'.1)
  have hle : s (n + 1) ≤ s n + 8 * L := (hsMono.monotone (by omega : n + 1 ≤ m)).trans
    (hm ▸ hy'.2)
  have hleq : (s (n + 1) : ℝ) - (s n : ℝ) ≤ 8 * (L : ℝ) := by
    have h' : (s (n + 1) : ℝ) ≤ (s n : ℝ) + 8 * (L : ℝ) := by exact_mod_cast hle
    linarith
  have hnonneg : 0 ≤ (s (n + 1) : ℝ) - (s n : ℝ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hsMono.monotone (by omega : n ≤ n + 1)
  have hlog0 : 0 ≤ Real.log (s n : ℝ) := by linarith
  have hceil : (L : ℝ) < c * Real.log (s n : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hlog0]
  nlinarith

end Proof

end OMA.R_Erdos208_erdos_208_variants_log_bound_R1
