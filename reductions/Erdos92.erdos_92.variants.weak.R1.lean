import FormalConjectures.ErdosProblems.«92»

-- Reduction Erdos92.erdos_92.variants.weak.R1 of Erdős Problem 92 — weak
-- Credit: @mrmario2202
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
`erdos_92.variants.weak` says that `f n ≤ n ^ o(1)` fails, where `f n` is the largest `k` such that
some `n`-point planar set has, around every point, `k` other points on a common circle.
The source derives this from the disproof of the unit distance conjecture (Erdős 90).
This file isolates the two ingredients and proves the asymptotic glue in `main`.
- `H1` (Sawin 2026, polynomial unit distance lower bound): for some `c > 0` there are arbitrarily
  large planar point sets `P` with at least `|P| ^ (1 + c)` unit distances. This is the content
  of `Erdos90.erdos_90.variants.polynomial_lower_bound`, stated here without `maxUnitDistances`.
- `H2` (elementary peeling bound): if `f m ≤ D` for every `m ≤ |P|`, then `P` spans at most
  `2 |P| D` unit distances. Some point of `P` has at most `f |P|` unit neighbours (the unit
  circle around it is one equidistant class); remove it and induct. This bridge is already proved
  in the accepted file `proofs/Erdos92.erdos_92.variants.strong.lean` (`directedEdges_le` and
  `unitDistNum_le` there).
`main`: if `f m ≤ m ^ (o m)` with `o → 0`, then eventually `o m < c / 2`, so `f m ≤ M₀ + n ^ (c / 2)`
for all `m ≤ n`; `H2` gives at most `2 n (M₀ + n ^ (c / 2))` unit distances, which is less than
`n ^ (1 + c)` for large `n`, contradicting `H1`.
-/

namespace OMA.R_Erdos92_erdos_92_variants_weak_R1

open Filter
open scoped Topology

/-- Polynomial unit distance lower bound (Sawin): for some `c > 0`, there are arbitrarily large
finite planar point sets `P` spanning at least `|P| ^ (1 + c)` unit distances. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    N ≤ P.card ∧ (P.card : ℝ) ^ (1 + c) ≤ (unitDistNum P : ℝ)

/-- Peeling bound: a planar point set all of whose sizes `m ≤ |P|` have `f m ≤ D` spans at most
`2 |P| D` unit distances. -/
def H2 : Prop :=
  ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))) (D : ℝ),
    (∀ m ≤ P.card, (Erdos92.f m : ℝ) ≤ D) → (unitDistNum P : ℝ) ≤ 2 * (P.card : ℝ) * D

/-- Trivial bound `f n ≤ n`. -/
lemma f_le_card (n : ℕ) : Erdos92.f n ≤ n := by
  unfold Erdos92.f
  refine csSup_le' fun m hm => ?_
  rcases hm with ⟨P, hcard, ⟨x, hx⟩, hall⟩
  refine (hall x hx).trans ?_
  unfold Erdos92.maxEquidistantPointsAt
  refine csSup_le' fun m hm => ?_
  rw [Finset.mem_coe, Finset.mem_image] at hm
  obtain ⟨d, _, rfl⟩ := hm
  exact (Finset.card_filter_le _ _).trans (Finset.card_erase_le.trans_eq hcard)

theorem main : H1 → H2 → type_of% @Erdos92.erdos_92.variants.weak := by
  intro hH1 hH2
  obtain ⟨c, hc, h1⟩ := hH1
  have h2 : ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))) (D : ℝ),
      (∀ m ≤ P.card, (Erdos92.f m : ℝ) ≤ D) → (unitDistNum P : ℝ) ≤ 2 * (P.card : ℝ) * D :=
    hH2
  rintro ⟨o, ho, hfo⟩
  have hc2 : 0 < c / 2 := half_pos hc
  have ho' : Tendsto o atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp ho
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (ho'.eventually (eventually_lt_nhds hc2))
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (c / 2)) atTop atTop :=
    (tendsto_rpow_atTop hc2).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp (htend.eventually_ge_atTop (2 * (M₀ : ℝ) + 3))
  obtain ⟨P, hNP, hP⟩ := h1 (max K 1)
  have hn1 : 1 ≤ P.card := (le_max_right _ _).trans hNP
  have hnK : K ≤ P.card := (le_max_left _ _).trans hNP
  have hn0 : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast (show 0 < P.card by omega)
  have ht : 2 * (M₀ : ℝ) + 3 ≤ (P.card : ℝ) ^ (c / 2) := hK P.card hnK
  have hM : (0 : ℝ) ≤ (M₀ : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) ≤ (P.card : ℝ) ^ (c / 2) := Real.rpow_nonneg hn0.le _
  have hD : ∀ m ≤ P.card, (Erdos92.f m : ℝ) ≤ (M₀ : ℝ) + (P.card : ℝ) ^ (c / 2) := by
    intro m hm
    by_cases hmM : m < M₀ + 1
    · have hfm : Erdos92.f m ≤ M₀ := (f_le_card m).trans (by omega)
      have hfm' : (Erdos92.f m : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hfm
      linarith
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
      have hom : o m < c / 2 := hM₀ m (by omega)
      have hmn : (m : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hm
      have hchain : (Erdos92.f m : ℝ) ≤ (P.card : ℝ) ^ (c / 2) :=
        calc (Erdos92.f m : ℝ) ≤ (m : ℝ) ^ (o m) := hfo m
          _ ≤ (m : ℝ) ^ (c / 2) := Real.rpow_le_rpow_of_exponent_le hm1 hom.le
          _ ≤ (P.card : ℝ) ^ (c / 2) := Real.rpow_le_rpow (by linarith) hmn hc2.le
      linarith
  have hup := h2 P _ hD
  have hsq : ((P.card : ℝ) ^ (c / 2)) ^ 2 = (P.card : ℝ) ^ c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  have hpow : (P.card : ℝ) ^ (1 + c) = (P.card : ℝ) * ((P.card : ℝ) ^ (c / 2)) ^ 2 := by
    rw [hsq, Real.rpow_add hn0, Real.rpow_one]
  have hlow : (P.card : ℝ) * ((P.card : ℝ) ^ (c / 2)) ^ 2 ≤ (unitDistNum P : ℝ) := by
    rw [← hpow]
    exact hP
  have hq : 0 < ((P.card : ℝ) ^ (c / 2)) ^ 2 - 2 * (M₀ : ℝ) - 2 * (P.card : ℝ) ^ (c / 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hpos,
      mul_nonneg hM (show (0 : ℝ) ≤ (P.card : ℝ) ^ (c / 2) - 1 by linarith)]
  nlinarith [mul_pos hn0 hq]

end OMA.R_Erdos92_erdos_92_variants_weak_R1
