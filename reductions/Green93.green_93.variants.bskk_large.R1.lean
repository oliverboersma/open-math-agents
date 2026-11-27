import FormalConjectures.GreensOpenProblems.«93»

/-!
The small- and intermediate-degree bounds from Bary-Soroker, Koukoulopoulos and Kozma,
*Irreducibility of random polynomials: general measures*, Sections 2.1, 2.2 and 3.1.
The two hypotheses absorb fixed constants into the exponent and degree threshold.
The reduction proves that their finite counts bound the reducible sample.
-/

namespace OMA.R_Green93_green_93_variants_bskk_large_R1

open Polynomial

/-- The conditional count of vectors admitting a positive divisor of degree at most `n^(1/10)`. -/
def H1 : Prop := by
  classical
  exact ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n →
    (Real.log (M : ℝ)) ^ 3 ≤ n →
    let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
    ((eligible.filter fun a => ∃ g : ℤ[X], g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      0 < g.natDegree ∧ (g.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 2) * eligible.card

/-- The conditional count in the remaining degree range, up to half the degree. -/
def H2 : Prop := by
  classical
  exact ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n →
    (Real.log (M : ℝ)) ^ 3 ≤ n →
    let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
    ((eligible.filter fun a => ∃ g : ℤ[X], g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 2) * eligible.card

lemma green93_monic_of_degree {n : ℕ} (a : Fin n → ℕ) :
    IsMonicOfDegree (Green93.monicPoly a) n := by
  cases n with
  | zero => simp [Green93.monicPoly]
  | succ n =>
    unfold Green93.monicPoly
    apply (isMonicOfDegree_X_pow ℤ (n + 1)).add_right
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ ?_) (Nat.lt_succ_self n)
    intro i _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ i.isLt)

lemma green93_coeff_below {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (Green93.monicPoly a).coeff i.val = (a i : ℤ) := by
  classical
  simp only [Green93.monicPoly, coeff_add, coeff_X_pow, if_neg i.isLt.ne, zero_add,
    finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun h => hji (Fin.ext h.symm))
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

open scoped Classical in
lemma green93_sample_nonempty {M n : ℕ} (hM : 1 ≤ M) (hn : 0 < n) :
    (Finset.univ.filter fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0).Nonempty := by
  let ones : Fin n → Fin (M + 1) := fun _ => ⟨1, by omega⟩
  refine ⟨ones, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have h := green93_coeff_below (fun j => (ones j : ℕ)) ⟨0, hn⟩
  rw [h]
  norm_num [ones]

lemma green93_small_factor_of_reducible (f : ℤ[X]) (hm : f.Monic)
    (hpos : 0 < f.natDegree) (hirr : ¬ Irreducible f) :
    ∃ g : ℤ[X], g ∣ f ∧ 0 < g.natDegree ∧ 2 * g.natDegree ≤ f.natDegree := by
  classical
  have hf : f ≠ 1 := by
    intro heq
    simp [heq] at hpos
  rw [hm.irreducible_iff_lt_natDegree_lt hf] at hirr
  push Not at hirr
  obtain ⟨g, -, hg, hdvd⟩ := hirr
  rw [Finset.mem_Ioc] at hg
  exact ⟨g, hdvd, hg.1, by omega⟩

theorem main : H1 → H2 → type_of% @Green93.green_93.variants.bskk_large := by
  classical
  intro hLow hHigh
  obtain ⟨c₁, hc₁, n₁, bound₁⟩ := hLow
  obtain ⟨c₂, hc₂, n₂, bound₂⟩ := hHigh
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max 1 (max n₁ n₂), ?_⟩
  intro M n hM hn hlog
  have hn1 : 1 ≤ n := (le_max_left 1 (max n₁ n₂)).trans hn
  have hmax : max n₁ n₂ ≤ n := (le_max_right 1 (max n₁ n₂)).trans hn
  have h₁ := bound₁ M n hM ((le_max_left n₁ n₂).trans hmax) hlog
  have h₂ := bound₂ M n hM ((le_max_right n₁ n₂).trans hmax) hlog
  let poly (a : Fin n → Fin (M + 1)) := Green93.monicPoly (fun j => (a j : ℕ))
  let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (poly a).coeff 0 ≠ 0
  let low := eligible.filter fun a => ∃ g : ℤ[X], g ∣ poly a ∧
    0 < g.natDegree ∧ (g.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)
  let high := eligible.filter fun a => ∃ g : ℤ[X], g ∣ poly a ∧
    (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n
  let good := eligible.filter fun a => Irreducible (poly a)
  let bad := eligible.filter fun a => ¬ Irreducible (poly a)
  change (low.card : ℝ) ≤ ((n : ℝ) ^ (-c₁) / 2) * eligible.card at h₁
  change (high.card : ℝ) ≤ ((n : ℝ) ^ (-c₂) / 2) * eligible.card at h₂
  have hSub : bad ⊆ low ∪ high := by
    intro a ha
    obtain ⟨heligible, hred⟩ := Finset.mem_filter.mp ha
    have hdegree : (poly a).natDegree = n := (green93_monic_of_degree _).natDegree_eq
    have hmonic : (poly a).Monic := (green93_monic_of_degree _).monic
    obtain ⟨g, hdvd, hpos, hhalf⟩ := green93_small_factor_of_reducible
      (poly a) hmonic (by omega) hred
    rw [hdegree] at hhalf
    by_cases h : (g.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heligible, g, hdvd, hpos, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨heligible, g, hdvd, (lt_of_not_ge h).le, hhalf⟩)
  have hbad : (bad.card : ℝ) ≤ (low.card : ℝ) + high.card := by
    exact_mod_cast ((Finset.card_le_card hSub).trans (Finset.card_union_le low high))
  have hsum : (good.card : ℝ) + bad.card = eligible.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := eligible) (p := fun a => Irreducible (poly a)))
  have nreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hpow₁ := Real.rpow_le_rpow_of_exponent_le nreal (neg_le_neg (min_le_left c₁ c₂))
  have hpow₂ := Real.rpow_le_rpow_of_exponent_le nreal (neg_le_neg (min_le_right c₁ c₂))
  have hcard0 : (0 : ℝ) ≤ eligible.card := by positivity
  have hscaled₁ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow₁ (by norm_num : (0 : ℝ) ≤ 2)) hcard0
  have hscaled₂ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow₂ (by norm_num : (0 : ℝ) ≤ 2)) hcard0
  have htotal : (bad.card : ℝ) ≤ (n : ℝ) ^ (-min c₁ c₂) * eligible.card := by
    linarith
  have hcard : (0 : ℝ) < eligible.card := by
    exact_mod_cast Finset.card_pos.mpr (green93_sample_nonempty (M := M) (n := n) (by omega) (by omega))
  have hprob : Green93.irreducibleProb M n = (good.card : ℝ) / eligible.card := by
    simp only [Green93.irreducibleProb, good, eligible, poly, Finset.filter_filter, and_comm]
  rw [hprob]
  apply (le_div_iff₀ hcard).2
  linarith

end OMA.R_Green93_green_93_variants_bskk_large_R1
