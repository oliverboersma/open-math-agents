import FormalConjectures.ErdosProblems.«282»

-- Problem: Erdős Problem 282 — fibonacci
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/282.lean:81 (declaration Erdos282.erdos_282.variants.fibonacci)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA

theorem rem_nonpos {A : Set ℕ} {x : ℚ} (hx : x ≤ 0) (t : ℕ) :
    Erdos282.greedyUnitFractionRem A x t = 0 := by
  rcases t with _ | t <;> rw [Erdos282.greedyUnitFractionRem, if_pos hx]

theorem sInf_eq {A : Set ℕ} {x : ℚ} (hA : ∀ m ∉ A, (m : ℚ) < 1 / x) :
    sInf {n | n ∈ A ∧ 1 / x ≤ n} = ⌈1 / x⌉₊ := by
  have hmem : ⌈1 / x⌉₊ ∈ {n | n ∈ A ∧ 1 / x ≤ (n : ℚ)} := by
    refine ⟨?_, Nat.le_ceil _⟩
    by_contra h
    exact absurd (hA _ h) (not_lt.mpr (Nat.le_ceil _))
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro b ⟨-, hb⟩
  exact Nat.ceil_le.mpr hb

theorem main (p : ℕ) : ∀ (q : ℕ) (A : Set ℕ) (x : ℚ), x = p / q → x < 1 →
    (∀ m ∉ A, (m : ℚ) < 1 / x) → ∀ t, p ≤ t + 1 →
    Erdos282.greedyUnitFractionRem A x t = 0 := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro q A x hxpq hx1 hA t ht
  by_cases hx0 : x ≤ 0
  · exact rem_nonpos hx0 t
  push Not at hx0
  have hp : 0 < (p : ℚ) := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hxpq; linarith
    · exact_mod_cast h
  have hq : 0 < (q : ℚ) := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hxpq; linarith
    · exact_mod_cast h
  set N := ⌈1 / x⌉₊ with hNdef
  have hN1 : 1 / x ≤ (N : ℚ) := Nat.le_ceil _
  have hN2 : (N : ℚ) < 1 / x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hinv : 1 / x = q / p := by rw [hxpq]; field_simp
  rw [hinv] at hN1 hN2
  have hqN : (q : ℚ) ≤ p * N := by rwa [div_le_iff₀ hp, mul_comm] at hN1
  have hqN' : (p : ℚ) * N < q + p := by
    rwa [div_add_one hp.ne', lt_div_iff₀ hp, mul_comm] at hN2
  have hqNn : q ≤ p * N := by exact_mod_cast hqN
  have hNpos : 0 < (N : ℚ) := by
    have : (0 : ℚ) < q / p := by positivity
    linarith
  have hrem : x - 1 / (N : ℚ) = ((p * N - q : ℕ) : ℚ) / ((q * N : ℕ) : ℚ) := by
    rw [hxpq, Nat.cast_sub hqNn]; push_cast; field_simp
  have hsInf := sInf_eq hA
  rcases t with _ | t <;>
    rw [Erdos282.greedyUnitFractionRem, if_neg (not_le.mpr hx0)] <;>
    simp only [hsInf, ← hNdef]
  · have hp0 : 0 < p := by exact_mod_cast hp
    have hp1 : p = 1 := by omega
    have hp1' : (p : ℚ) = 1 := by exact_mod_cast hp1
    have hNq : (N : ℚ) = q := by
      simp only [hp1', one_mul] at hqN'
      simp only [hp1, one_mul] at hqNn
      have hlt : N < q + 1 := by exact_mod_cast hqN'
      exact_mod_cast (show N = q by omega)
    rw [hxpq, hp1', hNq]; ring
  · by_cases hr0 : x - 1 / (N : ℚ) ≤ 0
    · exact rem_nonpos hr0 t
    push Not at hr0
    have hlt : p * N - q < p := by
      have : p * N < q + p := by exact_mod_cast hqN'
      omega
    apply ih _ hlt (q * N) _ _ hrem
    · have : 0 < 1 / (N : ℚ) := by positivity
      linarith
    · intro m hm
      have hrx : 1 / x < 1 / (x - 1 / N) := one_div_lt_one_div_of_lt hr0 (by
        have : 0 < 1 / (N : ℚ) := by positivity
        linarith)
      by_cases hmA : m ∈ A
      · have hmN : m = N := by
          by_contra h; exact hm ⟨hmA, h⟩
        subst hmN
        rw [lt_one_div (by positivity) hr0]
        rw [hxpq, sub_lt_iff_lt_add, div_lt_iff₀ hq]
        rw [show (1 / (N : ℚ) + 1 / N) * q = 2 * q / N by ring, lt_div_iff₀ hNpos]
        have hpq : (p : ℚ) < q := by
          rw [hxpq, div_lt_one hq] at hx1; exact hx1
        nlinarith
      · exact lt_trans (hA m hmA) hrx
    · omega

end OMA

theorem OMA.solution : type_of% @Erdos282.erdos_282.variants.fibonacci := by
  intro x hx
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨x.num.toNat, fun t ht => ?_⟩
  have hnum : 0 < x.num := Rat.num_pos.mpr hx.1
  refine OMA.main x.num.toNat x.den .univ x ?_ hx.2 (by simp) t (by omega)
  have : ((x.num.toNat : ℤ) : ℚ) = (x.num : ℚ) := by rw [Int.toNat_of_nonneg hnum.le]
  rw [show ((x.num.toNat : ℕ) : ℚ) = ((x.num.toNat : ℤ) : ℚ) by norm_cast, this]
  exact (Rat.num_div_den x).symm
