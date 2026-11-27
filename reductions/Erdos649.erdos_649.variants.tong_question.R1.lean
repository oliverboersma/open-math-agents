import FormalConjectures.ErdosProblems.«649»
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

/-!
Dedicating the exponent to the multiplicative order gives an exact test for
pure powers of q. The residual infinitude statement asks for primes failing
this test that also cannot occur with a mixed q-smooth successor.
-/

namespace OMA.R_Erdos649_erdos_649_variants_tong_question_R1

def H1 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → q < p →
    ((∃ e : ℕ, 0 < e ∧ (q ^ e - 1).maxPrimeFac = p) ↔
      (q ^ orderOf (q : ZMod p) - 1).maxPrimeFac = p)

def H2 : Prop :=
  ∀ q : ℕ, q.Prime → Odd q →
    {p : ℕ | p.Prime ∧ q < p ∧
      (q ^ orderOf (q : ZMod p) - 1).maxPrimeFac ≠ p ∧
      ∀ m : ℕ, m.maxPrimeFac = q →
        (∃ r : ℕ, r.Prime ∧ r < q ∧ r ∣ m) →
        (m - 1).maxPrimeFac ≠ p}.Infinite

section Proof

private theorem splitNext (m q : ℕ) (hq : q.Prime) (hmax : m.maxPrimeFac = q) :
    (∃ e : ℕ, 0 < e ∧ m = q ^ e) ∨ (∃ r : ℕ, r.Prime ∧ r < q ∧ r ∣ m) := by
  by_cases h : ∃ r : ℕ, r.Prime ∧ r < q ∧ r ∣ m
  · exact Or.inr h
  · have hm : 1 < m :=
      (Nat.one_lt_maxPrimeFac_iff m).mp (by simpa only [hmax] using hq.one_lt)
    have he := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : m ≠ 0)
        (fun {r} hr hrd => by
          have hle : r ≤ q := hmax ▸ Nat.le_maxPrimeFac (by omega) hr hrd
          exact le_antisymm hle (le_of_not_gt (fun hlt => h ⟨r, hr, hlt, hrd⟩)))
    have hePos : 0 < m.primeFactorsList.length := by
      by_contra h
      have hp := he
      rw [Nat.eq_zero_of_not_pos h, pow_zero] at hp
      omega
    exact Or.inl ⟨_, hePos, he⟩

theorem main : H1 → H2 → type_of% @Erdos649.erdos_649.variants.tong_question := by
  intro pureCriterion infiniteAvoidance q hq hqOdd
  apply (infiniteAvoidance q hq hqOdd).mono
  rintro p ⟨hp, hqp, hnotPure, hnotMixed⟩
  refine ⟨hp, ?_⟩
  rintro ⟨n, hn, hnNext⟩
  rcases splitNext (n + 1) q hq hnNext with ⟨e, he, hpow⟩ | hMixed
  · have hpred : q ^ e - 1 = n := by omega
    exact hnotPure ((pureCriterion p q hp hq hqp).mp ⟨e, he, by simpa only [hpred] using hn⟩)
  · exact hnotMixed (n + 1) hnNext hMixed (by simpa using hn)

end Proof

end OMA.R_Erdos649_erdos_649_variants_tong_question_R1
