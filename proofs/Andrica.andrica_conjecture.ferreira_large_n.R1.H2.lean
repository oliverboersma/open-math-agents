import OMAReductions.R_Andrica_andrica_conjecture_ferreira_large_n_R1
import Mathlib

-- Step Andrica.andrica_conjecture.ferreira_large_n.R1.H2: hypothesis H2 of reduction
-- Andrica.andrica_conjecture.ferreira_large_n.R1
-- Credit: @ivillar

/-!
Let `p = p_n ≥ X²` and `x = ⌊√p⌋ ≥ X`, so `x² ≤ p < (x+1)²`. Oppermann at `x + 1` gives primes in
`((x+1)x, (x+1)²)` and in `((x+1)², (x+1)(x+2))`. If `p < x(x+1)` the first is above `p`, so
`p_{n+1} < (x+1)² ≤ (√p + 1)²`. Otherwise the second is above `p`, so
`p_{n+1} ≤ x² + 3x + 1 < x(x+1) + 2√p + 1 ≤ (√p + 1)²` since `√p > x`.
-/

namespace OMA.AndricaH2

theorem next_le (n q : ℕ) (hq : q.Prime) (hlt : Nat.nth Nat.Prime n < q) :
    Nat.nth Nat.Prime (n + 1) ≤ q := by
  have hinf := Nat.infinite_setOfPred_prime
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite hinf, if_pos (Nat.prime_nth_prime n)]
  have h2 : n + 1 ≤ Nat.count Nat.Prime q := h1 ▸ Nat.count_monotone _ hlt
  calc Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
        Nat.nth_monotone hinf h2
    _ = q := Nat.nth_count hq

end OMA.AndricaH2

theorem OMA.solution : OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1.H2 := by
  unfold OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1.H2
  intro X hOpp n hn
  have hp2 := (Nat.prime_nth_prime n).two_le
  set p := Nat.nth Nat.Prime n with hpdef
  set x := Nat.sqrt p with hxdef
  have hx1 : x ^ 2 ≤ p := Nat.sqrt_le' p
  have hx2 : p < (x + 1) ^ 2 := Nat.lt_succ_sqrt' p
  have hX : X ≤ x := Nat.le_sqrt'.mpr hn
  have hx0 : 1 ≤ x := by
    by_contra h
    have : x = 0 := by omega
    rw [this] at hx2
    omega
  obtain ⟨⟨q1, hq1, hq1p⟩, ⟨q2, hq2, hq2p⟩⟩ := hOpp (x + 1) (by omega)
  rw [Finset.mem_Ioo] at hq1 hq2
  have e1 : (x + 1) * (x + 1 - 1) = (x + 1) * x := by rw [Nat.add_sub_cancel]
  rw [e1] at hq1
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsx : (x : ℝ) ≤ Real.sqrt p := Real.nat_sqrt_le_real_sqrt
  have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  rw [sub_lt_iff_lt_add, Real.sqrt_lt' (by positivity)]
  by_cases hc : p < x * (x + 1)
  · have hnext := OMA.AndricaH2.next_le n q1 hq1p (by nlinarith)
    have h1 : ((Nat.nth Nat.Prime (n + 1) : ℕ) : ℝ) < ((x + 1 : ℕ) : ℝ) ^ 2 := by
      have : Nat.nth Nat.Prime (n + 1) < (x + 1) ^ 2 := lt_of_le_of_lt hnext (by nlinarith)
      exact_mod_cast this
    push_cast at h1
    nlinarith
  · push Not at hc
    have hnext := OMA.AndricaH2.next_le n q2 hq2p (by nlinarith)
    have h1 : Nat.nth Nat.Prime (n + 1) + 1 ≤ (x + 1) * (x + 1 + 1) := by omega
    have h1R : ((Nat.nth Nat.Prime (n + 1) : ℕ) : ℝ) + 1 ≤ ((x : ℝ) + 1) * ((x : ℝ) + 1 + 1) := by
      exact_mod_cast h1
    have hcR : (x : ℝ) * ((x : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hc
    have hxlt : (x : ℝ) < Real.sqrt p := by
      rw [Real.lt_sqrt (Nat.cast_nonneg _)]
      have : x ^ 2 < p := by nlinarith
      exact_mod_cast this
    nlinarith
