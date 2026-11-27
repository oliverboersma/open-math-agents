import OMAReductions.R_Erdos824_erdos_824_variants_squarefree_R1

/-! Extracting primes with smooth successors from a Mangoldt-weighted sum.
The smooth shifted-prime supply is proved in Yao Xu's equal-divisor-sums-lean4
at 6280393739de (Apache-2.0). This alternative extraction uses the global
proper-prime-power error in the Chebyshev functions. -/
-- Credit: @marcusbuffett

open ArithmeticFunction Filter Finset

namespace OMA.R_Erdos824_erdos_824_variants_squarefree_R1_H1_R1

def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ e : ℝ, 0 < e → ∀ᶠ y : ℝ in atTop,
    y ^ (1 - e) ≤ ∑ n ∈ (Iic ⌊5*y⌋₊).filter
      (fun n => ∀ q : ℕ, q ∈ (n+1).primeFactors → (q : ℝ) ≤ y^δ), vonMangoldt n

def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ e : ℝ, 0 < e ∧ ∀ᶠ y : ℝ in atTop,
    Chebyshev.psi (5*y) - Chebyshev.theta (5*y) + y^(1-η) * Real.log (5*y) < y^(1-e)

private lemma restricted_mangoldt {z : ℝ} (hz : 1 ≤ z) (S : Finset ℕ) (hS : S ⊆ Iic ⌊z⌋₊) :
    ∑ n ∈ S, vonMangoldt n ≤
      Chebyshev.psi z - Chebyshev.theta z + ((S.filter Nat.Prime).card : ℝ) * Real.log z := by
  classical
  let U : Finset ℕ := Icc 0 ⌊z⌋₊
  have hSU : S ⊆ U := fun n hn => mem_Icc.mpr ⟨Nat.zero_le _, mem_Iic.mp (hS hn)⟩
  have htotal (T : Finset ℕ) := T.sum_filter_add_sum_filter_not Nat.Prime (fun n => vonMangoldt n)
  have hp : (∑ n ∈ U.filter Nat.Prime, vonMangoldt n) = Chebyshev.theta z := by
    rw [Chebyshev.theta_eq_sum_Icc]
    exact sum_congr rfl fun n hn => vonMangoldt_apply_prime (mem_filter.mp hn).2
  have hu : ∑ n ∈ U, vonMangoldt n = Chebyshev.psi z := (Chebyshev.psi_eq_sum_Icc z).symm
  have hb := sum_le_sum_of_subset_of_nonneg (filter_subset_filter (fun n : ℕ => ¬ n.Prime) hSU)
    (fun n _ _ => vonMangoldt_nonneg (n := n))
  have hg : (∑ n ∈ S.filter Nat.Prime, vonMangoldt n) ≤ ((S.filter Nat.Prime).card : ℝ) * Real.log z := by
    rw [← nsmul_eq_mul]
    apply sum_le_card_nsmul
    intro n hn
    obtain ⟨hnS, hnprime⟩ := mem_filter.mp hn
    rw [vonMangoldt_apply_prime hnprime]
    exact Real.log_le_log (by exact_mod_cast hnprime.pos)
      ((by exact_mod_cast mem_Iic.mp (hS hnS) : (n:ℝ) ≤ ⌊z⌋₊).trans (Nat.floor_le (by linarith)))
  linarith [htotal U, htotal S]

theorem main : H1 → H2 → OMA.R_Erdos824_erdos_824_variants_squarefree_R1.H1 := by
  intro hmass hrem δ hδ hδ' η hη
  obtain ⟨e, he, herr⟩ := hrem η hη
  apply eventually_atTop.mp
  filter_upwards [hmass δ hδ hδ' e he, herr, eventually_ge_atTop (1 : ℝ)] with y hm hr hy
  let S := (Iic ⌊5*y⌋₊).filter (fun n => ∀ q : ℕ, q ∈ (n+1).primeFactors → (q : ℝ) ≤ y^δ)
  have h := restricted_mangoldt (z := 5*y) (by linarith) S (filter_subset _ _)
  have heq : S.filter Nat.Prime = (Iic ⌊5*y⌋₊).filter
      (fun p => p.Prime ∧ ∀ q : ℕ, q ∈ (p+1).primeFactors → (q : ℝ) ≤ y^δ) := by
    ext p
    simp [S, and_assoc, and_left_comm, and_comm]
  rw [heq] at h
  change y^(1-e) ≤ ∑ n ∈ S, vonMangoldt n at hm
  have hlog : 0 < Real.log (5*y) := Real.log_pos (by linarith)
  apply le_of_lt
  apply (mul_lt_mul_iff_left₀ hlog).mp
  linarith

end OMA.R_Erdos824_erdos_824_variants_squarefree_R1_H1_R1
