import OMAReductions.R_Erdos10_erdos_10_variants_gallagher_R1
import Mathlib

/-! Separate Gallagher's averaged correlation of two distinct prime shifts from
the diagonal contribution. Distinct sets of binary exponents give distinct
shift sums. A family of more than a logarithmic square in size absorbs the
diagonal even using the trivial pointwise bound for the prime weight. -/
open Finset Filter Real
open scoped Classical
namespace OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1

/-- Gallagher's off-diagonal prime-pair estimate averaged over binary shifts.
Here Q may be taken to be distinct k-element sums on a short logarithmic
interval of exponents. The inner correlation only uses the nonzero gap. -/
def H1 : Prop :=
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ Q : Finset (Multiset ℕ), Q.Nonempty ∧
    (∀ t ∈ Q, t.card ≤ k ∧ (s t:ℝ) ≤ ε*N) ∧ Set.InjOn s (Q:Set (Multiset ℕ)) ∧
    log (2*(N:ℝ)+1)^2 ≤ ε*Q.card ∧
    (∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j*v (j+Nat.dist (s t) (s u))) ≤
      (1+ε)*N*(Q.card:ℝ)^2

/-- General finite translation inequality: the diagonal costs at most NM²
per shift, and each off-diagonal term is bounded by the pair correlation
at the absolute difference of its two shifts. -/
def H2 : Prop := ∀ (v : ℕ → ℝ) (s : Multiset ℕ → ℕ) (N : ℕ) (Q : Finset (Multiset ℕ))
    (M : ℝ), (∀ j, 0 ≤ v j) → 0 ≤ M → (∀ j < N, v j ≤ M) →
    (∑ j ∈ range N, (∑ t ∈ Q, if s t ≤ j then v (j-s t) else 0)^2) ≤
      N*Q.card*M^2 + ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j*v (j+Nat.dist (s t) (s u))

theorem main : H1 → H2 → OMA.R_Erdos10_erdos_10_variants_gallagher_R1.H2 := by
  intro pairs translate δ d0
  let ε := δ/2
  have e0 : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨k,samples⟩ := pairs ε e0
  refine ⟨k,?_⟩
  filter_upwards [samples] with N H
  obtain ⟨Q,Qp,support,_,diag,off⟩ := H
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  let v (j : ℕ) := if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let M := log (2*(N:ℝ)+1)
  have M0 : 0 ≤ M := Real.log_nonneg (by linarith [Nat.cast_nonneg N (α:=ℝ)])
  have v0 (j : ℕ) : 0 ≤ v j := by dsimp [v]; split <;> positivity
  have vmax (j : ℕ) (hj : j < N) : v j ≤ M := by
    dsimp [v]; split
    · have nj : (j:ℝ) ≤ N := by exact_mod_cast hj.le
      have le : log (2*j+1:ℕ) ≤ M := by
        dsimp only [M]
        apply Real.log_le_log (by positivity)
        push_cast
        linarith
      linarith
    · exact M0
  have h := translate v s N Q M v0 M0 vmax
  have qp : (0:ℝ) < Q.card := by exact_mod_cast Qp.card_pos
  refine ⟨Q,fun _ => (Q.card:ℝ)⁻¹,?_,?_,?_⟩
  · intro t ht
    obtain ⟨tk,ts⟩ := support t ht
    refine ⟨by positivity,tk,ts.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    dsimp [ε]; linarith
  · simp [qp.ne']
  change (∑ j ∈ range N,(∑ t ∈ Q,(Q.card:ℝ)⁻¹*(if s t ≤ j then v (j-s t) else 0))^2) ≤ _
  simp_rw [←mul_sum,mul_pow]
  rw [←mul_sum,inv_pow,←div_eq_inv_mul,div_le_iff₀ (sq_pos_of_pos qp)]
  apply h.trans
  change M^2 ≤ ε*(Q.card:ℝ) at diag
  have d := mul_le_mul_of_nonneg_left diag (show 0 ≤ (N:ℝ)*Q.card by positivity)
  dsimp only [s,v] at h ⊢
  dsimp [ε] at off d
  linarith only [off,d]

end OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1
