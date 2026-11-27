import FormalConjectures.ErdosProblems.«313»

/-!
Reduce Erdős 313 to finding prime sets of unbounded size with a local cofactor
congruence at each prime and reciprocal sum below one. The congruences give
divisibility by the whole squarefree product, and the sum bound selects
the first positive multiple.
-/

open Finset

namespace OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1

def H1 : Prop :=
  ∀ P : Finset ℕ, P.Nonempty → (∀ p ∈ P, p.Prime) →
    (∀ p ∈ P, p ∣ (∏ q ∈ P.erase p, q) + 1) →
    (∑ p ∈ P, (1 : ℚ) / p) < 1 →
    (∏ p ∈ P, p) = 1 + ∑ p ∈ P, ∏ q ∈ P.erase p, q

def H2 : Prop :=
  ∀ k : ℕ, ∃ P : Finset ℕ, k ≤ P.card ∧ P.Nonempty ∧
    (∀ p ∈ P, p.Prime) ∧
    (∀ p ∈ P, p ∣ (∏ q ∈ P.erase p, q) + 1) ∧
    (∑ p ∈ P, (1 : ℚ) / p) < 1

section Proof

private theorem cofactor_sum_eq (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, (1 : ℚ) / p) * (∏ p ∈ P, (p : ℚ)) =
      ∑ p ∈ P, (∏ q ∈ P.erase p, (q : ℚ)) := by
  rw [sum_mul]
  apply sum_congr rfl
  intro p hmem
  have hn : (p : ℚ) ≠ 0 := by exact_mod_cast (hp p hmem).ne_zero
  rw [← prod_erase_mul P (fun q : ℕ => (q : ℚ)) hmem]
  field_simp

private theorem solution_of_cofactor_sum {P : Finset ℕ} (hne : P.Nonempty)
    (hp : ∀ p ∈ P, p.Prime)
    (he : (∏ p ∈ P, p) = 1 + ∑ p ∈ P, ∏ q ∈ P.erase p, q) :
    (∏ p ∈ P, p, P) ∈ Erdos313.erdos313Solutions := by
  let D := ∏ p ∈ P, p
  have hD : 0 < D := Finset.prod_pos fun p hm => (hp p hm).pos
  obtain ⟨p, hm⟩ := hne
  have hpD : p ≤ D := Nat.le_of_dvd hD (Finset.dvd_prod_of_mem id hm)
  refine ⟨(hp p hm).two_le.trans hpD, ⟨p, hm⟩, hp, ?_⟩
  change (∑ p ∈ P, (1 : ℚ) / p) = 1 - 1 / (D : ℚ)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  apply (mul_left_inj' hDq).mp
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hDq]
  have hsum := cofactor_sum_eq P hp
  rw [← Nat.cast_prod] at hsum
  rw [hsum]
  have heq : (D : ℚ) = 1 + ∑ p ∈ P, ∏ q ∈ P.erase p, (q : ℚ) := by
    have hc := congrArg (fun a : ℕ => (a : ℚ)) he
    simpa only [D, Nat.cast_add, Nat.cast_one, Nat.cast_sum, Nat.cast_prod] using hc
  linarith

theorem main : H1 → H2 →
    type_of% @Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite := by
  intro hInt hSets hfinite
  let T := hfinite.toFinset
  let K := T.sup fun n : ℕ => n.primeFactors.card
  obtain ⟨P, hcard, hne, hp, hcong, hsum⟩ := hSets (K + 1)
  let n := ∏ p ∈ P, p
  have hs : Erdos313.IsPrimaryPseudoperfect n :=
    ⟨P, solution_of_cofactor_sum hne hp (hInt P hne hp hcong hsum)⟩
  have hnT : n ∈ T := hfinite.mem_toFinset.mpr hs
  have hnK : n.primeFactors.card ≤ K := Finset.le_sup (f := fun x : ℕ => x.primeFactors.card) hnT
  rw [show n.primeFactors = P from Nat.primeFactors_prod hp] at hnK
  omega

end Proof

end OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1
