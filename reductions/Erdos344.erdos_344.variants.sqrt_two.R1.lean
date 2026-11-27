import FormalConjectures.ErdosProblems.«344»

/-!
Replace the real-valued counting condition by a quadratic bound on the
increasing enumeration. Finite subset-sum progressions of arbitrary length
with bounded starts and differences imply an infinite progression.
-/

open Filter Finset

namespace OMA.R_Erdos344_erdos_344_variants_sqrt_two_R1

def H1 : Prop :=
  ∀ A : Set ℕ, (∀ᶠ N : ℕ in atTop, Real.sqrt (2 * N) ≤ A.countUpTo N) →
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, a n ∈ A ∧ 0 < a n) ∧
      (∀ᶠ n : ℕ in atTop, 2 * a n ≤ n ^ 2 + 2)

def H2 : Prop :=
  ∀ a : ℕ → ℕ, StrictMono a → (∀ n, 0 < a n) →
    (∀ᶠ n : ℕ in atTop, 2 * a n ≤ n ^ 2 + 2) →
    ∃ C : ℕ, ∀ k : ℕ, ∃ M b d : ℕ, b ≤ C ∧ 0 < d ∧ d ≤ C ∧
      (∀ j ≤ k, b + j * d ∈ subsetSums (a '' Set.Iio M))

section Proof

theorem main : H1 → H2 → type_of% @Erdos344.erdos_344.variants.sqrt_two := by
  intro hEnum hFin A hA
  obtain ⟨a, ha, haA, hquad⟩ := hEnum A hA
  obtain ⟨C, hAP⟩ := hFin a ha (fun n => (haA n).2) hquad
  by_contra hSub
  have hbad (b d : ℕ) : ∃ j, d = 0 ∨ b + j * d ∉ subsetSums A := by
    by_cases hd : d = 0
    · exact ⟨0, Or.inl hd⟩
    · by_contra! h
      exact hSub ⟨b, d, Nat.pos_of_ne_zero hd, fun j => (h j).2⟩
  choose j hj using hbad
  let P := (Finset.range (C + 1)) ×ˢ (Finset.Icc 1 C)
  let K := P.sup (fun v : ℕ × ℕ => j v.1 v.2)
  obtain ⟨M, b, d, hb, hd, hdC, hproof⟩ := hAP K
  have hP : (b, d) ∈ P := Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨hd, hdC⟩⟩
  have hK : j b d ≤ K := Finset.le_sup (f := fun v : ℕ × ℕ => j v.1 v.2) hP
  have hin : a '' Set.Iio M ⊆ A := by
    rintro _ ⟨i, _, rfl⟩
    exact (haA i).1
  exact ((hj b d).resolve_left (Nat.ne_of_gt hd)) (subsetSums_mono hin (hproof (j b d) hK))

end Proof

end OMA.R_Erdos344_erdos_344_variants_sqrt_two_R1
