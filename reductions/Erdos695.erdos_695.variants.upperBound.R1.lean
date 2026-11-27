import FormalConjectures.ErdosProblems.«695»
import Mathlib.Topology.Compactness.Compact

/-!
Fixed upper bounds make the choices at each coordinate finite. Hence
arbitrarily long bounded prefixes suffice, even if produced independently.
-/

namespace OMA.R_Erdos695_erdos_695_variants_upperBound_R1

open Filter Real

def H1 : Prop :=
  ∀ cap : ℕ → ℕ,
    (∀ N, ∃ q : ℕ → ℕ, (∀ k ≤ N, (q k).Prime ∧ q k ≤ cap k) ∧
      ∀ k < N, q k < q (k + 1) ∧ q (k + 1) % q k = 1) →
    ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ k, (q k).Prime) ∧
      (∀ k, q (k + 1) % q k = 1) ∧ ∀ k, q k ≤ cap k

def H2 : Prop :=
  ∃ o : ℕ → ℝ, (o =o[atTop] (1 : ℕ → ℝ)) ∧
    ∀ N, ∃ q : ℕ → ℕ,
      (∀ k ≤ N, (q k).Prime ∧ (q k : ℝ) ≤ exp ((k + 1) * log (k + 1) ^ (1 + o k))) ∧
      ∀ k < N, q k < q (k + 1) ∧ q (k + 1) % q k = 1

section Proof

theorem main : H1 → H2 → type_of% @Erdos695.erdos_695.variants.upperBound := by
  intro compactness finitePrefixes
  obtain ⟨o, ho, hfinite⟩ := finitePrefixes
  let B (k : ℕ) : ℝ := exp ((k + 1) * log (k + 1) ^ (1 + o k))
  let C (k : ℕ) := ⌊B k⌋₊
  have hB (k : ℕ) : 0 ≤ B k := (Real.exp_pos _).le
  have hPre N : ∃ q : ℕ → ℕ, (∀ k ≤ N, (q k).Prime ∧ q k ≤ C k) ∧
      ∀ k < N, q k < q (k + 1) ∧ q (k + 1) % q k = 1 := by
    obtain ⟨q, hq, hs⟩ := hfinite N
    refine ⟨q, ?_, hs⟩
    intro k hk
    exact ⟨(hq k hk).1, (Nat.le_floor_iff (hB k)).mpr (hq k hk).2⟩
  obtain ⟨q, hmono, hp, hs, hcap⟩ := compactness C hPre
  refine ⟨q, hmono, hp, hs, o, ho, fun k => ?_⟩
  exact (show (q k : ℝ) ≤ (C k : ℝ) from by exact_mod_cast hcap k).trans (Nat.floor_le (hB k))

end Proof

end OMA.R_Erdos695_erdos_695_variants_upperBound_R1
