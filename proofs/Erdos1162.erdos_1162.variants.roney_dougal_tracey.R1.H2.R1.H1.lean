import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1
import Mathlib

-- Step Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2.R1.H1: hypothesis H1 of reduction Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2.R1
-- Credit: @ivillar

/-!
# From conjugacy representatives to all subgroups of the symmetric group

If every subgroup of `Equiv.Perm (Fin n)` is a conjugate of a member of `R`, then
`(K, g) ↦ g K g⁻¹` maps `R × Equiv.Perm (Fin n)` onto the set of subgroups, so there are at most
`R.card * n !` subgroups.
-/

namespace Erdos1162OrbitStep

theorem orbit : ∀ n : ℕ, ∀ R : Finset (Subgroup (Equiv.Perm (Fin n))),
    (∀ H : Subgroup (Equiv.Perm (Fin n)), ∃ K ∈ R, ∃ g : Equiv.Perm (Fin n),
      K.map (MulAut.conj g).toMonoidHom = H) →
    Erdos1162.f n ≤ R.card * n.factorial := by
  intro n R hR
  unfold Erdos1162.f
  have hsurj : Function.Surjective (fun x : R × Equiv.Perm (Fin n) =>
      (x.1 : Subgroup (Equiv.Perm (Fin n))).map (MulAut.conj x.2).toMonoidHom) := by
    intro H
    obtain ⟨K, hK, g, hg⟩ := hR H
    exact ⟨(⟨K, hK⟩, g), hg⟩
  calc Nat.card (Subgroup (Equiv.Perm (Fin n)))
      ≤ Nat.card (R × Equiv.Perm (Fin n)) := Nat.card_le_card_of_surjective _ hsurj
    _ = R.card * n.factorial := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe,
          Fintype.card_perm, Fintype.card_fin]

end Erdos1162OrbitStep

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1.H1 :=
  Erdos1162OrbitStep.orbit
