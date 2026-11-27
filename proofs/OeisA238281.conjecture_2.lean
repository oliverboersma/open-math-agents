import FormalConjectures.OEIS.«238281»

/-!
For n = 14 the adjacent blocks have equal prime counts only at k = 4 and k = 12.
The corresponding values of 2k + 1 are 9 and 25.

The witness 14 was previously recorded by OEIS Open in its A238281 results.
Formalization for this target: @rleshner.
-/

set_option maxRecDepth 4096 in
theorem OMA.disproof : ¬ (type_of% @OeisA238281.conjecture_2) := by
  intro all_lengths
  obtain ⟨k, hk, hlt, hprime, hequal⟩ := all_lengths 14 (by decide) (by decide)
  have ties : ∀ i : Fin 14, 0 < i.val →
      Nat.primeCounting (i.val * 14) - Nat.primeCounting ((i.val - 1) * 14) =
      Nat.primeCounting ((i.val + 1) * 14) - Nat.primeCounting (i.val * 14) →
      i.val = 4 ∨ i.val = 12 := by decide
  rcases ties ⟨k, hlt⟩ hk hequal with h | h
  · change k = 4 at h
    subst k
    exact (by decide : ¬ Nat.Prime 9) hprime
  · change k = 12 at h
    subst k
    exact (by decide : ¬ Nat.Prime 25) hprime
