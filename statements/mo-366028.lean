import Mathlib

/-!
# Nine horses on a circular track that only pass at the start

Source: https://mathoverflow.net/questions/366028

Nine horses start together at one point of a circular track and run forever,
each at its own constant speed, all speeds different. They may pass each other
only at the common starting point; anywhere else they would collide. Can the
speeds be chosen so that no collision ever happens?

The track has length one, so at time `t` horse `i` is at position `v i * t`
modulo one, and the starting point is the class of zero. Two horses are at the
same point exactly when the difference of their positions is an integer. The
statement says that the speeds can be chosen (positive and pairwise distinct)
so that whenever two distinct horses meet, they meet at the starting point.
-/

namespace OMA.S_mo_366028

theorem main :
    ∃ v : Fin 9 → ℝ, Function.Injective v ∧ (∀ i, 0 < v i) ∧
      ∀ i j, i ≠ j → ∀ t : ℝ, 0 ≤ t →
        (∃ k : ℤ, v i * t - v j * t = k) → ∃ m : ℤ, v i * t = m := by
  sorry

end OMA.S_mo_366028
