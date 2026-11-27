import Mathlib

/-!
# Distance of vectors versus distance of their difference vectors

Source: https://mathoverflow.net/questions/267876
Credit: @zarnab222-dev

For two centered real vectors forming an angle of at most π/2, is their
Euclidean distance at most the Euclidean distance between their vectors of
absolute pairwise differences? Both distances are squared below. Each
unordered pair occurs once, with the smaller coordinate index first. The
inner product condition includes zero vectors, for which the inequality also
makes sense.
-/

namespace OMA.S_mo_267876

theorem main : ∀ (n : ℕ) (f g : Fin n → ℝ),
    (∑ i, f i) = 0 → (∑ i, g i) = 0 → 0 ≤ ∑ i, f i * g i →
    (∑ i, (f i - g i) ^ 2) ≤
      ∑ e ∈ (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)),
        (|f e.1 - f e.2| - |g e.1 - g e.2|) ^ 2 := by
  sorry

end OMA.S_mo_267876
