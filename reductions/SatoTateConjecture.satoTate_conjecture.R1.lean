import FormalConjectures.Wikipedia.SatoTateConjecture
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_SatoTateConjecture_satoTate_conjecture_R1
open Real Filter SatoTateConjecture
open scoped Classical

/-- Equidistribution of Frobenius angles for a non-CM elliptic curve. -/
def H1 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ¬ HasCM E →
    ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ π →
    Tendsto (fun N : ℕ =>
      ((((Nat.primesBelow N).filter fun p =>
        ∃ θ ∈ Set.Icc u v, normalisedAp E p = cos θ).card : ℝ) /
        ((Nat.primesBelow N).card : ℝ))) atTop
      (nhds (2 / π * ∫ θ in u..v, sin θ ^ 2))

/-- Pushforward of the angular Sato–Tate density by cosine. -/
def H2 : Prop :=
  ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 1 →
    2 / π * (∫ θ in arccos b..arccos a, sin θ ^ 2) = satoTateMeasure a b

theorem main : H1 → H2 → type_of% @SatoTateConjecture.satoTate_conjecture := by
  intro angles mass E _ hCM a b ha hab hb
  have h := angles E hCM _ _ (arccos_nonneg b) (arccos_le_arccos hab) (arccos_le_pi a)
  rw [mass a b ha hab hb] at h
  apply h.congr
  intro N
  unfold primeCountInInterval
  congr 3
  ext p
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨θ, ⟨h₁,h₂⟩, he⟩
    rw [he]
    have l := cos_le_cos_of_nonneg_of_le_pi (le_trans (arccos_nonneg b) h₁) (arccos_le_pi a) h₂
    have r := cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg b) (h₂.trans (arccos_le_pi a)) h₁
    simpa [cos_arccos ha (hab.trans hb), cos_arccos (ha.trans hab) hb] using And.intro l r
  · rintro ⟨hl,hr⟩
    exact ⟨_, ⟨arccos_le_arccos hr, arccos_le_arccos hl⟩, (cos_arccos (ha.trans hl) (hr.trans hb)).symm⟩

end OMA.R_SatoTateConjecture_satoTate_conjecture_R1
