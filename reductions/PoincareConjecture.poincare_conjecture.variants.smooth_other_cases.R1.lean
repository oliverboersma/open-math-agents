import FormalConjectures.Millennium.Poincare

/-! Reduce the smooth Poincaré variant to four dimension ranges. -/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1

open PoincareConjecture OpenPartialHomeomorph
open scoped Manifold ContDiff EuclideanGeometry ContinuousMap

universe u

-- H1 is covered by Wang and Xu, Corollary 1.13. H3 isolates dimension 176.
-- The smooth atlas is transported along ULift.down in smoothConjecture_lower.
def H1 : Prop :=
  ∀ n : ℕ, n > 4 → n ∉ SmoothTrueValues → n % 2 = 1 → ¬ SmoothConjectureFor.{0} n

def H2 : Prop :=
  ∀ n : ℕ, n > 4 → n ∉ SmoothTrueValues → n % 2 = 0 →
    n ≤ 200 → n ≠ 176 → ¬ SmoothConjectureFor.{0} n

def H3 : Prop :=
  ¬ SmoothConjectureFor.{0} 176

def H4 : Prop :=
  ∀ n : ℕ, n > 200 → n % 2 = 0 → ¬ SmoothConjectureFor.{0} n

lemma smoothConjecture_lower (n : ℕ) (h : SmoothConjectureFor.{u} n) :
    SmoothConjectureFor.{0} n := by
  intro M _ _ _ _ equiv
  let e : ULift.{u} M ≃ₜ M := Homeomorph.ulift
  let H := EuclideanSpace ℝ (Fin n)
  let _ : ChartedSpace H (ULift.{u} M) :=
    { atlas := e.transOpenPartialHomeomorph '' atlas H M
      chartAt x := e.transOpenPartialHomeomorph (chartAt H (e x))
      mem_chart_source x := mem_chart_source H (e x)
      chart_mem_atlas x := ⟨_, chart_mem_atlas H (e x), rfl⟩ }
  have : IsManifold (𝓡 n) ∞ (ULift.{u} M) := by
    refine { compatible := ?_ }
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    simp only [Homeomorph.transOpenPartialHomeomorph_eq_trans, trans_symm_eq_symm_trans_symm,
      trans_assoc, ← Homeomorph.symm_toOpenPartialHomeomorph]
    rw [← trans_assoc e.symm.toOpenPartialHomeomorph e.toOpenPartialHomeomorph b,
      ← Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.symm_trans_self,
      Homeomorph.refl_toOpenPartialHomeomorph, refl_trans]
    exact (contDiffGroupoid ∞ (𝓡 n)).compatible ha hb
  have hdown : ContMDiff (𝓡 n) (𝓡 n) ∞ e := by
    intro x
    let a := chartAt H (e x)
    let b := chartAt H x
    have hb : b = e.transOpenPartialHomeomorph a := rfl
    have hcomp : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (a.symm ∘ b) b.source := by
      apply contMDiffOn_chart_symm.comp contMDiffOn_chart
      change Set.MapsTo b b.source a.target
      rw [hb]
      exact (e.transOpenPartialHomeomorph a).mapsTo
    apply (hcomp.congr ?_).contMDiffAt (b.open_source.mem_nhds (mem_chart_source H x))
    intro y hy
    rw [hb] at hy ⊢
    exact (a.left_inv hy).symm
  have hup : ContMDiff (𝓡 n) (𝓡 n) ∞ e.symm := by
    intro x
    let a := chartAt H x
    let b := chartAt H (e.symm x)
    have hb : b = e.transOpenPartialHomeomorph a := by
      change e.transOpenPartialHomeomorph (chartAt H (e (e.symm x))) = _
      rw [e.apply_symm_apply]
    have hcomp : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (b.symm ∘ a) a.source := by
      apply contMDiffOn_chart_symm.comp contMDiffOn_chart
      change Set.MapsTo a a.source b.target
      rw [hb]
      exact a.mapsTo
    apply (hcomp.congr ?_).contMDiffAt (a.open_source.mem_nhds (mem_chart_source H x))
    intro y hy
    rw [hb]
    change e.symm y = e.symm (a.symm (a y))
    rw [a.left_inv hy]
  let lift : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ ULift.{u} M := ⟨e.symm.toEquiv, hup, hdown⟩
  obtain ⟨d⟩ := h (ULift.{u} M) (e.toHomotopyEquiv.trans equiv)
  exact ⟨lift.trans d⟩

theorem main : H1 → H2 → H3 → H4 →
    type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_other_cases := by
  intro h1 h2 h3 h4 n hn hexcluded h
  have hsmall := smoothConjecture_lower n h
  by_cases hodd : n % 2 = 1
  · exact h1 n hn hexcluded hodd hsmall
  have heven : n % 2 = 0 := by omega
  by_cases h176 : n = 176
  · subst n
    exact h3 hsmall
  by_cases hlow : n ≤ 200
  · exact h2 n hn hexcluded heven hlow h176 hsmall
  · exact h4 n (Nat.lt_of_not_ge hlow) heven hsmall

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_other_cases_R1
