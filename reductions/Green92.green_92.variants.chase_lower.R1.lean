import FormalConjectures.GreensOpenProblems.«92»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green92_green_92_variants_chase_lower_R1
open Filter Finset Green92
open scoped Classical

/-- Chase's binary testing lower bound for two competing source strings. -/
def H1 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, n % 4 = 3 →
    ∃ x y : Fin n → Bool, x ≠ y ∧
      ∀ (m : ℕ) (D : (Fin m → List Bool) → Prop),
      (9/10 : ℝ) ≤ ((univ.filter fun S : Fin m → Finset (Fin n) =>
        D (fun j => Green92.trace x (S j))).card : ℝ) / Fintype.card (Fin m → Finset (Fin n)) →
      (9/10 : ℝ) ≤ ((univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D (fun j => Green92.trace y (S j))).card : ℝ) / Fintype.card (Fin m → Finset (Fin n)) →
      c * (n : ℝ)^(3/2 : ℝ) / Real.log n ^ 7 ≤ m

/-- A finite number of independent traces suffices, since a trace can retain every bit. -/
def H2 : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∃ R : (Fin m → List Bool) → Fin n → Bool,
    ∀ x, (9/10 : ℝ) ≤ successProb R x

theorem main : H1 → H2 → type_of% @Green92.green_92.variants.chase_lower := by
  rintro ⟨c,hc,ht⟩ feasible
  refine ⟨c,hc,?_⟩
  filter_upwards [ht] with n hn hr
  obtain ⟨x,y,hxy,h⟩ := hn hr
  obtain ⟨R,hR⟩ : ∃ R : (Fin (numTraces n) → List Bool) → Fin n → Bool,
      ∀ x, (9/10 : ℝ) ≤ successProb R x := Nat.sInf_mem (feasible n)
  apply h _ (fun obs => R obs = x)
  · convert hR x using 1 <;> unfold successProb <;> congr 3 <;> ext s <;> simp
  refine (hR y).trans (div_le_div_of_nonneg_right ?_ (by positivity))
  apply Nat.cast_le.mpr
  apply card_le_card
  intro s hs
  simp only [mem_filter,mem_univ,true_and] at hs ⊢
  exact fun hx => hxy (hx.symm.trans hs)

end OMA.R_Green92_green_92_variants_chase_lower_R1
