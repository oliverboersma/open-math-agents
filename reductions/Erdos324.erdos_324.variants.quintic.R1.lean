import FormalConjectures.ErdosProblems.«324»
import Mathlib.FieldTheory.Finite.Basic

/-! A gap factorization for equal sums of two fifth powers. -/

-- Credit: @dhudakk
namespace OMA.R_Erdos324_erdos_324_variants_quintic_R1

-- For square gap product, the factorization in gap_obstruction bounds both
-- bases for each fixed gap pair. Only the bounded case remains.
def H1 : Prop :=
  ∀ h k m x y : ℤ, 0 < k → k < h → (h : ZMod 5) = k → 0 ≤ x → x+h < y → m ^ 2 = h * k →
    5 * ((x+h)^2 + x^2) ≤ h^5 - k^5 →
    (x+h)^5 - x^5 ≠ (y+k)^5 - y^5

-- For nonsquare gap product this is a generalized Pell equation in U,V.
-- The two square constraints enforce the centered gap shapes.
def H2 : Prop :=
  ∀ h k U V : ℤ, 0 < k → k < h → (h : ZMod 5) = k → (¬ ∃ m : ℤ, m^2 = h*k) →
    (∃ x y : ℤ, 0 ≤ x ∧ x+h < y ∧ U = (x+h)^2 + x^2 ∧ V = (y+k)^2 + y^2) →
    5*h*U^2 - 5*k*V^2 ≠ h^5 - k^5

lemma gap_obstruction (hs : H1) (hn : H2) (x y h k : ℤ)
    (hx : 0 ≤ x) (hxy : x+h < y) (hk : 0 < k) (hlt : k < h)
    (e : (x+h)^5 - x^5 = (y+k)^5 - y^5) : False := by
  let U := (x+h)^2 + x^2
  let V := (y+k)^2 + y^2
  have E : 5*h*U^2 - 5*k*V^2 = h^5-k^5 := by
    dsimp [U,V]
    linear_combination 4 * e
  have congr : (h : ZMod 5) = k := by
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have em := congrArg (fun z : ℤ => (z : ZMod 5)) e
    push_cast at em
    simpa only [ZMod.pow_card, add_sub_cancel_left] using em
  by_cases sq : ∃ m : ℤ, m^2 = h*k
  · obtain ⟨r,hr⟩ := sq
    let m := |r|
    have hm : m^2 = h*k := by simpa [m, sq_abs] using hr
    have hpos : 0 < h := by omega
    have vp : 0 ≤ V := by dsimp [V]; positivity
    have up : 0 ≤ U := by dsimp [U]; positivity
    have mv : 0 ≤ m*V := mul_nonneg (abs_nonneg _) vp
    have D : 5 * (h*U-m*V) * (h*U+m*V) = h*(h^5-k^5) := by
      linear_combination h * E - 5 * V^2 * hm
    have dif : 0 < h^5-k^5 := sub_pos.mpr (by gcongr)
    have pos : 0 < 5 * (h*U-m*V) * (h*U+m*V) := D.symm ▸ mul_pos hpos dif
    have sum0 : 0 ≤ h*U+m*V := by positivity
    have gap : 1 ≤ h*U-m*V := by
      by_contra! bad
      have := mul_nonpos_of_nonpos_of_nonneg (show 5*(h*U-m*V) ≤ 0 by omega) sum0
      omega
    have B : h * (5*U) ≤ h * (h^5-k^5) := by
      rw [← D]
      nlinarith [mul_nonneg (show 0 ≤ h*U-m*V-1 by omega) sum0]
    exact hs h k m x y hk hlt congr hx hxy hm ((mul_le_mul_iff_right₀ hpos).mp B) e
  · exact hn h k U V hk hlt congr sq ⟨x,y,hx,hxy,rfl,rfl⟩ E

lemma ordered (hs : H1) (hn : H2) (a b c d : ℕ)
    (hac : a < c) (hcd : c < d) (e : a^5+b^5 = c^5+d^5) : False := by
  have hdb : d < b := by
    by_contra! le
    have : a^5+b^5 < c^5+d^5 := add_lt_add_of_lt_of_le (by gcongr) (by gcongr)
    omega
  have E : (a:ℤ)^5 + (b:ℤ)^5 = (c:ℤ)^5 + (d:ℤ)^5 := by exact_mod_cast e
  let h : ℤ := (c:ℤ)-a
  let k : ℤ := (b:ℤ)-d
  have H : 0 < h := by dsimp [h]; omega
  have K : 0 < k := by dsimp [k]; omega
  have G : ((a:ℤ)+h)^5-(a:ℤ)^5 = ((d:ℤ)+k)^5-(d:ℤ)^5 := by
    dsimp [h,k]
    linear_combination -E
  have ad : (a:ℤ) < d := by exact_mod_cast hac.trans hcd
  have kh : k < h := by
    by_contra! le
    have bigger : ((a:ℤ)+h)^5-(a:ℤ)^5 < ((d:ℤ)+k)^5-(d:ℤ)^5 := by
      calc
        _ = (5*(a:ℤ)^4*h + 10*(a:ℤ)^3*h^2 + 10*(a:ℤ)^2*h^3 + h^5) + 5*h^4*a := by ring
        _ < (5*(d:ℤ)^4*k + 10*(d:ℤ)^3*k^2 + 10*(d:ℤ)^2*k^3 + k^5) + 5*k^4*d := by
          apply add_lt_add_of_le_of_lt
          · gcongr
          · calc
              _ < 5*h^4*d := mul_lt_mul_of_pos_left ad (by positivity)
              _ ≤ _ := by gcongr
        _ = _ := by ring
    omega
  exact gap_obstruction hs hn _ _ _ _ (by positivity) (by dsimp [h]; omega) K kh G

theorem main : H1 → H2 → type_of% @Erdos324.erdos_324.variants.quintic := by
  intro hs hn ⟨a,b⟩ hab ⟨c,d⟩ hcd e
  change a < b at hab
  change c < d at hcd
  change a^5+b^5 = c^5+d^5 at e
  rcases lt_trichotomy a c with lt | eq | gt
  · exact (ordered hs hn a b c d lt hcd e).elim
  · subst c
    have p : b^5 = d^5 := by omega
    have : b = d := by
      rcases lt_trichotomy b d with l | l | l
      · have : b^5 < d^5 := by gcongr
        omega
      · exact l
      · have : d^5 < b^5 := by gcongr
        omega
    simp [this]
  · exact (ordered hs hn c d a b gt hab e.symm).elim

end OMA.R_Erdos324_erdos_324_variants_quintic_R1
