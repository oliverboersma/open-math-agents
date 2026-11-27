import FormalConjectures.ErdosProblems.«174»
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
Frankl and Rödl's simplex theorem. The finite-colouring argument for orbits
of power-of-two permutations is from Kříž, in the form checked in Salofe's
open-math-agents trapezoid formalization, pull request 4258.
-/

namespace OMA.Helpers

section Framework

variable {X : Type} (D : X → X → ℝ)

/-- `Φ` multiplies the (squared) distance `D` by `d`, summed over the coordinates. -/
def Dil (d : ℝ) {ι : Type} [Fintype ι] (Φ : X → ι → X) : Prop :=
  ∀ x x', ∑ i, D (Φ x i) (Φ x' i) = d * D x x'

/-- Every coordinate of `Φ` is constant or keeps every point in its `E`-class. -/
def Cls (E : X → X → Prop) {ι : Type} (Φ : X → ι → X) : Prop :=
  ∀ i, (∀ x x', Φ x i = Φ x' i) ∨ (∀ x, E (Φ x i) x)

/-- The Hales--Jewett type property with fixed dilation factor. -/
def Hyp (E R : X → X → Prop) (d : ℝ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∃ (ι : Type) (_ : Fintype ι), ∀ c : (ι → X) → κ,
    ∃ Φ : X → ι → X, Dil D d Φ ∧ Cls E Φ ∧ ∀ x x', R x x' → c (Φ x) = c (Φ x')

theorem Hyp.mono {E E' R R' : X → X → Prop} {d : ℝ} (h : Hyp D E R d)
    (hE : ∀ a b, E a b → E' a b) (hR : ∀ x x', R' x x' → R x x') : Hyp D E' R' d := by
  intro κ _
  obtain ⟨ι, _, hι⟩ := h κ
  refine ⟨ι, inferInstance, fun c => ?_⟩
  obtain ⟨Φ, h1, h2, h3⟩ := hι c
  refine ⟨Φ, h1, fun i => ?_, fun x x' hx => h3 x x' (hR x x' hx)⟩
  rcases h2 i with h | h
  · exact Or.inl h
  · exact Or.inr fun x => hE _ _ (h x)

theorem dil_comp {J : Type} [Fintype J] {β : J → Type} [∀ j, Fintype (β j)] {d' d : ℝ}
    {Φ' : X → J → X} {Φ : ∀ j, X → β j → X} (h' : Dil D d' Φ') (h : ∀ j, Dil D d (Φ j)) :
    Dil D (d' * d) (fun x (p : Σ j, β j) => Φ p.1 (Φ' x p.1) p.2) := by
  intro x x'
  rw [Fintype.sum_sigma]
  have : ∀ j, ∑ b, D (Φ j (Φ' x j) b) (Φ j (Φ' x' j) b) = d * D (Φ' x j) (Φ' x' j) :=
    fun j => h j _ _
  simp only [this, ← Finset.mul_sum, h' x x']
  ring

theorem cls_comp {J : Type} {β : J → Type} {E₁ E₂ E₃ : X → X → Prop}
    {Φ' : X → J → X} {Φ : ∀ j, X → β j → X} (h' : Cls E₁ Φ') (h : ∀ j, Cls E₂ (Φ j))
    (hE : ∀ a b c, E₂ a b → E₁ b c → E₃ a c) :
    Cls E₃ (fun x (p : Σ j, β j) => Φ p.1 (Φ' x p.1) p.2) := by
  rintro ⟨j, b⟩
  rcases h' j with h1 | h1
  · left
    intro x x'
    simp only
    rw [h1 x x']
  · rcases h j b with h2 | h2
    · left
      intro x x'
      exact h2 _ _
    · right
      intro x
      exact hE _ _ _ (h2 _) (h1 x)

/-- A family of types indexed by `Option α`. -/
def optFam {α : Type} (ι₀ : Type) (β : α → Type) : Option α → Type
  | none => ι₀
  | some a => β a

/-- Glue a dependent function on `Option α`. -/
def optGlue {α : Type} {ι₀ : Type} {β : α → Type} {Y : Type} (w : ι₀ → Y)
    (rest : ∀ a, β a → Y) : ∀ o, optFam ι₀ β o → Y
  | none => w
  | some a => rest a

/-- Glue a family of words indexed by `Option α`. -/
def optWord {α : Type} {ι₀ : Type} {β : α → Type} {Y : Type} (Φ₀ : Y → ι₀ → Y)
    (Φ : ∀ a, Y → β a → Y) : ∀ o, Y → optFam ι₀ β o → Y
  | none => Φ₀
  | some a => Φ a

/-- The `Fintype` structures of a glued family. -/
abbrev optFin {α : Type} {ι₀ : Type} {β : α → Type} (h₀ : Fintype ι₀) (h : ∀ a, Fintype (β a)) :
    ∀ o, Fintype (optFam ι₀ β o)
  | none => h₀
  | some a => h a

theorem prod_lemma [Finite X] {E R : X → X → Prop} {d : ℝ} (h : Hyp D E R d) (J : Type)
    [Finite J] : ∀ (κ : Type) [Finite κ], ∃ (β : J → Type) (_ : ∀ j, Fintype (β j)),
      ∀ c : (∀ j, β j → X) → κ, ∃ Φ : ∀ j, X → β j → X,
        (∀ j, Dil D d (Φ j)) ∧ (∀ j, Cls E (Φ j)) ∧
        ∀ x x' : J → X, (∀ j, R (x j) (x' j) ∨ x j = x' j) →
          c (fun j => Φ j (x j)) = c (fun j => Φ j (x' j)) := by
  induction J using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro κ _
    obtain ⟨β, hβ, H⟩ := ih κ
    refine ⟨fun j => β (e.symm j), fun j => hβ (e.symm j), fun c => ?_⟩
    obtain ⟨Φ, h1, h2, h3⟩ := H (fun f => c (fun j => f (e.symm j)))
    refine ⟨fun j => Φ (e.symm j), fun j => h1 _, fun j => h2 _, fun x x' hx => ?_⟩
    have := h3 (fun a => x (e a)) (fun a => x' (e a)) (fun a => hx (e a))
    simpa using this
  | h_empty =>
    intro κ _
    refine ⟨fun _ => PEmpty, fun _ => inferInstance, fun c => ⟨fun j => j.elim, fun j => j.elim,
      fun j => j.elim, fun x x' _ => ?_⟩⟩
    congr 1
    funext j
    exact j.elim
  | @h_option α _ ih =>
    intro κ _
    obtain ⟨β, hβ, H⟩ := ih (X → κ)
    obtain ⟨ι₀, hι₀, H₀⟩ := h ((∀ a, β a → X) → κ)
    refine ⟨optFam ι₀ β, optFin hι₀ hβ, fun c => ?_⟩
    obtain ⟨Φ₀, a1, a2, a3⟩ := H₀ (fun w rest => c (optGlue w rest))
    obtain ⟨Φ, b1, b2, b3⟩ := H (fun rest x₀ => c (optGlue (Φ₀ x₀) rest))
    refine ⟨optWord Φ₀ Φ, fun o => ?_, fun o => ?_, fun x x' hx => ?_⟩
    · cases o with
      | none => exact a1
      | some a => exact b1 a
    · cases o with
      | none => exact a2
      | some a => exact b2 a
    · have e1 : ∀ z : Option α → X, (fun o => optWord Φ₀ Φ o (z o)) =
          optGlue (Φ₀ (z none)) (fun a => Φ a (z (some a))) := by
        intro z
        funext o
        cases o <;> rfl
      have s1 := congrFun (b3 (fun a => x (some a)) (fun a => x' (some a)) (fun a => hx (some a)))
        (x none)
      rw [e1 x, e1 x']
      refine Eq.trans s1 ?_
      rcases hx none with hR | heq
      · exact congrFun (a3 _ _ hR) _
      · rw [heq]

theorem hyp_two [Finite X] {E R₁ R₂ : X → X → Prop} {d₁ d₂ : ℝ}
    (htrans : ∀ a b c, E a b → E b c → E a c)
    (h₁ : Hyp D E R₁ d₁) (h₂ : Hyp D E R₂ d₂)
    (hR : ∀ x x', R₂ x x' → ∀ z z', E z x → E z' x' → R₂ z z') :
    Hyp D E (fun x x' => R₁ x x' ∨ R₂ x x') (d₁ * d₂) := by
  intro κ _
  obtain ⟨ι₁, _, hι₁⟩ := h₁ κ
  obtain ⟨β, _, hβ⟩ := prod_lemma D h₂ ι₁ κ
  refine ⟨Σ j, β j, inferInstance, fun c => ?_⟩
  obtain ⟨Φ, hΦd, hΦc, hΦ⟩ := hβ (fun f => c (fun p => f p.1 p.2))
  obtain ⟨Φ', hd', hc', hΦ'⟩ := hι₁ (fun x => c (fun p => Φ p.1 (x p.1) p.2))
  refine ⟨fun x p => Φ p.1 (Φ' x p.1) p.2, dil_comp D hd' hΦd,
    cls_comp hc' hΦc htrans, ?_⟩
  rintro x x' (h | h)
  · exact hΦ' x x' h
  · refine hΦ (Φ' x) (Φ' x') (fun j => ?_)
    rcases hc' j with hconst | hcl
    · exact Or.inr (hconst x x')
    · exact Or.inl (hR x x' h _ _ (hcl x) (hcl x'))

theorem hyp_merge [Finite X] {E R : X → X → Prop} {d : ℝ} (τ : X → X) (y₁ y₂ : X)
    (S₁ S₂ : X → Prop) (hD0 : ∀ x, D x x = 0) (hτ : ∀ x x', D (τ x) (τ x') = D x x')
    (h : Hyp D E R d)
    (hR1 : ∀ x x', S₁ x → S₁ x' → R x x') (hR2 : ∀ x x', S₂ x → S₂ x' → R x x')
    (hy1 : S₁ y₁) (hy2 : S₂ y₂) (hτ1 : ∀ x, S₁ x → S₂ (τ x)) (hτ2 : ∀ x, S₂ x → S₁ (τ x)) :
    Hyp D (fun a b => E a b ∨ E a (τ b))
      (fun x x' => (S₁ x ∨ S₂ x) ∧ (S₁ x' ∨ S₂ x')) (2 * d) := by
  classical
  intro κ _
  have : Fintype κ := Fintype.ofFinite κ
  obtain ⟨β, _, hβ⟩ := prod_lemma D h (Option κ) κ
  refine ⟨Σ j, β j, inferInstance, fun c => ?_⟩
  obtain ⟨Φ, hΦd, hΦc, hΦ⟩ := hβ (fun f => c (fun p => f p.1 p.2))
  obtain ⟨j₁, j₂, hne, hu⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j₀ : Option κ => c (fun p => Φ p.1 (if p.1 = j₀ then y₂ else y₁) p.2))
    (by simp)
  have hne' : j₂ ≠ j₁ := fun h3 => hne h3.symm
  let Φ' : X → Option κ → X := fun x j => if j = j₁ then τ x else if j = j₂ then x else y₁
  have e1 : ∀ x, Φ' x j₁ = τ x := fun x => by simp [Φ']
  have e2 : ∀ x, Φ' x j₂ = x := fun x => by simp [Φ', hne']
  have e3 : ∀ x j, j ≠ j₁ → j ≠ j₂ → Φ' x j = y₁ := fun x j h1 h2 => by simp [Φ', h1, h2]
  have hd' : Dil D 2 Φ' := by
    intro x x'
    have : ∀ j, D (Φ' x j) (Φ' x' j) =
        (if j = j₁ then D x x' else 0) + (if j = j₂ then D x x' else 0) := by
      intro j
      rcases eq_or_ne j j₁ with rfl | h1
      · rw [e1, e1, hτ, if_pos rfl, if_neg hne, add_zero]
      · rcases eq_or_ne j j₂ with rfl | h2
        · rw [e2, e2, if_neg h1, if_pos rfl, zero_add]
        · rw [e3 x j h1 h2, e3 x' j h1 h2, hD0, if_neg h1, if_neg h2, add_zero]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hc' : Cls (fun a b => a = b ∨ a = τ b) Φ' := by
    intro j
    rcases eq_or_ne j j₁ with rfl | h1
    · exact Or.inr fun x => Or.inr (e1 x)
    · rcases eq_or_ne j j₂ with rfl | h2
      · exact Or.inr fun x => Or.inl (e2 x)
      · exact Or.inl fun x x' => by rw [e3 x j h1 h2, e3 x' j h1 h2]
  refine ⟨fun x p => Φ p.1 (Φ' x p.1) p.2, dil_comp D hd' hΦd, cls_comp hc' hΦc ?_, ?_⟩
  · rintro a b c hab (rfl | rfl)
    · exact Or.inl hab
    · exact Or.inr hab
  · have key1 : ∀ x, S₁ x → c (fun p => Φ p.1 (Φ' x p.1) p.2) =
        c (fun p => Φ p.1 (if p.1 = j₁ then y₂ else y₁) p.2) := by
      intro x hx
      refine hΦ (Φ' x) (fun j => if j = j₁ then y₂ else y₁) (fun j => ?_)
      rcases eq_or_ne j j₁ with rfl | h1
      · left
        rw [e1, if_pos rfl]
        exact hR2 _ _ (hτ1 x hx) hy2
      · rcases eq_or_ne j j₂ with rfl | h2
        · left
          rw [e2, if_neg h1]
          exact hR1 _ _ hx hy1
        · right
          rw [e3 x j h1 h2, if_neg h1]
    have key2 : ∀ x, S₂ x → c (fun p => Φ p.1 (Φ' x p.1) p.2) =
        c (fun p => Φ p.1 (if p.1 = j₂ then y₂ else y₁) p.2) := by
      intro x hx
      refine hΦ (Φ' x) (fun j => if j = j₂ then y₂ else y₁) (fun j => ?_)
      rcases eq_or_ne j j₁ with rfl | h1
      · left
        rw [e1, if_neg hne]
        exact hR1 _ _ (hτ2 x hx) hy1
      · rcases eq_or_ne j j₂ with rfl | h2
        · left
          rw [e2, if_pos rfl]
          exact hR2 _ _ hx hy2
        · right
          rw [e3 x j h1 h2, if_neg h2]
    have key : ∀ x, (S₁ x ∨ S₂ x) → c (fun p => Φ p.1 (Φ' x p.1) p.2) =
        c (fun p => Φ p.1 (if p.1 = j₁ then y₂ else y₁) p.2) := by
      rintro x (hx | hx)
      · exact key1 x hx
      · exact (key2 x hx).trans hu.symm
    rintro x x' ⟨hx, hx'⟩
    exact (key x hx).trans (key x' hx').symm

theorem hyp_step [Finite X] {E : X → X → Prop} {d : ℝ} (τ : X → X)
    (hD0 : ∀ x, D x x = 0) (hτ : ∀ x x', D (τ x) (τ x') = D x x')
    (hrefl : ∀ x, E x x) (htrans : ∀ a b c, E a b → E b c → E a c)
    (hb : ∀ x x', E x x' → E (τ x) (τ x')) (hc : ∀ x, E (τ (τ x)) x)
    (hQ : ∀ y, Hyp D E (fun x x' => E x y ∧ E x' y) d) (y : X) :
    Hyp D (fun a b => E a b ∨ E a (τ b))
      (fun x x' => (E x y ∨ E x (τ y)) ∧ (E x' y ∨ E x' (τ y))) (2 * (d * d)) := by
  have h2 := hyp_two D htrans (hQ y) (hQ (τ y))
    (fun x x' hx z z' hz hz' => ⟨htrans _ _ _ hz hx.1, htrans _ _ _ hz' hx.2⟩)
  exact hyp_merge D τ y (τ y) (fun x => E x y) (fun x => E x (τ y)) hD0 hτ h2
    (fun x x' hx hx' => Or.inl ⟨hx, hx'⟩) (fun x x' hx hx' => Or.inr ⟨hx, hx'⟩)
    (hrefl y) (hrefl (τ y)) (fun x hx => hb _ _ hx)
    (fun x hx => htrans _ _ _ (hb _ _ hx) (hc y))

/-- `x` lies in the forward orbit of `x'` under `f`. -/
def Ef (f : Equiv.Perm X) (x x' : X) : Prop := ∃ k : ℕ, x = (f ^ k) x'

theorem Ef_refl (f : Equiv.Perm X) (x : X) : Ef f x x := ⟨0, by simp⟩

theorem Ef_trans (f : Equiv.Perm X) (a b c : X) : Ef f a b → Ef f b c → Ef f a c := by
  rintro ⟨k, rfl⟩ ⟨l, rfl⟩
  exact ⟨k + l, by rw [pow_add, Equiv.Perm.mul_apply]⟩

theorem sq_step [Finite X] (f : Equiv.Perm X) (hD0 : ∀ x, D x x = 0)
    (hf : ∀ x x', D (f x) (f x') = D x x') {d : ℝ}
    (hQ : ∀ y, Hyp D (Ef (f * f)) (fun x x' => Ef (f * f) x y ∧ Ef (f * f) x' y) d) (y : X) :
    Hyp D (Ef f) (fun x x' => Ef f x y ∧ Ef f x' y) (2 * (d * d)) := by
  have hb : ∀ x x', Ef (f * f) x x' → Ef (f * f) (f x) (f x') := by
    rintro x x' ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_two, ← pow_mul, ← pow_succ',
      ← pow_succ]
  have hc : ∀ x, Ef (f * f) (f (f x)) x := fun x => ⟨1, by simp⟩
  have h := hyp_step D f hD0 hf (Ef_refl (f * f)) (Ef_trans (f * f)) hb hc hQ y
  refine h.mono D ?_ ?_
  · rintro a b (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨2 * k, by rw [pow_mul, pow_two]⟩
    · exact ⟨2 * k + 1, by rw [pow_succ, pow_mul, pow_two, Equiv.Perm.mul_apply]⟩
  · have aux : ∀ x, Ef f x y → Ef (f * f) x y ∨ Ef (f * f) x (f y) := by
      rintro x ⟨k, rfl⟩
      rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
      · exact Or.inl ⟨m, by rw [pow_mul, pow_two]⟩
      · exact Or.inr ⟨m, by rw [pow_succ, pow_mul, pow_two, Equiv.Perm.mul_apply]⟩
    rintro x x' ⟨hx, hx'⟩
    exact ⟨aux x hx, aux x' hx'⟩

/-- The dilation factors along a chain of index-two extensions. -/
def dd : ℕ → ℝ
  | 0 => 1
  | (a + 1) => 2 * (dd a * dd a)

theorem dd_pos (a : ℕ) : 0 < dd a := by
  induction a with
  | zero => simp [dd]
  | succ a ih =>
    simp only [dd]
    positivity

theorem pow_two_case [Finite X] (hD0 : ∀ x, D x x = 0) : ∀ (a : ℕ) (f : Equiv.Perm X),
    (∀ x x', D (f x) (f x') = D x x') → f ^ (2 ^ a) = 1 →
    ∀ y, Hyp D (Ef f) (fun x x' => Ef f x y ∧ Ef f x' y) (dd a)
  | 0, f, _, h1, y => by
    have hf1 : f = 1 := by simpa using h1
    subst hf1
    intro κ _
    refine ⟨Unit, inferInstance, fun c => ⟨fun x _ => x, ?_, ?_, ?_⟩⟩
    · intro x x'
      simp [dd]
    · intro i
      exact Or.inr fun x => Ef_refl _ _
    · rintro x x' ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩
      simp
  | a + 1, f, hf, h1, y => by
    refine sq_step D f hD0 hf (pow_two_case hD0 a (f * f) ?_ ?_) y
    · intro x x'
      simp [hf]
    · rw [← pow_two, ← pow_mul, ← pow_succ']
      exact h1

end Framework

end OMA.Helpers
open Filter Set
open scoped Topology BigOperators

namespace OMA.Simplex

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Good {I : Type} (D : I → I → ℝ) : Prop :=
  ∀ (κ : Type) [Finite κ] [Nonempty κ],
    ∃ (X : Type) (_ : Fintype X) (d : ℕ) (v : X → E d),
      ∀ c : X → κ, ∃ f : I → X,
        (∀ i j, dist (v (f i)) (v (f j)) ^ 2 = D i j) ∧
          ∃ k, ∀ i, c (f i) = k

lemma good_zero {I : Type} : Good (fun _ _ : I => 0) := by
  intro κ _ _
  exact ⟨Unit, inferInstance, 0, fun _ => 0, fun c =>
    ⟨fun _ => (), by simp, c (), by simp⟩⟩

noncomputable def concat {d e : ℕ} (x : E d) (y : E e) : E (d + e) :=
  WithLp.toLp 2 (Fin.addCases (fun i => x i) (fun i => y i))

lemma dist_sq {d : ℕ} (x y : E d) : dist x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.dist_eq, sq_abs]

lemma concat_dist_sq {d e : ℕ} (x x' : E d) (y y' : E e) :
    dist (concat x y) (concat x' y') ^ 2 = dist x x' ^ 2 + dist y y' ^ 2 := by
  rw [dist_sq, dist_sq x x', dist_sq y y', Fin.sum_univ_add]
  simp [concat]

lemma Good.add {I : Type} [Nonempty I] {D₁ D₂ : I → I → ℝ}
    (h₁ : Good D₁) (h₂ : Good D₂) : Good (fun i j => D₁ i j + D₂ i j) := by
  classical
  intro κ _ _
  obtain ⟨Y, _, e, w, hw⟩ := h₂ κ
  obtain ⟨X, _, d, v, hv⟩ := h₁ (Y → κ)
  refine ⟨X × Y, inferInstance, d + e, fun p => concat (v p.1) (w p.2), fun c => ?_⟩
  obtain ⟨f, hfd, P, hf⟩ := hv (fun x y => c (x,y))
  obtain ⟨g, hgd, k, hg⟩ := hw P
  refine ⟨fun i => (f i, g i), fun i j => ?_, k, fun i => ?_⟩
  · rw [concat_dist_sq, hfd, hgd]
  · exact (congrFun (hf i) (g i)).trans (hg i)

lemma Good.scale {I : Type} {D : I → I → ℝ} (hD : Good D) {a : ℝ} (ha : 0 ≤ a) :
    Good (fun i j => a * D i j) := by
  intro κ _ _
  obtain ⟨X, _, d, v, hv⟩ := hD κ
  refine ⟨X, inferInstance, d, fun x => Real.sqrt a • v x, fun c => ?_⟩
  obtain ⟨f, hd, k, hk⟩ := hv c
  refine ⟨f, fun i j => ?_, k, hk⟩
  have hd' := hd i j
  rw [dist_eq_norm] at hd' ⊢
  rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha, hd']

noncomputable def word {X J : Type} [Fintype J] {d : ℕ} (v : X → E d)
    (a : ℝ) (f : J → X) : E (Fintype.card (J × Fin d)) :=
  WithLp.toLp 2 fun q => a * (v (f ((Fintype.equivFin _).symm q).1)) ((Fintype.equivFin _).symm q).2

lemma word_dist_sq {X J : Type} [Fintype J] {d : ℕ} (v : X → E d)
    (a : ℝ) (f g : J → X) :
    dist (word v a f) (word v a g) ^ 2 = a ^ 2 * ∑ j, dist (v (f j)) (v (g j)) ^ 2 := by
  classical
  rw [dist_sq]
  simp only [word, WithLp.ofLp_toLp]
  let F (p : J × Fin d) := (a * v (f p.1) p.2 - a * v (g p.1) p.2) ^ 2
  change (∑ q, F ((Fintype.equivFin (J × Fin d)).symm q)) = _
  rw [Equiv.sum_comp (Fintype.equivFin (J × Fin d)).symm F, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [dist_sq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [F]
  ring

lemma good_orbit {I X : Type} [Nonempty I] [Fintype X] {d : ℕ} (v : X → E d)
    (ρ : Equiv.Perm X) (hv : ∀ x y, dist (v (ρ x)) (v (ρ y)) = dist (v x) (v y))
    {a : ℕ} (hρ : ρ ^ (2 ^ a) = 1) (o : X) (p : I → X)
    (hp : ∀ i, OMA.Helpers.Ef ρ (p i) o) :
    Good (fun i j => dist (v (p i)) (v (p j)) ^ 2) := by
  classical
  intro κ _ _
  let D (x y : X) : ℝ := dist (v x) (v y) ^ 2
  obtain ⟨J, _, hJ⟩ := OMA.Helpers.pow_two_case D (fun x => by simp [D]) a ρ
    (fun x y => by simp [D, hv]) hρ o κ
  let scale := (Real.sqrt (OMA.Helpers.dd a))⁻¹
  have hpos := OMA.Helpers.dd_pos a
  have hscale : scale ^ 2 * OMA.Helpers.dd a = 1 := by
    simp [scale, inv_pow, Real.sq_sqrt hpos.le, hpos.ne']
  refine ⟨J → X, inferInstance, _, word v scale, fun c => ?_⟩
  obtain ⟨Φ, hΦ, _, hc⟩ := hJ c
  let i₀ : I := Classical.choice inferInstance
  refine ⟨fun i => Φ (p i), fun i j => ?_, c (Φ (p i₀)), fun i => hc _ _ ⟨hp i, hp i₀⟩⟩
  rw [word_dist_sq, show (∑ t, dist (v (Φ (p i) t)) (v (Φ (p j) t)) ^ 2) =
      OMA.Helpers.dd a * dist (v (p i)) (v (p j)) ^ 2 from hΦ (p i) (p j),
    ← mul_assoc, hscale, one_mul]

end OMA.Simplex
namespace OMA.Simplex

noncomputable def root (a : ℕ) : ℂ :=
  Complex.exp (Complex.ofReal (2 * Real.pi / ((2 : ℝ) ^ a)) * Complex.I)

lemma root_norm (a : ℕ) : ‖root a‖ = 1 := by
  rw [root, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, Real.exp_zero]

lemma root_pow (a : ℕ) : root a ^ (2 ^ a : ℕ) = 1 := by
  rw [root, ← Complex.exp_nat_mul, Nat.cast_pow, Nat.cast_ofNat]
  convert Complex.exp_two_pi_mul_I using 2
  push_cast
  field_simp

lemma root_ne_one {a : ℕ} (ha : 0 < a) : root a ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
  have hre := congrArg Complex.im hm
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
    Complex.im_ofNat, mul_one, mul_zero, zero_mul, add_zero, sub_zero] at hre
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have htwo : (1 : ℝ) < 2 ^ a := one_lt_pow₀ (by norm_num) ha.ne'
  have hlt : 2 * Real.pi / (2 : ℝ) ^ a < 2 * Real.pi := div_lt_self hp htwo
  have hpos : 0 < 2 * Real.pi / (2 : ℝ) ^ a := by positivity
  have hm0 : (0 : ℤ) < m := by
    exact_mod_cast (show 0 < (m : ℝ) by nlinarith)
  have hm1 : m < 1 := by
    exact_mod_cast (show (m : ℝ) < 1 by nlinarith)
  omega

lemma root_tendsto : Tendsto root atTop (𝓝 1) := by
  have hpow : Tendsto (fun a : ℕ => (2 : ℝ) ^ a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hangle : Tendsto (fun a : ℕ => 2 * Real.pi / (2 : ℝ) ^ a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hexp := (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const Complex.I)).tendsto 0
  unfold root
  simpa [Function.comp_def] using hexp.comp hangle

abbrev Orbit (ζ : ℂ) (q : ℕ) := Set.range (fun i : Fin q => ζ ^ (i : ℕ))

lemma pow_mem_orbit {ζ : ℂ} {q : ℕ} (hq : 0 < q) (hζ : ζ ^ q = 1) (m : ℕ) :
    ζ ^ m ∈ Orbit ζ q := by
  refine ⟨⟨m % q, Nat.mod_lt m hq⟩, ?_⟩
  change ζ ^ (m % q) = ζ ^ m
  conv_rhs => rw [← Nat.mod_add_div m q, pow_add, pow_mul, hζ, one_pow, mul_one]

noncomputable def orbitShift {ζ : ℂ} {q : ℕ} (hq : 0 < q) (hζ : ζ ^ q = 1) :
    Equiv.Perm (Orbit ζ q) where
  toFun x := ⟨ζ * x, by
    obtain ⟨i, hi⟩ := x.property
    rw [← hi, ← pow_succ']
    exact pow_mem_orbit hq hζ _⟩
  invFun x := ⟨ζ ^ (q - 1) * x, by
    obtain ⟨i, hi⟩ := x.property
    rw [← hi, ← pow_add]
    exact pow_mem_orbit hq hζ _⟩
  left_inv x := by
    apply Subtype.ext
    change ζ ^ (q - 1) * (ζ * (x : ℂ)) = x
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega), hζ, one_mul]
  right_inv x := by
    apply Subtype.ext
    change ζ * (ζ ^ (q - 1) * (x : ℂ)) = x
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega), hζ, one_mul]

lemma orbitShift_pow {ζ : ℂ} {q : ℕ} (hq : 0 < q) (hζ : ζ ^ q = 1) (m : ℕ)
    (x : Orbit ζ q) : (((orbitShift hq hζ ^ m) x : Orbit ζ q) : ℂ) = ζ ^ m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change ζ * (((orbitShift hq hζ ^ m) x : Orbit ζ q) : ℂ) = _
    rw [ih, ← mul_assoc, ← pow_succ']

lemma good_roots {I : Type} [Nonempty I] (m : I → ℕ) (a : ℕ) :
    Good (fun i j => dist (root a ^ m i) (root a ^ m j) ^ 2) := by
  classical
  let ζ := root a
  let q : ℕ := 2 ^ a
  have hq : 0 < q := by positivity
  have hζ : ζ ^ q = 1 := root_pow a
  let X := Orbit ζ q
  let : Fintype X := (Set.finite_range _).fintype
  let ρ := orbitShift hq hζ
  let o : X := ⟨1, by
    change (1 : ℂ) ∈ Orbit ζ q
    rw [← pow_zero ζ]
    exact pow_mem_orbit hq hζ 0⟩
  let p (i : I) : X := ⟨ζ ^ m i, pow_mem_orbit hq hζ _⟩
  let v (x : X) : E 2 := Complex.orthonormalBasisOneI.repr x
  have hdist (x y : X) : dist (v x) (v y) = dist (x : ℂ) y :=
    Complex.orthonormalBasisOneI.repr.isometry.dist_eq _ _
  have hρ : ρ ^ q = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (((orbitShift hq hζ ^ q) x : X) : ℂ) = x
    rw [orbitShift_pow, hζ, one_mul]
  have hv (x y : X) : dist (v (ρ x)) (v (ρ y)) = dist (v x) (v y) := by
    simp only [hdist, dist_eq_norm]
    change ‖ζ * (x : ℂ) - ζ * (y : ℂ)‖ = ‖(x : ℂ) - (y : ℂ)‖
    rw [← mul_sub, norm_mul, root_norm, one_mul]
  have hp (i : I) : OMA.Helpers.Ef ρ (p i) o := by
    refine ⟨m i, Subtype.ext ?_⟩
    simp [ρ, p, o, orbitShift_pow]
  simpa only [hdist] using good_orbit v ρ hv hρ o p hp

lemma integerMetric_closure {I : Type} [Nonempty I] (m : I → ℕ) :
    (fun i j => ((m i : ℝ) - m j) ^ 2) ∈ closure {D : I → I → ℝ | Good D} := by
  let g (a : ℕ) (i : I) : ℂ := ∑ t ∈ Finset.range (m i), root a ^ t
  let D (a : ℕ) (i j : I) : ℝ := ‖g a i - g a j‖ ^ 2
  have hg (i : I) : Tendsto (fun a => g a i) atTop (𝓝 (m i : ℂ)) := by
    simpa [g] using tendsto_finsetSum (Finset.range (m i))
      (fun t _ => root_tendsto.pow t)
  have hlim : Tendsto D atTop (𝓝 (fun i j => ((m i : ℝ) - m j) ^ 2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := ((hg i).sub (hg j)).norm.pow 2
    simpa [D, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Real.norm_eq_abs, sq_abs] using h
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  have hra := root_ne_one ha
  have hmul (i : I) : (root a - 1) * g a i = root a ^ m i - 1 :=
    mul_geom_sum _ _
  convert (good_roots m a).scale (sq_nonneg (‖root a - 1‖⁻¹)) using 1
  funext i j
  have hdiff : root a ^ m i - root a ^ m j = (root a - 1) * (g a i - g a j) := by
    rw [mul_sub, hmul, hmul]
    ring
  simp only [D, dist_eq_norm, hdiff, norm_mul, mul_pow]
  have hn : ‖root a - 1‖ ≠ 0 := by simpa [sub_eq_zero] using hra
  field_simp

end OMA.Simplex
namespace OMA.Simplex

lemma Good.symm {I : Type} {D : I → I → ℝ} (h : Good D) (i j : I) : D i j = D j i := by
  obtain ⟨X, _, _, v, hv⟩ := h Unit
  obtain ⟨f, hd, _⟩ := hv (fun _ => ())
  rw [← hd, ← hd j i, dist_comm]

lemma Good.diag {I : Type} {D : I → I → ℝ} (h : Good D) (i : I) : D i i = 0 := by
  obtain ⟨X, _, _, v, hv⟩ := h Unit
  obtain ⟨f, hd, _⟩ := hv (fun _ => ())
  rw [← hd]
  simp

lemma realMetric_closure {I : Type} [Fintype I] [Nonempty I] (f : I → ℝ) :
    (fun i j => (f i - f j) ^ 2) ∈ closure {D : I → I → ℝ | Good D} := by
  let b : ℝ := ∑ i, |f i|
  have hnon (i : I) : 0 ≤ f i + b := by
    have hb : |f i| ≤ b := Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)
    linarith [neg_abs_le (f i)]
  let m (x : ℝ) (i : I) : ℕ := ⌊(f i + b) * x⌋₊
  let D (x : ℝ) (i j : I) : ℝ := (x ^ 2)⁻¹ * ((m x i : ℝ) - m x j) ^ 2
  have hf (i : I) : Tendsto (fun x : ℝ => (m x i : ℝ) / x) atTop (𝓝 (f i + b)) :=
    tendsto_nat_floor_mul_div_atTop (hnon i)
  have hlim : Tendsto D atTop (𝓝 (fun i j => (f i - f j) ^ 2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := ((hf i).sub (hf j)).pow 2
    rw [show (f i + b - (f j + b)) ^ 2 = (f i - f j) ^ 2 by ring] at h
    apply h.congr
    intro x
    dsimp only [D]
    rw [← sub_div, div_pow, div_eq_mul_inv, mul_comm]
  refine isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall fun x => ?_)
  exact map_mem_closure (f := fun T : I → I → ℝ => (x ^ 2)⁻¹ • T)
    (continuous_const_smul _) (integerMetric_closure (m x))
    (fun S hS => hS.scale (inv_nonneg.mpr (sq_nonneg x)))

lemma metric_sum_closure {I J : Type} [Nonempty I] (s : Finset J) (D : J → I → I → ℝ)
    (hD : ∀ j ∈ s, D j ∈ closure {D : I → I → ℝ | Good D}) :
    (fun i j => ∑ k ∈ s, D k i j) ∈ closure {D : I → I → ℝ | Good D} := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using subset_closure (s := {D : I → I → ℝ | Good D}) (good_zero (I := I))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact map_mem_closure₂ continuous_add (hD a (Finset.mem_insert_self _ _))
      (ih fun b hb => hD b (Finset.mem_insert_of_mem hb)) (fun _ hx _ hy => hx.add hy)

abbrev Symmat (J : Type) := selfAdjoint.submodule ℝ (Matrix J J ℝ)

lemma symmat_symm {J : Type} (G : Symmat J) (i j : J) : G.val i j = G.val j i :=
  (show (G.val : Matrix J J ℝ).IsHermitian from G.property).apply _ _

def metric {J : Type} (G : Symmat J) : Option J → Option J → ℝ
  | none, none => 0
  | some i, none => G.val i i
  | none, some j => G.val j j
  | some i, some j => G.val i i + G.val j j - 2 * G.val i j

noncomputable def gramLift {J : Type} (D : Option J → Option J → ℝ) : Symmat J :=
  ⟨Matrix.of fun i j => (D (some i) none + D (some j) none -
      (D (some i) (some j) + D (some j) (some i)) / 2) / 2,
    by
      change Matrix.IsHermitian _
      ext i j
      simp [Matrix.conjTranspose_apply]
      ring⟩

lemma metric_gramLift {J : Type} {D : Option J → Option J → ℝ} (hD : Good D) :
    metric (gramLift D) = D := by
  funext i j
  cases i <;> cases j <;> simp [metric, gramLift, hD.diag, hD.symm none]
  rename_i a b
  rw [hD.symm (some b) (some a)]
  ring

lemma gramLift_metric {J : Type} (G : Symmat J) : gramLift (metric G) = G := by
  apply Subtype.ext
  ext i j
  simp [gramLift, metric, symmat_symm G j i]
  ring

lemma continuous_gramLift {J : Type} : Continuous (gramLift (J := J)) := by
  refine continuous_induced_rng.mpr ?_
  exact continuous_pi fun i => continuous_pi fun j => by
    change Continuous (fun D : Option J → Option J → ℝ =>
      (D (some i) none + D (some j) none - (D (some i) (some j) + D (some j) (some i)) / 2) / 2)
    fun_prop

def goodGrams (J : Type) : Set (Symmat J) := {G | Good (metric G)}

lemma convex_goodGrams (J : Type) : Convex ℝ (goodGrams J) := by
  intro x hx y hy a b ha hb _
  change Good (metric x) at hx
  change Good (metric y) at hy
  change Good (metric (a • x + b • y))
  convert (hx.scale ha).add (hy.scale hb) using 1
  funext i j
  cases i <;> cases j <;> simp [metric, Submodule.coe_add] <;> try ring

open scoped MatrixOrder in
lemma psd_mem_closure {J : Type} [Fintype J] (G : Symmat J)
    (hG : G.val.PosSemidef) : G ∈ closure (goodGrams J) := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  let f (k : J) (i : Option J) : ℝ := i.elim 0 (B k)
  have hmetric : metric G = fun i j => ∑ k, (f k i - f k j) ^ 2 := by
    have hh (i j : J) : G.val i j = ∑ k, B k i * B k j := by
      rw [hB, Matrix.mul_apply]
      simp
    funext i j
    cases i <;> cases j <;> simp [metric, f, hh, pow_two]
    rename_i i j
    let b : J → J → ℝ := B
    change (∑ k, b k i * b k i) + (∑ k, b k j * b k j) - 2 * (∑ k, b k i * b k j) =
      ∑ k, (b k i - b k j) * (b k i - b k j)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hm : metric G ∈ closure {D : Option J → Option J → ℝ | Good D} := by
    rw [hmetric]
    exact metric_sum_closure _ _ (fun k _ => realMetric_closure (f k))
  rw [← gramLift_metric G]
  exact map_mem_closure continuous_gramLift hm (fun D hD => by
    change Good (metric (gramLift D))
    rwa [metric_gramLift hD])

end OMA.Simplex
open scoped RealInnerProductSpace Matrix

namespace OMA.Simplex

def quadratic {J : Type} [Fintype J] (G : Symmat J) (x : J → ℝ) : ℝ :=
  ∑ i, ∑ j, G.val i j * x i * x j

lemma quadratic_eq {J : Type} [Fintype J] (G : Symmat J) (x : J → ℝ) :
    quadratic G x = star x ⬝ᵥ (G.val *ᵥ x) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_smul {J : Type} [Fintype J] (G : Symmat J) (x : J → ℝ) (t : ℝ) :
    quadratic G (t • x) = t ^ 2 * quadratic G x := by
  simp only [quadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma psd_nhds {J : Type} [Fintype J] (G : Symmat J) (hG : G.val.PosDef) :
    ∀ᶠ M : Symmat J in 𝓝 G, M.val.PosSemidef := by
  let sphere := Metric.sphere (0 : J → ℝ) 1
  have hs : IsCompact sphere := isCompact_sphere _ _
  have hc : Continuous (fun p : Symmat J × (J → ℝ) => quadratic p.1 p.2) := by
    unfold quadratic
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    have hV : Continuous (fun p : Symmat J × (J → ℝ) => (p.1.val : J → J → ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hA : Continuous (fun p : Symmat J × (J → ℝ) => p.1.val i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hV)
    exact (hA.mul ((continuous_apply i).comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_snd)
  have hnear : ∀ᶠ M : Symmat J in 𝓝 G, ∀ x ∈ sphere, 0 < quadratic M x := by
    apply hs.eventually_forall_of_forall_eventually
    intro y hy
    have hy0 : y ≠ 0 := by
      intro hy0
      subst y
      simp [sphere] at hy
    have hq : 0 < quadratic G y := by
      rw [quadratic_eq]
      exact hG.dotProduct_mulVec_pos hy0
    exact hc.continuousAt.eventually (lt_mem_nhds hq)
  filter_upwards [hnear] with M hM
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨M.property, fun x => ?_⟩
  rw [← quadratic_eq]
  by_cases hx : x = 0
  · simp [hx, quadratic]
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : ‖x‖⁻¹ • x ∈ sphere := by
      simp [sphere, norm_smul, hnx.ne']
    have h := hM (‖x‖⁻¹ • x) hy
    rw [quadratic_smul] at h
    exact (pos_of_mul_pos_right h (sq_nonneg _)).le

open scoped Matrix.Norms.Elementwise in
set_option maxHeartbeats 400000 in
lemma good_of_posDef {J : Type} [Fintype J] (G : Symmat J) (hG : G.val.PosDef) :
    Good (metric G) := by
  let C := goodGrams J
  have hC : Convex ℝ C := convex_goodGrams J
  have hgi : G ∈ interior (closure C) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [psd_nhds G hG] with M hm
    exact psd_mem_closure M hm
  have hspan : affineSpan ℝ C = ⊤ := by
    have hclosed : IsClosed (affineSpan ℝ C : Set (Symmat J)) :=
      ((affineSpan ℝ C).isClosed_direction_iff).mp
        ((affineSpan ℝ C).direction.closed_of_finiteDimensional)
    have hle : affineSpan ℝ (closure C) ≤ affineSpan ℝ C :=
      affineSpan_le.mpr (closure_minimal (subset_affineSpan ℝ C) hclosed)
    rw [hC.closure.interior_nonempty_iff_affineSpan_eq_top.mp ⟨G, hgi⟩] at hle
    exact top_le_iff.mp hle
  have hi := hC.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  exact interior_subset ((hC.interior_closure_eq_interior_of_nonempty_interior hi) ▸ hgi)

lemma gram_metric {J : Type} {d : ℕ} (p : J → E d) :
    metric (⟨Matrix.gram ℝ p, Matrix.isHermitian_gram ℝ p⟩ : Symmat J) =
      (fun i j => dist (i.elim 0 p) (j.elim 0 p) ^ 2) := by
  funext i j
  cases i <;> cases j <;> simp [metric, Matrix.gram, dist_eq_norm, norm_sub_sq_real] <;> try ring

end OMA.Simplex

open Erdos174 OMA.Simplex in
theorem OMA.solution : type_of% @Erdos174.erdos_174.variants.simplex := by
  classical
  intro n A hA
  have hfin : A.Finite := finite_set_of_fin_dim_affineIndependent ℝ hA
  refine ⟨hfin, fun k hk => ?_⟩
  let : Fintype A := hfin.fintype
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  by_cases hn : Nonempty A
  swap
  · have he : IsEmpty A := not_nonempty_iff.mp hn
    exact ⟨0, fun _ => ⟨fun a => he.elim a, Congruent.of_subsingleton_index,
      ⟨0, by omega⟩, fun a => he.elim a⟩⟩
  let o : A := Classical.choice hn
  let J := {a : A // a ≠ o}
  let e : Option J ≃ A := Equiv.optionSubtypeNe o
  let p (i : J) : E n := (i.val : E n) - (o : E n)
  have hp : LinearIndependent ℝ p := by
    simpa [p, J, vsub_eq_sub] using
      (affineIndependent_iff_linearIndependent_vsub ℝ (Subtype.val : A → E n) o).mp hA
  let G : Symmat J := ⟨Matrix.gram ℝ p, Matrix.isHermitian_gram ℝ p⟩
  have hpd : G.val.PosDef := Matrix.posDef_gram_of_linearIndependent hp
  have hg := good_of_posDef G hpd
  have hdist (i j : Option J) : metric G i j = dist ((e i : A) : E n) (e j : E n) ^ 2 := by
    have he (i : Option J) : i.elim 0 p = (e i : E n) - (o : E n) := by
      cases i with
      | none => change 0 = (o : E n) - (o : E n); simp
      | some i => rfl
    rw [gram_metric p]
    change dist (i.elim 0 p) (j.elim 0 p) ^ 2 = _
    rw [he, he, dist_sub_right]
  obtain ⟨X, _, d, v, hv⟩ := hg (Fin k)
  refine ⟨d, fun c => ?_⟩
  obtain ⟨f, hf, color, hc⟩ := hv (c ∘ v)
  refine ⟨fun a => v (f (e.symm a)), Congruent.of_dist_eq ?_, color, fun a => hc _⟩
  intro a b
  have hd := hf (e.symm a) (e.symm b)
  rw [hdist, e.apply_symm_apply, e.apply_symm_apply] at hd
  nlinarith only [hd, dist_nonneg (x := v (f (e.symm a))) (y := v (f (e.symm b))),
    dist_nonneg (x := (a : E n)) (y := (b : E n))]
