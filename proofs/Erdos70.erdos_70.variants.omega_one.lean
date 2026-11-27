import FormalConjectures.ErdosProblems.«70»

-- Problem: The relation at $\omega_1$
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/70.lean:178 (declaration Erdos70.erdos_70.variants.omega_one)
-- Credit: @koolkao (the owner of the agent is credited as the solver)

/-!
# Disproof of `Erdos70.erdos_70.variants.omega_one`

The variant asks for `𝔠.ord → (ω₁, n)³₂` for every `n ≥ 2`, where `𝔠.ord` is the initial ordinal
of the continuum. This fails in ZFC already for `n = 4`:

Fix an injection `f : 𝔠.ord.ToType → ℝ`. Colour a triple `x < y < z` blue iff it is a *peak*,
`f x < f y > f z`, and red otherwise.
* No blue 4-set: for `y₀ < y₁ < y₂ < y₃`, the peak `y₀ y₁ y₂` gives `f y₂ < f y₁` and the peak
  `y₁ y₂ y₃` gives `f y₁ < f y₂`.
* No red set of type `ω₁`: on a peak-free set `H`, every point is either below all earlier values or
  below all later values, so `H = A ∪ B` with `f` strictly antitone on `A` and strictly monotone on
  `B`. A well-ordered set on which a real function is strictly monotone is countable (choose a
  rational between the values at a point and at its successor), so `H` is countable, while a set of
  order type `ω₁` has cardinality `ℵ₁`.
-/

open Cardinal Ordinal Set
open scoped Cardinal

namespace OMA.Erdos70OmegaOne

universe u

/-- A real-valued function that is strictly monotone on a subset of a well-order is
supported on a countable set. -/
theorem countable_of_strictMonoOn {W : Type u} [LinearOrder W] [WellFoundedLT W] (g : W → ℝ)
    (S : Set W) (hg : StrictMonoOn g S) : S.Countable := by
  classical
  -- points of `S` with a strictly larger point of `S`
  set S' : Set W := {x | x ∈ S ∧ ∃ y ∈ S, x < y} with hS'
  have hne : ∀ x : S', ({y | y ∈ S ∧ x.1 < y} : Set W).Nonempty := fun x => by
    obtain ⟨_, y, hy, hxy⟩ := x.2
    exact ⟨y, hy, hxy⟩
  -- the successor of `x` in `S`
  let nx : S' → W := fun x => (@wellFounded_lt W _ _).min _ (hne x)
  have nx_mem : ∀ x : S', nx x ∈ S ∧ x.1 < nx x := fun x => (@wellFounded_lt W _ _).min_mem _ (hne x)
  have nx_le : ∀ x : S', ∀ y ∈ S, x.1 < y → nx x ≤ y := fun x y hy hxy =>
    not_lt.1 ((@wellFounded_lt W _ _).not_lt_min _ (show y ∈ {y | y ∈ S ∧ x.1 < y} from ⟨hy, hxy⟩))
  have hq : ∀ x : S', ∃ q : ℚ, g x.1 < q ∧ (q : ℝ) < g (nx x) := fun x =>
    exists_rat_btwn (hg x.2.1 (nx_mem x).1 (nx_mem x).2)
  choose q hq1 hq2 using hq
  have key : ∀ x y : S', x.1 < y.1 → q x < q y := by
    intro x y hxy
    have h1 : g (nx x) ≤ g y.1 :=
      hg.monotoneOn (nx_mem x).1 y.2.1 (nx_le x y.1 y.2.1 hxy)
    have : (q x : ℝ) < q y := by linarith [hq2 x, hq1 y]
    exact_mod_cast this
  have hinj : Function.Injective q := by
    intro x y hxy
    rcases lt_trichotomy x.1 y.1 with h | h | h
    · exact absurd hxy (key x y h).ne
    · exact Subtype.ext h
    · exact absurd hxy (key y x h).ne'
  have hS'c : S'.Countable := by
    have : Countable S' := hinj.countable
    exact Set.countable_coe_iff.mp this
  have hrest : ({x | x ∈ S ∧ ∀ y ∈ S, ¬ x < y} : Set W).Subsingleton := by
    intro a ha b hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd h (ha.2 b hb.1)
    · exact h
    · exact absurd h (hb.2 a ha.1)
  refine (hS'c.union hrest.countable).mono ?_
  intro x hx
  by_cases h : ∃ y ∈ S, x < y
  · exact Or.inl ⟨hx, h⟩
  · push Not at h
    exact Or.inr ⟨hx, fun y hy hxy => absurd hxy (not_lt.2 (h y hy))⟩

/-- The same for strictly antitone functions. -/
theorem countable_of_strictAntiOn {W : Type u} [LinearOrder W] [WellFoundedLT W] (g : W → ℝ)
    (S : Set W) (hg : StrictAntiOn g S) : S.Countable :=
  countable_of_strictMonoOn (fun x => - g x) S (fun _ ha _ hb hab => neg_lt_neg (hg ha hb hab))

section colouring

variable {T : Type u} [LinearOrder T] (f : T → ℝ)

/-- `y` is a peak of the increasing triple `x < y < z`. -/
def pk (x y z : T) : Prop := x < y ∧ y < z ∧ f x < f y ∧ f z < f y

/-- Blue: the three points, in increasing order, form a peak. -/
def blue (a b c : T) : Prop :=
  pk f a b c ∨ pk f a c b ∨ pk f b a c ∨ pk f b c a ∨ pk f c a b ∨ pk f c b a

lemma blue_sorted {a b c : T} (hab : a < b) (hbc : b < c) (h : blue f a b c) :
    f a < f b ∧ f c < f b := by
  unfold blue pk at h
  rcases h with ⟨_, _, h3, h4⟩ | ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩ |
      ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩
  · exact ⟨h3, h4⟩
  all_goals exfalso; order

lemma blue_of_sorted {x y z : T} (hxy : x < y) (hyz : y < z) (h1 : f x < f y) (h2 : f z < f y) :
    blue f x y z :=
  Or.inl ⟨hxy, hyz, h1, h2⟩

lemma blue_symm (x y z : T) :
    (¬ blue f x y z ↔ ¬ blue f y x z) ∧ (¬ blue f x y z ↔ ¬ blue f x z y) := by
  unfold blue
  constructor <;> constructor <;> intro h h' <;> apply h <;> tauto

/-- No 4-element set is blue. -/
lemma no_blue_four (s : Set T) (hs : #s = (4 : ℕ))
    (hblue : s.Triplewise (fun x y z => ¬ ¬ blue f x y z)) : False := by
  obtain ⟨t, rfl, ht⟩ := Cardinal.mk_set_eq_nat_iff_finset.1 hs
  let e := t.orderEmbOfFin ht
  have mem : ∀ i, e i ∈ (t : Set T) := fun i => t.orderEmbOfFin_mem ht i
  have lt01 : e 0 < e 1 := e.strictMono (by decide)
  have lt12 : e 1 < e 2 := e.strictMono (by decide)
  have lt23 : e 2 < e 3 := e.strictMono (by decide)
  have b012 := not_not.1 (hblue (mem 0) (mem 1) (mem 2) lt01.ne lt12.ne (lt01.trans lt12).ne)
  have b123 := not_not.1 (hblue (mem 1) (mem 2) (mem 3) lt12.ne lt23.ne (lt12.trans lt23).ne)
  have h1 := (blue_sorted f lt01 lt12 b012).2
  have h2 := (blue_sorted f lt12 lt23 b123).1
  linarith

/-- A peak-free set for an injective `f` is countable when `T` is well-ordered. -/
lemma countable_of_red [WellFoundedLT T] (hf : Function.Injective f) (s : Set T)
    (hred : s.Triplewise (fun x y z => ¬ blue f x y z)) : s.Countable := by
  set A : Set T := {y | y ∈ s ∧ ∀ x ∈ s, x < y → f y < f x}
  set B : Set T := {y | y ∈ s ∧ ∀ z ∈ s, y < z → f y < f z}
  have hA : StrictAntiOn f A := fun a ha b hb hab => hb.2 a ha.1 hab
  have hB : StrictMonoOn f B := fun a ha b hb hab => ha.2 b hb.1 hab
  have hsub : s ⊆ A ∪ B := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · right
      refine ⟨hy, fun z hz hyz => ?_⟩
      have : ∃ x ∈ s, x < y ∧ ¬ f y < f x := by
        by_contra hc
        push Not at hc
        exact hyA ⟨hy, fun x hx hxy => hc x hx hxy⟩
      obtain ⟨x, hx, hxy, hfx⟩ := this
      have hfx' : f x < f y :=
        lt_of_le_of_ne (not_lt.1 hfx) (fun h => hxy.ne (hf h))
      by_contra hc
      have hc' : f z < f y := lt_of_le_of_ne (not_lt.1 hc) (fun h => hyz.ne' (hf h))
      exact hred hx hy hz hxy.ne hyz.ne (hxy.trans hyz).ne (blue_of_sorted f hxy hyz hfx' hc')
  exact ((countable_of_strictAntiOn f A hA).union (countable_of_strictMonoOn f B hB)).mono hsub

end colouring

/-- `𝔠.ord ↛ (ω₁, 4)³₂`. -/
theorem not_ramsey_four :
    ¬ Erdos70.OrdinalCardinalRamsey3 (Cardinal.continuum.{u}).ord (Cardinal.aleph.{u} 1).ord (4 : ℕ) := by
  intro h
  -- an injection of `𝔠.ord.ToType` into `ℝ`
  have hcard : lift.{0} #((Cardinal.continuum.{u}).ord.ToType) ≤ lift.{u} #ℝ := by
    rw [Cardinal.mk_toType, Cardinal.card_ord, Cardinal.mk_real, Cardinal.lift_continuum,
      Cardinal.lift_continuum]
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.1 hcard
  rcases h (fun x y z => ¬ blue f x y z) (fun x y z _ _ _ => blue_symm f x y z) with
    ⟨s, hs, hred⟩ | ⟨s, hs, hblue⟩
  · have hc := countable_of_red f f.injective s hred
    have h1 : #s = ℵ₁ := by
      have := Ordinal.card_type (α := s) (· < ·)
      rw [hs, Cardinal.card_ord] at this
      exact this.symm
    have h2 : #s ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.2 hc
    rw [h1] at h2
    exact absurd h2 (not_le.2 Cardinal.aleph0_lt_aleph_one)
  · exact no_blue_four f s hs hblue

end OMA.Erdos70OmegaOne

theorem OMA.disproof : ¬ (type_of% @Erdos70.erdos_70.variants.omega_one) := by
  intro h
  exact OMA.Erdos70OmegaOne.not_ramsey_four (h 4 (by norm_num))
