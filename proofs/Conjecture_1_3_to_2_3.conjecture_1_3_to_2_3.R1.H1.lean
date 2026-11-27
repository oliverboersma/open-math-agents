import OMAReductions.R_Conjecture_1_3_to_2_3_conjecture_1_3_to_2_3_R1

-- Step Conjecture_1_3_to_2_3.conjecture_1_3_to_2_3.R1.H1: hypothesis H1 of reduction Conjecture_1_3_to_2_3.conjecture_1_3_to_2_3.R1
-- Credit: @sobrien032
-- H1 := ∀ (P : Type) [Finite P] [PartialOrder P]     (not_total : ¬ Std.Total (α := P) (· ≤ ·))     (width_le_two : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b)     (total_ext : Set <| OrderHom P ℕ)     (total_ext_def : ∀ σ, σ ∈ total_ext ↔ Set.range σ = Set.Icc 1 (Nat.card P)),     ∃ x y : P, ({σ ∈ total_ext | σ x < σ y}.ncard / total_ext.ncard : ℚ)       ∈ Set.Icc (1/3) (2/3)  -- Posets 6-delgados (Brightwell-Wright 1992 para 5-delgados, Peczarski 2008 para 6-delgados).
-- Linial's theorem: N. Linial, The information-theoretic bound is good for merging, SIAM J. Comput. 13 (1984) 795-801.

/-!
# Linial's theorem for posets of width at most two

Proof outline. Linear extensions are handled as plain functions `f : P → ℕ` (the set `Ext P`).
Let `x` be minimal among the elements that are incomparable to something, and let `I` be the
set of elements incomparable to `x`; by width two `I` is a chain, and every `z < x` is comparable
to everything. Write `A x y` for the extensions with `f x < f y` and `L x p` for those in which
`p ∈ I` is the last member of `I` before `x`. In a member of `L x p` the element `p` sits
immediately before `x`, so swapping the two gives an injection `L x p → A x p`. Hence along the
chain `I` the count `|A x y|` at most doubles from one member to the next, and the total is at
most twice the count at the top of `I`. A discrete intermediate value argument then finds `y`
with `T ≤ 3 |A x y| ≤ 2 T`, provided `3 |A x m| ≤ 2 T` for the least member `m` of `I`.
Otherwise the same argument is run from `m`, which is again minimal, with `x` in its chain.
-/

namespace LinialWidthTwo

/-- Linear extensions of `P`, as plain functions onto `1, ..., n`. -/
def Ext (P : Type) [PartialOrder P] : Set (P → ℕ) :=
  {f | Monotone f ∧ Set.range f = Set.Icc 1 (Nat.card P)}

/-- The linear extensions that put `x` before `y`. -/
def A {P : Type} [PartialOrder P] (x y : P) : Set (P → ℕ) :=
  {f | f ∈ Ext P ∧ f x < f y}

/-- The linear extensions in which `p` comes before `x`, and every element incomparable to `x`
that lies above `p` comes after `x`. -/
def L {P : Type} [PartialOrder P] (x p : P) : Set (P → ℕ) :=
  {f | f ∈ Ext P ∧ f p < f x ∧ ∀ w, ¬ w ≤ x → ¬ x ≤ w → p < w → f x < f w}

theorem ext_injective {P : Type} [Finite P] [PartialOrder P] {f : P → ℕ} (hf : f ∈ Ext P) :
    Function.Injective f := by
  have h : (f '' Set.univ).ncard = (Set.univ : Set P).ncard := by
    rw [Set.image_univ, hf.2, Set.ncard_univ, ← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  exact Set.injOn_univ.1 (Set.injOn_of_ncard_image_eq h)

theorem ext_strictMono {P : Type} [Finite P] [PartialOrder P] {f : P → ℕ} (hf : f ∈ Ext P) :
    StrictMono f :=
  hf.1.strictMono_of_injective (ext_injective hf)

theorem ext_mem_Icc {P : Type} [PartialOrder P] {f : P → ℕ} (hf : f ∈ Ext P) (p : P) :
    1 ≤ f p ∧ f p ≤ Nat.card P := by
  have h : f p ∈ Set.Icc 1 (Nat.card P) := by
    rw [← hf.2]
    exact Set.mem_range_self p
  exact h

theorem ext_surj {P : Type} [PartialOrder P] {f : P → ℕ} (hf : f ∈ Ext P) {k : ℕ}
    (h1 : 1 ≤ k) (h2 : k ≤ Nat.card P) : ∃ q, f q = k := by
  have h : k ∈ Set.range f := by
    rw [hf.2]
    exact ⟨h1, h2⟩
  exact h

theorem ext_finite (P : Type) [Finite P] [PartialOrder P] : (Ext P).Finite := by
  have h : (Set.pi Set.univ (fun _ : P => Set.Icc 1 (Nat.card P))).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc 1 (Nat.card P))
  refine h.subset ?_
  intro f hf p _
  exact ext_mem_Icc hf p

theorem ext_nonempty (P : Type) [Finite P] [PartialOrder P] : (Ext P).Nonempty := by
  classical
  have hfin : Finite (LinearExtension P) := ‹Finite P›
  let inst : Fintype (LinearExtension P) := Fintype.ofFinite (LinearExtension P)
  have hc : Fintype.card (LinearExtension P) = Nat.card P :=
    (Nat.card_eq_fintype_card (α := LinearExtension P)).symm
  let e : Fin (Nat.card P) ≃o LinearExtension P := Fintype.orderIsoFinOfCardEq (LinearExtension P) hc
  refine ⟨fun p => (e.symm (toLinearExtension p)).val + 1, ?_, ?_⟩
  · intro a b hab
    have h : e.symm (toLinearExtension a) ≤ e.symm (toLinearExtension b) :=
      e.symm.monotone (toLinearExtension.monotone hab)
    have h' : (e.symm (toLinearExtension a)).val ≤ (e.symm (toLinearExtension b)).val := h
    exact Nat.succ_le_succ h'
  · ext k
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt (e.symm (toLinearExtension p)).isLt⟩
    · rintro ⟨h1, h2⟩
      have hk : k - 1 < Nat.card P := by omega
      refine ⟨e ⟨k - 1, hk⟩, ?_⟩
      show (e.symm (e ⟨k - 1, hk⟩)).val + 1 = k
      rw [OrderIso.symm_apply_apply]
      show k - 1 + 1 = k
      omega

/-- Swapping two incomparable elements in adjacent positions gives a linear extension. -/
theorem swap_mem {P : Type} [Finite P] [PartialOrder P] [DecidableEq P] {f : P → ℕ}
    (hf : f ∈ Ext P) {a b : P} (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) (h : f b = f a + 1) :
    f ∘ Equiv.swap a b ∈ Ext P := by
  have hs := ext_strictMono hf
  have hm := hf.1
  have e1 : Equiv.swap a b a = b := Equiv.swap_apply_left a b
  have e2 : Equiv.swap a b b = a := Equiv.swap_apply_right a b
  have e3 : ∀ q, q ≠ a → q ≠ b → Equiv.swap a b q = q :=
    fun q h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
  refine ⟨?_, ?_⟩
  · intro q r hqr
    show f (Equiv.swap a b q) ≤ f (Equiv.swap a b r)
    by_cases hqa : q = a
    · rw [hqa] at hqr ⊢
      rw [e1]
      by_cases hra : r = a
      · rw [hra, e1]
      · by_cases hrb : r = b
        · rw [hrb] at hqr
          exact absurd hqr hab
        · rw [e3 r hra hrb]
          have := hs (lt_of_le_of_ne hqr (Ne.symm hra))
          omega
    · by_cases hqb : q = b
      · rw [hqb] at hqr ⊢
        rw [e2]
        by_cases hra : r = a
        · rw [hra] at hqr
          exact absurd hqr hba
        · by_cases hrb : r = b
          · rw [hrb, e2]
          · rw [e3 r hra hrb]
            have := hm hqr
            omega
      · rw [e3 q hqa hqb]
        by_cases hra : r = a
        · rw [hra] at hqr ⊢
          rw [e1]
          have := hm hqr
          omega
        · by_cases hrb : r = b
          · rw [hrb] at hqr ⊢
            rw [e2]
            have := hs (lt_of_le_of_ne hqr hqb)
            omega
          · rw [e3 r hra hrb]
            exact hm hqr
  · rw [(Equiv.swap a b).surjective.range_comp f]
    exact hf.2

/-- If `p` is the last element incomparable to `x` that comes before `x`, then `p` sits
immediately before `x`. -/
theorem adjacent {P : Type} [Finite P] [PartialOrder P] {x : P}
    (hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
    (hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y)
    {f : P → ℕ} (hf : f ∈ Ext P) {p : P} (hpx : ¬ p ≤ x) (hxp : ¬ x ≤ p)
    (hlt : f p < f x) (hlast : ∀ w, ¬ w ≤ x → ¬ x ≤ w → p < w → f x < f w) :
    f x = f p + 1 := by
  by_contra hne
  have hgap : f p + 1 < f x := by omega
  have hxn := (ext_mem_Icc hf x).2
  obtain ⟨q, hq⟩ := ext_surj hf (k := f p + 1) (by omega) (by omega)
  have hm := hf.1
  by_cases hqx : q ≤ x
  · have hqne : q ≠ x := by
      intro hqe
      rw [hqe] at hq
      omega
    rcases hmin q (lt_of_le_of_ne hqx hqne) p with h | h
    · have := hm h
      omega
    · exact hpx (le_trans h hqx)
  · by_cases hxq : x ≤ q
    · have := hm hxq
      omega
    · rcases hchain q p hqx hxq hpx hxp with h | h
      · have := hm h
        omega
      · have hpq : p ≠ q := by
          intro hpe
          rw [hpe] at hq
          omega
        have := hlast q hqx hxq (lt_of_le_of_ne h hpq)
        omega

/-- The swap of `p` and `x` maps `L x p` injectively into `A x p`. -/
theorem ncard_L_le {P : Type} [Finite P] [PartialOrder P] {x : P}
    (hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
    (hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y)
    {p : P} (hpx : ¬ p ≤ x) (hxp : ¬ x ≤ p) : (L x p).ncard ≤ (A x p).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (fun f => f ∘ Equiv.swap p x) ?_ ?_
    ((ext_finite P).subset fun f hf => hf.1)
  · rintro f ⟨hf, hlt, hlast⟩
    have hadj := adjacent hmin hchain hf hpx hxp hlt hlast
    refine ⟨swap_mem hf hpx hxp hadj, ?_⟩
    show f (Equiv.swap p x x) < f (Equiv.swap p x p)
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
    exact hlt
  · intro f _ g _ hfg
    exact (Equiv.swap p x).surjective.injective_comp_right hfg

theorem ncard_le_two_mul {P : Type} [Finite P] [PartialOrder P] {x : P}
    (hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
    (hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y)
    {p : P} (hpx : ¬ p ≤ x) (hxp : ¬ x ≤ p) {S : Set (P → ℕ)} (hS : S ⊆ A x p ∪ L x p) :
    S.ncard ≤ 2 * (A x p).ncard := by
  have hfinA : (A x p).Finite := (ext_finite P).subset fun f hf => hf.1
  have hfinL : (L x p).Finite := (ext_finite P).subset fun f hf => hf.1
  have h1 : S.ncard ≤ (A x p ∪ L x p).ncard := Set.ncard_le_ncard hS (hfinA.union hfinL)
  have h2 : (A x p ∪ L x p).ncard ≤ (A x p).ncard + (L x p).ncard := Set.ncard_union_le _ _
  have h3 := ncard_L_le hmin hchain hpx hxp
  omega

/-- The intermediate value step, from an element `x` all of whose strict predecessors are
comparable to everything, given one element `y0` incomparable to `x` whose count is at most
two thirds of the total. -/
theorem core {P : Type} [Finite P] [PartialOrder P]
    (hw : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b)
    {x : P} (hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
    {y0 : P} (hy0 : ¬ y0 ≤ x) (hy0' : ¬ x ≤ y0)
    (h0 : 3 * (A x y0).ncard ≤ 2 * (Ext P).ncard) :
    ∃ y, (Ext P).ncard ≤ 3 * (A x y).ncard ∧ 3 * (A x y).ncard ≤ 2 * (Ext P).ncard := by
  have hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y := by
    intro y y' h1 h2 h3 h4
    rcases hw x y y' with h | h | h | h | h | h
    · exact absurd h h2
    · exact absurd h h1
    · exact absurd h h4
    · exact absurd h h3
    · exact Or.inl h
    · exact Or.inr h
  by_cases hB : ∃ w, ¬ w ≤ x ∧ ¬ x ≤ w ∧ 3 * (A x w).ncard < (Ext P).ncard
  · obtain ⟨p, ⟨hpx, hxp, hp3⟩, hpmax⟩ := (wellFounded_gt (α := P)).has_min
      {w | ¬ w ≤ x ∧ ¬ x ≤ w ∧ 3 * (A x w).ncard < (Ext P).ncard} hB
    have hpne : p ≠ x := fun h => hpx (le_of_eq h)
    by_cases hS : ∃ w, ¬ w ≤ x ∧ ¬ x ≤ w ∧ p < w
    · obtain ⟨y, ⟨hyx, hxy, hpy⟩, hymin⟩ := (wellFounded_lt (α := P)).has_min
        {w | ¬ w ≤ x ∧ ¬ x ≤ w ∧ p < w} hS
      refine ⟨y, ?_, ?_⟩
      · by_contra hlt
        exact hpmax y ⟨hyx, hxy, by omega⟩ hpy
      · have hsub : A x y ⊆ A x p ∪ L x p := by
          rintro f ⟨hf, hlt⟩
          by_cases h : f x < f p
          · exact Or.inl ⟨hf, h⟩
          · refine Or.inr ⟨hf, ?_, ?_⟩
            · have hne : f p ≠ f x := fun h' => hpne (ext_injective hf h')
              omega
            · intro w hwx hxw hpw
              have hyw : y ≤ w := by
                rcases hchain y w hyx hxy hwx hxw with h' | h'
                · exact h'
                · by_contra hnot
                  exact hymin w ⟨hwx, hxw, hpw⟩ (lt_of_le_not_ge h' hnot)
              exact lt_of_lt_of_le hlt (hf.1 hyw)
        have := ncard_le_two_mul hmin hchain hpx hxp hsub
        omega
    · exfalso
      have hsub : Ext P ⊆ A x p ∪ L x p := by
        intro f hf
        by_cases h : f x < f p
        · exact Or.inl ⟨hf, h⟩
        · refine Or.inr ⟨hf, ?_, ?_⟩
          · have hne : f p ≠ f x := fun h' => hpne (ext_injective hf h')
            omega
          · intro w hwx hxw hpw
            exact absurd ⟨w, hwx, hxw, hpw⟩ hS
      have := ncard_le_two_mul hmin hchain hpx hxp hsub
      omega
  · refine ⟨y0, ?_, h0⟩
    by_contra hlt
    exact hB ⟨y0, hy0, hy0', by omega⟩

/-- Linial's theorem, counted over `Ext P`. -/
theorem linial {P : Type} [Finite P] [PartialOrder P]
    (hnt : ¬ Std.Total (α := P) (· ≤ ·))
    (hw : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b) :
    ∃ x y : P, (Ext P).ncard ≤ 3 * (A x y).ncard ∧ 3 * (A x y).ncard ≤ 2 * (Ext P).ncard := by
  have hN : ∃ a : P, ∃ b, ¬ a ≤ b ∧ ¬ b ≤ a := by
    by_contra h
    apply hnt
    constructor
    intro a b
    by_contra h'
    exact h ⟨a, b, fun hab => h' (Or.inl hab), fun hba => h' (Or.inr hba)⟩
  obtain ⟨x, ⟨u, hxu, hux⟩, hxmin⟩ := (wellFounded_lt (α := P)).has_min
    {a | ∃ b, ¬ a ≤ b ∧ ¬ b ≤ a} hN
  have hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z := by
    intro z hz v
    by_contra h
    exact hxmin z ⟨v, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩ hz
  obtain ⟨m, ⟨hmx, hxm⟩, hmmin⟩ := (wellFounded_lt (α := P)).has_min
    {w | ¬ w ≤ x ∧ ¬ x ≤ w} ⟨u, hux, hxu⟩
  by_cases h : 3 * (A x m).ncard ≤ 2 * (Ext P).ncard
  · obtain ⟨y, hy⟩ := core hw hmin hmx hxm h
    exact ⟨x, y, hy⟩
  · have hleast : ∀ w, ¬ w ≤ x → ¬ x ≤ w → m ≤ w := by
      intro w hwx hxw
      rcases hw x m w with h' | h' | h' | h' | h' | h'
      · exact absurd h' hxm
      · exact absurd h' hmx
      · exact absurd h' hxw
      · exact absurd h' hwx
      · exact h'
      · by_contra hnot
        exact hmmin w ⟨hwx, hxw⟩ (lt_of_le_not_ge h' hnot)
    have hmin' : ∀ z, z < m → ∀ v, z ≤ v ∨ v ≤ z := by
      intro z hz v
      by_cases hzx : z ≤ x
      · have hzne : z ≠ x := by
          intro hze
          rw [hze] at hz
          exact hxm (le_of_lt hz)
        exact hmin z (lt_of_le_of_ne hzx hzne) v
      · by_cases hxz : x ≤ z
        · exact absurd (le_trans hxz (le_of_lt hz)) hxm
        · exact absurd (hleast z hzx hxz) (not_le_of_gt hz)
    have hsum : (A x m).ncard + (A m x).ncard ≤ (Ext P).ncard := by
      have hfin := ext_finite P
      have hfinA : (A x m).Finite := hfin.subset fun f hf => hf.1
      have hfinA' : (A m x).Finite := hfin.subset fun f hf => hf.1
      have hdisj : Disjoint (A x m) (A m x) := by
        rw [Set.disjoint_left]
        rintro f ⟨_, h1⟩ ⟨_, h2⟩
        omega
      rw [← Set.ncard_union_eq hdisj hfinA hfinA']
      refine Set.ncard_le_ncard ?_ hfin
      rintro f (hf | hf)
      · exact hf.1
      · exact hf.1
    obtain ⟨y, hy⟩ := core hw hmin' hxm hmx (by omega)
    exact ⟨m, y, hy⟩

end LinialWidthTwo

theorem OMA.solution : OMA.R_Conjecture_1_3_to_2_3_conjecture_1_3_to_2_3_R1.H1 := by
  intro P _ _ not_total width_le_two total_ext total_ext_def
  obtain ⟨x, y, h1, h2⟩ := LinialWidthTwo.linial not_total width_le_two
  have hT : 0 < (LinialWidthTwo.Ext P).ncard :=
    (Set.ncard_pos (LinialWidthTwo.ext_finite P)).2 (LinialWidthTwo.ext_nonempty P)
  have e1 : total_ext.ncard = (LinialWidthTwo.Ext P).ncard := by
    have himg : (fun σ : P →o ℕ => (σ : P → ℕ)) '' total_ext = LinialWidthTwo.Ext P := by
      ext f
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ.monotone, (total_ext_def σ).1 hσ⟩
      · rintro ⟨hm, hr⟩
        exact ⟨⟨f, hm⟩, (total_ext_def _).2 hr, rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ DFunLike.coe_injective]
  have e2 : {σ ∈ total_ext | σ x < σ y}.ncard = (LinialWidthTwo.A x y).ncard := by
    have himg : (fun σ : P →o ℕ => (σ : P → ℕ)) '' {σ ∈ total_ext | σ x < σ y}
        = LinialWidthTwo.A x y := by
      ext f
      constructor
      · rintro ⟨σ, ⟨hσ, hlt⟩, rfl⟩
        exact ⟨⟨σ.monotone, (total_ext_def σ).1 hσ⟩, hlt⟩
      · rintro ⟨⟨hm, hr⟩, hlt⟩
        exact ⟨⟨f, hm⟩, ⟨(total_ext_def _).2 hr, hlt⟩, rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ DFunLike.coe_injective]
  refine ⟨x, y, ?_⟩
  rw [e1, e2, Set.mem_Icc]
  have hTq : (0 : ℚ) < ((LinialWidthTwo.Ext P).ncard : ℚ) := by exact_mod_cast hT
  have h1q : ((LinialWidthTwo.Ext P).ncard : ℚ) ≤ 3 * ((LinialWidthTwo.A x y).ncard : ℚ) := by
    exact_mod_cast h1
  have h2q : 3 * ((LinialWidthTwo.A x y).ncard : ℚ) ≤ 2 * ((LinialWidthTwo.Ext P).ncard : ℚ) := by
    exact_mod_cast h2
  constructor
  · rw [le_div_iff₀ hTq]
    linarith
  · rw [div_le_iff₀ hTq]
    linarith
